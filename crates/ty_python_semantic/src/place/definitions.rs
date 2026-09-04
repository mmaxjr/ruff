use smallvec::SmallVec;
use ty_python_core::definition::{Definition, DefinitionState};
use ty_python_core::scope::ScopeId;
use ty_python_core::{BindingWithConstraintsIterator, global_scope, place_table, use_def_map};

use crate::Db;
use crate::place::{
    Place, builtins_module_scope, class_body_implicit_symbol, implicit_builtins_symbol,
    module_type_implicit_global_symbol,
};
use crate::place_load::{ImplicitPlaceLoad, PlaceLoadSource, PlaceLoadSourceKind};
use crate::reachability::ReachabilityConstraintsExtension;
use crate::types::ProgramEnvironment;

/// Records the definitions that can supply a name's value and the limits of that resolution.
///
/// A consumer needs more than the definitions to decide whether it can rewrite a name safely.
/// Resolution also tracks whether values lack explicit definitions, whether the name can be
/// deleted, and whether lookup crosses a `global` or `nonlocal` declaration.
#[derive(Debug, Clone, Eq, PartialEq)]
pub(crate) struct DefinitionResolution<'db> {
    definitions: SmallVec<[Definition<'db>; 2]>,
    is_complete: bool,
    may_be_deleted: bool,
    crosses_scope_declaration: bool,
}

#[cfg_attr(not(test), expect(dead_code, reason = "awaiting IDE integration"))]
impl<'db> DefinitionResolution<'db> {
    pub(crate) fn new() -> Self {
        Self {
            definitions: SmallVec::new(),
            is_complete: true,
            may_be_deleted: false,
            crosses_scope_declaration: false,
        }
    }

    /// Returns the definitions found by name resolution.
    pub(crate) fn definitions(&self) -> &[Definition<'db>] {
        &self.definitions
    }

    /// Returns whether every possible result is represented by a definition.
    ///
    /// Implicit builtin values are incomplete because no explicit import connects the name
    /// to their definitions. A complete resolution can still leave a name possibly unbound.
    pub(crate) fn is_complete(&self) -> bool {
        self.is_complete
    }

    /// Returns whether a visited binding source contains a reachable deletion.
    ///
    /// Scope-wide binding histories do not include deletions. This flag is meaningful only for
    /// a complete resolution.
    pub(crate) fn may_be_deleted(&self) -> bool {
        self.may_be_deleted
    }

    /// Returns whether resolution crosses a `global` or `nonlocal` declaration.
    pub(crate) fn crosses_scope_declaration(&self) -> bool {
        self.crosses_scope_declaration
    }

    pub(crate) fn finish(mut self, crosses_scope_declaration: bool) -> Self {
        self.crosses_scope_declaration = crosses_scope_declaration;
        self.definitions.shrink_to_fit();
        self
    }

    fn from_place_load_source(
        db: &'db dyn Db,
        environment: &ProgramEnvironment<'db>,
        scope: ScopeId<'db>,
        source: &PlaceLoadSource<'db>,
    ) -> Self {
        match &source.kind {
            PlaceLoadSourceKind::Bindings(bindings) => Self::from_bindings(db, bindings.clone()),
            PlaceLoadSourceKind::DefinitionsFromOwningScope { scope, id } => {
                Self::from_bindings(db, use_def_map(db, *scope).reachable_bindings(*id))
            }
            PlaceLoadSourceKind::Implicit(ImplicitPlaceLoad::ExplicitGlobalSymbol {
                file,
                name,
            }) => {
                let scope = global_scope(db, *file);
                let Some(symbol) = place_table(db, scope).symbol_id(name) else {
                    return Self::new();
                };
                Self::from_bindings(db, use_def_map(db, scope).reachable_symbol_bindings(symbol))
            }
            PlaceLoadSourceKind::Implicit(ImplicitPlaceLoad::DunderClass(class_def)) => {
                let mut resolution = Self::new();
                resolution.push_definition(*class_def);
                resolution
            }
            PlaceLoadSourceKind::Implicit(ImplicitPlaceLoad::ClassBodySymbol(name)) => {
                Self::from_place_without_definition(
                    class_body_implicit_symbol(db, environment, name).place,
                )
            }
            PlaceLoadSourceKind::Implicit(ImplicitPlaceLoad::ModuleImplicitGlobal {
                file,
                name,
            }) => Self::from_place_without_definition(
                module_type_implicit_global_symbol(db, *file, name).place,
            ),
            PlaceLoadSourceKind::Implicit(ImplicitPlaceLoad::Builtin(name)) => {
                Self::from_builtin(db, environment, scope, name)
            }
        }
    }

    fn from_builtin(
        db: &'db dyn Db,
        environment: &ProgramEnvironment<'db>,
        scope: ScopeId<'db>,
        name: &str,
    ) -> Self {
        if Some(scope) == builtins_module_scope(db, environment) {
            // A missing name in `builtins` cannot fall back to the module that is currently being
            // resolved. Treating it as undefined also avoids a recursive semantic query.
            return Self::from_place_without_definition(Place::Undefined);
        }

        // Builtin values have no explicit import for a consumer to follow. Record whether a
        // value exists without collecting definitions that consumers cannot use.
        Self::from_place_without_definition(implicit_builtins_symbol(db, environment, name).place)
    }

    /// Resolves the reachable definitions supplied by the given bindings.
    pub(crate) fn from_bindings(
        db: &'db dyn Db,
        mut bindings: BindingWithConstraintsIterator<'db, 'db>,
    ) -> Self {
        let mut resolution = Self::new();

        while let Some(binding) = bindings.next() {
            let reachability = bindings.reachability_constraints().evaluate(
                db,
                bindings.predicates(),
                binding.reachability_constraint,
            );
            if reachability.is_always_false() {
                continue;
            }

            match binding.binding {
                DefinitionState::Defined(definition) => {
                    resolution.push_definition(definition);
                }
                DefinitionState::Deleted => {
                    resolution.may_be_deleted |= reachability.may_be_true();
                }
                DefinitionState::Undefined => {}
            }
        }

        resolution
    }

    fn push_definition(&mut self, definition: Definition<'db>) {
        if !self.definitions.contains(&definition) {
            self.definitions.push(definition);
        }
    }

    fn from_place_without_definition(place: Place<'db>) -> Self {
        Self {
            is_complete: place.is_undefined(),
            ..Self::new()
        }
    }

    fn extend(&mut self, other: Self) {
        for definition in other.definitions {
            self.push_definition(definition);
        }
        self.is_complete &= other.is_complete;
        self.may_be_deleted |= other.may_be_deleted;
    }
}

#[cfg(test)]
mod tests {
    use ruff_db::files::system_path_to_file;
    use ruff_db::parsed::parsed_module;
    use ruff_python_trivia::textwrap::dedent;
    use ruff_text_size::Ranged;
    use ty_python_core::ProgramFile;
    use ty_python_core::place::PlaceExpr;
    use ty_python_core::semantic_index;

    use super::*;
    use crate::db::tests::TestDbBuilder;
    use crate::place_load::{PlaceLoadMode, PlaceLoadResolutionStep, resolve_place_load};

    #[test]
    fn resolution_collects_and_merges_reachable_definitions() {
        let source = dedent(
            "
            value = 1
            if condition:
                value = 2
            if condition:
                del value
            other = 4
            read = value
            ",
        );
        let db = TestDbBuilder::new()
            .with_file("/src/test.py", &source)
            .build()
            .unwrap();
        let file = system_path_to_file(&db, "/src/test.py").unwrap();
        let file = ProgramFile::new(&db, file, db.program_environment().program(&db));
        let module = parsed_module(&db, file.python_file(&db)).load(&db);
        let scope = global_scope(&db, file);
        let environment = ProgramEnvironment::from_file(file);
        let name = module.suite()[4]
            .as_assign_stmt()
            .unwrap()
            .value
            .as_name_expr()
            .unwrap();
        let mut sources = resolve_place_load(
            &db,
            semantic_index(&db, file),
            scope,
            PlaceExpr::from_expr_name(name),
            PlaceLoadMode::AtExpression(name.into()),
        );
        let Some(PlaceLoadResolutionStep::Source(binding_source)) = sources.next() else {
            panic!("expected a binding source");
        };
        let mut resolution =
            DefinitionResolution::from_place_load_source(&db, &environment, scope, &binding_source)
                .finish(sources.crosses_scope_declaration());

        let mut definitions: Vec<_> = resolution
            .definitions()
            .iter()
            .map(|definition| &source[definition.full_range(&db, &module).range()])
            .collect();
        definitions.sort_unstable();
        assert_eq!(definitions, ["value = 1", "value = 2"]);
        assert!(resolution.is_complete());
        assert!(resolution.may_be_deleted());

        let other = place_table(&db, scope).symbol_id("other").unwrap();
        let other = DefinitionResolution::from_bindings(
            &db,
            use_def_map(&db, scope).end_of_scope_symbol_bindings(other),
        );
        resolution.extend(other);
        resolution.extend(resolution.clone());
        assert_eq!(resolution.definitions().len(), 3);

        assert!(
            DefinitionResolution::from_builtin(&db, &environment, scope, "value").is_complete()
        );
        resolution.extend(DefinitionResolution::from_builtin(
            &db,
            &environment,
            scope,
            "print",
        ));
        assert!(!resolution.is_complete());
        assert!(resolution.may_be_deleted());
        assert!(resolution.finish(true).crosses_scope_declaration());
    }
}
