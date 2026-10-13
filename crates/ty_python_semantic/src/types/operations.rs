//! Entry points for semantic type operations and the state borrowed by their recursive helpers.

use std::ops::Deref;
use std::rc::Rc;

use ty_python_core::{Program, ProgramFile};

use super::{ApplyTypeMappingVisitor, TypeRecursionState};
use crate::{Db, ProgramEnvironment};

/// Active guards shared by every semantic operation descended from the same root.
/// Transformation caches remain local to each mapping.
#[derive(Clone)]
pub(crate) struct TypeRecursionContext<'db>(Rc<TypeRecursionState<'db>>);

impl<'db> TypeRecursionContext<'db> {
    pub(super) fn state(&self) -> &TypeRecursionState<'db> {
        &self.0
    }
}

/// Access to semantic operations within one active computation.
///
/// Helpers borrow this object instead of choosing whether to preserve a caller's recursion
/// state. Structural transformations use its mapping visitor; semantic comparisons and body
/// inspection retain the same context.
///
/// Semantic comparisons borrow the current operation:
///
/// ```
/// use ty_python_semantic::{Db, TypeOperations};
/// use ty_python_semantic::types::Type;
///
/// fn compare<'db>(db: &'db dyn Db, env: &TypeOperations<'db>, left: Type<'db>, right: Type<'db>) -> bool {
///     left.is_assignable_to(db, env, right)
/// }
/// ```
///
/// Program metadata alone cannot perform a semantic comparison:
///
/// ```compile_fail
/// use ty_python_semantic::{Db, ProgramEnvironment};
/// use ty_python_semantic::types::Type;
///
/// fn compare<'db>(db: &'db dyn Db, env: &ProgramEnvironment<'db>, left: Type<'db>, right: Type<'db>) -> bool {
///     left.is_assignable_to(db, env, right)
/// }
/// ```
#[derive(Clone)]
pub struct TypeOperations<'db> {
    db: &'db dyn Db,
    env: ProgramEnvironment<'db>,
    context: TypeRecursionContext<'db>,
}

impl<'db> Deref for TypeOperations<'db> {
    type Target = ProgramEnvironment<'db>;

    fn deref(&self) -> &Self::Target {
        &self.env
    }
}

impl<'db> TypeOperations<'db> {
    /// Start semantic work for a file at an IDE or command-line entry point.
    pub fn for_file(db: &'db dyn Db, file: ProgramFile<'db>) -> Self {
        Self::for_inference(db, ProgramEnvironment::from_file(file))
    }

    /// Start semantic work that is independent of a particular source file.
    pub fn for_program(db: &'db dyn Db, program: Program<'db>) -> Self {
        Self::for_inference(db, ProgramEnvironment::from_program(program))
    }

    /// Create the owner of a source-inference operation.
    pub(crate) fn for_inference(db: &'db dyn Db, env: ProgramEnvironment<'db>) -> Self {
        Self {
            db,
            env,
            context: TypeRecursionContext(Rc::new(TypeRecursionState::default())),
        }
    }

    /// Read source metadata from another environment without replacing the active operation.
    pub(crate) fn in_environment(&self, env: ProgramEnvironment<'db>) -> Self {
        Self {
            db: self.db,
            env,
            context: self.context.clone(),
        }
    }

    /// Start a mapping whose caches belong to this transformation and whose guards remain shared.
    pub(super) fn mapping(&self) -> ApplyTypeMappingVisitor<'_, 'db> {
        ApplyTypeMappingVisitor::new(self)
    }

    pub(super) fn context(&self) -> &TypeRecursionContext<'db> {
        &self.context
    }
}

#[cfg(test)]
mod tests {
    use crate::ProgramEnvironment;
    use crate::db::tests::setup_db;
    use crate::types::Type;

    #[test]
    fn nested_operations_share_guards_without_caching_completed_results() {
        let db = setup_db();
        let env = db.program_environment();
        let nested = env.in_environment(ProgramEnvironment::from_program(env.program(&db)));
        let left = Type::int_literal(1);
        let right = Type::int_literal(2);

        assert!(!env.context().check_redundancy(&db, &env, left, right, || {
            assert!(
                nested
                    .context()
                    .check_redundancy(&db, &nested, left, right, || false)
            );
            false
        }));
        assert!(
            nested
                .context()
                .check_redundancy(&db, &nested, left, right, || true)
        );
    }
}
