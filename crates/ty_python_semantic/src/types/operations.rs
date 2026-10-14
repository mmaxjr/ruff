//! Entry points for semantic type operations and the state borrowed by their recursive helpers.

use std::cell::Cell;
use std::ops::Deref;
use std::rc::Rc;

use salsa::plumbing::AsId;
#[cfg(any(test, feature = "testing"))]
use ty_python_core::Program;
use ty_python_core::ProgramFile;

use super::cyclic::GuardToken;
use super::{ApplyTypeMappingVisitor, TypeRecursionState};
use crate::{Db, ProgramEnvironment};

mod sealed {
    pub(crate) trait SourceQuery {}
}

/// A registered source computation whose result depends only on its explicit inputs.
/// Implementations receive an owner, but callers cannot supply their own computation.
pub(crate) trait SourceQuery<'db, 'input>: sealed::SourceQuery {
    type Input: Send + Sync;
    type Output: Send + Sync;

    fn compute(db: &'db dyn Db, source: &SourceTypeQuery<'db>, input: Self::Input) -> Self::Output;
}

/// Declare a registered query beside the source facts it computes.
macro_rules! source_query {
    (fn $query:ident<$db:lifetime, $input:lifetime>(
        $database:ident: $database_type:ty,
        $source:ident: $source_type:ty,
        $($argument:ident: $argument_type:ty),* $(,)?
    ) -> $output:ty $body:block) => {
        impl<$db: $input, $input> $crate::types::SourceQuery<$db, $input>
            for $crate::types::source_queries::$query
        {
            type Input = ($($argument_type,)*);
            type Output = $output;

            fn compute(
                $database: $database_type,
                $source: $source_type,
                ($($argument,)*): Self::Input,
            ) -> Self::Output $body
        }
    };
}

pub(crate) use source_query;

pub(crate) mod registered;
pub(crate) use registered as source_queries;

/// Starts a registered source computation with explicit inputs. Neither its inputs nor its
/// result can contain operation state, and callers cannot substitute another computation.
/// All environments created within the computation share this root's recursion guards.
pub(crate) struct SourceTypeQuery<'db> {
    db: &'db dyn Db,
    context: TypeRecursionContext<'db>,
}

impl<'db> SourceTypeQuery<'db> {
    fn new(db: &'db dyn Db) -> Self {
        Self {
            db,
            context: TypeRecursionContext(Rc::new(TypeRecursionState::default())),
        }
    }

    pub(crate) fn run<'input, Q: SourceQuery<'db, 'input>>(
        db: &'db dyn Db,
        input: Q::Input,
    ) -> Q::Output {
        Q::compute(db, &Self::new(db), input)
    }

    pub(crate) fn operations(&self, env: ProgramEnvironment<'db>) -> TypeOperations<'db> {
        TypeOperations {
            db: self.db,
            env,
            context: self.context.clone(),
        }
    }
}

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
    pub(super) fn db(&self) -> &'db dyn Db {
        self.db
    }
    pub(crate) fn semantic_model(
        db: &'db dyn Db,
        file: ProgramFile<'db>,
    ) -> crate::SemanticModel<'db> {
        let source = SourceTypeQuery::new(db);
        crate::SemanticModel::with_operations(
            db,
            file,
            source.operations(ProgramEnvironment::from_file(file)),
        )
    }

    #[cfg(any(test, feature = "testing"))]
    pub fn for_test_program(db: &'db dyn Db, program: Program<'db>) -> Self {
        SourceTypeQuery::new(db).operations(ProgramEnvironment::from_program(program))
    }

    /// Keep global query caches unavailable while a local recursive operation is active.
    pub(super) fn enter_recursive_scope<'guard>(
        &self,
        guard: GuardToken<'guard>,
    ) -> RecursiveOperationScope<'guard, 'db> {
        let operation = &self.context.state().operation;
        let previous = operation.depth.replace(operation.depth.get() + 1);
        RecursiveOperationScope {
            context: self.context.clone(),
            previous,
            _guard: guard,
        }
    }

    pub(super) fn identity(&self) -> TypeOperationIdentity {
        TypeOperationIdentity {
            owner: self.context.state().operation.identity.clone(),
            program: self.program(self.db).as_id(),
        }
    }

    /// Use a global query only when no enclosing recursive operation can affect its result.
    /// Nested work computes with the caller's existing owner.
    pub(super) fn cached_query<R>(
        &self,
        cached: impl FnOnce() -> R,
        local: impl FnOnce() -> R,
    ) -> R {
        if self.context.state().operation.is_active() {
            local()
        } else {
            cached()
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

#[derive(Default)]
pub(super) struct OperationState {
    identity: Rc<()>,
    depth: Cell<usize>,
}

impl OperationState {
    fn is_active(&self) -> bool {
        self.depth.get() != 0
    }
}

/// A local cache belongs to one operation and one program environment.
#[derive(Clone, Debug)]
pub(super) struct TypeOperationIdentity {
    owner: Rc<()>,
    program: salsa::Id,
}

impl PartialEq for TypeOperationIdentity {
    fn eq(&self, other: &Self) -> bool {
        Rc::ptr_eq(&self.owner, &other.owner) && self.program == other.program
    }
}

impl Eq for TypeOperationIdentity {}

/// Restores the enclosing guard scope even when recursive analysis unwinds.
#[must_use]
pub(super) struct RecursiveOperationScope<'guard, 'db> {
    context: TypeRecursionContext<'db>,
    previous: usize,
    _guard: GuardToken<'guard>,
}

impl Drop for RecursiveOperationScope<'_, '_> {
    fn drop(&mut self) {
        self.context.state().operation.depth.set(self.previous);
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
