//! Entry points for semantic type operations and the state borrowed by their recursive helpers.

use super::{ApplyTypeMappingVisitor, Type, TypeRecursionContext};
use crate::{Db, ProgramEnvironment};

/// Access to semantic operations within one active computation.
///
/// Helpers borrow this object instead of choosing whether to preserve a caller's recursion
/// state. Structural transformations use its mapping visitor; semantic comparisons and body
/// inspection retain the same context.
pub(crate) struct TypeOperations<'op, 'db> {
    db: &'db dyn Db,
    env: &'op ProgramEnvironment<'db>,
    context: &'op TypeRecursionContext<'db>,
}

impl<'db> TypeOperations<'_, 'db> {
    /// Start an independent operation at an inference or inspection boundary.
    pub(super) fn with_root<R>(
        db: &'db dyn Db,
        env: &ProgramEnvironment<'db>,
        run: impl FnOnce(&TypeOperations<'_, 'db>) -> R,
    ) -> R {
        let context = TypeRecursionContext::default();
        run(&TypeOperations {
            db,
            env,
            context: &context,
        })
    }

    /// Negate a type while retaining the surrounding operation's active comparisons.
    pub(super) fn negate(&self, ty: Type<'db>) -> Type<'db> {
        ty.negate_with_recursion(self.db, self.env, self.context)
    }

    /// Start a mapping whose caches belong to this transformation and whose guards remain shared.
    pub(super) fn mapping(&self) -> ApplyTypeMappingVisitor<'_, 'db> {
        ApplyTypeMappingVisitor::new(self.env).with_recursion_context(self.context)
    }

    pub(super) fn context(&self) -> &TypeRecursionContext<'db> {
        self.context
    }
}
