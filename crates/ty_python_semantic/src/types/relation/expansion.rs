//! Consume deferred bodies while the comparison that opened them remains active.

use crate::Db;
use crate::types::constraints::ConstraintSet;
use crate::types::recursive::{RecursiveType, TypeExpansionContext};
use crate::types::type_alias::TypeAliasType;
use crate::types::{CallableType, Type};

use super::{DisjointnessChecker, TypeRelationChecker};

/// A relation whose pair guard has already been installed.
///
/// Expansion returns a comparison result, never an alias body or signature. This keeps the
/// expanded values inside the comparison that owns their recursion state.
pub(in crate::types) struct GuardedRelation<'op, 'guard, 'env, 'c, 'db> {
    checker: &'op TypeRelationChecker<'env, 'c, 'db>,
    expansion: &'op TypeExpansionContext<'guard, 'env, 'db>,
}

impl<'op, 'guard, 'env, 'c, 'db> GuardedRelation<'op, 'guard, 'env, 'c, 'db> {
    pub(super) fn new(
        checker: &'op TypeRelationChecker<'env, 'c, 'db>,
        expansion: &'op TypeExpansionContext<'guard, 'env, 'db>,
    ) -> Self {
        Self { checker, expansion }
    }

    pub(in crate::types) fn compare_source_alias(
        &self,
        db: &'db dyn Db,
        source: TypeAliasType<'db>,
        target: Type<'db>,
    ) -> ConstraintSet<'db, 'c> {
        self.checker
            .check_type_pair(db, source.value_type(db, self.checker.env), target)
    }

    pub(in crate::types) fn compare_target_alias(
        &self,
        db: &'db dyn Db,
        source: Type<'db>,
        target: TypeAliasType<'db>,
    ) -> ConstraintSet<'db, 'c> {
        self.checker
            .check_type_pair(db, source, target.value_type(db, self.checker.env))
    }

    pub(in crate::types) fn compare_source_recursive(
        &self,
        db: &'db dyn Db,
        source: RecursiveType<'db>,
        target: Type<'db>,
    ) -> ConstraintSet<'db, 'c> {
        let by_arguments = if let Type::Recursive(target) = target {
            self.checker
                .when_recursive_types_relate_by_arguments(db, source, target)
        } else {
            self.checker.never()
        };
        by_arguments.or(db, self.checker.constraints, || {
            self.expansion
                .expand_recursive(db, source)
                .map(|source| self.checker.check_type_pair(db, source, target))
                .unwrap_or(ConstraintSet::from_bool(
                    self.checker.constraints,
                    self.checker.relation.is_assignability(),
                ))
        })
    }

    pub(in crate::types) fn compare_target_recursive(
        &self,
        db: &'db dyn Db,
        source: Type<'db>,
        target: RecursiveType<'db>,
    ) -> ConstraintSet<'db, 'c> {
        self.expansion
            .expand_recursive(db, target)
            .map(|target| self.checker.check_type_pair(db, source, target))
            .unwrap_or(ConstraintSet::from_bool(
                self.checker.constraints,
                self.checker.relation.is_assignability(),
            ))
    }

    pub(in crate::types) fn compare_signatures(
        &self,
        db: &'db dyn Db,
        source: CallableType<'db>,
        target: CallableType<'db>,
    ) -> ConstraintSet<'db, 'c> {
        self.expansion
            .inspect_signatures(db, source, |source| {
                self.expansion
                    .inspect_signatures(db, target, |target| {
                        self.checker
                            .check_callable_signature_pair(db, source, target)
                    })
                    .unwrap_or_else(|| self.checker.never())
            })
            .unwrap_or_else(|| self.checker.never())
    }
}

/// Disjointness has a different cycle policy from subtyping, but the same expansion boundary.
pub(super) struct GuardedDisjointness<'op, 'guard, 'env, 'c, 'db> {
    checker: &'op DisjointnessChecker<'env, 'c, 'db>,
    expansion: &'op TypeExpansionContext<'guard, 'env, 'db>,
}

impl<'op, 'guard, 'env, 'c, 'db> GuardedDisjointness<'op, 'guard, 'env, 'c, 'db> {
    pub(super) fn new(
        checker: &'op DisjointnessChecker<'env, 'c, 'db>,
        expansion: &'op TypeExpansionContext<'guard, 'env, 'db>,
    ) -> Self {
        Self { checker, expansion }
    }

    pub(super) fn compare_source_alias(
        &self,
        db: &'db dyn Db,
        source: TypeAliasType<'db>,
        target: Type<'db>,
    ) -> ConstraintSet<'db, 'c> {
        self.checker
            .check_type_pair(db, source.value_type(db, self.checker.env), target)
    }

    pub(super) fn compare_target_alias(
        &self,
        db: &'db dyn Db,
        source: Type<'db>,
        target: TypeAliasType<'db>,
    ) -> ConstraintSet<'db, 'c> {
        self.checker
            .check_type_pair(db, source, target.value_type(db, self.checker.env))
    }

    pub(super) fn compare_source_recursive(
        &self,
        db: &'db dyn Db,
        source: RecursiveType<'db>,
        target: Type<'db>,
    ) -> ConstraintSet<'db, 'c> {
        self.expansion
            .expand_recursive(db, source)
            .map(|source| self.checker.check_type_pair(db, source, target))
            .unwrap_or(self.checker.never())
    }

    pub(super) fn compare_target_recursive(
        &self,
        db: &'db dyn Db,
        source: Type<'db>,
        target: RecursiveType<'db>,
    ) -> ConstraintSet<'db, 'c> {
        self.expansion
            .expand_recursive(db, target)
            .map(|target| self.checker.check_type_pair(db, source, target))
            .unwrap_or(self.checker.never())
    }
}
