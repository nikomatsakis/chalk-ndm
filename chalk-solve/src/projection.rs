//! Logic for dealing with

use crate::cast::Cast;
use chalk_engine::fallible::Fallible;
use chalk_ir::family::{ChalkIr, TypeFamily};
use chalk_ir::fold::shift::Shift;
use chalk_ir::fold::{
    DefaultFreeVarFolder, DefaultInferenceFolder, DefaultPlaceholderFolder, Fold, TypeFolder,
};
use chalk_ir::*;

/// The "importer" imports a type or goal into the program clause
/// being built (which is in the type family TTF). Its main job is to
/// convert projection types into variables and `ProjectionEq`
/// goals. For this, it takes mutable references to the binders for
/// the clause along with the list of conditions being built.
///
/// # Example
///
/// Suppose we were importing `Implemented(A: Foo<<B as
/// Iterator>::Item)`.  We would create a fresh variable `C` for `<B
/// as Iterator>::Item`, and return `Implemented(A: Foo<C>)`. We would
/// also create a new condition
///
/// ```ignore
/// ProjectionEq(<B as Iterator>::Item = C)
/// ```
///
/// # Note on creating binders
///
/// The importer pushes new binders onto the end of the list. This is
/// convenient because it doesn't disturb the de Bruijn indices of
/// existing variables. Effectively we are adding "outer" binders to
/// the term being folder (i.e., if in our example we are folding
/// `forall<B> forall<A> ...` we are sort of creating `forall<C>
/// forall<B> forall<A>`, except that all variables are actually part
/// of the same `forall`).
pub struct GoalImporter<'me, TTF: TypeFamily> {
    counter: ProjectionCounter<ChalkIr>,
    projections_converted: usize,
}

/// Phase 1: We have to count the number of projections we find in the
/// type.
struct ProjectionCounter<TF: TypeFamily> {
    projections_found: usize,
}

impl<TF: TypeFamily> TypeFolder<ChalkIr, TTF> for ProjectionCounter<'_, TF> {
    fn fold_ty(&mut self, ty: &Ty<ChalkIr>, binders: usize) -> Fallible<Ty<TTF>> {
        if let TyData::Projection(_) = ty.data() {
            self.projections_found += 1;
        }
        fold::super_fold_ty(self, ty, binders)
    }

    fn fold_lifetime(
        &mut self,
        lifetime: &Lifetime<ChalkIr>,
        binders: usize,
    ) -> Fallible<Lifetime<TTF>> {
        fold::super_fold_lifetime(self, lifetime, binders)
    }
}

impl<TTF: TypeFamily> DefaultPlaceholderFolder for GoalImporter<'_, TTF> {
    fn forbid() -> bool {
        true
    }
}

impl<TTF: TypeFamily> DefaultFreeVarFolder for GoalImporter<'_, TTF> {
    fn forbid() -> bool {
        true
    }
}

impl<TTF: TypeFamily> DefaultInferenceFolder for GoalImporter<'_, TTF> {
    fn forbid() -> bool {
        true
    }
}

/// Phase 2: We are given a goal like
///
/// ```
/// Implemented(Foo: Bar<^0, <^1 as Iterator>::Item>)
/// ```
///
/// Here, `^0` and `^1` are references to the canonical bindings.
/// We wish to produce a goal like:
///
/// ```
/// exists<type> {
///     Implemented(Foo: Bar<^1, ^0>),
///     ProjectionEq(<^2 as Iterator>::Item = ^0),
/// }
/// ```
///
/// Note that we have to introduce the `exists` binder, which means
/// that the indices of the existing variables were shifted up one (so
/// `^0` became `^1`).
struct ProjectionConverter<TF: TypeFamily, TTF: TypeFamily> {
    projections_found: usize,
    projections_converted: usize,
    projection_eq_goals: Vec<Goal<TTF>>,
}

impl<TF: TypeFamily, TTF: TypeFamily> TypeFolder<TF, TTF> for ProjectionConverter<TF, TTF> {
    fn fold_ty(&mut self, ty: &Ty<TF>, binders: usize) -> Fallible<Ty<TTF>> {
        if let TyData::Projection(_) = ty.data() {
            let projection = projection.fold_with(self, binders).unwrap();
            let new_index = self.projections_converted;
            self.projections_converted += 1;
            assert!(self.projections_converted < self.projections_found);
            let new_ty: Ty<TTF> = TyData::BoundVar(new_index).intern();

            // Careful:
            let projection_eq = ProjectionEq {
                projection: projection.shifted_out(binders).unwrap(),
                ty: new_ty.clone(),
            };
            self.conditions.push(projection_eq.cast());
        }
        fold::super_fold_ty(self, ty, binders)
    }

    fn fold_lifetime(
        &mut self,
        lifetime: &Lifetime<ChalkIr>,
        binders: usize,
    ) -> Fallible<Lifetime<TTF>> {
        fold::super_fold_lifetime(self, lifetime, binders)
    }
}

impl<TTF: TypeFamily> DefaultPlaceholderFolder for GoalImporter<'_, TTF> {
    fn forbid() -> bool {
        true
    }
}

impl<TTF: TypeFamily> DefaultFreeVarFolder for GoalImporter<'_, TTF> {
    fn forbid() -> bool {
        true
    }
}

impl<TTF: TypeFamily> DefaultInferenceFolder for GoalImporter<'_, TTF> {
    fn forbid() -> bool {
        true
    }
}
