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
pub struct Importer<'me, TTF: TypeFamily> {
    binders: &'me mut Vec<ParameterKind<()>>,
    conditions: &'me mut Vec<Goal<TTF>>,
}

impl<'me, TTF: TypeFamily> Importer<'me, TTF> {
    pub fn new(
        binders: &'me mut Vec<ParameterKind<()>>,
        conditions: &'me mut Vec<Goal<TTF>>,
    ) -> Self {
        Self {
            binders,
            conditions,
        }
    }
}

impl<TTF: TypeFamily> TypeFolder<ChalkIr, TTF> for Importer<'_, TTF> {
    fn fold_ty(&mut self, ty: &Ty<ChalkIr>, binders: usize) -> Fallible<Ty<TTF>> {
        match ty.data() {
            TyData::Projection(projection) => {
                let projection = projection.fold_with(self, binders).unwrap();
                let new_index = self.binders.len();
                self.binders.push(ParameterKind::Ty(()));
                let new_ty: Ty<TTF> = TyData::BoundVar(new_index).intern();
                let projection_eq = ProjectionEq {
                    projection: projection.shifted_out(binders).unwrap(),
                    ty: new_ty.clone(),
                };
                self.conditions.push(projection_eq.cast());
                Ok(new_ty.shifted_in(binders))
            }

            _ => fold::super_fold_ty(self, ty, binders),
        }
    }

    fn fold_lifetime(
        &mut self,
        lifetime: &Lifetime<ChalkIr>,
        binders: usize,
    ) -> Fallible<Lifetime<TTF>> {
        fold::super_fold_lifetime(self, lifetime, binders)
    }
}

impl<TTF: TypeFamily> DefaultPlaceholderFolder for Importer<'_, TTF> {
    fn forbid() -> bool {
        true
    }
}

impl<TTF: TypeFamily> DefaultFreeVarFolder for Importer<'_, TTF> {
    fn forbid() -> bool {
        // When we fold things with the importer, we start "within"
        // the binders on the clause itself. Therefore, anything bound
        // in the clause itself will be a free variable, so we don't
        // want to forbid free variables.
        false
    }
}

impl<TTF: TypeFamily> DefaultInferenceFolder for Importer<'_, TTF> {
    fn forbid() -> bool {
        true
    }
}
