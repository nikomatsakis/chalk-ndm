use crate::cast::{Cast, CastTo, Caster};
use crate::clauses::importer::Importer;
use crate::RustIrDatabase;
use chalk_ir::family::{ChalkIr, HasTypeFamily, TypeFamily};
use chalk_ir::fold::Fold;
use chalk_ir::*;
use chalk_rust_ir::*;
use std::marker::PhantomData;

/// The "clause builder" is a useful tool for building up sets of
/// program clauses. It takes ownership of the output vector while it
/// lasts, and offers methods like `push_clause` and so forth to
/// append to it.
///
/// The clauses will be built in the target type family `TTF`. Any
/// projection types found in the input will be converted into
/// `ProjectionEq` relations.
pub struct ClauseBuilder<'me, TTF: TypeFamily> {
    pub db: &'me dyn RustIrDatabase,
    clauses: &'me mut Vec<ProgramClause<TTF>>,
    binders: Vec<ParameterKind<()>>,
    parameters: Vec<Parameter<ChalkIr>>,
}

impl<'me, TTF> ClauseBuilder<'me, TTF>
where
    TTF: TypeFamily,
{
    pub fn new(db: &'me dyn RustIrDatabase, clauses: &'me mut Vec<ProgramClause<TTF>>) -> Self {
        Self {
            db,
            clauses,
            binders: vec![],
            parameters: vec![],
        }
    }

    /// Pushes a "fact" `forall<..> { consequence }` into the set of
    /// program clauses, meaning something that we can assume to be
    /// true unconditionally. The `forall<..>` binders will be
    /// whichever binders have been pushed (see `push_binders`).
    pub fn push_fact(&mut self, consequence: impl CastTo<DomainGoal<ChalkIr>>) {
        self.push_clause(consequence, None::<Goal<_>>);
    }

    fn import<T: Fold<ChalkIr, TTF>>(
        &mut self,
        value: &T,
        conditions: &mut Vec<Goal<TTF>>,
    ) -> T::Result {
        let importer = &mut Importer::new(&mut self.binders, conditions);
        value.fold_with(importer, 0).unwrap()
    }

    /// Pushes a clause `forall<..> { consequence :- conditions }`
    /// into the set of program clauses, meaning that `consequence`
    /// can be proven if `conditions` are all true.  The `forall<..>`
    /// binders will be whichever binders have been pushed (see `push_binders`).
    pub fn push_clause(
        &mut self,
        in_consequence: impl CastTo<DomainGoal<ChalkIr>>,
        in_conditions: impl IntoIterator<Item = impl CastTo<Goal<ChalkIr>>>,
    ) {
        // the "importing" actions below can push binders, so save the
        // length before we enter
        let old_binders_len = self.binders.len();

        let mut out_conditions = vec![];
        let out_consequence = self.import(&in_consequence.cast(), &mut out_conditions);
        for in_condition in in_conditions.into_iter().casted() {
            let out_condition = self.import(&in_condition, &mut out_conditions);
            out_conditions.push(out_condition);
        }
        let clause = ProgramClauseImplication {
            consequence: out_consequence,
            conditions: out_conditions,
        };

        if self.binders.len() == 0 {
            self.clauses.push(ProgramClause::Implies(clause));
        } else {
            self.clauses.push(ProgramClause::ForAll(Binders {
                binders: self.binders.clone(),
                value: clause,
            }));
        }

        debug!("pushed clause {:?}", self.clauses.last());

        self.binders.truncate(old_binders_len);
    }

    /// Accesses the placeholders for the current list of parameters in scope.
    pub fn placeholders_in_scope(&self) -> &[Parameter<ChalkIr>] {
        &self.parameters
    }

    /// Executes `op` with the `binders` in-scope; `op` is invoked
    /// with the bound value `v` as a parameter. After `op` finishes,
    /// the binders are popped from scope.
    ///
    /// The new binders are always pushed onto the end of the internal
    /// list of binders; this means that any extant values where were
    /// created referencing the *old* list of binders are still valid.
    pub fn push_binders<V>(&mut self, binders: &Binders<V>, op: impl FnOnce(&mut Self, V::Result))
    where
        V: Fold<ChalkIr, ChalkIr> + HasTypeFamily<TypeFamily = ChalkIr>,
    {
        let old_len = self.binders.len();
        self.binders.extend(binders.binders.clone());
        self.parameters.extend(
            binders
                .binders
                .iter()
                .zip(old_len..)
                .map(|p| p.to_parameter()),
        );

        let value = binders.substitute(&self.parameters[old_len..]);
        op(self, value);

        self.binders.truncate(old_len);
        self.parameters.truncate(old_len);
    }

    /// Push a single binder, for a type, at the end of the binder
    /// list.  The indices of previously bound variables are
    /// unaffected and hence the context remains usable. Invokes `op`,
    /// passing a type representing this new type variable in as an
    /// argument.
    #[allow(dead_code)]
    pub fn push_bound_ty(&mut self, op: impl FnOnce(&mut Self, Ty<ChalkIr>)) {
        let binders = Binders {
            binders: vec![ParameterKind::Ty(())],
            value: PhantomData::<ChalkIr>,
        };
        self.push_binders(&binders, |this, PhantomData| {
            let ty = this
                .placeholders_in_scope()
                .last()
                .unwrap()
                .assert_ty_ref()
                .clone();
            op(this, ty)
        });
    }
}
