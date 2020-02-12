/*!

The "syntactic equality" lowering converts Rust *semantic* type
equality into *syntactic* type equality.

## Syntactic vs semantic equality

So, what is the difference between syntactic vs semantic equality?
Glad you asked!

* *Semantic* type equality means that the types are equivalent for
  Rust programmers.

* *Syntactic* type equality means that the types are written using the
  same tokens.

Syntactic equality is a subset of semantic of equality -- that is, if
two types are syntactically equal, then they must be **semantically**
equal. But it is also possible for types that are written differently
to be equivalent.

Examples of the some of the ways that semantic equality can differ
from syntactic equality:

* **Lifetime relationships:** `&'a T` and `&'b T` are equivalent if `'a: 'b` and `'b: 'a`
* **Higher-ranked types:** `for<'a, 'b> fn(&'a u32, &'b u32)` and `for<'a, 'b> fn(&'b u32, &'a u32)` are equivalent
* **Associated type normalization:** `<vec::IntoIter<u32> as Iterator>::Item` and `u32` are equivalent

## The transformation this module performs

This module takes **program clauses** and **goals** and converts them
so they require only **syntactic equality**. It does this by
introducing sub-goals for cases where semantic equality may diverge.

### Example: transforming a program clause with repeated lifetimes

Consider the following trait/impl:

```rust
trait SomeTrait<T> { }
impl<'a> SomeTrait<&'a u32> for &'a u32 { }
```

The equivalent program clause for this impl would be:

```notrust
forall<'a> {
    Implemented(&'a u32: SomeTrait<&'a u32>)
}
```

This program clause, however, assumes *semantic equality* -- that is,
it uses `'a` in two places, but it isn't really necessary to have the
*same regions* in both places. It suffices to have any two regions
which outlive one another.

We can convert this program clause into a syntactic clause by
introducing a fresh region `'b`, along with a `Equal` subgoals:

```notrust
forall<'a, 'b> {
    Implemented(&'a u32: SomeTrait<&'b u32>) :-
        Equal('a = 'b)
}
```

The `Equal` goal is built-in to the system and implements *semantic
equality*. `Equal('a = 'b)` is provable if `Outlives('a: 'b`),
Outlives('b: 'a)` is provable.

### Example: transforming a program clause with associated types

Consider the following trait/impl:

```rust
trait SomeTrait<T> { }
impl<T: Iterator> SomeTrait<T::Item> for T { }
```

The equivalent program clause for this impl would be:

```notrust
forall<T> {
    Implemented(T: SomeTrait<<T as Iterator>::Item>) :-
        Implemented(T: Iterator)
}
```

Again, this assumes semantic equality, as it contains `<T as
Iterator>::Item`, but we expect this rule to apply to **any type `U`
where `T::Item` normalizes to `U`**.

We can express this same concept using only syntactic equality like
so:

```notrust
forall<T, U> {
    Implemented(T: SomeTrait<U>) :-
        Implemented(T: Iterator),
        Equal(<T as Iterator>::Item = U)
}
```

The pattern should look familiar: we just introduce a variable and add
a new `Equal` subgoal to capture semantic equality. `Equal` on a
projection type will ultimately lead to a `ProjectionEq` subgoal.

### Example: transforming a goal with associated types

Continuing the previous example, imagine that we have a **goal** that
we would like to prove, and that goal is expressed with **semantic**
equality. For example, perhaps we are type-checking a call `foo::<X>` to this function:

```rust
fn foo<T>()
where
    T: Iterator,
    T: SomeTrait<T::Item>
{ }
```

In that case, we have to prove `Implemented(X: Iterator)` but also:

```notrust
Implemented(X: SomeTrait<<X as Iterator>::Item>)
````

This goal assumes semantic equality. We can transform it goal into syntatic equality like so:

```notrust
exists<U> {
    Implemented(X: SomeTrait<U>),
    Equal(<X as Iterator>::Item = U),
}
```

### Generalizing: the rules to convert from syntactic to semantic equality

The general rules for converting from syntactic to semantic equality
are as follows. First, we identify a set of parameters that require
semantic equality. For each, we'll also have an associated set of
goal(s) that express semantic equality. Let's call them "SemEq"
parameters:

* All lifetimes
* Function types, owing to their binders
* Alias types

The rule to convert a **program clause** can then be expressed like so:

* For a program clause `forall<X0..Xx> { DG(P0..Pn) :- Goal0, .., GoalN }`:
  * Replace each SemEq parameter `Pi` with a new variable `Y`
  * Add a subgoal `Equate(Pi, Y)`

Therefore, if *all* of the parameters `P0..Pn` were SemEq parameters, the result would be:

```notrust
forall<X0..Xx, Y0..Yn> {
    DG(Y0..Yn) :-
        Goal0, .., GoalN,
        Equal(Y0 = P0), ..., Equal(Yn = Pn)
}
```

The rule `SemEq(G)` to convert a **goal** `G` can be expressed like so:

* For a non-domain goal, recursively convert the subgoals
  * e.g., `G1, G2` becomes `SemEq(G1), SemEq(G2)`
* For a domain goal `DG(P0..Pn)` where some of the parameters `P` are SemEq parameters:
  * Replace each SemEq parameter `Pi` with a new variable `Y`
  * Replace with the goal `exists<Y...> { DG(..), Equate(Pi.. = Yi..) }`

Therefore, if *all* of the parameters `P0..Pn` were SemEq parameters, the result would be:

```notrust
exists<Y0..Yn> {
    DG(Y0..Yn),
    Equal(Y0 = P0), ..., Equal(Yn = Pn)
}
```

*/

pub struct SyntacticEquality<SemTF: TypeFamily, SynTF: TargetTypeFamily<SemTF>> {
    db: &'me dyn RustIrDatabase<TF>,
}

impl<SemTF, SynTF> Folder<SemTF, SynTF> for SyntacticEquality<SemTF, SynTF>
where
    SemTF: TypeFamily,
    SynTF: TargetTypeFamily<SemTF>,
{
    fn fold_goal(&mut self, goal_sem: &Goal<SemTF>, binders: usize) -> Fallible<Goal<SynTF>> {
        if let GoalData::DomainGoal(domain_goal_sem) = goal_sem {
            Ok(self.lower_domain_goal(domain_goal_sem, binders))
        } else {
            goal_sem.super_fold_with(self, binders)
        }
    }

    fn fold_program_clause(
        &mut self,
        pc_sem: &ProgramClause<SemTF>,
        binders: usize,
    ) -> Fallible<Goal<SynTF>> {
        Ok(self.lower_clause(pc_sem, binders))
    }
}

impl<SemTF, SynTF> SyntacticEquality<SemTF, SynTF>
where
    SemTF: TypeFamily,
    SynTF: TargetTypeFamily<SemTF>,
{
    fn lower_domain_goal(
        &mut self,
        domain_goal_sem: &DomainGoal<SemTF>,
        binders: &mut Vec<ParameterKind<()>>,
    ) -> Goal<SynTF> {
        // As noted above, the transformation here is
        //
        // Foo<T0>
        //
        // to
        //
        // exists<X> {
        //   Foo<X>, Equal(T0, X)
        // }

        let mut equate_goals = vec![];
    }

    fn lower_clause(
        &mut self,
        pc_sem: &ProgramClause<SemTF>,
        binders: usize,
    ) -> ProgramClause<SynTF> {
        let (mut binders, implication_sem) = match pc_sem {
            ProgramClause::Implies(pci) => (vec![], pci),
            ProgramClause::ForAll(binders) => (binders.binders.clone(), binders.value),
        };

        let implication_syn = self.lower_clause_implication(&mut binders, implication_sem);
        if binders.is_empty() {
            ProgramClause::Implies(implication_syn)
        } else {
            ProgramClause::ForAll(Binders {
                binders,
                value: implication_syn,
            })
        }
    }

    fn lower_clause_implication(
        &mut self,
        binders: &mut Vec<ParameterKind<()>>,
        implication_sem: &ProgramClauseImplication<SemTF>,
    ) -> ProgramClauseImplication<SynTF> {
        let mut equate_goals = vec![];

        // Managing the debruijn indices here is a bit tricky.
        //
        // ..... forall<X0..., [Y0...]> { consequence :- conditions }
        // ^^^^^        ^^^^^  ^^^^^^^
        // |            |      |
        // |            |      new variables we will introduce for SemEq parameters
        // |            existing contents of `binders`
        // various other bindings that may be in outer scopes

        let (consequence_syn, conditions_sem) = self.replace_semeq_parameters(
            binders,
            &mut equate_goals,
            &implication_sem.consequence,
            &implication_sem.conditions,
        );

        let conditions_syn: Vec<Goal<SynTF>> = implication_sem
            .conditions
            .iter()
            .map(|condition_sem| self.lower_goal(condition_sem))
            .collect();

        ProgramClauseImplication {
            consequence: consequence_syn,
            conditions: conditions_syn,
        }
    }
}
