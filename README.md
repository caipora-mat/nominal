# Nominal Sets and Nominal Unification in Lean 4

A Lean 4 / Mathlib formalization of nominal set theory following Pitts' *Nominal Sets* (CUP 2013),
together with nominal terms and an executable nominal unification algorithm, proved sound,
complete, principal and equivariant.

## Toolchain

Lean v4.28.0

## Project Structure

```
Nominal.lean              # top-level: imports Core + Set + Syntax
Nominal/
  Wheels.lean             # utility lemmas; pick_new tactic
  Core.lean               # re-exports Core.*
  Core/
    Name.lean             # Name typeclass (DecidableEq + Infinite)
    FinitePerm.lean       # FinitePerm α ≤ Equiv.Perm α
  Set.lean                # re-exports Set.*
  Set/
    PermType.lean         # PermType typeclass + instances
    PFun.lean             # PFun newtype (conjugation action on functions)
    Equivariant.lean      # Equivariant (MulActionHom wrapper)
    Swap.lean             # swap transposition + movedFinset lemmas
    Support.lean          # supports / FinSupported; Pitts Prop. 2.1
    Nominal.lean          # Nominal typeclass; supp; all Nominal instances
    Freshness.lean        # re-exports Freshness.*
    Freshness/
      Basic.lean          # Fresh (#) relation
      Tactic.lean         # choose_fresh tactic
    NFun.lean             # NFun (finitely supported functions)
    FreshQuantifier.lean  # И quantifier; someAny (Pitts 3.9)
    NameAbstraction.lean  # NameAbs ([A]X); abs / ⟪a⟫ x; supp_abs
    Concretion.lean       # concreteAt (⊙); liftAbs; Prop. 4.9; ext
    FCB.lean              # FCB / liftFCB (Thm 4.15); liftFresh (Cor 4.17)
    EquivalenceClass.lean # quotients by equivariant equivalences (Pitts 1.7, 2.9)
  Syntax.lean             # re-exports Syntax.*
  Syntax/
    LPerm.lean            # permutations as lists of swaps
    Terms.lean            # nominal terms (atoms, suspensions, n-ary applications, abstractions)
    Ds.lean               # difference set ds(π, π')
    Fresh.lean            # freshness Γ ⊢ a # t, as a Bool-valued function
    AlphaEquiv/           # α-equivalence Γ ⊢ s ≈α t; equivalence; object-level equivariance
    Substitution/         # simultaneous substitution, composition, idempotence
    Problems/             # constraints, problems, entailment
    Rename.lean           # meta-level renaming of atoms and metavariables (relabel)
    TermsNominal.lean     # terms, contexts and substitutions form nominal sets
    Unification.lean      # re-exports Unification.*
    Unification/
      Basic.lean          # solutions, instantiation ordering (preorder; partial order on the quotient)
      Algorithm.lean      # unify (first stage), finalizeDeferred (second stage), solve
      Algorithm/          # one-step function, termination measure, helpers
      Properties.lean     # soundness
      Completeness.lean   # completeness and principality
      Mgu.lean            # solved form; absorption vs. independent witness
      Equivariance.lean   # solve commutes with renaming of atoms and metavariables
      NominalSet.lean     # solve as a morphism of nominal sets
```

## Key API

| Concept | Type | Key lemmas |
|---|---|---|
| Atoms | `Name α` | — |
| Finite perms | `FinitePerm α` | `swap_factorization`, `eq_closure_isSwap` |
| Perm-set | `PermType α X` | instances for atoms, products, `Option`, `Finset`, `PFun` |
| Transposition | `swap a b` | `swap_smul_eq_of_not_mem`, `movedFinset_swap_smul_subset` |
| Equivariance | `IsEquivariant α f`, `EquivariantRel α R` | `IsEquivariant.comp`, `IsEquivariant.supports_image` |
| Support | `supports s x` | `supports_iff_swap` (Pitts 2.1), `supports_inter`, `supports_smul` |
| Nominal set | `Nominal α X`, `supp x` | `supp_supports`, `supp_le`, `supp_equivariant`, `supp_atom`, `supp_prod` |
| Freshness | `x # y` | `fresh_atom_left`, `fresh_swap`, `fresh_prod_right`, `exists_fresh_atom` |
| Fresh quant. | `И a, ϕ a` | `someAny` (Pitts 3.9), `freshQuantifier_and` |
| FS functions | `NFun α X Y` | `supp_apply_le`, `fresh_apply` |
| Name abs. | `NameAbs α X`, `⟪a⟫ x` | `abs_eq_iff` (Lemma 4.3), `supp_abs` (Prop. 4.5), `fresh_abs` |
| Concretion | `F ⊙ a` | `concreteAt_abs_self/fresh/not_fresh`, `abs_concreteAt_eq` (Prop. 4.9), `nameAbs_ext` (4.16) |
| Functor | `liftAbs f hf` | `liftAbs_abs`, `liftAbs_unique`, `liftAbs_id`, `liftAbs_comp` |
| FCB | `FCB F`, `liftFCB` | `liftFCB_abs` (4.33), `liftFCB_abs_of_fresh`, `supp_liftFCB_le`, `liftFCB_unique` |
| Elim. principle | `liftFresh f` | `liftFresh_abs`, `liftFresh_equivariant`, `liftFresh_unique` |

## Nominal unification

`UnifProblem.solve` takes a list of equations `s ≈? t` and freshness obligations `a #? t` and
returns a freshness context and a substitution, or `none`. It runs in two stages: a terminating
loop that decomposes constraints, instantiates metavariables and defers primitive obligations
`a # X`, followed by a single application of the accumulated (solved-form) substitution to the
deferred obligations. The whole specification is executable.

| Property | Theorem |
|---|---|
| Soundness | `UnifProblem.solve_satisfies` |
| Completeness (decision procedure) | `UnifProblem.solve_none_iff_no_solution` |
| Principality (m.g.u.) | `UnifProblem.solve_principal`, `UnifProblem.solve_le_indep` |
| ≈α is an equivalence | `alphaEquiv_refl`, `alphaEquiv_symm`, `alphaEquiv_trans` |
| Equivariance (atoms and metavariables) | `UnifProblem.solve_relabel`, `UnifProblem.mem_solutions_relabel` |
| Equivariance (atoms) | `UnifProblem.solve_rename`, `UnifProblem.mem_solutions_rename` |
| Equivariance (metavariables) | `UnifProblem.solve_renameVar`, `UnifProblem.solve_rename_renameVar` |
| Morphism of nominal sets | `UnifProblem.solve_isEquivariant`, `ntm.instNominal` |

**Design note:** `PFun α X Y` wraps `X → Y` with the conjugation action to avoid a diamond with Mathlib's `Pi.instSMul`.

## Build

```bash
lake build
```

## References

- A. M. Pitts, *Nominal Sets: Names and Symmetry in Computer Science*, CUP 2013.
- C. Urban, A. M. Pitts, M. J. Gabbay, *Nominal unification*, TCS 323, 2004.
- M. Fernández, M. J. Gabbay, *Nominal rewriting*, Information and Computation 205, 2007.
- V. Choudhury, nominal sets in Agda.
- D. Paranhos, nominal sets in Rocq.
