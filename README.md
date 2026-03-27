# Nominal Sets in Lean 4

A Lean 4 / Mathlib formalization of nominal set theory following Pitts' *Nominal Sets* (CUP 2013).

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
    NFun.lean             # re-exports NFun.*
    NFun/
      Basic.lean          # NFun (finitely supported functions); supp_apply_le
      Tactic.lean         # nfun_ext and related NFun tactics
    FreshQuantifier.lean  # И quantifier; someAny (Pitts 3.9)
    NameAbstraction.lean  # NameAbs ([A]X); abs / ⟪a⟫ x; supp_abs
    Concretion.lean       # concreteAt (⊙); liftAbs; Prop. 4.9; ext
    FCB.lean              # FCB / liftFCB (Thm 4.15); liftFresh (Cor 4.17)
    Structural.lean       # structural isos; SepProd; adjunctions (stubs)
    EquivalenceClass.lean # nominal quotient sets; supp ⟦x⟧ ⊆ supp x
  Syntax.lean             # re-exports Syntax.*
  Syntax/
    LPerm.lean            # λ-calculus permutation syntax
    Terms.lean            # nominal term language
Instances.lean            # top-level instances: imports LambdaCalculus
Instances/
  LambdaCalculus.lean     # re-exports LambdaCalculus.*
  LambdaCalculus/
    Basic.lean            # raw LamTerm α (var/app/lam); PermType instance
    Induction.lean        # strong_ind with freshness side-condition (Barendregt)
    Recursion.lean        # Urban (JAR 2008) recursion combinator on Term α
    Substitution.lean     # capture-avoiding substitution t[x := s]; Urban Lem. 16
    Beta.lean             # beta reduction; parallel reduction; Church-Rosser (WIP)
    Pitts.lean            # Pitts (JACM 2006) ĝ construction (stubs)
```

## Key API

**Atoms** — `Name α`

**Finite perms** — `FinitePerm α` — `swap_factorization`, `eq_closure_isSwap`

**Perm-set** — `PermType α X` — instances for atoms, products, `Option`, `Finset`, `PFun`

**Transposition** — `swap a b` — `swap_smul_eq_of_not_mem`, `movedFinset_swap_smul_subset`

**Equivariance** — `Equivariant α X Y` (`MulActionHom (FinitePerm α) X Y`)

**Support** — `supports s x` — `supports_iff_swap` (Pitts 2.1), `supports_inter`, `supports_smul`

**Nominal set** — `Nominal α X`, `supp x` — `supp_supports`, `supp_le`, `supp_equivariant`, `supp_atom`, `supp_prod`

**Freshness** — `x # y` — `fresh_atom_left`, `fresh_swap`, `fresh_prod_right`, `exists_fresh_atom`

**Fresh quantifier** — `И a, ϕ a` — `someAny` (Pitts 3.9), `freshQuantifier_and`

**FS functions** — `NFun α X Y` — `supp_apply_le`, `fresh_apply`

**Name abstraction** — `NameAbs α X`, `⟪a⟫ x` — `abs_eq_iff` (Lemma 4.3), `supp_abs` (Prop. 4.5), `fresh_abs`

**Concretion** — `F ⊙ a` — `concreteAt_abs_self/fresh/not_fresh`, `abs_concreteAt_eq` (Prop. 4.9), `nameAbs_ext` (4.16)

**Functor** — `liftAbs f hf` — `liftAbs_abs`, `liftAbs_unique`, `liftAbs_id`, `liftAbs_comp`

**FCB** — `FCB F`, `liftFCB` — `liftFCB_abs` (4.33), `liftFCB_abs_of_fresh`, `supp_liftFCB_le`, `liftFCB_unique`

**Elimination principle** — `liftFresh f` — `liftFresh_abs`, `liftFresh_equivariant`, `liftFresh_unique`

**Structural isos** — `absAtomEquiv`, `prodEquiv`, `sumEquiv`, `discreteEquiv`, `expEquiv` — (Pitts 4.12–4.18)

**Nominal quotient** — `Quotient s` (equivariant setoid) — `supp_quotient_le`, `supp_quotient_eq`

**Design note:** `PFun α X Y` wraps `X → Y` with the conjugation action to avoid a diamond with Mathlib's `Pi.instSMul`.

## Build

```bash
lake build
```

## References

- A. M. Pitts, *Nominal Sets: Names and Symmetry in Computer Science*, CUP 2013.
- C. Urban, *Nominal Techniques in Isabelle/HOL*, JAR 2008.
- A. M. Pitts, *Alpha-Structural Recursion and Induction*, JACM 2006.
- V. Choudhury, nominal sets in Agda.
- D. Paranhos, nominal sets in Rocq.
