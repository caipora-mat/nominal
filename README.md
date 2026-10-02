# Nominal Sets in Lean 4

A Lean 4 / Mathlib formalization of nominal set theory following Pitts' *Nominal Sets* (CUP 2013).

See [the roadmap and progress tracker](docs/roadmap.md) for task status, dependencies,
nominal-function ergonomics, and the path to a lambda-calculus Church–Rosser case study.

## Toolchain

Lean v4.34.1 / Mathlib v4.34.1

## Project Structure

```
Nominal.lean              # top-level: imports Core + Set
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
    EquivalenceClass.lean # equivariant quotients and their nominal structure
    Freshness.lean        # re-exports Freshness.*
    Freshness/
      Basic.lean          # Fresh (#) relation
      Tactic.lean         # choose_fresh and split_fresh tactics
    NFun.lean             # compatibility umbrella for NFun.Basic + NFun.Tactic
    NFun/
      Basic.lean         # finitely supported functions and proof-backed constructors
      Tactic.lean        # support tactic and experimental nfun macro
    FreshQuantifier.lean  # И quantifier; someAny (Pitts 3.9)
    NameAbstraction.lean  # NameAbs ([A]X); abs / ⟪a⟫ x; supp_abs
    Concretion.lean       # concreteAt (⊙); liftAbs; Prop. 4.9; ext
    FCB.lean              # FCB / liftFCB (Thm 4.15); liftFresh (Cor 4.17)
Instances.lean            # lambda-calculus case-study umbrella
Instances/
  LambdaCalculus.lean     # imports all four case-study modules
  LambdaCalculus/
    Basic.lean           # alpha quotient, action, support/free variables
    Induction.lean       # strong induction with fresh binders
    Recursion.lean       # supported-handler iteration
    Substitution.lean    # capture-avoiding substitution and composition
```

## Key API

| Concept | Type | Key lemmas |
|---|---|---|
| Atoms | `Name α` | — |
| Finite perms | `FinitePerm α` | `swap_factorization`, `eq_closure_isSwap` |
| Perm-set | `PermType α X` | instances for atoms, products, `Option`, `Finset`, `PFun` |
| Transposition | `swap a b` | `swap_smul_eq_of_not_mem`, `movedFinset_swap_smul_subset` |
| Equivariance | `Equivariant α X Y` | `MulActionHom (FinitePerm α) X Y` |
| Support | `supports s x` | `supports_iff_swap` (Pitts 2.1), `supports_inter`, `supports_smul` |
| Nominal set | `Nominal α X`, `supp x` | `supp_supports`, `supp_le`, `supp_equivariant`, `supp_atom`, `supp_prod` |
| Freshness | `x # y` | `fresh_atom_left`, `fresh_swap`, `fresh_prod_right`, `exists_fresh_atom` |
| Fresh quant. | `И a, ϕ a` | `someAny` (Pitts 3.9), `freshQuantifier_and` |
| FS functions | `NFun α X Y` | `supp_apply_le`, `fresh_apply` |
| Name abs. | `NameAbs α X`, `⟪a⟫ x` | `abs_eq_iff` (Lemma 4.3), `supp_abs` (Prop. 4.5), `fresh_abs` |
| Concretion | `F ⊙ a` | `concreteAt_abs_self/fresh/not_fresh`, `abs_concreteAt_eq` (Prop. 4.9), `nameAbs_ext` (4.16) |
| Functor | `liftAbs hf` | `liftAbs_abs`, `liftAbs_unique`, `liftAbs_id`, `liftAbs_comp` |
| FCB | `FCB F`, `liftFCB` | `liftFCB_abs` (4.33), `liftFCB_abs_of_fresh`, `supp_liftFCB_le`, `liftFCB_unique` |
| Elim. principle | `liftFresh f` | `liftFresh_abs`, `liftFresh_equivariant`, `liftFresh_unique` |

**Design note:** `PFun α X Y` wraps `X → Y` with the conjugation action to avoid a diamond with Mathlib's `Pi.instSMul`.

The `nfun` macro is experimental: global identifiers and `let`/`match`/nested-function
scopes have known failures. Its explicit capture syntax is
`nfun [capturing a b c] fun x => body`. Use `NFun.equivariant`, `NFun.ofSupports`, or
`NFun.ofCaptures` with explicit proofs when the macro is unsuitable.
The lambda case study currently reaches substitution; reduction and Church–Rosser
remain roadmap work.

The separate raw `Nominal.Syntax` sketch is excluded from this branch for now.

## Build

```bash
lake build
# Explicit equivalent: build both supported libraries.
lake build Nominal Instances
```

The default build covers both `Nominal` and `Instances`, including the NFun tactic
module and all four lambda-calculus modules.

## Freshness tactic regressions

```bash
lake build Examples
# Directly elaborate the regression file:
lake env lean Examples/Freshness.lean
# Validate both supported libraries and the regressions together:
lake build Nominal Instances Examples
```

[Examples/Freshness.lean](Examples/Freshness.lean) tests automatic and explicit
freshness selection, shadowing, derived instances, ambiguity, nested splitting,
and diagnostics. Its axiom audit rejects admissions and dependencies beyond the
standard `propext`, `Classical.choice`, and `Quot.sound` foundations.

`choose_fresh a` scans eligible locals using instance synthesis;
`choose_fresh a from X x` mixes type expansion and explicit terms. Generated names
are always indexed: `aFresh1`, `aFresh2`, …, or `h1`, `h2`, … with `with h`.
`split_fresh h` recursively splits products into `h_1`, `h_2`, …, skipping occupied
names. Its `with` form requires one distinct, unused name per leaf. See the
[tactic documentation](Nominal/Set/Freshness/Tactic.lean) for ordering, filtering,
atom-sort selection, and failure behavior.

## References

- A. M. Pitts, *Nominal Sets: Names and Symmetry in Computer Science*, CUP 2013.
- V. Choudhury, nominal sets in Agda.
- D. Paranhos, nominal sets in Rocq.
