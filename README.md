# Nominal Sets in Lean 4

A formalization of **nominal set theory** in Lean 4

## Goals

1. **Formalize nominal set theory**: atoms, finite permutations, permutation actions,
   finite support, nominal sets, freshness, equivariance, name abstraction, concretion,
   and alpha-equivalence.

2. **Nominal inductive types via metaprogramming (TODO FUTURE)**: use Lean 4's `Elab`/`Meta` framework
   to automatically derive nominal datatypes (à la Isabelle's `nominal_datatype`),
   including permutation actions, nominal instances, alpha-equivalence relations, and
   alpha-structural induction/recursion principles.

## Toolchain

Lean v4.28.0

## Project Structure

```
NominalSets.lean
NominalSets/
  Wheels.lean                 # Utility lemmas and the pick_new tactic
  Name.lean                   # Name typeclass: DecidableEq + Infinite
  FinitePerm.lean             # FinitePerm α subgroup of Equiv.Perm α
  PermType.lean               # PermType typeclass, instances, movedFinset
  Swap.lean                   # swap (transposition), structural swap lemmas
  Equivariant.lean            # Equivariant functions (MulActionHom wrapper)
  Support.lean                # supports, FinSupported, Pitts Prop. 2.1
  Nominal.lean                # Nominal typeclass, supp (least support)
```

## Core Concepts

### Atoms — `Name α`

Any type `α` with `DecidableEq` and `Infinite` can serve as the atom type.

### Finite Permutations — `FinitePerm α`

`FinitePerm α` is the subgroup of `Equiv.Perm α` consisting of permutations that
move only finitely many atoms. Mathlib's `Equiv.Perm.support` requires a `Fintype`
instance, so this library uses `Set.Finite` on the moved-point set directly.

Key facts:
- Every transposition belongs to `FinitePerm α` (`FinitePerm.swap_finite`).
- `FinitePerm α` equals the closure of all transpositions (`eq_closure_isSwap`).
- Every element factors as a finite product of transpositions (`swap_factorization`).

### Permutation Types — `PermType α X`

A **permutation type** (Perm-set) is a type `X` with a `FinitePerm α`-action.

Instances:
- `instAtoms` — atoms act on themselves: `π • a = π a`.
- `instProd` — component-wise action on `X × Y`.
- `instOption` — `Option X` acts fixing `none` and acting on `some x`.
- `instFinset` — image action on `Finset α`: `π • s = s.image π`.
- `PFun.instPermType` — conjugation action `(π • f) x = π • f (π⁻¹ • x)`.

The function action is placed on the newtype `PFun α X Y` (a wrapper around `X → Y`)
to avoid a diamond with Mathlib's pointwise `Pi.instSMul`.

### Transpositions — `swap`

`swap a b : FinitePerm α` is the bundled transposition of atoms `a` and `b`.

Key lemmas:
- `swapFP_fixes_of_not_mem` — a swap of atoms outside `s` fixes every element of `s`.
- `swap_self` — `swap a a = 1`.
- `movedFinset_swap_smul_subset` — left-composing `swap a (σ a)` strictly shrinks
  the moved-point set of `σ`.
- `swap_triple_factorization` — `swap a a' = swap a a'' * swap a' a'' * swap a a''`
  for distinct `a`, `a'`, `a''`.

### Equivariant Functions — `Equivariant α X Y`

An **equivariant function** between two permutation types is one that commutes with the
group action: `f (π • x) = π • f x`. This is an abbreviation for `MulActionHom
(FinitePerm α) X Y`.

### Support — `supports`, `FinSupported`

A finset `s` **supports** `x` if every permutation fixing `s` pointwise also fixes `x`.

Key results:
- **Pitts, Prop. 2.1** (`supports_iff_swap`) — `s` supports `x` iff every transposition
  of two atoms outside `s` fixes `x`.
- `supports_inter` — the intersection of two finite supports is a support.
- `supports_smul` — if `s` supports `x`, then `π • s` supports `π • x`.

### Nominal Sets — `Nominal α X`, `supp`

A **nominal set** is a permutation type in which every element has finite support.

Nominal instances: atoms, products, `Option X`, `Finset α`.

The **least support** `supp x : Finset α` is the intersection of all finite supports.

Key results:
- `mem_supp` — `a ∈ supp x ↔ ∀ s, supports s x → a ∈ s`.
- `supp_supports` — `supp x` supports `x`.
- `supp_le` — `supp x ⊆ s` for every finite support `s`.
- `supp_equivariant` — `π • supp x = supp (π • x)`.
- `supp_eq_empty_iff` — `supp x = ∅ ↔ ∀ π, π • x = x`.
- `supp_prod` — `supp (x, y) = supp x ∪ supp y`.

## Build

```bash
# Full build
lake build

# Single file
lake build NominalSets.Nominal

# Clean rebuild
lake clean && lake build
```

## Design Notes

### Atom type parametricity

All definitions are parametric in the atom type `α` via `Name α`. Any infinite type with
decidable equality qualifies, matching the standard presentation in Pitts' book.

## References

- A. M. Pitts, *Nominal Sets: Names and Symmetry in Computer Science*, CUP 2013.
- V. Choudhury, nominal sets in Agda (constructive).
- D. Paranhos, nominal sets in Rocq (constructive).