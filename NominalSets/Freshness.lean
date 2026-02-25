import NominalSets.Nominal

import Mathlib.Data.Finset.Disjoint

/-!
# Freshness

The **freshness** relation between elements of nominal sets formalises the notion of
"having nothing in common" or "being independent." Given two elements `x : X` and
`y : Y` of nominal sets over the same atom type `α`, we write `x # y` to mean
that their least supports are disjoint: `Disjoint (supp x) (supp y)`.

When one of the arguments is an atom `a : α`, freshness reduces to non-membership:
`a # x ↔ a ∉ supp x`.

## Main definitions

* `Fresh x y` — `Disjoint (supp x) (supp y)`.
* `x # y` — scoped notation for `Fresh x y`.
* `choose_fresh a from x₁ x₂ … xₙ` — tactic: picks an atom `a` fresh for all `xᵢ`,
  introducing individual freshness hypotheses into the local context.

## Main results

* `fresh_comm` — freshness is symmetric.
* `fresh_equivariant` — freshness is preserved by the permutation action.
* `fresh_swap` — swapping two atoms that are both fresh for `x` fixes `x`.
* `fresh_prod_right` — freshness distributes over products on the right.
* `fresh_prod_left` — freshness distributes over products on the left.
* `fresh_atom_left` — `a # x ↔ a ∉ supp x`.
* `fresh_atoms` — `a # b ↔ a ≠ b` for atoms.
* `exists_fresh_atom` — for every `x`, there exists an atom fresh for it.
* `fresh_of_not_mem_support` — atoms outside a support are fresh.
* `fresh_atom_cofinite` — the set of atoms fresh for `x` is cofinite.
* `fresh_of_supp_empty` — elements with empty support are fresh for every atom.
* `fresh_atom_finset` — `a # A ↔ a ∉ A` for a finite set of atoms `A`.
* `fresh_finset` — `A # B ↔ Disjoint A B` for finite sets of atoms.

## References

* [A. M. Pitts, *Nominal Sets*][Pitts2013], Chapter 3.
-/

namespace NominalSets

open MulAction

variable {α : Type*} [Name α]

/-! ### Freshness -/

section Fresh

variable {X Y Z : Type*} [Nominal α X] [Nominal α Y] [Nominal α Z]

/-- Two elements are **fresh** for each other if their least supports are disjoint. -/
def Fresh (x : X) (y : Y) : Prop := Disjoint (supp x) (supp y)

scoped infix:50 " # " => Fresh

/-- Unfold `Fresh` to disjointness of supports. -/
theorem fresh_iff {x : X} {y : Y} : x # y ↔ Disjoint (supp x) (supp y) :=
  Iff.rfl

/-- Freshness is symmetric. -/
theorem fresh_comm {x : X} {y : Y} : x # y ↔ y # x := by
  simp only [Fresh, disjoint_comm]

/-- Freshness is preserved by the permutation action. -/
theorem fresh_equivariant (π : FinitePerm α) {x : X} {y : Y}
    (h : x # y) : (π • x) # (π • y) := by
  rw [Fresh, ← supp_equivariant, ← supp_equivariant]
  rw [Fresh] at h
  rw [Finset.disjoint_left] at h ⊢
  intro a ha hy
  rw [PermType.mem_smul_finset_iff] at ha hy
  exact h ha hy

/-- An atom `a` is fresh for `x` if and only if `a ∉ supp x`. -/
@[simp]
theorem fresh_atom_left (a : α) (x : X) : a # x ↔ a ∉ supp x := by
  simp [Fresh, supp_atom, Finset.disjoint_singleton_left]

/-- `x` is fresh for an atom `a` if and only if `a ∉ supp x`. -/
@[simp]
theorem fresh_atom_right (x : X) (a : α) : x # a ↔ a ∉ supp x := by
  rw [fresh_comm]
  exact fresh_atom_left a x

/-- Two atoms are fresh for each other if and only if they are distinct. -/
@[simp]
theorem fresh_atoms (a b : α) : a # b ↔ a ≠ b := by
  simp [Fresh, supp_atom, Finset.disjoint_singleton_left, Finset.mem_singleton]

/-- If both `a` and `b` are fresh for `x`, then swapping them fixes `x`. -/
theorem fresh_swap {a b : α} {x : X} (ha : a # x) (hb : b # x) : swap a b • x = x := by
  rw [fresh_atom_left] at ha hb
  exact (supports_iff_swap.mp (supp_supports x)) a b ha hb

/-- Freshness distributes over products: `x # (y, z) ↔ x # y ∧ x # z`. -/
theorem fresh_prod_right {x : X} {y : Y} {z : Z} : x # (y, z) ↔ x # y ∧ x # z := by
  simp [Fresh, supp_prod, Finset.disjoint_union_right]

/-- Freshness distributes over products (left): `(x, y) # z ↔ x # z ∧ y # z`. -/
theorem fresh_prod_left {x : X} {y : Y} {z : Z} : (x, y) # z ↔ x # z ∧ y # z := by
  simp [Fresh, supp_prod, Finset.disjoint_union_left]

/-- For every `x` in a nominal set, there exists an atom fresh for it. -/
theorem exists_fresh_atom (x : X) : ∃ a : α, a # x := by
  pick_new a (supp x)
  exact ⟨a, (fresh_atom_left a x).mpr aNew⟩

/-- If `s` supports `x`, any atom outside `s` is fresh for `x`. -/
theorem fresh_of_not_mem_support {s : Finset α} {x : X} (hs : supports s x) {a : α} (ha : a ∉ s) : a # x :=
  (fresh_atom_left a x).mpr (fun hmem ↦ ha (supp_le s hs hmem))

/-- The set of atoms fresh for `x` is cofinite (its complement is `supp x`, which is finite). -/
theorem fresh_atom_cofinite (x : X) : Set.Finite {a : α | ¬ a # x} := by
  apply Set.Finite.subset (Finset.finite_toSet (supp x))
  intro a ha
  simp only [Set.mem_setOf_eq, fresh_atom_left, not_not] at ha
  exact ha

/-- If `x` has empty support, every atom is fresh for it. -/
theorem fresh_of_supp_empty {x : X} (h : supp x = ∅) (a : α) : a # x := by
  simp [Fresh, h]

/-- An atom `a` is fresh for a finite set of atoms `A` if and only if `a ∉ A`. -/
@[simp]
theorem fresh_atom_finset (a : α) (A : Finset α) : a # A ↔ a ∉ A := by
  simp [Fresh, supp_atom, supp_finset, Finset.disjoint_singleton_left]

/-- A finite set of atoms `A` is fresh for `B` if and only if they are disjoint. -/
@[simp]
theorem fresh_finset (A B : Finset α) : A # B ↔ Disjoint A B := by
  simp [Fresh, supp_finset]

end Fresh

end NominalSets
