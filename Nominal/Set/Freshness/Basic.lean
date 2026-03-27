import Nominal.Set.Nominal

import Mathlib.Data.Finset.Disjoint
import Mathlib.Order.Filter.Cofinite
import Mathlib.Data.Finite.Defs

/-!
# Freshness

The **freshness** relation between elements of nominal sets formalises the notion of
"having nothing in common" or "being independent." Given two elements `x : X` and
`y : Y` of nominal sets over the same atom type `α`, we write `x # y` to mean
that their least supports are disjoint: `Disjoint (supp x) (supp y)`.

When one of the arguments is an atom `a : α`, freshness reduces to non-membership: `a # x ↔ a ∉ supp x`.

## Main definitions

* `Fresh x y` — `Disjoint (supp x) (supp y)`.

## Notation

* `x # y` — scoped infix notation for `Fresh x y`.

## Main results

### Basic API
* `fresh_iff` — unfolds `Fresh` to `Disjoint (supp x) (supp y)`.
* `fresh_comm` — freshness is symmetric.
* `fresh_equivariant` — freshness is preserved by the permutation action.
* `fresh_equivariant_iff` — `(π • x) # (π • y) ↔ x # y`.
* `fresh_swap` — swapping two atoms that are both fresh for `x` fixes `x`.
* `fresh_of_swap_eq` — if `a # x` and `swap a b • x = x`, then `b # x`.
* `fresh_prod_right` — `x # (y, z) ↔ x # y ∧ x # z`.
* `fresh_prod_left` — `(x, y) # z ↔ x # z ∧ y # z`.
* `fresh_atom_left` — `a # x ↔ a ∉ supp x`.
* `fresh_atom_right` — `x # a ↔ a ∉ supp x`.
* `fresh_atoms` — `a # b ↔ a ≠ b` for atoms.
* `fresh_finitePerm` — `a # σ ↔ σ a = a` for finite permutations.
* `fresh_finitePerm_right` — `σ # a ↔ σ a = a` for finite permutations.
* `fresh_self_iff` — `x # x ↔ supp x = ∅`.
* `exists_fresh_atom` — for every `x`, there exists an atom fresh for it.
* `exists_fresh_atoms` — for every `x` and `n`, there exist `n` mutually distinct fresh atoms.
* `fresh_of_not_mem_support` — atoms outside a support are fresh.
* `fresh_of_supp_subset` — freshness monotonicity via support containment.
* `fresh_of_equivariant` — equivariant maps preserve freshness (Pitts 3.4(iii)).
* `fresh_of_supp_empty` — elements with empty support are fresh for every atom.
* `fresh_of_supp_empty_left` — elements with empty support are fresh for any nominal element.
* `fresh_of_supp_empty_right` — any nominal element is fresh for elements with empty support.
* `fresh_atom_finset` — `a # A ↔ a ∉ A` for a finite set of atoms `A`.
* `fresh_finset` — `A # B ↔ Disjoint A B` for finite sets of atoms.
* `fresh_none` — every atom is fresh for `none`.
* `fresh_some` — `a # some y ↔ a # y`.
* `fresh_inl` — `a # Sum.inl x ↔ a # x`.
* `fresh_inr` — `a # Sum.inr y ↔ a # y`.
* `equivariantRel_fresh` — the freshness relation is equivariant.
* `not_fresh_iff` — `¬ (a # x) ↔ a ∈ supp x`.
* `fresh_of_supp_subset_left` — freshness monotonicity (left): if `supp x ⊆ supp x'` and `x' # y`, then `x # y`.
* `fresh_smul_left` — `a # (π • x) ↔ (π⁻¹ • a) # x`.
* `fresh_smul_right` — `(π • x) # y ↔ x # (π⁻¹ • y)`.
* `fresh_perm_comm` — fresh permutations commute: if `π # σ`, then `π * σ = σ * π`.
* `fresh_unit` — every element of a nominal set is fresh for `()`.

### Cofinite filter API
* `fresh_atom_compl_eq_supp` — the complement of the fresh-atom set equals `supp x`.
* `fresh_cofinite` — `{a | a # x}` belongs to the cofinite filter.
* `fresh_atom_cofinite` — `∀ᶠ a in cofinite, a # x`.
* `fresh_atom_notin_iff_in_supp` — `w ∈ supp x ↔ w ∉ {a | a # x}`.

## References

* [A. M. Pitts, *Nominal Sets*][Pitts2013], Chapter 3.
-/

namespace Nominal.Set
open Core

open MulAction

variable {α : Type*} [Name α]

/-! ### Freshness -/

section Fresh

variable {X Y Z : Type*} [Nominal α X] [Nominal α Y] [Nominal α Z]

/-- Two elements are **fresh** for each other if their least supports are disjoint. -/
def Fresh (x : X) (y : Y) : Prop := Disjoint (supp x) (supp y)

scoped infix:50 " # " => Fresh

/-- Unfold `Fresh` to disjointness of supports. -/
@[simp]
theorem fresh_iff {x : X} {y : Y} : x # y ↔ Disjoint (supp x) (supp y) :=
  Iff.rfl

/-- Freshness is symmetric. -/
@[grind =]
theorem fresh_comm {x : X} {y : Y} : x # y ↔ y # x := by
  simp only [Fresh, disjoint_comm]

/-- The freshness relation is equivariant. -/
theorem equivariantRel_fresh : EquivariantRel α (Fresh : X → Y → Prop) where
  smul_iff π _ _ := by
    simp only [Fresh, ← supp_equivariant, PermType.finset_smul,
      Finset.disjoint_image (FinitePerm.injective π)]

/-- Freshness is preserved by the permutation action. -/
@[grind .]
theorem fresh_equivariant (π : FinitePerm α) {x : X} {y : Y} (h : x # y) : (π • x) # (π • y) :=
  equivariantRel_fresh.smul π h

/-- Freshness is invariant under the permutation action. -/
@[simp]
theorem fresh_equivariant_iff (π : FinitePerm α) {x : X} {y : Y} : (π • x) # (π • y) ↔ x # y :=
  equivariantRel_fresh.smul_iff' π x y

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

/-- An element is fresh for itself if and only if it has empty support. -/
theorem fresh_self_iff {x : X} : x # x ↔ supp x = ∅ := by
  simp [Fresh, disjoint_self, Finset.bot_eq_empty]

/-- If both `a` and `b` are fresh for `x`, then swapping them fixes `x`. -/
theorem fresh_swap {a b : α} {x : X} (ha : a # x) (hb : b # x) : swap a b • x = x := by
  rw [fresh_atom_left] at ha hb
  exact (supports_iff_swap.mp (supp_supports x)) a b ha hb

/-- If `a # x` and swapping `a` and `b` fixes `x`, then `b # x`.
    Partial converse of `fresh_swap`, derived from equivariance of freshness. -/
theorem fresh_of_swap_eq {a b : α} {x : X}
    (ha : a # x) (hswap : swap a b • x = x) : b # x := by
  have := fresh_equivariant (swap a b) ha
  rwa [swap_apply_left, hswap] at this

/-- Freshness distributes over products: `x # (y, z) ↔ x # y ∧ x # z`. -/
@[simp]
theorem fresh_prod_right {x : X} {y : Y} {z : Z} : x # (y, z) ↔ x # y ∧ x # z := by
  simp [Fresh, supp_prod, Finset.disjoint_union_right]

/-- Freshness distributes over products (left): `(x, y) # z ↔ x # z ∧ y # z`. -/
@[simp]
theorem fresh_prod_left {x : X} {y : Y} {z : Z} : (x, y) # z ↔ x # z ∧ y # z := by
  simp [Fresh, supp_prod, Finset.disjoint_union_left]

/-- For every `x` in a nominal set, there exists an atom fresh for it. -/
theorem exists_fresh_atom (x : X) : ∃ a : α, a # x := by
  pick_new a (supp x)
  exact ⟨a, (fresh_atom_left a x).mpr aNew⟩

/-- If `s` supports `x`, any atom outside `s` is fresh for `x`. -/
@[grind .]
theorem fresh_of_not_mem_support {s : Finset α} {a : α} {x : X}
  (hs : supports s x) (ha : a ∉ s) : a # x := (fresh_atom_left a x).mpr (fun hmem ↦ ha (supp_le hs hmem))

/-- If `x` has empty support, every atom is fresh for it. -/
theorem fresh_of_supp_empty {x : X} (h : supp x = ∅) (a : α) : a # x := by
  simp [Fresh, h]

/-- If `x` has empty support, it is fresh for every element of any nominal set. -/
theorem fresh_of_supp_empty_left {x : X} (h : supp x = ∅) (y : Y) : x # y := by
  simp [Fresh, h]

/-- If `y` has empty support, every element of any nominal set is fresh for it. -/
theorem fresh_of_supp_empty_right {y : Y} (h : supp y = ∅) (x : X) : x # y := by
  simp [Fresh, h]

/-- If the support of `y` is contained in the support of `x`, then freshness
    for `x` implies freshness for `y`. -/
theorem fresh_of_supp_subset {a : α} {x : X} {y : Y}
    (hsub : supp y ⊆ supp x) (ha : a # x) : a # y := by
  rw [fresh_atom_left] at ha ⊢
  exact fun hy ↦ ha (hsub hy)

/-- If the support of `y` is contained in a finset `A` of atoms and `a # A`, then `a # y`. -/
theorem fresh_of_supp_subset_finset {a : α} {A : Finset α} {y : Y}
    (hsub : supp y ⊆ A) (ha : a # A) : a # y :=
  fresh_of_supp_subset ((supp_finset A).symm ▸ hsub) ha

/-- If `f` is equivariant and `a # x`, then `a # f x`.
    Pitts Proposition 3.4(iii): equivariant maps preserve freshness. -/
theorem fresh_of_equivariant {Y : Type*} [Nominal α Y] {f : X → Y} (hf : IsEquivariant α f)
    {a : α} {x : X} (ha : a # x) : a # f x :=
  fresh_of_supp_subset (supp_map_le hf x) ha

/-- For any `x` and any `n`, there exist `n` mutually distinct atoms all fresh for `x`. -/
theorem exists_fresh_atoms (x : X) (n : Nat) : ∃ as : Finset α, as.card = n ∧ ∀ a ∈ as, a # x := by
  induction n with
  | zero => exact ⟨∅, by simp⟩
  | succ n ih =>
    obtain ⟨as, hcard, hfresh⟩ := ih
    obtain ⟨b, hb⟩ := (supp x ∪ as).exists_notMem
    rw [Finset.mem_union, not_or] at hb
    exact ⟨insert b as,
      by rw [Finset.card_insert_of_notMem hb.2, hcard],
      fun a ha ↦ by
        rw [Finset.mem_insert] at ha
        exact ha.elim (fun h ↦ h ▸ (fresh_atom_left b x).mpr hb.1) (hfresh a)⟩

/-- An atom `a` is fresh for a finite set of atoms `A` if and only if `a ∉ A`. -/
@[simp]
theorem fresh_atom_finset {A : Finset α} {a : α} : a # A ↔ a ∉ A := by
  simp [Fresh, supp_atom, supp_finset, Finset.disjoint_singleton_left]

/-- A finite set of atoms `A` is fresh for `B` if and only if they are disjoint. -/
@[simp]
theorem fresh_finset {A B : Finset α} : A # B ↔ Disjoint A B := by
  simp [Fresh, supp_finset]

/-- An atom `a` is fresh for a permutation `σ` if and only if `σ` fixes `a`. -/
@[simp]
theorem fresh_finitePerm {σ : FinitePerm α} {a : α} : a # σ ↔ σ a = a := by
  rw [fresh_atom_left, supp_finitePerm, PermType.mem_movedFinset, not_not]

/-- A permutation `σ` is fresh for an atom `a` if and only if `σ` fixes `a`. -/
@[simp]
theorem fresh_finitePerm_right {σ : FinitePerm α} {a : α} : σ # a ↔ σ a = a := by
  rw [fresh_comm, fresh_finitePerm]

/-- Every atom is fresh for `none`. -/
@[simp]
theorem fresh_none (a : α) : a # (none : Option X) := by
  simp [supp_none]

/-- `a # some y ↔ a # y`. -/
@[simp]
theorem fresh_some {a : α} {x : X} : a # (some x) ↔ a # x := by
  simp [supp_some]

/-- `a # Sum.inl x ↔ a # x`. -/
@[simp]
theorem fresh_inl {a : α} {x : X} : a # (Sum.inl x : X ⊕ Y) ↔ a # x := by
  simp [supp_inl]

/-- `a # Sum.inr y ↔ a # y`. -/
@[simp]
theorem fresh_inr {a : α} {y : Y} : a # (Sum.inr y : X ⊕ Y) ↔ a # y := by
  simp [supp_inr]

/-- Negation of atom freshness: `¬ (a # x) ↔ a ∈ supp x`. -/
theorem not_fresh_iff {a : α} {x : X} : ¬ (a # x) ↔ a ∈ supp x := by
  simp

/-- Freshness monotonicity (left): if `supp x ⊆ supp x'` and `x' # y`, then `x # y`. -/
theorem fresh_of_supp_subset_left {x x' : X} {y : Y} (hsub : supp x ⊆ supp x') (h : x' # y) : x # y := by
  simp only [Fresh] at h ⊢
  exact Disjoint.mono_left hsub h

/-- Freshness through a permutation: `a # (π • x) ↔ π⁻¹ • a # x`. -/
@[simp]
theorem fresh_smul_left (a : α) (π : FinitePerm α) (x : X) : a # (π • x) ↔ (π⁻¹ • a) # x := by
  rw [fresh_atom_left, fresh_atom_left, mem_supp_smul]

/-- Freshness is transported by permutations: `(π • x) # y ↔ x # (π⁻¹ • y)`. -/
theorem fresh_smul_right (π : FinitePerm α) (x : X) (y : Y) : (π • x) # y ↔ x # (π⁻¹ • y) := by
  calc (π • x) # y
      ↔ (π • x) # (π • (π⁻¹ • y)) := by rw [PermType.smul_inv_smul]
    _ ↔ x # (π⁻¹ • y) := fresh_equivariant_iff π

/-- Fresh permutations commute: if `π # σ`, then `π * σ = σ * π`. -/
theorem fresh_perm_comm {π σ : FinitePerm α} (h : π # σ) : π * σ = σ * π := by
  have hd : Equiv.Perm.Disjoint (π : Equiv.Perm α) (σ : Equiv.Perm α) := by
    intro a
    simp only [Fresh, supp_finitePerm] at h
    by_contra hc
    push_neg at hc
    obtain ⟨h₁, h₂⟩ := hc
    have ha₁ : a ∈ PermType.movedFinset π := PermType.mem_movedFinset.mpr h₁
    have ha₂ : a ∈ PermType.movedFinset σ := PermType.mem_movedFinset.mpr h₂
    exact absurd rfl (Finset.disjoint_iff_ne.mp h a ha₁ a ha₂)
  exact Subtype.ext hd.commute.eq

section Filter

open Filter

-- TODO: these lemmas can be generalized for any nominal set, not only names (α)

/-- an atom belongs to `supp x` precisely when it is not fresh for `x`. -/
@[grind =]
theorem fresh_atom_compl_eq_supp (x : X) : supp x = {a : α | a # x}ᶜ := by
  ext a
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq, fresh_atom_left, not_not, Finset.mem_coe]

/-- The set of atoms fresh for `x` belongs to the cofinite filter. -/
theorem fresh_cofinite (x : X) : {a : α | a # x} ∈ cofinite := by
  rw [mem_cofinite, ←fresh_atom_compl_eq_supp]
  exact (supp x).finite_toSet

/-- The set of atoms fresh for `x` is cofinite (its complement is `supp x`, which is finite). -/
theorem fresh_atom_cofinite (x : X) : ∀ᶠ (a : α) in cofinite, a # x :=
  fresh_cofinite x

/-- An atom `w` belongs to `supp x` if and only if it is not fresh for `x`. -/
theorem fresh_atom_notin_iff_in_supp (w : α) (x : X) :
  w ∈ supp x ↔ w ∉ {a : α | a # x} := by simp

end Filter

/-- Every element of a nominal set is fresh for `()`. -/
theorem fresh_unit (x : X) : letI := Nominal.instUnit (α := α); x # () := by
  letI := Nominal.instUnit (α := α)
  simp [Fresh]

end Fresh

end Nominal.Set
