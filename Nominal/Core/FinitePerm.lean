import Nominal.Wheels
import Mathlib.GroupTheory.Perm.ClosureSwap
import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# Finite Permutations

A **finite permutation** of a type `α` is a permutation `π : Equiv.Perm α` that moves only finitely many elements, i.e., the set `{a : α | π a ≠ a}` is finite.

Mathlib's `Equiv.Perm.support` requires a `Fintype` instance and is therefore not available for infinite types. This file works with `Set.Finite` directly, defining the
moved-point set `Equiv.Perm.movedPoints` and the subgroup `FinitePerm α` of permutations with finite moved-point sets.

## Main definitions

* `Equiv.Perm.movedPoints π` — the set `{a | π a ≠ a}` of atoms moved by `π`.
* `Equiv.Perm.IsFinitePerm π` — predicate: `π.movedPoints` is finite.
* `FinitePerm α` — the subgroup of `Equiv.Perm α` consisting of permutations with finite support.

## Instances

* `instFunLike` — `FinitePerm α` elements can be applied directly as functions `α → α`.
* `instCoe` — coercion from `FinitePerm α` to `Equiv.Perm α`.

## Main results

### `Equiv.Perm` preliminaries
* `Equiv.Perm.mem_movedPoints` — `a ∈ π.movedPoints ↔ π a ≠ a`.
* `Equiv.Perm.not_mem_movedPoints` — `a ∉ π.movedPoints ↔ π a = a`.
* `Equiv.Perm.movedPoints_eq_compl_fixedBy` — `movedPoints π = (fixedBy α π)ᶜ`.
* `Equiv.Perm.movedPoints_one` — the identity moves no atoms.
* `Equiv.Perm.movedPoints_mul_subset` — `(π * σ).movedPoints ⊆ π.movedPoints ∪ σ.movedPoints`.
* `Equiv.Perm.movedPoints_inv` — `π⁻¹.movedPoints = π.movedPoints`.
* `Equiv.Perm.movedPoints_conj` — `(π * σ * π⁻¹).movedPoints = π '' σ.movedPoints`.
* `Equiv.Perm.movedPoints_swap` — `(swap a b).movedPoints = {a, b}` when `a ≠ b`.
* `Equiv.Perm.movedPoints_swap_self` — `(swap a a).movedPoints = ∅`.
* `Equiv.Perm.isFinitePerm_one` — the identity has finite support.
* `Equiv.Perm.IsFinitePerm.mul` — finite support is closed under multiplication.
* `Equiv.Perm.IsFinitePerm.inv` — finite support is closed under inversion.
* `Equiv.Perm.IsFinitePerm.conj` — finite support is closed under conjugation.
* `Equiv.Perm.IsFinitePerm.swap` — every transposition has finite support.
* `Equiv.Perm.movedPoints_subset_iff` — `π.movedPoints ⊆ S ↔ ∀ a ∉ S, π a = a`.
* `Equiv.Perm.movedPoints_mul_disjoint` — `(f * g).movedPoints = f.movedPoints ∪ g.movedPoints` when `f.movedPoints ∩ g.movedPoints = ∅`.

### Function-like and coercion API
* `FinitePerm.ext` — extensionality: two finite permutations are equal iff they agree pointwise.
* `FinitePerm.coe_mk` — computation lemma for the subtype constructor.
* `FinitePerm.coe_one` / `FinitePerm.one_apply` — the identity acts as `id`.
* `FinitePerm.coe_mul` / `FinitePerm.mul_apply` — multiplication acts as function composition.
* `FinitePerm.inv_apply_self` / `FinitePerm.apply_inv_self` — left and right inverse laws.
* `FinitePerm.injective` / `FinitePerm.surjective` / `FinitePerm.bijective` — every finite permutation is a bijection.
* `FinitePerm.apply_eq_iff_eq` — `π a = π b ↔ a = b` (injectivity in simp-normal form).
* `FinitePerm.coe_val` — coercion to `Equiv.Perm α` is the subtype projection.
* `FinitePerm.coe_toPerm_one` / `FinitePerm.coe_toPerm_mul` / `FinitePerm.coe_toPerm_inv` — coercion commutes with group operations (for `norm_cast`).
* `FinitePerm.coe_injective` / `FinitePerm.coe_inj` — coercion to `Equiv.Perm α` is injective.

### Group structure
* `FinitePerm.support_finite` — every element of `FinitePerm α` has finitely many moved points.
* `FinitePerm.movedPoints_conj` — `(π * σ * π⁻¹ : Perm α).movedPoints = (π : Perm α) '' (σ : Perm α).movedPoints`.
* `FinitePerm.swap_finite` — every transposition belongs to `FinitePerm α`.
* `FinitePerm.eq_closure_isSwap` — `FinitePerm α` equals the closure of all transpositions in `Equiv.Perm α`.
* `FinitePerm.swap_factorization` — every finite permutation is a product of a finite list of transpositions.
* `FinitePerm.movedPoints'` — the moved-point set at the `FinitePerm` level.
-/

open Equiv MulAction Set

namespace Equiv.Perm

variable {α : Type*} (π : Perm α)

/-- The set of atoms moved by a permutation: `{a | π a ≠ a}`. -/
def movedPoints : Set α := {a | π a ≠ a}

@[simp]
theorem mem_movedPoints {a : α} : a ∈ π.movedPoints ↔ π a ≠ a := Iff.rfl

/-- An atom not in the moved-point set is a fixed point of `π`. Negation of `mem_movedPoints`. -/
@[simp]
theorem not_mem_movedPoints {a : α} : a ∉ π.movedPoints ↔ π a = a := by
  simp [mem_movedPoints]

/-- A permutation has **finite support** if it moves only finitely many atoms -/
@[reducible]
def IsFinitePerm : Prop := π.movedPoints.Finite

@[grind =]
theorem movedPoints_eq_compl_fixedBy : π.movedPoints = (fixedBy α π)ᶜ := by
  ext a
  simp [movedPoints, fixedBy, Perm.smul_def]

@[simp]
theorem movedPoints_one : (1 : Perm α).movedPoints = ∅ := by
  ext a; simp [movedPoints]

theorem movedPoints_mul_subset (π σ : Perm α) : (π * σ).movedPoints ⊆ π.movedPoints ∪ σ.movedPoints := by
  intro a ha
  simp only [movedPoints, mem_ofPred_eq, Perm.mul_apply, mem_union] at *
  by_contra h
  push Not at h
  exact ha (by rw [h.2, h.1])

@[simp]
theorem movedPoints_inv : π⁻¹.movedPoints = π.movedPoints := by
  ext a
  simp only [movedPoints, mem_ofPred_eq, ne_eq]
  constructor
  · intro h heq
    exact h (by rw [Perm.inv_def, show π.symm a = π.symm (π a) from congrArg π.symm heq.symm,
                     π.symm_apply_apply])
  · intro h heq
    exact h (by rw [show π a = π (π.symm a) from congrArg π heq.symm,
                     π.apply_symm_apply])

/-- Conjugation permutes the moved-point set: `(π * σ * π⁻¹).movedPoints = π '' σ.movedPoints`. -/
@[grind =]
theorem movedPoints_conj (π σ : Perm α) : (π * σ * π⁻¹).movedPoints = π '' σ.movedPoints := by
  ext a
  simp only [mem_movedPoints, Perm.mul_apply, Perm.inv_def, Set.mem_image]
  constructor
  · intro h
    refine ⟨π.symm a, fun heq ↦ h ?_, π.apply_symm_apply a⟩
    rw [heq, π.apply_symm_apply]
  · rintro ⟨b, hb, rfl⟩ heq
    exact hb (π.injective (by rwa [π.symm_apply_apply] at heq))

/-- The moved-point set of a transposition `swap a b` (with `a ≠ b`) is `{a, b}`. -/
@[simp]
theorem movedPoints_swap [DecidableEq α] {a b : α} (h : a ≠ b) : (Equiv.swap a b).movedPoints = {a, b} := by
  ext c
  simp only [mem_movedPoints, Set.mem_insert_iff, Set.mem_singleton_iff]
  exact swap_apply_ne_self_iff.trans ⟨fun ⟨_, hc⟩ ↦ hc, fun hc ↦ ⟨h, hc⟩⟩

/-- The moved-point set of the reflexive swap `swap a a` is empty. -/
@[simp]
theorem movedPoints_swap_self [DecidableEq α] (a : α) : (Equiv.swap a a).movedPoints = ∅ := by
  simp [Equiv.swap_self, movedPoints]

/-- The identity permutation has finite support. -/
@[simp]
theorem isFinitePerm_one : (1 : Perm α).IsFinitePerm := by simp [IsFinitePerm]

/-- Finite support is closed under multiplication. -/
@[grind .]
theorem IsFinitePerm.mul {π σ : Perm α} (hπ : π.IsFinitePerm) (hσ : σ.IsFinitePerm) : (π * σ).IsFinitePerm :=
  (hπ.union hσ).subset (movedPoints_mul_subset π σ)

/-- Finite support is closed under inversion. -/
@[simp]
theorem IsFinitePerm.inv {π : Perm α} (h : π.IsFinitePerm) : π⁻¹.IsFinitePerm := by
  rwa [IsFinitePerm, movedPoints_inv]

/-- Finite support is closed under conjugation. -/
theorem IsFinitePerm.conj {π σ : Perm α} (hσ : σ.IsFinitePerm) : (π * σ * π⁻¹).IsFinitePerm := by
  rw [IsFinitePerm, movedPoints_conj]
  exact hσ.image π

/-- Every transposition `swap a b` is a finite permutation (it moves at most 2 atoms). -/
theorem IsFinitePerm.swap [DecidableEq α] (a b : α) : (swap a b).IsFinitePerm := by
  simp only [IsFinitePerm, movedPoints]
  exact (({a, b} : Finset α).finite_toSet).subset fun x hx ↦
    (swap_apply_ne_self_iff.mp hx).2 |>.elim
      (fun h ↦ Finset.mem_coe.mpr (Finset.mem_insert.mpr (Or.inl h)))
      (fun h ↦ Finset.mem_coe.mpr (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr h))))

/-- The moved-point set of `π` is contained in `S` iff `π` fixes every atom outside `S`. -/
theorem movedPoints_subset_iff {S : Set α} : π.movedPoints ⊆ S ↔ ∀ a, a ∉ S → π a = a := by
  simp only [Set.subset_def, mem_movedPoints]
  exact ⟨fun h a ha ↦ by_contra (fun hne ↦ ha (h a hne)), fun h a hne ↦ by_contra (fun ha ↦ hne (h a ha))⟩

/-- When two permutations have disjoint moved-point sets, the moved-point set of their product is exactly the union. -/
theorem movedPoints_mul_disjoint {α : Type*} {f g : Perm α} (h : f.movedPoints ∩ g.movedPoints = ∅) :
    (f * g).movedPoints = f.movedPoints ∪ g.movedPoints := by
  ext a
  simp only [mem_movedPoints, Equiv.Perm.mul_apply, Set.mem_union]
  constructor
  · exact fun ha ↦ movedPoints_mul_subset f g ha
  · rintro (ha | ha)
    · have hag : g a = a := by
        rw [← not_mem_movedPoints]
        intro hg
        have : a ∈ f.movedPoints ∩ g.movedPoints := Set.mem_inter ha hg
        rw [h] at this; exact this
      rw [hag]; exact ha
    · have haf : f a = a := by
        rw [← not_mem_movedPoints]
        intro hf
        have : a ∈ f.movedPoints ∩ g.movedPoints := Set.mem_inter hf ha
        rw [h] at this; exact this
      intro heq
      exact ha (f.injective (by rwa [haf]))

end Equiv.Perm

/-- `FinitePerm α` is the subgroup of `Equiv.Perm α` consisting of permutations that move only finitely many atoms. -/
def FinitePerm (α : Type*) : Subgroup (Perm α) where
  carrier := {π | π.IsFinitePerm}
  one_mem' := by simp [Equiv.Perm.IsFinitePerm, Equiv.Perm.movedPoints]
  mul_mem' := by
    intro f g hf hg
    simp only [Set.mem_ofPred_eq, Equiv.Perm.IsFinitePerm] at *
    exact (hf.union hg).subset (Equiv.Perm.movedPoints_mul_subset f g)
  inv_mem' := by
    intro f hf
    simp only [Set.mem_ofPred_eq, Equiv.Perm.IsFinitePerm] at *
    rwa [Equiv.Perm.movedPoints_inv]

namespace Nominal.Core.FinitePerm

/-! ### Function-like coercion

`FinitePerm α` elements can be applied directly as functions `α → α` -/
instance instFunLike {α} : FunLike (FinitePerm α) α α where
  coe π := π.val
  coe_injective _ _ h := Subtype.ext (Equiv.Perm.ext (congr_fun h))

/-! ### Coercion to `Equiv.Perm`

`FinitePerm α` coerces to `Equiv.Perm α` via the subtype projection.
The `@[norm_cast]` lemmas allow `norm_cast` / `push_cast` / `pull_cast`
to commute coercions through the group operations. -/

instance instCoe {α} : Coe (FinitePerm α) (Perm α) := ⟨Subtype.val⟩

section Coe

open Equiv

variable {α : Type*} (π σ : FinitePerm α)

@[simp] theorem coe_mk (π : Perm α) (h : π ∈ FinitePerm α) : (⟨π, h⟩ : FinitePerm α) = π.toFun := rfl

@[ext] theorem ext {π σ : FinitePerm α} (h : ∀ a, π a = σ a) : π = σ := DFunLike.ext π σ h

@[simp] theorem coe_one : (1 : FinitePerm α) = (id : α → α) := rfl

@[simp, grind =] theorem one_apply (a : α) : (1 : FinitePerm α) a = a := rfl

@[simp, grind =] theorem coe_mul : (π * σ : FinitePerm α) = π ∘ σ := rfl

@[simp, grind =] theorem mul_apply (a : α) : (π * σ) a = π (σ a) := rfl

@[simp, grind =] theorem inv_apply_self (a : α) : π⁻¹ (π a) = a := π.val.symm_apply_apply a

@[simp, grind =] theorem apply_inv_self (a : α) : π (π⁻¹ a) = a := π.val.apply_symm_apply a

@[grind .] theorem injective : Function.Injective π := π.val.injective

@[grind .]
theorem surjective : Function.Surjective π := π.val.surjective

/-- Every finite permutation is a bijection `α → α`. -/
@[grind .]
theorem bijective : Function.Bijective π := ⟨injective π, surjective π⟩

/-- Injectivity of a finite permutation in simp-normal iff form. -/
@[simp]
theorem apply_eq_iff_eq (a b : α) : π a = π b ↔ a = b := π.val.apply_eq_iff_eq

@[simp, grind =] theorem coe_val : (π : Perm α) = π.val := rfl

@[simp, norm_cast, grind =]
theorem coe_toPerm_one : ((1 : FinitePerm α) : Perm α) = 1 := rfl

@[simp, norm_cast, grind =]
theorem coe_toPerm_mul : ((π * σ : FinitePerm α) : Perm α) = (π : Perm α) * σ := rfl

@[simp, norm_cast, grind =]
theorem coe_toPerm_inv : ((π⁻¹ : FinitePerm α) : Perm α) = (π : Perm α)⁻¹ := rfl

theorem coe_injective : Function.Injective ((↑) : FinitePerm α → Perm α) := Subtype.val_injective

@[simp, grind =]
theorem coe_inj {π σ : FinitePerm α} : (π : Perm α) = σ ↔ π = σ := Subtype.val_inj

end Coe

variable {α : Type*}

/-- Every element of `FinitePerm α` moves finitely many atoms -/
@[grind .]
theorem support_finite (π : FinitePerm α) : ((π : Equiv.Perm α).movedPoints).Finite := π.property

/-- Conjugating a finite permutation permutes its moved-point set. -/
@[grind =]
theorem movedPoints_conj (π σ : FinitePerm α) : (π * σ * π⁻¹ : Equiv.Perm α).movedPoints =
    (π : Equiv.Perm α) '' (σ : Equiv.Perm α).movedPoints := by
  simp only [coe_toPerm_inv, Equiv.Perm.movedPoints_conj]

/-- Every transposition (swap) is a finite permutation (it moves at most 2 atoms) -/
@[grind .]
theorem swap_finite (a b : α) [DecidableEq α] : swap a b ∈ FinitePerm α := by
  change (swap a b).IsFinitePerm
  simp only [Perm.IsFinitePerm, Perm.movedPoints]
  apply Set.Finite.subset (({a, b} : Finset α).finite_toSet)
  intro x hx
  simp only [Set.mem_ofPred_eq] at hx
  simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton]
  exact (swap_apply_ne_self_iff.mp hx).2

/-- `FinitePerm α` is exactly the subgroup generated by all transpositions. -/
@[grind =]
theorem eq_closure_isSwap [DecidableEq α] : FinitePerm α = Subgroup.closure {σ : Perm α | σ.IsSwap} := by
  ext f
  simp only [Subgroup.mem_mk, FinitePerm, Perm.IsFinitePerm, Perm.movedPoints_eq_compl_fixedBy]
  exact mem_closure_isSwap'.symm

/-- Every finite permutation is a product of transpositions: there exists a list of swaps whose product equals the given permutation.
The list may be empty, in which case the product is the identity by convention. -/
theorem swap_factorization [DecidableEq α] (π : FinitePerm α) : ∃ l : List (Perm α), (∀ σ ∈ l, σ.IsSwap) ∧ l.prod = π := by
  obtain ⟨f, hf⟩ := π
  have hmem : f ∈ Subgroup.closure {σ : Perm α | σ.IsSwap} :=
    @eq_closure_isSwap α _ ▸ hf
  induction hmem using Subgroup.closure_induction_left with
  | one => exact ⟨[], by simp, by simp⟩
  | mul_left σ hσ τ hτ ih =>
    obtain ⟨l, hl, hprod⟩ := ih (@eq_closure_isSwap α _ ▸ hτ)
    exact ⟨σ :: l, by simpa [List.forall_mem_cons] using ⟨hσ, hl⟩, by simp [hprod]⟩
  | inv_mul_cancel σ hσ τ hτ ih =>
    obtain ⟨l, hl, hprod⟩ := ih (@eq_closure_isSwap α _ ▸ hτ)
    obtain ⟨x, y, hne, rfl⟩ := hσ
    exact ⟨swap x y :: l, by simpa [List.forall_mem_cons] using ⟨⟨x, y, hne, rfl⟩, hl⟩,
      by simp [Perm.inv_def, hprod]⟩

/-- The set of atoms moved by a finite permutation, as a `Set α`. -/
def movedPoints' (π : FinitePerm α) : Set α := (π : Equiv.Perm α).movedPoints

end Nominal.Core.FinitePerm
