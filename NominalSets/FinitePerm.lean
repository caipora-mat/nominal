import NominalSets.Wheels
import Mathlib.GroupTheory.Perm.ClosureSwap
import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# Finite Permutations

A **finite permutation** of a type `α` is a permutation `π : Equiv.Perm α` that
moves only finitely many elements, i.e., the set `{a : α | π a ≠ a}` is finite.

Mathlib's `Equiv.Perm.support` requires a `Fintype` instance and is therefore not
available for infinite types. This file works with `Set.Finite` directly, defining the
moved-point set `Equiv.Perm.movedPoints` and the subgroup `FinitePerm α` of permutations
with finite moved-point sets.

## Main definitions

* `Equiv.Perm.movedPoints π` — the set `{a | π a ≠ a}` of atoms moved by `π`.
* `Equiv.Perm.IsFinitePerm π` — predicate asserting that `π.movedPoints` is finite.
* `FinitePerm α` — the subgroup of `Equiv.Perm α` of permutations with finite support.

## Main results

* `FinitePerm.support_finite` — every member of `FinitePerm α` has finitely many moved points.
* `FinitePerm.swap_finite` — every transposition belongs to `FinitePerm α`.
* `FinitePerm.eq_closure_isSwap` — `FinitePerm α` equals the closure of all transpositions in `Equiv.Perm α`.
* `FinitePerm.swap_factorization` — every finite permutation is a product of a finite list of transpositions.
* `FinitePerm.ext` — extensionality: two finite permutations are equal iff they agree pointwise.
-/

open Equiv MulAction Set

namespace Equiv.Perm

variable {α : Type*} (π : Perm α)

/-- The set of atoms moved by a permutation (better name? support already taken by Perm.support) -/
def movedPoints : Set α := {a | π a ≠ a}

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

theorem movedPoints_mul_subset (π σ : Perm α) :
    (π * σ).movedPoints ⊆ π.movedPoints ∪ σ.movedPoints := by
  intro a ha
  simp only [movedPoints, mem_setOf_eq, Perm.mul_apply, mem_union] at *
  by_contra h
  push_neg at h
  exact ha (by rw [h.2, h.1])

theorem movedPoints_inv : π⁻¹.movedPoints = π.movedPoints := by
  ext a
  simp only [movedPoints, mem_setOf_eq, ne_eq]
  constructor
  · intro h heq
    exact h (by rw [Perm.inv_def, show π.symm a = π.symm (π a) from congrArg π.symm heq.symm,
                     π.symm_apply_apply])
  · intro h heq
    exact h (by rw [show π a = π (π.symm a) from congrArg π heq.symm,
                     π.apply_symm_apply])

end Equiv.Perm

/-- `FinitePerm α` is the subgroup of `Equiv.Perm α` consisting of permutations that move only finitely many atoms. -/
def FinitePerm (α : Type*) : Subgroup (Perm α) where
  carrier := {π | π.IsFinitePerm}
  one_mem' := by simp [Equiv.Perm.IsFinitePerm, Equiv.Perm.movedPoints]
  mul_mem' := by
    intro f g hf hg
    simp only [Set.mem_setOf_eq, Equiv.Perm.IsFinitePerm] at *
    exact (hf.union hg).subset (Equiv.Perm.movedPoints_mul_subset f g)
  inv_mem' := by
    intro f hf
    simp only [Set.mem_setOf_eq, Equiv.Perm.IsFinitePerm] at *
    rwa [Equiv.Perm.movedPoints_inv]

section Coe

open Equiv

variable {α : Type*} (π σ : FinitePerm α)

/-! ### Function-like coercion

`FinitePerm α` elements can be applied directly as functions `α → α` -/
instance instFunLike : FunLike (FinitePerm α) α α where
  coe π := π.val
  coe_injective' _ _ h := Subtype.ext (Equiv.Perm.ext (congr_fun h))

@[simp] theorem coe_mk (π : Perm α) (h : π ∈ FinitePerm α) : (⟨π, h⟩ : FinitePerm α) = π.toFun := rfl

@[ext]
theorem ext {π σ : FinitePerm α} (h : ∀ a, π a = σ a) : π = σ := DFunLike.ext π σ h

@[simp] theorem coe_one : (1 : FinitePerm α) = (id : α → α) := rfl

@[simp, grind =] theorem one_apply (a : α) : (1 : FinitePerm α) a = a := rfl

@[simp, grind =] theorem coe_mul : (π * σ : FinitePerm α) = π ∘ σ := rfl

@[simp, grind =] theorem mul_apply (a : α) : (π * σ) a = π (σ a) := rfl

@[simp, grind =] theorem inv_apply_self (a : α) : π⁻¹ (π a) = a := π.val.symm_apply_apply a

@[simp, grind =] theorem apply_inv_self (a : α) : π (π⁻¹ a) = a := π.val.apply_symm_apply a

@[grind .] theorem injective : Function.Injective π := π.val.injective

theorem surjective : Function.Surjective π := π.val.surjective

/-! ### Coercion to `Equiv.Perm`

`FinitePerm α` coerces to `Equiv.Perm α` via the subtype projection.
The `@[norm_cast]` lemmas allow `norm_cast` / `push_cast` / `pull_cast`
to commute coercions through the group operations. -/

instance instCoe : Coe (FinitePerm α) (Perm α) := ⟨Subtype.val⟩

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

namespace FinitePerm

variable {α : Type*}

/-- Every element of `FinitePerm α` moves finitely many atoms -/
@[grind .]
theorem support_finite (π : FinitePerm α) : ((π : Equiv.Perm α).movedPoints).Finite := π.property

/-- Every transposition (swap) is a finite permutation (it moves at most 2 atoms) -/
@[grind .]
theorem swap_finite (a b : α) [DecidableEq α] : swap a b ∈ FinitePerm α := by
  change (swap a b).IsFinitePerm
  simp only [Perm.IsFinitePerm, Perm.movedPoints]
  apply Set.Finite.subset (({a, b} : Finset α).finite_toSet)
  intro x hx
  simp only [Set.mem_setOf_eq] at hx
  simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton]
  exact (swap_apply_ne_self_iff.mp hx).2

/-- `FinitePerm α` is exactly the subgroup generated by all transpositions. -/
theorem eq_closure_isSwap [DecidableEq α] : FinitePerm α = Subgroup.closure {σ : Perm α | σ.IsSwap} := by
  ext f
  simp only [Subgroup.mem_mk, FinitePerm, Perm.IsFinitePerm, Perm.movedPoints_eq_compl_fixedBy]
  exact mem_closure_isSwap'.symm

/-- Every finite permutation is a product of transpositions: there exists a list of
swaps whose product equals the given permutation. The list may be empty, in which case the product is the identity by convention. -/
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

end FinitePerm
