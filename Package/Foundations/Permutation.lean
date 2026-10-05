/-
Copyright (c) 2026 Nominal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nominal contributors
-/
import Mathlib.Algebra.Group.End
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.FunLike.Basic

/-!
# Finite permutations

`Perm A` is the subgroup of bijections of `A` with finitely many moved points.
Neither infinitude nor decidable equality is required for the group. Swaps use
decidable equality; support theory and swap factorization are separate layers.

The elementary moved-set/subgroup arguments adapt the reference development in
`Nominal/Core/FinitePerm.lean`, without importing it or installing its actions.
-/

namespace NominalPackage

universe u

private def movedPoints {A : Type u} (π : Equiv.Perm A) : Set A := {a | π a ≠ a}

private theorem movedPoints_one (A : Type u) : movedPoints (1 : Equiv.Perm A) = ∅ := by
  ext a
  simp [movedPoints]

private theorem movedPoints_mul_subset {A : Type u} (π σ : Equiv.Perm A) :
    movedPoints (π * σ) ⊆ movedPoints π ∪ movedPoints σ := by
  intro a ha
  by_contra h
  have hπ : π a = a := by simpa [movedPoints] using fun hp => h (Or.inl hp)
  have hσ : σ a = a := by simpa [movedPoints] using fun hs => h (Or.inr hs)
  exact ha (by change π (σ a) = a; rw [hσ, hπ])

private theorem movedPoints_inv {A : Type u} (π : Equiv.Perm A) :
    movedPoints π⁻¹ = movedPoints π := by
  ext a
  change (π.symm a ≠ a) ↔ π a ≠ a
  apply not_congr
  constructor
  · intro h
    calc π a = π (π.symm a) := congrArg π h.symm
      _ = a := π.apply_symm_apply a
  · intro h
    calc π.symm a = π.symm (π a) := congrArg π.symm h.symm
      _ = a := π.symm_apply_apply a

/-- The subgroup of bijections with finite moved-point sets. -/
def permSubgroup (A : Type u) : Subgroup (Equiv.Perm A) where
  carrier := {π | (movedPoints π).Finite}
  one_mem' := by simp [movedPoints_one]
  mul_mem' hπ hσ := (hπ.union hσ).subset (movedPoints_mul_subset _ _)
  inv_mem' hπ := by
    change (movedPoints _).Finite at hπ ⊢
    simpa only [movedPoints_inv] using hπ

/-- Finite permutations, with the group operations inherited from the subgroup. -/
abbrev Perm (A : Type u) : Type u := ↥(permSubgroup A)

namespace Perm

variable {A : Type u}

/-- The underlying bijection. -/
def toEquiv (π : Perm A) : Equiv.Perm A := π.val

instance : FunLike (Perm A) A A where
  coe π := π.val
  coe_injective _ _ h := Subtype.ext (Equiv.ext (congrFun h))

@[ext]
theorem ext {π σ : Perm A} (h : ∀ a, π a = σ a) : π = σ := DFunLike.ext _ _ h

@[simp] theorem toEquiv_apply (π : Perm A) (a : A) : π.toEquiv a = π a := rfl
@[simp] theorem one_apply (a : A) : (1 : Perm A) a = a := rfl
@[simp] theorem mul_apply (π σ : Perm A) (a : A) : (π * σ) a = π (σ a) := rfl
@[simp] theorem inv_apply_apply (π : Perm A) (a : A) : π⁻¹ (π a) = a :=
  π.val.symm_apply_apply a
@[simp] theorem apply_inv_apply (π : Perm A) (a : A) : π (π⁻¹ a) = a :=
  π.val.apply_symm_apply a

@[simp] theorem toEquiv_one : (1 : Perm A).toEquiv = 1 := rfl
@[simp] theorem toEquiv_mul (π σ : Perm A) : (π * σ).toEquiv = π.toEquiv * σ.toEquiv := rfl
@[simp] theorem toEquiv_inv (π : Perm A) : (π⁻¹).toEquiv = π.toEquiv⁻¹ := rfl

/-- Atoms moved by a permutation; this is not a chosen finite enumeration. -/
def moved (π : Perm A) : Set A := {a | π a ≠ a}

@[simp] theorem mem_moved (π : Perm A) (a : A) : a ∈ π.moved ↔ π a ≠ a := Iff.rfl

theorem moved_finite (π : Perm A) : π.moved.Finite := π.property

@[simp] theorem moved_one : moved (1 : Perm A) = ∅ := movedPoints_one A

theorem moved_mul_subset (π σ : Perm A) : moved (π * σ) ⊆ moved π ∪ moved σ :=
  movedPoints_mul_subset π.val σ.val

@[simp] theorem moved_inv (π : Perm A) : moved π⁻¹ = moved π := movedPoints_inv π.val

theorem moved_conj (π σ : Perm A) : moved (π * σ * π⁻¹) = π '' moved σ := by
  ext a
  constructor
  · intro ha
    refine ⟨π⁻¹ a, ?_, apply_inv_apply π a⟩
    intro h
    exact ha (by simp only [mul_apply, h, apply_inv_apply])
  · rintro ⟨b, hb, rfl⟩ h
    apply hb
    have h' : π (σ b) = π b := by
      simpa only [mul_apply, inv_apply_apply] using h
    exact π.val.injective h'

section Swaps

variable [DecidableEq A]

/-- The finite permutation interchanging two atoms. -/
def swap (a b : A) : Perm A :=
  ⟨Equiv.swap a b, by
    apply (Set.Finite.insert a (Set.finite_singleton b)).subset
    intro c hc
    exact (Equiv.swap_apply_ne_self_iff.mp hc).2⟩

@[simp] theorem swap_apply_left (a b : A) : swap a b a = b := Equiv.swap_apply_left a b
@[simp] theorem swap_apply_right (a b : A) : swap a b b = a := Equiv.swap_apply_right a b

theorem swap_apply_of_ne_of_ne {a b c : A} (hca : c ≠ a) (hcb : c ≠ b) :
    swap a b c = c := Equiv.swap_apply_of_ne_of_ne hca hcb

@[simp] theorem swap_self (a : A) : swap a a = 1 :=
  Subtype.ext (Equiv.swap_self a)

@[simp] theorem swap_inv (a b : A) : (swap a b)⁻¹ = swap a b :=
  Subtype.ext (Equiv.swap_inv a b)

@[simp] theorem swap_mul_self (a b : A) : swap a b * swap a b = 1 :=
  Subtype.ext (Equiv.swap_mul_self a b)

theorem conj_swap (π : Perm A) (a b : A) :
    π * swap a b * π⁻¹ = swap (π a) (π b) :=
  Subtype.ext (Equiv.swap_apply_apply π.val a b).symm

theorem moved_swap {a b : A} (hab : a ≠ b) : moved (swap a b) = {a, b} := by
  ext c
  exact Equiv.swap_apply_ne_self_iff.trans
    ⟨fun h => h.2, fun h => ⟨hab, h⟩⟩

end Swaps

end Perm
end NominalPackage
