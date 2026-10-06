/-
Copyright (c) 2026 Nominal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nominal contributors
-/
import Package.Foundations.Action
import Mathlib.GroupTheory.GroupAction.Support
import Mathlib.Data.Set.Finite.Basic

/-!
# Finite support for selected permutation actions

`Supports S x` specializes Mathlib's two-carrier support predicate to a finite
atom bound. `FinitelySupported A x` asserts existence of such a bound for one
element of an already selected action, without a carrier-wide nominality class.

Basic support laws need no atom assumptions. Finite-set operations and swaps
use decidable equality; finite intersection additionally needs infinite atoms.
No action instance, least-support operator or freshness interface is introduced.
-/

namespace NominalPackage

universe u v w

/-- Every finite permutation fixing the atom bound pointwise fixes the element. -/
abbrev Supports {A : Type u} {X : Type v}
    [MulAction (Perm A) X] (S : Finset A) (x : X) : Prop :=
  MulAction.Supports (Perm A) (S : Set A) x

/-- Existence of a finite supporting atom bound for the selected action. -/
def FinitelySupported (A : Type u) {X : Type v}
    [MulAction (Perm A) X] (x : X) : Prop :=
  ∃ S : Finset A, Supports S x

variable {A : Type u} {X : Type v} {Y : Type w}
variable [MulAction (Perm A) X] [MulAction (Perm A) Y]
variable {S T : Finset A} {x : X} {y : Y} {f : X → Y}

/-- The pointwise-fixing condition in the explicit-binder form used by `Perm`. -/
theorem supports_iff (S : Finset A) (x : X) :
    Supports S x ↔ ∀ π : Perm A, (∀ a ∈ S, π a = a) → π • x = x :=
  ⟨fun h π hfix => h π (fun _ ha => hfix _ ha),
    fun h π hfix => h π (fun _ ha => hfix ha)⟩

/-- Enlarging a supporting bound preserves support. -/
theorem supports_mono (hST : S ⊆ T) (hS : Supports S x) : Supports T x :=
  MulAction.Supports.mono (fun _ ha => hST ha) hS

/-- Empty support is invariance under every finite permutation. -/
theorem supports_empty_iff (x : X) :
    Supports (∅ : Finset A) x ↔ ∀ π : Perm A, π • x = x := by
  constructor
  · intro h π
    exact (supports_iff ∅ x).1 h π (by simp)
  · intro h
    exact (supports_iff ∅ x).2 (fun π _ => h π)

/-- An equivariant image retains every sufficient support bound. -/
theorem supports_map (hf : Equivariant A f) (hS : Supports S x) :
    Supports S (f x) := by
  intro π hfix
  rw [← hf, hS π hfix]

/-- A common bound supports a pair exactly when it supports both components. -/
theorem supports_prod_iff (S : Finset A) (x : X) (y : Y) :
    Supports S (x, y) ↔ Supports S x ∧ Supports S y := by
  constructor
  · intro h
    exact ⟨supports_map (Equivariant.fst A) h, supports_map (Equivariant.snd A) h⟩
  · rintro ⟨hx, hy⟩ π hfix
    exact Prod.ext (hx π hfix) (hy π hfix)

/-- Any explicit support bound certifies finite supportedness. -/
theorem Supports.finitelySupported (hS : Supports S x) : FinitelySupported A x :=
  ⟨S, hS⟩

/-- The union of component bounds supports the pair. -/
theorem supports_prod [DecidableEq A] (hS : Supports S x) (hT : Supports T y) :
    Supports (S ∪ T) (x, y) :=
  (supports_prod_iff _ _ _).2
    ⟨supports_mono Finset.subset_union_left hS, supports_mono Finset.subset_union_right hT⟩

/-- Finite supportedness is preserved by an ordinary equivariant map. -/
theorem FinitelySupported.map (hx : FinitelySupported A x)
    (hf : Equivariant A f) : FinitelySupported A (f x) := by
  obtain ⟨S, hS⟩ := hx
  exact ⟨S, supports_map hf hS⟩

/-- Finite support witnesses for a product stay inside the existential proof. -/
theorem FinitelySupported.prod (hx : FinitelySupported A x)
    (hy : FinitelySupported A y) : FinitelySupported A (x, y) := by
  classical
  obtain ⟨S, hS⟩ := hx
  obtain ⟨T, hT⟩ := hy
  exact ⟨S ∪ T, supports_prod hS hT⟩

section DecidableEq

variable [DecidableEq A]
open scoped Pointwise

/-- Rename a support bound and its element together. The proof conjugates the
pointwise-fixing permutation; no commuting-action assumption is needed. -/
theorem supports_smul (hS : Supports S x) (π : Perm A) :
    Supports (π • S) (π • x) := by
  apply (supports_iff _ _).2
  intro σ hfix
  have hc : (π⁻¹ * σ * π) • x = x := (supports_iff S x).1 hS _ (by
    intro a ha
    have hmem : π a ∈ π • S := by
      rw [Perm.mem_smul_finset]
      simpa only [Perm.inv_apply_apply] using ha
    simp only [Perm.mul_apply, hfix _ hmem, Perm.inv_apply_apply])
  calc
    σ • (π • x) = π • ((π⁻¹ * σ * π) • x) := by
      simp only [mul_smul, smul_inv_smul]
    _ = π • x := congrArg (π • ·) hc

/-- Simultaneous renaming preserves and reflects a support bound. -/
theorem supports_smul_iff (π : Perm A) (S : Finset A) (x : X) :
    Supports (π • S) (π • x) ↔ Supports S x := by
  constructor
  · intro h
    simpa only [inv_smul_smul] using supports_smul h π⁻¹
  · intro h
    exact supports_smul h π

/-- Finite support is equivalent to invariance under swaps outside its bound.
This specializes the arbitrary-set criterion from controlled factorization. -/
theorem supports_iff_swap (S : Finset A) (x : X) :
    Supports S x ↔ ∀ a b : A, a ∉ S → b ∉ S → Perm.swap a b • x = x :=
  (supports_iff S x).trans (Perm.forall_smul_eq_iff_swap_smul_eq (S : Set A) x)

/-- Swapping two atoms outside a sufficient support bound fixes the element. -/
theorem swap_smul_eq_of_supports (hS : Supports S x)
    {a b : A} (ha : a ∉ S) (hb : b ∉ S) : Perm.swap a b • x = x :=
  (supports_iff_swap S x).1 hS a b ha hb

/-- Two finite support bounds have a supporting intersection over infinite atoms.
Infinitude supplies a spare atom for the triple-swap argument. On two atoms,
either singleton supports an atom, while their empty intersection need not. -/
theorem supports_inter [Infinite A] (hS : Supports S x) (hT : Supports T x) :
    Supports (S ∩ T) x := by
  apply (supports_iff_swap _ x).2
  intro a b ha hb
  by_cases hab : a = b
  · subst b
    simp
  obtain ⟨c, hc⟩ := Finset.exists_notMem (S ∪ T ∪ {a, b})
  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, not_or] at hc
  have hac : Perm.swap a c • x = x := by
    by_cases haS : a ∈ S
    · exact swap_smul_eq_of_supports hT
        (fun haT => ha (Finset.mem_inter.mpr ⟨haS, haT⟩)) hc.1.2
    · exact swap_smul_eq_of_supports hS haS hc.1.1
  have hcb : Perm.swap c b • x = x := by
    by_cases hbS : b ∈ S
    · exact swap_smul_eq_of_supports hT hc.1.2
        (fun hbT => hb (Finset.mem_inter.mpr ⟨hbS, hbT⟩))
    · exact swap_smul_eq_of_supports hS hc.1.1 hbS
  have hconj : Perm.swap a c * Perm.swap c b * Perm.swap a c = Perm.swap a b := by
    simpa only [Perm.swap_inv, Perm.swap_apply_right,
      Perm.swap_apply_of_ne_of_ne (Ne.symm hab) (Ne.symm hc.2.2)] using
      Perm.conj_swap (Perm.swap a c) c b
  rw [← hconj, mul_smul, mul_smul, hac, hcb, hac]

end DecidableEq

/-- Renaming preserves finite supportedness; its witness image stays in `Prop`. -/
theorem FinitelySupported.smul (hx : FinitelySupported A x) (π : Perm A) :
    FinitelySupported A (π • x) := by
  classical
  obtain ⟨S, hS⟩ := hx
  exact ⟨_, supports_smul hS π⟩

/-- Finite supportedness is invariant under the selected permutation action. -/
theorem finitelySupported_smul_iff (π : Perm A) (x : X) :
    FinitelySupported A (π • x) ↔ FinitelySupported A x := by
  constructor
  · intro h
    simpa only [inv_smul_smul] using FinitelySupported.smul h π⁻¹
  · intro h
    exact FinitelySupported.smul h π

end NominalPackage
