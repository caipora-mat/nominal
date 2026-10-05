/-
Copyright (c) 2026 Nominal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nominal contributors
-/
import Package.Foundations.Permutation
import Mathlib.GroupTheory.Perm.ClosureSwap
import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# Controlled swap factorization

Every finite permutation is a product of swaps with distinct endpoints in its
original moved-point set. Specializing Mathlib's `mem_closure_isSwap` to these
restricted generators supplies endpoint control; unrestricted generation alone
would not give the avoidance corollary.

List products use the existing composition convention: the rightmost swap acts
first. The witness is not canonical. No infinitude or ambient finiteness is needed.
-/

namespace NominalPackage.Perm

universe u

variable {A : Type u} [DecidableEq A]

/-- Factor a finite permutation into swaps of distinct atoms in its original
moved set. A list's rightmost swap acts first; identity has the empty witness. -/
theorem swap_factorization (π : Perm A) :
    ∃ l : List (A × A),
      (l.map (fun p => swap p.1 p.2)).prod = π ∧
      ∀ p ∈ l, p.1 ≠ p.2 ∧ p.1 ∈ π.moved ∧ p.2 ∈ π.moved := by
  let G : Set (Equiv.Perm A) := {g | ∃ a b,
    a ≠ b ∧ a ∈ π.moved ∧ b ∈ π.moved ∧ g = Equiv.swap a b}
  have hgen : ∀ g ∈ G, g.IsSwap := by
    rintro g ⟨a, b, hab, _, _, rfl⟩
    exact ⟨a, b, hab, rfl⟩
  have hπ : π.toEquiv ∈ Subgroup.closure G := by
    apply (mem_closure_isSwap hgen).2
    refine ⟨π.moved_finite, ?_⟩
    intro a
    by_cases ha : π a = a
    · rw [toEquiv_apply, ha]
      exact MulAction.mem_orbit_self a
    · have hb : π a ∈ π.moved := fun h => ha (π.toEquiv.injective h)
      exact ⟨⟨Equiv.swap a (π a),
        Subgroup.subset_closure ⟨a, π a, Ne.symm ha, ha, hb, rfl⟩⟩,
        Equiv.swap_apply_left a (π a)⟩
  -- Keep π, hence the original endpoint bound, fixed throughout closure induction.
  let P (g : Equiv.Perm A) : Prop := ∃ l : List (A × A),
    (l.map (fun p => swap p.1 p.2)).prod.toEquiv = g ∧
    ∀ p ∈ l, p.1 ≠ p.2 ∧ p.1 ∈ π.moved ∧ p.2 ∈ π.moved
  have prepend : ∀ g ∈ G, ∀ f, P f → P (g * f) := by
    rintro g ⟨a, b, hab, ha, hb, rfl⟩ f ⟨l, hl, hs⟩
    refine ⟨(a, b) :: l, ?_, ?_⟩
    · change (swap a b * (l.map (fun p => swap p.1 p.2)).prod).toEquiv = _
      rw [toEquiv_mul, hl]
      rfl
    · intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact ⟨hab, ha, hb⟩
      · exact hs p hp
  obtain ⟨l, hl, hs⟩ : P π.toEquiv := Subgroup.closure_induction_left
    (p := fun g _ => P g)
    ⟨[], rfl, by simp⟩
    (fun g hg f _ hf => prepend g hg f hf)
    (fun g hg f _ hf => by
      have hinv : g⁻¹ = g := by
        obtain ⟨a, b, _, _, _, rfl⟩ := hg
        exact Equiv.swap_inv a b
      rw [hinv]
      exact prepend g hg f hf)
    hπ
  exact ⟨l, Subtype.ext hl, hs⟩

/-- A permutation fixing an arbitrary set pointwise factors into swaps whose
distinct endpoints avoid that set. The set need not be finite. -/
theorem swap_factorization_avoiding (π : Perm A) (S : Set A)
    (hfix : ∀ a ∈ S, π a = a) :
    ∃ l : List (A × A),
      (l.map (fun p => swap p.1 p.2)).prod = π ∧
      ∀ p ∈ l, p.1 ≠ p.2 ∧ p.1 ∉ S ∧ p.2 ∉ S := by
  obtain ⟨l, hl, hs⟩ := swap_factorization π
  refine ⟨l, hl, ?_⟩
  intro p hp
  obtain ⟨hab, ha, hb⟩ := hs p hp
  exact ⟨hab, fun h => ha (hfix _ h), fun h => hb (hfix _ h)⟩

end NominalPackage.Perm
