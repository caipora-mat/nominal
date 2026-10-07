/-
Copyright (c) 2026 Nominal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nominal contributors
-/
import Mathlib.GroupTheory.GroupAction.Support
import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic

/-!
# Support adapters for general selected actions

Injective action-preserving maps reflect arbitrary sufficient support bounds.
Same-group transport uses conjugation, not a commuting-action hypothesis.
These results concern sufficient sets, not least finite supports.
-/

namespace NominalPackage.ActionSupport

universe u v w z

section Scalar
variable {M : Type u} {B : Type v} {X : Type w} {Y : Type z}
variable [SMul M B] [SMul M X] [SMul M Y]

/-- An action-preserving map preserves any sufficient support bound. -/
theorem supports_map (f : X → Y) (hf : ∀ (m : M) x, f (m • x) = m • f x)
    {S : Set B} {x : X} (hS : MulAction.Supports M S x) :
    MulAction.Supports M S (f x) := by
  intro m hfix
  rw [← hf, hS m hfix]

/-- An injective action-preserving map also reflects sufficient support. -/
theorem supports_map_iff (f : X → Y) (hf : ∀ (m : M) x, f (m • x) = m • f x)
    (hinj : Function.Injective f) (S : Set B) (x : X) :
    MulAction.Supports M S (f x) ↔ MulAction.Supports M S x := by
  refine ⟨?_, supports_map f hf⟩
  intro h m hfix
  apply hinj
  rw [hf]
  exact h m hfix
end Scalar

section Group
open scoped Pointwise
variable {G : Type u} {B : Type v} {X : Type w}
variable [Group G] [MulAction G B] [MulAction G X]

/-- Rename a sufficient bound and its value by the same group element. -/
theorem supports_smul {S : Set B} {x : X} (hS : MulAction.Supports G S x) (g : G) :
    MulAction.Supports G (g • S) (g • x) := by
  intro h hfix
  have hc : (g⁻¹ * h * g) • x = x := hS _ (by
    intro b hb
    have hh : h • (g • b) = g • b := hfix ⟨b, hb, rfl⟩
    simp only [mul_smul, hh, inv_smul_smul])
  calc
    h • (g • x) = g • ((g⁻¹ * h * g) • x) := by
      simp only [mul_smul, smul_inv_smul]
    _ = g • x := congrArg (g • ·) hc

/-- Simultaneous transport preserves and reflects arbitrary sufficient bounds. -/
theorem supports_smul_iff (g : G) (S : Set B) (x : X) :
    MulAction.Supports G (g • S) (g • x) ↔ MulAction.Supports G S x := by
  refine ⟨?_, fun h => supports_smul h g⟩
  intro h
  simpa only [inv_smul_smul] using supports_smul h g⁻¹
end Group
end NominalPackage.ActionSupport
