import Nominal.Syntax.Unification.Basic

namespace Nominal

open Core

variable {F X 𝔸 : Type*} [DecidableEq F] [DecidableEq X] [Name 𝔸]

-- (Lemma 29: Partial order properties of instantiation ordering).

/-- Reflexivity of instantiation ordering: every solution is ≤ itself. -/
theorem Solution.le_refl (sol : Solution F X 𝔸) : sol ≤ sol := by
  use []
  simp only [ntm.subst_nil]
  constructor
  · intro Y
    exact alphaEquiv_refl sol.ctx ((ntm.mvar [] Y).subst sol.subst)
  · intro a x hax
    simp [fresh]
    exact hax

/-- Transitivity of instantiation ordering. -/
theorem Solution.le_trans {sol₁ sol₂ sol₃ : Solution F X 𝔸}
    (h₁ : sol₁ ≤ sol₂) (h₂ : sol₂ ≤ sol₃) : sol₁ ≤ sol₃ := by
  obtain ⟨σ₁, h1_alpha, h1_entails⟩ := h₁
  obtain ⟨σ₂, h2_alpha, h2_entails⟩ := h₂
  use σ₁ ++ σ₂
  constructor
  · intro Y
    sorry
  · intro a x hax
    sorry

/-- Antisymmetry of instantiation ordering (if provable). -/
theorem Solution.le_antisymm {sol₁ sol₂ : Solution F X 𝔸}
    (h₁ : sol₁ ≤ sol₂) (h₂ : sol₂ ≤ sol₁) : sol₁ = sol₂ := by
  sorry

/-- The instantiation ordering is a partial order. -/
instance : PartialOrder (Solution F X 𝔸) where
  le := (· ≤ ·)
  le_refl := Solution.le_refl
  le_trans := fun _ _ _ => Solution.le_trans
  le_antisymm := fun _ _ => Solution.le_antisymm

end Nominal
