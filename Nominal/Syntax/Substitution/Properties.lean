import Nominal.Syntax.Substitution.Basic
import Nominal.Syntax.Problems.Properties
import Nominal.Syntax.AlphaEquiv

namespace Nominal

open Core

variable {F X 𝔸 : Type*} [DecidableEq F] [DecidableEq X] [Name 𝔸]

-- (Lemma 22: Substitution preserves alpha-equivalence and freshness).

mutual
  /-- Lemma 22: single-variable substitution preserves alpha-equivalence.
      If `Γ ⊢ s ≈α t` then `Γ ⊢ u[Y↦s] ≈α u[Y↦t]`. -/
  theorem ntm.applyOne_alphaEquiv_congr
      (Γ : Context 𝔸 X) (u : ntm F X 𝔸) (Y : X) (s t : ntm F X 𝔸)
      (h : (Γ ⊢ s ≈α t) = true) :
      alphaEquiv Γ (u.applyOne Y s) (u.applyOne Y t) = true := by
    match u with
    | .atm a => simp [applyOne, alphaEquiv_refl]
    | .mvar π x =>
      simp only [applyOne]
      by_cases hx : x = Y
      · rw [if_pos hx, if_pos hx]
        exact alphaEquiv_permute_congr Γ s t π h
      · rw [if_neg hx, if_neg hx, alphaEquiv_refl]
    | .fapp f ts =>
      simp [applyOne, alphaEquiv] 
      exact alphaEquivList_applyOne_congr Γ ts Y s t h
    | .abs a u' =>
      simp only [applyOne, alphaEquiv]
      exact ntm.applyOne_alphaEquiv_congr Γ u' Y s t h

  /-- List version of substitutivity for alpha-equivalence. -/
  theorem ntm.alphaEquivList_applyOne_congr
      (Γ : Context 𝔸 X) (us : List (ntm F X 𝔸)) (Y : X) (s t : ntm F X 𝔸)
      (h : alphaEquiv Γ s t = true) :
      alphaEquivList Γ (us.map fun u => u.applyOne Y s) (us.map fun u => u.applyOne Y t) = true := by
    match us with
    | [] => simp [alphaEquivList]
    | u :: us' =>
      simp [alphaEquivList]
      constructor
      · exact ntm.applyOne_alphaEquiv_congr Γ u Y s t h
      ·         exact ntm.alphaEquivList_applyOne_congr Γ us' Y s t h
end

/-- Freshness is preserved by congruent single-variable substitution.
    If `alphaEquiv Γ s t` then `(Γ ⊢ a # u[Y↦s]) = (Γ ⊢ a # u[Y↦t])`. -/
theorem ntm.applyOne_fresh_congr
    (Γ : Context 𝔸 X) (a : 𝔸) (u : ntm F X 𝔸) (Y : X) (s t : ntm F X 𝔸)
    (h : alphaEquiv Γ s t = true) :
    (Γ ⊢ a # u.applyOne Y s) = (Γ ⊢ a # u.applyOne Y t) := by
  have h_st : alphaEquiv Γ (u.applyOne Y s) (u.applyOne Y t) = true :=
    ntm.applyOne_alphaEquiv_congr Γ u Y s t h
  have h_ts : alphaEquiv Γ (u.applyOne Y t) (u.applyOne Y s) = true :=
    alphaEquiv_symm Γ (u.applyOne Y s) (u.applyOne Y t) h_st
  by_cases h : fresh Γ a (u.applyOne Y s)
  · simp [h]
    exact freshPreserves_alphaEquiv Γ a (u.applyOne Y s) (u.applyOne Y t) h h_st
  · simp [h]
    by_contra h_contra
    push_neg at h_contra
    simp at h_contra
    have := freshPreserves_alphaEquiv Γ a (u.applyOne Y t) (u.applyOne Y s) h_contra h_ts
    simp at h
    simp [h] at this


-- (Corollary 25: Derivability preserved under substitution of equals).

/-- Corollary 25(1): constraint entailment preserved under alpha-equivalent substitution. -/
theorem Constraint.applyOne_entails_congr
    (Γ : Context 𝔸 X) (c : Constraint F X 𝔸) (Y : X) (s t : ntm F X 𝔸)
    (h : alphaEquiv Γ s t = true) :
    (c.applyOne Y s |>.Entails Γ) = (c.applyOne Y t |>.Entails Γ) := by
  match c with
  | .fresh a u =>
    simp only [Constraint.applyOne, Constraint.Entails, fresh]
    exact ntm.applyOne_fresh_congr Γ a u Y s t h
  | .alpha u v =>
    simp only [Constraint.applyOne, Constraint.Entails, alphaEquiv]
    have h1 : alphaEquiv Γ (u.applyOne Y s) (u.applyOne Y t) = true :=
      ntm.applyOne_alphaEquiv_congr Γ u Y s t h
    have h2 : alphaEquiv Γ (v.applyOne Y s) (v.applyOne Y t) = true :=
      ntm.applyOne_alphaEquiv_congr Γ v Y s t h
    have h3 : alphaEquiv Γ (u.applyOne Y t) (u.applyOne Y s) = true :=
      alphaEquiv_symm Γ (u.applyOne Y s) (u.applyOne Y t) h1
    have h4 : alphaEquiv Γ (v.applyOne Y t) (v.applyOne Y s) = true :=
      alphaEquiv_symm Γ (v.applyOne Y s) (v.applyOne Y t) h2
    by_cases h_lhs : alphaEquiv Γ (u.applyOne Y s) (v.applyOne Y s)
    · simp [h_lhs]
      exact alphaEquiv_trans Γ (u.applyOne Y t) (u.applyOne Y s) (v.applyOne Y t)
        h3 (alphaEquiv_trans Γ (u.applyOne Y s) (v.applyOne Y s) (v.applyOne Y t)
        h_lhs h2)
    · simp [h_lhs]
      by_contra h_contra
      push_neg at h_contra
      simp at h_contra
      have := alphaEquiv_trans Γ (u.applyOne Y s) (u.applyOne Y t) (v.applyOne Y s)
        h1 (alphaEquiv_trans Γ (u.applyOne Y t) (v.applyOne Y t) (v.applyOne Y s)
        h_contra h4)
      exact h_lhs this

/-- Corollary 25(1): problem entailment preserved under alpha-equivalent substitution. -/
theorem Problem.applyOne_entails_congr
    (Γ : Context 𝔸 X) (P : Problem F X 𝔸) (Y : X) (s t : ntm F X 𝔸)
    (h : alphaEquiv Γ s t = true) :
    Problem.Entails Γ (P.applyOne Y s) ↔ Problem.Entails Γ (P.applyOne Y t) := by
  simp only [Problem.Entails, Problem.applyOne, List.mem_map]
  constructor
  · intro hP c' ⟨c, hc, hc'⟩
    subst hc'
    have h_eq : (c.applyOne Y s |>.Entails Γ) = (c.applyOne Y t |>.Entails Γ) :=
      Constraint.applyOne_entails_congr Γ c Y s t h
    rw [← h_eq]
    exact hP (c.applyOne Y s) ⟨c, hc, rfl⟩
  · intro hP c' ⟨c, hc, hc'⟩
    subst hc'
    have h_eq : (c.applyOne Y s |>.Entails Γ) = (c.applyOne Y t |>.Entails Γ) :=
      Constraint.applyOne_entails_congr Γ c Y s t h
    rw [h_eq]
    exact hP (c.applyOne Y t) ⟨c, hc, rfl⟩

end Nominal
