import Nominal.Syntax.AlphaEquiv.Fresh
import Nominal.Syntax.AlphaEquiv.Equivariance

namespace Nominal

open Core

variable {F X 𝔸 : Type*} [DecidableEq F] [DecidableEq X] [Name 𝔸]

-- (Reflexivity of ≈α ).
mutual
/-- α-equivalence is reflexive: every term is α-equivalent to itself. -/
    theorem alphaEquiv_refl (Γ : Context 𝔸 X) (t : ntm F X 𝔸) :
        (Γ ⊢ t ≈α t) = true := by
      match t with
      | .atm a => simp [alphaEquiv]
      | .mvar σ x => simp [alphaEquiv, ds]
      | .fapp f ts =>
        simp only [alphaEquiv, decide_eq_true_eq, true_and]
        exact alphaEquivList_refl Γ ts
      | .abs a t' =>
        simp only [alphaEquiv]
        exact alphaEquiv_refl Γ t'

    theorem alphaEquivList_refl (Γ : Context 𝔸 X) (ts : List (ntm F X 𝔸)) :
        alphaEquivList Γ ts ts = true := by
      match ts with
      | [] => simp [alphaEquivList]
      | t :: tl =>
        simp only [alphaEquivList, Bool.decide_and, Bool.decide_eq_true, Bool.and_eq_true]
        exact ⟨alphaEquiv_refl Γ t, alphaEquivList_refl Γ tl⟩
  end

-- (Symmetry of ≈α ).
mutual
  /-- α-equivalence is symmetric. -/
  theorem alphaEquiv_symm (Γ : Context 𝔸 X) (s t : ntm F X 𝔸)
      (h : (Γ ⊢ s ≈α t) = true) : (Γ ⊢ t ≈α s) = true := by
    match s, t with
    | ntm.atm a, ntm.atm b =>
      simp [alphaEquiv] at *
      exact Eq.symm h
    | ntm.mvar σ x, ntm.mvar σ' y =>
      simp [alphaEquiv] at *
      obtain ⟨hxy, hds⟩ := h
      subst hxy
      simp [ds] at *
      intro n hn hneq
      apply hds n
      · exact Or.symm hn
      · intro h
        apply hneq
        exact Eq.symm h
    | ntm.fapp f ss, ntm.fapp g ts =>
      simp [alphaEquiv] at *
      obtain ⟨hfg, hα⟩ := h
      exact ⟨hfg.symm, alphaEquivList_symm Γ ss ts hα⟩
    | ntm.abs a s, ntm.abs b t =>
      simp [alphaEquiv]
      split_ifs with heq
      · subst heq
        simp [alphaEquiv] at h
        exact alphaEquiv_symm Γ s t h
      · simp [alphaEquiv] at h
        rw [if_neg (Ne.symm heq)] at h
        obtain ⟨hα, hfresh⟩ := h
        constructor
        · rw [alphaEquivPermInver Γ s t [(b,a)]] at hα
          simp at hα
          have hds : ds [(b,a)] [(a,b)] = ∅ := by simp [ds_swap_symm b a]
          rw [alphaEquiv_permute_right_ds_empty Γ s t [(b,a)] [(a,b)] hds] at hα
          exact (alphaEquiv_symm Γ s (ntm.permute [(a, b)] t)) hα

        · rw [fresh_equivariance Γ b s [(b,a)]] at hfresh
          simp at hfresh
          exact freshPreserves_alphaEquiv Γ a (ntm.permute [(b, a)] s) t hfresh hα

    | ntm.atm _, ntm.mvar _ _
    | ntm.atm _, ntm.fapp _ _
    | ntm.atm _, ntm.abs _ _
    | ntm.mvar _ _, ntm.atm _
    | ntm.mvar _ _, ntm.fapp _ _
    | ntm.mvar _ _, ntm.abs _ _
    | ntm.fapp _ _, ntm.atm _
    | ntm.fapp _ _, ntm.mvar _ _
    | ntm.fapp _ _, ntm.abs _ _
    | ntm.abs _ _, ntm.atm _
    | ntm.abs _ _, ntm.mvar _ _
    | ntm.abs _ _, ntm.fapp _ _ =>
      simp [alphaEquiv] at *

  theorem alphaEquivList_symm (Γ : Context 𝔸 X) (ss ts : List (ntm F X 𝔸))
      (h : (alphaEquivList Γ ss ts) = true) : (alphaEquivList Γ ts ss) = true := by
    match ss, ts with
    | [], [] => simp [alphaEquivList]
    | [], _ :: _ =>
      simp [alphaEquivList] at *
    | _ :: _, [] =>
      simp [alphaEquivList] at *
    | s :: ss', t :: ts' =>
      simp [alphaEquivList] at *
      exact ⟨alphaEquiv_symm Γ s t h.1, alphaEquivList_symm Γ ss' ts' h.2⟩
end

-- (Transitivity of ≈α ).
mutual
/-- α-equivalence is transitive. -/
  theorem alphaEquiv_trans (Γ : Context 𝔸 X) (t₁ t₂ t₃ : ntm F X 𝔸)
      (h₁ : (Γ ⊢ t₁ ≈α t₂) = true) (h₂ : (Γ ⊢ t₂ ≈α t₃) = true) :
      (Γ ⊢ t₁ ≈α t₃) = true := by

    match t₁, t₂ with
    | ntm.atm a, ntm.atm b =>
      match t₃ with
      | ntm.atm c =>
        simp [alphaEquiv] at *
        subst h₁
        trivial
      | ntm.mvar _ _ | ntm.fapp _ _ | ntm.abs _ _ => simp [alphaEquiv] at h₂

    | ntm.mvar π₁ x, ntm.mvar π₂ y =>
      match t₃ with
      | ntm.mvar π₃ z =>
        simp [alphaEquiv] at *
        obtain ⟨hxy, h12⟩ := h₁
        obtain ⟨hyz, h23⟩ := h₂
        subst hxy
        simp [hyz]
        subst hyz
        intro n hn
        have h : n ∈ ds π₁ π₂ ∨ n ∈ ds π₂ π₃ :=
          ds_trans π₁ π₂ π₃ n hn
        cases h with
        | inl h12n => exact h12 n h12n
        | inr h23n => exact h23 n h23n
      | ntm.atm _ | ntm.fapp _ _ | ntm.abs _ _ => simp [alphaEquiv] at h₂

    | ntm.fapp f ts₁, ntm.fapp g ts₂ =>
      match t₃ with
      | ntm.fapp h ts₃ =>
        simp only [alphaEquiv, decide_eq_true_eq] at *
        obtain ⟨hfg, hl12⟩ := h₁
        obtain ⟨hgh, hl23⟩ := h₂
        subst hfg; subst hgh
        exact ⟨rfl, alphaEquivList_trans Γ ts₁ ts₂ ts₃ hl12 hl23⟩
      | ntm.mvar _ _ | ntm.atm _ | ntm.abs _ _ => simp [alphaEquiv] at h₂

    | ntm.abs a t₁, ntm.abs b t₂ =>
      match t₃ with
      | ntm.abs c t₃ =>
        simp [alphaEquiv] at *
        by_cases hab : a = b
        · by_cases hbc : b = c
          · -- all equal: a = b = c
            subst hab; subst hbc
            simp at *
            exact alphaEquiv_trans Γ t₁ t₂ t₃ h₁ h₂
          · -- a = b, but c different
            subst hab
            simp [hbc] at *
            constructor
            · rw [alphaEquiv_equivariance Γ t₁ t₂ [(c,a)]] at h₁
              exact alphaEquiv_trans Γ (ntm.permute [(c, a)] t₁) (ntm.permute [(c, a)] t₂) t₃ h₁ h₂.1
            · exact freshPreserves_alphaEquiv Γ c t₂ t₁ h₂.2 (alphaEquiv_symm Γ t₁ t₂ h₁)
        · by_cases hbc : b = c
          · -- b = c, a different
            subst hbc
            simp [hab] at *
            constructor
            · exact alphaEquiv_trans Γ (ntm.permute [(b, a)] t₁) t₂ t₃ h₁.1 h₂
            · exact h₁.2
          · by_cases hac : a = c
            · -- a = c, b different
              subst hac
              simp [hab, hbc] at *
              rw [alphaEquivPermInver Γ t₁ t₂ [(b, a)]] at h₁
              simp at h₁
              have hdssymm : ds [(a, b)] [(b, a)] = ∅ := ds_swap_symm a b
              rw [<- alphaEquiv_permute_right_ds_empty Γ t₁ t₂ [(a, b)] [(b, a)] hdssymm] at h₁
              exact alphaEquiv_trans Γ t₁ (ntm.permute [(a, b)] t₂) t₃ h₁.1 h₂.1
            · -- all different
              simp [hab, hbc, hac] at h₁ h₂ ⊢
              obtain ⟨h₁α, h₁fresh⟩ := h₁
              obtain ⟨h₂α, h₂fresh⟩ := h₂
              constructor
              · have hds : ds [(c,a)] ([(b,a)] ++ [(c,b)]) = {b, c} := by
                  simp [ds, LPerm.atoms]
                  ext n
                  simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton, swapApply]
                  constructor
                  · rintro ⟨hmem, hne⟩
                    rcases hmem with rfl | rfl | rfl
                    · right; rfl
                    · exfalso; apply hne
                      split_ifs <;> simp_all <;> tauto
                    · left; rfl
                  · rintro (rfl | rfl)
                    · refine ⟨Or.inr (Or.inr rfl), ?_⟩
                      split_ifs <;> simp_all <;> tauto
                    · refine ⟨Or.inl rfl, ?_⟩
                      split_ifs <;> simp_all <;> tauto

                have hct1 : (Γ ⊢ c # t₁) = true := by
                  have hc₂ : (Γ ⊢ c # ntm.permute [(b, a)] t₁) = true :=
                    freshPreserves_alphaEquiv Γ c t₂ _ h₂fresh
                    (alphaEquiv_symm Γ _ _ ‹_›)
                  rw [show c = swapApply (b,a) c from
                    (swapApply_other b a c (Ne.symm hbc) (Ne.symm hac)).symm] at hc₂
                  rw [<- LPermApply_singleton, <- fresh_equivariance] at hc₂
                  exact hc₂

                have hinv : (Γ ⊢ ntm.permute [(c, a)] t₁ ≈α
                      ntm.permute ([(b, a)] ++ [(c, b)]) t₁) = true := by
                  apply alphaEquiv_invariance_mp
                  intro n hn
                  rw [hds] at hn
                  rcases Finset.mem_insert.mp hn with rfl | hn
                  · exact h₁fresh
                  · rw [Finset.mem_singleton] at hn; subst hn; exact hct1

                rw [alphaEquiv_equivariance Γ (ntm.permute [(b, a)] t₁) t₂ [(c, b)]] at h₁α
                rw [ntm.permute_append] at h₁α
                exact alphaEquiv_trans Γ _ _ _ (alphaEquiv_trans Γ _ _ _ hinv h₁α) h₂α

              · have hc₂ : (Γ ⊢ c # ntm.permute [(b,a)] t₁) = true := freshPreserves_alphaEquiv Γ c t₂ (ntm.permute [(b, a)] t₁) h₂fresh (alphaEquiv_symm Γ (ntm.permute [(b, a)] t₁) t₂ h₁α)
                rw [show c = swapApply (b,a) c from (swapApply_other b a c (Ne.symm hbc) (Ne.symm hac)).symm] at hc₂
                rw [<- LPermApply_singleton, <- fresh_equivariance Γ c t₁ [(b, a)]] at hc₂
                exact hc₂
      | ntm.mvar _ _ | ntm.fapp _ _ | ntm.atm _ => simp [alphaEquiv] at h₂

    | ntm.atm _, ntm.mvar _ _
    | ntm.atm _, ntm.fapp _ _
    | ntm.atm _, ntm.abs _ _
    | ntm.mvar _ _, ntm.atm _
    | ntm.mvar _ _, ntm.fapp _ _
    | ntm.mvar _ _, ntm.abs _ _
    | ntm.fapp _ _, ntm.atm _
    | ntm.fapp _ _, ntm.mvar _ _
    | ntm.fapp _ _, ntm.abs _ _
    | ntm.abs _ _, ntm.atm _
    | ntm.abs _ _, ntm.mvar _ _
    | ntm.abs _ _, ntm.fapp _ _ => simp [alphaEquiv] at h₁
  termination_by ntmSize t₁
  decreasing_by all_goals simp [ntmSize, ntmPermSize]

  theorem alphaEquivList_trans (Γ : Context 𝔸 X) (ts₁ ts₂ ts₃ : List (ntm F X 𝔸))
      (h₁ : (alphaEquivList Γ ts₁ ts₂) = true) (h₂ : (alphaEquivList Γ ts₂ ts₃) = true) :
      (alphaEquivList Γ ts₁ ts₃) = true := by
    match ts₁, ts₂, ts₃ with
    | [], [], []
    | [], _ :: _,  _ :: _
    | _ :: _, [], _ :: _
    | _ :: _, _ :: _, [] => simp [alphaEquivList] at *
    | t₁ :: ts₁, t₂ :: ts₂, t₃ :: ts₃ =>
      simp [alphaEquivList] at *
      exact ⟨alphaEquiv_trans Γ t₁ t₂ t₃ h₁.1 h₂.1, alphaEquivList_trans Γ ts₁ ts₂ ts₃ h₁.2 h₂.2⟩
  termination_by ntmSize.ntmSizeList ts₁
  decreasing_by
    · simp [ntmSize.ntmSizeList]
      omega
    · simp [ntmSize.ntmSizeList]
end

-- (Congruence of ≈α — second half of Theorem 24.)

/-- Congruence under abstraction: if `s ≈α t` then `[a]s ≈α [a]t`. (≈αabsa) -/
theorem alphaEquiv_abs_congr (Γ : Context 𝔸 X) (a : 𝔸) (s t : ntm F X 𝔸)
    (h : (Γ ⊢ s ≈α t) = true) :
    (Γ ⊢ ntm.abs a s ≈α ntm.abs a t) = true := by
  simp only [alphaEquiv, if_true]
  exact h

/-- Congruence under permutation: if `s ≈α t` then `π·s ≈α π·t`. (Lemma 21) -/
theorem alphaEquiv_permute_congr (Γ : Context 𝔸 X) (s t : ntm F X 𝔸) (π : LPerm 𝔸)
    (h : (Γ ⊢ s ≈α t) = true) :
    (Γ ⊢ s.permute π ≈α t.permute π) = true := by
  rw [← alphaEquiv_equivariance]
  exact h

/-- Congruence under tuple position: replacing one position in a list of arguments by an
    α-equivalent term preserves the list-level α-equivalence. -/
theorem alphaEquivList_replace_congr (Γ : Context 𝔸 X)
    (us₁ us₂ : List (ntm F X 𝔸)) (s t : ntm F X 𝔸)
    (h : (Γ ⊢ s ≈α t) = true) :
    alphaEquivList Γ (us₁ ++ s :: us₂) (us₁ ++ t :: us₂) = true := by
  induction us₁ with
  | nil =>
    simp only [List.nil_append, alphaEquivList,
               Bool.decide_and, Bool.decide_eq_true, Bool.and_eq_true]
    exact ⟨h, alphaEquivList_refl Γ us₂⟩
  | cons u us ih =>
    simp only [List.cons_append, alphaEquivList,
               Bool.decide_and, Bool.decide_eq_true, Bool.and_eq_true]
    exact ⟨alphaEquiv_refl Γ u, ih⟩

/-- Congruence under function application: replacing one argument by an α-equivalent term
    preserves α-equivalence of the application. (≈αtup) -/
theorem alphaEquiv_fapp_congr (Γ : Context 𝔸 X) (f : F)
    (us₁ us₂ : List (ntm F X 𝔸)) (s t : ntm F X 𝔸)
    (h : (Γ ⊢ s ≈α t) = true) :
    (Γ ⊢ ntm.fapp f (us₁ ++ s :: us₂) ≈α ntm.fapp f (us₁ ++ t :: us₂)) = true := by
  simp only [alphaEquiv, Bool.decide_and, Bool.decide_eq_true, Bool.and_eq_true,
             decide_eq_true_eq]
  exact ⟨trivial, alphaEquivList_replace_congr Γ us₁ us₂ s t h⟩

end Nominal
