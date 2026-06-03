import Nominal.Syntax.Substitution.Basic
import Nominal.Syntax.Problems.Properties
import Nominal.Syntax.AlphaEquiv

namespace Nominal

open Core

variable {F X 𝔸 : Type*} [DecidableEq F] [DecidableEq X] [Name 𝔸]

-- (Composition of substitutions: subst is functorial wrt list concatenation).

/-- `t.subst (σ ++ σ') = (t.subst σ).subst σ'`: substitution lists compose by append. -/
@[simp] lemma ntm.subst_append (t : ntm F X 𝔸) (σ σ' : Subst F X 𝔸) :
    t.subst (σ ++ σ') = (t.subst σ).subst σ' := by
  induction σ generalizing t with
  | nil => rfl
  | cons p σ ih =>
    obtain ⟨Y, s⟩ := p
    simp only [List.cons_append, ntm.subst_cons]
    exact ih _

/-- An idempotent substitution is idempotent on all terms, not just on bare metavariables. -/
lemma ntm.subst_idempotent {σ : Subst F X 𝔸} (hσ : σ.IsIdempotent) (t : ntm F X 𝔸) :
    (t.subst σ).subst σ = t.subst σ := by
  match t with
  | .atm a => simp
  | .mvar π x =>
    rw [ntm.subst_mvar, ntm.subst_permute, ← hσ x]
  | .fapp f ts =>
    simp only [ntm.subst_fapp, List.map_map]
    congr 1
    apply List.map_congr_left
    intro u _
    exact ntm.subst_idempotent hσ u
  | .abs b t' =>
    simp only [ntm.subst_abs]
    rw [ntm.subst_idempotent hσ t']

-- (Applying a full substitution to constraints and problems).

def Constraint.applySubst (c : Constraint F X 𝔸) (σ : Subst F X 𝔸) : Constraint F X 𝔸 :=
  match c with
  | .fresh a t => .fresh a (t.subst σ)
  | .alpha s t => .alpha (s.subst σ) (t.subst σ)

def Problem.applySubst (P : Problem F X 𝔸) (σ : Subst F X 𝔸) : Problem F X 𝔸 :=
  P.map fun c => c.applySubst σ

-- (Lemma 22: substitution preserves freshness and alpha-equivalence).
-- Hypothesis `hctx` encodes that Γ' satisfies all freshness constraints of Γ after applying σ,
-- i.e. Γ' ≥ ⟨Γσ⟩_nf in the paper's sense.

mutual
  /-- Lemma 22(a): freshness preserved by substitution. -/
  lemma ntm.fresh_subst (Γ Γ' : Context 𝔸 X) (σ : Subst F X 𝔸) (a : 𝔸) (t : ntm F X 𝔸)
      (hctx : ∀ p ∈ Γ, (Γ' ⊢ p.1 # (ntm.mvar (F := F) [] p.2).subst σ) = true)
      (h : (Γ ⊢ a # t) = true) :
      (Γ' ⊢ a # t.subst σ) = true := by
    match t with
    | .atm b =>
      simp only [ntm.subst_atm, fresh_atm] at h ⊢
      exact h
    | .mvar π y => 
      simp only [fresh, decide_eq_true_eq] at h
      have hkey := hctx ⟨LPermApply π.reverse a, y⟩ h
      simp at hkey
      rw [ntm.subst_mvar]
      -- fresh_equivariance: (Γ' ⊢ b # t) = (Γ' ⊢ LPermApply π b # t.permute π)
      -- instantiate with b := LPermApply π.reverse a, then use LPermApply_reverse_right
      conv_lhs => rw [show a = LPermApply π (LPermApply π.reverse a)
                          from (LPermApply_reverse_right π a).symm]
      rw [← fresh_equivariance]
      exact hkey
    | .fapp f ts =>
      simp only [ntm.subst_fapp, fresh] at h ⊢
      exact ntm.freshList_subst Γ Γ' σ a ts hctx h

    | .abs b t =>
      rw [ntm.subst_abs]
      simp [fresh] at h ⊢
      rcases h with hab | ht
      · left; exact hab
      · right; exact ntm.fresh_subst Γ Γ' σ a t hctx ht
      
  lemma ntm.freshList_subst (Γ Γ' : Context 𝔸 X) (σ : Subst F X 𝔸) (a : 𝔸)
      (ts : List (ntm F X 𝔸))
      (hctx : ∀ p ∈ Γ, (Γ' ⊢ p.1 # (ntm.mvar (F := F) [] p.2).subst σ) = true)
      (h : freshList Γ a ts = true) :
      freshList Γ' a (ts.map (·.subst σ)) = true := by
    match ts with
    | [] => simp [freshList]
    | hd :: tl =>
      simp [List.map_cons, freshList] at h ⊢
      obtain ⟨hhd, htl⟩ := h
      exact ⟨ntm.fresh_subst Γ Γ' σ a hd hctx hhd,
             ntm.freshList_subst Γ Γ' σ a tl hctx htl⟩
end

/-- If every atom where π and π' differ is fresh for t, then π·t ≈α π'·t. -/
lemma ntm.alphaEquiv_of_perm_fresh (Γ : Context 𝔸 X) (π π' : LPerm 𝔸) (t : ntm F X 𝔸)
    (h : ∀ n ∈ ds π π', (Γ ⊢ n # t) = true) :
    (Γ ⊢ t.permute π ≈α t.permute π') = true := by
  match t with
  | .atm a =>
    simp [permute, alphaEquiv, fresh] at h ⊢
    by_contra hne
    simp [ds] at h
    push_neg at hne
    by_cases hmem : a ∈ LPerm.atoms π ∪ LPerm.atoms π'
    · simp at hmem
      exact hne (h hmem)
    · rw [Finset.mem_union, not_or] at hmem
      exact hne ((LPermApply_not_mem_atoms π a hmem.1).trans
               (LPermApply_not_mem_atoms π' a hmem.2).symm)
  | .mvar σ x
  | .fapp f ts
  | .abs a t => 
    sorry


mutual
  /-- Lemma 22(b): alpha-equivalence preserved by substitution. -/
  lemma ntm.alphaEquiv_subst (Γ Γ' : Context 𝔸 X) (σ : Subst F X 𝔸) (s t : ntm F X 𝔸)
      (hctx : ∀ p ∈ Γ, (Γ' ⊢ p.1 # (ntm.mvar (F := F) [] p.2).subst σ) = true)
      (h : (Γ ⊢ s ≈α t) = true) :
      (Γ' ⊢ s.subst σ ≈α t.subst σ) = true := by
    match s, t with
    | .atm a, .atm b =>
      simp [ntm.subst_atm, alphaEquiv] at h ⊢
      exact h
    | .mvar π x, .mvar π' y =>
      simp only [alphaEquiv, Bool.decide_and, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨hxy, hds⟩ := h
      subst hxy
      rw [ntm.subst_mvar π, ntm.subst_mvar π']
      apply ntm.alphaEquiv_of_perm_fresh
      intro n hn
      exact hctx ⟨n, x⟩ (hds n hn)
    | .fapp f ss, .fapp g ts =>
      simp [alphaEquiv] at h
      obtain ⟨hfg, hlist⟩ := h
      subst hfg
      simp [ntm.subst_fapp, alphaEquiv]
      exact ntm.alphaEquivList_subst Γ Γ' σ ss ts hctx hlist
    | .abs a s', .abs b t' =>
      simp only [ntm.subst_abs, alphaEquiv] at h ⊢
      by_cases hab : a = b
      · simp only [if_pos hab] at h ⊢
        exact ntm.alphaEquiv_subst Γ Γ' σ s' t' hctx h
      · simp [if_neg hab] at h ⊢
        obtain ⟨haα, hbs⟩ := h
        refine ⟨?_, ntm.fresh_subst Γ Γ' σ b s' hctx hbs⟩
        have := ntm.alphaEquiv_subst Γ Γ' σ (s'.permute [(b, a)]) t' hctx haα
        rwa [ntm.subst_permute] at this
    
    | .atm _, .mvar _ _ | .atm _, .fapp _ _ | .atm _, .abs _ _
    | .mvar _ _, .atm _ | .mvar _ _, .fapp _ _ | .mvar _ _, .abs _ _
    | .fapp _ _, .atm _ | .fapp _ _, .mvar _ _ | .fapp _ _, .abs _ _
    | .abs _ _, .atm _ | .abs _ _, .mvar _ _ | .abs _ _, .fapp _ _ =>
      simp [alphaEquiv] at h

  lemma ntm.alphaEquivList_subst (Γ Γ' : Context 𝔸 X) (σ : Subst F X 𝔸)
      (ss ts : List (ntm F X 𝔸))
      (hctx : ∀ p ∈ Γ, (Γ' ⊢ p.1 # (ntm.mvar (F := F) [] p.2).subst σ) = true)
      (h : alphaEquivList Γ ss ts = true) :
      alphaEquivList Γ' (ss.map (·.subst σ)) (ts.map (·.subst σ)) = true := by
    match ss, ts with
    | [], [] => simp [alphaEquivList]
    | [], _ :: _ | _ :: _, [] => simp [alphaEquivList] at h
    | s :: ss', t :: ts' =>
      simp [List.map_cons, alphaEquivList] at h ⊢
      obtain ⟨hst, hsts⟩ := h
      exact ⟨ntm.alphaEquiv_subst Γ Γ' σ s t hctx hst,
             ntm.alphaEquivList_subst Γ Γ' σ ss' ts' hctx hsts⟩
end

/-- Lemma 22 (general): problem derivability preserved by substitution. -/
lemma Problem.entails_subst (Γ Γ' : Context 𝔸 X) (σ : Subst F X 𝔸) (P : Problem F X 𝔸)
    (hctx : ∀ p ∈ Γ, (Γ' ⊢ p.1 # (ntm.mvar (F := F) [] p.2).subst σ) = true)
    (h : Problem.Entails Γ P) :
    Problem.Entails Γ' (P.applySubst σ) := by
  match P with
  | [] => simp [applySubst, Entails]
  | P :: Ps =>
    simp [applySubst, Entails] at h ⊢ 
    obtain ⟨hP, hPs⟩ := h
    refine ⟨?_, fun c hc => ?_⟩
    · cases P with
      | fresh a t =>
        simp [Constraint.Entails, Constraint.applySubst] at hP ⊢
        exact ntm.fresh_subst Γ Γ' σ a t hctx hP
      | alpha s t =>
        simp [Constraint.Entails, Constraint.applySubst] at hP ⊢
        exact ntm.alphaEquiv_subst Γ Γ' σ s t hctx hP
    · have hc' := hPs c hc
      cases c with
      | fresh a t =>
        simp [Constraint.Entails, Constraint.applySubst] at hc' ⊢
        exact ntm.fresh_subst Γ Γ' σ a t hctx hc'
      | alpha s t =>
        simp [Constraint.Entails, Constraint.applySubst] at hc' ⊢
        exact ntm.alphaEquiv_subst Γ Γ' σ s t hctx hc'

-- (Corollary 25: alpha-equivalent substitution preserves derivability).

mutual
  /-- Corollary 25: if Γ ⊢ s ≈α t then Γ ⊢ u[Y↦s] ≈α u[Y↦t]. -/
  lemma ntm.applyOne_alphaEquiv_congr
      (Γ : Context 𝔸 X) (u : ntm F X 𝔸) (Y : X) (s t : ntm F X 𝔸)
      (h : (Γ ⊢ s ≈α t) = true) :
      (Γ ⊢ u.applyOne Y s ≈α u.applyOne Y t) = true := by
    sorry

  lemma ntm.alphaEquivList_applyOne_congr
      (Γ : Context 𝔸 X) (us : List (ntm F X 𝔸)) (Y : X) (s t : ntm F X 𝔸)
      (h : (Γ ⊢ s ≈α t) = true) :
      alphaEquivList Γ (us.map (·.applyOne Y s)) (us.map (·.applyOne Y t)) = true := by
    sorry
end

/-- Corollary 25: freshness preserved by alpha-equivalent single substitution. -/
lemma ntm.applyOne_fresh_congr
    (Γ : Context 𝔸 X) (a : 𝔸) (u : ntm F X 𝔸) (Y : X) (s t : ntm F X 𝔸)
    (h : (Γ ⊢ s ≈α t) = true) :
    (Γ ⊢ a # u.applyOne Y s) = (Γ ⊢ a # u.applyOne Y t) := by
  sorry

/-- Corollary 25(1): constraint entailment preserved by alpha-equivalent single substitution. -/
theorem Constraint.applyOne_entails_congr
    (Γ : Context 𝔸 X) (c : Constraint F X 𝔸) (Y : X) (s t : ntm F X 𝔸)
    (h : (Γ ⊢ s ≈α t) = true) :
    (c.applyOne Y s).Entails Γ = (c.applyOne Y t).Entails Γ := by
  sorry

/-- Corollary 25(1): problem entailment preserved by alpha-equivalent single substitution. -/
theorem Problem.applyOne_entails_congr
    (Γ : Context 𝔸 X) (P : Problem F X 𝔸) (Y : X) (s t : ntm F X 𝔸)
    (h : (Γ ⊢ s ≈α t) = true) :
    Problem.Entails Γ (P.applyOne Y s) ↔ Problem.Entails Γ (P.applyOne Y t) := by
  sorry

end Nominal
