import Nominal.Syntax.Substitution.Basic
import Nominal.Syntax.Problems.Properties
import Nominal.Syntax.AlphaEquiv

namespace Nominal

open Core

variable {F X 𝔸 : Type*} [DecidableEq F] [DecidableEq X] [Name 𝔸]

/-- Idempotency lifts from bare metavariables to all terms. -/
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


def Constraint.applySubst (c : Constraint F X 𝔸) (σ : Subst F X 𝔸) : Constraint F X 𝔸 :=
  match c with
  | .fresh a t => .fresh a (t.subst σ)
  | .alpha s t => .alpha (s.subst σ) (t.subst σ)

def Problem.applySubst (P : Problem F X 𝔸) (σ : Subst F X 𝔸) : Problem F X 𝔸 :=
  P.map fun c => c.applySubst σ


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

mutual
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
  | .mvar σ x =>
    simp only [ntm.permute, alphaEquiv, beq_self_eq_true, decide_eq_true_eq, true_and]
    intro m hm
    simp only [ds, Finset.mem_filter, Finset.mem_union] at hm
    obtain ⟨_, hmne⟩ := hm
    have hπn : LPermApply π (LPermApply σ m) ≠ LPermApply π' (LPermApply σ m) := by
      rw [← LPermApply_append, ← LPermApply_append]; exact hmne
    have hnds : LPermApply σ m ∈ ds π π' := by
      simp only [ds, Finset.mem_filter, Finset.mem_union]
      refine ⟨?_, hπn⟩
      by_contra hnat
      rw [not_or] at hnat
      exact hπn ((LPermApply_not_mem_atoms π _ hnat.1).trans
                 (LPermApply_not_mem_atoms π' _ hnat.2).symm)
    have hh := h _ hnds
    simp only [fresh, LPermApply_reverse_left] at hh
    exact of_decide_eq_true hh
  | .fapp f ts =>
    simp only [ntm.permute, alphaEquiv, beq_self_eq_true, decide_eq_true_eq, true_and]
    exact ntm.alphaEquivList_of_perm_fresh Γ π π' ts (fun n hn => by
      have := h n hn; simpa only [fresh] using this)
  | .abs a t' =>
    simp only [ntm.permute, alphaEquiv]
    by_cases hpa : LPermApply π a = LPermApply π' a
    · rw [if_pos hpa]
      apply ntm.alphaEquiv_of_perm_fresh
      intro n hn
      have hh := h n hn
      simp only [fresh, Bool.or_eq_true, decide_eq_true_eq] at hh
      rcases hh with rfl | hh
      · exfalso; simp only [ds, Finset.mem_filter] at hn; exact hn.2 hpa
      · exact hh
    · rw [if_neg hpa, decide_eq_true_eq]
      refine ⟨?_, ?_⟩
      · -- Part 1: alphaEquiv (permute swap ∘ permute π) (permute π') via recursion.
        rw [ntm.permute_append]
        apply ntm.alphaEquiv_of_perm_fresh
        intro n hn
        have hnne : LPermApply (π ++ [(LPermApply π' a, LPermApply π a)]) n
            ≠ LPermApply π' n := by
          simp only [ds, Finset.mem_filter] at hn; exact hn.2
        rw [LPermApply_append, LPermApply_singleton] at hnne
        have hna : n ≠ a := by
          rintro rfl
          exact hnne (by rw [swapApply_right])
        have hpn : LPermApply π n ≠ LPermApply π' n := by
          by_cases hp1 : LPermApply π n = LPermApply π' a
          · rw [hp1]; intro heq; exact hna (LPermApply_injective π' heq).symm
          · have hp2 : LPermApply π n ≠ LPermApply π a := fun heq =>
              hna (LPermApply_injective π heq)
            rwa [swapApply_other _ _ _ hp1 hp2] at hnne
        have hnds : n ∈ ds π π' := by
          simp only [ds, Finset.mem_filter, Finset.mem_union]
          refine ⟨?_, hpn⟩
          by_contra hc; rw [not_or] at hc
          exact hpn ((LPermApply_not_mem_atoms π n hc.1).trans
                     (LPermApply_not_mem_atoms π' n hc.2).symm)
        have hf := h n hnds
        simp only [fresh, Bool.or_eq_true, decide_eq_true_eq] at hf
        rcases hf with rfl | hf
        · exact absurd rfl hna
        · exact hf
      · -- Part 2: π'·a is fresh for t'.permute π, via the witness c = π⁻¹·(π'·a).
        have hc : LPermApply π.reverse (LPermApply π' a) ≠ a := by
          intro heq
          apply hpa
          have h2 := congrArg (LPermApply π) heq
          rw [LPermApply_reverse_right] at h2
          exact h2.symm
        have hπc : LPermApply π (LPermApply π.reverse (LPermApply π' a)) = LPermApply π' a :=
          LPermApply_reverse_right π _
        have hpc : LPermApply π (LPermApply π.reverse (LPermApply π' a))
            ≠ LPermApply π' (LPermApply π.reverse (LPermApply π' a)) := by
          rw [hπc]; intro heq; exact hc (LPermApply_injective π' heq).symm
        have hcds : LPermApply π.reverse (LPermApply π' a) ∈ ds π π' := by
          simp only [ds, Finset.mem_filter, Finset.mem_union]
          refine ⟨?_, hpc⟩
          by_contra hcc; rw [not_or] at hcc
          exact hpc ((LPermApply_not_mem_atoms π _ hcc.1).trans
                     (LPermApply_not_mem_atoms π' _ hcc.2).symm)
        have hf := h _ hcds
        simp only [fresh, Bool.or_eq_true, decide_eq_true_eq] at hf
        rcases hf with hca | hf
        · exact absurd hca hc
        · rw [fresh_equivariance Γ _ t' π, hπc] at hf
          exact hf

lemma ntm.alphaEquivList_of_perm_fresh (Γ : Context 𝔸 X) (π π' : LPerm 𝔸) :
    ∀ (ts : List (ntm F X 𝔸)), (∀ n ∈ ds π π', freshList Γ n ts = true) →
      alphaEquivList Γ (ts.map (·.permute π)) (ts.map (·.permute π')) = true
  | [], _ => by simp [alphaEquivList]
  | t :: ts', h => by
      simp only [List.map_cons, alphaEquivList, decide_eq_true_eq]
      refine ⟨ntm.alphaEquiv_of_perm_fresh Γ π π' t (fun n hn => ?_),
              ntm.alphaEquivList_of_perm_fresh Γ π π' ts' (fun n hn => ?_)⟩
      · have := h n hn; simp only [freshList, decide_eq_true_eq] at this; exact this.1
      · have := h n hn; simp only [freshList, decide_eq_true_eq] at this; exact this.2
end


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

/-- `x ∉ dom σ ↔ σ.lookup x = none`. -/
lemma Subst.lookup_eq_none_iff_not_mem_dom (σ : Subst F X 𝔸) (x : X) :
    Subst.lookup σ x = none ↔ x ∉ Subst.dom σ := by
  induction σ with
  | nil => simp [Subst.lookup]
  | cons p σ' ih =>
      obtain ⟨Y, s⟩ := p
      simp only [Subst.lookup_cons, Subst.dom_cons, Finset.mem_insert, not_or]
      by_cases hxY : x = Y
      · subst hxY; simp
      · rw [if_neg hxY, ih]; simp only [hxY, not_false_iff, true_and]

@[simp] lemma Subst.dom_normalize (σ : Subst F X 𝔸) :
    (σ.normalize).dom = σ.dom := by
  simp only [Subst.normalize, Subst.dom, List.map_map]
  congr 1

/-- `(normalize σ).lookupSim x = (mvar [] x).subst σ`. -/
lemma Subst.lookupSim_normalize (σ : Subst F X 𝔸) (x : X) :
    (σ.normalize).lookupSim x = (ntm.mvar (F := F) [] x).subst σ := by
  unfold Subst.lookupSim Subst.normalize
  rw [List.find?_map]
  simp only [Function.comp_def]
  cases hf : σ.find? (fun p => p.1 == x) with
  | none =>
      simp only [Option.map_none, Option.elim_none]
      have hnd : x ∉ σ.dom := by
        rw [Subst.dom, List.mem_toFinset, List.mem_map]
        rintro ⟨p, hp, hpx⟩
        have := List.find?_eq_none.mp hf p hp
        simp only [beq_iff_eq] at this
        exact this hpx
      have hnone : Subst.lookup σ x = none :=
        (Subst.lookup_eq_none_iff_not_mem_dom σ x).mpr hnd
      rw [ntm.subst_mvar_nil, hnone]; rfl
  | some p =>
      simp only [Option.map_some, Option.elim_some]
      have hpx : p.1 = x := by
        have := List.find?_some hf
        simpa using this
      rw [hpx]

end Nominal
