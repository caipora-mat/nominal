import Nominal.Syntax.AlphaEquiv.Basic

namespace Nominal

open Core

variable {F X 𝔸 : Type*} [DecidableEq F] [DecidableEq X] [Name 𝔸]

mutual
/-- If `π` and `π'` agree on all atoms (empty difference set), permuting the left-hand side
    by either gives the same α-equivalence judgement. -/
  theorem alphaEquiv_permute_left_ds_empty (Γ : Context 𝔸 X) (s t : ntm F X 𝔸) (π π' : LPerm 𝔸)
      (h : ds π π' = ∅) :
      (Γ ⊢ ntm.permute π s ≈α t) = (Γ ⊢ ntm.permute π' s ≈α t) := by
    match s, t with
    | ntm.atm a, ntm.atm b =>
      simp [ntm.permute, alphaEquiv, LPermApply_eq_of_ds_empty π π' h]

    | ntm.mvar σ x, ntm.mvar σ' y =>
      simp only [ntm.permute, alphaEquiv, Bool.decide_and]
      congr
      rw [ds_append_eq_of_ds_empty σ σ' π π' h]

    | ntm.fapp f ss, ntm.fapp g ts =>
      simp only [ntm.permute, alphaEquiv]
      rw [alphaEquivList_permute_left_ds_empty Γ ss ts π π' h]

    | ntm.abs a s', ntm.abs b t' =>
      simp only [ntm.permute, alphaEquiv, Bool.decide_and, Bool.decide_eq_true]
      rw [LPermApply_eq_of_ds_empty π π' h]
      split_ifs with hcase
      · apply alphaEquiv_permute_left_ds_empty Γ s' t' π π'
        exact h
      · rw [ntm.permute_append, ntm.permute_append]
        rw [alphaEquiv_permute_left_ds_empty Γ s' t' (π ++ [(b, LPermApply π' a)]) (π' ++ [(b, LPermApply π' a)])]
        · rw [fresh_permute_ds_empty Γ b s' π π' h]
        rw [<- ds_append]
        exact h

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
      simp [ntm.permute, alphaEquiv]

  theorem alphaEquivList_permute_left_ds_empty (Γ : Context 𝔸 X) (ss ts : List (ntm F X 𝔸))
      (π π' : LPerm 𝔸) (h : ds π π' = ∅) :
      alphaEquivList Γ (ss.map (ntm.permute π)) ts =
        alphaEquivList Γ (ss.map (ntm.permute π')) ts := by
    match ss, ts with
    | [], [] => simp [alphaEquivList]
    | [], _ :: _ => simp [alphaEquivList]
    | _ :: _, [] => simp [alphaEquivList]
    | s :: ss', t :: ts' =>
      simp only [List.map_cons, alphaEquivList]
      rw [alphaEquiv_permute_left_ds_empty Γ s t π π' h,
          alphaEquivList_permute_left_ds_empty Γ ss' ts' π π' h]
end

mutual
/-- If `π` and `π'` agree on all atoms, permuting the right-hand side by either gives the same
    α-equivalence judgement. -/
  theorem alphaEquiv_permute_right_ds_empty (Γ : Context 𝔸 X) (s t : ntm F X 𝔸) (π π' : LPerm 𝔸)
      (h : ds π π' = ∅) :
      (Γ ⊢ s ≈α ntm.permute π t) = (Γ ⊢ s ≈α ntm.permute π' t) := by
    match s, t with
    | ntm.atm a, ntm.atm b =>
      simp [ntm.permute, alphaEquiv, LPermApply_eq_of_ds_empty π π' h]

    | ntm.mvar σ x, ntm.mvar σ' y =>
      simp only [ntm.permute, alphaEquiv, Bool.decide_and]
      congr
      rw [ds_comm σ (σ' ++ π), ds_comm σ (σ' ++ π')]
      rw [ds_append_eq_of_ds_empty σ' σ π π' h]

    | ntm.fapp f ss, ntm.fapp g ts =>
      simp only [ntm.permute, alphaEquiv]
      rw [alphaEquivList_permute_right_ds_empty Γ ss ts π π' h]

    | ntm.abs a s', ntm.abs b t' =>
      simp only [ntm.permute, alphaEquiv, Bool.decide_and, Bool.decide_eq_true]
      rw [LPermApply_eq_of_ds_empty π π' h]
      split_ifs with hcase
      · apply alphaEquiv_permute_right_ds_empty Γ s' t' π π'
        exact h
      · rw [alphaEquiv_permute_right_ds_empty Γ (ntm.permute [(LPermApply π' b, a)] s') t' π π' h]

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
      simp [ntm.permute, alphaEquiv]

  theorem alphaEquivList_permute_right_ds_empty (Γ : Context 𝔸 X) (ss ts : List (ntm F X 𝔸))
      (π π' : LPerm 𝔸) (h : ds π π' = ∅) :
      alphaEquivList Γ ss (ts.map (ntm.permute π)) =
        alphaEquivList Γ ss (ts.map (ntm.permute π')) := by
    match ss, ts with
    | [], [] => simp [alphaEquivList]
    | [], _ :: _ => simp [alphaEquivList]
    | _ :: _, [] => simp [alphaEquivList]
    | s :: ss', t :: ts' =>
      simp only [List.map_cons, alphaEquivList]
      rw [alphaEquiv_permute_right_ds_empty Γ s t π π' h,
          alphaEquivList_permute_right_ds_empty Γ ss' ts' π π' h]
end

mutual
  lemma alphaEquivPermInver (Γ : Context 𝔸 X) (s t : ntm F X 𝔸) (π : LPerm 𝔸) :
      (Γ ⊢ (s.permute π) ≈α t) = (Γ ⊢ s ≈α (t.permute π.reverse)) := by

    match s, t with
    | ntm.atm a, ntm.atm b =>
      simp only [ntm.permute, alphaEquiv, decide_eq_decide]
      constructor
      · intro h; rw [← h, LPermApply_reverse_left]
      · intro h; rw [h, LPermApply_reverse_right]

    | ntm.mvar σ x, ntm.mvar σ' y =>
      simp only [ntm.permute, alphaEquiv, Bool.decide_and]
      congr 1
      rw [ds_perm_swap]

    | ntm.fapp f ss, ntm.fapp g ts =>
      simp only [ntm.permute, alphaEquiv]
      rw [alphaEquivListPermInver Γ ss ts π]

    | ntm.abs a s', ntm.abs b t' =>
      simp only [ntm.permute, alphaEquiv]
      have hcond : (LPermApply π a = b) ↔ (a = LPermApply π.reverse b) := by
        constructor
        · intro h; rw [← h, LPermApply_reverse_left]
        · intro h; rw [h, LPermApply_reverse_right]
      by_cases hcase : LPermApply π a = b
      · have hcase' : a = LPermApply π.reverse b := hcond.mp hcase
        rw [if_pos hcase, if_pos hcase']
        exact alphaEquivPermInver Γ s' t' π
      · have hcase' : a ≠ LPermApply π.reverse b := fun h => hcase (hcond.mpr h)
        rw [if_neg hcase, if_neg hcase']
        rw [ntm.permute_append]
        rw [alphaEquivPermInver Γ s' t' (π ++ [(b, LPermApply π a)])]
        simp only [List.reverse_append, List.reverse_singleton]
        rw [alphaEquivPermInver Γ s' (ntm.permute π.reverse t') [(LPermApply π.reverse b, a)]]
        simp only [List.reverse_singleton, ntm.permute_append]
        have hds :
            ds ([(b, LPermApply π a)] ++ π.reverse)
               (π.reverse ++ [(LPermApply π.reverse b, a)]) = ∅ := by
          have := ds_swap_conjugate π.reverse (LPermApply π a) b
          simp only [LPermApply_reverse_left] at this
          exact this
        rw [alphaEquiv_permute_right_ds_empty Γ s' t' _ _ hds]
        simp only [Bool.decide_and]
        rw [fresh_equivariance Γ (LPermApply π.reverse b) s' π]
        simp only [LPermApply_reverse_right]

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
      simp [ntm.permute, alphaEquiv]

  lemma alphaEquivListPermInver (Γ : Context 𝔸 X) (ss ts : List (ntm F X 𝔸)) (π : LPerm 𝔸) :
      alphaEquivList Γ (ss.map (ntm.permute π)) ts =
        alphaEquivList Γ ss (ts.map (ntm.permute π.reverse)) := by
    match ss, ts with
    | [], [] => simp [alphaEquivList]
    | [], _ :: _ => simp [alphaEquivList]
    | _ :: _, [] => simp [alphaEquivList]
    | s :: ss', t :: ts' =>
      simp only [List.map_cons, alphaEquivList]
      rw [alphaEquivPermInver Γ s t π, alphaEquivListPermInver Γ ss' ts' π]
end

/-- α-equivalence is equivariant: permuting both the atom and the term preserves α-equivalence. -/
theorem alphaEquiv_equivariance (Γ : Context 𝔸 X) (s t : ntm F X 𝔸) (π : LPerm 𝔸) :
    (Γ ⊢ s ≈α t) = (Γ ⊢ s.permute π ≈α t.permute π) := by
  rw [alphaEquivPermInver]
  rw [ntm.permute_append]
  have hds : ds (π ++ π.reverse) [] = ∅ := by simp [ds_reverse_nil]
  simp [alphaEquiv_permute_right_ds_empty Γ s t (π ++ List.reverse π) [] hds]
  simp [ntm.permute_nil]

mutual
  theorem alphaEquiv_invariance_mp (Γ : Context 𝔸 X) (t : ntm F X 𝔸) (π π' : LPerm 𝔸) :
      (∀ a ∈ ds π π', (Γ ⊢ a # t) = true) ->
        (Γ ⊢ ntm.permute π t ≈α ntm.permute π' t) = true := by
    match t with
    | ntm.atm b =>
      simp [fresh, alphaEquiv, ntm.permute]
      intro h
      exact (Lperm_not_in_ds b π π').mpr h

    | ntm.mvar σ x =>
      simp [fresh, alphaEquiv, ntm.permute]
      intro h
      intro n hn
      have hne : LPermApply π (LPermApply σ n) ≠ LPermApply π' (LPermApply σ n) := by
        simp only [ds, Finset.mem_filter, LPermApply_append] at hn
        exact hn.2
      have hσn_ds : LPermApply σ n ∈ ds π π' := by
        simp only [ds, Finset.mem_filter, Finset.mem_union]
        exact ⟨by_contra fun h => hne (by push_neg at h; rw [LPermApply_not_mem_atoms _ _ h.1, LPermApply_not_mem_atoms _ _ h.2]), hne⟩
      have := h _ hσn_ds
      rwa [LPermApply_reverse_left] at this

    | ntm.fapp f ts =>
      simp [fresh, alphaEquiv, ntm.permute]
      intro h
      exact alphaEquivList_invariance_mp Γ ts π π' h

    | ntm.abs b t =>
      simp [fresh, alphaEquiv, ntm.permute]
      intro h
      split_ifs with heq
      · have hb_not_ds : b ∉ ds π π' := by
          exact (Lperm_not_in_ds b π π').mp heq
        exact alphaEquiv_invariance_mp Γ t π π' (fun a ha => by
            rcases h a ha with rfl | hfresh
            · exact absurd ha hb_not_ds
            · exact hfresh)
      · constructor
        · rw [ntm.permute_append]
          apply alphaEquiv_invariance_mp Γ t (π ++ [(LPermApply π' b, LPermApply π b)]) π'
          intro a ha
          by_cases hab : a = b
          · subst hab
            exfalso
            have : LPermApply (π ++ [(LPermApply π' a, LPermApply π a)]) a = LPermApply π' a := by
              simp [LPermApply_append, swapApply_right]
            exact absurd ha ((Lperm_not_in_ds a _ π').mp this)
          · have hads : a ∈ ds π π' := ds_append_swap_sub π π' b a hab ha
            exact (h a hads).resolve_left hab
        · rw [fresh_equivariance Γ (LPermApply π' b) (ntm.permute π t) π.reverse]
          simp [ntm.permute_append]
          have hnil : ds (π ++ π.reverse) [] = ∅ := by
            simp [ds_reverse_nil]
          rw [fresh_permute_ds_empty Γ (LPermApply (List.reverse π) (LPermApply π' b)) t (π ++ π.reverse) [] hnil]
          simp [ntm.permute_nil]
          set c := LPermApply π.reverse (LPermApply π' b)
          have hcb : c ≠ b := by
            intro heq'
            apply heq
            have := congrArg (LPermApply π) heq'
            rw [← this]
            simp [c]
            simp [LPermApply_reverse_right]
          have hc_ds : c ∈ ds π π' := by
            by_contra h_not
            have heq1 : LPermApply π c = LPermApply π' b := by simp [c, LPermApply_reverse_right]
            have heq2 : LPermApply π c = LPermApply π' c := (Lperm_not_in_ds c π π').mpr h_not
            exact hcb (LPermApply_injective π' (heq1 ▸ heq2).symm)
          rcases h c hc_ds with hceqb | hfresh
          · exact absurd hceqb hcb
          · exact hfresh

  theorem alphaEquivList_invariance_mp (Γ : Context 𝔸 X) (ts : List (ntm F X 𝔸)) (π π' : LPerm 𝔸) :
      (∀ a ∈ ds π π', freshList Γ a ts = true) ->
        alphaEquivList Γ (ts.map (ntm.permute π)) (ts.map (ntm.permute π')) = true := by
    match ts with
    | [] => simp [alphaEquivList]
    | t :: ts' =>
      intro h
      simp [freshList] at h
      simp [alphaEquivList]
      have h1 : ∀ a ∈ ds π π', (Γ ⊢ a # t) = true := fun a ha => (h a ha).1
      have h2 : ∀ a ∈ ds π π', freshList Γ a ts' = true := fun a ha => (h a ha).2
      exact ⟨alphaEquiv_invariance_mp Γ t π π' h1, alphaEquivList_invariance_mp Γ ts' π π' h2⟩

end

mutual
  theorem alphaEquiv_invariance_mpr (Γ : Context 𝔸 X) (t : ntm F X 𝔸) (π π' : LPerm 𝔸) :
       (Γ ⊢ ntm.permute π t ≈α ntm.permute π' t) = true ->
        (∀ a ∈ ds π π', (Γ ⊢ a # t) = true) := by
    match t with
    | ntm.atm b =>
      simp [fresh, alphaEquiv, ntm.permute]
      intro h
      exact (Lperm_not_in_ds b π π').mp h

    | ntm.mvar σ x =>
      simp [fresh, alphaEquiv, ntm.permute]
      intro h
      intro a ha
      have hne : LPermApply π a ≠ LPermApply π' a := by
        simp only [ds, Finset.mem_filter] at ha; exact ha.2
      apply h
      simp only [ds, Finset.mem_filter, Finset.mem_union, LPermAtoms_append, LPermApply_append, ne_eq]
      refine ⟨?_, by rw [LPermApply_reverse_right]; exact hne⟩
      by_contra hnot
      push_neg at hnot
      have hσ_fix := LPermApply_not_mem_atoms σ _ hnot.1.1
      have hπ_fix := LPermApply_not_mem_atoms π _ hnot.1.2
      have hπ'_fix := LPermApply_not_mem_atoms π' _ hnot.2.2
      have hrev : LPermApply σ.reverse a = a := by
        have := LPermApply_reverse_right σ a; rw [hσ_fix] at this; exact this
      rw [hrev] at hπ_fix hπ'_fix
      exact hne (hπ_fix.trans hπ'_fix.symm)

    | ntm.fapp f ts =>
      simp [fresh, alphaEquiv, ntm.permute]
      intro h
      exact alphaEquivList_invariance_mpr Γ ts π π' h

    | ntm.abs b t =>
      simp [fresh, alphaEquiv, ntm.permute]
      intro h
      by_cases hcase : LPermApply π b = LPermApply π' b
      · simp [hcase] at h
        intro a
        by_cases hab : a = b
        · subst hab
          simp
        · simp [hab]
          intro hads
          exact alphaEquiv_invariance_mpr Γ t π π' h a hads
      · simp [hcase] at h
        intro a
        by_cases hab : a = b
        · subst hab
          simp
        · simp [hab]
          intro hads
          by_cases hpa : LPermApply π a = LPermApply π' b
          · have key : LPermApply π.reverse (LPermApply π' b) = a := by
              rw [← hpa, LPermApply_reverse_left]
            rw [← key, fresh_equivariance Γ _ t π, LPermApply_reverse_right]
            exact h.2
          · have hpb : LPermApply π a ≠ LPermApply π b := by
              intro h; exact hab (LPermApply_injective π h)
            have h1 := h.1
            rw [ntm.permute_append] at h1
            have hmpr := alphaEquiv_invariance_mpr Γ t (π ++ [(LPermApply π' b, LPermApply π b)]) π' h1
            apply hmpr
            simp only [ds, Finset.mem_filter, Finset.mem_union, LPermAtoms_append,
                     LPermApply_append, ne_eq]
            constructor
            · by_contra hnot
              push_neg at hnot
              have hne := (Finset.mem_filter.mp (show a ∈ _ from hads)).2
              exact hne (by
                rw [LPermApply_not_mem_atoms _ _ hnot.1.1,
                    LPermApply_not_mem_atoms _ _ hnot.2])
            · simp only [LPermApply_cons, LPermApply_nil]
              rw [swapApply_other _ _ _ hpa hpb]
              exact (Finset.mem_filter.mp (show a ∈ _ from hads)).2

  theorem alphaEquivList_invariance_mpr (Γ : Context 𝔸 X) (ts : List (ntm F X 𝔸)) (π π' : LPerm 𝔸) :
      alphaEquivList Γ (ts.map (ntm.permute π)) (ts.map (ntm.permute π')) = true ->
      (∀ a ∈ ds π π', freshList Γ a ts = true) := by
    match ts with
    | [] => simp [freshList]
    | t :: ts' =>
      intro h
      simp [freshList]
      simp [alphaEquivList] at h
      obtain ⟨h, hlist⟩ := h
      simp only [imp_and, forall_and]
      constructor
      · exact alphaEquiv_invariance_mpr Γ t π π' h
      · exact alphaEquivList_invariance_mpr Γ ts' π π' hlist
end

/-- (Invariance of ≈α under the action of permutations), full iff statement. -/
theorem alphaEquiv_invariance (Γ : Context 𝔸 X) (s : ntm F X 𝔸) (π π' : LPerm 𝔸) :
    (∀ a ∈ ds π π', (Γ ⊢ a # s) = true) ↔
      (Γ ⊢ ntm.permute π s ≈α ntm.permute π' s) = true := by
  constructor
  · exact alphaEquiv_invariance_mp Γ s π π'
  · exact alphaEquiv_invariance_mpr Γ s π π'

end Nominal
