import Nominal.Syntax.Terms
import Nominal.Syntax.Ds
import Nominal.Syntax.Fresh

namespace Nominal

open Core

variable {F X 𝔸 : Type*} [DecidableEq F] [DecidableEq X] [Name 𝔸]

mutual
  def alphaEquiv
    (Γ : Context 𝔸 X) : ntm F X 𝔸 → ntm F X 𝔸 → Bool
    -- (≈αa)
    | ntm.atm a, ntm.atm b => a = b
    -- (≈αX)
    | ntm.mvar π x, ntm.mvar π' y => x = y ∧ (∀ n ∈ ds π π', (n, x) ∈ Γ)
    -- (≈αtup)/(≈αf)
    | ntm.fapp f ss, ntm.fapp g ts => f = g ∧ alphaEquivList Γ ss ts
    -- (≈αabsa)/(≈αabsb)
    | ntm.abs a s, ntm.abs b t =>
        if a = b then alphaEquiv Γ s t
        else alphaEquiv Γ (ntm.permute [(b, a)] s) t ∧ fresh Γ b s
    | _, _ => false

  def alphaEquivList
    (Γ : Context 𝔸 X) : List (ntm F X 𝔸) → List (ntm F X 𝔸) → Bool
    | [], [] => true
    | s :: ss, t :: ts => alphaEquiv Γ s t ∧ alphaEquivList Γ ss ts
    | _,  _  => false
end

/-- Alpha-equivalence judgment: `Γ ⊢ s ≈α t` means `s` and `t` are alpha-equivalent under context `Γ`. -/
notation Γ " ⊢ " s " ≈α " t => alphaEquiv Γ s t

mutual
  lemma ntm.permute_swap_symm_alphaEquiv (Γ : Context 𝔸 X) (a b : 𝔸) (s : ntm F X 𝔸) :
      Γ ⊢ (permute [(a,b)] s) ≈α (permute [(b,a)] s) := by
    match s with
    | atm c => simp [alphaEquiv, permute, swapApply_symm]
    | mvar π x =>
      simp only [permute, alphaEquiv, ds, ne_eq, LPermAtoms_append, LPerm.atoms, Finset.union_empty,
        Finset.union_insert, Finset.union_singleton, Finset.insert_union, Finset.union_idempotent,
        Finset.mem_insert, true_or, Finset.insert_eq_of_mem, or_true, Finset.mem_filter, and_imp,
        forall_eq_or_imp, true_and, Bool.decide_and, decide_implies, dite_eq_ite, ite_not,
        Bool.if_true_left, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]
      constructor
      · left
        rw [LPermApply_append, LPermApply_append]
        simp only [LPermApply_cons, LPermApply_nil]
        simp [swapApply_symm]
      · constructor
        · left
          rw [LPermApply_append, LPermApply_append]
          simp only [LPermApply_cons, LPermApply_nil]
          simp [swapApply_symm]
        · intro n hn h
          rw [LPermApply_append, LPermApply_append] at h
          exfalso
          apply h
          simp only [LPermApply_cons, LPermApply_nil]
          simp [swapApply_symm]
    | fapp f ss =>
      simp only [ntm.permute, alphaEquiv, decide_eq_true_eq, true_and]
      exact ntm.permute_swap_symm_alphaEquivList Γ a b ss
    | abs c t =>
      simp only [permute, LPermApply_cons, LPermApply_nil, swapApply_symm, alphaEquiv, ↓reduceIte]
      exact permute_swap_symm_alphaEquiv Γ a b t

  lemma ntm.permute_swap_symm_alphaEquivList (Γ : Context 𝔸 X) (a b : 𝔸)
      (ss : List (ntm F X 𝔸)) :
      alphaEquivList Γ (ss.map (ntm.permute [(a, b)])) (ss.map (ntm.permute [(b, a)])) = true := by
    match ss with
    | [] => simp [alphaEquivList]
    | t :: tl =>
      simp only [List.map_cons, alphaEquivList, Bool.decide_and, Bool.decide_eq_true,
        Bool.and_eq_true]
      exact ⟨ntm.permute_swap_symm_alphaEquiv Γ a b t,
             ntm.permute_swap_symm_alphaEquivList Γ a b tl⟩
end

-- (Freshness preservation under ≈α).
mutual
  lemma freshPreserves_alphaEquiv (Γ : Context 𝔸 X) (a : 𝔸) (s t : ntm F X 𝔸)
    (hf : fresh Γ a s = true) (ha : alphaEquiv Γ s t = true) : fresh Γ a t = true := by

  match s, t with
  | ntm.atm b, ntm.atm c =>
    simp only [fresh, ne_eq, decide_not, Bool.not_eq_eq_eq_not, Bool.not_true,
      decide_eq_false_iff_not, alphaEquiv, decide_eq_true_eq] at *
    rw [<- ha]
    exact hf

  | ntm.mvar π x, ntm.mvar π' y =>
    simp only [fresh, decide_eq_true_eq, alphaEquiv, Bool.decide_and, Bool.and_eq_true] at *
    obtain ⟨hxy, hds⟩ := ha
    rw [<- hxy]
    set c := LPermApply (List.reverse π) a
    set c' := LPermApply (List.reverse π') a
    by_cases hcases : c' ∈ ds π π'
    · exact hds c' hcases
    · have hnotds : LPermApply π c' = LPermApply π' c' := by
        simp only [ds, Finset.mem_filter, not_and] at hcases
        by_cases hmem : c' ∈ LPerm.atoms π ∪ LPerm.atoms π'
        · push_neg at hcases
          exact hcases hmem
        · simp only [Finset.mem_union] at hmem
          push_neg at hmem
          push_neg at hcases
          rw [LPermApply_not_mem_atoms π c' hmem.1, LPermApply_not_mem_atoms π' c' hmem.2]
      have hpi'c' : LPermApply π' c' = a := by
        simp [c', LPermApply_reverse_right]
      have hcc' : c' = c := by
        apply LPermApply_injective π
        rw [hnotds, hpi'c', LPermApply_reverse_right]
      rw [hcc']
      exact hf

  | ntm.fapp f ss, ntm.fapp g ts =>
    simp only [fresh, alphaEquiv, Bool.decide_and, Bool.decide_eq_true, Bool.and_eq_true,
      decide_eq_true_eq] at *
    rcases ha with ⟨hfg, ha⟩
    exact freshListPreserves_alphaEquiv Γ a ss ts hf ha

  | ntm.abs b s', ntm.abs c t' =>
    by_cases hbc : b = c
    · subst hbc
      simp only [fresh, Bool.decide_or, Bool.decide_eq_true, Bool.or_eq_true, decide_eq_true_eq,
        alphaEquiv, ↓reduceIte] at *
      rcases hf with h | h
      · left; exact h
      · right; exact freshPreserves_alphaEquiv Γ a s' t' h ha
    · simp only [fresh, Bool.decide_or, Bool.decide_eq_true, Bool.or_eq_true,
      decide_eq_true_eq] at hf ⊢
      simp only [alphaEquiv, hbc, ↓reduceIte, Bool.decide_and, Bool.decide_eq_true,
        Bool.and_eq_true] at ha
      obtain ⟨haα, hcs⟩ := ha
      by_cases hac : a = c
      · left; exact hac
      · right
        have hkey : fresh Γ a (ntm.permute [(c, b)] s') = true := by
          by_cases hab : a = b
          · have heq := fresh_equivariance Γ c s' [(c, b)]
            simp only [LPermApply_cons, swapApply_left, LPermApply_nil] at heq
            rw [hab, ← heq]; exact hcs
          · have hfs : fresh Γ a s' = true := by
              rcases hf with h | h
              · exact absurd h hab
              · exact h
            have heq := fresh_equivariance Γ a s' [(c, b)]
            simp only [LPermApply_cons, swapApply_other c b a hac hab, LPermApply_nil] at heq
            rw [← heq]; exact hfs
        exact freshPreserves_alphaEquiv Γ a (ntm.permute [(c, b)] s') t' hkey haα

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
    simp [alphaEquiv] at ha

  lemma freshListPreserves_alphaEquiv (Γ : Context 𝔸 X) (a : 𝔸) (ss ts : List (ntm F X 𝔸))
    (hf : freshList Γ a ss = true) (ha : alphaEquivList Γ ss ts = true) :
      freshList Γ a ts = true := by
    match ss, ts with
    | [], [] => simp [freshList]
    | [], _ :: _ =>
      simp only [alphaEquivList] at ha
      contradiction
    | _ :: _, [] =>
      simp only [alphaEquivList] at ha
      contradiction
    | s :: ss', t :: ts' =>
      simp only [freshList, Bool.decide_and, Bool.decide_eq_true, Bool.and_eq_true,
        alphaEquivList] at *
      obtain ⟨hfs, hfss⟩ := hf
      obtain ⟨hat, hats⟩ := ha
      exact ⟨freshPreserves_alphaEquiv Γ a s t hfs hat,
             freshListPreserves_alphaEquiv Γ a ss' ts' hfss hats⟩
end

mutual
  /-- Swap-conjugation up to α-equivalence: prepending swap `(b, a)` to `π` produces an
      α-equivalent term to appending the swap of the permuted atoms. -/
  lemma ntm.permute_cons_alphaEquiv (Γ : Context 𝔸 X) (a b : 𝔸) (π : LPerm 𝔸)
      (t : ntm F X 𝔸) :
      (Γ ⊢ ntm.permute ((b, a) :: π) t
          ≈α ntm.permute (π ++ ([(LPermApply π b, LPermApply π a)] : LPerm 𝔸)) t) = true := by
    match t with
    | .atm c =>
      simp only [permute, LPermApply_cons, LPermApply_append, LPermApply_nil, alphaEquiv,
        decide_eq_true_eq]
      by_cases hcb : c = b
      · subst hcb
        rw [swapApply_left, swapApply_left]
      · by_cases hca : c = a
        · subst hca
          rw [swapApply_right, swapApply_right]
        · rw [swapApply_other _ _ _ hcb hca]
          have hπcb : LPermApply π c ≠ LPermApply π b :=
            fun heq => hcb (LPermApply_injective π heq)
          have hπca : LPermApply π c ≠ LPermApply π a :=
            fun heq => hca (LPermApply_injective π heq)
          rw [swapApply_other _ _ _ hπcb hπca]
    | .mvar σ x =>
      simp only [permute, alphaEquiv, true_and, decide_eq_true_eq]
      intro n hn
      exfalso
      simp only [ds, Finset.mem_filter, LPermApply_append] at hn
      apply hn.2
      rw [LPermApply_cons]
      simp only [LPermApply_cons, LPermApply_nil]
      exact (LPermApply_swap_conjugate π a b (LPermApply σ n))

    | .fapp f ts =>
      simp only [ntm.permute, alphaEquiv, decide_eq_true_eq, true_and]
      exact ntm.permute_cons_alphaEquivList Γ a b π ts

    | .abs c t' =>
      simp only [permute, LPermApply_cons, alphaEquiv, Bool.decide_and, Bool.decide_eq_true,
        Bool.ite_eq_true_distrib, Bool.and_eq_true]
      split_ifs with heq
      · exact ntm.permute_cons_alphaEquiv Γ a b π t'
      · exfalso
        apply heq
        rw [LPermApply_append, LPermApply_cons, LPermApply_nil]
        exact LPermApply_swap_conjugate π a b c

  /-- List version of `ntm.permute_cons_alphaEquiv`. -/
  lemma ntm.permute_cons_alphaEquivList (Γ : Context 𝔸 X) (a b : 𝔸) (π : LPerm 𝔸)
      (ts : List (ntm F X 𝔸)) :
      alphaEquivList Γ (ts.map (ntm.permute ((b, a) :: π)))
        (ts.map (ntm.permute (π ++ ([(LPermApply π b, LPermApply π a)] : LPerm 𝔸)))) = true := by
    match ts with
    | [] => simp [alphaEquivList]
    | t :: tl =>
      simp only [List.map_cons, alphaEquivList]
      simp only [Bool.decide_and, Bool.decide_eq_true, Bool.and_eq_true]
      exact ⟨ntm.permute_cons_alphaEquiv Γ a b π t,
             ntm.permute_cons_alphaEquivList Γ a b π tl⟩
end

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

-- (Inversion of permutations over ≈α ).
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
    match t₁, t₂, t₃ with
    | ntm.atm a, ntm.atm b, ntm.atm c =>
      simp [alphaEquiv] at *
      subst h₁
      trivial
    | ntm.mvar π₁ x, ntm.mvar π₂ y, ntm.mvar π₃ z =>
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
    | ntm.fapp f ts₁, ntm.fapp g ts₂, ntm.fapp h ts₃ =>
      simp only [alphaEquiv, decide_eq_true_eq] at *
      obtain ⟨hfg, hl12⟩ := h₁
      obtain ⟨hgh, hl23⟩ := h₂
      subst hfg; subst hgh
      exact ⟨rfl, alphaEquivList_trans Γ ts₁ ts₂ ts₃ hl12 hl23⟩

    -- TODO: finish transitivy proving abstraction
    | ntm.abs a t₁, ntm.abs b t₂, ntm.abs c t₃ =>
      simp [alphaEquiv] at *
      sorry

    -- TODO: finish remaining cases for transitivity
    | _, _, _ => sorry
  
  -- TODO: prove transitivity for lists 
  theorem alphaEquivList_trans (Γ : Context 𝔸 X) (ts₁ ts₂ ts₃ : List (ntm F X 𝔸))
      (h₁ : (alphaEquivList Γ ts₁ ts₂) = true) (h₂ : (alphaEquivList Γ ts₂ ts₃) = true) :
      (alphaEquivList Γ ts₁ ts₃) = true := by
    sorry
end

end Nominal
