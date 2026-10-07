import Nominal.Syntax.AlphaEquiv.Basic

namespace Nominal

open Core

variable {F X 𝔸 : Type*} [DecidableEq F] [DecidableEq X] [Name 𝔸]

mutual
  lemma ntm.permute_swap_symm_alphaEquiv (Γ : Context 𝔸 X) (a b : 𝔸) (s : ntm F X 𝔸) :
      Γ ⊢ (permute [(a,b)] s) ≈α (permute [(b,a)] s) := by
    match s with
    | atm c => simp [alphaEquiv, permute, swapApply_symm]
    | mvar π x =>
      simp only [permute, alphaEquiv, ds, ne_eq, LPerm.atoms_append, LPerm.atoms, Finset.union_empty,
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
        · rw [Finset.mem_union, not_or] at hmem
          rw [LPermApply_not_mem_atoms π c' hmem.1, LPermApply_not_mem_atoms π' c' hmem.2]
      have hc'c : c' = c := by
        have h1 : LPermApply π' c' = a := by
          show LPermApply π' (LPermApply π'.reverse a) = a
          exact LPermApply_reverse_right π' a
        have h2 : LPermApply π c' = a := hnotds.trans h1
        have := congrArg (LPermApply π.reverse) h2
        rw [LPermApply_reverse_left] at this
        exact this
      rw [hc'c]; exact hf

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

end Nominal
