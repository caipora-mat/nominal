import Nominal.Syntax.Unification.Algorithm.Measure
import Mathlib.Data.Multiset.DershowitzManna
import Mathlib.Tactic.Abel

namespace Nominal

open Core

variable {F X 𝔸 : Type*} [DecidableEq F] [DecidableEq X] [Name 𝔸]

-- ============================================================
-- Helpers for the termination proof.
-- ============================================================

-- The foldl defining unifVars is monotone in its accumulator:
-- if acc ⊆ acc' then foldl_unifVars acc Pr ⊆ foldl_unifVars acc' Pr.
lemma unifVars_foldl_mono (Pr : UnifProblem F X 𝔸) {acc acc' : Finset X}
    (h : acc ⊆ acc') :
    Pr.foldl (fun a c => match c with
      | .fresh _ _ => a
      | .unif s t  => a ∪ s.metavars ∪ t.metavars) acc ⊆
    Pr.foldl (fun a c => match c with
      | .fresh _ _ => a
      | .unif s t  => a ∪ s.metavars ∪ t.metavars) acc' := by
  induction Pr generalizing acc acc' with
  | nil => simpa
  | cons c rest ih =>
    simp only [List.foldl_cons]
    apply ih
    cases c with
    | fresh _ _ => exact h
    | unif s t =>
      intro x hx
      simp only [Finset.mem_union] at *
      exact hx.imp_left (·.imp_left (h ·))

/-- Adding any constraint to a problem can only enlarge its unifVars. -/
lemma UnifProblem.unifVars_subset_cons (c : UnifConstraint F X 𝔸) (Pr : UnifProblem F X 𝔸) :
    UnifProblem.unifVars Pr ⊆ UnifProblem.unifVars (c :: Pr) := by
  simp only [UnifProblem.unifVars, List.foldl_cons]
  apply unifVars_foldl_mono
  cases c with
  | fresh _ _ => exact Finset.Subset.refl ∅
  | unif _ _  => exact Finset.empty_subset _

/-- Prepending any constraint adds exactly one element to unifDepthMs. -/
lemma UnifProblem.unifDepthMs_cons (c : UnifConstraint F X 𝔸) (Pr : UnifProblem F X 𝔸) :
    UnifProblem.unifDepthMs (c :: Pr) =
      {(match c with | .fresh _ t => t.depth + 1 | .unif s t => max s.depth t.depth + 2)} +
      UnifProblem.unifDepthMs Pr := by
  show ((List.map _ (c :: Pr) : List ℕ) : Multiset ℕ) = _
  rw [List.map_cons]
  rfl

lemma UnifProblem.unifDepthMs_append (Pr Pr' : UnifProblem F X 𝔸) :
    (Pr ++ Pr').unifDepthMs = Pr.unifDepthMs + Pr'.unifDepthMs := by
  simp [UnifProblem.unifDepthMs, List.map_append, ← Multiset.coe_add]

-- foldl over an all-fresh problem leaves the accumulator unchanged.
lemma unifVars_foldl_fresh_stable (Pr : UnifProblem F X 𝔸) (acc : Finset X)
    (hall : ∀ c ∈ Pr, ∃ a t, c = UnifConstraint.fresh a t) :
    Pr.foldl (fun a c => match c with
      | .fresh _ _ => a
      | .unif s t  => a ∪ s.metavars ∪ t.metavars) acc = acc := by
  induction Pr with
  | nil => rfl
  | cons c rest ih =>
    simp only [List.foldl_cons]
    obtain ⟨a', t', rfl⟩ := hall c List.mem_cons_self
    exact ih (fun c' hc' => hall c' (List.mem_cons_of_mem _ hc'))


mutual
   lemma ntm.metavars_applyOne_le (t : ntm F X 𝔸) (x : X) (s : ntm F X 𝔸)
       (hs : s.metavars = ∅) :
       (t.applyOne x s).metavars ⊆ t.metavars := by
     match t with
     | .atm _ => simp [ntm.applyOne, ntm.metavars]
     | .mvar π y =>
       simp only [ntm.applyOne]
       split_ifs with hyx
       · simp [ntm.permute_metavars, hs]
       · rfl
     | .fapp _ ts =>
       simp only [ntm.applyOne, ntm.metavars]
       exact ntmList.metavars_applyOne_le ts x s hs
     | .abs _ t' =>
       simp only [ntm.applyOne, ntm.metavars]
       exact ntm.metavars_applyOne_le t' x s hs

   lemma ntmList.metavars_applyOne_le (ts : List (ntm F X 𝔸)) (x : X) (s : ntm F X 𝔸)
       (hs : s.metavars = ∅) :
       ntmList.metavars (ts.map (·.applyOne x s)) ⊆ ntmList.metavars ts := by
     match ts with
     | [] => simp [ntmList.metavars]
     | t :: ts' =>
       simp only [List.map_cons, ntmList.metavars]
       exact Finset.union_subset_union
         (ntm.metavars_applyOne_le t x s hs)
         (ntmList.metavars_applyOne_le ts' x s hs)
 end

-- Every constraint produced by simplifyFresh is a `.fresh` with depth ≤ the original term's depth.
mutual
  lemma simplifyFresh_constraints_le (a : 𝔸) (t : ntm F X 𝔸) {cs : Problem F X 𝔸}
      (h : simplifyFresh a t = some cs) :
      ∀ c ∈ cs, ∃ a' u, c = Constraint.fresh a' u ∧ u.depth + 1 ≤ t.depth + 1 := by
    match t with
    | .atm b =>
      simp [simplifyFresh] at h
      simp [h]
    | .mvar π x =>
      simp [simplifyFresh] at h; subst h
      intro c hc; simp at hc; subst hc
      exact ⟨_, _, rfl, by simp [ntm.depth]⟩
    | .abs b t' =>
      simp only [simplifyFresh] at h
      split_ifs at h with hab
      · simp at h; subst h; intro c hc; simp at hc
      · intro c hc
        obtain ⟨a', u, rfl, hle⟩ := simplifyFresh_constraints_le a t' h c hc
        exact ⟨a', u, rfl, by simp only [ntm.depth]; omega⟩
    | .fapp _ ts =>
      simp only [simplifyFresh] at h
      intro c hc
      obtain ⟨a', u, rfl, hle⟩ := simplifyFreshList_constraints_le a ts h c hc
      exact ⟨a', u, rfl, by simp only [ntm.depth]; omega⟩

  lemma simplifyFreshList_constraints_le (a : 𝔸) (ts : List (ntm F X 𝔸)) {cs : Problem F X 𝔸}
      (h : simplifyFreshList a ts = some cs) :
      ∀ c ∈ cs, ∃ a' u, c = Constraint.fresh a' u ∧ u.depth + 1 ≤ ntmList.maxDepth ts + 1 := by
    match ts with
    | [] =>
      simp [simplifyFreshList] at h; subst h
      intro c hc; simp at hc
    | t :: ts' =>
      simp only [simplifyFreshList] at h
      rcases h1 : simplifyFresh a t with _ | cs₁
      · rw [h1] at h; simp at h
      · rcases h2 : simplifyFreshList a ts' with _ | cs₂
        · rw [h1, h2] at h; simp at h
        · rw [h1, h2] at h; simp at h; subst h
          intro c hc
          rw [List.mem_append] at hc
          cases hc with
          | inl hc₁ =>
            obtain ⟨a', u, rfl, hle⟩ := simplifyFresh_constraints_le a t h1 c hc₁
            exact ⟨a', u, rfl, by
              simp only [ntmList.maxDepth]
              have := Nat.le_max_left t.depth (ntmList.maxDepth ts')
              omega⟩
          | inr hc₂ =>
            obtain ⟨a', u, rfl, hle⟩ := simplifyFreshList_constraints_le a ts' h2 c hc₂
            exact ⟨a', u, rfl, by
              simp only [ntmList.maxDepth]
              have := Nat.le_max_right t.depth (ntmList.maxDepth ts')
              omega⟩
end

lemma unifVars_foldl_applySubst_le
      (Pr : UnifProblem F X 𝔸) (x : X) (s : ntm F X 𝔸)
      (hs : s.metavars = ∅) (acc : Finset X) :
      (Pr.applySubst [(x, s)]).foldl (fun a c => match c with
          | .fresh _ _ => a | .unif u v => a ∪ u.metavars ∪ v.metavars) acc ⊆
      Pr.foldl (fun a c => match c with
          | .fresh _ _ => a | .unif u v => a ∪ u.metavars ∪ v.metavars) acc := by
    induction Pr generalizing acc with
    | nil => simp [UnifProblem.applySubst]
    | cons c rest ih =>
      simp only [UnifProblem.applySubst, List.map_cons, List.foldl_cons]
      -- step 1: IH at acc' = f acc (c.applySubst)
      -- step 2: mono from (f acc c.applySubst) ⊆ (f acc c)
      apply Finset.Subset.trans (ih _)
      apply unifVars_foldl_mono
      cases c with
      | fresh _ _ => simp [UnifConstraint.applySubst]
      | unif u v =>
        simp only [UnifConstraint.applySubst, ntm.subst_cons, ntm.subst_nil]
        apply Finset.union_subset_union
        · apply Finset.union_subset_union
          · rfl
          exact ntm.metavars_applyOne_le u x s hs
        · exact ntm.metavars_applyOne_le v x s hs

lemma UnifProblem.unifVars_applySubst_le
    (Pr : UnifProblem F X 𝔸) (x : X) (s : ntm F X 𝔸)
    (hs : s.metavars = ∅) :
    (Pr.applySubst [(x, s)]).unifVars ⊆ Pr.unifVars :=
  unifVars_foldl_applySubst_le Pr x s hs ∅

mutual
  lemma ntm.depth_applyOne_depth0 (t : ntm F X 𝔸) (x : X) (s : ntm F X 𝔸)
      (hs : s.depth = 0) : (t.applyOne x s).depth = t.depth := by
    match t with
    | .atm _ => simp [ntm.applyOne, ntm.depth]
    | .mvar π y =>
      simp only [ntm.applyOne]
      split_ifs with hyx
      · simp [ntm.permute_depth, ntm.depth, hs]
      · rfl
    | .fapp _ ts =>
      simp only [ntm.applyOne, ntm.depth]
      congr 1; exact ntmList.maxDepth_applyOne_depth0 ts x s hs
    | .abs _ t' =>
      simp only [ntm.applyOne, ntm.depth]
      congr 1; exact ntm.depth_applyOne_depth0 t' x s hs

  lemma ntmList.maxDepth_applyOne_depth0 (ts : List (ntm F X 𝔸)) (x : X) (s : ntm F X 𝔸)
      (hs : s.depth = 0) : ntmList.maxDepth (ts.map (·.applyOne x s)) = ntmList.maxDepth ts := by
    match ts with
    | [] => simp [ntmList.maxDepth]
    | t :: ts' =>
      simp only [List.map_cons, ntmList.maxDepth]
      rw [ntm.depth_applyOne_depth0 t x s hs, ntmList.maxDepth_applyOne_depth0 ts' x s hs]
end

lemma UnifProblem.unifDepthMs_applySubst_depth0
    (Pr : UnifProblem F X 𝔸) (x : X) (s : ntm F X 𝔸) (hs : s.depth = 0) :
    (Pr.applySubst [(x, s)]).unifDepthMs = Pr.unifDepthMs := by
  simp only [UnifProblem.unifDepthMs, UnifProblem.applySubst, List.map_map]
  congr 1
  apply List.map_congr_left
  intro c _
  cases c with
  | fresh _ t => simp [UnifConstraint.applySubst, ntm.subst_cons, ntm.subst_nil,
                        ntm.depth_applyOne_depth0 t x s hs]
  | unif u v  => simp [UnifConstraint.applySubst, ntm.subst_cons, ntm.subst_nil,
                        ntm.depth_applyOne_depth0 u x s hs, ntm.depth_applyOne_depth0 v x s hs]

lemma le_unifVars_foldl (Pr : UnifProblem F X 𝔸) (acc : Finset X) :
    acc ⊆ Pr.foldl (fun a c => match c with
      | .fresh _ _ => a | .unif s t => a ∪ (s.metavars ∪ t.metavars)) acc := by
  induction Pr generalizing acc with
  | nil => exact Finset.Subset.refl _
  | cons c rest ih =>
    simp only [List.foldl_cons]
    apply Finset.Subset.trans _ (ih _)
    cases c with
    | fresh _ _ => exact Finset.Subset.refl _
    | unif s t  => exact Finset.subset_union_left

-- x always in unifVars of a unif constraint mentioning it
lemma unifVars_mem_of_unif_mvar (x : X) (π : LPerm 𝔸) (u : ntm F X 𝔸)
    (rest : UnifProblem F X 𝔸) :
    x ∈ UnifProblem.unifVars (UnifConstraint.unif (ntm.mvar π x) u :: rest) := by
  simp [UnifProblem.unifVars, List.foldl_cons, ntm.metavars]
  exact le_unifVars_foldl rest _ (Finset.mem_insert_self x _)

mutual
  lemma ntm.not_mem_metavars_applyOne_self (t : ntm F X 𝔸) (x : X) (s : ntm F X 𝔸)
      (hs : x ∉ s.metavars) :
      x ∉ (t.applyOne x s).metavars := by
    match t with
    | .atm _ => simp [ntm.applyOne, ntm.metavars]
    | .mvar π y =>
      simp only [ntm.applyOne]
      split_ifs with hyx
      · simp [ntm.permute_metavars, hs]
      · simp [ntm.metavars, hyx]
        exact Ne.symm hyx
    | .fapp _ ts =>
      simp only [ntm.applyOne, ntm.metavars]
      exact ntmList.not_mem_metavars_applyOne_self ts x s hs
    | .abs _ t' =>
      simp only [ntm.applyOne, ntm.metavars]
      exact ntm.not_mem_metavars_applyOne_self t' x s hs

  lemma ntmList.not_mem_metavars_applyOne_self (ts : List (ntm F X 𝔸)) (x : X)
      (s : ntm F X 𝔸) (hs : x ∉ s.metavars) :
      x ∉ ntmList.metavars (ts.map (·.applyOne x s)) := by
    match ts with
    | [] => simp [ntmList.metavars]
    | t :: ts' =>
      simp only [List.map_cons, ntmList.metavars, Finset.mem_union, not_or]
      exact ⟨ntm.not_mem_metavars_applyOne_self t x s hs,
             ntmList.not_mem_metavars_applyOne_self ts' x s hs⟩
end

lemma not_mem_unifVars_applySubst_self (Pr : UnifProblem F X 𝔸) (x : X)
    (s : ntm F X 𝔸) (hs : x ∉ s.metavars) :
    x ∉ (Pr.applySubst [(x, s)]).unifVars := by
  simp only [UnifProblem.unifVars, UnifProblem.applySubst]
  suffices h : ∀ acc : Finset X, x ∉ acc →
      x ∉ (Pr.map (·.applySubst [(x, s)])).foldl (fun a c => match c with
        | .fresh _ _ => a | .unif u v => a ∪ u.metavars ∪ v.metavars) acc from
    h ∅ (by simp)
  intro acc hacc
  induction Pr generalizing acc with
  | nil => simpa
  | cons c rest ih =>
    simp only [List.map_cons, List.foldl_cons]
    cases c with
    | fresh _ _ => simpa [UnifConstraint.applySubst] using ih acc hacc
    | unif u v =>
      simp only [UnifConstraint.applySubst, ntm.subst_cons, ntm.subst_nil]
      apply ih
      simp only [Finset.mem_union, not_or]
      exact ⟨⟨hacc, ntm.not_mem_metavars_applyOne_self u x s hs⟩,
         ntm.not_mem_metavars_applyOne_self v x s hs⟩

mutual
  lemma ntm.metavars_applyOne_subset (t : ntm F X 𝔸) (x : X) (s : ntm F X 𝔸) :
      (t.applyOne x s).metavars ⊆ t.metavars ∪ s.metavars := by
    match t with
    | .atm _ => simp [ntm.applyOne, ntm.metavars]
    | .mvar π y =>
      simp only [ntm.applyOne]; split_ifs with hyx
      · rw [ntm.permute_metavars]; exact Finset.subset_union_right
      · exact Finset.subset_union_left
    | .fapp _ ts =>
      simp only [ntm.applyOne, ntm.metavars]
      exact ntmList.metavars_applyOne_subset ts x s
    | .abs _ t' =>
      simp only [ntm.applyOne, ntm.metavars]
      exact ntm.metavars_applyOne_subset t' x s

  lemma ntmList.metavars_applyOne_subset (ts : List (ntm F X 𝔸)) (x : X) (s : ntm F X 𝔸) :
      ntmList.metavars (ts.map (·.applyOne x s)) ⊆ ntmList.metavars ts ∪ s.metavars := by
    match ts with
    | [] => simp [ntmList.metavars]
    | t :: ts' =>
      simp only [List.map_cons, ntmList.metavars]
      intro z hz; simp only [Finset.mem_union] at hz ⊢
      rcases hz with hz | hz
      · rcases Finset.mem_union.mp (ntm.metavars_applyOne_subset t x s hz) with h | h
        · exact Or.inl (Or.inl h)
        · exact Or.inr h
      · rcases Finset.mem_union.mp (ntmList.metavars_applyOne_subset ts' x s hz) with h | h
        · exact Or.inl (Or.inr h)
        · exact Or.inr h
end

mutual
  lemma ntm.occursIn_false_iff_not_mem_metavars (x : X) (t : ntm F X 𝔸) :
      t.occursIn x = false ↔ x ∉ t.metavars := by
    match t with
    | .atm _ => simp [ntm.occursIn, ntm.metavars]
    | .mvar _ y => simp [ntm.occursIn, ntm.metavars]
    | .fapp _ ts =>
      simp only [ntm.occursIn, ntm.metavars]
      exact ntmList.occursIn_false_iff_not_mem_metavars x ts
    | .abs _ t' =>
      simp only [ntm.occursIn, ntm.metavars]
      exact ntm.occursIn_false_iff_not_mem_metavars x t'

  lemma ntmList.occursIn_false_iff_not_mem_metavars (x : X) (ts : List (ntm F X 𝔸)) :
      ntmList.occursIn x ts = false ↔ x ∉ ntmList.metavars ts := by
    match ts with
    | [] => simp [ntmList.occursIn, ntmList.metavars]
    | hd :: tl =>
      simp only [ntmList.occursIn, ntmList.metavars, Bool.or_eq_false_iff,
                 Finset.mem_union, not_or]
      exact and_congr (ntm.occursIn_false_iff_not_mem_metavars x hd)
                      (ntmList.occursIn_false_iff_not_mem_metavars x tl)
end

lemma unifVars_foldl_applySubst_subset
      (Pr : UnifProblem F X 𝔸) (x : X) (s : ntm F X 𝔸) {acc acc' : Finset X}
      (h : acc ⊆ acc' ∪ s.metavars) :
      (Pr.applySubst [(x, s)]).foldl (fun a c => match c with
          | .fresh _ _ => a | .unif u v => a ∪ u.metavars ∪ v.metavars) acc ⊆
      Pr.foldl (fun a c => match c with
          | .fresh _ _ => a | .unif u v => a ∪ u.metavars ∪ v.metavars) acc' ∪ s.metavars := by
    induction Pr generalizing acc acc' with
    | nil => simpa [UnifProblem.applySubst] using h
    | cons c rest ih =>
      simp only [UnifProblem.applySubst, List.map_cons, List.foldl_cons]
      apply ih
      cases c with
      | fresh _ _ => simpa [UnifConstraint.applySubst] using h
      | unif u v =>
        simp only [UnifConstraint.applySubst, ntm.subst_cons, ntm.subst_nil]
        refine Finset.union_subset (Finset.union_subset ?_ ?_) ?_
        · refine Finset.Subset.trans h ?_
          intro z hz; simp only [Finset.mem_union] at hz ⊢; tauto
        · refine Finset.Subset.trans (ntm.metavars_applyOne_subset u x s) ?_
          intro z hz; simp only [Finset.mem_union] at hz ⊢; tauto
        · refine Finset.Subset.trans (ntm.metavars_applyOne_subset v x s) ?_
          intro z hz; simp only [Finset.mem_union] at hz ⊢; tauto

lemma UnifProblem.unifVars_applySubst_subset
    (Pr : UnifProblem F X 𝔸) (x : X) (s : ntm F X 𝔸) :
    (Pr.applySubst [(x, s)]).unifVars ⊆ Pr.unifVars ∪ s.metavars :=
  unifVars_foldl_applySubst_subset Pr x s (by simp)

lemma ntm.depth_le_maxDepth {s : ntm F X 𝔸} :
    ∀ {ss : List (ntm F X 𝔸)}, s ∈ ss → s.depth ≤ ntmList.maxDepth ss
  | [], h => by simp at h
  | hd :: tl, h => by
    simp only [ntmList.maxDepth]
    rcases List.mem_cons.mp h with rfl | h
    · exact Nat.le_max_left _ _
    · exact (ntm.depth_le_maxDepth h).trans (Nat.le_max_right _ _)

lemma unifVars_foldl_zip_subset
    (ss ts : List (ntm F X 𝔸)) (acc : Finset X) :
    ((ss.zip ts).map (fun p => UnifConstraint.unif p.1 p.2)).foldl
      (fun a c => match c with
        | .fresh _ _ => a
        | .unif s t => a ∪ s.metavars ∪ t.metavars) acc ⊆
    acc ∪ ntmList.metavars ss ∪ ntmList.metavars ts := by
  induction ss generalizing ts acc with
  | nil =>
    intro z hz; simp [List.zip] at hz
    simp only [Finset.mem_union]; tauto
  | cons s ss' ih =>
    cases ts with
    | nil =>
      intro z hz; simp [List.zip] at hz
      simp only [Finset.mem_union]; tauto
    | cons t ts' =>
      simp only [List.zip_cons_cons, List.map_cons, List.foldl_cons, ntmList.metavars]
      refine (ih ts' _).trans ?_
      intro z hz; simp only [Finset.mem_union] at hz ⊢; tauto

end Nominal
