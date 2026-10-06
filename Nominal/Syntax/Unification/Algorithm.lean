import Nominal.Syntax.Unification.Algorithm.Helpers

namespace Nominal

open Core

variable {F X 𝔸 : Type*} [DecidableEq F] [DecidableEq X] [Name 𝔸]


/-- Reducing `a # t`, for `t` not a suspension, yields strictly lighter freshness constraints. -/
private lemma simplifyFresh_constraints_lt (a : 𝔸) (t : ntm F X 𝔸)
    (ht : ∀ π x, t ≠ .mvar π x) {cs : Problem F X 𝔸} (h : simplifyFresh a t = some cs) :
    ∀ c ∈ cs, ∃ a' u, c = Constraint.fresh a' u ∧ u.depth + 1 < t.depth + 1 := by
  cases t with
  | mvar π x => exact absurd rfl (ht π x)
  | atm b =>
    simp [simplifyFresh] at h
    simp [h]
  | abs b t' =>
    simp only [simplifyFresh] at h
    split_ifs at h with hab
    · cases h; simp
    · intro c hc
      obtain ⟨a', u, rfl, hle⟩ := simplifyFresh_constraints_le a t' h c hc
      exact ⟨a', u, rfl, by simp only [ntm.depth]; omega⟩
  | fapp f ts =>
    simp only [simplifyFresh] at h
    intro c hc
    obtain ⟨a', u, rfl, hle⟩ := simplifyFreshList_constraints_le a ts h c hc
    exact ⟨a', u, rfl, by simp only [ntm.depth]; omega⟩

/-- Every `.next` output of `unifStep` is strictly smaller in the lex measure. -/
private lemma unifStep_next_decreasing
    (c : UnifConstraint F X 𝔸) (rest : UnifProblem F X 𝔸)
    (σ : Subst F X 𝔸) (Pr' : UnifProblem F X 𝔸) (σ' : Subst F X 𝔸)
    (h : unifStep c rest σ = .next Pr' σ') :
    Prod.Lex (fun x1 x2 ↦ x1 < x2) Multiset.IsDershowitzMannaLT
      (UnifProblem.unifVars Pr' |>.card, UnifProblem.unifDepthMs Pr')
      ((UnifProblem.unifVars (c :: rest)).card,
       UnifProblem.unifDepthMs (c :: rest)) := by
  cases UnifRule.of_unifStep h with
  | fresh a t cs ht hcs =>
    have hlt := simplifyFresh_constraints_lt a t ht hcs
    apply Prod.Lex.right'
    · -- all cs are .fresh → cs.map toUnif adds nothing to unifVars
      have hL : UnifProblem.unifVars (rest ++ cs.map (·.toUnif)) =
                UnifProblem.unifVars rest := by
        simp only [UnifProblem.unifVars, List.foldl_append]
        apply unifVars_foldl_fresh_stable
        intro c hc; simp only [List.mem_map] at hc
        obtain ⟨c₀, hc₀, rfl⟩ := hc
        obtain ⟨a', u, rfl, _⟩ := hlt c₀ hc₀
        exact ⟨a', u, rfl⟩
      have hR : UnifProblem.unifVars (UnifConstraint.fresh a t :: rest) =
                UnifProblem.unifVars rest := by
        simp [UnifProblem.unifVars, List.foldl_cons]
      simp [hL, hR]
    · -- DM: original weight = t.depth + 1; all new weights are strictly smaller
      rw [UnifProblem.unifDepthMs_append,
          show UnifProblem.unifDepthMs (UnifConstraint.fresh a t :: rest) =
               {t.depth + 1} + rest.unifDepthMs from UnifProblem.unifDepthMs_cons _ _]
      exact ⟨rest.unifDepthMs, UnifProblem.unifDepthMs (cs.map (·.toUnif)),
             {t.depth + 1}, by simp, by rfl, by abel,
             fun y hy => ⟨t.depth + 1, Multiset.mem_singleton_self _, by
               simp only [UnifProblem.unifDepthMs, List.map_map, Multiset.mem_coe,
                          List.mem_map] at hy
               obtain ⟨c, hc, rfl⟩ := hy
               obtain ⟨a', u, rfl, hlt'⟩ := hlt c hc
               simp [Constraint.toUnif]; omega⟩⟩
  | atm a =>
    apply Prod.Lex.right'
    · simp [UnifProblem.unifVars, List.foldl_cons, ntm.metavars]
    · rw [UnifProblem.unifDepthMs_cons]; simp only [ntm.depth, Nat.max_self]
      exact ⟨UnifProblem.unifDepthMs rest, ∅, {2},
             by simp, by simp, by rw [add_comm], by simp⟩
  | mvarSame π π' x =>
    apply Prod.Lex.right'
    · apply Finset.card_le_card
      have hL : UnifProblem.unifVars
                (rest ++ (dsList π π').map
                  (fun a => UnifConstraint.fresh a (ntm.mvar [] x)))
            = UnifProblem.unifVars rest := by
        simp only [UnifProblem.unifVars, List.foldl_append]
        apply unifVars_foldl_fresh_stable
        intro c hc
        simp only [List.mem_map] at hc
        obtain ⟨a, _, rfl⟩ := hc
        exact ⟨a, _, rfl⟩
      rw [hL]
      exact UnifProblem.unifVars_subset_cons _ rest
    · rw [UnifProblem.unifDepthMs_append,
        show UnifProblem.unifDepthMs
            (UnifConstraint.unif (ntm.mvar π x) (ntm.mvar π' x) :: rest)
            = {2} + UnifProblem.unifDepthMs rest from by
        rw [UnifProblem.unifDepthMs_cons]; simp [ntm.depth]]
      exact ⟨UnifProblem.unifDepthMs rest,
        UnifProblem.unifDepthMs
        ((dsList π π').map (fun a => UnifConstraint.fresh a (ntm.mvar [] x))),
        {2}, by simp, by rfl, by abel,
        fun z hz => ⟨2, Multiset.mem_singleton_self _, by
          simp only [UnifProblem.unifDepthMs, List.map_map, Multiset.mem_coe,
                     List.mem_map, Function.comp_apply] at hz
          obtain ⟨a, _, rfl⟩ := hz
          simp [ntm.depth]⟩⟩
  | instL π x u hocc =>
    -- instantiation eliminates `x`: the number of unification variables drops
    apply Prod.Lex.left
    refine Finset.card_lt_card ⟨?_, fun hsub => ?_⟩
    · refine Finset.Subset.trans
        (UnifProblem.unifVars_applySubst_subset rest x _) ?_
      rw [ntm.permute_metavars]
      refine Finset.union_subset (UnifProblem.unifVars_subset_cons _ rest) ?_
      intro z hz
      simp only [UnifProblem.unifVars, List.foldl_cons, ntm.metavars, Finset.union_assoc]
      exact le_unifVars_foldl rest _ (by
        simp only [Finset.empty_union, Finset.mem_union, Finset.mem_singleton]
        exact Or.inr hz)
    · exact not_mem_unifVars_applySubst_self rest x _
        (by rw [ntm.permute_metavars]
            exact (ntm.occursIn_false_iff_not_mem_metavars x _).mp hocc)
        (hsub (unifVars_mem_of_unif_mvar x π u rest))
  | instR π x u hocc =>
    apply Prod.Lex.left
    refine Finset.card_lt_card ⟨?_, fun hsub => ?_⟩
    · refine Finset.Subset.trans
        (UnifProblem.unifVars_applySubst_subset rest x _) ?_
      rw [ntm.permute_metavars]
      refine Finset.union_subset (UnifProblem.unifVars_subset_cons _ rest) ?_
      intro z hz
      simp only [UnifProblem.unifVars, List.foldl_cons, ntm.metavars, Finset.union_assoc]
      exact le_unifVars_foldl rest _ (by
        simp only [Finset.empty_union, Finset.mem_union, Finset.mem_singleton]
        exact Or.inl hz)
    · have hxc : x ∈ UnifProblem.unifVars
                     (UnifConstraint.unif u (ntm.mvar π x) :: rest) := by
        simp only [UnifProblem.unifVars, List.foldl_cons, ntm.metavars, Finset.union_assoc]
        exact le_unifVars_foldl rest _ (by
          simp [Finset.empty_union])
      exact not_mem_unifVars_applySubst_self rest x _
        (by rw [ntm.permute_metavars]
            exact (ntm.occursIn_false_iff_not_mem_metavars x _).mp hocc)
        (hsub hxc)
  | fapp f ss ts hlen =>
    apply Prod.Lex.right'
    · apply Finset.card_le_card
      simp only [UnifProblem.unifVars, List.foldl_append, List.foldl_cons, ntm.metavars]
      exact unifVars_foldl_mono rest (unifVars_foldl_zip_subset ss ts ∅)
    · rw [UnifProblem.unifDepthMs_append,
          show UnifProblem.unifDepthMs
                 (UnifConstraint.unif (ntm.fapp f ss) (ntm.fapp f ts) :: rest) =
               {max (1 + ntmList.maxDepth ss) (1 + ntmList.maxDepth ts) + 2} +
               UnifProblem.unifDepthMs rest from by
            rw [UnifProblem.unifDepthMs_cons]; simp [ntm.depth]]
      refine ⟨UnifProblem.unifDepthMs rest,
              UnifProblem.unifDepthMs
                ((ss.zip ts).map (fun p => UnifConstraint.unif p.1 p.2)),
              {max (1 + ntmList.maxDepth ss) (1 + ntmList.maxDepth ts) + 2},
              by simp, by abel, by abel, ?_⟩
      intro y hy
      refine ⟨_, Multiset.mem_singleton_self _, ?_⟩
      simp only [UnifProblem.unifDepthMs, List.map_map, Multiset.mem_coe,
                 List.mem_map, Function.comp_apply] at hy
      obtain ⟨p, hp, rfl⟩ := hy
      obtain ⟨hps, hpt⟩ := List.of_mem_zip hp
      have h1 := ntm.depth_le_maxDepth hps
      have h2 := ntm.depth_le_maxDepth hpt
      omega
  | absSame a s t =>
    apply Prod.Lex.right'
    · -- abs strips no metavars: unifVars Pr' = unifVars (c :: rest)
      apply Finset.card_le_card
      apply Finset.subset_of_eq
      simp [UnifProblem.unifVars, List.foldl_cons, ntm.metavars, Finset.empty_union]
    · -- weight drops by 1: max(1+d_s, 1+d_t)+2 > max(d_s, d_t)+2
      have h1 : UnifProblem.unifDepthMs (.unif s t :: rest) =
                {max s.depth t.depth + 2} + UnifProblem.unifDepthMs rest :=
        UnifProblem.unifDepthMs_cons _ _
      have h2 : UnifProblem.unifDepthMs (.unif (.abs a s) (.abs a t) :: rest) =
                {max (1 + s.depth) (1 + t.depth) + 2} + UnifProblem.unifDepthMs rest := by
        rw [UnifProblem.unifDepthMs_cons]; simp [ntm.depth]
      rw [h1, h2]
      exact ⟨UnifProblem.unifDepthMs rest,
             {max s.depth t.depth + 2},
             {max (1 + s.depth) (1 + t.depth) + 2},
             by simp, by rw [add_comm], by rw [add_comm],
             by simp⟩
  | absDiff a b s t hab =>
    apply Prod.Lex.right'
    · -- metavars preserved under permutation → unifVars equal
      apply Finset.card_le_card; apply Finset.subset_of_eq
      simp [UnifProblem.unifVars, List.foldl_cons, ntm.metavars, Finset.empty_union,
            ntm.permute_metavars]
    · -- both new weights strictly < original weight → DM decrease
      have hPr : UnifProblem.unifDepthMs
          (.unif (s.permute [(b, a)]) t :: .fresh b s :: rest) =
          {max s.depth t.depth + 2} + ({s.depth + 1} +
          UnifProblem.unifDepthMs rest) := by
        rw [UnifProblem.unifDepthMs_cons, UnifProblem.unifDepthMs_cons]
        simp only [ntm.permute_depth]
      have hc : UnifProblem.unifDepthMs (.unif (.abs a s) (.abs b t) :: rest) =
          {max (1 + s.depth) (1 + t.depth) + 2} + UnifProblem.unifDepthMs rest := by
        rw [UnifProblem.unifDepthMs_cons]; simp [ntm.depth]
      rw [hPr, hc]
      exact ⟨UnifProblem.unifDepthMs rest,
             {max s.depth t.depth + 2} + {s.depth + 1},
             {max (1 + s.depth) (1 + t.depth) + 2},
             by simp,
             by abel,
             by rw [add_comm],
             by simp; omega⟩

/-- Main loop: iterate `unifStep` on the constraint queue, threading `σ` and
    a list of deferred freshness pairs.  Terminates on the lex measure
    `(unifVars.card, unifDepthMs)`.  Corresponds to Maribel's algorithm
    (Theorem 35), with freshness bindings deferred until after the loop. -/
def unify (Pr : UnifProblem F X 𝔸) (σ : Subst F X 𝔸) (deferred : List (𝔸 × X)) :
    Option (List (𝔸 × X) × Subst F X 𝔸) :=
  match Pr with
  | []        => some (deferred, σ)
  | c :: rest =>
    match h : unifStep c rest σ with
    | .fail        => none
    | .ctx a x     => unify rest σ ((a, x) :: deferred)
    | .next Pr' σ' => unify Pr' σ' deferred
termination_by (Pr.unifVars.card, Pr.unifDepthMs)
decreasing_by
  · apply Prod.Lex.right'
    · exact Finset.card_le_card (UnifProblem.unifVars_subset_cons c rest)
    · cases c with
      | fresh a t =>
        rw [UnifProblem.unifDepthMs_cons]
        exact ⟨UnifProblem.unifDepthMs rest, ∅, {t.depth + 1},
               by simp, by simp, by rw [add_comm], by simp⟩
      | unif s t =>
        rw [UnifProblem.unifDepthMs_cons]
        exact ⟨UnifProblem.unifDepthMs rest, ∅, {max s.depth t.depth + 2},
               by simp, by simp, by rw [add_comm], by simp⟩
  · exact unifStep_next_decreasing c rest σ Pr' σ' h

/-- The fold step of `finalizeDeferred`: collect primitive obligations into the context. -/
def ctxStep (g : Context 𝔸 X) (c : Constraint F X 𝔸) : Context 𝔸 X :=
  match c with
  | .fresh a' (.mvar [] x') => insert (a', x') g
  | _                       => g

/-- Post-loop step: applies the final `σ` to each deferred `(a, x)` pair and
    accumulates the reduced freshness leaves into `Γ`. -/
def finalizeDeferred : List (𝔸 × X) → Subst F X 𝔸 → Context 𝔸 X →
    Option (Context 𝔸 X)
  | [],            _, Γ => some Γ
  | (a, x) :: tl, σ, Γ =>
    match simplifyFresh a ((ntm.mvar (F := F) [] x).subst σ) with
    | none    => none
    | some cs =>
      finalizeDeferred tl σ (cs.foldl ctxStep Γ)

/-- Top-level entry point: runs `unify` then `finalizeDeferred`. -/
def UnifProblem.solve (Pr : UnifProblem F X 𝔸) : Option (Context 𝔸 X × Subst F X 𝔸) :=
  match unify Pr [] [] with
  | none => none
  | some (deferred, σ) =>
    match finalizeDeferred deferred σ ∅ with
    | none   => none
    | some Γ => some (Γ, σ)

end Nominal
