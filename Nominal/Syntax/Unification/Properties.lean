import Nominal.Syntax.Unification.Algorithm

namespace Nominal

open Core

variable {F X 𝔸 : Type*} [DecidableEq F] [DecidableEq X] [Name 𝔸]

-- ============================================================
-- Soundness of `unifStep`.
--
-- For each `.next Pr' σ'` outcome, a context `Γ` that entails the converted
-- (next) problem also entails the converted (original) problem.  This is the
-- "one direction" needed to argue that the algorithm only ever produces real
-- solutions.
-- ============================================================

/-- Convert + applySubst commute. -/
@[simp] lemma UnifConstraint.toConstraint_applySubst (c : UnifConstraint F X 𝔸)
    (σ : Subst F X 𝔸) :
    (c.applySubst σ).toConstraint = c.toConstraint.applySubst σ := by
  cases c <;> simp [UnifConstraint.applySubst, UnifConstraint.toConstraint,
                    Constraint.applySubst]

@[simp] lemma UnifProblem.toConstraint_applySubst (Pr : UnifProblem F X 𝔸)
    (σ : Subst F X 𝔸) :
    (Pr.applySubst σ).toConstraint = Pr.toConstraint.applySubst σ := by
  simp [UnifProblem.toConstraint, UnifProblem.applySubst, Problem.applySubst,
        List.map_map, Function.comp_def]

@[simp] lemma UnifProblem.applySubst_cons (c : UnifConstraint F X 𝔸)
    (rest : UnifProblem F X 𝔸) (σ : Subst F X 𝔸) :
    UnifProblem.applySubst (c :: rest) σ =
      c.applySubst σ :: UnifProblem.applySubst rest σ := rfl

@[simp] lemma UnifProblem.toConstraint_cons (c : UnifConstraint F X 𝔸)
    (rest : UnifProblem F X 𝔸) :
    UnifProblem.toConstraint (c :: rest) =
      c.toConstraint :: UnifProblem.toConstraint rest := rfl

/-- `Problem.Entails` on a cons. -/
lemma Problem.Entails_cons {Γ : Context 𝔸 X} {c : Constraint F X 𝔸}
    {P : Problem F X 𝔸} :
    Problem.Entails Γ (c :: P) ↔ c.Entails Γ ∧ Problem.Entails Γ P := by
  constructor
  · intro h
    refine ⟨h c List.mem_cons_self, fun c' hc' => h c' (List.mem_cons_of_mem _ hc')⟩
  · rintro ⟨hc, hP⟩ c' hc'
    rcases List.mem_cons.mp hc' with rfl | hc'
    · exact hc
    · exact hP c' hc'

/-- Pairwise entailment on `ss.zip ts` (substituted form) gives `alphaEquivList`
    on the substituted lists. -/
lemma alphaEquivList_of_zip_subst_entails (Γ : Context 𝔸 X) (σ : Subst F X 𝔸) :
    ∀ (ss ts : List (ntm F X 𝔸)),
      ss.length = ts.length →
      Problem.Entails Γ
        ((ss.zip ts).map (fun p => Constraint.alpha (p.1.subst σ) (p.2.subst σ))) →
      alphaEquivList Γ (ss.map (·.subst σ)) (ts.map (·.subst σ)) = true
  | [], [], _, _ => by simp [alphaEquivList]
  | [], _ :: _, hlen, _ => by simp at hlen
  | _ :: _, [], hlen, _ => by simp at hlen
  | s :: ss', t :: ts', hlen, hzip => by
    simp only [List.zip_cons_cons, List.map_cons, Problem.Entails_cons] at hzip
    obtain ⟨hst, htail⟩ := hzip
    simp only [Constraint.Entails] at hst
    simp only [List.map_cons, alphaEquivList, hst, true_and,
               decide_eq_true_eq]
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
    exact alphaEquivList_of_zip_subst_entails Γ σ ss' ts' hlen htail

-- ============================================================
-- Commutation of `simplifyFresh` with substitution.
-- ============================================================

mutual
  /-- If `simplifyFresh a t = some cs` and the substituted leaves are entailed
      by Γ, then `Γ ⊢ a # t.subst τ`. -/
  lemma fresh_subst_of_simplifyFresh_entails (Γ : Context 𝔸 X) (a : 𝔸)
      (τ : Subst F X 𝔸) :
      ∀ (t : ntm F X 𝔸) (cs : Problem F X 𝔸),
        simplifyFresh a t = some cs →
        Problem.Entails Γ (cs.applySubst τ) →
        (Γ ⊢ a # t.subst τ) = true
    | .atm b, cs, hs, _ => by
      simp only [simplifyFresh] at hs
      by_cases hab : a = b
      · rw [if_pos hab] at hs; cases hs
      · rw [if_neg hab] at hs
        simp [ntm.subst_atm, fresh_atm, hab]
    | .mvar π x, cs, hs, hcs => by
      simp only [simplifyFresh] at hs
      injection hs with hcs_eq
      subst hcs_eq
      rw [ntm.subst_mvar]
      rw [show a = LPermApply π (LPermApply π.reverse a)
            from (LPermApply_reverse_right π a).symm]
      rw [← fresh_equivariance]
      have hmem : Constraint.fresh (LPermApply π.reverse a)
          ((ntm.mvar (F := F) [] x).subst τ) ∈
          Problem.applySubst
            [Constraint.fresh (LPermApply π.reverse a)
              ((ntm.mvar (F := F) [] x : ntm F X 𝔸))] τ := by
        simp [Problem.applySubst, Constraint.applySubst]
      have := hcs _ hmem
      simp only [Constraint.Entails] at this
      exact this
    | .fapp _ ts, cs, hs, hcs => by
      simp only [simplifyFresh] at hs
      simp only [ntm.subst_fapp, fresh]
      exact freshList_subst_of_simplifyFreshList_entails Γ a τ ts cs hs hcs
    | .abs b t', cs, hs, hcs => by
      simp only [simplifyFresh] at hs
      split_ifs at hs with hab
      · simp [ntm.subst_abs, fresh, hab]
      · simp [ntm.subst_abs, fresh]
        right
        exact fresh_subst_of_simplifyFresh_entails Γ a τ t' cs hs hcs

  lemma freshList_subst_of_simplifyFreshList_entails (Γ : Context 𝔸 X) (a : 𝔸)
      (τ : Subst F X 𝔸) :
      ∀ (ts : List (ntm F X 𝔸)) (cs : Problem F X 𝔸),
        simplifyFreshList a ts = some cs →
        Problem.Entails Γ (cs.applySubst τ) →
        freshList Γ a (ts.map (·.subst τ)) = true
    | [], cs, hs, _ => by
      simp only [simplifyFreshList] at hs
      injection hs with hcs_eq
      subst hcs_eq
      simp [freshList]
    | t :: ts', cs, hs, hcs => by
      simp only [simplifyFreshList] at hs
      cases hf : simplifyFresh a t with
      | none => rw [hf] at hs; cases hs
      | some cs₁ =>
        cases hg : simplifyFreshList a ts' with
        | none => rw [hf, hg] at hs; cases hs
        | some cs₂ =>
          rw [hf, hg] at hs
          injection hs with hcs_eq
          subst hcs_eq
          have hcs' : Problem.Entails Γ (cs₁.applySubst τ) ∧
                      Problem.Entails Γ (cs₂.applySubst τ) := by
            rw [show (cs₁ ++ cs₂).applySubst τ = cs₁.applySubst τ ++ cs₂.applySubst τ from by
                  simp [Problem.applySubst, List.map_append],
                Problem.Entails_append_iff] at hcs
            exact hcs
          simp [List.map_cons, freshList]
          refine ⟨?_, ?_⟩
          · exact fresh_subst_of_simplifyFresh_entails Γ a τ t cs₁ hf hcs'.1
          · exact freshList_subst_of_simplifyFreshList_entails Γ a τ ts' cs₂ hg hcs'.2
end

/-- Soundness of `.next` outcomes: if `Γ` entails `Pr'.applySubst τ` for ANY
    target substitution `τ`, then `Γ` entails `(c :: rest).applySubst τ`.
    `τ` is independent of the `.next` output `σ'` so this lemma composes with
    deeper recursion (where the final σ extends σ'). -/
lemma unifStep_next_sound
    (c : UnifConstraint F X 𝔸) (rest : UnifProblem F X 𝔸) (σ : Subst F X 𝔸)
    (Pr' : UnifProblem F X 𝔸) (σ' : Subst F X 𝔸) (Γ : Context 𝔸 X)
    (τ : Subst F X 𝔸)
    (h : unifStep c rest σ = .next Pr' σ')
    (hΓ : Problem.Entails Γ (UnifProblem.toConstraint (UnifProblem.applySubst Pr' τ))) :
    Problem.Entails Γ (UnifProblem.toConstraint (UnifProblem.applySubst (c :: rest) τ)) := by
  cases c with
  | fresh a t =>
    cases t with
    | mvar π x =>
      simp [unifStep] at h
    | atm b =>
      simp only [unifStep, simplifyFresh] at h
      by_cases hab : a = b
      · simp only [if_pos hab] at h
        exact absurd h (by simp)
      · simp only [if_neg hab, List.map_nil, List.append_nil, StepResult.next.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp only [UnifProblem.applySubst_cons, UnifProblem.toConstraint_cons,
                   Problem.Entails_cons]
        refine ⟨?_, hΓ⟩
        simp [UnifConstraint.applySubst, UnifConstraint.toConstraint,
              Constraint.Entails, fresh_atm, hab]
    | fapp f ts =>
      simp only [unifStep, simplifyFresh] at h
      cases hcs : simplifyFreshList a ts with
      | none => rw [hcs] at h; cases h
      | some cs =>
        rw [hcs] at h
        simp only [StepResult.next.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rw [UnifProblem.applySubst, List.map_append, ← UnifProblem.applySubst,
            ← UnifProblem.applySubst,
            UnifProblem.toConstraint, List.map_append, ← UnifProblem.toConstraint,
            ← UnifProblem.toConstraint,
            Problem.Entails_append_iff] at hΓ
        obtain ⟨hrest, hcsE⟩ := hΓ
        simp only [UnifProblem.applySubst_cons, UnifProblem.toConstraint_cons,
                   Problem.Entails_cons]
        refine ⟨?_, hrest⟩
        simp only [UnifConstraint.applySubst, UnifConstraint.toConstraint,
                   Constraint.Entails, ntm.subst_fapp, fresh, decide_eq_true_eq]
        have hcs' : Problem.Entails Γ (Problem.applySubst cs τ) := by
          intro c hc
          simp only [Problem.applySubst, List.mem_map] at hc
          obtain ⟨c0, hc0, rfl⟩ := hc
          have heq : (c0.toUnif.applySubst τ).toConstraint = c0.applySubst τ := by
            cases c0 <;> simp [Constraint.toUnif, UnifConstraint.applySubst,
                               UnifConstraint.toConstraint, Constraint.applySubst]
          have hin : c0.applySubst τ ∈
              UnifProblem.toConstraint (UnifProblem.applySubst (cs.map (·.toUnif)) τ) := by
            simp only [UnifProblem.toConstraint, UnifProblem.applySubst, List.map_map,
                       List.mem_map, Function.comp_apply]
            exact ⟨c0, hc0, heq⟩
          exact hcsE _ hin
        exact freshList_subst_of_simplifyFreshList_entails Γ a τ ts cs hcs hcs'
    | abs b t =>
      simp only [unifStep, simplifyFresh] at h
      by_cases hab : a = b
      · simp only [if_pos hab, List.map_nil, List.append_nil, StepResult.next.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        subst hab
        simp only [UnifProblem.applySubst_cons, UnifProblem.toConstraint_cons,
                   Problem.Entails_cons]
        refine ⟨?_, hΓ⟩
        simp [UnifConstraint.applySubst, UnifConstraint.toConstraint,
              Constraint.Entails, fresh_abs_same]
      · simp only [if_neg hab] at h
        cases hcs : simplifyFresh a t with
        | none => rw [hcs] at h; cases h
        | some cs =>
          rw [hcs] at h
          simp only [StepResult.next.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          rw [UnifProblem.applySubst, List.map_append, ← UnifProblem.applySubst,
              ← UnifProblem.applySubst,
              UnifProblem.toConstraint, List.map_append, ← UnifProblem.toConstraint,
              ← UnifProblem.toConstraint,
              Problem.Entails_append_iff] at hΓ
          obtain ⟨hrest, hcsE⟩ := hΓ
          simp only [UnifProblem.applySubst_cons, UnifProblem.toConstraint_cons,
                     Problem.Entails_cons]
          refine ⟨?_, hrest⟩
          simp only [UnifConstraint.applySubst, UnifConstraint.toConstraint,
                     Constraint.Entails, ntm.subst_abs, fresh,
                     Bool.decide_or, Bool.or_eq_true, decide_eq_true_eq]
          right
          have hcs' : Problem.Entails Γ (Problem.applySubst cs τ) := by
            intro c hc
            simp only [Problem.applySubst, List.mem_map] at hc
            obtain ⟨c0, hc0, rfl⟩ := hc
            have heq : (c0.toUnif.applySubst τ).toConstraint = c0.applySubst τ := by
              cases c0 <;> simp [Constraint.toUnif, UnifConstraint.applySubst,
                                 UnifConstraint.toConstraint, Constraint.applySubst]
            have hin : c0.applySubst τ ∈
                UnifProblem.toConstraint (UnifProblem.applySubst (cs.map (·.toUnif)) τ) := by
              simp only [UnifProblem.toConstraint, UnifProblem.applySubst, List.map_map,
                         List.mem_map, Function.comp_apply]
              exact ⟨c0, hc0, heq⟩
            exact hcsE _ hin
          exact fresh_subst_of_simplifyFresh_entails Γ a τ t cs hcs hcs'
  | unif s t =>
    cases s with
    | atm a =>
      cases t with
      | atm b =>
        simp only [unifStep] at h
        by_cases hab : a = b
        · simp only [if_pos hab, StepResult.next.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          subst hab
          simp only [UnifProblem.applySubst_cons, UnifProblem.toConstraint_cons,
                     Problem.Entails_cons]
          refine ⟨?_, hΓ⟩
          simp [UnifConstraint.applySubst, UnifConstraint.toConstraint,
                Constraint.applySubst, Constraint.Entails, alphaEquiv]
        · simp only [if_neg hab] at h
          exact absurd h (by simp)
      | mvar π x => sorry
      | fapp _ _ | abs _ _ => simp [unifStep] at h
    | mvar π x =>
      cases t with
      | atm a => sorry
      | mvar π' y =>
        simp only [unifStep] at h
        by_cases hxy : x = y
        · subst hxy
          simp at h
          obtain ⟨rfl, rfl⟩ := h
          simp only [UnifProblem.applySubst_cons, UnifProblem.toConstraint_cons,
                     Problem.Entails_cons]
          -- hΓ has the (rest ++ fresh_list).applySubst σ'.toConstraint piece
          rw [UnifProblem.applySubst, List.map_append, ← UnifProblem.applySubst,
              ← UnifProblem.applySubst,
              UnifProblem.toConstraint, List.map_append, ← UnifProblem.toConstraint,
              ← UnifProblem.toConstraint,
              Problem.Entails_append_iff] at hΓ
          obtain ⟨hrest, hfresh⟩ := hΓ
          refine ⟨?_, hrest⟩
          -- Goal: alphaEquiv ((mvar π x).subst σ') ((mvar π' x).subst σ')
          simp only [UnifConstraint.applySubst, UnifConstraint.toConstraint,
                     Constraint.Entails]
          have heq1 : (ntm.mvar π x : ntm F X 𝔸).subst τ =
              ((ntm.mvar (F := F) [] x : ntm F X 𝔸).subst τ).permute π :=
            ntm.subst_mvar π x τ
          have heq2 : (ntm.mvar π' x : ntm F X 𝔸).subst τ =
              ((ntm.mvar (F := F) [] x : ntm F X 𝔸).subst τ).permute π' :=
            ntm.subst_mvar π' x τ
          rw [heq1, heq2]
          apply ntm.alphaEquiv_of_perm_fresh
          intro n hn
          -- Use hfresh on the corresponding `.fresh n (mvar [] x)` constraint
          have hmem : n ∈ dsList π π' := (mem_dsList_iff_mem_ds n π π').mpr hn
          have hcfresh : Constraint.fresh n (((ntm.mvar (F := F) [] x : ntm F X 𝔸).subst τ)) ∈
              UnifProblem.toConstraint
                ((UnifProblem.applySubst
                  ((dsList π π').map (fun a => UnifConstraint.fresh a (ntm.mvar [] x))) τ)) := by
            simp only [UnifProblem.applySubst, UnifProblem.toConstraint, List.map_map,
                       List.mem_map, Function.comp_def]
            exact ⟨n, hmem, by simp [UnifConstraint.applySubst, UnifConstraint.toConstraint]⟩
          have := hfresh _ hcfresh
          simp only [Constraint.Entails] at this
          exact this
        · sorry
      | fapp f ts => sorry
      | abs b t => sorry
    | fapp f ss =>
      cases t with
      | fapp g ts =>
        simp only [unifStep] at h
        split_ifs at h with hfg
        · obtain ⟨rfl, rfl⟩ := h
          obtain ⟨rfl, hlen⟩ := hfg
          rw [UnifProblem.applySubst, List.map_append, ← UnifProblem.applySubst,
              ← UnifProblem.applySubst,
              UnifProblem.toConstraint, List.map_append, ← UnifProblem.toConstraint,
              ← UnifProblem.toConstraint,
              Problem.Entails_append_iff] at hΓ
          obtain ⟨hzip, hrest⟩ := hΓ
          simp only [UnifProblem.applySubst_cons, UnifProblem.toConstraint_cons,
                     Problem.Entails_cons]
          refine ⟨?_, hrest⟩
          simp only [UnifConstraint.applySubst, UnifConstraint.toConstraint,
                     Constraint.Entails, ntm.subst_fapp, alphaEquiv,
                     Bool.decide_and, Bool.and_eq_true, decide_eq_true_eq]
          refine ⟨trivial, ?_⟩
          apply alphaEquivList_of_zip_subst_entails Γ τ ss ts hlen
          simp only [UnifProblem.applySubst, UnifProblem.toConstraint,
                     List.map_map, Function.comp_def,
                     UnifConstraint.applySubst, UnifConstraint.toConstraint] at hzip
          exact hzip
      | mvar π' y => sorry
      | atm _ | abs _ _ => simp [unifStep] at h
    | abs a s' =>
      cases t with
      | abs b t' =>
        simp only [unifStep] at h
        by_cases hab : a = b
        · subst hab
          simp only [if_pos rfl, StepResult.next.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          simp only [UnifProblem.applySubst_cons, UnifProblem.toConstraint_cons,
                     Problem.Entails_cons] at hΓ ⊢
          obtain ⟨hst, hrest⟩ := hΓ
          refine ⟨?_, hrest⟩
          simp only [UnifConstraint.applySubst, UnifConstraint.toConstraint,
                     Constraint.Entails, ntm.subst_abs, alphaEquiv,
                     decide_eq_true_eq, if_pos rfl] at hst ⊢
          exact hst
        · simp only [if_neg hab, StepResult.next.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          simp only [UnifProblem.applySubst_cons, UnifProblem.toConstraint_cons,
                     Problem.Entails_cons] at hΓ ⊢
          obtain ⟨hperm, hfresh, hrest⟩ := hΓ
          refine ⟨?_, hrest⟩
          simp only [UnifConstraint.applySubst, UnifConstraint.toConstraint,
                     Constraint.Entails, ntm.subst_abs, alphaEquiv,
                     decide_eq_true_eq, if_neg hab] at hperm hfresh ⊢
          refine ⟨?_, hfresh⟩
          rw [ntm.subst_permute] at hperm
          exact hperm
      | mvar π' y => sorry
      | atm _ | fapp _ _ => simp [unifStep] at h

-- ============================================================
-- Freshness monotonicity in Γ (used by `finalizeDeferred_sound`).
-- ============================================================

mutual
  /-- Freshness is monotone in the context. -/
  theorem fresh_mono {Γ Γ' : Context 𝔸 X} (hsub : Γ ⊆ Γ') (a : 𝔸) (t : ntm F X 𝔸)
      (h : (Γ ⊢ a # t) = true) : (Γ' ⊢ a # t) = true := by
    match t with
    | ntm.atm _ => exact h
    | ntm.mvar π x =>
      simp only [fresh, decide_eq_true_eq] at h ⊢
      exact hsub h
    | ntm.fapp _ ts =>
      simp only [fresh] at h ⊢
      exact freshList_mono hsub a ts h
    | ntm.abs b s =>
      simp [fresh] at h ⊢
      rcases h with hab | hs
      · exact Or.inl hab
      · exact Or.inr (fresh_mono hsub a s hs)

  theorem freshList_mono {Γ Γ' : Context 𝔸 X} (hsub : Γ ⊆ Γ') (a : 𝔸)
      (ts : List (ntm F X 𝔸)) (h : freshList Γ a ts = true) :
      freshList Γ' a ts = true := by
    match ts with
    | [] => rfl
    | t :: ts' =>
      simp [freshList] at h ⊢
      obtain ⟨h1, h2⟩ := h
      exact ⟨fresh_mono hsub a t h1, freshList_mono hsub a ts' h2⟩
end

-- ============================================================
-- Soundness of `finalizeDeferred`.
-- ============================================================

/-- A reduced constraint has the shape `.fresh _ (.mvar [] _)`. -/
lemma Constraint.reduced_destr {c : Constraint F X 𝔸} (h : c.IsReduced = true) :
    ∃ a x, c = .fresh a (.mvar [] x) := by
  cases c with
  | fresh a t =>
    cases t with
    | mvar π x =>
      cases π with
      | nil => exact ⟨a, x, rfl⟩
      | cons _ _ => simp [Constraint.IsReduced] at h
    | atm _  => simp [Constraint.IsReduced] at h
    | fapp _ _ => simp [Constraint.IsReduced] at h
    | abs _ _ => simp [Constraint.IsReduced] at h
  | alpha _ _ => simp [Constraint.IsReduced] at h

/-- The foldl that builds the new Γ from reduced freshness constraints. -/
private def finalize_foldl_step (Γ : Context 𝔸 X) (cs : List (Constraint F X 𝔸)) :
    Context 𝔸 X :=
  cs.foldl (fun g c =>
    match c with
    | .fresh a' (.mvar [] x') => insert (a', x') g
    | _                       => g) Γ

lemma finalize_foldl_step_mono (Γ : Context 𝔸 X) (cs : List (Constraint F X 𝔸)) :
    Γ ⊆ finalize_foldl_step Γ cs := by
  induction cs generalizing Γ with
  | nil => simp [finalize_foldl_step]
  | cons c cs' ih =>
    simp only [finalize_foldl_step, List.foldl_cons]
    refine Finset.Subset.trans ?_ (ih _)
    cases c with
    | fresh a' t =>
      cases t with
      | mvar π x =>
        cases π with
        | nil => exact Finset.subset_insert _ _
        | cons _ _ => exact Finset.Subset.refl _
      | _ => exact Finset.Subset.refl _
    | alpha _ _ => exact Finset.Subset.refl _

/-- Reduced constraints in cs are entailed by the foldl-built context. -/
lemma finalize_foldl_step_entails (Γ : Context 𝔸 X) (cs : List (Constraint F X 𝔸))
    (hred : Problem.IsReduced cs) :
    Problem.Entails (finalize_foldl_step Γ cs) cs := by
  intro c hc
  obtain ⟨a', x', rfl⟩ := Constraint.reduced_destr (hred c hc)
  simp only [Constraint.Entails, fresh, List.reverse_nil, LPermApply_nil,
             decide_eq_true_eq]
  clear hred
  induction cs generalizing Γ with
  | nil => cases hc
  | cons c0 cs' ih =>
    simp only [finalize_foldl_step, List.foldl_cons]
    rcases List.mem_cons.mp hc with hh | hmem
    · subst hh
      apply finalize_foldl_step_mono
      exact Finset.mem_insert_self _ _
    · exact ih _ hmem

/-- Specialised Problem-entailment monotonicity for reduced problems. -/
lemma Problem.Entails_mono_reduced {Γ Γ' : Context 𝔸 X} (hsub : Γ ⊆ Γ')
    {P : Problem F X 𝔸} (hred : Problem.IsReduced P)
    (h : Problem.Entails Γ P) : Problem.Entails Γ' P := by
  intro c hc
  obtain ⟨a', x', rfl⟩ := Constraint.reduced_destr (hred c hc)
  have := h _ hc
  simp only [Constraint.Entails] at this ⊢
  exact fresh_mono hsub _ _ this

/-- Soundness of `finalizeDeferred`: every deferred `(a, x)` is satisfied by the
    returned context, and the initial context is preserved. -/
lemma finalizeDeferred_sound (σ : Subst F X 𝔸) :
    ∀ (ds : List (𝔸 × X)) (Γ₀ Γ : Context 𝔸 X),
      finalizeDeferred ds σ Γ₀ = some Γ →
      Γ₀ ⊆ Γ ∧ ∀ p ∈ ds, (Γ ⊢ p.1 # (ntm.mvar (F := F) [] p.2).subst σ) = true
  | [], Γ₀, Γ, h => by
    simp only [finalizeDeferred, Option.some.injEq] at h
    subst h
    exact ⟨Finset.Subset.refl _, by intro p hp; cases hp⟩
  | (a, x) :: tl, Γ₀, Γ, h => by
    simp only [finalizeDeferred] at h
    cases hcs : simplifyFresh a ((ntm.mvar (F := F) [] x).subst σ) with
    | none => rw [hcs] at h; cases h
    | some cs =>
      rw [hcs] at h
      have hrec := finalizeDeferred_sound σ tl (finalize_foldl_step Γ₀ cs) Γ
        (show finalizeDeferred tl σ (finalize_foldl_step Γ₀ cs) = some Γ from h)
      refine ⟨?_, ?_⟩
      · exact Finset.Subset.trans (finalize_foldl_step_mono Γ₀ cs) hrec.1
      · rintro p hp
        rcases List.mem_cons.mp hp with hh | hmem
        · subst hh
          have hred : Problem.IsReduced cs := simplifyFresh_isReduced a _ hcs
          have hent : Problem.Entails (finalize_foldl_step Γ₀ cs) cs :=
            finalize_foldl_step_entails Γ₀ cs hred
          have hent' : Problem.Entails Γ cs :=
            Problem.Entails_mono_reduced hrec.1 hred hent
          exact (simplifyFresh_sound Γ a _ hcs).mpr hent'
        · exact hrec.2 p hmem

-- ============================================================
-- Soundness of `unify`.
-- ============================================================

/-- Inversion of `.ctx`: only `.fresh _ (.mvar _ _)` produces it. -/
lemma unifStep_ctx_inv (c : UnifConstraint F X 𝔸) (rest : UnifProblem F X 𝔸)
    (σ : Subst F X 𝔸) (a : 𝔸) (x : X) (h : unifStep c rest σ = .ctx a x) :
    ∃ (b : 𝔸) (π : LPerm 𝔸), c = .fresh b (.mvar π x) ∧ a = LPermApply π.reverse b := by
  cases c with
  | fresh b t =>
    cases t with
    | mvar π y =>
      simp only [unifStep, StepResult.ctx.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨b, π, rfl, rfl⟩
    | atm a' =>
      simp only [unifStep] at h
      cases hcs : simplifyFresh b (.atm (F := F) (X := X) a') with
      | none => rw [hcs] at h; cases h
      | some cs => rw [hcs] at h; cases h
    | fapp f ts =>
      simp only [unifStep] at h
      cases hcs : simplifyFresh b (.fapp f ts) with
      | none => rw [hcs] at h; cases h
      | some cs => rw [hcs] at h; cases h
    | abs c t =>
      simp only [unifStep] at h
      cases hcs : simplifyFresh b (.abs c t) with
      | none => rw [hcs] at h; cases h
      | some cs => rw [hcs] at h; cases h
  | unif s t =>
    cases s <;> cases t <;>
      first
        | (simp only [unifStep] at h; split_ifs at h)
        | (simp only [unifStep] at h; cases h)

/-- Soundness of `unify`: if the final deferred is satisfied by `Γ` under `σ'`,
    then `Γ` satisfies the original problem under `σ'` and the original deferred. -/
theorem unify_sound (Γ : Context 𝔸 X) :
    ∀ (Pr : UnifProblem F X 𝔸) (σ : Subst F X 𝔸) (ds : List (𝔸 × X)),
      ∀ (ds' : List (𝔸 × X)) (σ' : Subst F X 𝔸),
        unify Pr σ ds = some (ds', σ') →
        (∀ p ∈ ds', (Γ ⊢ p.1 # (ntm.mvar (F := F) [] p.2).subst σ') = true) →
        Problem.Entails Γ (UnifProblem.applySubst Pr σ').toConstraint ∧
        (∀ p ∈ ds, (Γ ⊢ p.1 # (ntm.mvar (F := F) [] p.2).subst σ') = true) := by
  intro Pr σ ds
  induction Pr, σ, ds using unify.induct with
  | case1 σ ds =>
    intro ds' σ' h hf
    simp only [unify, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨?_, hf⟩
    intro c hc
    simp [UnifProblem.applySubst, UnifProblem.toConstraint] at hc
  | case2 σ ds c rest hfail =>
    intro ds' σ' h hf
    rw [unify] at h
    rw [hfail] at h
    cases h
  | case3 σ ds c rest a x hctx ih =>
    intro ds' σ' h hf
    rw [unify] at h
    rw [hctx] at h
    obtain ⟨hpr, hds_all⟩ := ih ds' σ' h hf
    -- Get c = .fresh b (.mvar π x) and a = π⁻¹·b.
    obtain ⟨b, π, rfl, rfl⟩ := unifStep_ctx_inv c rest σ a x hctx
    refine ⟨?_, ?_⟩
    · simp only [UnifProblem.applySubst_cons, UnifProblem.toConstraint_cons,
                 Problem.Entails_cons]
      refine ⟨?_, hpr⟩
      have ha := hds_all (LPermApply π.reverse b, x) List.mem_cons_self
      simp only [Constraint.Entails, UnifConstraint.applySubst, UnifConstraint.toConstraint]
      rw [ntm.subst_mvar]
      rw [show b = LPermApply π (LPermApply π.reverse b)
            from (LPermApply_reverse_right π b).symm]
      rw [← fresh_equivariance]
      exact ha
    · intro p hp
      exact hds_all p (List.mem_cons_of_mem _ hp)
  | case4 σ ds c rest Pr' σ_next hnext ih =>
    intro ds' σ' h hf
    rw [unify] at h
    rw [hnext] at h
    obtain ⟨hpr', hds⟩ := ih ds' σ' h hf
    refine ⟨?_, hds⟩
    exact unifStep_next_sound c rest σ Pr' σ_next Γ σ' hnext hpr'

-- ============================================================
-- Soundness of `UnifProblem.solve`.
-- ============================================================

/-- `solve Pr = some (Γ, σ)` produces a context that entails `Pr` under σ. -/
theorem UnifProblem.solve_sound (Pr : UnifProblem F X 𝔸) (Γ : Context 𝔸 X)
    (σ : Subst F X 𝔸) (h : Pr.solve = some (Γ, σ)) :
    Problem.Entails Γ (Pr.applySubst σ).toConstraint := by
  simp only [UnifProblem.solve] at h
  cases hu : unify Pr [] [] with
  | none => rw [hu] at h; cases h
  | some result =>
    rw [hu] at h
    obtain ⟨ds, σ_u⟩ := result
    simp only at h
    cases hf : finalizeDeferred ds σ_u ∅ with
    | none => rw [hf] at h; cases h
    | some Γ_fin =>
      rw [hf] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨hΓeq, hσeq⟩ := h
      subst hΓeq
      subst hσeq
      have ⟨_, hfresh⟩ := finalizeDeferred_sound σ_u ds ∅ Γ_fin hf
      exact (unify_sound Γ_fin Pr [] [] ds σ_u hu hfresh).1

end Nominal
