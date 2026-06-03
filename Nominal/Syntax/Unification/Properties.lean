import Nominal.Syntax.Unification.Algorithm.Defs

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
    simp only [List.map_cons, alphaEquivList, Bool.and_eq_true, hst, true_and,
               decide_eq_true_eq]
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
    exact alphaEquivList_of_zip_subst_entails Γ σ ss' ts' hlen htail

/-- Soundness of `.next` outcomes: if `Γ` entails `Pr'.applySubst σ'` (the next
    problem under the next σ), then `Γ` entails `(c :: rest).applySubst σ'` —
    so an entailed next-state corresponds to an entailed original state. -/
lemma unifStep_next_sound
    (c : UnifConstraint F X 𝔸) (rest : UnifProblem F X 𝔸) (σ : Subst F X 𝔸)
    (Pr' : UnifProblem F X 𝔸) (σ' : Subst F X 𝔸) (Γ : Context 𝔸 X)
    (h : unifStep c rest σ = .next Pr' σ')
    (hΓ : Problem.Entails Γ (UnifProblem.toConstraint (UnifProblem.applySubst Pr' σ'))) :
    Problem.Entails Γ (UnifProblem.toConstraint (UnifProblem.applySubst (c :: rest) σ')) := by
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
      sorry
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
        sorry
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
          have heq1 : (ntm.mvar π x : ntm F X 𝔸).subst σ =
              ((ntm.mvar (F := F) [] x : ntm F X 𝔸).subst σ).permute π :=
            ntm.subst_mvar π x σ
          have heq2 : (ntm.mvar π' x : ntm F X 𝔸).subst σ =
              ((ntm.mvar (F := F) [] x : ntm F X 𝔸).subst σ).permute π' :=
            ntm.subst_mvar π' x σ
          rw [heq1, heq2]
          apply ntm.alphaEquiv_of_perm_fresh
          intro n hn
          -- Use hfresh on the corresponding `.fresh n (mvar [] x)` constraint
          have hmem : n ∈ dsList π π' := (mem_dsList_iff_mem_ds n π π').mpr hn
          have hcfresh : Constraint.fresh n (((ntm.mvar (F := F) [] x : ntm F X 𝔸).subst σ)) ∈
              UnifProblem.toConstraint
                ((UnifProblem.applySubst
                  ((dsList π π').map (fun a => UnifConstraint.fresh a (ntm.mvar [] x))) σ)) := by
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
          apply alphaEquivList_of_zip_subst_entails Γ σ ss ts hlen
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

end Nominal
