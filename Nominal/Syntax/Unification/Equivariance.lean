import Nominal.Syntax.Unification.Algorithm
import Nominal.Syntax.Rename

/-!
# Equivariance of the unification algorithm

Renaming the atoms of a problem by any bijection `ρ` renames its output accordingly:

  `(Pr.rename ρ).solve = Pr.solve.map (rename ρ)`

This is an exact equation: the algorithm only ever compares atoms for equality, so it treats
names uniformly. Correspondingly, the set of solutions is equivariant
(`UnifProblem.mem_solutions_rename`).
-/

namespace Nominal

open Core

variable {F X 𝔸 : Type*} [DecidableEq F] [DecidableEq X] [Name 𝔸]

/-! ### Renaming problems, results and deferred lists -/

def UnifConstraint.rename (ρ : Equiv.Perm 𝔸) : UnifConstraint F X 𝔸 → UnifConstraint F X 𝔸
  | .fresh a t => .fresh (ρ a) (t.rename ρ)
  | .unif s t  => .unif (s.rename ρ) (t.rename ρ)

def UnifProblem.rename (ρ : Equiv.Perm 𝔸) (Pr : UnifProblem F X 𝔸) : UnifProblem F X 𝔸 :=
  Pr.map (UnifConstraint.rename ρ)

/-- Renaming of a list of deferred obligations `a # X`. -/
def deferredRename (ρ : Equiv.Perm 𝔸) (D : List (𝔸 × X)) : List (𝔸 × X) :=
  D.map fun p => (ρ p.1, p.2)

def StepResult.rename (ρ : Equiv.Perm 𝔸) : StepResult F X 𝔸 → StepResult F X 𝔸
  | .fail      => .fail
  | .ctx a x   => .ctx (ρ a) x
  | .next Pr σ => .next (Pr.rename ρ) (Subst.rename ρ σ)

@[simp] lemma UnifProblem.rename_nil (ρ : Equiv.Perm 𝔸) :
    UnifProblem.rename ρ ([] : UnifProblem F X 𝔸) = [] := rfl

@[simp] lemma UnifProblem.rename_cons (ρ : Equiv.Perm 𝔸) (c : UnifConstraint F X 𝔸)
    (Pr : UnifProblem F X 𝔸) :
    UnifProblem.rename ρ (c :: Pr) = c.rename ρ :: Pr.rename ρ := rfl

@[simp] lemma UnifProblem.rename_append (ρ : Equiv.Perm 𝔸) (Pr Pr' : UnifProblem F X 𝔸) :
    UnifProblem.rename ρ (Pr ++ Pr') = Pr.rename ρ ++ Pr'.rename ρ := by
  simp [UnifProblem.rename]

lemma UnifProblem.rename_applySubst (ρ : Equiv.Perm 𝔸) (Pr : UnifProblem F X 𝔸)
    (σ : Subst F X 𝔸) :
    (Pr.applySubst σ).rename ρ = (Pr.rename ρ).applySubst (Subst.rename ρ σ) := by
  simp only [UnifProblem.applySubst, UnifProblem.rename, List.map_map]
  apply List.map_congr_left
  intro c _
  cases c <;> simp [UnifConstraint.applySubst, UnifConstraint.rename, ntm.rename_subst]

/-- `UnifProblem.rename_applySubst` with the renaming unfolded to `List.map`. -/
lemma map_rename_applySubst (ρ : Equiv.Perm 𝔸) (Pr : UnifProblem F X 𝔸) (σ : Subst F X 𝔸) :
    (Pr.applySubst σ).map (UnifConstraint.rename ρ)
      = UnifProblem.applySubst (Pr.map (UnifConstraint.rename ρ)) (Subst.rename ρ σ) :=
  UnifProblem.rename_applySubst ρ Pr σ

lemma Constraint.toUnif_rename (ρ : Equiv.Perm 𝔸) (c : Constraint F X 𝔸) :
    (c.rename ρ).toUnif = c.toUnif.rename ρ := by
  cases c <;> rfl

lemma UnifConstraint.toConstraint_rename (ρ : Equiv.Perm 𝔸) (c : UnifConstraint F X 𝔸) :
    (c.rename ρ).toConstraint = c.toConstraint.rename ρ := by
  cases c <;> rfl

mutual
  lemma ntm.occursIn_rename (ρ : Equiv.Perm 𝔸) (x : X) (t : ntm F X 𝔸) :
      (t.rename ρ).occursIn x = t.occursIn x := by
    match t with
    | .atm _ | .mvar _ _ => simp [ntm.occursIn]
    | .fapp _ ts =>
      simp only [ntm.rename_fapp, ntm.occursIn]
      exact ntmList.occursIn_rename ρ x ts
    | .abs _ t =>
      simp only [ntm.rename_abs, ntm.occursIn]
      exact ntm.occursIn_rename ρ x t

  lemma ntmList.occursIn_rename (ρ : Equiv.Perm 𝔸) (x : X) (ts : List (ntm F X 𝔸)) :
      ntmList.occursIn x (ts.map (ntm.rename ρ)) = ntmList.occursIn x ts := by
    match ts with
    | [] => simp [ntmList.occursIn]
    | t :: ts =>
      simp only [List.map_cons, ntmList.occursIn, ntm.occursIn_rename ρ x t,
        ntmList.occursIn_rename ρ x ts]
end

/-! ### One step -/

theorem unifStep_rename (ρ : Equiv.Perm 𝔸) (c : UnifConstraint F X 𝔸)
    (rest : UnifProblem F X 𝔸) (σ : Subst F X 𝔸) :
    unifStep (c.rename ρ) (UnifProblem.rename ρ rest) (Subst.rename ρ σ) = (unifStep c rest σ).rename ρ := by
  cases c with
  | fresh a t =>
    by_cases ht : ∃ π x, t = .mvar π x
    · obtain ⟨π, x, rfl⟩ := ht
      simp [unifStep, UnifConstraint.rename, StepResult.rename, LPermApply_rename]
    · push_neg at ht
      have ht' : ∀ π x, t.rename ρ ≠ .mvar π x := by
        intro π x h
        cases t with
        | mvar π' x' => exact ht π' x' rfl
        | _ => simp at h
      simp only [UnifConstraint.rename]
      rw [unifStep_fresh_of_not_mvar _ _ _ _ ht', unifStep_fresh_of_not_mvar _ _ _ _ ht,
        simplifyFresh_rename]
      cases simplifyFresh a t with
      | none => rfl
      | some cs =>
        simp [StepResult.rename, UnifProblem.rename, Problem.rename, Function.comp_def,
          Constraint.toUnif_rename]
  | unif s t =>
    cases s <;> cases t <;>
      simp only [unifStep, UnifConstraint.rename, ntm.rename_atm, ntm.rename_mvar,
        ntm.rename_fapp, ntm.rename_abs, EmbeddingLike.apply_eq_iff_eq, List.length_map,
        ntm.occursIn, ntm.occursIn_rename, ntmList.occursIn_rename] <;>
      (try split_ifs) <;>
      simp_all [StepResult.rename, map_rename_applySubst, Subst.rename_comp,
        ntm.rename_permute, dsList_rename, UnifProblem.rename, UnifConstraint.rename,
        List.zip_map, Function.comp_def]

/-! ### The loop -/

theorem unify_rename (ρ : Equiv.Perm 𝔸) (Pr : UnifProblem F X 𝔸) (σ : Subst F X 𝔸)
    (D : List (𝔸 × X)) :
    unify (Pr.rename ρ) (Subst.rename ρ σ) (deferredRename ρ D)
      = (unify Pr σ D).map fun r => (deferredRename ρ r.1, Subst.rename ρ r.2) := by
  fun_induction unify Pr σ D with
  | case1 σ D => simp [unify]
  | case2 σ D c rest h =>
    have e : unifStep (c.rename ρ) (UnifProblem.rename ρ rest) (Subst.rename ρ σ) = .fail := by
      rw [unifStep_rename, h]; rfl
    rw [UnifProblem.rename_cons, unify]
    split <;> simp_all
  | case3 σ D c rest a x h ih =>
    have e : unifStep (c.rename ρ) (UnifProblem.rename ρ rest) (Subst.rename ρ σ) = .ctx (ρ a) x := by
      rw [unifStep_rename, h]; rfl
    rw [UnifProblem.rename_cons, unify]
    split
    · simp_all
    · rename_i a' x' h'
      rw [e] at h'
      cases h'
      rw [← ih]
      rfl
    · simp_all
  | case4 σ D c rest Pr' σ' h ih =>
    have e : unifStep (c.rename ρ) (UnifProblem.rename ρ rest) (Subst.rename ρ σ)
        = .next (Pr'.rename ρ) (Subst.rename ρ σ') := by
      rw [unifStep_rename, h]; rfl
    rw [UnifProblem.rename_cons, unify]
    split
    · simp_all
    · simp_all
    · rename_i Pr'' σ'' h'
      rw [e] at h'
      cases h'
      exact ih

/-! ### The second stage -/

lemma finalizeDeferred_cons (a : 𝔸) (x : X) (tl : List (𝔸 × X)) (σ : Subst F X 𝔸)
    (Γ : Context 𝔸 X) :
    finalizeDeferred ((a, x) :: tl) σ Γ =
      match simplifyFresh a ((ntm.mvar (F := F) [] x).subst σ) with
      | none    => none
      | some cs => finalizeDeferred tl σ (cs.foldl ctxStep Γ) := by
  rw [finalizeDeferred]; rfl

lemma ctxStep_rename (ρ : Equiv.Perm 𝔸) (Γ : Context 𝔸 X) (c : Constraint F X 𝔸) :
    ctxStep (Context.rename ρ Γ) (c.rename ρ) = Context.rename ρ (ctxStep Γ c) := by
  rcases c with ⟨a, t⟩ | ⟨s, t⟩
  · cases t with
    | mvar π x => cases π <;> simp [ctxStep, Constraint.rename]
    | _ => simp [ctxStep, Constraint.rename]
  · simp [ctxStep, Constraint.rename]

lemma foldl_ctxStep_rename (ρ : Equiv.Perm 𝔸) (cs : Problem F X 𝔸) (Γ : Context 𝔸 X) :
    (Problem.rename ρ cs).foldl ctxStep (Context.rename ρ Γ)
      = Context.rename ρ (cs.foldl ctxStep Γ) := by
  induction cs generalizing Γ with
  | nil => rfl
  | cons c cs ih =>
    simp only [Problem.rename, List.map_cons, List.foldl_cons] at ih ⊢
    rw [ctxStep_rename, ih]

theorem finalizeDeferred_rename (ρ : Equiv.Perm 𝔸) (D : List (𝔸 × X)) (σ : Subst F X 𝔸)
    (Γ : Context 𝔸 X) :
    finalizeDeferred (deferredRename ρ D) (Subst.rename ρ σ) (Context.rename ρ Γ)
      = (finalizeDeferred D σ Γ).map (Context.rename ρ) := by
  induction D generalizing Γ with
  | nil => simp [deferredRename, finalizeDeferred]
  | cons p D ih =>
    obtain ⟨a, x⟩ := p
    simp only [deferredRename, List.map_cons] at ih ⊢
    rw [finalizeDeferred_cons, finalizeDeferred_cons, ntm.subst_mvar_nil_rename,
      simplifyFresh_rename]
    cases simplifyFresh a ((ntm.mvar (F := F) [] x).subst σ) with
    | none => rfl
    | some cs =>
      simp only [Option.map_some]
      rw [foldl_ctxStep_rename, ih]

/-! ### Main results -/

/-- **Equivariance of the algorithm.** Renaming the atoms of a problem renames the computed
    most general unifier, and preserves failure. -/
theorem UnifProblem.solve_rename (ρ : Equiv.Perm 𝔸) (Pr : UnifProblem F X 𝔸) :
    (Pr.rename ρ).solve = Pr.solve.map fun r => (Context.rename ρ r.1, Subst.rename ρ r.2) := by
  have hu := unify_rename ρ Pr [] []
  simp only [Subst.rename_nil, deferredRename, List.map_nil] at hu
  unfold UnifProblem.solve
  rw [hu]
  cases unify Pr [] [] with
  | none => rfl
  | some r =>
    obtain ⟨D, σ⟩ := r
    have hf := finalizeDeferred_rename ρ D σ ∅
    simp only [Context.rename_empty, deferredRename] at hf
    simp only [Option.map_some]
    rw [hf]
    cases finalizeDeferred D σ ∅ <;> rfl

lemma UnifProblem.toConstraint_rename_applySubst (ρ : Equiv.Perm 𝔸) (Pr : UnifProblem F X 𝔸)
    (σ : Subst F X 𝔸) :
    ((Pr.rename ρ).applySubst (Subst.rename ρ σ)).toConstraint
      = Problem.rename ρ (Pr.applySubst σ).toConstraint := by
  rw [← UnifProblem.rename_applySubst]
  simp [UnifProblem.toConstraint, UnifProblem.rename, Problem.rename, Function.comp_def,
    UnifConstraint.toConstraint_rename]

/-- **Equivariance of the solution set.** -/
theorem UnifProblem.mem_solutions_rename (ρ : Equiv.Perm 𝔸) (Pr : UnifProblem F X 𝔸)
    (Γ : Context 𝔸 X) (σ : Subst F X 𝔸) :
    (Context.rename ρ Γ, Subst.rename ρ σ) ∈ (Pr.rename ρ).Solutions ↔ (Γ, σ) ∈ Pr.Solutions := by
  simp only [UnifProblem.Solutions, Set.mem_setOf_eq, Solution.Satisfies,
    UnifProblem.toConstraint_rename_applySubst, Problem.entails_rename,
    Subst.isIdempotent_rename_iff]

end Nominal
