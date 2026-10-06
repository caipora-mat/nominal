import Nominal.Syntax.Unification.Equivariance
import Nominal.Syntax.RenameVar

/-!
# Equivariance of the unification algorithm in metavariables

Renaming the metavariables of a problem by any bijection `τ` renames its output accordingly:

  `(Pr.renameVar τ).solve = Pr.solve.map (renameVar τ)`

The algorithm only compares metavariables for equality, so it treats unknowns uniformly. Together
with `UnifProblem.solve_rename`, this covers the freshening of rewrite rules, which renames both
their atoms and their unknowns (Fernández–Gabbay, *Nominal rewriting*, Lemma 69).
-/

namespace Nominal

open Core

variable {F X 𝔸 : Type*} [DecidableEq F] [DecidableEq X] [Name 𝔸]

/-! ### Renaming problems, results and deferred lists -/

def UnifConstraint.renameVar (τ : Equiv.Perm X) : UnifConstraint F X 𝔸 → UnifConstraint F X 𝔸
  | .fresh a t => .fresh a (t.renameVar τ)
  | .unif s t  => .unif (s.renameVar τ) (t.renameVar τ)

def UnifProblem.renameVar (τ : Equiv.Perm X) (Pr : UnifProblem F X 𝔸) : UnifProblem F X 𝔸 :=
  Pr.map (UnifConstraint.renameVar τ)

/-- Renaming of a list of deferred obligations `a # X`. -/
def deferredRenameVar (τ : Equiv.Perm X) (D : List (𝔸 × X)) : List (𝔸 × X) :=
  D.map fun p => (p.1, τ p.2)

def StepResult.renameVar (τ : Equiv.Perm X) : StepResult F X 𝔸 → StepResult F X 𝔸
  | .fail      => .fail
  | .ctx a x   => .ctx a (τ x)
  | .next Pr σ => .next (Pr.renameVar τ) (Subst.renameVar τ σ)

@[simp] lemma UnifProblem.renameVar_cons (τ : Equiv.Perm X) (c : UnifConstraint F X 𝔸)
    (Pr : UnifProblem F X 𝔸) :
    UnifProblem.renameVar τ (c :: Pr) = c.renameVar τ :: Pr.renameVar τ := rfl

lemma UnifProblem.renameVar_applySubst (τ : Equiv.Perm X) (Pr : UnifProblem F X 𝔸)
    (σ : Subst F X 𝔸) :
    (Pr.applySubst σ).renameVar τ = (Pr.renameVar τ).applySubst (Subst.renameVar τ σ) := by
  simp only [UnifProblem.applySubst, UnifProblem.renameVar, List.map_map]
  apply List.map_congr_left
  intro c _
  cases c <;> simp [UnifConstraint.applySubst, UnifConstraint.renameVar, ntm.renameVar_subst]

/-- `UnifProblem.renameVar_applySubst` with the renaming unfolded to `List.map`. -/
lemma map_renameVar_applySubst (τ : Equiv.Perm X) (Pr : UnifProblem F X 𝔸)
    (σ : Subst F X 𝔸) :
    (Pr.applySubst σ).map (UnifConstraint.renameVar τ)
      = UnifProblem.applySubst (Pr.map (UnifConstraint.renameVar τ)) (Subst.renameVar τ σ) :=
  UnifProblem.renameVar_applySubst τ Pr σ

lemma Constraint.toUnif_renameVar (τ : Equiv.Perm X) (c : Constraint F X 𝔸) :
    (c.renameVar τ).toUnif = c.toUnif.renameVar τ := by
  cases c <;> rfl

lemma UnifConstraint.toConstraint_renameVar (τ : Equiv.Perm X) (c : UnifConstraint F X 𝔸) :
    (c.renameVar τ).toConstraint = c.toConstraint.renameVar τ := by
  cases c <;> rfl

mutual
  lemma ntm.occursIn_renameVar (τ : Equiv.Perm X) (x : X) (t : ntm F X 𝔸) :
      (t.renameVar τ).occursIn (τ x) = t.occursIn x := by
    match t with
    | .atm _ => simp [ntm.occursIn]
    | .mvar _ _ => simp [ntm.occursIn]
    | .fapp _ ts =>
      simp only [ntm.renameVar_fapp, ntm.occursIn]
      exact ntmList.occursIn_renameVar τ x ts
    | .abs _ t =>
      simp only [ntm.renameVar_abs, ntm.occursIn]
      exact ntm.occursIn_renameVar τ x t

  lemma ntmList.occursIn_renameVar (τ : Equiv.Perm X) (x : X) (ts : List (ntm F X 𝔸)) :
      ntmList.occursIn (τ x) (ts.map (ntm.renameVar τ)) = ntmList.occursIn x ts := by
    match ts with
    | [] => simp [ntmList.occursIn]
    | t :: ts =>
      simp only [List.map_cons, ntmList.occursIn, ntm.occursIn_renameVar τ x t,
        ntmList.occursIn_renameVar τ x ts]
end

/-! ### One step -/

theorem unifStep_renameVar (τ : Equiv.Perm X) (c : UnifConstraint F X 𝔸)
    (rest : UnifProblem F X 𝔸) (σ : Subst F X 𝔸) :
    unifStep (c.renameVar τ) (UnifProblem.renameVar τ rest) (Subst.renameVar τ σ)
      = (unifStep c rest σ).renameVar τ := by
  cases c with
  | fresh a t =>
    by_cases ht : ∃ π x, t = .mvar π x
    · obtain ⟨π, x, rfl⟩ := ht
      simp [unifStep, UnifConstraint.renameVar, StepResult.renameVar]
    · push_neg at ht
      have ht' : ∀ π x, t.renameVar τ ≠ .mvar π x := by
        intro π x h
        cases t with
        | mvar π' x' => exact ht π' x' rfl
        | _ => simp at h
      simp only [UnifConstraint.renameVar]
      rw [unifStep_fresh_of_not_mvar _ _ _ _ ht', unifStep_fresh_of_not_mvar _ _ _ _ ht,
        simplifyFresh_renameVar]
      cases simplifyFresh a t with
      | none => rfl
      | some cs =>
        simp [StepResult.renameVar, UnifProblem.renameVar, Problem.renameVar, Function.comp_def,
          Constraint.toUnif_renameVar]
  | unif s t =>
    cases s <;> cases t <;>
      simp only [unifStep, UnifConstraint.renameVar, ntm.renameVar_atm, ntm.renameVar_mvar,
        ntm.renameVar_fapp, ntm.renameVar_abs, EmbeddingLike.apply_eq_iff_eq, List.length_map,
        ntm.occursIn, ntm.occursIn_renameVar, ntmList.occursIn_renameVar] <;>
      (try split_ifs) <;>
      simp_all [StepResult.renameVar, map_renameVar_applySubst, Subst.renameVar_comp,
        ntm.renameVar_permute, UnifProblem.renameVar, UnifConstraint.renameVar,
        List.zip_map, Function.comp_def]

/-! ### The loop -/

theorem unify_renameVar (τ : Equiv.Perm X) (Pr : UnifProblem F X 𝔸) (σ : Subst F X 𝔸)
    (D : List (𝔸 × X)) :
    unify (Pr.renameVar τ) (Subst.renameVar τ σ) (deferredRenameVar τ D)
      = (unify Pr σ D).map fun r => (deferredRenameVar τ r.1, Subst.renameVar τ r.2) := by
  fun_induction unify Pr σ D with
  | case1 σ D => simp [unify, UnifProblem.renameVar]
  | case2 σ D c rest h =>
    have e : unifStep (c.renameVar τ) (UnifProblem.renameVar τ rest) (Subst.renameVar τ σ)
        = .fail := by
      rw [unifStep_renameVar, h]; rfl
    rw [UnifProblem.renameVar_cons, unify]
    split <;> simp_all
  | case3 σ D c rest a x h ih =>
    have e : unifStep (c.renameVar τ) (UnifProblem.renameVar τ rest) (Subst.renameVar τ σ)
        = .ctx a (τ x) := by
      rw [unifStep_renameVar, h]; rfl
    rw [UnifProblem.renameVar_cons, unify]
    split
    · simp_all
    · rename_i a' x' h'
      rw [e] at h'
      cases h'
      rw [← ih]
      rfl
    · simp_all
  | case4 σ D c rest Pr' σ' h ih =>
    have e : unifStep (c.renameVar τ) (UnifProblem.renameVar τ rest) (Subst.renameVar τ σ)
        = .next (Pr'.renameVar τ) (Subst.renameVar τ σ') := by
      rw [unifStep_renameVar, h]; rfl
    rw [UnifProblem.renameVar_cons, unify]
    split
    · simp_all
    · simp_all
    · rename_i Pr'' σ'' h'
      rw [e] at h'
      cases h'
      exact ih

/-! ### The second stage -/

lemma ctxStep_renameVar (τ : Equiv.Perm X) (Γ : Context 𝔸 X) (c : Constraint F X 𝔸) :
    ctxStep (Context.renameVar τ Γ) (c.renameVar τ) = Context.renameVar τ (ctxStep Γ c) := by
  rcases c with ⟨a, t⟩ | ⟨s, t⟩
  · cases t with
    | mvar π x => cases π <;> simp [ctxStep, Constraint.renameVar]
    | _ => simp [ctxStep, Constraint.renameVar]
  · simp [ctxStep, Constraint.renameVar]

lemma foldl_ctxStep_renameVar (τ : Equiv.Perm X) (cs : Problem F X 𝔸) (Γ : Context 𝔸 X) :
    (Problem.renameVar τ cs).foldl ctxStep (Context.renameVar τ Γ)
      = Context.renameVar τ (cs.foldl ctxStep Γ) := by
  induction cs generalizing Γ with
  | nil => rfl
  | cons c cs ih =>
    simp only [Problem.renameVar, List.map_cons, List.foldl_cons] at ih ⊢
    rw [ctxStep_renameVar, ih]

theorem finalizeDeferred_renameVar (τ : Equiv.Perm X) (D : List (𝔸 × X)) (σ : Subst F X 𝔸)
    (Γ : Context 𝔸 X) :
    finalizeDeferred (deferredRenameVar τ D) (Subst.renameVar τ σ) (Context.renameVar τ Γ)
      = (finalizeDeferred D σ Γ).map (Context.renameVar τ) := by
  induction D generalizing Γ with
  | nil => simp [deferredRenameVar, finalizeDeferred]
  | cons p D ih =>
    obtain ⟨a, x⟩ := p
    simp only [deferredRenameVar, List.map_cons] at ih ⊢
    rw [finalizeDeferred_cons, finalizeDeferred_cons, ntm.subst_mvar_nil_renameVar,
      simplifyFresh_renameVar]
    cases simplifyFresh a ((ntm.mvar (F := F) [] x).subst σ) with
    | none => rfl
    | some cs =>
      simp only [Option.map_some]
      rw [foldl_ctxStep_renameVar, ih]

/-! ### Main results -/

/-- **Equivariance in metavariables.** Renaming the unknowns of a problem renames the computed
    most general unifier, and preserves failure. -/
theorem UnifProblem.solve_renameVar (τ : Equiv.Perm X) (Pr : UnifProblem F X 𝔸) :
    (Pr.renameVar τ).solve
      = Pr.solve.map fun r => (Context.renameVar τ r.1, Subst.renameVar τ r.2) := by
  have hu := unify_renameVar τ Pr [] []
  simp only [Subst.renameVar_nil, deferredRenameVar, List.map_nil] at hu
  unfold UnifProblem.solve
  rw [hu]
  cases unify Pr [] [] with
  | none => rfl
  | some r =>
    obtain ⟨D, σ⟩ := r
    have hf := finalizeDeferred_renameVar τ D σ ∅
    simp only [Context.renameVar_empty, deferredRenameVar] at hf
    simp only [Option.map_some]
    rw [hf]
    cases finalizeDeferred D σ ∅ <;> rfl

lemma UnifProblem.toConstraint_renameVar_applySubst (τ : Equiv.Perm X)
    (Pr : UnifProblem F X 𝔸) (σ : Subst F X 𝔸) :
    ((Pr.renameVar τ).applySubst (Subst.renameVar τ σ)).toConstraint
      = Problem.renameVar τ (Pr.applySubst σ).toConstraint := by
  rw [← UnifProblem.renameVar_applySubst]
  simp [UnifProblem.toConstraint, UnifProblem.renameVar, Problem.renameVar, Function.comp_def,
    UnifConstraint.toConstraint_renameVar]

/-- **Equivariance of the solution set in metavariables.** -/
theorem UnifProblem.mem_solutions_renameVar (τ : Equiv.Perm X) (Pr : UnifProblem F X 𝔸)
    (Γ : Context 𝔸 X) (σ : Subst F X 𝔸) :
    (Context.renameVar τ Γ, Subst.renameVar τ σ) ∈ (Pr.renameVar τ).Solutions
      ↔ (Γ, σ) ∈ Pr.Solutions := by
  simp only [UnifProblem.Solutions, Set.mem_setOf_eq, Solution.Satisfies,
    UnifProblem.toConstraint_renameVar_applySubst, Problem.entails_renameVar,
    Subst.isIdempotent_renameVar_iff]

/-! ### Renaming atoms and unknowns together -/

/-- **Freshening.** Renaming both the atoms (by `ρ`) and the unknowns (by `τ`) of a problem, as
    when a rewrite rule is freshened (Fernández–Gabbay, *Nominal rewriting*, Lemma 69), renames
    the computed most general unifier in the same way, and preserves failure. -/
theorem UnifProblem.solve_rename_renameVar (ρ : Equiv.Perm 𝔸) (τ : Equiv.Perm X)
    (Pr : UnifProblem F X 𝔸) :
    ((Pr.rename ρ).renameVar τ).solve
      = Pr.solve.map fun r =>
          (Context.renameVar τ (Context.rename ρ r.1), Subst.renameVar τ (Subst.rename ρ r.2)) := by
  rw [UnifProblem.solve_renameVar, UnifProblem.solve_rename, Option.map_map]
  rfl

/-- The solution set is preserved by renaming atoms and unknowns together. -/
theorem UnifProblem.mem_solutions_rename_renameVar (ρ : Equiv.Perm 𝔸) (τ : Equiv.Perm X)
    (Pr : UnifProblem F X 𝔸) (Γ : Context 𝔸 X) (σ : Subst F X 𝔸) :
    (Context.renameVar τ (Context.rename ρ Γ), Subst.renameVar τ (Subst.rename ρ σ))
        ∈ ((Pr.rename ρ).renameVar τ).Solutions
      ↔ (Γ, σ) ∈ Pr.Solutions := by
  rw [UnifProblem.mem_solutions_renameVar, UnifProblem.mem_solutions_rename]

end Nominal
