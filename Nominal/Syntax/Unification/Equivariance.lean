import Nominal.Syntax.Unification.Algorithm
import Nominal.Syntax.Rename

/-!
# Equivariance of the unification algorithm

Renaming the atoms of a problem by any bijection `ρ`, and its metavariables by any bijection
`τ`, renames its output accordingly:

  `(Pr.relabel ρ τ).solve = Pr.solve.map (relabel ρ τ)`

This is an exact equation: the algorithm only ever compares atoms and metavariables for
equality, so it treats names and unknowns uniformly. Correspondingly, the set of solutions is
equivariant (`UnifProblem.mem_solutions_relabel`).

The cases `τ = 1` (`UnifProblem.solve_rename`) and `ρ = 1` (`UnifProblem.solve_renameVar`) are
stated separately. Together they cover the freshening of rewrite rules, which renames both
their atoms and their unknowns (Fernández–Gabbay, *Nominal rewriting*, Lemma 69).
-/

namespace Nominal

open Core

variable {F X 𝔸 : Type*} [DecidableEq F] [DecidableEq X] [Name 𝔸]

/-! ### Relabelling problems, results and deferred lists -/

def UnifConstraint.relabel (ρ : Equiv.Perm 𝔸) (τ : Equiv.Perm X) : UnifConstraint F X 𝔸 → UnifConstraint F X 𝔸
  | .fresh a t => .fresh (ρ a) (t.relabel ρ τ)
  | .unif s t  => .unif (s.relabel ρ τ) (t.relabel ρ τ)

def UnifProblem.relabel (ρ : Equiv.Perm 𝔸) (τ : Equiv.Perm X) (Pr : UnifProblem F X 𝔸) : UnifProblem F X 𝔸 :=
  Pr.map (UnifConstraint.relabel ρ τ)

/-- Relabelling of a list of deferred obligations `a # X`. -/
def deferredRelabel (ρ : Equiv.Perm 𝔸) (τ : Equiv.Perm X) (D : List (𝔸 × X)) : List (𝔸 × X) :=
  D.map fun p => (ρ p.1, τ p.2)

def StepResult.relabel (ρ : Equiv.Perm 𝔸) (τ : Equiv.Perm X) : StepResult F X 𝔸 → StepResult F X 𝔸
  | .fail      => .fail
  | .ctx a x   => .ctx (ρ a) (τ x)
  | .next Pr σ => .next (Pr.relabel ρ τ) (Subst.relabel ρ τ σ)

@[simp] lemma UnifProblem.relabel_nil (ρ : Equiv.Perm 𝔸) (τ : Equiv.Perm X) :
    UnifProblem.relabel ρ τ ([] : UnifProblem F X 𝔸) = [] := rfl

@[simp] lemma UnifProblem.relabel_cons (ρ : Equiv.Perm 𝔸) (τ : Equiv.Perm X) (c : UnifConstraint F X 𝔸)
    (Pr : UnifProblem F X 𝔸) :
    UnifProblem.relabel ρ τ (c :: Pr) = c.relabel ρ τ :: Pr.relabel ρ τ := rfl

@[simp] lemma UnifProblem.relabel_append (ρ : Equiv.Perm 𝔸) (τ : Equiv.Perm X) (Pr Pr' : UnifProblem F X 𝔸) :
    UnifProblem.relabel ρ τ (Pr ++ Pr') = Pr.relabel ρ τ ++ Pr'.relabel ρ τ := by
  simp [UnifProblem.relabel]

lemma UnifProblem.relabel_applySubst (ρ : Equiv.Perm 𝔸) (τ : Equiv.Perm X) (Pr : UnifProblem F X 𝔸)
    (σ : Subst F X 𝔸) :
    (Pr.applySubst σ).relabel ρ τ = (Pr.relabel ρ τ).applySubst (Subst.relabel ρ τ σ) := by
  simp only [UnifProblem.applySubst, UnifProblem.relabel, List.map_map]
  apply List.map_congr_left
  intro c _
  cases c <;> simp [UnifConstraint.applySubst, UnifConstraint.relabel, ntm.relabel_subst]

/-- `UnifProblem.relabel_applySubst` with the relabelling unfolded to `List.map`. -/
lemma map_relabel_applySubst (ρ : Equiv.Perm 𝔸) (τ : Equiv.Perm X) (Pr : UnifProblem F X 𝔸) (σ : Subst F X 𝔸) :
    (Pr.applySubst σ).map (UnifConstraint.relabel ρ τ)
      = UnifProblem.applySubst (Pr.map (UnifConstraint.relabel ρ τ)) (Subst.relabel ρ τ σ) :=
  UnifProblem.relabel_applySubst ρ τ Pr σ

lemma Constraint.toUnif_relabel (ρ : Equiv.Perm 𝔸) (τ : Equiv.Perm X) (c : Constraint F X 𝔸) :
    (c.relabel ρ τ).toUnif = c.toUnif.relabel ρ τ := by
  cases c <;> rfl

lemma UnifConstraint.toConstraint_relabel (ρ : Equiv.Perm 𝔸) (τ : Equiv.Perm X) (c : UnifConstraint F X 𝔸) :
    (c.relabel ρ τ).toConstraint = c.toConstraint.relabel ρ τ := by
  cases c <;> rfl

mutual
  lemma ntm.occursIn_relabel (ρ : Equiv.Perm 𝔸) (τ : Equiv.Perm X) (x : X) (t : ntm F X 𝔸) :
      (t.relabel ρ τ).occursIn (τ x) = t.occursIn x := by
    match t with
    | .atm _ | .mvar _ _ => simp [ntm.occursIn]
    | .fapp _ ts =>
      simp only [ntm.relabel_fapp, ntm.occursIn]
      exact ntmList.occursIn_relabel ρ τ x ts
    | .abs _ t =>
      simp only [ntm.relabel_abs, ntm.occursIn]
      exact ntm.occursIn_relabel ρ τ x t

  lemma ntmList.occursIn_relabel (ρ : Equiv.Perm 𝔸) (τ : Equiv.Perm X) (x : X) (ts : List (ntm F X 𝔸)) :
      ntmList.occursIn (τ x) (ts.map (ntm.relabel ρ τ)) = ntmList.occursIn x ts := by
    match ts with
    | [] => simp [ntmList.occursIn]
    | t :: ts =>
      simp only [List.map_cons, ntmList.occursIn, ntm.occursIn_relabel ρ τ x t,
        ntmList.occursIn_relabel ρ τ x ts]
end

/-! ### One step -/

theorem unifStep_relabel (ρ : Equiv.Perm 𝔸) (τ : Equiv.Perm X) (c : UnifConstraint F X 𝔸)
    (rest : UnifProblem F X 𝔸) (σ : Subst F X 𝔸) :
    unifStep (c.relabel ρ τ) (UnifProblem.relabel ρ τ rest) (Subst.relabel ρ τ σ) = (unifStep c rest σ).relabel ρ τ := by
  cases c with
  | fresh a t =>
    by_cases ht : ∃ π x, t = .mvar π x
    · obtain ⟨π, x, rfl⟩ := ht
      simp [unifStep, UnifConstraint.relabel, StepResult.relabel, LPermApply_rename]
    · push_neg at ht
      have ht' : ∀ π x, t.relabel ρ τ ≠ .mvar π x := by
        intro π x h
        cases t with
        | mvar π' x' => exact ht π' x' rfl
        | _ => simp at h
      simp only [UnifConstraint.relabel]
      rw [unifStep_fresh_of_not_mvar _ _ _ _ ht', unifStep_fresh_of_not_mvar _ _ _ _ ht,
        simplifyFresh_relabel]
      cases simplifyFresh a t with
      | none => rfl
      | some cs =>
        simp [StepResult.relabel, UnifProblem.relabel, Problem.relabel, Function.comp_def,
          Constraint.toUnif_relabel]
  | unif s t =>
    cases s <;> cases t <;>
      simp only [unifStep, UnifConstraint.relabel, ntm.relabel_atm, ntm.relabel_mvar,
        ntm.relabel_fapp, ntm.relabel_abs, EmbeddingLike.apply_eq_iff_eq, List.length_map,
        ntm.occursIn, ntm.occursIn_relabel, ntmList.occursIn_relabel] <;>
      (try split_ifs) <;>
      simp_all [StepResult.relabel, map_relabel_applySubst, Subst.relabel_comp,
        ntm.relabel_permute, dsList_rename, UnifProblem.relabel, UnifConstraint.relabel,
        List.zip_map, Function.comp_def]

/-! ### The loop -/

theorem unify_relabel (ρ : Equiv.Perm 𝔸) (τ : Equiv.Perm X) (Pr : UnifProblem F X 𝔸) (σ : Subst F X 𝔸)
    (D : List (𝔸 × X)) :
    unify (Pr.relabel ρ τ) (Subst.relabel ρ τ σ) (deferredRelabel ρ τ D)
      = (unify Pr σ D).map fun r => (deferredRelabel ρ τ r.1, Subst.relabel ρ τ r.2) := by
  fun_induction unify Pr σ D with
  | case1 σ D => simp [unify]
  | case2 σ D c rest h =>
    have e : unifStep (c.relabel ρ τ) (UnifProblem.relabel ρ τ rest) (Subst.relabel ρ τ σ) = .fail := by
      rw [unifStep_relabel, h]; rfl
    rw [UnifProblem.relabel_cons, unify]
    split <;> simp_all
  | case3 σ D c rest a x h ih =>
    have e : unifStep (c.relabel ρ τ) (UnifProblem.relabel ρ τ rest) (Subst.relabel ρ τ σ) = .ctx (ρ a) (τ x) := by
      rw [unifStep_relabel, h]; rfl
    rw [UnifProblem.relabel_cons, unify]
    split
    · simp_all
    · rename_i a' x' h'
      rw [e] at h'
      cases h'
      rw [← ih]
      rfl
    · simp_all
  | case4 σ D c rest Pr' σ' h ih =>
    have e : unifStep (c.relabel ρ τ) (UnifProblem.relabel ρ τ rest) (Subst.relabel ρ τ σ)
        = .next (Pr'.relabel ρ τ) (Subst.relabel ρ τ σ') := by
      rw [unifStep_relabel, h]; rfl
    rw [UnifProblem.relabel_cons, unify]
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

lemma ctxStep_relabel (ρ : Equiv.Perm 𝔸) (τ : Equiv.Perm X) (Γ : Context 𝔸 X) (c : Constraint F X 𝔸) :
    ctxStep (Context.relabel ρ τ Γ) (c.relabel ρ τ) = Context.relabel ρ τ (ctxStep Γ c) := by
  rcases c with ⟨a, t⟩ | ⟨s, t⟩
  · cases t with
    | mvar π x => cases π <;> simp [ctxStep, Constraint.relabel]
    | _ => simp [ctxStep, Constraint.relabel]
  · simp [ctxStep, Constraint.relabel]

lemma foldl_ctxStep_relabel (ρ : Equiv.Perm 𝔸) (τ : Equiv.Perm X) (cs : Problem F X 𝔸) (Γ : Context 𝔸 X) :
    (Problem.relabel ρ τ cs).foldl ctxStep (Context.relabel ρ τ Γ)
      = Context.relabel ρ τ (cs.foldl ctxStep Γ) := by
  induction cs generalizing Γ with
  | nil => rfl
  | cons c cs ih =>
    simp only [Problem.relabel, List.map_cons, List.foldl_cons] at ih ⊢
    rw [ctxStep_relabel, ih]

theorem finalizeDeferred_relabel (ρ : Equiv.Perm 𝔸) (τ : Equiv.Perm X) (D : List (𝔸 × X)) (σ : Subst F X 𝔸)
    (Γ : Context 𝔸 X) :
    finalizeDeferred (deferredRelabel ρ τ D) (Subst.relabel ρ τ σ) (Context.relabel ρ τ Γ)
      = (finalizeDeferred D σ Γ).map (Context.relabel ρ τ) := by
  induction D generalizing Γ with
  | nil => simp [deferredRelabel, finalizeDeferred]
  | cons p D ih =>
    obtain ⟨a, x⟩ := p
    simp only [deferredRelabel, List.map_cons] at ih ⊢
    rw [finalizeDeferred_cons, finalizeDeferred_cons, ntm.subst_mvar_nil_relabel,
      simplifyFresh_relabel]
    cases simplifyFresh a ((ntm.mvar (F := F) [] x).subst σ) with
    | none => rfl
    | some cs =>
      simp only [Option.map_some]
      rw [foldl_ctxStep_relabel, ih]

/-! ### Main results -/

/-- **Equivariance of the algorithm.** Relabelling the atoms and the unknowns of a problem
    relabels the computed most general unifier, and preserves failure. -/
theorem UnifProblem.solve_relabel (ρ : Equiv.Perm 𝔸) (τ : Equiv.Perm X)
    (Pr : UnifProblem F X 𝔸) :
    (Pr.relabel ρ τ).solve
      = Pr.solve.map fun r => (Context.relabel ρ τ r.1, Subst.relabel ρ τ r.2) := by
  have hu := unify_relabel ρ τ Pr [] []
  simp only [Subst.relabel_nil, deferredRelabel, List.map_nil] at hu
  unfold UnifProblem.solve
  rw [hu]
  cases unify Pr [] [] with
  | none => rfl
  | some r =>
    obtain ⟨D, σ⟩ := r
    have hf := finalizeDeferred_relabel ρ τ D σ ∅
    simp only [Context.relabel_empty, deferredRelabel] at hf
    simp only [Option.map_some]
    rw [hf]
    cases finalizeDeferred D σ ∅ <;> rfl

lemma UnifProblem.toConstraint_relabel_applySubst (ρ : Equiv.Perm 𝔸) (τ : Equiv.Perm X)
    (Pr : UnifProblem F X 𝔸) (σ : Subst F X 𝔸) :
    ((Pr.relabel ρ τ).applySubst (Subst.relabel ρ τ σ)).toConstraint
      = Problem.relabel ρ τ (Pr.applySubst σ).toConstraint := by
  rw [← UnifProblem.relabel_applySubst]
  simp [UnifProblem.toConstraint, UnifProblem.relabel, Problem.relabel, Function.comp_def,
    UnifConstraint.toConstraint_relabel]

/-- **Equivariance of the solution set.** -/
theorem UnifProblem.mem_solutions_relabel (ρ : Equiv.Perm 𝔸) (τ : Equiv.Perm X)
    (Pr : UnifProblem F X 𝔸) (Γ : Context 𝔸 X) (σ : Subst F X 𝔸) :
    (Context.relabel ρ τ Γ, Subst.relabel ρ τ σ) ∈ (Pr.relabel ρ τ).Solutions
      ↔ (Γ, σ) ∈ Pr.Solutions := by
  simp only [UnifProblem.Solutions, Set.mem_setOf_eq, Solution.Satisfies,
    UnifProblem.toConstraint_relabel_applySubst, Problem.entails_relabel,
    Subst.isIdempotent_relabel_iff]

/-! ### Renaming atoms only, or metavariables only -/

abbrev UnifConstraint.rename (ρ : Equiv.Perm 𝔸) : UnifConstraint F X 𝔸 → UnifConstraint F X 𝔸 :=
  UnifConstraint.relabel ρ 1

abbrev UnifProblem.rename (ρ : Equiv.Perm 𝔸) : UnifProblem F X 𝔸 → UnifProblem F X 𝔸 :=
  UnifProblem.relabel ρ 1

abbrev UnifProblem.renameVar (τ : Equiv.Perm X) : UnifProblem F X 𝔸 → UnifProblem F X 𝔸 :=
  UnifProblem.relabel 1 τ

/-- **Equivariance in atoms.** Renaming the atoms of a problem renames the computed most
    general unifier, and preserves failure. -/
theorem UnifProblem.solve_rename (ρ : Equiv.Perm 𝔸) (Pr : UnifProblem F X 𝔸) :
    (Pr.rename ρ).solve = Pr.solve.map fun r => (Context.rename ρ r.1, Subst.rename ρ r.2) :=
  UnifProblem.solve_relabel ρ 1 Pr

/-- **Equivariance in metavariables.** Renaming the unknowns of a problem renames the computed
    most general unifier, and preserves failure. -/
theorem UnifProblem.solve_renameVar (τ : Equiv.Perm X) (Pr : UnifProblem F X 𝔸) :
    (Pr.renameVar τ).solve
      = Pr.solve.map fun r => (Context.renameVar τ r.1, Subst.renameVar τ r.2) :=
  UnifProblem.solve_relabel 1 τ Pr

theorem UnifProblem.mem_solutions_rename (ρ : Equiv.Perm 𝔸) (Pr : UnifProblem F X 𝔸)
    (Γ : Context 𝔸 X) (σ : Subst F X 𝔸) :
    (Context.rename ρ Γ, Subst.rename ρ σ) ∈ (Pr.rename ρ).Solutions ↔ (Γ, σ) ∈ Pr.Solutions :=
  UnifProblem.mem_solutions_relabel ρ 1 Pr Γ σ

theorem UnifProblem.mem_solutions_renameVar (τ : Equiv.Perm X) (Pr : UnifProblem F X 𝔸)
    (Γ : Context 𝔸 X) (σ : Subst F X 𝔸) :
    (Context.renameVar τ Γ, Subst.renameVar τ σ) ∈ (Pr.renameVar τ).Solutions
      ↔ (Γ, σ) ∈ Pr.Solutions :=
  UnifProblem.mem_solutions_relabel 1 τ Pr Γ σ

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
