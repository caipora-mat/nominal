import Instances.LambdaCalculus.Substitution

/-!
# Contextual beta reduction on quotient lambda terms

`Term.Beta` is ordinary one-step, full contextual beta reduction: a redex can
contract in either application position or beneath a lambda. The contraction
rule has no freshness, closedness, or evaluation-order premise and uses the
existing capture-avoiding substitution.

Both endpoints are quotient `Term` values. Thus alpha equality is actual
equality in the indices. In particular, `subst_eq_of_lam_eq` says that equal
abstractions have equal contraction results for every argument, including one
containing either binder freely. `Beta.beta_of_lam_eq` exposes this compatibility.

The nominal properties below use ordinary induction on derivations and the
public constructor/substitution laws. This recursor does **not** supply binders
fresh for an external context; `ReductionInduction` and `ReductionInversion`
provide the separate fresh rule induction and inversion interfaces.
-/

namespace LambdaCalculus

open Nominal.Core Nominal.Set

universe u
variable {α : Type u} [Name α]

namespace Term

/-- One beta contraction anywhere in a term, including beneath binders. -/
inductive Beta : Term α → Term α → Prop where
  | beta (a : α) (t s : Term α) : Beta (app (lam a t) s) (t[a := s])
  | app_left {t t' : Term α} (h : Beta t t') (s : Term α) :
      Beta (app t s) (app t' s)
  | app_right (t : Term α) {s s' : Term α} (h : Beta s s') :
      Beta (app t s) (app t s')
  | lam (a : α) {t t' : Term α} (h : Beta t t') : Beta (lam a t) (lam a t')

scoped[LambdaCalculus] infix:50 " →β " => LambdaCalculus.Term.Beta

namespace Beta

/-- Simultaneously permuting both endpoints preserves a beta step. -/
theorem equivariant (π : FinitePerm α) {t s : Term α} (h : Beta t s) :
    Beta (π • t) (π • s) := by
  induction h with
  | beta a t s =>
    simpa only [smul_app, smul_lam, subst_equivariant] using
      Beta.beta (π • a) (π • t) (π • s)
  | app_left h s ih => simpa only [smul_app] using Beta.app_left ih (π • s)
  | app_right t h ih => simpa only [smul_app] using Beta.app_right (π • t) ih
  | lam a h ih => simpa only [smul_lam] using Beta.lam (π • a) ih

@[simp] theorem equivariant_iff (π : FinitePerm α) {t s : Term α} :
    Beta (π • t) (π • s) ↔ Beta t s := by
  constructor
  · intro h
    simpa only [inv_smul_smul] using h.equivariant π⁻¹
  · exact equivariant π

/-- A beta step introduces no new free atoms. It can erase some. -/
theorem supp_le {t s : Term α} (h : Beta t s) : supp s ⊆ supp t := by
  induction h with
  | beta a t s => simpa only [supp_term_app, supp_term_lam] using supp_subst_le t a s
  | app_left h s ih =>
    simpa only [supp_term_app] using
      Finset.union_subset_union ih (Finset.Subset.refl (supp s))
  | app_right t h ih =>
    simpa only [supp_term_app] using
      Finset.union_subset_union (Finset.Subset.refl (supp t)) ih
  | lam a h ih =>
    simpa only [supp_term_lam] using
      Finset.sdiff_subset_sdiff ih (Finset.Subset.refl {a})

/-- Atoms fresh for the source stay fresh for its reduct. -/
theorem fresh {t s : Term α} (h : Beta t s) {a : α} (ha : a # t) : a # s := by
  rw [fresh_atom_left] at ha ⊢
  exact fun hs => ha (h.supp_le hs)

/-- Use any equal abstraction to compute the result of an unrestricted redex. -/
theorem beta_of_lam_eq (a b : α) (t u s : Term α) (h : Term.lam a t = Term.lam b u) :
    Beta (app (Term.lam a t) s) (u[b := s]) := by
  rw [← subst_eq_of_lam_eq a b t u s h]
  exact Beta.beta a t s

/-- A variable has no one-step beta successors. Quotient constructor disjointness
suffices; no inspection of raw alpha-equivalence is needed. -/
@[simp] theorem not_var {a : α} {t : Term α} : ¬ Beta (var a) t := by
  intro h
  have source_ne_var {s t : Term α} (h : Beta s t) : ∀ a, s ≠ var a := by
    cases h with
    | beta b t s => exact fun a => app_ne_var _ _ a
    | app_left h s => exact fun a => app_ne_var _ _ a
    | app_right t h => exact fun a => app_ne_var _ _ a
    | lam b h => exact fun a => lam_ne_var _ _ a
  exact source_ne_var h a rfl

/-- An application step reduces either component or contracts a head lambda.
The existential lambda presentation is equality in the quotient. -/
theorem app_iff {t s u : Term α} :
    Beta (app t s) u ↔
      (∃ t', Beta t t' ∧ u = app t' s) ∨
      (∃ s', Beta s s' ∧ u = app t s') ∨
      (∃ a v, t = Term.lam a v ∧ u = v[a := s]) := by
  constructor
  · intro h
    generalize heq : app t s = v at h
    cases h with
    | beta a v w =>
      obtain ⟨rfl, rfl⟩ := app_inj.mp heq
      exact Or.inr (Or.inr ⟨a, v, rfl, rfl⟩)
    | app_left h w =>
      obtain ⟨rfl, rfl⟩ := app_inj.mp heq
      exact Or.inl ⟨_, h, rfl⟩
    | app_right v h =>
      obtain ⟨rfl, rfl⟩ := app_inj.mp heq
      exact Or.inr (Or.inl ⟨_, h, rfl⟩)
    | lam a h => exact (app_ne_lam _ _ _ _ heq).elim
  · rintro (⟨t', h, rfl⟩ | ⟨s', h, rfl⟩ | ⟨a, v, rfl, rfl⟩)
    · exact Beta.app_left h s
    · exact Beta.app_right t h
    · exact Beta.beta a v s

/-- Ordinary lambda inversion retains the rule's actual binder and the equation
identifying its source. It does not claim a fresh binder or fresh induction. -/
theorem lam_iff {a : α} {t u : Term α} :
    Beta (Term.lam a t) u ↔
      ∃ b v w, Term.lam a t = Term.lam b v ∧ Beta v w ∧ u = Term.lam b w := by
  constructor
  · intro h
    generalize heq : Term.lam a t = v at h
    cases h with
    | beta b v w => exact (lam_ne_app _ _ _ _ heq).elim
    | app_left h w => exact (lam_ne_app _ _ _ _ heq).elim
    | app_right v h => exact (lam_ne_app _ _ _ _ heq).elim
    | lam b h => exact ⟨b, _, _, rfl, h, rfl⟩
  · rintro ⟨b, v, w, heq, h, rfl⟩
    rw [heq]
    exact Beta.lam b h

end Beta
end Term
end LambdaCalculus
