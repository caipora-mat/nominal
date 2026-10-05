import Instances.LambdaCalculus.Substitution

/-!
# Parallel beta reduction on quotient lambda terms

`Term.Parallel` is the standard parallel relation: variables stay fixed,
applications and lambdas reduce their immediate subterms, and a beta contraction
may reduce both its body and its argument before substituting. No rule imposes
freshness, closedness, or evaluation-order conditions. The relation is reflexive;
it is not asserted to be transitive.

The endpoints and all rule premises are quotient `Term` values, so alpha equality
is ordinary equality in the rules. In particular, `subst_eq_of_lam_eq` identifies
the contraction results for equal abstractions, without restricting the
replacement. `Parallel.beta_rename` makes the corresponding simultaneous
renaming of a contraction's body premise explicit.

The nominal properties below use ordinary induction on a derivation. The
constructor inversion lemmas retain the binders occurring in those rules; they
do not choose binders fresh for an arbitrary context. `ReductionInduction` and
`ReductionInversion` derive those stronger interfaces separately.
-/

namespace LambdaCalculus

open Nominal.Core Nominal.Set

universe u

variable {α : Type u} [Name α]

namespace Term

/-- Parallel beta reduction. In `beta`, both the body and the argument reduce
before capture-avoiding substitution; the binder is unrestricted. -/
inductive Parallel : Term α → Term α → Prop where
  | var (a : α) : Parallel (Term.var a) (Term.var a)
  | app {t t' s s' : Term α} (ht : Parallel t t') (hs : Parallel s s') :
      Parallel (Term.app t s) (Term.app t' s')
  | lam (a : α) {t t' : Term α} (h : Parallel t t') :
      Parallel (Term.lam a t) (Term.lam a t')
  | beta (a : α) {t t' s s' : Term α} (ht : Parallel t t') (hs : Parallel s s') :
      Parallel (Term.app (Term.lam a t) s) (t'[a := s'])

scoped[LambdaCalculus] infix:50 " ⇉ " => LambdaCalculus.Term.Parallel

namespace Parallel

/-- Every quotient term reduces to itself in parallel. -/
@[refl] theorem refl (t : Term α) : t ⇉ t := by
  induction t using strong_ind_finset ∅ with
  | hVar a => exact .var a
  | hApp _ _ iht ihs => exact .app iht ihs
  | hLam a _ _ ih => exact .lam a ih

/-- Simultaneously permuting both endpoints preserves parallel reduction. -/
theorem equivariant (π : FinitePerm α) {t s : Term α} (h : t ⇉ s) :
    (π • t) ⇉ (π • s) := by
  induction h with
  | var a => simpa only [smul_var] using Parallel.var (π • a)
  | app _ _ iht ihs => simpa only [smul_app] using Parallel.app iht ihs
  | lam a _ ih => simpa only [smul_lam] using Parallel.lam (π • a) ih
  | beta a _ _ iht ihs =>
    simpa only [smul_app, smul_lam, subst_equivariant] using
      Parallel.beta (π • a) iht ihs

theorem equivariant_iff (π : FinitePerm α) {t s : Term α} :
    (π • t) ⇉ (π • s) ↔ t ⇉ s := by
  constructor
  · intro h
    simpa only [inv_smul_smul] using equivariant π⁻¹ h
  · exact equivariant π

/-- Parallel reduction introduces no new free atoms. -/
theorem supp_le {t s : Term α} (h : t ⇉ s) : supp s ⊆ supp t := by
  induction h with
  | var _ => exact Finset.Subset.refl _
  | app _ _ iht ihs =>
    simpa only [supp_term_app] using Finset.union_subset_union iht ihs
  | lam _ _ ih =>
    simpa only [supp_term_lam] using
      Finset.sdiff_subset_sdiff ih (Finset.Subset.refl _)
  | @beta a t t' s s' _ _ iht ihs =>
    simp only [supp_term_app, supp_term_lam]
    exact (supp_subst_le t' a s').trans
      (Finset.union_subset_union
        (Finset.sdiff_subset_sdiff iht (Finset.Subset.refl _)) ihs)

/-- Any atom fresh for the source remains fresh for the target. -/
theorem fresh {t s : Term α} (h : t ⇉ s) {a : α} (ha : a # t) : a # s :=
  fresh_of_supp_subset h.supp_le ha

/-- The same preservation law holds for freshness of arbitrary nominal values. -/
theorem fresh_left {X : Type*} [Nominal α X] {t s : Term α} (h : t ⇉ s)
    {x : X} (hx : x # t) : x # s := by
  exact fresh_comm.mpr (fresh_of_supp_subset_left h.supp_le (fresh_comm.mp hx))

/-- Renaming a contraction binder transports its body premise and leaves the
result unchanged. Freshness for the source abstraction suffices: support
preservation supplies freshness for the reduced abstraction, and the argument
need not be fresh for either binder. -/
theorem beta_rename (a b : α) {t t' s s' : Term α}
    (ht : t ⇉ t') (hs : s ⇉ s') (hb : b # Term.lam a t) :
    Term.app (Term.lam b (swap a b • t)) s ⇉ t'[a := s'] := by
  have hb' : b # Term.lam a t' := (Parallel.lam a ht).fresh hb
  rw [subst_rename a b t' s' hb']
  exact Parallel.beta b (equivariant (swap a b) ht) hs

/-- A variable has only itself as a parallel successor. -/
@[simp] theorem var_iff {a : α} {t : Term α} : Term.var a ⇉ t ↔ t = Term.var a := by
  constructor
  · intro h
    generalize heq : Term.var a = s at h
    cases h <;> simp_all
  · rintro rfl
    exact .var a

/-- An application either reduces its components in parallel or contracts a
lambda in its function position. The latter alternative records the actual
binder and body of the contraction rule. -/
theorem app_iff {t s r : Term α} : Term.app t s ⇉ r ↔
    (∃ t' s', t ⇉ t' ∧ s ⇉ s' ∧ r = Term.app t' s') ∨
    (∃ a u u' s', t = Term.lam a u ∧ u ⇉ u' ∧ s ⇉ s' ∧ r = u'[a := s']) := by
  constructor
  · intro h
    generalize heq : Term.app t s = v at h
    cases h with
    | var a => exact False.elim (app_ne_var t s a heq)
    | @app t₀ t' s₀ s' ht hs =>
      obtain ⟨rfl, rfl⟩ := app_inj.mp heq
      exact Or.inl ⟨t', s', ht, hs, rfl⟩
    | lam a h => exact False.elim (app_ne_lam _ _ _ _ heq)
    | @beta a u u' s₀ s' ht hs =>
      obtain ⟨hfun, rfl⟩ := app_inj.mp heq
      exact Or.inr ⟨a, u, u', s', hfun, ht, hs, rfl⟩
  · rintro (⟨t', s', ht, hs, rfl⟩ | ⟨a, u, u', s', rfl, ht, hs, rfl⟩)
    · exact .app ht hs
    · exact .beta a ht hs

/-- Ordinary lambda inversion retains a representative from the derivation.
It does not assert that its binder is fresh for any external context. -/
theorem lam_iff {a : α} {t s : Term α} : Term.lam a t ⇉ s ↔
    ∃ b u u', Term.lam a t = Term.lam b u ∧ u ⇉ u' ∧ s = Term.lam b u' := by
  constructor
  · intro h
    generalize heq : Term.lam a t = v at h
    cases h with
    | var b => exact False.elim (lam_ne_var _ _ _ heq)
    | app ht hs => exact False.elim (lam_ne_app _ _ _ _ heq)
    | @lam b u u' h => exact ⟨b, u, u', rfl, h, rfl⟩
    | beta b ht hs => exact False.elim (lam_ne_app _ _ _ _ heq)
  · rintro ⟨b, u, u', heq, h, rfl⟩
    rw [heq]
    exact .lam b h

end Parallel

end Term

end LambdaCalculus
