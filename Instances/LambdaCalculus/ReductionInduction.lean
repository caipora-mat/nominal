import Instances.LambdaCalculus.Beta
import Instances.LambdaCalculus.Parallel

/-!
# Fresh induction on reduction derivations

`Beta.strong_ind` and `Parallel.strong_ind` justify fresh-binder rule induction
for arbitrary predicates on the two endpoints and a nominal avoidance context.
Every recursive premise supplies both its derivation and an induction hypothesis
at **all** contexts. No equivariance or support assumption on the predicate is
needed. Contexts can include atoms, terms, finite sets, and previously chosen
binders, so nested uses can enlarge the avoidance context.

The proofs strengthen ordinary **derivation** induction over permutations.
Lambda cases rename both premise endpoints. Contraction cases rename only the
body premise and use `subst_rename` to preserve the conclusion with the original
replacement. The fresh binder also avoids the argument(s), but is never required
to be fresh for its own body. The underlying unrestricted relations are unchanged.
-/

namespace LambdaCalculus

open Nominal.Core Nominal.Set

universe u v
variable {α : Type u} [Name α]

namespace Term.Beta

/-- Fresh rule induction for contextual beta reduction. Recursive hypotheses may
be instantiated at a new context, for example one containing an enclosing binder.
The predicate is arbitrary; only the avoidance context carries a nominal action. -/
@[elab_as_elim]
theorem strong_ind {Z : Type v} [Nominal α Z]
    {P : Term α → Term α → Z → Prop}
    (hBeta : ∀ a t s z, a # z → a # s → P (Term.app (Term.lam a t) s) (t[a := s]) z)
    (hAppLeft : ∀ t t' s z, Beta t t' → (∀ d, P t t' d) → P (Term.app t s) (Term.app t' s) z)
    (hAppRight : ∀ t s s' z, Beta s s' → (∀ d, P s s' d) → P (Term.app t s) (Term.app t s') z)
    (hLam : ∀ a t t' z, Beta t t' → a # z → (∀ d, P t t' d) → P (Term.lam a t) (Term.lam a t') z)
    {t t' : Term α} (h : Beta t t') (z : Z) : P t t' z := by
  have aux : ∀ (π : FinitePerm α) (z : Z), P (π • t) (π • t') z := by
    induction h with
    | beta a t s =>
      intro π z
      simp only [smul_app, smul_lam, subst_equivariant]
      choose_fresh b from z (π • t) (π • s)
      have hb : b # Term.lam (π • a) (π • t) :=
        fresh_term_lam_of_fresh _ _ _ bFresh2
      rw [lam_eq_swap hb, subst_rename (π • a) b (π • t) (π • s) hb]
      exact hBeta b _ _ z bFresh1 bFresh3
    | @app_left t t' h s ih =>
      intro π z
      simp only [smul_app]
      exact hAppLeft _ _ _ z (h.equivariant π) (ih π)
    | @app_right t s s' h ih =>
      intro π z
      simp only [smul_app]
      exact hAppRight _ _ _ z (h.equivariant π) (ih π)
    | @lam a t t' h ih =>
      intro π z
      simp only [smul_lam]
      choose_fresh b from z (π • t)
      have hb' := (h.equivariant π).fresh bFresh2
      rw [lam_eq_swap (fresh_term_lam_of_fresh _ _ _ bFresh2),
        lam_eq_swap (fresh_term_lam_of_fresh _ _ _ hb')]
      refine hLam b _ _ z ((h.equivariant π).equivariant (swap (π • a) b))
        bFresh1 (fun d => ?_)
      simpa only [mul_smul] using ih (swap (π • a) b * π) d
  simpa only [one_smul] using aux 1 z

/-- Convenience form with a fixed finite avoidance set and an endpoint predicate.
Use `strong_ind` when recursive calls must change their avoidance context. -/
@[elab_as_elim]
theorem strong_ind_finset (A : Finset α) {P : Term α → Term α → Prop}
    (hBeta : ∀ a t s, a ∉ A → a # s → P (Term.app (Term.lam a t) s) (t[a := s]))
    (hAppLeft : ∀ t t' s, Beta t t' → P t t' → P (Term.app t s) (Term.app t' s))
    (hAppRight : ∀ t s s', Beta s s' → P s s' → P (Term.app t s) (Term.app t s'))
    (hLam : ∀ a t t', Beta t t' → a ∉ A → P t t' → P (Term.lam a t) (Term.lam a t'))
    {t t' : Term α} (h : Beta t t') : P t t' := by
  exact strong_ind (P := fun t t' B => B = A → P t t')
    (hBeta := fun a t s B ha hs heq => hBeta a t s
      (fresh_atom_finset.mp (heq ▸ ha)) hs)
    (hAppLeft := fun t t' s _ ht ih _ => hAppLeft t t' s ht (ih A rfl))
    (hAppRight := fun t s s' _ hs ih _ => hAppRight t s s' hs (ih A rfl))
    (hLam := fun a t t' B ht ha ih heq => hLam a t t' ht
      (fresh_atom_finset.mp (heq ▸ ha)) (ih A rfl)) h A rfl

end Term.Beta

namespace Term.Parallel

/-- Fresh rule induction for parallel reduction. The contraction case supplies
both premise derivations and both context-generalized induction hypotheses.
Avoiding a context `(x, r, r')` supports substitution in related subjects by
related replacements; freshness of the binder for `s` and `s'` is also exposed. -/
@[elab_as_elim]
theorem strong_ind {Z : Type v} [Nominal α Z]
    {P : Term α → Term α → Z → Prop}
    (hVar : ∀ a z, P (Term.var a) (Term.var a) z)
    (hApp : ∀ t t' s s' z, Parallel t t' → Parallel s s' →
      (∀ d, P t t' d) → (∀ d, P s s' d) → P (Term.app t s) (Term.app t' s') z)
    (hLam : ∀ a t t' z, Parallel t t' → a # z → (∀ d, P t t' d) →
      P (Term.lam a t) (Term.lam a t') z)
    (hBeta : ∀ a t t' s s' z, Parallel t t' → Parallel s s' →
      a # z → a # s → a # s' → (∀ d, P t t' d) → (∀ d, P s s' d) →
      P (Term.app (Term.lam a t) s) (t'[a := s']) z)
    {t t' : Term α} (h : Parallel t t') (z : Z) : P t t' z := by
  have aux : ∀ (π : FinitePerm α) (z : Z), P (π • t) (π • t') z := by
    induction h with
    | var a =>
      intro π z
      simpa only [smul_var] using hVar (π • a) z
    | @app t t' s s' ht hs iht ihs =>
      intro π z
      simp only [smul_app]
      exact hApp _ _ _ _ z (ht.equivariant π) (hs.equivariant π) (iht π) (ihs π)
    | @lam a t t' h ih =>
      intro π z
      simp only [smul_lam]
      choose_fresh b from z (π • t)
      have hb' := (h.equivariant π).fresh bFresh2
      rw [lam_eq_swap (fresh_term_lam_of_fresh _ _ _ bFresh2),
        lam_eq_swap (fresh_term_lam_of_fresh _ _ _ hb')]
      refine hLam b _ _ z ((h.equivariant π).equivariant (swap (π • a) b))
        bFresh1 (fun d => ?_)
      simpa only [mul_smul] using ih (swap (π • a) b * π) d
    | @beta a t t' s s' ht hs iht ihs =>
      intro π z
      simp only [smul_app, smul_lam, subst_equivariant]
      choose_fresh b from z (π • t) (π • s)
      have hbt : b # Term.lam (π • a) (π • t) :=
        fresh_term_lam_of_fresh _ _ _ bFresh2
      have hbt' : b # Term.lam (π • a) (π • t') :=
        fresh_term_lam_of_fresh _ _ _ ((ht.equivariant π).fresh bFresh2)
      rw [lam_eq_swap hbt, subst_rename (π • a) b (π • t') (π • s') hbt']
      refine hBeta b _ _ _ _ z
        ((ht.equivariant π).equivariant (swap (π • a) b)) (hs.equivariant π)
        bFresh1 bFresh3 ((hs.equivariant π).fresh bFresh3) (fun d => ?_) (ihs π)
      simpa only [mul_smul] using iht (swap (π • a) b * π) d
  simpa only [one_smul] using aux 1 z

/-- Parallel rule induction avoiding a fixed finite set. Both contraction
premises retain their derivations and induction hypotheses. -/
@[elab_as_elim]
theorem strong_ind_finset (A : Finset α) {P : Term α → Term α → Prop}
    (hVar : ∀ a, P (Term.var a) (Term.var a))
    (hApp : ∀ t t' s s', Parallel t t' → Parallel s s' → P t t' → P s s' →
      P (Term.app t s) (Term.app t' s'))
    (hLam : ∀ a t t', Parallel t t' → a ∉ A → P t t' →
      P (Term.lam a t) (Term.lam a t'))
    (hBeta : ∀ a t t' s s', Parallel t t' → Parallel s s' →
      a ∉ A → a # s → a # s' → P t t' → P s s' →
      P (Term.app (Term.lam a t) s) (t'[a := s']))
    {t t' : Term α} (h : Parallel t t') : P t t' := by
  exact strong_ind (P := fun t t' B => B = A → P t t')
    (hVar := fun a _ _ => hVar a)
    (hApp := fun t t' s s' _ ht hs iht ihs _ =>
      hApp t t' s s' ht hs (iht A rfl) (ihs A rfl))
    (hLam := fun a t t' B ht ha ih heq =>
      hLam a t t' ht (fresh_atom_finset.mp (heq ▸ ha)) (ih A rfl))
    (hBeta := fun a t t' s s' B ht hs ha has has' iht ihs heq =>
      hBeta a t t' s s' ht hs (fresh_atom_finset.mp (heq ▸ ha)) has has'
        (iht A rfl) (ihs A rfl)) h A rfl

end Term.Parallel

end LambdaCalculus
