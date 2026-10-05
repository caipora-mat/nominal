import Instances.LambdaCalculus.Beta
import Instances.LambdaCalculus.Parallel

/-!
# Fresh inversion for lambda-calculus reduction

The chosen-binder principles `lam_iff_at_fresh`, `lam_iff_common_fresh`, and
`app_iff_at_fresh` align derivations using quotient lambda equality and relation
equivariance. A chosen atom need only be fresh for the source abstraction (or
the function of an application). In particular it may be the original binder,
and it need not be fresh for that binder's body or for a contraction argument.

The `lam_iff_fresh` and `app_iff_fresh` variants obtain a binder avoiding an
arbitrary nominal context. Application inversion retains every congruence and
contraction alternative; for parallel reduction those alternatives can overlap.
-/

namespace LambdaCalculus

open Nominal.Core Nominal.Set

universe u v
variable {α : Type u} [Name α]

namespace Term
namespace Beta

/-- Invert a lambda step at any chosen atom fresh for its source abstraction.
The premise derivation is transported together with both of its endpoints. -/
theorem lam_iff_at_fresh {a c : α} {t u : Term α} (hc : c # Term.lam a t) :
    Beta (Term.lam a t) u ↔
      ∃ v, Beta (swap a c • t) v ∧ u = Term.lam c v := by
  constructor
  · intro h
    obtain ⟨b, v, w, heq, hvw, rfl⟩ := lam_iff.mp h
    have hcv : c # Term.lam b v := heq ▸ hc
    have hcw : c # Term.lam b w := (Beta.lam b hvw).fresh hcv
    refine ⟨swap b c • w, ?_, lam_eq_swap hcw⟩
    rw [(lam_eq_iff_common_fresh hc hcv).mp heq]
    exact hvw.equivariant (swap b c)
  · rintro ⟨v, h, rfl⟩
    rw [lam_eq_swap hc]
    exact Beta.lam c h

/-- Lambda inversion can retain the binder already displayed by the client. -/
theorem lam_iff_same {a : α} {t u : Term α} :
    Beta (Term.lam a t) u ↔ ∃ v, Beta t v ∧ u = Term.lam a v := by
  simpa only [swap_self, one_smul] using
    lam_iff_at_fresh (u := u) (fresh_term_lam_of_eq a t)

/-- Reduction under a common binder is exactly reduction of the bodies. -/
theorem lam_lam_iff {a : α} {t s : Term α} :
    Beta (Term.lam a t) (Term.lam a s) ↔ Beta t s := by
  rw [lam_iff_same]
  constructor
  · rintro ⟨v, h, heq⟩
    exact (lam_inj.mp heq).symm ▸ h
  · intro h
    exact ⟨s, h, rfl⟩

/-- Align differently named lambda endpoints at a common fresh binder. -/
theorem lam_iff_common_fresh {a b c : α} {t s : Term α}
    (hc₁ : c # Term.lam a t) (hc₂ : c # Term.lam b s) :
    Beta (Term.lam a t) (Term.lam b s) ↔
      Beta (swap a c • t) (swap b c • s) := by
  rw [lam_eq_swap hc₁, lam_eq_swap hc₂, lam_lam_iff]

/-- Obtain a common lambda binder fresh for an arbitrary nominal context. -/
theorem lam_iff_fresh {X : Type v} [Nominal α X] (z : X)
    {a : α} {t u : Term α} :
    Beta (Term.lam a t) u ↔ ∃ c v w,
      c # z ∧ Term.lam a t = Term.lam c v ∧ Beta v w ∧ u = Term.lam c w := by
  constructor
  · intro h
    obtain ⟨c, hc⟩ := exists_fresh_atom (α := α) (z, Term.lam a t)
    obtain ⟨hcz, hct⟩ := fresh_prod_right.mp hc
    obtain ⟨w, hw, hu⟩ := (lam_iff_at_fresh hct).mp h
    exact ⟨c, swap a c • t, w, hcz, lam_eq_swap hct, hw, hu⟩
  · rintro ⟨c, v, w, _, heq, h, rfl⟩
    rw [heq]
    exact Beta.lam c h

/-- Application inversion with a prescribed binder for the contraction branch.
There is no freshness requirement on the argument `s`. -/
theorem app_iff_at_fresh {c : α} {t s u : Term α} (hc : c # t) :
    Beta (app t s) u ↔
      (∃ t', Beta t t' ∧ u = app t' s) ∨
      (∃ s', Beta s s' ∧ u = app t s') ∨
      (∃ v, t = Term.lam c v ∧ u = v[c := s]) := by
  rw [app_iff]
  constructor
  · rintro (h | h | ⟨a, v, heq, hu⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · have hcv : c # Term.lam a v := heq ▸ hc
      exact Or.inr (Or.inr ⟨swap a c • v, heq.trans (lam_eq_swap hcv),
        hu.trans (subst_rename a c v s hcv)⟩)
  · rintro (h | h | ⟨v, heq, hu⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨c, v, heq, hu⟩)

/-- Application inversion obtaining a contraction binder fresh for the context
and argument. The two contextual reduction alternatives are retained. -/
theorem app_iff_fresh {X : Type v} [Nominal α X] (z : X) {t s u : Term α} :
    Beta (app t s) u ↔
      (∃ t', Beta t t' ∧ u = app t' s) ∨
      (∃ s', Beta s s' ∧ u = app t s') ∨
      (∃ a v, a # (z, s) ∧ t = Term.lam a v ∧ u = v[a := s]) := by
  constructor
  · intro h
    obtain ⟨a, ha⟩ := exists_fresh_atom (α := α) ((z, s), t)
    obtain ⟨hazs, hat⟩ := fresh_prod_right.mp ha
    rcases (app_iff_at_fresh hat).mp h with h | h | ⟨v, ht, hu⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨a, v, hazs, ht, hu⟩)
  · rintro (⟨t', h, rfl⟩ | ⟨s', h, rfl⟩ | ⟨a, v, _, rfl, rfl⟩)
    · exact Beta.app_left h s
    · exact Beta.app_right t h
    · exact Beta.beta a v s

end Beta

namespace Parallel

/-- Invert a parallel lambda step at a chosen atom fresh for the abstraction. -/
theorem lam_iff_at_fresh {a c : α} {t u : Term α} (hc : c # Term.lam a t) :
    Term.lam a t ⇉ u ↔ ∃ v, (swap a c • t) ⇉ v ∧ u = Term.lam c v := by
  constructor
  · intro h
    obtain ⟨b, v, w, heq, hvw, rfl⟩ := lam_iff.mp h
    have hcv : c # Term.lam b v := heq ▸ hc
    have hcw : c # Term.lam b w := (Parallel.lam b hvw).fresh hcv
    refine ⟨swap b c • w, ?_, lam_eq_swap hcw⟩
    rw [(lam_eq_iff_common_fresh hc hcv).mp heq]
    exact equivariant (swap b c) hvw
  · rintro ⟨v, h, rfl⟩
    rw [lam_eq_swap hc]
    exact Parallel.lam c h

/-- Lambda inversion retaining the binder displayed by the client. -/
theorem lam_iff_same {a : α} {t u : Term α} :
    Term.lam a t ⇉ u ↔ ∃ v, t ⇉ v ∧ u = Term.lam a v := by
  simpa only [swap_self, one_smul] using
    lam_iff_at_fresh (u := u) (fresh_term_lam_of_eq a t)

/-- Parallel reduction under a common binder reduces exactly the bodies. -/
theorem lam_lam_iff {a : α} {t s : Term α} :
    Term.lam a t ⇉ Term.lam a s ↔ t ⇉ s := by
  rw [lam_iff_same]
  constructor
  · rintro ⟨v, h, heq⟩
    exact (lam_inj.mp heq).symm ▸ h
  · intro h
    exact ⟨s, h, rfl⟩

/-- Align differently named lambda endpoints at any common fresh binder. -/
theorem lam_iff_common_fresh {a b c : α} {t s : Term α}
    (hc₁ : c # Term.lam a t) (hc₂ : c # Term.lam b s) :
    Term.lam a t ⇉ Term.lam b s ↔ (swap a c • t) ⇉ (swap b c • s) := by
  rw [lam_eq_swap hc₁, lam_eq_swap hc₂, lam_lam_iff]

/-- Obtain a common lambda binder avoiding an arbitrary nominal context. -/
theorem lam_iff_fresh {X : Type v} [Nominal α X] (z : X)
    {a : α} {t u : Term α} :
    Term.lam a t ⇉ u ↔ ∃ c v w,
      c # z ∧ Term.lam a t = Term.lam c v ∧ v ⇉ w ∧ u = Term.lam c w := by
  constructor
  · intro h
    obtain ⟨c, hc⟩ := exists_fresh_atom (α := α) (z, Term.lam a t)
    obtain ⟨hcz, hct⟩ := fresh_prod_right.mp hc
    obtain ⟨w, hw, hu⟩ := (lam_iff_at_fresh hct).mp h
    exact ⟨c, swap a c • t, w, hcz, lam_eq_swap hct, hw, hu⟩
  · rintro ⟨c, v, w, _, heq, h, rfl⟩
    rw [heq]
    exact Parallel.lam c h

/-- Parallel application inversion with a prescribed contraction binder. Both
body endpoints are renamed; the argument premise and its endpoints are left
unchanged. Congruence and contraction are alternatives, not exclusive cases. -/
theorem app_iff_at_fresh {c : α} {t s r : Term α} (hc : c # t) :
    Term.app t s ⇉ r ↔
      (∃ t' s', t ⇉ t' ∧ s ⇉ s' ∧ r = Term.app t' s') ∨
      (∃ u u' s', t = Term.lam c u ∧ u ⇉ u' ∧ s ⇉ s' ∧ r = u'[c := s']) := by
  rw [app_iff]
  constructor
  · rintro (h | ⟨a, u, u', s', heq, hu, hs, hr⟩)
    · exact Or.inl h
    · have hcu : c # Term.lam a u := heq ▸ hc
      have hcu' : c # Term.lam a u' := (Parallel.lam a hu).fresh hcu
      exact Or.inr ⟨swap a c • u, swap a c • u', s',
        heq.trans (lam_eq_swap hcu), equivariant (swap a c) hu, hs,
        hr.trans (subst_rename a c u' s' hcu')⟩
  · rintro (h | ⟨u, u', s', heq, hu, hs, hr⟩)
    · exact Or.inl h
    · exact Or.inr ⟨c, u, u', s', heq, hu, hs, hr⟩

/-- Parallel application inversion obtaining a contraction binder fresh for
the context and both argument endpoints. All overlapping alternatives remain. -/
theorem app_iff_fresh {X : Type v} [Nominal α X] (z : X) {t s r : Term α} :
    Term.app t s ⇉ r ↔
      (∃ t' s', t ⇉ t' ∧ s ⇉ s' ∧ r = Term.app t' s') ∨
      (∃ a u u' s', a # (z, s, s') ∧ t = Term.lam a u ∧
        u ⇉ u' ∧ s ⇉ s' ∧ r = u'[a := s']) := by
  constructor
  · intro h
    obtain ⟨a, ha⟩ := exists_fresh_atom (α := α) ((z, s), t)
    obtain ⟨hazs, hat⟩ := fresh_prod_right.mp ha
    rcases (app_iff_at_fresh hat).mp h with h | ⟨u, u', s', ht, hu, hs, hr⟩
    · exact Or.inl h
    · obtain ⟨haz, has⟩ := fresh_prod_right.mp hazs
      exact Or.inr ⟨a, u, u', s',
        fresh_prod_right.mpr ⟨haz, fresh_prod_right.mpr ⟨has, hs.fresh has⟩⟩,
        ht, hu, hs, hr⟩
  · rintro (⟨t', s', ht, hs, rfl⟩ | ⟨a, u, u', s', _, rfl, hu, hs, rfl⟩)
    · exact Parallel.app ht hs
    · exact Parallel.beta a hu hs

end Parallel
end Term
end LambdaCalculus
