import Instances.LambdaCalculus.ParallelSubstitution
import Instances.LambdaCalculus.ReductionInversion
import Mathlib.Logic.Relation

/-!
# Diamond for parallel reduction

Any two parallel reducts of an arbitrary open quotient term have a common
parallel reduct. `Relation.Join Parallel` denotes two parallel edges, with no
reflexive-transitive closure.

The proof uses fresh rule induction with the competing target as its nominal
context, leaving that target and its derivation generalized in every induction
hypothesis. Public lambda inversion aligns binders even when the derivations
use different representatives. In the application/contraction overlap, the
function induction hypothesis joins two lambdas; inversion exposes a common
body. Simultaneous substitution compatibility then joins the contractions.

This direct route needs no additional inversion lemmas or recursion interface.
Complete development and its computation/renaming obligations are unnecessary.
-/

namespace LambdaCalculus

open Nominal.Core Nominal.Set

universe u
variable {α : Type u} [Name α]

namespace Term.Parallel

/-- Parallel reduction has the diamond property on all quotient terms:
`t ⇉ t₁` and `t ⇉ t₂` imply `∃ u, t₁ ⇉ u ∧ t₂ ⇉ u`.
Both joining edges are parallel reductions, including reflexive ones. -/
theorem diamond {t t₁ t₂ : Term α} (h₁ : t ⇉ t₁) (h₂ : t ⇉ t₂) :
    Relation.Join Parallel t₁ t₂ := by
  apply strong_ind
    (P := fun t t' u => t ⇉ u → Relation.Join Parallel t' u)
    (hVar := by
      intro a u hu
      obtain rfl := var_iff.mp hu
      exact ⟨Term.var a, Parallel.refl _, Parallel.refl _⟩)
    (hApp := by
      intro t t' s s' u ht _ iht ihs hu
      rcases app_iff.mp hu with ⟨t₂, s₂, ht₂, hs₂, rfl⟩ |
          ⟨a, v, v₂, s₂, rfl, hv₂, hs₂, rfl⟩
      · -- Congruence / congruence: join the two pairs of components.
        obtain ⟨p, ht'p, ht₂p⟩ := iht t₂ ht₂
        obtain ⟨q, hs'q, hs₂q⟩ := ihs s₂ hs₂
        exact ⟨Term.app p q, Parallel.app ht'p hs'q, Parallel.app ht₂p hs₂q⟩
      · -- Congruence / contraction: the function IH joins two lambdas.
        obtain ⟨v₁, _, rfl⟩ := lam_iff_same.mp ht
        obtain ⟨p, hv₁p, hv₂p⟩ := iht (Term.lam a v₂) (Parallel.lam a hv₂)
        obtain ⟨w, hv₁w, rfl⟩ := lam_iff_same.mp hv₁p
        have hv₂w := lam_lam_iff.mp hv₂p
        obtain ⟨q, hs'q, hs₂q⟩ := ihs s₂ hs₂
        exact ⟨w[a := q], Parallel.beta a hv₁w hs'q, hv₂w.subst hs₂q a⟩)
    (hLam := by
      intro a t t' u _ _ ih hu
      obtain ⟨t₂, ht₂, rfl⟩ := lam_iff_same.mp hu
      obtain ⟨p, ht'p, ht₂p⟩ := ih t₂ ht₂
      exact ⟨Term.lam a p, Parallel.lam a ht'p, Parallel.lam a ht₂p⟩)
    (hBeta := by
      intro a t t' s s' u _ _ _ _ _ iht ihs hu
      -- Invert at the induction binder; the competing rule's binder may differ.
      rcases (app_iff_at_fresh (fresh_term_lam_of_eq a t)).mp hu with
          ⟨t₂, s₂, ht₂, hs₂, rfl⟩ | ⟨v, v₂, s₂, heq, hv₂, hs₂, rfl⟩
      · -- Contraction / congruence.
        obtain ⟨v₂, hv₂, rfl⟩ := lam_iff_same.mp ht₂
        obtain ⟨p, ht'p, hv₂p⟩ := iht v₂ hv₂
        obtain ⟨q, hs'q, hs₂q⟩ := ihs s₂ hs₂
        exact ⟨p[a := q], ht'p.subst hs'q a, Parallel.beta a hv₂p hs₂q⟩
      · -- Contraction / contraction: aligned sources have equal bodies.
        obtain rfl := Term.lam_inj.mp heq
        obtain ⟨p, ht'p, hv₂p⟩ := iht v₂ hv₂
        obtain ⟨q, hs'q, hs₂q⟩ := ihs s₂ hs₂
        exact ⟨p[a := q], ht'p.subst hs'q a, hv₂p.subst hs₂q a⟩)
    h₁ t₂ h₂

end Term.Parallel

end LambdaCalculus
