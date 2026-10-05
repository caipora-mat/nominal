/-
Copyright (c) 2026 Nominal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nominal contributors
-/
import Instances
import Lean.Util.CollectAxioms

/-!
# Quotient lambda reduction examples

These clients exercise unrestricted contextual beta reduction and parallel
reduction on open quotient terms. All equalities and substitution calculations
use the public term interface; no raw alpha-equivalence witnesses are exposed.
-/

namespace LambdaReductionExamples

open Nominal.Core Nominal.Set LambdaCalculus LambdaCalculus.Term

universe u
variable {α : Type u} [Name α]

/-- Identity contracts with an arbitrary, possibly open replacement. -/
theorem identity (a : α) (s : Term α) :
    Beta (app (lam a (var a)) s) s := by
  simpa using Beta.beta a (var a) s

/-- Both atoms occur freely in the replacement; neither must avoid the binder. -/
theorem openTerm (a b : α) :
    Beta (app (lam a (var a)) (app (var a) (var b))) (app (var a) (var b)) :=
  identity a _

theorem applicationLeft (a : α) (s u : Term α) :
    Beta (app (app (lam a (var a)) s) u) (app s u) :=
  Beta.app_left (identity a s) u

theorem applicationRight (a : α) (t s : Term α) :
    Beta (app t (app (lam a (var a)) s)) (app t s) :=
  Beta.app_right t (identity a s)

/-- Reduction also proceeds under lambdas, without any closedness condition. -/
theorem beneathLambda (a b : α) (s : Term α) :
    Beta (lam b (app (lam a (var a)) s)) (lam b s) :=
  Beta.lam b (identity a s)

/-- The argument's free `b` would be captured by a direct descent under `lam b`.
Renaming that inner binder to `c` leaves the occurrence of `b` free. -/
theorem captureAvoidance (a b c : α) (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b) :
    Beta (app (lam a (lam b (var a))) (var b)) (lam c (var b)) ∧
      ¬ b # lam c (var b) := by
  have hsubst : (lam b (var a))[a := var b] = lam c (var b) := by
    rw [subst_lam_rename b c (var a) a (var b) (by simpa using hca)]
    have hswap : swap b c • var a = var a := by simp [hab, Ne.symm hca]
    rw [hswap, subst_lam c (var a) a (var b) (by simp [hca, hcb])]
    simp
  refine ⟨?_, ?_⟩
  · simpa only [hsubst] using Beta.beta a (lam b (var a)) (var b)
  · simp [Ne.symm hcb]

/-- Two alpha-equivalent presentations have exactly the same contraction
target. In particular, the arbitrary replacement need not avoid either binder. -/
theorem alphaRenamedContraction (a b : α) (t s : Term α) (hb : b # lam a t) :
    app (lam a t) s = app (lam b (swap a b • t)) s ∧
      Beta (app (lam a t) s) (t[a := s]) ∧
      Beta (app (lam b (swap a b • t)) s) (t[a := s]) := by
  refine ⟨congrArg (fun u => app u s) (lam_eq_swap hb), Beta.beta a t s, ?_⟩
  rw [subst_rename a b t s hb]
  exact Beta.beta b (swap a b • t) s

/-- Both binder names occur freely in this particular replacement. This tests
the unrestricted contraction rule at two alpha-equivalent identity binders. -/
theorem alphaRenamedOpenIdentity (a b : α) :
    app (lam a (var a)) (app (var a) (var b)) =
        app (lam b (var b)) (app (var a) (var b)) ∧
      Beta (app (lam a (var a)) (app (var a) (var b))) (app (var a) (var b)) ∧
      Beta (app (lam b (var b)) (app (var a) (var b))) (app (var a) (var b)) ∧
      ¬ a # app (var a) (var b) ∧ ¬ b # app (var a) (var b) := by
  have heq : lam a (var a) = lam b (var b) := by
    simpa using (lam_eq_swap (a := a) (b := b) (t := var a) (by simp))
  exact ⟨congrArg (fun u => app u (app (var a) (var b))) heq,
    identity a _, identity b _, by simp, by simp⟩

theorem parallelIdentity (a : α) (s : Term α) :
    Parallel (app (lam a (var a)) s) s := by
  simpa using Parallel.beta a (Parallel.var a) (Parallel.refl s)

/-- The outer contraction reduces its body `(λb.b) a` to `a` and its argument
`(λc.c) d` to `d` before substituting. Both premises are genuine contractions. -/
theorem parallelBodyAndArgument (a b c d : α) :
    Parallel
      (app (lam a (app (lam b (var b)) (var a))) (app (lam c (var c)) (var d)))
      (var d) := by
  simpa using Parallel.beta a (parallelIdentity b (var a)) (parallelIdentity c (var d))

/-- Reflexivity is part of parallel reduction, unlike one-step beta reduction. -/
theorem parallelReflexive (t : Term α) : Parallel t t :=
  Parallel.refl t

/-- Contracting an identity in function position exposes a new head redex.
Two parallel steps can contract both, but a single parallel step cannot. -/
theorem parallelTwoStepsNotOne (a b c : α) :
    Parallel (app (app (lam a (var a)) (lam b (var b))) (var c))
      (app (lam b (var b)) (var c)) ∧
      Parallel (app (lam b (var b)) (var c)) (var c) ∧
      ¬ Parallel (app (app (lam a (var a)) (lam b (var b))) (var c)) (var c) := by
  refine ⟨Parallel.app (parallelIdentity a (lam b (var b))) (Parallel.var c),
    parallelIdentity b (var c), ?_⟩
  rw [Parallel.app_iff]
  rintro (⟨t', s', _, _, heq⟩ | ⟨d, t, t', s', heq, _, _, _⟩)
  · exact var_ne_app c t' s' heq
  · exact app_ne_lam _ _ d t heq

/-- Reflexive-transitive beta reduction composes steps in different contexts. -/
theorem contextualSequence (a b : α) (t s : Term α) :
    BetaStar (app (app (lam a (var a)) t) (app (lam b (var b)) s)) (app t s) :=
  (BetaStar.app_left (BetaStar.single (identity a t)) (app (lam b (var b)) s)).trans
    (BetaStar.app_right t (BetaStar.single (identity b s)))

/-- Conversion can reverse an erasing contraction. Unlike directed reduction,
it need not preserve support or freshness in either direction. -/
theorem conversionCanIntroduceFreeAtoms (a b c : α) :
    BetaEq (lam b (var b)) (app (lam a (lam b (var b))) (var c)) ∧
      ¬ supp (app (lam a (lam b (var b))) (var c)) ⊆ supp (lam b (var b)) := by
  have hsubst : (lam b (var b))[a := var c] = lam b (var b) :=
    subst_fresh a _ _ (by simp)
  have hstep : Beta (app (lam a (lam b (var b))) (var c)) (lam b (var b)) := by
    simpa only [hsubst] using Beta.beta a (lam b (var b)) (var c)
  exact ⟨(BetaEq.of_beta hstep).symm, by simp⟩

/-- A variable has no one-step beta successor, including itself. -/
theorem variableHasNoBetaSuccessor (a : α) (t : Term α) : ¬ Beta (var a) t :=
  Beta.not_var

end LambdaReductionExamples

-- Reject admissions and additional axioms in these clients and the public
-- lambda results they consume. Classical Lean's standard foundations are allowed.
open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "LambdaReductionExamples." ||
        name.toString.startsWith "LambdaCalculus." then
      let axioms ← collectAxioms name
      let extra := axioms.filter fun a =>
        a != `propext && a != `Classical.choice && a != `Quot.sound
      unless extra.isEmpty do
        throwError "{name}: unexpected axioms {extra}"
