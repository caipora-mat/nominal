/-
Copyright (c) 2026 Nominal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nominal contributors
-/
import Instances
import Lean.Util.CollectAxioms

/-!
# Parallel substitution on open quotient terms

These clients use the public reduction and substitution interfaces. They cover
simultaneously contracting subjects and replacements, capture avoidance beneath
binders, repeated binder shadowing, and substitution across a contraction whose
body and argument both reduce.
-/

namespace LambdaParallelSubstitutionExamples

open Nominal.Core Nominal.Set LambdaCalculus LambdaCalculus.Term

universe u
variable {α : Type u} [Name α]

theorem identity (a : α) (s : Term α) : app (lam a (var a)) s ⇉ s := by
  simpa using Parallel.beta a (Parallel.var a) (Parallel.refl s)

/-- Both inputs genuinely contract, and the free replacement atom survives. -/
theorem bothContract (a b c x : α) :
    app (lam a (var a)) (var x) ≠ var x ∧
      app (lam c (var c)) (var b) ≠ var b ∧
      (app (lam a (var a)) (var x))[x := app (lam c (var c)) (var b)] ⇉
        (var x)[x := var b] ∧
      ¬ b # (var x)[x := var b] := by
  exact ⟨app_ne_var _ _ _, app_ne_var _ _ _,
    (identity a (var x)).subst (identity c (var b)) x, by simp⟩

/-- The subject reduces below `b`, while the replacement reduces to the free
atom `b`. Computing the target requires changing the binder to `c`; the final
freshness assertion rules out capturing that free occurrence. -/
theorem captureAvoidance (a b c d : α)
    (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b) :
    (lam b (app (lam d (var d)) (var a)))[a := app (lam d (var d)) (var b)] ⇉
        lam c (var b) ∧
      ¬ b # lam c (var b) := by
  have hsubst : (lam b (var a))[a := var b] = lam c (var b) := by
    rw [subst_lam_rename b c (var a) a (var b) (by simpa using hca)]
    have hswap : swap b c • var a = var a := by simp [hab, Ne.symm hca]
    rw [hswap, subst_lam c (var a) a (var b) (by simp [hca, hcb])]
    simp
  refine ⟨?_, by simp [Ne.symm hcb]⟩
  simpa only [hsubst] using
    (Parallel.lam b (identity d (var a))).subst (identity d (var b)) a

/-- The free occurrence of `x` receives the reducing replacement, while both
nested binders named `x` shield their body from substitution. The reduction
inside those binders is still retained. -/
theorem repeatedBinderShadowing (a b x : α) :
    (app (var x) (lam x (lam x (app (lam a (var a)) (var x)))))
        [x := app (lam a (var a)) (var b)] =
        app (app (lam a (var a)) (var b))
          (lam x (lam x (app (lam a (var a)) (var x)))) ∧
      (app (var x) (lam x (lam x (app (lam a (var a)) (var x)))))
        [x := app (lam a (var a)) (var b)] ⇉
        app (var b) (lam x (lam x (var x))) := by
  have hsource :
      (lam x (lam x (app (lam a (var a)) (var x))))
        [x := app (lam a (var a)) (var b)] =
        lam x (lam x (app (lam a (var a)) (var x))) :=
    subst_fresh x _ _ (by simp)
  have htarget : (lam x (lam x (var x)))[x := var b] = lam x (lam x (var x)) :=
    subst_fresh x _ _ (by simp)
  refine ⟨by simp only [subst_app, subst_var, ↓reduceIte, hsource], ?_⟩
  have ht := Parallel.app (Parallel.var x)
    (Parallel.lam x (Parallel.lam x (identity a (var x))))
  simpa only [subst_app, subst_var, ↓reduceIte, htarget] using
    ht.subst (identity a (var b)) x

/-- A fixed arbitrary replacement may contain the identity binder freely. -/
theorem fixedReplacement (a x : α) (s : Term α) :
    (app (lam a (var a)) (var x))[x := s] ⇉ s := by
  simpa using (identity a (var x)).subst_left x s

/-- Reducing a replacement reaches both occurrences in a fixed open subject. -/
theorem fixedSubject (a b x : α) :
    (app (var x) (var x))[x := app (lam a (var a)) (var b)] ⇉
      app (var b) (var b) := by
  simpa using (identity a (var b)).subst_right (app (var x) (var x)) x

/-- The outer contraction has genuine body and argument contractions, and the
replacement genuinely contracts too. Its free `a` collides with the outer
contraction binder. Compatibility computes the two successive substitutions
without requiring that displayed binder to be fresh for the replacement. -/
theorem contractionComposition (a b c d x : α) (hax : a ≠ x) :
    app (lam b (var b)) (app (var a) (var x)) ≠ app (var a) (var x) ∧
      app (lam c (var c)) (var x) ≠ var x ∧
      app (lam d (var d)) (var a) ≠ var a ∧
      (app (lam a (app (lam b (var b)) (app (var a) (var x))))
        (app (lam c (var c)) (var x)))[x := app (lam d (var d)) (var a)] ⇉
        app (var a) (var a) ∧
      ¬ a # app (var a) (var a) := by
  have hbody := identity b (app (var a) (var x))
  have harg := identity c (var x)
  have hreplacement := identity d (var a)
  refine ⟨?_, app_ne_var _ _ _, app_ne_var _ _ _, ?_, by simp⟩
  · intro heq
    exact lam_ne_var _ _ _ (app_inj.mp heq).1
  · simpa [hax, Ne.symm hax] using (Parallel.beta a hbody harg).subst hreplacement x

end LambdaParallelSubstitutionExamples

-- Every consumer rejects admissions and extra axioms. The allowed axioms are
-- exactly the standard foundations used throughout the classical library.
open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "LambdaParallelSubstitutionExamples." then
      let axioms ← collectAxioms name
      let extra := axioms.filter fun a =>
        a != `propext && a != `Classical.choice && a != `Quot.sound
      unless extra.isEmpty do
        throwError "{name}: unexpected axioms {extra}"
