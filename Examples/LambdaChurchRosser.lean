/-
Copyright (c) 2026 Nominal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nominal contributors
-/
import Instances
import Lean.Util.CollectAxioms

/-!
# Church–Rosser and normal-form clients

The peak `(λa. a a) ((λb. b) x)` contracts either its outer redex or its
argument. The resulting terms are distinct; the duplicated branch takes two
steps to reach the displayed common reduct `x x`. These are open quotient
terms, and the under-lambda client keeps `x` free as well.

The examples use the public reduction, constructor, substitution, freshness,
and Church–Rosser interfaces. Normal-form uniqueness identifies an arbitrary
normal reduct or normal convertible of this particular source; no existence
or termination assertion is made for arbitrary terms.
-/

namespace LambdaChurchRosserExamples

open Nominal.Core Nominal.Set LambdaCalculus LambdaCalculus.Term

universe u
variable {α : Type u} [Name α]

/-- A displayed identity redex keeps the concrete peak readable. -/
abbrev identityApp (a : α) (s : Term α) : Term α := app (lam a (var a)) s

theorem identity (a : α) (s : Term α) : identityApp a s →β s := by
  simpa [identityApp] using Beta.beta a (var a) s

/-- Contracting the outer redex duplicates an unreduced argument. Contracting
the argument first leaves only one final step. Both routes reach the open
normal form `x x`, and the two immediate reducts are unequal quotient terms. -/
theorem duplicatingPeak (a b x : α) :
    let source := app (lam a (app (var a) (var a))) (identityApp b (var x))
    let left := app (identityApp b (var x)) (identityApp b (var x))
    let right := app (lam a (app (var a) (var a))) (var x)
    let common := app (var x) (var x)
    source →β left ∧ source →β right ∧
      left →β* common ∧ right →β* common ∧ left ≠ right ∧ ¬ x # common := by
  dsimp only
  refine ⟨?_, Beta.app_right _ (identity b (var x)),
    BetaStar.app (BetaStar.single (identity b (var x)))
      (BetaStar.single (identity b (var x))), ?_, ?_, by simp⟩
  · simpa using Beta.beta a (app (var a) (var a)) (identityApp b (var x))
  · apply BetaStar.single
    simpa using Beta.beta a (app (var a) (var a)) (var x)
  · intro heq
    exact app_ne_lam _ _ _ _ (app_inj.mp heq).1

/-- Apply beta confluence to the actual distinct branches of the peak.
`duplicatingPeak` separately identifies an explicit joining term. -/
theorem duplicatingPeakConfluence (a b x : α) :
    ∃ p, app (identityApp b (var x)) (identityApp b (var x)) →β* p ∧
      app (lam a (app (var a) (var a))) (var x) →β* p := by
  obtain ⟨hleft, hright, _, _, _, _⟩ := duplicatingPeak a b x
  exact BetaStar.confluent (BetaStar.single hleft) (BetaStar.single hright)

/-- This conversion travels forward from the duplicated branch to `x x`,
then backwards along the other branch's final contraction. Church–Rosser
recovers a common directed reduct from that two-way conversion. -/
theorem forwardBackwardConversion (a b x : α) :
    let left := app (identityApp b (var x)) (identityApp b (var x))
    let right := app (lam a (app (var a) (var a))) (var x)
    left ≡β right ∧ ∃ p, left →β* p ∧ right →β* p := by
  dsimp only
  obtain ⟨_, _, hleft, hright, _, _⟩ := duplicatingPeak a b x
  have hconvert := (BetaEq.of_betaStar hleft).trans (BetaEq.of_betaStar hright).symm
  exact ⟨hconvert, BetaEq.church_rosser hconvert⟩

/-- Both premises of the parallel contraction are genuine beta steps. The
inclusions serialize the simultaneous contraction into a finite beta sequence. -/
theorem simultaneousContractionSequence (a b c x : α) :
    app (lam a (identityApp b (var a))) (identityApp c (var x)) →β* var x := by
  have hparallel :
      app (lam a (identityApp b (var a))) (identityApp c (var x)) ⇉ var x := by
    simpa using Parallel.beta a (Beta.to_parallel (identity b (var a)))
      (Beta.to_parallel (identity c (var x)))
  exact Parallel.to_betaStar hparallel

/-- The same open peak reduces beneath a lambda. The explicit inequality
ensures that `x` survives freely in the resulting abstraction. -/
theorem openUnderLambda (a b x z : α) (hxz : x ≠ z) :
    lam z (app (lam a (app (var a) (var a))) (identityApp b (var x))) →β*
        lam z (app (var x) (var x)) ∧
      ¬ x # lam z (app (var x) (var x)) := by
  obtain ⟨hleft, _, hjoin, _, _, _⟩ := duplicatingPeak a b x
  exact ⟨BetaStar.lam z ((BetaStar.single hleft).trans hjoin), by simp [hxz]⟩

/-- Constructor inversion rules out reductions in either variable and a head
contraction, establishing normality without inspecting raw representatives. -/
theorem applicationNormal (x y : α) : BetaNormal (app (var x) (var y)) := by
  intro t h
  rcases Beta.app_iff.mp h with ⟨_, h, _⟩ | ⟨_, h, _⟩ | ⟨_, _, heq, _⟩
  · exact Beta.not_var h
  · exact Beta.not_var h
  · exact var_ne_lam _ _ _ heq

/-- Any normal reduct of the duplicating redex is the explicit quotient term
`x x`; the caller need not expose its reduction sequence or normal-form syntax. -/
theorem normalReductUnique (a b x : α) {n : Term α}
    (h : app (lam a (app (var a) (var a))) (identityApp b (var x)) →β* n)
    (hn : BetaNormal n) : n = app (var x) (var x) := by
  obtain ⟨hleft, _, hjoin, _, _, _⟩ := duplicatingPeak a b x
  exact BetaStar.normal_unique h ((BetaStar.single hleft).trans hjoin)
    hn (applicationNormal x x)

/-- Even a normal term reached only by conversion must equal `x x`.
Convertibility may contain backwards steps and need not describe a reduct. -/
theorem convertibleNormalUnique (a b x : α) {n : Term α}
    (h : app (lam a (app (var a) (var a))) (identityApp b (var x)) ≡β n)
    (hn : BetaNormal n) : n = app (var x) (var x) := by
  obtain ⟨hleft, _, hjoin, _, _, _⟩ := duplicatingPeak a b x
  have hconvert := h.symm.trans (BetaEq.of_betaStar ((BetaStar.single hleft).trans hjoin))
  exact BetaEq.normal_unique hconvert hn (applicationNormal x x)

end LambdaChurchRosserExamples

-- Check the headline results explicitly, and reject admissions or custom
-- axioms throughout these clients. The accepted classical foundations are
-- propext, Classical.choice, and Quot.sound.
open Lean Elab Command in
run_cmd do
  let headlines := [
    ``LambdaCalculus.Term.betaStar_iff_parallelStar,
    ``LambdaCalculus.Term.betaStar_eq_parallelStar,
    ``LambdaCalculus.Term.BetaStar.confluent,
    ``LambdaCalculus.Term.BetaEq.church_rosser,
    ``LambdaCalculus.Term.BetaEq.iff_join,
    ``LambdaCalculus.Term.BetaStar.normal_unique,
    ``LambdaCalculus.Term.BetaEq.normal_unique]
  for (name, _) in (← getEnv).constants.toList do
    if name ∈ headlines || name.toString.startsWith "LambdaChurchRosserExamples." then
      let axioms ← collectAxioms name
      let extra := axioms.filter fun a =>
        a != `propext && a != `Classical.choice && a != `Quot.sound
      unless extra.isEmpty do
        throwError "{name}: unexpected axioms {extra}"
