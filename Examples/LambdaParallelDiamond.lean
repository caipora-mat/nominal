/-
Copyright (c) 2026 Nominal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nominal contributors
-/
import Instances
import Lean.Util.CollectAxioms

/-!
# Explicit parallel-reduction diamonds

The joining edges below are single parallel reductions. The examples retain
open arguments and free atoms, contract different redexes in both premises of
an outer contraction, and align differently named outer lambda binders through
the public alpha-renaming interface.
-/

namespace LambdaParallelDiamondExamples

open Nominal.Core Nominal.Set LambdaCalculus LambdaCalculus.Term

universe u
variable {α : Type u} [Name α]

/-- A displayed identity redex, used only to keep the peaks readable. -/
abbrev identityApp (a : α) (s : Term α) : Term α := app (lam a (var a)) s

theorem identity (a : α) (s : Term α) : identityApp a s ⇉ s := by
  simpa [identityApp] using Parallel.beta a (Parallel.var a) (Parallel.refl s)

/-- One branch contracts the outer application while the other uses application
congruence. The explicit common reduct is `s'`, which may be any open term. -/
theorem mixedPeak (a b : α) {s s' : Term α} (h : s ⇉ s') :
    app (lam a (identityApp b (var a))) s ⇉ s ∧
      app (lam a (identityApp b (var a))) s ⇉ identityApp a s' ∧
      s ⇉ s' ∧ identityApp a s' ⇉ s' := by
  refine ⟨?_, Parallel.app (Parallel.lam a (identity b (var a))) h, h, identity a s'⟩
  simpa using Parallel.beta a (identity b (var a)) (Parallel.refl s)

/-- Apply the general theorem to the mixed peak in both derivation orders.
`mixedPeak` additionally identifies `s'` as an explicit common reduct. -/
theorem mixedPeakBothOrders (a b : α) {s s' : Term α} (h : s ⇉ s') :
    (∃ p, s ⇉ p ∧ identityApp a s' ⇉ p) ∧
      (∃ p, identityApp a s' ⇉ p ∧ s ⇉ p) := by
  obtain ⟨hcontract, hcongruence, _, _⟩ := mixedPeak a b h
  exact ⟨hcontract.diamond hcongruence, hcongruence.diamond hcontract⟩

/-- Both outer steps contract. Their bodies reduce opposite immediate redexes,
and their arguments independently do the same. Simultaneous substitution
compatibility joins these different choices at the displayed open term. -/
theorem bothContract (a b c d x y z w : α) (hxy : x ≠ y) :
    let body := app (identityApp a (var x)) (identityApp b (var y))
    let bodyLeft := app (var x) (identityApp b (var y))
    let bodyRight := app (identityApp a (var x)) (var y)
    let argument := app (identityApp c (var z)) (identityApp d (var w))
    let argumentLeft := app (var z) (identityApp d (var w))
    let argumentRight := app (identityApp c (var z)) (var w)
    let common := app (app (var z) (var w)) (var y)
    app (lam x body) argument ⇉ bodyLeft[x := argumentLeft] ∧
      app (lam x body) argument ⇉ bodyRight[x := argumentRight] ∧
      bodyLeft[x := argumentLeft] ⇉ common ∧
      bodyRight[x := argumentRight] ⇉ common ∧
      bodyLeft ≠ bodyRight ∧ argumentLeft ≠ argumentRight ∧ ¬ y # common := by
  dsimp only
  have hbodyLeft := Parallel.app (identity a (var x)) (Parallel.refl (identityApp b (var y)))
  have hbodyRight := Parallel.app (Parallel.refl (identityApp a (var x))) (identity b (var y))
  have hargumentLeft := Parallel.app (identity c (var z)) (Parallel.refl (identityApp d (var w)))
  have hargumentRight := Parallel.app (Parallel.refl (identityApp c (var z))) (identity d (var w))
  have hbodyLeftJoin := Parallel.app (Parallel.var x) (identity b (var y))
  have hbodyRightJoin := Parallel.app (identity a (var x)) (Parallel.var y)
  have hargumentLeftJoin := Parallel.app (Parallel.var z) (identity d (var w))
  have hargumentRightJoin := Parallel.app (identity c (var z)) (Parallel.var w)
  refine ⟨Parallel.beta x hbodyLeft hargumentLeft,
    Parallel.beta x hbodyRight hargumentRight, ?_, ?_, ?_, ?_, by simp⟩
  · simpa [Ne.symm hxy] using hbodyLeftJoin.subst hargumentLeftJoin x
  · simpa [Ne.symm hxy] using hbodyRightJoin.subst hargumentRightJoin x
  · intro heq
    exact var_ne_app _ _ _ (app_inj.mp heq).1
  · intro heq
    exact var_ne_app _ _ _ (app_inj.mp heq).1

/-- The two lambda branches contract different inner redexes and display
distinct outer binders. Renaming to `b` aligns the first joining edge; the free
atom `x` survives both renaming and reduction. -/
theorem alphaRenamedPeak (a b x : α) (hab : a ≠ b) (hxa : x ≠ a) (hxb : x ≠ b) :
    let source := lam a (app (identityApp a (var a)) (identityApp a (var x)))
    let left := lam a (app (var a) (identityApp a (var x)))
    let right := lam b (app (identityApp b (var b)) (var x))
    let common := lam b (app (var b) (var x))
    a ≠ b ∧ source ⇉ left ∧ source ⇉ right ∧
      left ⇉ common ∧ right ⇉ common ∧ ¬ x # common := by
  dsimp only
  have hsource :
      lam a (app (identityApp a (var a)) (identityApp a (var x))) =
        lam b (app (identityApp b (var b)) (identityApp b (var x))) := by
    simpa [identityApp, hxa, hxb] using
      (lam_eq_swap (a := a) (b := b)
        (t := app (identityApp a (var a)) (identityApp a (var x)))
        (by simp [identityApp, Ne.symm hxb]))
  have hcommon : lam a (app (var a) (var x)) = lam b (app (var b) (var x)) := by
    simpa [hxa, hxb] using
      (lam_eq_swap (a := a) (b := b) (t := app (var a) (var x))
        (by simp [Ne.symm hxb]))
  refine ⟨hab,
    Parallel.lam a (Parallel.app (identity a (var a)) (Parallel.refl (identityApp a (var x)))),
    ?_, ?_, Parallel.lam b (Parallel.app (identity b (var b)) (Parallel.var x)), by simp [hxb]⟩
  · rw [hsource]
    exact Parallel.lam b (Parallel.app (Parallel.refl (identityApp b (var b))) (identity b (var x)))
  · rw [← hcommon]
    exact Parallel.lam a (Parallel.app (Parallel.var a) (identity a (var x)))

/-- Two outer contractions use distinct presentations of the same quotient
abstraction. The first reduces the body; the second reduces the argument. Their
distinct targets join at the free atom `a`, which also occurs in the argument
under the original contraction binder's name. -/
theorem alphaRenamedContractions (a b c : α) (hab : a ≠ b) :
    let argument := identityApp c (identityApp c (var a))
    let source := app (lam a (identityApp a (var a))) argument
    source ⇉ argument ∧ source ⇉ identityApp b (var a) ∧
      argument ⇉ var a ∧ identityApp b (var a) ⇉ var a ∧
      argument ≠ identityApp b (var a) ∧ a ≠ b ∧ ¬ a # var a := by
  dsimp only
  have hhead : lam a (identityApp a (var a)) = lam b (identityApp b (var b)) := by
    simpa [identityApp] using
      (lam_eq_swap (a := a) (b := b) (t := identityApp a (var a))
        (by simp [identityApp]))
  have hargument : identityApp c (identityApp c (var a)) ⇉ var a := by
    simpa using Parallel.beta c (Parallel.var c) (identity c (var a))
  have hidentity : (lam b (var b))[b := var a] = lam b (var b) :=
    subst_fresh b _ _ (by simp)
  refine ⟨?_, ?_, hargument, identity b (var a), ?_, hab, by simp⟩
  · simpa using Parallel.beta a (identity a (var a))
      (Parallel.refl (identityApp c (identityApp c (var a))))
  · rw [hhead]
    simpa only [identityApp, subst_app, hidentity, subst_var, ↓reduceIte] using
      Parallel.beta b (Parallel.refl (identityApp b (var b))) hargument
  · intro heq
    exact app_ne_var _ _ _ (app_inj.mp heq).2

end LambdaParallelDiamondExamples

-- Every example rejects admissions and dependencies beyond the library's
-- standard classical foundations.
open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "LambdaParallelDiamondExamples." then
      let axioms ← collectAxioms name
      let extra := axioms.filter fun a =>
        a != `propext && a != `Classical.choice && a != `Quot.sound
      unless extra.isEmpty do
        throwError "{name}: unexpected axioms {extra}"
