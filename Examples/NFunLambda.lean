/-
Copyright (c) 2026 Nominal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nominal contributors
-/
import Instances.LambdaCalculus.Substitution
import Lean.Util.CollectAxioms

/-!
# Nominal-function clients in the lambda calculus

Compile with `lake build Examples` or `lake env lean Examples/NFunLambda.lean`.
These examples consume supported handlers through the iterator's public equations,
then use substitution as an ordinary function with fixed nominal parameters.
-/

namespace NFunLambdaExamples

open Nominal.Core Nominal.Set LambdaCalculus LambdaCalculus.Term

universe u
variable {α : Type u} [Name α]

def varHandler : NFun α α (Term α) :=
  NFun.equivariant var (fun π a => (smul_var π a).symm)

def appHandler : NFun α (Term α × Term α) (Term α) :=
  NFun.equivariant (fun p => app p.1 p.2) (by intro π p; simp)

def lamHandler : NFun α (α × Term α) (Term α) :=
  NFun.equivariant (fun p => lam p.1 p.2) (by intro π p; simp)

/-- The lam handler satisfies the iterator's condition for every avoidance set. -/
theorem lamHandler_fcb (A : Finset α) :
    ∀ a y, a # A → a # (lamHandler : NFun α (α × Term α) (Term α)) (a, y) :=
  NFun.fcb_of_binder lamHandler (fun a y => fresh_term_lam_of_eq a y) A

noncomputable def rebuild : Term α → Term α :=
  recNoContext varHandler appHandler lamHandler ∅
    (by simp [varHandler]) (by simp [appHandler]) (by simp [lamHandler])
    (lamHandler_fcb ∅)

/-- Constructor handlers are consumed by the iterator, not just applied in isolation. -/
theorem rebuild_app (t s : Term α) : rebuild (app t s) = app (rebuild t) (rebuild s) := by
  simp [rebuild, appHandler]

theorem rebuild_lam (a : α) (t : Term α) : rebuild (lam a t) = lam a (rebuild t) := by
  unfold rebuild
  rw [recNoContext_lam _ _ _ _ _ _ _ _ a t (by simp)]
  rfl

theorem app_partial_support (s : Term α) :
    supp (NFun.curry appHandler s) ⊆ supp s := by
  simpa [appHandler] using NFun.supp_curry_apply_le appHandler s

theorem subst_joint :
    IsEquivariant₂ α (fun (p : α × Term α) (t : Term α) => t[p.1 := p.2]) :=
  ⟨fun π p t => (subst_equivariant π t p.1 p.2).symm⟩

/-- Fixing both nominal substitution parameters yields a supported function. -/
noncomputable def substFixed (x : α) (s : Term α) : NFun α (Term α) (Term α) :=
  NFun.fromParam (fun (p : α × Term α) (t : Term α) => t[p.1 := p.2]) subst_joint (x, s)

@[simp] theorem substFixed_apply (x : α) (s t : Term α) :
    substFixed x s t = t[x := s] := by simp [substFixed]

theorem substFixed_support (x : α) (s : Term α) :
    supp (substFixed x s) ⊆ {x} ∪ supp s := by
  simpa [substFixed, supp_prod, supp_atom] using
    NFun.supp_fromParam_le
      (fun (p : α × Term α) (t : Term α) => t[p.1 := p.2]) subst_joint (x, s)

theorem substFixed_fresh (a x : α) (s : Term α) (ha : a # (x, s)) :
    a # substFixed x s :=
  NFun.fresh_fromParam _ subst_joint ha

/-- Function coercions work as ordinary higher-order arguments. -/
theorem substFixed_higherOrder (x : α) (s : Term α) (ts : List (Term α)) :
    ts.map (substFixed x s) = ts.map (fun t => t[x := s]) := by
  congr 1

/-- Equality of nominal functions rewrites below an ordinary lambda. -/
theorem substFixed_rewrite (x : α) (s : Term α) (f : NFun α (Term α) (Term α))
    (h : substFixed x s = f) : (fun t => t[x := s]) = fun t => f t := by
  change (fun t => substFixed x s t) = _
  rw [h]

theorem substFixed_fresh_input (x : α) (s t : Term α) (h : x # t) :
    substFixed x s t = t := by
  simpa using subst_fresh x t s h

/-- The replacement contains the old binder, so pushing substitution through that
binder would capture its free atom. Rename it to `c` before computing. -/
theorem capture_collision (a b c : α) (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b) :
    (lam b (var a))[a := var b] = lam c (var b) := by
  rw [subst_lam_rename b c (var a) a (var b) (by simpa using hca)]
  have hc : c # (a, var b) :=
    fresh_prod_right.mpr ⟨(fresh_atoms c a).mpr hca, (fresh_term_var c b).mpr hcb⟩
  rw [subst_lam _ _ _ _ hc]
  simp [hab, hca.symm]

end NFunLambdaExamples

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "NFunLambdaExamples." then
      let axioms ← collectAxioms name
      let extra := axioms.filter fun a =>
        a != `propext && a != `Classical.choice && a != `Quot.sound
      unless extra.isEmpty do
        throwError "{name}: unexpected axioms {extra}"
