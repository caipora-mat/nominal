/-
Copyright (c) 2026 Nominal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nominal contributors
-/
import Instances
import Mathlib.Tactic.SuccessIfFailWithMsg
import Lean.Util.CollectAxioms

/-! Regression clients for explicit support automation and the small `nfun` subset. -/
open Nominal.Core Nominal.Set LambdaCalculus

namespace NFunSupportExamples

variable {α X Y : Type} [Name α] [Nominal α X] [Nominal α Y]

-- Deliberately leave a sibling goal visible to test the tactic's goal isolation.
set_option linter.style.multiGoal false in
theorem siblingGoals :
    supports (∅ : Finset α) (PFun.mk (α := α) (fun x : X => x)) ∧ True := by
  constructor
  supports_nfun
  trivial
theorem rightAssociated (a b c : X) :
    supports (supp a ∪ (supp b ∪ supp c)) (PFun.mk (α := α) (fun _ : X => c)) := by
  supports_nfun from c b a

theorem extraComponent (a c : X) :
    supports (supp a ∪ supp c) (PFun.mk (α := α) (fun _ : X => c)) := by
  supports_nfun from c c

theorem namedSupport (S : Finset α) (c : X) (hc : supp c ⊆ S) :
    supports S (PFun.mk (α := α) (fun _ : X => c)) := by
  supports_nfun from c

theorem collisions (π hπ x _hfix_1 : X) :
    supports (supp π ∪ supp hπ ∪ supp x ∪ supp _hfix_1)
      (PFun.mk (α := α) (fun _ : X => (π, hπ, x, _hfix_1))) := by
  supports_nfun from π hπ x _hfix_1

theorem variableHandler (x : α) (s : Term α) :
    supports ({x} ∪ supp s)
      (PFun.mk (α := α) (fun a : α => if a = x then s else Term.var a)) := by
  supports_nfun from x s

theorem suppliedRule (f : X → Y) (hf : IsEquivariant α f) :
    supports (∅ : Finset α) (PFun.mk (α := α) f) := by
  supports_nfun [hf.map_smul]

theorem supportHypothesis (S : Finset α) (c : X) (hc : supports S c) :
    supports S (PFun.mk (α := α) (fun _ : X => c)) := by
  supports_nfun from c

theorem compoundCaptures (p : X × Y) :
    supports (supp p) (PFun.mk (α := α) (fun _ : X => (p.1, p.2))) := by
  supports_nfun from (p.1) (p.2)

theorem shadowCapture (x : X) : ∀ y : X,
    supports (supp (x, y)) (PFun.mk (α := α) (fun _ : X => y)) := by
  intro x
  -- The two locals share a printed name, but only the visible local is captured.
  supports_nfun from x

theorem nominalApplication (f : NFun α X Y) (c : X) :
    supports (supp f ∪ supp c)
      (PFun.mk (α := α) (fun x : X => (f x, c))) := by
  supports_nfun from f c

theorem evaluation : supports (∅ : Finset α)
    (PFun.mk (α := α) (fun p : NFun α X Y × X =>
      (NFun.eval : NFun α (NFun α X Y × X) Y) p)) := by
  supports_nfun

theorem mappedApplication (f : NFun α X Y) (g : Y → Y) (hg : IsEquivariant α g) :
    supports (supp f) (PFun.mk (α := α) (fun x : X => (f.map g hg) x)) := by
  supports_nfun [hg.map_smul] from f

theorem comappedApplication (f : NFun α X Y) (g : X → X) (hg : IsEquivariant α g) :
    supports (supp f) (PFun.mk (α := α) (fun x : X => (f.comap g hg) x)) := by
  supports_nfun [hg.map_smul] from f

theorem parameterApplication (f : X → X → Y) (hf : IsEquivariant₂ α f) (c : X) :
    supports (supp c) (PFun.mk (α := α) (fun x : X => NFun.fromParam f hf c x)) := by
  supports_nfun [← hf.map_smul] from c

theorem returnedNominal :
    supports (∅ : Finset α)
      (PFun.mk (α := α) (fun x : X => (NFun.const x : NFun α Y X))) := by
  supports_nfun

theorem composeCapture (g : NFun α X X) :
    supports (supp g)
      (PFun.mk (α := α) (fun f : NFun α X X => f.comp g)) := by
  supports_nfun from g

theorem curryHandler : supports (∅ : Finset α)
    (PFun.mk (α := α) (fun f : NFun α (X × X) Y => NFun.curry f)) := by
  supports_nfun

theorem uncurryHandler : supports (∅ : Finset α)
    (PFun.mk (α := α) (fun f : NFun α X (NFun α X Y) => NFun.uncurry f)) := by
  supports_nfun

theorem conditionalReversed (x : α) (s : Term α) :
    supports ({x} ∪ supp s)
      (PFun.mk (α := α) (fun a : α => if x = a then s else Term.var a)) := by
  supports_nfun from x s

set_option linter.unusedVariables false in
theorem insufficientCapture (c : X) :
    supports (∅ : Finset α) (PFun.mk (α := α) (fun x : X => x)) := by
  success_if_fail_with_msg "supports_nfun: cannot prove the support of capture c is contained in the supplied set; provide a local inclusion or support hypothesis"
    supports_nfun from c
  supports_nfun

theorem ordinaryFunctionNeedsProof (f : X → Y) (S : Finset α)
    (hf : supports S (PFun.mk (α := α) f)) :
    supports S (PFun.mk (α := α) f) := by
  fail_if_success supports_nfun
  exact hf

set_option linter.unusedVariables false in
theorem predicateNeedsProof (P : α → Prop) [DecidablePred P] (s t : Term α)
    (S : Finset α) (hs : supp s ⊆ S) (ht : supp t ⊆ S)
    (h : supports S (PFun.mk (α := α) (fun a : α => if P a then s else t))) :
    supports S (PFun.mk (α := α) (fun a : α => if P a then s else t)) := by
  fail_if_success supports_nfun from s t
  exact h

noncomputable def explicitLet (c : X) : NFun α X X :=
  nfun [capturing c] fun _ => let y := c; y

theorem explicitLet_apply (c x : X) : explicitLet c x = c := rfl

noncomputable def explicitMatch (c : X) : NFun α (X × X) X :=
  nfun [capturing c] fun p => match p with | (_, _) => c

theorem explicitMatch_apply (c : X) (p : X × X) : explicitMatch c p = c := rfl

theorem ordinaryGlobalNeedsCertificate (a : α) : (NFun.id : NFun α α α) a = a := by
  fail_if_success have f : NFun α α α := nfun fun x => _root_.id x
  rfl

theorem automaticScopeErrors (c : X) : (NFun.id : NFun α X X) c = c := by
  success_if_fail_with_msg "nfun: automatic captures do not support let, match, or nested functions; use explicit [capturing ...] or NFun.ofCaptures with a proof"
    have f : NFun α X X := nfun fun _ => let y := c; y
  success_if_fail_with_msg "nfun: automatic captures do not support let, match, or nested functions; use explicit [capturing ...] or NFun.ofCaptures with a proof"
    have f : NFun α (X × X) X := nfun fun p => match p with | (x, _) => x
  success_if_fail_with_msg "nfun: automatic captures do not support let, match, or nested functions; use explicit [capturing ...] or NFun.ofCaptures with a proof"
    have f : NFun α X (NFun α X X) := nfun fun _ => nfun fun _ => c
  success_if_fail_with_msg "nfun: automatic construction accepts one binder; use NFun.curry for curried nominal functions"
    have f : NFun α X (NFun α X X) := nfun fun x y => x
  success_if_fail_with_msg "nfun: automatic construction accepts one binder; use NFun.curry for curried nominal functions"
    have f : NFun α X (NFun α X X) := nfun fun (x y : X) => x
  rfl

end NFunSupportExamples

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "NFunSupportExamples." then
      let axioms ← collectAxioms name
      let extra := axioms.filter fun a =>
        a != `propext && a != `Classical.choice && a != `Quot.sound
      unless extra.isEmpty do
        throwError "{name}: unexpected axioms {extra}"
