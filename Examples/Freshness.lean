/-
Copyright (c) 2026 Nominal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nominal contributors
-/
import Nominal
import Mathlib.Tactic.SuccessIfFailWithMsg
import Lean.Util.CollectAxioms

/-!
# Freshness tactic regressions

Compile with `lake build Examples` or `lake env lean Examples/Freshness.lean`.
Each positive theorem consumes the advertised facts. Negative cases check diagnostics
inside completed proofs, and the final audit rejects unexpected axiom dependencies.
-/

open Nominal.Core Nominal.Set

namespace FreshnessExamples

theorem atoms {α : Type} [Name α] (b c : α) : ∃ a : α, a # b ∧ a # c := by
  choose_fresh a
  exact ⟨a, aFresh1, aFresh2⟩

theorem mixed {α X : Type} [Name α] [Nominal α X] (x : X) (b : α) :
    ∃ a : α, a # x ∧ a # b := by
  choose_fresh a
  exact ⟨a, aFresh1, aFresh2⟩

theorem derived {α X : Type} [Name α] [Nominal α X]
    (p : α × X) (t : NameAbs α X) (f : NFun α X X) :
    ∃ a : α, a # p ∧ a # t ∧ a # f := by
  choose_fresh a
  exact ⟨a, aFresh1, aFresh2, aFresh3⟩

theorem shadowAuto {α X : Type} [Name α] [Nominal α X] (x : X) :
    ∀ y : X, ∃ a : α, a # x ∧ a # y := by
  intro x
  choose_fresh a
  exact ⟨a, aFresh1, aFresh2⟩

theorem shadowType {α X : Type} [Name α] [Nominal α X] (x : X) :
    ∀ y : X, ∃ a : α, a # x ∧ a # y := by
  intro x
  choose_fresh a from X
  exact ⟨a, aFresh1, aFresh2⟩

theorem splitRight {α : Type} [Name α] (a b c d : α) (h : a # (b, c, d)) :
    a # b ∧ a # c ∧ a # d := by
  split_fresh h
  fail_if_success have _ := h
  exact ⟨h_1, h_2, h_3⟩

theorem splitLeftAssoc {α : Type} [Name α] (a b c d : α) (h : a # ((b, c), d)) :
    a # b ∧ a # c ∧ a # d := by
  split_fresh h with hb hc hd
  exact ⟨hb, hc, hd⟩

-- Pin the existing indexed convention, including one-element results.
theorem names {α : Type} [Name α] (b : α) : ∃ a : α, a # b := by
  choose_fresh a from b with h
  exact ⟨a, h1⟩

theorem shadowDifferentAuto {α X Y : Type} [Name α] [Nominal α X] [Nominal α Y]
    (x : X) : ∀ y : Y, ∃ a : α, a # x ∧ a # y := by
  intro x
  choose_fresh a
  exact ⟨a, aFresh1, aFresh2⟩

theorem shadowDifferentType {α X Y : Type} [Name α] [Nominal α X] [Nominal α Y]
    (x : X) : ∀ y : Y, ∃ a : α, a # x ∧ a # y := by
  intro x
  choose_fresh a from X Y
  exact ⟨a, aFresh1, aFresh2⟩

theorem explicitMixed {α X : Type} [Name α] [Nominal α X]
    (x x' : X) (b c : α) :
    ∃ a : α, a # b ∧ a # x ∧ a # x' ∧ a # (b, c) ∧ a # x ∧ a # c := by
  choose_fresh a from b X (b, c) x c with hf
  exact ⟨a, hf1, hf2, hf3, hf4, hf5, hf6⟩

theorem explicitDerivedTypes {α X : Type} [Name α] [Nominal α X]
    (p : α × X) (t : NameAbs α X) (f : NFun α X X) :
    ∃ a : α, a # p ∧ a # t ∧ a # f := by
  choose_fresh a from (α × X) (NameAbs α X) (NFun α X X)
  exact ⟨a, aFresh1, aFresh2, aFresh3⟩

theorem internalNames {α : Type} [Name α] (_pfresh _hmem_i : α) :
    ∃ a : α, a # _pfresh ∧ a # _hmem_i ∧ a # _pfresh := by
  choose_fresh a from _pfresh _hmem_i _pfresh
  exact ⟨a, aFresh1, aFresh2, aFresh3⟩

theorem letLocal {α : Type} [Name α] (b : α) : ∃ a : α, a # b ∧ a # (b, b) := by
  let p := (b, b)
  choose_fresh a
  exact ⟨a, aFresh1, aFresh2⟩

theorem singleDefault {α : Type} [Name α] (b : α) : ∃ a : α, a # b := by
  choose_fresh a from b
  exact ⟨a, aFresh1⟩

theorem splitLeftRightAssoc {α : Type} [Name α] (a b c d : α) (h : (a, b, c) # d) :
    a # d ∧ b # d ∧ c # d := by
  split_fresh h with ha hb hc
  exact ⟨ha, hb, hc⟩

theorem splitLeftLeftAssoc {α : Type} [Name α] (a b c d : α) (h : ((a, b), c) # d) :
    a # d ∧ b # d ∧ c # d := by
  split_fresh h
  exact ⟨h_1, h_2, h_3⟩

-- Right-hand components are visited first, then left-hand components.
theorem splitBoth {α : Type} [Name α] (a b c d e : α) (h : ((a, b), c) # (d, e)) :
    a # d ∧ b # d ∧ c # d ∧ a # e ∧ b # e ∧ c # e := by
  split_fresh h with had hbd hcd hae hbe hce
  exact ⟨had, hbd, hcd, hae, hbe, hce⟩

theorem splitBothUnnamed {α : Type} [Name α] (a b c d e : α) (h : (a, b, c) # (d, e)) :
    a # d ∧ b # d ∧ c # d ∧ a # e ∧ b # e ∧ c # e := by
  split_fresh h
  exact ⟨h_1, h_2, h_3, h_4, h_5, h_6⟩

theorem splitCollision {α : Type} [Name α] (a b c : α)
    (h_1 : a # a) (h : a # (b, c)) : a # a ∧ a # b ∧ a # c := by
  split_fresh h
  exact ⟨h_1, h_2, h_3⟩

theorem splitErrors {α : Type} [Name α] (a b c : α) (h : a # (b, c)) :
    a # b ∧ a # c := by
  success_if_fail_with_msg "split_fresh: expected 2 names, got 1"
    split_fresh h with hb
  success_if_fail_with_msg "split_fresh: expected 2 names, got 3"
    split_fresh h with hb hc hd
  success_if_fail_with_msg "split_fresh: name 'hb' is already in use"
    split_fresh h with hb hb
  success_if_fail_with_msg "split_fresh: name 'a' is already in use"
    split_fresh h with a hc
  success_if_fail_with_msg "split_fresh: name 'h' is already in use"
    split_fresh h with h hc
  split_fresh h with hb hc
  success_if_fail_with_msg "split_fresh: hypothesis has no product freshness to split"
    split_fresh hb
  success_if_fail_with_msg "split_fresh: expected a freshness hypothesis"
    split_fresh a
  exact ⟨hb, hc⟩

set_option linter.unusedVariables false in
theorem chooseErrors {α X : Type} [Name α] (b : α) (f : α → α) : ∃ a : α, a # b := by
  success_if_fail_with_msg "choose_fresh: 'b' is already declared in the local context"
    choose_fresh b from b
  success_if_fail_with_msg "choose_fresh: no local declarations of type 'X' found in context"
    choose_fresh a from X
  success_if_fail_with_msg "choose_fresh: no common atom type with Nominal instances for the selected inputs (use 'from' with nominal terms or types having local elements)"
    choose_fresh a from f
  choose_fresh a from b with hf
  success_if_fail_with_msg "choose_fresh: hypothesis name 'hf1' is already in use (use 'with' to change the prefix)"
    choose_fresh c from b with hf
  exact ⟨a, hf1⟩

theorem ambiguity {α β : Type} [Name α] [Name β] (b : α) (c : β) :
    (∃ a : α, a # b) ∧ (∃ a : β, a # c) := by
  success_if_fail_with_msg "choose_fresh: ambiguous atom types [α, β]; use 'from' to select objects with one common atom type"
    choose_fresh a
  success_if_fail_with_msg "choose_fresh: no common atom type with Nominal instances for the selected inputs (use 'from' with nominal terms or types having local elements)"
    choose_fresh a from b c
  constructor
  · choose_fresh a from b
    exact ⟨a, aFresh1⟩
  · choose_fresh a from c
    exact ⟨a, aFresh1⟩

-- An unused Name instance alone does not make the selected inputs ambiguous.
theorem unusedAtomSort {α β : Type} [Name α] [Name β] (b : α) : ∃ a : α, a # b := by
  choose_fresh a
  exact ⟨a, aFresh1⟩

theorem splitProductVariable {α : Type} [Name α] (a : α) (p : α × α) (h : a # p) : a # p.1 ∧ a # p.2 := by
  split_fresh h
  exact ⟨h_1, h_2⟩
theorem competingInstances {α β X : Type} [Name α] [Name β] [Nominal α X] [Nominal β X] (x : X) : x = x := by
  success_if_fail_with_msg "choose_fresh: ambiguous atom types [α, β]; use 'from' to select objects with one common atom type"
    choose_fresh a from x
  rfl

open Lean Meta Elab Tactic in
elab "with_unresolved_local " tac:tactic : tactic => withMainContext do
  let ty ← mkFreshExprMVar (mkSort (.succ .zero))
  let val ← mkFreshExprMVar ty
  let goal ← getMainGoal
  let (_, goal) ← (← goal.assert `unresolved ty val).intro1P
  replaceMainGoal [goal]
  evalTactic tac
  if ← ty.mvarId!.isAssigned then throwError "candidate scan assigned an existing metavariable"
  ty.mvarId!.assign (mkConst ``Bool)
  val.mvarId!.assign (mkConst ``Bool.true)

theorem unresolvedAuto {α X : Type} [Name α] [Nominal α X] (x : X) : ∃ a : α, a # x := by
  with_unresolved_local choose_fresh a
  exact ⟨a, aFresh1⟩
theorem unresolvedType {α X : Type} [Name α] [Nominal α X] (x : X) : ∃ a : α, a # x := by
  with_unresolved_local choose_fresh a from X
  exact ⟨a, aFresh1⟩

-- Proofs, types and ordinary functions are not nominal objects for this scan.
theorem irrelevantLocals {α : Type} [Name α] (b : α) (f : α → α) (h : f b = b) :
    ∃ a : α, a # b ∧ f b = b := by
  choose_fresh a
  exact ⟨a, aFresh1, h⟩

set_option linter.unusedVariables false in
theorem emptyScan {α : Type} [Name α] : (0 : Nat) = 0 := by
  success_if_fail_with_msg "choose_fresh: no common atom type with Nominal instances for the selected inputs (use 'from' with nominal terms or types having local elements)"
    choose_fresh a
  rfl

section Concrete
local instance : Name Nat where
  dec := inferInstance

theorem globalAtomInstance (b : Nat) : ∃ a : Nat, a # b := by
  choose_fresh a
  exact ⟨a, aFresh1⟩
end Concrete

-- A moderately larger persistent case consumes every generated hypothesis.
theorem sixteen {α : Type} [Name α] (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : α) :
    ∃ a : α, a # b0 ∧ a # b1 ∧ a # b2 ∧ a # b3 ∧ a # b4 ∧ a # b5 ∧ a # b6 ∧ a # b7 ∧
      a # b8 ∧ a # b9 ∧ a # b10 ∧ a # b11 ∧ a # b12 ∧ a # b13 ∧ a # b14 ∧ a # b15 := by
  choose_fresh a
  exact ⟨a, aFresh1, aFresh2, aFresh3, aFresh4, aFresh5, aFresh6, aFresh7, aFresh8,
    aFresh9, aFresh10, aFresh11, aFresh12, aFresh13, aFresh14, aFresh15, aFresh16⟩

-- Auxiliary nominal declarations must not change the public output count.
open Lean Meta Elab Tactic in
elab "with_auxiliary_locals " x:term:max tac:tactic : tactic => withMainContext do
  let e ← Term.elabTerm x none
  let mut goal ← getMainGoal
  for kind in #[LocalDeclKind.auxDecl, LocalDeclKind.implDetail] do
    let (fid, next) ← goal.note `hidden e
    goal := next
    goal.setFVarKind fid kind
  replaceMainGoal [goal]
  evalTactic tac

theorem skipAuxiliary {α : Type} [Name α] (b : α) : ∃ a : α, a # b := by
  with_auxiliary_locals b choose_fresh a
  fail_if_success have _ := aFresh2
  exact ⟨a, aFresh1⟩

theorem skipAuxiliaryType {α : Type} [Name α] (b : α) : ∃ a : α, a # b := by
  with_auxiliary_locals b choose_fresh a from α
  fail_if_success have _ := aFresh2
  exact ⟨a, aFresh1⟩

theorem splitReduciblePredicate {α : Type} [Name α] (a b c : α)
    (h : (fun x => x # (b, c)) a) : a # b ∧ a # c := by
  split_fresh h with hb hc
  exact ⟨hb, hc⟩

theorem competingDerivedInstances {α β X : Type} [Name α] [Name β]
    [Nominal α X] [Nominal β X] (p : X × X) : p = p := by
  success_if_fail_with_msg "choose_fresh: ambiguous atom types [α, β]; use 'from' to select objects with one common atom type"
    choose_fresh a from p
  success_if_fail_with_msg "choose_fresh: ambiguous atom types [α, β]; use 'from' to select objects with one common atom type"
    choose_fresh a
  rfl

-- Explicit inputs choose their unique common sort and retain its instances.
theorem commonSort {α β X : Type} [Name α] [Name β]
    [nx : Nominal α X] [Nominal β X] (p : X × X) (b : α) :
    ∃ a : α, @Nominal.Set.Fresh α _ α (X × X) _ (@Nominal.instProd α _ X X nx nx) a p ∧ a # b := by
  choose_fresh a from p b
  exact ⟨a, aFresh1, aFresh2⟩

-- Concrete projections must reduce: downstream rewriting expects the original term.
theorem splitRewrite {α : Type} [Name α] (a b c d : α) (f : α → α)
    (hmap : ∀ x, a # x → x = c) (h : a # (b, d)) : f b = f c := by
  split_fresh h with hb hd
  have hb' := hmap _ hb
  rw [hb']

theorem splitDependent {α : Type} [Name α] (a b c : α) (h : a # (b, c))
    (Q : (a # (b, c)) → Prop) (hq : Q h) : (a # b ∧ a # c) ∧ Q h := by
  split_fresh h
  exact ⟨⟨h_1, h_2⟩, hq⟩

end FreshnessExamples

-- Fail the regression target if any example acquires an admission or a new axiom.
open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "FreshnessExamples." then
      let axioms ← collectAxioms name
      let extra := axioms.filter fun a =>
        a != `propext && a != `Classical.choice && a != `Quot.sound
      unless extra.isEmpty do
        throwError "{name}: unexpected axioms {extra}"

