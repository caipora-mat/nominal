/-
Copyright (c) 2026 Nominal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nominal contributors
-/
import Nominal
import Lean.Util.CollectAxioms

/-!
# Supported-function interface regressions

Run `lake env lean Examples/NFun.lean` or `lake build Examples`.
These consumers exercise coercion normalization, higher-order use, captured
parameters, empty domains, and computation without exposing support certificates.
The nominal types and the atom sort are explicit at API boundaries; ordinary
applications, nested extensionality, and higher-order arguments need no wrappers.

## Reproducing the elaboration comparison

The six theorem statements below named `functionEquality`, `curriedFunction`,
`curryAction`, `partialSupport`, `equivariantSupport`, and `nestedExt` are the
benchmark statements. The initial comparison used `Basic.lean` from commit
`0277d3d` and then the updated module, with Lean/Mathlib v4.34.1 and cached
dependencies. Both runs import `Nominal.Set.NFun.Basic` and `Lean.Elab.Tactic`.
Copy those six statements into a standalone file, preserving their generic
`Name`/`Nominal` assumptions. Use these baseline proofs, in the same order:

```lean
by rfl
by rfl
by
  ext x y
  simp
by
  exact (NFun.supp_apply_le f.curry x).trans
    (Finset.union_subset_union_left (NFun.supp_curry_le f))
by exact NFun.supp_eq_empty_iff'.mpr hf.map_smul
by
  ext x y
  exact h x y
```

The updated proofs are the proofs in the named declarations below: `simp`,
`simp`, `simp`, `exact NFun.supp_curry_apply_le f x`, `simp`, and the unchanged
nested `ext` proof. Thus the measured change includes replacing `rfl` with
discoverable simp normalization; it is not a claim that simp beats `rfl`.

For each proof, wrap its tactics in this local instrumentation, using the theorem
name as the label. This counts only tactic execution and leaves heartbeat limits
and elaboration options unchanged; 1000 internal heartbeats equal one unit of
Lean's `maxHeartbeats` option.

```lean
open Lean Elab Tactic in
elab "measure " label:str " => " t:tacticSeq : tactic => do
  let start ← IO.getNumHeartbeats
  evalTactic t
  let finish ← IO.getNumHeartbeats
  logInfo m!"{label.getString}: {finish - start} internal heartbeats"
```

Run each standalone file five times and record all wall times, including process
startup, together with the emitted heartbeat counts. Use separate build/import
directories for the old and new `Basic.olean`; do not overwrite the current
project artifacts. The original baseline used a `/tmp` overlay of cached project
artifacts with only `Basic` rebuilt from the recorded commit and prepended to
`LEAN_PATH`. Preserve both the lean source and output for every run. Process
timings are sensitive to filesystem warming; compare medians and retain outliers.
-/

/-!
The constructor coercion examples below deliberately take a typed
`hf : FinSupported f`. Passing a literal existential witness directly to `mk`
or `ofFun` can expose a transparency mismatch to `simp`. A named theorem with
the `FinSupported` type avoids it; see the conditional handler in the tutorial.
`ofSupports` also avoids this mismatch, but passing a noncomputable support set
as its data argument may require a noncomputable definition.
-/

open Nominal.Core Nominal.Set

namespace NFunExamples

section Generic

variable {α P X Y Z : Type*} [Name α]
variable [Nominal α P] [Nominal α X] [Nominal α Y] [Nominal α Z]

theorem application (f : NFun α X Y) (g : NFun α Y Z) (x : X) :
    (g.comp f) x = g (f x) := by simp

/-- A supported function commutes with swaps outside its support, even when it
is not globally equivariant. This is the iterator's handler-renaming step. -/
theorem freshSwapApplication (f : NFun α X Y) (a b : α) (x : X)
    (ha : a # f) (hb : b # f) : f (swap a b • x) = swap a b • f x :=
  f.apply_smul_of_fixed (swap a b) (fresh_swap ha hb) x

theorem higherOrder (f : NFun α X Y) (g : NFun α Y Z) (xs : List X) :
    xs.map (g.comp f) = (xs.map f).map g := by simp [List.map_map]

theorem functionEquality (f : NFun α X Y) (g : NFun α Y Z) :
    (g.comp f : X → Z) = g ∘ f := by simp

theorem basicCoercions (y : Y) (f : NFun α X Y) (g : NFun α X Z) :
    (NFun.id : X → X) = id ∧
    (NFun.const y : X → Y) = Function.const X y ∧
    (f.prod g : X → Y × Z) = (fun x => (f x, g x)) ∧
    (NFun.eval : (NFun α X Y × X) → Y) = (fun p => p.1 p.2) := by simp

theorem compositionCoercions (f : NFun α X Y) (g : Y → Z) (hg : IsEquivariant α g)
    (h : P → X) (hh : IsEquivariant α h) :
    (f.map g hg : X → Z) = g ∘ f ∧ (f.comap h hh : P → Y) = f ∘ h := by simp

theorem constructorCoercions (f : PFun α X Y) (hf : FinSupported f)
    (s : Finset α) (h : supports s f) :
    (NFun.mk f hf : X → Y) = f ∧
    (NFun.ofSupports f s h : X → Y) = f ∧
    (NFun.ofCaptures f s h : X → Y) = f := by simp

theorem ofFunCoercion (f : X → Y) (h : FinSupported (f : PFun α X Y)) :
    (NFun.ofFun f h : X → Y) = f := by simp

theorem equivariantCoercions (f : X → Y) (hf : IsEquivariant α f) :
    (NFun.equivariant f hf.map_smul : X → Y) = f ∧ (hf.toNFun : X → Y) = f := by simp

theorem explicitSupport (f : PFun α X Y) (s : Finset α) (h : supports s f) :
    supp (NFun.ofSupports f s h) ⊆ s ∧ supp (NFun.ofCaptures f s h) ⊆ s :=
  ⟨NFun.supp_ofSupports_le f s h, NFun.supp_ofCaptures_le f s h⟩

theorem explicitFresh (f : PFun α X Y) (s : Finset α) (h : supports s f)
    (a : α) (ha : a ∉ s) :
    a # NFun.ofSupports f s h ∧ a # NFun.ofCaptures f s h :=
  ⟨NFun.fresh_ofSupports f s h ha, NFun.fresh_ofCaptures f s h ha⟩

theorem pointwiseEquality (f g : NFun α X Y) (h : f = g) (x : X) :
    f x = g x := DFunLike.congr_fun h x

theorem nestedExt (f g : NFun α X (NFun α Y Z))
    (h : ∀ x y, f x y = g x y) : f = g := by
  ext x y
  exact h x y

theorem rewriteLambda (f g : NFun α X Y) (h : f = g) :
    (fun x => f x) = (fun x => g x) := by rw [h]

theorem rewriteHigherOrder (f g : NFun α X Y) (h : f = g) (xs : List X) :
    xs.map f = xs.map g := by rw [h]

theorem curriedFunction (f : NFun α (X × Y) Z) (x : X) :
    (f.curry x : Y → Z) = Function.curry (f : X × Y → Z) x := by simp

theorem uncurriedFunction (f : NFun α X (NFun α Y Z)) :
    (f.uncurry : X × Y → Z) = Function.uncurry (fun x y => f x y) := by simp

theorem curriedHigherOrder (f : NFun α (X × Y) Z) (x : X) (ys : List Y) :
    ys.map (f.curry x) = ys.map (fun y => f (x, y)) := by simp

theorem uncurriedHigherOrder (f : NFun α X (NFun α Y Z)) (ps : List (X × Y)) :
    ps.map f.uncurry = ps.map (fun p => f p.1 p.2) := by simp [Function.uncurry]

theorem curryRoundTrip (f : NFun α X (NFun α Y Z)) :
    f.uncurry.curry = f := by simp

theorem uncurryRoundTrip (f : NFun α (X × Y) Z) :
    f.curry.uncurry = f := by simp

theorem curryAction (f : NFun α (X × Y) Z) (π : FinitePerm α) :
    π • f.curry = (π • f).curry := by simp

theorem uncurryAction (f : NFun α X (NFun α Y Z)) (π : FinitePerm α) :
    π • f.uncurry = (π • f).uncurry := by simp

theorem currySupport (f : NFun α (X × Y) Z) : supp f.curry = supp f := by simp

theorem uncurrySupport (f : NFun α X (NFun α Y Z)) : supp f.uncurry = supp f := by simp

theorem partialSupport (f : NFun α (X × Y) Z) (x : X) :
    supp (f.curry x) ⊆ supp f ∪ supp x := NFun.supp_curry_apply_le f x

theorem partialFresh (f : NFun α (X × Y) Z) (x : X) (a : α)
    (hf : a # f) (hx : a # x) : a # f.curry x := NFun.fresh_curry_apply hf hx

theorem curryFresh (f : NFun α (X × Y) Z) (a : α) :
    a # f.curry ↔ a # f := by simp

theorem uncurryFresh (f : NFun α X (NFun α Y Z)) (a : α) :
    a # f.uncurry ↔ a # f := by simp

theorem equivariantSupport (f : X → Y) (hf : IsEquivariant α f) :
    supp (NFun.equivariant f hf.map_smul) = ∅ := by simp

theorem predicateAdapter (f : X → Y) (hf : IsEquivariant α f) (xs : List X) :
    xs.map hf.toNFun = xs.map f := by simp

theorem parameterApplication (f : P → X → Y) (hf : IsEquivariant₂ α f) (p : P) (x : X) :
    NFun.fromParam f hf p x = f p x := by simp

theorem parameterCoercion (f : P → X → Y) (hf : IsEquivariant₂ α f) (p : P) :
    (NFun.fromParam f hf p : X → Y) = f p := by simp

theorem parameterSupport (f : P → X → Y) (hf : IsEquivariant₂ α f) (p : P) :
    supp (NFun.fromParam f hf p) ⊆ supp p := NFun.supp_fromParam_le f hf p

theorem parameterFresh (f : P → X → Y) (hf : IsEquivariant₂ α f) (p : P) (a : α)
    (ha : a # p) : a # NFun.fromParam f hf p := by
  exact NFun.fresh_fromParam f hf ha

theorem parameterAction (f : P → X → Y) (hf : IsEquivariant₂ α f) (p : P)
    (π : FinitePerm α) : π • NFun.fromParam f hf p = NFun.fromParam f hf (π • p) := by
  simp

-- All generic curry laws above intentionally omit Nonempty assumptions.
theorem emptyDomainConstant [IsEmpty X] (y : Y) :
    supp (NFun.const y : NFun α X Y) = ∅ := by
  apply supp_eq_empty_iff.mpr
  intro π
  ext x
  exact isEmptyElim x

theorem emptyDomainCurry [IsEmpty X] (f : NFun α (X × Y) Z) :
    supp f.curry = ∅ := by
  rw [NFun.supp_curry]
  apply supp_eq_empty_iff.mpr
  intro π
  ext p
  exact isEmptyElim p.1

theorem constantSupport [Nonempty X] (y : Y) :
    supp (NFun.const y : NFun α X Y) = supp y := by simp

end Generic

section Computation

local instance : Name Nat := { dec := inferInstance }

-- A fixed atom is captured, even though the two-argument operation is equivariant.
def captured (a : Nat) : NFun Nat Nat Nat :=
  NFun.fromParam (fun a _ => a) ⟨fun _ _ _ => rfl⟩ a

theorem capturedSupport (a : Nat) : supp (captured a) = {a} := by
  have h : captured a = (NFun.const a : NFun Nat Nat Nat) := by ext x; simp [captured]
  rw [h]
  simp

-- These are computable definitions, rather than noncomputable test wrappers.
def computedConst : Nat := (NFun.const 7 : NFun Nat Nat Nat) 3
def computedComp : Nat := ((NFun.const 7 : NFun Nat Nat Nat).comp NFun.id) 3
def computedCurry : Nat :=
  (NFun.equivariant (fun p : Nat × Nat => p.1) (fun _ _ => rfl)).curry 7 3
def computedUncurry : Nat :=
  (NFun.equivariant (fun p : Nat × Nat => p.1) (fun _ _ => rfl)).curry.uncurry (7, 3)

/-- info: 7 -/
#guard_msgs in
#eval computedConst
/-- info: 7 -/
#guard_msgs in
#eval computedComp
/-- info: 7 -/
#guard_msgs in
#eval computedCurry
/-- info: 7 -/
#guard_msgs in
#eval computedUncurry
/-- info: 7 -/
#guard_msgs in
#eval captured 7 3

end Computation

end NFunExamples

-- Include public laws as well as consumers: reject admissions and custom axioms.
open Lean Elab Command in
run_cmd do
  let publicResults := #[``NFun.curry_uncurry, ``NFun.uncurry_curry,
    ``NFun.supp_curry, ``NFun.supp_uncurry, ``NFun.supp_fromParam_le,
    ``NFun.apply_smul_of_fixed]
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "NFunExamples." || publicResults.contains name then
      let axioms ← collectAxioms name
      let extra := axioms.filter fun a =>
        a != `propext && a != `Classical.choice && a != `Quot.sound
      unless extra.isEmpty do
        throwError "{name}: unexpected axioms {extra}"
