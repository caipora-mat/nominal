/-
Copyright (c) 2026 Nominal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nominal contributors
-/
import Nominal
import Lean.Util.CollectAxioms

/-!
# Core contracts used by binder clients

Run `lake build Examples` or `lake env lean Examples/CoreContracts.lean`.
These regressions check action-instance coherence and the boundaries between
least support, strong support, cofinite truth, and supported binder elimination.
The generic abstraction and quotient interfaces below share the atom universe.
-/

open Nominal.Core Nominal.Set Nominal.Set.NameAbs

namespace CoreContracts

universe u
variable {α X Y : Type u} [Name α] [Nominal α X] [Nominal α Y]

/-! The action chosen by typeclass search agrees definitionally with the
corresponding nominal action. Finite permutations use conjugation; their
separate multiplication action must not be selected by the nominal interface. -/

theorem atomAction :
    (inferInstance : SMul (FinitePerm α) α) =
      (inferInstance : Nominal α α).toPermType.toSMul := rfl

theorem permutationAction :
    (inferInstance : SMul (FinitePerm α) (FinitePerm α)) =
      (inferInstance : Nominal α (FinitePerm α)).toPermType.toSMul := rfl

theorem permutationMulAction :
    (inferInstance : MulAction (FinitePerm α) (FinitePerm α)) =
      (inferInstance : Nominal α (FinitePerm α)).toPermType.toMulAction := rfl

theorem permutationConjugation (π σ : FinitePerm α) : π • σ = π * σ * π⁻¹ := rfl

theorem productAction :
    (inferInstance : SMul (FinitePerm α) (X × Y)) =
      (inferInstance : Nominal α (X × Y)).toPermType.toSMul := rfl

theorem optionAction :
    (inferInstance : SMul (FinitePerm α) (Option X)) =
      (inferInstance : Nominal α (Option X)).toPermType.toSMul := rfl

theorem pfunAction :
    (inferInstance : SMul (FinitePerm α) (PFun α X Y)) =
      (inferInstance : PermType α (PFun α X Y)).toSMul := rfl

theorem nfunAction :
    (inferInstance : SMul (FinitePerm α) (NFun α X Y)) =
      (inferInstance : Nominal α (NFun α X Y)).toPermType.toSMul := rfl

theorem abstractionAction :
    (inferInstance : SMul (FinitePerm α) (NameAbs α X)) =
      (inferInstance : Nominal α (NameAbs α X)).toPermType.toSMul := rfl

theorem quotientAction (s : Setoid X) [IsEquivariantSetoid α X s] :
    (inferInstance : SMul (FinitePerm α) (Quotient s)) =
      (inferInstance : Nominal α (Quotient s)).toPermType.toSMul := rfl

/-- On ordinary functions the action is pointwise. On `PFun` it also permutes
the input contravariantly, so the identity function is fixed. -/
theorem ordinaryAndConjugation (a b : α) :
    (swap a b • (id : α → α)) a = b ∧
      (swap a b • (PFun.id : PFun α α α)) a = a := by
  constructor
  · change swap a b • a = b
    simp
  · simp

/-- Fixing a finite set as an element need not fix each of its atoms. Thus
least support is not automatically strong support. -/
theorem leastSupportNotStrong (a b : α) (hne : a ≠ b) :
    ¬ StrongSupports (supp ({a, b} : Finset α)) ({a, b} : Finset α) := by
  rw [supp_finset]
  intro h
  have hfix : swap a b • ({a, b} : Finset α) = {a, b} := by
    simp [PermType.finset_smul, Finset.pair_comm]
  have bad := (h (swap a b)).mpr hfix a (by simp)
  exact hne (by simpa using bad.symm)

/-! Some/Any applies to an equivariant relation with all nominal parameters
collected in a context. Fixing those parameters does not require the resulting
predicate to be equivariant without them. No finite exception set is rebuilt. -/

theorem someAnyWithParameters (R : α → X → Y → Prop)
    (hR : EquivariantRel α (fun a (p : X × Y) => R a p.1 p.2)) (x : X) (y : Y) :
    (И a, R a x y) ↔ ∀ a, a # (x, y) → R a x y :=
  someAny_forall (x := (x, y)) hR

theorem oneFreshWitness (R : α → X → Y → Prop)
    (hR : EquivariantRel α (fun a (p : X × Y) => R a p.1 p.2)) (x : X) (y : Y)
    (h : ∃ a, a # (x, y) ∧ R a x y) : ∀ a, a # (x, y) → R a x y :=
  someAny_forall_of_exists (x := (x, y)) hR h

/-- Negation commutes with И under the stated finite/cofinite condition.
An arbitrary predicate on an infinite atom type need not satisfy it. -/
theorem supportedNegation (p : α → Prop)
    (hp : Set.Finite {a | p a} ∨ Set.Finite {a | ¬ p a}) :
    (¬ (И a, p a)) ↔ (И a, ¬ p a) := freshQuantifier_neg hp

/-! Concretion at a different *fresh* binder renames the body. -/

theorem concretionRenames (a b : α) (x : X) (hne : b ≠ a) (hb : b # x) :
    (⟪a⟫ x) ⊙ b = some (swap a b • x) := concreteAt_abs_fresh hne hb

/-! A parameterized elimination example retains an external payload `z` and
rebinds the body. Its result is fresh for the binder only when the binder is
fresh for `z`. The cofinite condition therefore depends on the fixed parameter;
it is not an unconditional freshness claim or an exact support equation. -/

def retainParameter (z : X) (a : α) (y : Y) : X × NameAbs α Y := (z, ⟪a⟫ y)

theorem retainParameterEquivariant (π : FinitePerm α) (z : X) (a : α) (y : Y) :
    retainParameter (π • z) (π • a) (π • y) = π • retainParameter z a y := by
  simp [retainParameter, abs_equivariant]

theorem retainParameterFresh (z : X) : И a, ∀ y : Y, a # retainParameter z a y := by
  exact freshQuantifier_mono
    (fun a ha y => fresh_prod_right.mpr ⟨ha, fresh_binder_abs a y⟩)
    (freshQuantifier_fresh z)

noncomputable def retainLift : X → NameAbs α Y → X × NameAbs α Y :=
  NameAbs.liftFreshParam retainParameter retainParameterEquivariant retainParameterFresh

theorem retainLiftComputes (z : X) : И a, ∀ y : Y,
    retainLift z (⟪a⟫ y) = retainParameter z a y :=
  NameAbs.liftFreshParam_abs retainParameter retainParameterEquivariant retainParameterFresh z

/-- Uniqueness identifies the lift without choosing quotient representatives. -/
theorem retainLift_eq : (retainLift : X → NameAbs α Y → X × NameAbs α Y) =
    fun z w => (z, w) := by
  symm
  exact NameAbs.liftFreshParam_unique retainParameter retainParameterEquivariant
    retainParameterFresh (fun z w => (z, w))
    (fun _ => freshQuantifier_of_forall (fun _ _ => rfl))

end CoreContracts

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "CoreContracts." then
      let axioms ← collectAxioms name
      let extra := axioms.filter fun a =>
        a != `propext && a != `Classical.choice && a != `Quot.sound
      unless extra.isEmpty do
        throwError "{name}: unexpected axioms {extra}"
