/-
Copyright (c) 2026 Nominal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nominal contributors
-/
import Package.Foundations.PredicateSupport
import Package.Foundations.Quotient
import Mathlib.Data.Setoid.Basic

/-!
# Ordinary predicates on quotients

Compatibility alone gives ordinary predicate descent, via Mathlib's function
universal property and propositional extensionality. No action or finite support
is required. For an invariant relation the explicitly constructed quotient action
makes pullback preserve and reflect every sufficient predicate bound. This is
separate from support inclusion for quotient objects and gives no representative
attaining a class's least support.
-/

namespace NominalPackage.PredicateDescent
universe u v

section Ordinary
variable {X : Type v}

/-- Related representatives satisfy the same proposition. -/
abbrev Compatible (s : Setoid X) (p : X → Prop) : Prop :=
  ∀ x y, s.r x y → (p x ↔ p y)

namespace Compatible
variable {s : Setoid X} {p q : X → Prop}

theorem const (s : Setoid X) (b : Prop) : Compatible s (fun _ => b) :=
  fun _ _ _ => Iff.rfl
theorem not (hp : Compatible s p) : Compatible s (fun x => ¬p x) :=
  fun x y h => not_congr (hp x y h)
theorem and (hp : Compatible s p) (hq : Compatible s q) :
    Compatible s (fun x => p x ∧ q x) := fun x y h => and_congr (hp x y h) (hq x y h)
theorem or (hp : Compatible s p) (hq : Compatible s q) :
    Compatible s (fun x => p x ∨ q x) := fun x y h => or_congr (hp x y h) (hq x y h)
theorem imp (hp : Compatible s p) (hq : Compatible s q) :
    Compatible s (fun x => p x → q x) := fun x y h => imp_congr (hp x y h) (hq x y h)
theorem iff (hp : Compatible s p) (hq : Compatible s q) :
    Compatible s (fun x => p x ↔ q x) := fun x y h => iff_congr (hp x y h) (hq x y h)
end Compatible

theorem compatible_iff_le_ker (s : Setoid X) (p : X → Prop) :
    Compatible s p ↔ s ≤ Setoid.ker p :=
  ⟨fun h x y hxy => propext (h x y hxy), fun h _ _ hxy => Iff.of_eq (h hxy)⟩

theorem compatible_iff_factorsThrough (s : Setoid X) (p : X → Prop) :
    Compatible s p ↔ Function.FactorsThrough p (Quotient.mk s) :=
  ⟨fun h _ _ hxy => propext (h _ _ (Quotient.exact hxy)),
    fun h _ _ hxy => Iff.of_eq (h (Quotient.sound hxy))⟩

/-- Observe a quotient predicate on its representatives. -/
def pullback (s : Setoid X) (P : Quotient s → Prop) : X → Prop := P ∘ Quotient.mk s

@[simp] theorem pullback_apply (s : Setoid X) (P : Quotient s → Prop) (x : X) :
    pullback s P x ↔ P (Quotient.mk s x) := Iff.rfl

theorem compatible_pullback (s : Setoid X) (P : Quotient s → Prop) :
    Compatible s (pullback s P) :=
  fun _ _ hxy => Iff.of_eq (congrArg P (Quotient.sound hxy))

/-- Lift a compatible ordinary predicate using the existing function correspondence. -/
def descend (s : Setoid X) (p : X → Prop) (hp : Compatible s p) : Quotient s → Prop :=
  Setoid.liftEquiv s ⟨p, (compatible_iff_le_ker s p).1 hp⟩

/-- The ordinary function universal property specialized to logical compatibility. -/
def ordinaryEquiv (s : Setoid X) : (Quotient s → Prop) ≃ {p : X → Prop // Compatible s p} :=
  (Setoid.liftEquiv (β := Prop) s).symm.trans
    (Equiv.subtypeEquivRight fun p => (compatible_iff_le_ker s p).symm)

@[simp] theorem descend_mk (s : Setoid X) (p : X → Prop) (hp : Compatible s p) (x : X) :
    descend s p hp (Quotient.mk s x) ↔ p x := Iff.rfl

@[simp] theorem pullback_descend (s : Setoid X) (p : X → Prop) (hp : Compatible s p) :
    pullback s (descend s p hp) = p := rfl

@[simp] theorem descend_pullback (s : Setoid X) (P : Quotient s → Prop) :
    descend s (pullback s P) (compatible_pullback s P) = P :=
  (ordinaryEquiv s).symm_apply_apply P

theorem descend_proof_irrel (s : Setoid X) (p : X → Prop) (h₁ h₂ : Compatible s p) :
    descend s p h₁ = descend s p h₂ := rfl

@[simp] theorem ordinaryEquiv_apply (s : Setoid X) (P : Quotient s → Prop) (x : X) :
    (ordinaryEquiv s P).val x ↔ P (Quotient.mk s x) := Iff.rfl

@[simp] theorem ordinaryEquiv_symm_apply (s : Setoid X)
    (p : {p : X → Prop // Compatible s p}) (x : X) :
    (ordinaryEquiv s).symm p (Quotient.mk s x) ↔ p.val x := Iff.rfl

/-- Compatibility is exactly the existence of a predicate with these representative values. -/
theorem compatible_iff_exists_descend (s : Setoid X) (p : X → Prop) :
    Compatible s p ↔ ∃ P : Quotient s → Prop, ∀ x, P (Quotient.mk s x) ↔ p x := by
  constructor
  · intro hp
    exact ⟨descend s p hp, descend_mk s p hp⟩
  · rintro ⟨P, hP⟩ x y hxy
    rw [← hP x, ← hP y, Quotient.sound hxy]

/-- A predicate distinguishing related representatives cannot descend, regardless of support. -/
theorem cannot_descend (s : Setoid X) (p : X → Prop) {x y : X}
    (hxy : s.r x y) (hx : p x) (hy : ¬p y) :
    ¬ ∃ P : Quotient s → Prop, ∀ z, P (Quotient.mk s z) ↔ p z := by
  intro hP
  exact hy (((compatible_iff_exists_descend s p).2 hP x y hxy).1 hx)
end Ordinary

section CanonicalAction
variable {A : Type u} {X : Type v} [MulAction (Perm A) X]
variable (s : Setoid X) (hs : SMulInvariant (Perm A) s)

/-- The canonical projection reflects every supplied predicate bound. -/
theorem supports_pullback_iff (S : Finset A) (P : Quotient s → Prop) :
    letI := QuotientAction.mulAction s hs
    SupportsPred S (pullback s P) ↔ SupportsPred S P := by
  let _ := QuotientAction.mulAction s hs
  exact supportsPred_pullback_iff (Quotient.mk s) (QuotientAction.equivariant_mk A s hs)
    Quotient.mk_surjective S P

theorem supports_descend_iff (S : Finset A) (p : X → Prop) (hp : Compatible s p) :
    letI := QuotientAction.mulAction s hs
    SupportsPred S (descend s p hp) ↔ SupportsPred S p := by
  let _ := QuotientAction.mulAction s hs
  exact (supports_pullback_iff s hs S (descend s p hp)).symm

theorem finitelySupported_descend_iff (p : X → Prop) (hp : Compatible s p) :
    letI := QuotientAction.mulAction s hs
    FinitelySupportedPred A (descend s p hp) ↔ FinitelySupportedPred A p := by
  let _ := QuotientAction.mulAction s hs
  exact exists_congr fun S => supports_descend_iff s hs S p hp

include hs in
/-- Renaming preserves compatibility for an invariant relation. -/
theorem compatible_rename (p : X → Prop) (hp : Compatible s p) (π : Perm A) :
    Compatible s (renamePred π p) := fun _ _ hxy => hp _ _ (hs π⁻¹ hxy)

theorem descend_rename (p : X → Prop) (hp : Compatible s p) (π : Perm A) :
    letI := QuotientAction.mulAction s hs
    descend s (renamePred π p) (compatible_rename s hs p hp π) =
      renamePred π (descend s p hp) := by
  let _ := QuotientAction.mulAction s hs
  funext q
  induction q using Quotient.inductionOn with
  | h x => rfl
end CanonicalAction
end NominalPackage.PredicateDescent
