/-
Copyright (c) 2026 Nominal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nominal contributors
-/
import Package.Foundations.FunctionSupport

/-!
# Support of ordinary predicates

Predicates remain functions into Prop. Their logical support certificates use
Iff, without an action on bare Prop. A discrete-truth function object and the
scoped Set image action give proved semantic views. Logical operations and
quotient-predicate descent are separate interfaces.
-/

namespace NominalPackage
universe u v w z

/-- An ordinary predicate is invariant under permutations fixing this bound. -/
def SupportsPred {A : Type u} {X : Type v} [MulAction (Perm A) X]
    (S : Finset A) (P : X → Prop) : Prop :=
  ∀ π : Perm A, (∀ a ∈ S, π a = a) → ∀ x, P (π • x) ↔ P x

/-- Existence of a finite logical support bound for an ordinary predicate. -/
def FinitelySupportedPred (A : Type u) {X : Type v} [MulAction (Perm A) X]
    (P : X → Prop) : Prop := ∃ S : Finset A, SupportsPred S P

/-- Inverse precomposition, without changing the action on ordinary arrows. -/
def renamePred {A : Type u} {X : Type v} [MulAction (Perm A) X]
    (π : Perm A) (P : X → Prop) : X → Prop := fun x => P (π⁻¹ • x)

/-- The atom argument selects the conjugation carrier; truth values are explicitly discrete. -/
def predicateObject (A : Type u) {X : Type v} (P : X → Prop) :
    FunctionObject (Perm A) X (Discrete A Prop) := FunctionObject.ofFun (Perm A) (fun x => Discrete.mk (P x))

@[simp] theorem predicateObject_apply (A : Type u) {X : Type v} (P : X → Prop) (x : X) :
    predicateObject A P x = Discrete.mk (P x) := rfl
@[simp] theorem predicateObject_val (A : Type u) {X : Type v} (P : X → Prop) (x : X) :
    (predicateObject A P x).val = P x := rfl

/-- Ordinary predicates and full discrete-truth function objects contain the same information. -/
def predicateObjectEquiv (A : Type u) (X : Type v) :
    (X → Prop) ≃ FunctionObject (Perm A) X (Discrete A Prop) where
  toFun := predicateObject A
  invFun F x := (F x).val
  left_inv _ := rfl
  right_inv F := by ext x; rfl

variable {A : Type u} {X : Type v} {Y : Type w}
variable [MulAction (Perm A) X] [MulAction (Perm A) Y]
variable {S T : Finset A} {P : X → Prop}

@[simp] theorem renamePred_one (P : X → Prop) : renamePred (1 : Perm A) P = P := by
  funext x; simp [renamePred]
theorem renamePred_mul (π σ : Perm A) (P : X → Prop) :
    renamePred (π * σ) P = renamePred π (renamePred σ P) := by
  funext x; simp only [renamePred, mul_inv_rev, mul_smul]
@[simp] theorem renamePred_apply_smul (π : Perm A) (P : X → Prop) (x : X) :
    renamePred π P (π • x) ↔ P x := by simp [renamePred]
theorem renamePred_eq_arrowAction (π : Perm A) (P : X → Prop) :
    renamePred π P = @SMul.smul (Perm A) (X → Prop) arrowAction.toSMul π P := rfl

theorem predicateObject_rename (π : Perm A) (P : X → Prop) :
    predicateObject A (renamePred π P) = π • predicateObject A P := rfl

theorem supportsPred_iff_supportsMap (S : Finset A) (P : X → Prop) :
    SupportsPred S P ↔ SupportsMap S (fun x => (Discrete.mk (P x) : Discrete A Prop)) := by
  constructor
  · intro h π hfix x
    exact congrArg Discrete.mk (propext (h π hfix x))
  · intro h π hfix x
    exact Iff.of_eq (congrArg Discrete.val (h π hfix x))

theorem supportsPred_iff (S : Finset A) (P : X → Prop) :
    SupportsPred S P ↔ Supports S (predicateObject A P) :=
  (supportsPred_iff_supportsMap S P).trans (supportsMap_iff S _)

theorem finitelySupportedPred_iff (A : Type u) {X : Type v} [MulAction (Perm A) X] (P : X → Prop) :
    FinitelySupportedPred A P ↔ FinitelySupported A (predicateObject A P) :=
  exists_congr fun S => supportsPred_iff S P

theorem SupportsPred.mono (hP : SupportsPred S P) (hST : S ⊆ T) : SupportsPred T P :=
  (supportsPred_iff T P).2 (supports_mono hST ((supportsPred_iff S P).1 hP))
theorem SupportsPred.finitelySupported (hP : SupportsPred S P) : FinitelySupportedPred A P := ⟨S, hP⟩
theorem supportsPred_empty_iff (A : Type u) {X : Type v} [MulAction (Perm A) X] (P : X → Prop) :
    SupportsPred (∅ : Finset A) P ↔ ∀ π : Perm A, ∀ x, P (π • x) ↔ P x := by
  simp only [SupportsPred, Finset.notMem_empty, IsEmpty.forall_iff, implies_true, forall_const]

open scoped Pointwise

/-- This correspondence fixes Mathlib's scoped direct-image Set action. -/
theorem supportsPred_iff_set (S : Finset A) (P : X → Prop) :
    SupportsPred S P ↔ Supports S {x | P x} := by
  constructor
  · intro h π hfix
    ext x
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    simpa only [smul_inv_smul, Set.mem_ofPred_eq] using
      (h π (fun _ ha => hfix ha) (π⁻¹ • x)).symm
  · intro h π hfix x
    have he := congrArg (fun Q : Set X => π • x ∈ Q) (h π (fun _ ha => hfix _ ha))
    simpa only [Set.smul_mem_smul_set_iff, Set.mem_ofPred_eq] using (Iff.of_eq he).symm

section Bounds
variable [DecidableEq A]

theorem supportsPred_smul_iff (π : Perm A) (S : Finset A) (P : X → Prop) :
    SupportsPred (π • S) (renamePred π P) ↔ SupportsPred S P := by
  rw [supportsPred_iff, predicateObject_rename, supports_smul_iff, ← supportsPred_iff]

theorem SupportsPred.precomp {P : Y → Prop} {f : X → Y} (hP : SupportsPred S P) (hf : SupportsMap T f) :
    SupportsPred (S ∪ T) (P ∘ f) := by
  intro π hfix x
  change P (f (π • x)) ↔ P (f x)
  rw [hf π (fun a ha => hfix a (Finset.mem_union_right S ha))]
  exact hP π (fun a ha => hfix a (Finset.mem_union_left T ha)) (f x)

theorem SupportsPred.section {R : Y × X → Prop} {p : Y}
    (hR : SupportsPred S R) (hp : Supports T p) : SupportsPred (S ∪ T) (fun x => R (p,x)) := by
  apply (supportsPred_iff_supportsMap _ _).2
  exact ((supportsPred_iff_supportsMap _ _).1 hR).section hp
end Bounds

/-- Fixing a supported parameter of a jointly invariant predicate needs only its bound. -/
theorem supportsPred_section_of_invariant {R : Y × X → Prop}
    (hR : ∀ (π : Perm A) q, R (π • q) ↔ R q) {p : Y} (hp : Supports S p) :
    SupportsPred S (fun x => R (p,x)) := by
  intro π hfix x
  simpa only [Prod.smul_mk, hp π (fun _ ha => hfix _ ha)] using hR π (p,x)

theorem FinitelySupportedPred.precomp {P : Y → Prop} {f : X → Y}
    (hP : FinitelySupportedPred A P) (hf : FinitelySupportedMap A f) : FinitelySupportedPred A (P ∘ f) := by
  classical
  obtain ⟨S, hS⟩ := hP
  obtain ⟨T, hT⟩ := hf
  exact (hS.precomp hT).finitelySupported

theorem FinitelySupportedPred.section {R : Y × X → Prop} {p : Y}
    (hR : FinitelySupportedPred A R) (hp : FinitelySupported A p) :
    FinitelySupportedPred A (fun x => R (p,x)) := by
  classical
  obtain ⟨S, hS⟩ := hR
  obtain ⟨T, hT⟩ := hp
  exact (hS.section hT).finitelySupported

theorem FinitelySupportedPred.rename (hP : FinitelySupportedPred A P) (π : Perm A) :
    FinitelySupportedPred A (renamePred π P) :=
  (finitelySupportedPred_iff A _).2 (by
    rw [predicateObject_rename]
    exact ((finitelySupportedPred_iff A P).1 hP).smul π)

/-- Equivariant pullback retains the same bound, without requiring surjectivity. -/
theorem SupportsPred.pullback {P : Y → Prop} {q : X → Y}
    (hP : SupportsPred S P) (hq : Equivariant A q) : SupportsPred S (P ∘ q) := by
  classical
  simpa only [Finset.union_empty] using hP.precomp ((supportsMap_empty_iff A q).2 hq)

theorem FinitelySupportedPred.pullback {P : Y → Prop} {q : X → Y}
    (hP : FinitelySupportedPred A P) (hq : Equivariant A q) :
    FinitelySupportedPred A (P ∘ q) := by
  obtain ⟨S, hS⟩ := hP
  exact ⟨S, hS.pullback hq⟩

/-- Surjectivity makes every supplied predicate bound detectable by pullback. -/
theorem supportsPred_pullback_iff (q : X → Y) (hq : Equivariant A q)
    (hsurj : Function.Surjective q) (S : Finset A) (P : Y → Prop) :
    SupportsPred S (P ∘ q) ↔ SupportsPred S P :=
  forall_congr' fun π => forall_congr' fun _ =>
    ActionSupport.invariant_pullback_iff q hsurj π (hq π) P

theorem finitelySupportedPred_pullback_iff (q : X → Y) (hq : Equivariant A q)
    (hsurj : Function.Surjective q) (P : Y → Prop) :
    FinitelySupportedPred A (P ∘ q) ↔ FinitelySupportedPred A P :=
  exists_congr fun S => supportsPred_pullback_iff q hq hsurj S P

theorem renamePred_pullback (q : X → Y) (hq : Equivariant A q)
    (π : Perm A) (P : Y → Prop) : renamePred π P ∘ q = renamePred π (P ∘ q) := by
  funext x
  simp only [renamePred, Function.comp_apply, hq π⁻¹ x]

/-- Exact least support concerns the individually certified predicate objects,
not the ordinary arrows or the support of a representative. -/
theorem FinitelySupportedPred.support_pullback [Infinite A] {P : Y → Prop}
    (hP : FinitelySupportedPred A P) (q : X → Y) (hq : Equivariant A q)
    (hsurj : Function.Surjective q) :
    ((finitelySupportedPred_iff A (P ∘ q)).1 (hP.pullback hq)).support =
      ((finitelySupportedPred_iff A P).1 hP).support := by
  apply le_antisymm
  · apply FinitelySupported.support_minimal
    apply (supportsPred_iff _ _).1
    apply (supportsPred_pullback_iff q hq hsurj _ P).2
    exact (supportsPred_iff _ _).2 (FinitelySupported.supports_support _)
  · apply FinitelySupported.support_minimal
    apply (supportsPred_iff _ _).1
    apply (supportsPred_pullback_iff q hq hsurj _ P).1
    exact (supportsPred_iff _ _).2 (FinitelySupported.supports_support _)

/-- Equality with a fixed value has exactly the sufficient bounds of that value. -/
theorem supportsPred_eq_iff (S : Finset A) (x : X) :
    SupportsPred S (fun y => y = x) ↔ Supports S x := by
  constructor
  · intro h π hfix
    exact (h π (fun _ ha => hfix ha) x).2 rfl
  · intro h π hfix y
    have hx := h π (fun _ ha => hfix _ ha)
    calc
      π • y = x ↔ π • y = π • x := by rw [hx]
      _ ↔ y = x := smul_left_cancel_iff π

/-- The equality-predicate object retains a supported parameter's exact least support. -/
theorem FinitelySupported.support_predicate_eq [Infinite A] {x : X} (hx : FinitelySupported A x) :
    ((finitelySupportedPred_iff A _).1
      (show FinitelySupportedPred A (fun y => y = x) from
        ⟨hx.support, (supportsPred_eq_iff _ _).2 hx.supports_support⟩)).support = hx.support := by
  apply le_antisymm
  · exact FinitelySupported.support_minimal _ ((supportsPred_iff _ _).1
      ((supportsPred_eq_iff _ _).2 hx.supports_support))
  · apply hx.support_minimal
    exact (supportsPred_eq_iff _ _).1 ((supportsPred_iff _ _).2 (FinitelySupported.supports_support _))
end NominalPackage
