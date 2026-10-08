/-
Copyright (c) 2026 Nominal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nominal contributors
-/
import Package.Foundations.PredicateLogic
import Package.Foundations.SupportedFunction
import Mathlib.Order.BooleanSubalgebra

/-!
# Supported predicate values

Ordinary predicates with proof-only finite support have one function coercion,
returning Prop. The named map and full-object views reuse discrete truth and
conjugation from the function theory. Inverse precomposition gives the action;
injective action transfer and support reflection supply its laws and nominality.

The satisfying-set view uses Mathlib's scoped image action. Supported subsets
form a Boolean subalgebra of Set, whose algebra is transferred to the predicate
record. No action on bare Prop, competing Set action, or nominality of the full
powerset is installed. Least support of each full view uses individual evidence.
Atom and carrier universes are independent; basic constructions need only the
selected action on the carrier.
-/

namespace NominalPackage
universe u v

/-- A predicate and proof that some finite supporting bound exists. -/
structure SupportedPred (A : Type u) (X : Type v)
    [MulAction (Perm A) X] : Type v where
  /-- The ordinary logical predicate. -/
  toFun : X → Prop
  /-- Support existence is a proof field; no chosen bound is stored as data. -/
  supported : FinitelySupportedPred A toFun

namespace SupportedPred
variable {A : Type u} {X : Type v} [MulAction (Perm A) X]

instance instFunLike : FunLike (SupportedPred A X) X Prop where
  coe := toFun
  coe_injective := by
    rintro ⟨p, hp⟩ ⟨q, hq⟩ h
    cases h
    rfl

@[ext] theorem ext {p q : SupportedPred A X} (h : ∀ x, p x ↔ q x) : p = q :=
  DFunLike.ext p q (fun x => propext (h x))

theorem congr_apply {p q : SupportedPred A X} (h : p = q) (x : X) : p x ↔ q x :=
  Iff.of_eq (DFunLike.congr_fun h x)

@[simp] theorem mk_apply (p : X → Prop) (hp : FinitelySupportedPred A p) (x : X) :
    (mk p hp : SupportedPred A X) x ↔ p x := Iff.rfl

variable (A) in
/-- Bundle an ordinary predicate with its certificate, without selecting a bound. -/
def ofFun (p : X → Prop) (hp : FinitelySupportedPred A p) : SupportedPred A X := ⟨p, hp⟩

variable (A) in
def ofSupports (p : X → Prop) (S : Finset A) (hp : SupportsPred S p) : SupportedPred A X :=
  ofFun A p hp.finitelySupported

variable (A) in
def ofInvariant (p : X → Prop) (hp : ∀ π : Perm A, ∀ x, p (π • x) ↔ p x) :
    SupportedPred A X :=
  ofSupports A p ∅ ((supportsPred_empty_iff A p).2 hp)

@[simp] theorem ofFun_apply (p : X → Prop) (hp : FinitelySupportedPred A p) (x : X) :
    ofFun A p hp x ↔ p x := Iff.rfl
@[simp] theorem coe_ofFun (p : X → Prop) (hp : FinitelySupportedPred A p) :
    (ofFun A p hp : X → Prop) = p := rfl

/-- The explicit existential binder also lets simp match literal support proofs. -/
@[simp] theorem coe_ofFun_exists (p : X → Prop) (hp : ∃ S : Finset A, SupportsPred S p) :
    (ofFun A p hp : X → Prop) = p := rfl

@[simp] theorem ofSupports_apply (p : X → Prop) (S : Finset A) (hp : SupportsPred S p) (x : X) :
    ofSupports A p S hp x ↔ p x := Iff.rfl
@[simp] theorem coe_ofSupports (p : X → Prop) (S : Finset A) (hp : SupportsPred S p) :
    (ofSupports A p S hp : X → Prop) = p := rfl
@[simp] theorem ofInvariant_apply (p : X → Prop)
    (hp : ∀ π : Perm A, ∀ x, p (π • x) ↔ p x) (x : X) : ofInvariant A p hp x ↔ p x := Iff.rfl
@[simp] theorem coe_ofInvariant (p : X → Prop) (hp : ∀ π : Perm A, ∀ x, p (π • x) ↔ p x) :
    (ofInvariant A p hp : X → Prop) = p := rfl

theorem ofFun_proof_irrel (p : X → Prop) (h₁ h₂ : FinitelySupportedPred A p) :
    ofFun A p h₁ = ofFun A p h₂ := rfl

/-- The full conjugation object, with explicit discrete truth values. -/
def toObject (p : SupportedPred A X) : FunctionObject (Perm A) X (Discrete A Prop) :=
  predicateObject A p

@[simp] theorem toObject_apply (p : SupportedPred A X) (x : X) :
    (p.toObject x).val = p x := rfl

theorem toObject_eq (p : SupportedPred A X) :
    p.toObject = predicateObject A (fun x => p x) := rfl

theorem toObject_injective : Function.Injective (toObject : SupportedPred A X → _) := by
  intro p q h
  exact ext (fun x => Iff.of_eq (congrArg Discrete.val (DFunLike.congr_fun h x)))

theorem toObject_finitelySupported (p : SupportedPred A X) : FinitelySupported A p.toObject :=
  (finitelySupportedPred_iff A _).1 p.supported

/-- The supported-function view; this is a named conversion, not another coercion. -/
def toMap (p : SupportedPred A X) : SupportedMap A X (Discrete A Prop) :=
  ⟨p.toObject, p.toObject_finitelySupported⟩

/-- Read a supported discrete-truth map as an ordinary predicate. -/
def ofMap (F : SupportedMap A X (Discrete A Prop)) : SupportedPred A X :=
  ⟨fun x => (F x).val, by
    obtain ⟨S, hS⟩ := F.certificate
    exact ⟨S, (supportsPred_iff_supportsMap S _).2 hS⟩⟩

@[simp] theorem toMap_apply (p : SupportedPred A X) (x : X) : (p.toMap x).val = p x := rfl
@[simp] theorem ofMap_apply (F : SupportedMap A X (Discrete A Prop)) (x : X) :
    ofMap F x ↔ (F x).val := Iff.rfl
@[simp] theorem toMap_ofMap (F : SupportedMap A X (Discrete A Prop)) : (ofMap F).toMap = F := by
  ext x
  rfl
@[simp] theorem ofMap_toMap (p : SupportedPred A X) : ofMap p.toMap = p := rfl

variable (A X) in
/-- Direct logical storage and the supported discrete-truth map contain the same information. -/
def mapEquiv : SupportedPred A X ≃ SupportedMap A X (Discrete A Prop) where
  toFun := toMap
  invFun := ofMap
  left_inv := ofMap_toMap
  right_inv := toMap_ofMap

/-- The satisfying set, without a second automatic coercion. -/
def toSet (p : SupportedPred A X) : Set X := {x | p x}

@[simp] theorem mem_toSet (p : SupportedPred A X) (x : X) : x ∈ p.toSet ↔ p x := Iff.rfl

private instance instSMul : SMul (Perm A) (SupportedPred A X) where
  smul π p := ⟨renamePred π p, p.supported.rename π⟩

@[simp] theorem toObject_smul (π : Perm A) (p : SupportedPred A X) :
    (π • p).toObject = π • p.toObject := predicateObject_rename π p

instance instMulAction : MulAction (Perm A) (SupportedPred A X) :=
  Function.Injective.mulAction toObject toObject_injective toObject_smul

@[simp] theorem smul_apply (π : Perm A) (p : SupportedPred A X) (x : X) :
    (π • p) x ↔ p (π⁻¹ • x) := Iff.rfl
@[simp] theorem smul_apply_smul (π : Perm A) (p : SupportedPred A X) (x : X) :
    (π • p) (π • x) ↔ p x := renamePred_apply_smul π p x

@[simp] theorem toMap_smul (π : Perm A) (p : SupportedPred A X) :
    (π • p).toMap = π • p.toMap := rfl
@[simp] theorem ofMap_smul (π : Perm A) (F : SupportedMap A X (Discrete A Prop)) :
    ofMap (π • F) = π • ofMap F := rfl

theorem supports_iff_toObject (S : Finset A) (p : SupportedPred A X) :
    Supports S p ↔ Supports S p.toObject :=
  (ActionSupport.supports_map_iff toObject toObject_smul toObject_injective (S : Set A) p).symm

theorem supports_iff (S : Finset A) (p : SupportedPred A X) :
    Supports S p ↔ SupportsPred S (fun x => p x) :=
  (supports_iff_toObject S p).trans (supportsPred_iff S _).symm

theorem supports_iff_toMap (S : Finset A) (p : SupportedPred A X) :
    Supports S p ↔ Supports S p.toMap :=
  (supports_iff_toObject S p).trans (SupportedMap.supports_iff_toObject S p.toMap).symm

instance instNominal : Nominal A (SupportedPred A X) where
  finitelySupported p := by
    obtain ⟨S, hS⟩ := p.supported
    exact ⟨S, (supports_iff S p).2 hS⟩

open scoped Pointwise

@[simp] theorem toSet_smul (π : Perm A) (p : SupportedPred A X) :
    (π • p).toSet = π • p.toSet := by
  ext x
  exact Set.mem_smul_set_iff_inv_smul_mem.symm

/-- Support of the set view always means support under the image action. -/
theorem supports_iff_toSet (S : Finset A) (p : SupportedPred A X) :
    Supports S p ↔ Supports S p.toSet :=
  (supports_iff S p).trans (supportsPred_iff_set S _)

theorem toSet_finitelySupported (p : SupportedPred A X) : FinitelySupported A p.toSet :=
  (Nominal.finitelySupported (A := A) p).map toSet_smul

variable (A) in
/-- Certify a set using the existing Pointwise image action fixed in this signature. -/
def ofSet (U : Set X) (hU : FinitelySupported A U) : SupportedPred A X :=
  ofFun A (fun x => x ∈ U) (by
    obtain ⟨S, hS⟩ := hU
    exact ⟨S, (supportsPred_iff_set S _).2 hS⟩)

@[simp] theorem ofSet_apply (U : Set X) (hU : FinitelySupported A U) (x : X) :
    ofSet A U hU x ↔ x ∈ U := Iff.rfl
@[simp] theorem toSet_ofSet (U : Set X) (hU : FinitelySupported A U) : (ofSet A U hU).toSet = U := rfl
@[simp] theorem ofSet_toSet (p : SupportedPred A X) : ofSet A p.toSet p.toSet_finitelySupported = p := rfl
@[simp] theorem ofSet_smul (π : Perm A) (U : Set X) (hU : FinitelySupported A U) :
    ofSet A (π • U) (hU.smul π) = π • ofSet A U hU := by
  ext x
  exact Set.mem_smul_set_iff_inv_smul_mem

section LeastSupport
variable [Infinite A]

theorem support_toMap (p : SupportedPred A X) : support A p = support A p.toMap :=
  le_antisymm (support_minimal A ((supports_iff_toMap _ p).2 (supports_support A p.toMap)))
    (support_minimal A ((supports_iff_toMap _ p).1 (supports_support A p)))

/-- The full object needs only its elementwise certificate, not nominality of all predicates. -/
theorem support_toObject (p : SupportedPred A X) :
    support A p = p.toObject_finitelySupported.support :=
  p.support_toMap.trans p.toMap.support_toObject

/-- The full powerset is not assumed nominal; this uses the certificate for this set alone. -/
theorem support_toSet (p : SupportedPred A X) : support A p = p.toSet_finitelySupported.support :=
  le_antisymm (support_minimal A ((supports_iff_toSet _ p).2 p.toSet_finitelySupported.supports_support))
    (p.toSet_finitelySupported.support_minimal ((supports_iff_toSet _ p).1 (supports_support A p)))
end LeastSupport

variable (A X) in
/-- Logical closure supplies a subalgebra of Mathlib's ordinary powerset algebra. -/
def supportedSets : BooleanSubalgebra (Set X) where
  carrier := {U | FinitelySupportedPred A (fun x => x ∈ U)}
  supClosed' := fun _ hp _ hq => hp.or hq
  infClosed' := fun _ hp _ hq => hp.and hq
  compl_mem' := fun hp => hp.not
  bot_mem' := FinitelySupportedPred.const A X False

variable (A X) in
/-- The supported-subset view, retaining only proof evidence alongside the satisfying set. -/
def subsetEquiv : SupportedPred A X ≃ supportedSets A X where
  toFun p := ⟨p.toSet, p.supported⟩
  invFun U := ⟨fun x => x ∈ U.val, U.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem mem_subsetEquiv (p : SupportedPred A X) (x : X) :
    x ∈ (subsetEquiv A X p).val ↔ p x := Iff.rfl

private instance instSMulSupportedSets : SMul (Perm A) (supportedSets A X) where
  smul π U := ⟨π • U.val, by
    have hU : FinitelySupported A U.val :=
      (exists_congr (fun S => supportsPred_iff_set S (fun x => x ∈ U.val))).1 U.property
    exact (ofSet A (π • U.val) (hU.smul π)).supported⟩

@[simp] theorem val_smul_supportedSets (π : Perm A) (U : supportedSets A X) :
    (π • U).val = π • U.val := rfl

instance instMulActionSupportedSets : MulAction (Perm A) (supportedSets A X) :=
  Function.Injective.mulAction Subtype.val Subtype.val_injective val_smul_supportedSets

@[simp] theorem subsetEquiv_smul (π : Perm A) (p : SupportedPred A X) :
    subsetEquiv A X (π • p) = π • subsetEquiv A X p :=
  Subtype.ext (toSet_smul π p)

instance instNominalSupportedSets : Nominal A (supportedSets A X) :=
  Equivariant.nominal_of_surjective subsetEquiv_smul (subsetEquiv A X).surjective

theorem support_subsetEquiv [Infinite A] (p : SupportedPred A X) :
    support A p = support A (subsetEquiv A X p) := by
  have h := ActionSupport.supports_map_iff (B := A) (subsetEquiv A X) subsetEquiv_smul
    (subsetEquiv A X).injective
  exact le_antisymm
    (support_minimal A ((h _ p).1 (supports_support A (subsetEquiv A X p))))
    (support_minimal A ((h _ p).2 (supports_support A p)))

/-- One Boolean structure, transferred from the supported-subset subalgebra. -/
instance instBooleanAlgebra : BooleanAlgebra (SupportedPred A X) :=
  (subsetEquiv A X).booleanAlgebra

end SupportedPred
end NominalPackage
