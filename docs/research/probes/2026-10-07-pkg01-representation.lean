import Package
import Mathlib.Order.BooleanSubalgebra
import Mathlib.Order.BooleanAlgebra.Basic

/-! Bounded PKG-01 design probe. No production module imports this file. -/

namespace Pkg01Representation
open NominalPackage
universe u v w z

/--
error: Type mismatch
  p x
has type
  Discrete A Prop
but is expected to have type
  Prop
-/
#guard_msgs (error, drop all) in
#check fun {A : Type u} {X : Type v} [MulAction (Perm A) X]
    (p : SupportedMap A X (Discrete A Prop)) (x : X) => (p x : Prop)

structure Direct (A : Type u) (X : Type v) [MulAction (Perm A) X] : Type v where
  toPred : X → Prop
  supported : FinitelySupportedPred A toPred

namespace Direct
variable {A : Type u} {X : Type v} [MulAction (Perm A) X]

instance : FunLike (Direct A X) X Prop where
  coe p := p.toPred
  coe_injective := by
    rintro ⟨p,hp⟩ ⟨q,hq⟩ h
    cases h
    rfl

@[ext] theorem ext {p q : Direct A X} (h : ∀ x, p x ↔ q x) : p = q :=
  DFunLike.ext p q (fun x => propext (h x))

def ofPred (A : Type u) {X : Type v} [MulAction (Perm A) X]
    (P : X → Prop) (hP : FinitelySupportedPred A P) : Direct A X := ⟨P,hP⟩
@[simp] theorem ofPred_apply (P : X → Prop) (hP : FinitelySupportedPred A P) (x : X) :
    ofPred A P hP x ↔ P x := Iff.rfl
@[simp] theorem coe_ofPred (P : X → Prop) (hP : FinitelySupportedPred A P) :
    (ofPred A P hP : X → Prop) = P := rfl
@[simp] theorem coe_ofPred_exists (P : X → Prop) (hP : ∃ S : Finset A, SupportsPred S P) :
    (ofPred A P hP : X → Prop) = P := rfl
theorem proof_independent (P : X → Prop) (h₁ h₂ : FinitelySupportedPred A P) :
    ofPred A P h₁ = ofPred A P h₂ := rfl

def toMap (p : Direct A X) : SupportedMap A X (Discrete A Prop) :=
  SupportedMap.ofFun A (fun x => Discrete.mk (p x))
    (by obtain ⟨S,hS⟩ := p.supported
        exact ⟨S,(supportsPred_iff_supportsMap S _).1 hS⟩)

def fromMap (p : SupportedMap A X (Discrete A Prop)) : Direct A X :=
  ⟨fun x => (p x).val, by
    obtain ⟨S,hS⟩ := p.certificate
    exact ⟨S,(supportsPred_iff_supportsMap S _).2 hS⟩⟩

def mapEquiv (A : Type u) (X : Type v) [MulAction (Perm A) X] :
    Direct A X ≃ SupportedMap A X (Discrete A Prop) where
  toFun := toMap
  invFun := fromMap
  left_inv _ := rfl
  right_inv _ := by ext x; rfl

def toObject (p : Direct A X) : FunctionObject (Perm A) X (Discrete A Prop) :=
  predicateObject A p

theorem toObject_injective : Function.Injective (toObject : Direct A X → _) := by
  intro p q h
  ext x
  exact Iff.of_eq (congrArg Discrete.val (DFunLike.congr_fun h x))

instance : SMul (Perm A) (Direct A X) where
  smul π p := ⟨renamePred π p, p.supported.rename π⟩

@[simp] theorem toObject_smul (π : Perm A) (p : Direct A X) :
    toObject (π • p) = π • toObject p := rfl

instance : MulAction (Perm A) (Direct A X) :=
  Function.Injective.mulAction toObject toObject_injective toObject_smul

@[simp] theorem smul_apply (π : Perm A) (p : Direct A X) (x : X) :
    (π • p) x ↔ p (π⁻¹ • x) := Iff.rfl

theorem supports_iff (S : Finset A) (p : Direct A X) :
    Supports S p ↔ SupportsPred S (fun x => p x) :=
  (ActionSupport.supports_map_iff toObject toObject_smul toObject_injective
    (S : Set A) p).symm.trans (supportsPred_iff S _).symm

instance : Nominal A (Direct A X) where
  finitelySupported p := by
    obtain ⟨S,hS⟩ := p.supported
    exact ⟨S,(supports_iff S p).2 hS⟩

@[simp] theorem toMap_smul (π : Perm A) (p : Direct A X) :
    toMap (π • p) = π • toMap p := by ext x; rfl

theorem least_support_agrees [Infinite A] (p : Direct A X) :
    support A p = support A p.toMap := by
  apply le_antisymm
  · apply support_minimal A
    apply (supports_iff _ _).2
    apply (supportsPred_iff_supportsMap _ _).2
    exact (SupportedMap.supports_iff _ _).1 (supports_support A p.toMap)
  · apply support_minimal A
    apply (SupportedMap.supports_iff _ _).2
    apply (supportsPred_iff_supportsMap _ _).1
    exact (supports_iff _ _).1 (supports_support A p)

example (p : Direct A X) (x : X) : Prop := p x
example (p q : Direct A X) (h : ∀ x, p x ↔ q x) : p = q := by ext x; exact h x
example (p q : Direct A X) (h : p = q) (x : X) : p x ↔ q x := by rw [h]
example (p : Direct A X) (xs : List X) : xs.map p = xs.map (fun x => p x) := rfl
example (P : X → Prop) (hP : FinitelySupportedPred A P) (xs : List X) :
    xs.map (ofPred A P hP) = xs.map P := by simp
example (p : Direct A X) (x : X) (h : p x ↔ True) : p x := by simp [h]
example (π : Perm A) (p : Direct A X) (x : X) : (π • p) (π • x) ↔ p x := by simp
end Direct

/- A wrapper over SupportedMap also supports ordinary propositions, provided
    its one coercion projects through Discrete.val. -/
structure Wrapped (A : Type u) (X : Type v) [MulAction (Perm A) X] : Type v where
  toMap : SupportedMap A X (Discrete A Prop)

namespace Wrapped
variable {A : Type u} {X : Type v} [MulAction (Perm A) X]
instance : FunLike (Wrapped A X) X Prop where
  coe p x := (p.toMap x).val
  coe_injective := by
    rintro ⟨p⟩ ⟨q⟩ h
    have hpq : p = q := by
      ext x
      exact congrArg Discrete.mk (congrFun h x)
    cases hpq
    rfl
@[ext] theorem ext {p q : Wrapped A X} (h : ∀ x, p x ↔ q x) : p = q :=
  DFunLike.ext p q (fun x => propext (h x))
def ofPred (A : Type u) {X : Type v} [MulAction (Perm A) X]
    (P : X → Prop) (hP : FinitelySupportedPred A P) : Wrapped A X :=
  ⟨(Direct.ofPred A P hP).toMap⟩
@[simp] theorem coe_ofPred (P : X → Prop) (hP : FinitelySupportedPred A P) :
    (ofPred A P hP : X → Prop) = P := rfl
@[simp] theorem coe_ofPred_exists (P : X → Prop) (hP : ∃ S : Finset A, SupportsPred S P) :
    (ofPred A P hP : X → Prop) = P := rfl
example (p : Wrapped A X) (x : X) : Prop := p x
example (p q : Wrapped A X) (h : ∀ x, p x ↔ q x) : p = q := by ext x; exact h x
example (p q : Wrapped A X) (h : p = q) (x : X) : p x ↔ q x := by rw [h]
example (P : X → Prop) (hP : FinitelySupportedPred A P) (xs : List X) :
    xs.map (ofPred A P hP) = xs.map P := by simp
example (P : X → Prop) (h₁ h₂ : FinitelySupportedPred A P) :
    ofPred A P h₁ = ofPred A P h₂ := rfl
end Wrapped

/- Both atom/action choices remain independent during actual renaming. -/
example {A : Type u} {B : Type w} {X : Type v} {Y : Type z}
    [MulAction (Perm A) X] [MulAction (Perm B) Y]
    (p : Direct A X) (q : Direct B Y) (π : Perm A) (σ : Perm B) (x : X) (y : Y) :
    (π • p) (π • x) ∧ (σ • q) (σ • y) ↔ p x ∧ q y := by simp

section GeneralQuantifiers
variable {A : Type u} {X : Type v} {Y : Type w}
variable [MulAction (Perm A) X] [MulAction (Perm A) Y]
variable {S : Finset A} {R : X × Y → Prop}

theorem supports_all (hR : SupportsPred S R) :
    SupportsPred S (fun x => ∀ y, R (x,y)) := by
  intro π hfix x
  constructor
  · intro h y
    exact (hR π hfix (x,y)).1 (h (π • y))
  · intro h y
    simpa using (hR π hfix (x,π⁻¹ • y)).2 (h _)

theorem supports_exists (hR : SupportsPred S R) :
    SupportsPred S (fun x => ∃ y, R (x,y)) := by
  intro π hfix x
  constructor
  · rintro ⟨y,hy⟩
    exact ⟨π⁻¹ • y,(hR π hfix (x,π⁻¹ • y)).1 (by simpa using hy)⟩
  · rintro ⟨y,hy⟩
    exact ⟨π • y,(hR π hfix (x,y)).2 hy⟩

theorem finite_all (hR : FinitelySupportedPred A R) :
    FinitelySupportedPred A (fun x => ∀ y, R (x,y)) := by
  obtain ⟨S,hS⟩ := hR
  exact ⟨S,supports_all hS⟩

theorem finite_exists (hR : FinitelySupportedPred A R) :
    FinitelySupportedPred A (fun x => ∃ y, R (x,y)) := by
  obtain ⟨S,hS⟩ := hR
  exact ⟨S,supports_exists hS⟩

/- Independent ordinary indexing needs a *uniform* bound, but no action on I. -/
theorem uniform_all {I : Sort z} {P : I → X → Prop}
    (h : ∀ i, SupportsPred S (P i)) : SupportsPred S (fun x => ∀ i, P i x) := by
  intro π hfix x
  exact forall_congr' (fun i => h i π hfix x)

theorem uniform_exists {I : Sort z} {P : I → X → Prop}
    (h : ∀ i, SupportsPred S (P i)) : SupportsPred S (fun x => ∃ i, P i x) := by
  intro π hfix x
  exact exists_congr (fun i => h i π hfix x)

/- Restricted quantifiers use support of the entire implication/conjunction;
    a union bound for R and the guard is only a sufficient constructor. -/
theorem restricted_all_same {D : X × Y → Prop}
    (hD : SupportsPred S D) (hR : SupportsPred S R) :
    SupportsPred S (fun x => ∀ y, D (x,y) → R (x,y)) :=
  supports_all (R := fun xy => D xy → R xy)
    (fun π hfix xy => imp_congr (hD π hfix xy) (hR π hfix xy))

theorem restricted_exists_same {D : X × Y → Prop}
    (hD : SupportsPred S D) (hR : SupportsPred S R) :
    SupportsPred S (fun x => ∃ y, D (x,y) ∧ R (x,y)) :=
  supports_exists (R := fun xy => D xy ∧ R xy)
    (fun π hfix xy => and_congr (hD π hfix xy) (hR π hfix xy))
end GeneralQuantifiers

section ConstructorEvidence
variable {A : Type u} {X : Type v} [MulAction (Perm A) X]
example (P : X → Prop) (S : Finset A) (hS : SupportsPred S P) (xs : List X) :
    xs.map (Direct.ofPred A P ⟨S,hS⟩) = xs.map P := by simp
example (P : X → Prop) (S : Finset A) (hS : SupportsPred S P) (xs : List X) :
    xs.map (Wrapped.ofPred A P ⟨S,hS⟩) = xs.map P := by simp
example (P : X → Prop) {S T : Finset A} (hS : SupportsPred S P) (hST : S ⊆ T) :
    Direct.ofPred A P ⟨S,hS⟩ = Direct.ofPred A P ⟨T,hS.mono hST⟩ := rfl
end ConstructorEvidence

section SubsetAndAlgebra
variable {A : Type u} {X : Type v} [MulAction (Perm A) X]

abbrev SupportedSubset (A : Type u) (X : Type v) [MulAction (Perm A) X] :=
  {U : Set X // FinitelySupportedPred A (fun x => x ∈ U)}

/--
error: Function expected at
  p
but this term has type
  SupportedSubset A X

Note: Expected a function because this term is being applied to the argument
  x
-/
#guard_msgs (error, drop all) in
#check fun (p : SupportedSubset A X) (x : X) => (p x : Prop)

/- Bare subtype fails ordinary p x and List.map p. An explicit FunLike repairs it. -/
instance : FunLike (SupportedSubset A X) X Prop where
  coe p x := x ∈ p.val
  coe_injective := by
    intro p q h
    apply Subtype.ext
    exact h
example (p : SupportedSubset A X) (x : X) : Prop := p x
example (p q : SupportedSubset A X) (h : ∀ x, p x ↔ q x) : p = q := by ext x; exact h x
example (p q : SupportedSubset A X) (h : p = q) (x : X) : p x ↔ q x := by rw [h]
example (p : SupportedSubset A X) (xs : List X) : xs.map p = xs.map (fun x => p x) := rfl

theorem supports_not {S : Finset A} {P : X → Prop} (h : SupportsPred S P) :
    SupportsPred S (fun x => ¬ P x) := fun π hfix x => not_congr (h π hfix x)

theorem finite_not {P : X → Prop} (h : FinitelySupportedPred A P) :
    FinitelySupportedPred A (fun x => ¬ P x) := by
  obtain ⟨S,hS⟩ := h
  exact ⟨S,supports_not hS⟩

theorem finite_and {P Q : X → Prop} (hP : FinitelySupportedPred A P)
    (hQ : FinitelySupportedPred A Q) : FinitelySupportedPred A (fun x => P x ∧ Q x) := by
  classical
  obtain ⟨S,hS⟩ := hP
  obtain ⟨T,hT⟩ := hQ
  exact ⟨S ∪ T,fun π hfix x => and_congr
    (hS π (fun a ha => hfix a (Finset.mem_union_left T ha)) x)
    (hT π (fun a ha => hfix a (Finset.mem_union_right S ha)) x)⟩

theorem finite_or {P Q : X → Prop} (hP : FinitelySupportedPred A P)
    (hQ : FinitelySupportedPred A Q) : FinitelySupportedPred A (fun x => P x ∨ Q x) := by
  classical
  obtain ⟨S,hS⟩ := hP
  obtain ⟨T,hT⟩ := hQ
  exact ⟨S ∪ T,fun π hfix x => or_congr
    (hS π (fun a ha => hfix a (Finset.mem_union_left T ha)) x)
    (hT π (fun a ha => hfix a (Finset.mem_union_right S ha)) x)⟩

def supportedSets (A : Type u) (X : Type v) [MulAction (Perm A) X] :
    BooleanSubalgebra (Set X) where
  carrier := {U | FinitelySupportedPred A (fun x => x ∈ U)}
  supClosed' := fun _ hp _ hq => finite_or hp hq
  infClosed' := fun _ hp _ hq => finite_and hp hq
  compl_mem' := fun hp => finite_not hp
  bot_mem' := ⟨∅,fun _ _ _ => Iff.rfl⟩

def subsetEquiv (A : Type u) (X : Type v) [MulAction (Perm A) X] :
    Direct A X ≃ supportedSets A X where
  toFun p := ⟨{x | p x},p.supported⟩
  invFun p := ⟨fun x => x ∈ p.val,p.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/- Two Mathlib reuse routes: inherit the subtype algebra directly, or transfer
    it along this equivalence. This does not prove algebraic laws anew. -/
noncomputable abbrev directBooleanAlgebra (A : Type u) (X : Type v)
    [MulAction (Perm A) X] : BooleanAlgebra (Direct A X) :=
  (subsetEquiv A X).booleanAlgebra

example : BooleanAlgebra (supportedSets A X) := inferInstance
example (p q : Direct A X) (x : X) :
    letI := directBooleanAlgebra A X
    (p ⊓ q) x ↔ p x ∧ q x := Iff.rfl
example (p q : Direct A X) (x : X) :
    letI := directBooleanAlgebra A X
    (p ⇨ q) x ↔ (p x → q x) := Iff.rfl
example (p : Direct A X) (x : X) :
    letI := directBooleanAlgebra A X
    pᶜ x ↔ ¬ p x := Iff.rfl
end SubsetAndAlgebra

section ParticularParameters
/- FunctionObject contains unsupported values; no nominality of this carrier
    is used. Its identity nevertheless has an individual empty certificate. -/
def supportedNonnominalParameter (A : Type u) :
    FunctionObject (Perm A) (Perm A) (Perm A) := FunctionObject.id (Perm A) (Perm A)

theorem parameter_has_support (A : Type u) :
    FinitelySupported A (supportedNonnominalParameter A) :=
  ⟨∅,fun π _ => FunctionObject.smul_id π⟩

example (A : Type u) {X : Type v} [MulAction (Perm A) X]
    (R : FunctionObject (Perm A) (Perm A) (Perm A) × X → Prop)
    (hR : ∀ (π : Perm A) q, R (π • q) ↔ R q) :
    FinitelySupportedPred A (fun x => R (supportedNonnominalParameter A,x)) :=
  ⟨∅, supportsPred_section_of_invariant hR
    (fun π _ => FunctionObject.smul_id π)⟩

theorem regular_one_not_supported {A : Type u} [Infinite A] :
    ¬ FinitelySupported A (1 : Perm A) := by
  classical
  rintro ⟨S,hS⟩
  obtain ⟨a,ha⟩ := Finset.exists_notMem S
  obtain ⟨b,hb⟩ := Finset.exists_notMem (insert a S)
  have hfix : ∀ c ∈ S, Perm.swap a b c = c := fun c hc =>
    Perm.swap_apply_of_ne_of_ne (fun he => ha (he ▸ hc))
      (fun he => hb (Finset.mem_insert_of_mem (he ▸ hc)))
  have he : Perm.swap a b = 1 := by simpa using hS (Perm.swap a b) hfix
  have hab : b = a := by simpa using congrArg (fun π : Perm A => π a) he
  exact hb (hab ▸ Finset.mem_insert_self a S)

theorem parameter_carrier_not_nominal {A : Type u} [Infinite A] :
    ¬ Nominal A (FunctionObject (Perm A) (Perm A) (Perm A)) := by
  intro hN
  let := hN
  have hc := (finitelySupportedMap_iff A _).2
    (Nominal.finitelySupported (A := A) (FunctionObject.const (Perm A) (Perm A) (1 : Perm A)))
  exact regular_one_not_supported ((finitelySupportedMap_const_iff _).1 hc)

example {A : Type u} {X : Type v} [Infinite A] [MulAction (Perm A) X]
    {S : Finset A} (R : X × FunctionObject (Perm A) (Perm A) (Perm A) → Prop)
    (hR : SupportsPred S R) :
    ¬ Nominal A (FunctionObject (Perm A) (Perm A) (Perm A)) ∧
      SupportsPred S (fun x => ∀ F, R (x,F)) ∧
      SupportsPred S (fun x => ∃ F, R (x,F)) :=
  ⟨parameter_carrier_not_nominal, supports_all hR, supports_exists hR⟩

theorem fixed_atom_supported_noninvariant {A : Type u} [DecidableEq A]
    (a b : A) (hab : a ≠ b) :
    FinitelySupportedPred A (fun x : A => x = a) ∧
    ¬ SupportsPred (∅ : Finset A) (fun x : A => x = a) := by
  refine ⟨⟨{a},(supportsPred_eq_iff _ a).2 (supports_atom A a)⟩,?_⟩
  intro h
  have hfix := (supports_empty_iff a).1 ((supportsPred_eq_iff _ a).1 h) (Perm.swap a b)
  exact hab (by simpa only [Perm.smul_atom,Perm.swap_apply_left] using hfix.symm)

/- The general quantification proof includes IsEmpty Y without a separate
    branch or support/equivariance evidence for individual y. -/
example {A : Type u} {X : Type v} {Y : Type w}
    [MulAction (Perm A) X] [MulAction (Perm A) Y] [IsEmpty Y]
    (R : X × Y → Prop) : FinitelySupportedPred A (fun x => ∀ y, R (x,y)) :=
  finite_all ⟨∅,fun _ _ xy => isEmptyElim xy.2⟩
end ParticularParameters

section SupportedCollections
variable {A : Type u} {X : Type v} [MulAction (Perm A) X]
variable {S : Finset A} (C : Direct A (Direct A X))
theorem collection_union_bound (hC : SupportsPred S (fun p => C p)) :
    SupportsPred S (fun x => ∃ p : Direct A X, C p ∧ p x) :=
  supports_exists (R := fun xp : X × Direct A X => C xp.2 ∧ xp.2 xp.1)
    (fun π hfix xp => and_congr (hC π hfix xp.2) (by simp))
theorem collection_intersection_bound (hC : SupportsPred S (fun p => C p)) :
    SupportsPred S (fun x => ∀ p : Direct A X, C p → p x) :=
  supports_all (R := fun xp : X × Direct A X => C xp.2 → xp.2 xp.1)
    (fun π hfix xp => imp_congr (hC π hfix xp.2) (by simp))
end SupportedCollections

-- An explicit surplus atom in the bound is harmless, and the logical
-- certificate supplies the renamed conclusion rather than merely existing.
theorem nonminimal_logic_consumer (π : Perm Nat)
    (hπ : ∀ a ∈ ({0,1,2} : Finset Nat), π a = a) :
    SupportsPred ({0,1,2} : Finset Nat) (fun n : Nat => n = 0 ∨ n = 1) ∧
      ((π • (0 : Nat)) = 0 ∨ (π • (0 : Nat)) = 1) := by
  have h0 : SupportsPred ({0,1,2} : Finset Nat) (fun n : Nat => n = 0) :=
    (supportsPred_eq_iff _ _).2 (supports_mono (by simp) (supports_atom Nat 0))
  have h1 : SupportsPred ({0,1,2} : Finset Nat) (fun n : Nat => n = 1) :=
    (supportsPred_eq_iff _ _).2 (supports_mono (by simp) (supports_atom Nat 1))
  have hOr : SupportsPred ({0,1,2} : Finset Nat) (fun n : Nat => n = 0 ∨ n = 1) :=
    fun σ hσ n => or_congr (h0 σ hσ n) (h1 σ hσ n)
  exact ⟨hOr, (hOr π hπ 0).2 (Or.inl rfl)⟩

#check Direct
#check Wrapped
#print axioms Direct.mapEquiv
#print axioms Direct.least_support_agrees
#print axioms supports_all
#print axioms supports_exists
#print axioms restricted_all_same
#print axioms uniform_all
#print axioms supportedSets
#print axioms directBooleanAlgebra
#print axioms fixed_atom_supported_noninvariant
#print axioms parameter_has_support
#print axioms parameter_carrier_not_nominal
#print axioms collection_union_bound
#print axioms collection_intersection_bound
#print axioms nonminimal_logic_consumer
end Pkg01Representation
