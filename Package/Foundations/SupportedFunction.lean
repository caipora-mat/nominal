/-
Copyright (c) 2026 Nominal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nominal contributors
-/
import Package.Foundations.FunctionSupport
import Mathlib.GroupTheory.GroupAction.SubMulAction

/-!
# Supported function values

Support existence is a proof field, not observable data. Only selected actions
are needed on the domain and codomain. The automatic coercion is to ordinary
functions; `toObject` explicitly exposes the full conjugation carrier.
-/

namespace NominalPackage
universe u v w z t

/-- A function object together with proof-only finite support. -/
structure SupportedMap (A : Type u) (X : Type v) (Y : Type w)
    [MulAction (Perm A) X] [MulAction (Perm A) Y] : Type (max v w) where
  /-- The underlying full function object. -/
  toObject : FunctionObject (Perm A) X Y
  /-- A finite support exists; no bound is stored as data. -/
  supported : FinitelySupported A toObject

namespace SupportedMap
variable {A : Type u} {X : Type v} {Y : Type w} {Z : Type z}
variable [MulAction (Perm A) X] [MulAction (Perm A) Y] [MulAction (Perm A) Z]

instance : FunLike (SupportedMap A X Y) X Y where
  coe F := F.toObject
  coe_injective := by
    rintro ⟨F, hF⟩ ⟨H, hH⟩ he
    have : F = H := DFunLike.coe_injective he
    cases this
    rfl

@[ext] theorem ext {F H : SupportedMap A X Y} (h : ∀ x, F x = H x) : F = H := DFunLike.ext F H h

theorem toObject_injective : Function.Injective (toObject : SupportedMap A X Y → _) := by
  intro F H h
  ext x
  exact DFunLike.congr_fun h x

@[simp] theorem toObject_apply (F : SupportedMap A X Y) (x : X) : F.toObject x = F x := rfl
@[simp] theorem coe_toObject (F : SupportedMap A X Y) : (F.toObject : X → Y) = F := rfl
@[simp] theorem mk_apply (F : FunctionObject (Perm A) X Y) (hF : FinitelySupported A F) (x : X) :
    (mk F hF : SupportedMap A X Y) x = F x := rfl

variable (A) in
/-- Bundle an ordinary map with a certificate, keeping all choices in Prop. -/
def ofFun (f : X → Y) (hf : FinitelySupportedMap A f) : SupportedMap A X Y :=
  ⟨FunctionObject.ofFun (Perm A) f, hf.toObject⟩

variable (A) in
def ofSupports (f : X → Y) (S : Finset A) (hS : SupportsMap S f) : SupportedMap A X Y := ofFun A f ⟨S, hS⟩
variable (A) in
def ofEquivariant (f : X → Y) (hf : Equivariant A f) : SupportedMap A X Y := ofFun A f hf.finitelySupportedMap
variable (A) in
def ofIsEmpty [IsEmpty X] (f : X → Y) : SupportedMap A X Y := ofSupports A f ∅ (supportsMap_of_isEmpty _ _)

@[simp] theorem ofFun_apply (f : X → Y) (hf : FinitelySupportedMap A f) (x : X) : ofFun A f hf x = f x := rfl
@[simp] theorem coe_ofFun (f : X → Y) (hf : FinitelySupportedMap A f) : (ofFun A f hf : X → Y) = f := rfl
@[simp] theorem ofSupports_apply (f : X → Y) (S : Finset A) (hS : SupportsMap S f) (x : X) :
    ofSupports A f S hS x = f x := rfl
@[simp] theorem coe_ofSupports (f : X → Y) (S : Finset A) (hS : SupportsMap S f) :
    (ofSupports A f S hS : X → Y) = f := rfl
@[simp] theorem ofEquivariant_apply (f : X → Y) (hf : Equivariant A f) (x : X) : ofEquivariant A f hf x = f x := rfl
@[simp] theorem coe_ofEquivariant (f : X → Y) (hf : Equivariant A f) : (ofEquivariant A f hf : X → Y) = f := rfl
@[simp] theorem ofIsEmpty_apply [IsEmpty X] (f : X → Y) (x : X) : ofIsEmpty A f x = f x := rfl
@[simp] theorem coe_ofIsEmpty [IsEmpty X] (f : X → Y) : (ofIsEmpty A f : X → Y) = f := rfl

theorem ofFun_proof_irrel (f : X → Y) (h₁ h₂ : FinitelySupportedMap A f) : ofFun A f h₁ = ofFun A f h₂ := rfl

instance : SMul (Perm A) (SupportedMap A X Y) where
  smul π F := ⟨π • F.toObject, F.supported.smul π⟩

@[simp] theorem toObject_smul (π : Perm A) (F : SupportedMap A X Y) : (π • F).toObject = π • F.toObject := rfl

instance : MulAction (Perm A) (SupportedMap A X Y) :=
  Function.Injective.mulAction toObject toObject_injective toObject_smul

@[simp] theorem smul_apply (π : Perm A) (F : SupportedMap A X Y) (x : X) :
    (π • F) x = π • F (π⁻¹ • x) := rfl
@[simp] theorem smul_apply_smul (π : Perm A) (F : SupportedMap A X Y) (x : X) :
    (π • F) (π • x) = π • F x := by simp

theorem supports_iff_toObject (S : Finset A) (F : SupportedMap A X Y) : Supports S F ↔ Supports S F.toObject :=
  (ActionSupport.supports_map_iff toObject toObject_smul toObject_injective (S : Set A) F).symm

theorem supports_iff (S : Finset A) (F : SupportedMap A X Y) : Supports S F ↔ SupportsMap S (fun x => F x) :=
  (supports_iff_toObject S F).trans (supportsMap_iff S _).symm

instance instNominal : Nominal A (SupportedMap A X Y) where
  finitelySupported F := by
    obtain ⟨S, hS⟩ := F.supported
    exact ⟨S, (supports_iff_toObject S F).2 hS⟩

/-- The same finite-support certificate at the ordinary-map boundary. -/
theorem certificate (F : SupportedMap A X Y) : FinitelySupportedMap A (fun x => F x) :=
  (finitelySupportedMap_iff A _).2 F.supported

variable (A X Y) in
/-- Mathlib's invariant-subset construction supplies the supported full carrier. -/
def supportedSubaction : SubMulAction (Perm A) (FunctionObject (Perm A) X Y) where
  carrier := {F | FinitelySupported A F}
  smul_mem' π _ h := h.smul π

variable (A X Y) in
/-- A proof-field record and the supported full subtype are equivalent. -/
def supportedSubtypeEquiv : SupportedMap A X Y ≃ supportedSubaction A X Y where
  toFun F := ⟨F.toObject, F.supported⟩
  invFun F := ⟨F.val, F.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem supportedSubtypeEquiv_smul (π : Perm A) (F : SupportedMap A X Y) :
    supportedSubtypeEquiv A X Y (π • F) = π • supportedSubtypeEquiv A X Y F := rfl

theorem support_toObject [Infinite A] (F : SupportedMap A X Y) : support A F = F.supported.support :=
  le_antisymm (support_minimal A ((supports_iff_toObject _ F).2 F.supported.supports_support))
    (F.supported.support_minimal ((supports_iff_toObject _ F).1 (supports_support A F)))

variable (A X) in
def id : SupportedMap A X X := ofEquivariant A _root_.id (Equivariant.id A)
variable (A X) in
def const (y : Y) (hy : FinitelySupported A y) : SupportedMap A X Y := ofFun A (Function.const X y) (finitelySupportedMap_const hy)
variable (A X) in
def constOfNominal [Nominal A Y] (y : Y) : SupportedMap A X Y := const A X y (Nominal.finitelySupported (A := A) y)
def comp (H : SupportedMap A Y Z) (F : SupportedMap A X Y) : SupportedMap A X Z := ofFun A (H ∘ F) (H.certificate.comp F.certificate)
def pair (F : SupportedMap A X Y) (H : SupportedMap A X Z) : SupportedMap A X (Y × Z) :=
  ofFun A (fun x => (F x,H x)) (F.certificate.pair H.certificate)

theorem equivariant_eval : Equivariant A (fun p : SupportedMap A X Y × X => p.1 p.2) := by intro π p; simp
variable (A X Y) in
def eval : SupportedMap A (SupportedMap A X Y × X) Y := ofEquivariant A _ equivariant_eval

def fromParam {P : Type t} [MulAction (Perm A) P] (E : P × X → Y) (hE : Equivariant A E)
    (p : P) (hp : FinitelySupported A p) : SupportedMap A X Y := ofFun A (fun x => E (p,x)) (hE.finitelySupportedMap_section hp)

@[simp] theorem id_apply (x : X) : id A X x = x := rfl
@[simp] theorem const_apply (y : Y) (hy : FinitelySupported A y) (x : X) : const A X y hy x = y := rfl
@[simp] theorem constOfNominal_apply [Nominal A Y] (y : Y) (x : X) : constOfNominal A X y x = y := rfl
@[simp] theorem comp_apply (H : SupportedMap A Y Z) (F : SupportedMap A X Y) (x : X) : H.comp F x = H (F x) := rfl
@[simp] theorem pair_apply (F : SupportedMap A X Y) (H : SupportedMap A X Z) (x : X) : F.pair H x = (F x,H x) := rfl
@[simp] theorem eval_apply (p : SupportedMap A X Y × X) : eval A X Y p = p.1 p.2 := rfl
@[simp] theorem fromParam_apply {P : Type t} [MulAction (Perm A) P] (E : P × X → Y) (hE : Equivariant A E)
    (p : P) (hp : FinitelySupported A p) (x : X) : fromParam E hE p hp x = E (p,x) := rfl
@[simp] theorem coe_id : (id A X : X → X) = _root_.id := rfl
@[simp] theorem coe_const (y : Y) (hy : FinitelySupported A y) : (const A X y hy : X → Y) = Function.const X y := rfl
@[simp] theorem coe_comp (H : SupportedMap A Y Z) (F : SupportedMap A X Y) : (H.comp F : X → Z) = H ∘ F := rfl
@[simp] theorem coe_pair (F : SupportedMap A X Y) (H : SupportedMap A X Z) :
    (F.pair H : X → Y × Z) = fun x => (F x,H x) := rfl
@[simp] theorem coe_eval : (eval A X Y : SupportedMap A X Y × X → Y) = fun p => p.1 p.2 := rfl
@[simp] theorem coe_fromParam {P : Type t} [MulAction (Perm A) P] (E : P × X → Y) (hE : Equivariant A E)
    (p : P) (hp : FinitelySupported A p) : (fromParam E hE p hp : X → Y) = fun x => E (p,x) := rfl

@[simp] theorem comp_id (F : SupportedMap A X Y) : F.comp (id A X) = F := by ext x; rfl
@[simp] theorem id_comp (F : SupportedMap A X Y) : (id A Y).comp F = F := by ext x; rfl
theorem comp_assoc {W : Type t} [MulAction (Perm A) W] (K : SupportedMap A Z W)
    (H : SupportedMap A Y Z) (F : SupportedMap A X Y) : (K.comp H).comp F = K.comp (H.comp F) := by ext x; rfl
theorem smul_id (π : Perm A) : π • id A X = id A X := by ext x; simp
theorem smul_const (π : Perm A) (y : Y) (hy : FinitelySupported A y) :
    π • const A X y hy = const A X (π • y) (hy.smul π) := by ext x; rfl
theorem smul_comp (π : Perm A) (H : SupportedMap A Y Z) (F : SupportedMap A X Y) :
    π • H.comp F = (π • H).comp (π • F) := by ext x; simp
theorem smul_pair (π : Perm A) (F : SupportedMap A X Y) (H : SupportedMap A X Z) :
    π • F.pair H = (π • F).pair (π • H) := ext (fun _ => rfl)
theorem smul_fromParam {P : Type t} [MulAction (Perm A) P] (E : P × X → Y) (hE : Equivariant A E)
    (π : Perm A) (p : P) (hp : FinitelySupported A p) :
    π • fromParam E hE p hp = fromParam E hE (π • p) (hp.smul π) := by
  ext x
  simpa only [smul_apply, fromParam_apply, Prod.smul_mk, smul_inv_smul] using (hE π (p, π⁻¹ • x)).symm

/-- A nonempty domain lets equality of constants recover equality of values. -/
theorem const_inj [Nonempty X] {y z : Y} (hy : FinitelySupported A y) (hz : FinitelySupported A z) :
    const A X y hy = const A X z hz ↔ y = z := by
  constructor
  · intro h
    obtain ⟨x⟩ := ‹Nonempty X›
    exact DFunLike.congr_fun h x
  · intro h
    subst z
    rfl

section LeastSupport
variable [Infinite A]

theorem support_eq_empty_iff (F : SupportedMap A X Y) : support A F = ∅ ↔ Equivariant A (fun x => F x) := by
  rw [support_toObject]
  exact F.certificate.support_eq_empty_iff
@[simp] theorem support_id : support A (id A X) = ∅ := (support_eq_empty_iff _).2 (Equivariant.id A)
@[simp] theorem support_eval : support A (eval A X Y) = ∅ := (support_eq_empty_iff _).2 equivariant_eval
theorem support_const [Nonempty X] (y : Y) (hy : FinitelySupported A y) : support A (const A X y hy) = hy.support := by
  rw [support_toObject]
  exact FinitelySupportedMap.support_const X hy
theorem support_ofIsEmpty [IsEmpty X] (F : SupportedMap A X Y) : support A F = ∅ :=
  (support_eq_empty_iff _).2 (fun _ x => isEmptyElim x)
theorem support_fromParam_subset {P : Type t} [MulAction (Perm A) P] (E : P × X → Y) (hE : Equivariant A E)
    (p : P) (hp : FinitelySupported A p) : support A (fromParam E hE p hp) ⊆ hp.support :=
  support_minimal A ((supports_iff _ _).2 (hE.supportsMap_section hp.supports_support))

variable [DecidableEq A]
theorem support_apply_subset (F : SupportedMap A X Y) {x : X} (hx : FinitelySupported A x) :
    (F.certificate.apply hx).support ⊆ support A F ∪ hx.support := by
  rw [support_toObject]
  exact F.certificate.support_apply_subset hx
theorem support_comp_subset (H : SupportedMap A Y Z) (F : SupportedMap A X Y) :
    support A (H.comp F) ⊆ support A H ∪ support A F := by
  simp only [support_toObject]
  exact H.certificate.support_comp_subset F.certificate
theorem support_pair (F : SupportedMap A X Y) (H : SupportedMap A X Z) :
    support A (F.pair H) = support A F ∪ support A H := by
  simp only [support_toObject]
  exact F.certificate.support_pair H.certificate
end LeastSupport

theorem freshWith_apply [Infinite A] (F : SupportedMap A X Y) {x : X} (hx : FinitelySupported A x)
    {z : Z} (hz : FinitelySupported A z) (hF : F.supported.FreshWith hz) (hX : hx.FreshWith hz) :
    (F.certificate.apply hx).FreshWith hz := F.certificate.freshWith_apply hx hz hF hX
theorem fresh_apply [Infinite A] (F : SupportedMap A X Y) {x : X} (hx : FinitelySupported A x)
    {a : A} (hF : Fresh A a F) (hX : hx.Fresh a) : (F.certificate.apply hx).Fresh a := by
  classical
  rw [fresh_iff_notMem_support] at hF
  rw [FinitelySupported.fresh_iff_notMem_support] at hX ⊢
  exact fun ha => (Finset.mem_union.mp (F.support_apply_subset hx ha)).elim hF hX

theorem fresh_comp [Infinite A] (H : SupportedMap A Y Z) (F : SupportedMap A X Y) {a : A}
    (hH : Fresh A a H) (hF : Fresh A a F) : Fresh A a (H.comp F) := by
  classical
  rw [fresh_iff_notMem_support] at *
  exact fun ha => (Finset.mem_union.mp (support_comp_subset H F ha)).elim hH hF

theorem fresh_fromParam [Infinite A] {P : Type t} [MulAction (Perm A) P]
    (E : P × X → Y) (hE : Equivariant A E) (p : P) (hp : FinitelySupported A p)
    {a : A} (ha : hp.Fresh a) : Fresh A a (fromParam E hE p hp) := by
  rw [fresh_iff_notMem_support]
  exact fun h => (hp.fresh_iff_notMem_support a).1 ha (support_fromParam_subset E hE p hp h)

/-! ## Supported sections and currying -/

/-- A supported map returning supported maps can always be uncurried. -/
def uncurry (H : SupportedMap A X (SupportedMap A Y Z)) : SupportedMap A (X × Y) Z :=
  ofFun A (fun p => H p.1 p.2) (by
    obtain ⟨S, hS⟩ := H.certificate
    refine ⟨S, fun π hfix p => ?_⟩
    change H (π • p.1) (π • p.2) = π • H p.1 p.2
    have he := DFunLike.congr_fun (hS π hfix p.1) (π • p.2)
    simpa only [smul_apply_smul] using he)

/-- Individual parameter evidence is sufficient to form one supported section. -/
def curryAt (F : SupportedMap A (X × Y) Z) (x : X) (hx : FinitelySupported A x) : SupportedMap A Y Z :=
  ofFun A (fun y => F (x,y)) (F.certificate.section hx)

/-- The exact admission condition for currying into supported function values.
Reducibility lets ordinary lambdas supplying section proofs participate in simp. -/
abbrev SectionsSupported (F : SupportedMap A (X × Y) Z) : Prop :=
  ∀ x, FinitelySupportedMap A (fun y => F (x,y))

/-- All sections may be supported even when their parameter carrier is not nominal. -/
def curryWithSections (F : SupportedMap A (X × Y) Z) (hs : F.SectionsSupported) :
    SupportedMap A X (SupportedMap A Y Z) :=
  ofFun A (fun x => ofFun A (fun y => F (x,y)) (hs x)) (by
    obtain ⟨S, hS⟩ := F.certificate
    refine ⟨S, fun π hfix x => ?_⟩
    apply ext
    intro y
    simpa only [ofFun_apply, smul_apply, Prod.smul_mk, smul_inv_smul] using hS π hfix (x, π⁻¹ • y))

@[simp] theorem uncurry_apply (H : SupportedMap A X (SupportedMap A Y Z)) (p : X × Y) :
    H.uncurry p = H p.1 p.2 := rfl
@[simp] theorem curryAt_apply (F : SupportedMap A (X × Y) Z) (x : X) (hx : FinitelySupported A x) (y : Y) :
    F.curryAt x hx y = F (x,y) := rfl
@[simp] theorem curryWithSections_apply (F : SupportedMap A (X × Y) Z) (hs : F.SectionsSupported) (x : X) (y : Y) :
    F.curryWithSections hs x y = F (x,y) := rfl
@[simp] theorem coe_uncurry (H : SupportedMap A X (SupportedMap A Y Z)) :
    (H.uncurry : X × Y → Z) = Function.uncurry (fun x y => H x y) := rfl
@[simp] theorem coe_curryAt (F : SupportedMap A (X × Y) Z) (x : X) (hx : FinitelySupported A x) :
    (F.curryAt x hx : Y → Z) = fun y => F (x,y) := rfl
@[simp] theorem coe_curryWithSections_apply (F : SupportedMap A (X × Y) Z) (hs : F.SectionsSupported) (x : X) :
    (F.curryWithSections hs x : Y → Z) = fun y => F (x,y) := rfl

theorem sectionsSupported_uncurry (H : SupportedMap A X (SupportedMap A Y Z)) : H.uncurry.SectionsSupported :=
  fun x => (H x).certificate

theorem sectionsSupported_of_nominal [Nominal A X] (F : SupportedMap A (X × Y) Z) : F.SectionsSupported :=
  fun x => F.certificate.section (Nominal.finitelySupported (A := A) x)

theorem sectionsSupported_smul {F : SupportedMap A (X × Y) Z} (hs : F.SectionsSupported) (π : Perm A) :
    (π • F).SectionsSupported := fun x =>
  (finitelySupportedMap_iff A _).2 ((hs (π⁻¹ • x)).toObject.smul π)

@[simp] theorem uncurry_curryWithSections (F : SupportedMap A (X × Y) Z) (hs : F.SectionsSupported) :
    (F.curryWithSections hs).uncurry = F := ext (fun _ => rfl)
@[simp] theorem curryWithSections_uncurry (H : SupportedMap A X (SupportedMap A Y Z)) :
    H.uncurry.curryWithSections H.sectionsSupported_uncurry = H := ext (fun _ => ext (fun _ => rfl))

theorem curryWithSections_proof_irrel (F : SupportedMap A (X × Y) Z) (hs ht : F.SectionsSupported) :
    F.curryWithSections hs = F.curryWithSections ht := rfl

theorem uncurry_injective : Function.Injective (uncurry : SupportedMap A X (SupportedMap A Y Z) → _) := by
  intro F H h
  exact ext (fun x => ext (fun y => DFunLike.congr_fun h (x,y)))

theorem uncurry_smul (π : Perm A) (H : SupportedMap A X (SupportedMap A Y Z)) :
    (π • H).uncurry = π • H.uncurry := ext (fun _ => rfl)
theorem curryWithSections_smul (π : Perm A) (F : SupportedMap A (X × Y) Z) (hs : F.SectionsSupported) :
    (π • F).curryWithSections (sectionsSupported_smul hs π) = π • F.curryWithSections hs :=
  ext (fun _ => ext (fun _ => rfl))

theorem curryAt_smul (π : Perm A) (F : SupportedMap A (X × Y) Z) (x : X) (hx : FinitelySupported A x) :
    (π • F).curryAt (π • x) (hx.smul π) = π • F.curryAt x hx := by
  apply ext
  intro y
  simp only [curryAt_apply, smul_apply, Prod.smul_mk, inv_smul_smul]

variable (A X Y Z) in
/-- The invariant part on which bundle-valued curry is defined. -/
def sectionSubaction : SubMulAction (Perm A) (SupportedMap A (X × Y) Z) where
  carrier := {F | F.SectionsSupported}
  smul_mem' π _ h := sectionsSupported_smul h π

variable (A X Y Z) in
/-- Exact curry correspondence for arbitrary acted-on carriers. -/
def admissibleCurryEquiv : sectionSubaction A X Y Z ≃ SupportedMap A X (SupportedMap A Y Z) where
  toFun F := F.val.curryWithSections F.property
  invFun H := ⟨H.uncurry, H.sectionsSupported_uncurry⟩
  left_inv F := Subtype.ext (uncurry_curryWithSections F.val F.property)
  right_inv H := curryWithSections_uncurry H

@[simp] theorem admissibleCurryEquiv_smul (π : Perm A) (F : sectionSubaction A X Y Z) :
    admissibleCurryEquiv A X Y Z (π • F) = π • admissibleCurryEquiv A X Y Z F :=
  curryWithSections_smul π F.val F.property

/-- Nominality of the parameter carrier supplies all section certificates. -/
def curry [Nominal A X] (F : SupportedMap A (X × Y) Z) : SupportedMap A X (SupportedMap A Y Z) :=
  F.curryWithSections F.sectionsSupported_of_nominal

@[simp] theorem curry_apply [Nominal A X] (F : SupportedMap A (X × Y) Z) (x : X) (y : Y) : F.curry x y = F (x,y) := rfl
@[simp] theorem coe_curry_apply [Nominal A X] (F : SupportedMap A (X × Y) Z) (x : X) :
    (F.curry x : Y → Z) = Function.curry (F : X × Y → Z) x := rfl
@[simp] theorem uncurry_curry [Nominal A X] (F : SupportedMap A (X × Y) Z) : F.curry.uncurry = F :=
  uncurry_curryWithSections _ _
@[simp] theorem curry_uncurry [Nominal A X] (H : SupportedMap A X (SupportedMap A Y Z)) : H.uncurry.curry = H :=
  curryWithSections_uncurry H

theorem curry_smul [Nominal A X] (π : Perm A) (F : SupportedMap A (X × Y) Z) :
    (π • F).curry = π • F.curry := curryWithSections_smul _ _ _

variable (A X Y Z) in
/-- On a nominal parameter carrier every supported binary map is admissible. -/
def curryEquiv [Nominal A X] : SupportedMap A (X × Y) Z ≃ SupportedMap A X (SupportedMap A Y Z) where
  toFun := curry
  invFun := uncurry
  left_inv := uncurry_curry
  right_inv := curry_uncurry

/-- Uncurrying reflects arbitrary sufficient bounds without nominality hypotheses. -/
theorem supports_uncurry_set_iff {B : Type t} [SMul (Perm A) B] (S : Set B)
    (H : SupportedMap A X (SupportedMap A Y Z)) :
    MulAction.Supports (Perm A) S H.uncurry ↔ MulAction.Supports (Perm A) S H :=
  ActionSupport.supports_map_iff uncurry uncurry_smul uncurry_injective S H

theorem supports_uncurry_iff (S : Finset A) (H : SupportedMap A X (SupportedMap A Y Z)) :
    Supports S H.uncurry ↔ Supports S H := supports_uncurry_set_iff (S : Set A) H

theorem supports_curryWithSections_set_iff {B : Type t} [SMul (Perm A) B] (S : Set B)
    (F : SupportedMap A (X × Y) Z) (hs : F.SectionsSupported) :
    MulAction.Supports (Perm A) S (F.curryWithSections hs) ↔ MulAction.Supports (Perm A) S F := by
  rw [← supports_uncurry_set_iff S, uncurry_curryWithSections]

theorem supports_curryWithSections_iff (S : Finset A) (F : SupportedMap A (X × Y) Z) (hs : F.SectionsSupported) :
    Supports S (F.curryWithSections hs) ↔ Supports S F := supports_curryWithSections_set_iff (S : Set A) F hs

section CurrySupport
variable [Infinite A]

theorem support_uncurry (H : SupportedMap A X (SupportedMap A Y Z)) : support A H.uncurry = support A H :=
  le_antisymm (support_minimal A ((supports_uncurry_iff _ H).2 (supports_support A H)))
    (support_minimal A ((supports_uncurry_iff _ H).1 (supports_support A H.uncurry)))
theorem support_curryWithSections (F : SupportedMap A (X × Y) Z) (hs : F.SectionsSupported) :
    support A (F.curryWithSections hs) = support A F := by rw [← support_uncurry, uncurry_curryWithSections]
theorem support_curry [Nominal A X] (F : SupportedMap A (X × Y) Z) : support A F.curry = support A F :=
  support_curryWithSections _ _
theorem support_curryAt_subset [DecidableEq A] (F : SupportedMap A (X × Y) Z) (x : X) (hx : FinitelySupported A x) :
    support A (F.curryAt x hx) ⊆ support A F ∪ hx.support := by
  rw [support_toObject, support_toObject]
  exact F.certificate.support_section_subset hx

theorem fresh_curryAt (F : SupportedMap A (X × Y) Z) (x : X) (hx : FinitelySupported A x) {a : A}
    (hF : Fresh A a F) (hX : hx.Fresh a) : Fresh A a (F.curryAt x hx) := by
  classical
  rw [fresh_iff_notMem_support] at hF ⊢
  rw [FinitelySupported.fresh_iff_notMem_support] at hX
  exact fun ha => (Finset.mem_union.mp (support_curryAt_subset F x hx ha)).elim hF hX

theorem fresh_uncurry_iff {W : Type t} [MulAction (Perm A) W] [Nominal A W]
    (w : W) (H : SupportedMap A X (SupportedMap A Y Z)) : Fresh A w H.uncurry ↔ Fresh A w H := by
  simp only [Fresh, support_uncurry]
theorem fresh_curryWithSections_iff {W : Type t} [MulAction (Perm A) W] [Nominal A W]
    (w : W) (F : SupportedMap A (X × Y) Z) (hs : F.SectionsSupported) :
    Fresh A w (F.curryWithSections hs) ↔ Fresh A w F := by simp only [Fresh, support_curryWithSections]

/-- The exact curry freshness laws also work with evidence for a single external value. -/
theorem freshWith_uncurry_iff {W : Type t} [MulAction (Perm A) W] {w : W}
    (hw : FinitelySupported A w) (H : SupportedMap A X (SupportedMap A Y Z)) :
    H.uncurry.supported.FreshWith hw ↔ H.supported.FreshWith hw := by
  change Disjoint _ _ ↔ Disjoint _ _
  rw [← support_toObject, ← support_toObject, support_uncurry]

theorem freshWith_curryWithSections_iff {W : Type t} [MulAction (Perm A) W] {w : W}
    (hw : FinitelySupported A w) (F : SupportedMap A (X × Y) Z) (hs : F.SectionsSupported) :
    (F.curryWithSections hs).supported.FreshWith hw ↔ F.supported.FreshWith hw := by
  change Disjoint _ _ ↔ Disjoint _ _
  rw [← support_toObject, ← support_toObject, support_curryWithSections]
end CurrySupport
end SupportedMap
end NominalPackage
