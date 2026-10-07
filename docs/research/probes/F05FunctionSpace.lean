import Package.Foundations.Nominal
import Mathlib.GroupTheory.GroupAction.Hom

/-!
Bounded F05 research probe, 2026-10-07. Not a production module or proposed full API.
Pinned Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612 / Lean 4.34.1.
The atom/group, domain, and codomain universes are independent. No whole-carrier
nominality is assumed. Existential support choices occur only in proof fields.
-/

open NominalPackage

universe u v w z t

namespace F05Probe

/-- A distinct carrier isolates conjugation while preserving the ordinary pointwise action. -/
structure ConjFun (G : Type u) (X : Type v) (Y : Type w) : Type (max v w) where
  toFun : X → Y

namespace ConjFun

variable {G : Type u} {X : Type v} {Y : Type w}

instance : FunLike (ConjFun G X Y) X Y where
  coe := toFun
  coe_injective := by rintro ⟨f⟩ ⟨g⟩ h; cases h; rfl

@[ext] theorem ext {f g : ConjFun G X Y} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext f g h

@[simp] theorem mk_apply (f : X → Y) (x : X) : (mk f : ConjFun G X Y) x = f x := rfl

section Curry
variable {Z : Type z}

def curry (f : ConjFun G (X × Y) Z) : ConjFun G X (ConjFun G Y Z) :=
  ⟨fun x => ⟨Function.curry f x⟩⟩

def uncurry (f : ConjFun G X (ConjFun G Y Z)) : ConjFun G (X × Y) Z :=
  ⟨Function.uncurry (fun x y => f x y)⟩

@[simp] theorem curry_apply (f : ConjFun G (X × Y) Z) (x : X) (y : Y) :
    curry f x y = f (x, y) := rfl

@[simp] theorem uncurry_apply (f : ConjFun G X (ConjFun G Y Z)) (x : X) (y : Y) :
    uncurry f (x, y) = f x y := rfl

theorem uncurry_curry (f : ConjFun G (X × Y) Z) : uncurry (curry f) = f := by
  ext p
  rfl

theorem curry_uncurry (f : ConjFun G X (ConjFun G Y Z)) : curry (uncurry f) = f := by
  ext x y
  rfl

def curryEquiv : ConjFun G (X × Y) Z ≃ ConjFun G X (ConjFun G Y Z) where
  toFun := curry
  invFun := uncurry
  left_inv := uncurry_curry
  right_inv := curry_uncurry

end Curry

section Action
variable [DivisionMonoid G] [MulAction G X] [MulAction G Y]

instance : MulAction G (ConjFun G X Y) where
  smul g f := ⟨fun x => g • f (g⁻¹ • x)⟩
  one_smul f := by
    ext x
    change (1 : G) • f ((1 : G)⁻¹ • x) = f x
    simp
  mul_smul g h f := by
    ext x
    change (g * h) • f ((g * h)⁻¹ • x) = g • (h • f (h⁻¹ • (g⁻¹ • x)))
    simp [mul_smul]

@[simp] theorem smul_apply (g : G) (f : ConjFun G X Y) (x : X) :
    (g • f) x = g • f (g⁻¹ • x) := rfl

variable {Z : Type z} [MulAction G Z]

/-- Full curry commutes with conjugation without any support/inhabitance premise. -/
theorem curry_smul (g : G) (f : ConjFun G (X × Y) Z) : curry (g • f) = g • curry f := by
  ext x y
  rfl

theorem uncurry_smul (g : G) (f : ConjFun G X (ConjFun G Y Z)) :
    uncurry (g • f) = g • uncurry f := by
  ext p
  rfl

end Action

variable [Group G] [MulAction G X] [MulAction G Y]

theorem smul_eq_iff (g : G) (f : ConjFun G X Y) :
    g • f = f ↔ ∀ x, f (g • x) = g • f x := by
  constructor
  · intro h x
    have := DFunLike.congr_fun h (g • x)
    simpa using this.symm
  · intro h
    ext x
    simpa using (h (g⁻¹ • x)).symm

theorem smul_id (g : G) : g • (mk id : ConjFun G X X) = mk id := by
  ext x
  simp

/-- This remains Mathlib's pointwise codomain action. -/
example (g : G) (f : X → Y) (x : X) : (g • f) x = g • f x := rfl

/-- Mathlib's alternate action acts on the domain only. -/
example (g : G) (f : X → Y) (x : X) :
    @SMul.smul G (X → Y) arrowAction.toSMul g f x =
      f (g⁻¹ • x) := rfl

def equivariantHom (f : ConjFun G X Y) (hf : ∀ g : G, g • f = f) : X →[G] Y :=
  ⟨f, fun g x => (smul_eq_iff g f).1 (hf g) x⟩

end ConjFun

/-- Concrete obstruction to identifying the ordinary and conjugation actions. -/
theorem pointwise_id_not_fixed :
    Perm.swap false true • (id : Bool → Bool) ≠ id := by
  intro h
  have h' := congrFun h false
  change Perm.swap false true false = false at h'
  simp at h'

theorem ordinary_id_not_emptySupported :
    ¬ Supports (∅ : Finset Bool) (id : Bool → Bool) := by
  intro h
  exact pointwise_id_not_fixed ((supports_empty_iff _).1 h (Perm.swap false true))

section OrdinaryCertificates

variable {A : Type u} {X : Type v} {Y : Type w}
variable [MulAction (Perm A) X] [MulAction (Perm A) Y]

/-- An ordinary function certificate does not select an action on `X → Y`. -/
def SupportsFun (S : Finset A) (f : X → Y) : Prop :=
  ∀ π : Perm A, (∀ a ∈ S, π a = a) → ∀ x, f (π • x) = π • f x

def FinSupportedFun (A : Type u) {X : Type v} {Y : Type w}
    [MulAction (Perm A) X] [MulAction (Perm A) Y] (f : X → Y) : Prop :=
  ∃ S : Finset A, SupportsFun S f

theorem supportsFun_iff (S : Finset A) (f : X → Y) :
    SupportsFun S f ↔ Supports S (ConjFun.mk f : ConjFun (Perm A) X Y) := by
  rw [supports_iff]
  exact forall_congr' fun π => forall_congr' fun _ => (ConjFun.smul_eq_iff π _).symm

theorem finSupportedFun_iff (f : X → Y) :
    FinSupportedFun A f ↔ FinitelySupported A (ConjFun.mk f : ConjFun (Perm A) X Y) :=
  exists_congr fun S => supportsFun_iff S f

theorem supportsFun_empty_iff (f : X → Y) :
    SupportsFun (∅ : Finset A) f ↔ Equivariant A f := by
  simp only [SupportsFun, Finset.notMem_empty, IsEmpty.forall_iff, implies_true,
    forall_const, Equivariant]

variable {P : Type z} [MulAction (Perm A) P]

theorem supportsFun_fromParam (f : P × X → Y) (hf : Equivariant A f)
    {p : P} {S : Finset A} (hp : Supports S p) : SupportsFun S (fun x => f (p, x)) := by
  intro π hfix x
  have h := hf π (p, x)
  have hp' := (supports_iff S p).1 hp π hfix
  simpa only [Prod.smul_mk, hp'] using h

theorem finSupportedFun_fromParam (f : P × X → Y) (hf : Equivariant A f)
    {p : P} (hp : FinitelySupported A p) : FinSupportedFun A (fun x => f (p, x)) := by
  obtain ⟨S, hS⟩ := hp
  exact ⟨S, supportsFun_fromParam f hf hS⟩

end OrdinaryCertificates

/-- Context-first sufficient support: captured p,q need only individual bounds;
U is any user-selected enlargement. This certifies the action equation rather
than inferring supportedness from the syntax of the local context. -/
theorem contextBound {A : Type u} {P : Type v} {Q : Type w} {X : Type z} {Y : Type t}
    [DecidableEq A] [MulAction (Perm A) P] [MulAction (Perm A) Q]
    [MulAction (Perm A) X] [MulAction (Perm A) Y]
    (E : (P × Q) × X → Y) (hE : Equivariant A E)
    {p : P} {q : Q} {S T : Finset A} (hp : Supports S p) (hq : Supports T q)
    (U : Finset A) : SupportsFun ((S ∪ T) ∪ U) (fun x => E ((p, q), x)) :=
  supportsFun_fromParam E hE (supports_mono Finset.subset_union_left (supports_prod hp hq))

/-- The data is an ordinary function; the support witness is entirely proof-only. -/
structure SupportedFun (A : Type u) (X : Type v) (Y : Type w)
    [MulAction (Perm A) X] [MulAction (Perm A) Y] : Type (max v w) where
  toConjFun : ConjFun (Perm A) X Y
  supported : FinitelySupported A toConjFun

namespace SupportedFun

variable {A : Type u} {X : Type v} {Y : Type w}
variable [MulAction (Perm A) X] [MulAction (Perm A) Y]

instance : FunLike (SupportedFun A X Y) X Y where
  coe f := f.toConjFun
  coe_injective := by
    rintro ⟨f, hf⟩ ⟨g, hg⟩ h
    have : f = g := DFunLike.coe_injective h
    cases this
    rfl

@[ext] theorem ext {f g : SupportedFun A X Y} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext f g h

def ofFun (f : X → Y) (hf : FinSupportedFun A f) : SupportedFun A X Y :=
  ⟨⟨f⟩, (finSupportedFun_iff f).1 hf⟩

@[simp] theorem ofFun_apply (f : X → Y) (hf : FinSupportedFun A f) (x : X) :
    ofFun f hf x = f x := rfl

instance : MulAction (Perm A) (SupportedFun A X Y) where
  smul π f := ⟨π • f.toConjFun, f.supported.smul π⟩
  one_smul f := by ext x; exact DFunLike.congr_fun (one_smul _ f.toConjFun) x
  mul_smul π σ f := by ext x; exact DFunLike.congr_fun (mul_smul π σ f.toConjFun) x

@[simp] theorem smul_apply (π : Perm A) (f : SupportedFun A X Y) (x : X) :
    (π • f) x = π • f (π⁻¹ • x) := rfl

theorem supports_iff_toConjFun (S : Finset A) (f : SupportedFun A X Y) :
    Supports S f ↔ Supports S f.toConjFun := by
  constructor
  · intro h π hfix
    exact congrArg toConjFun (h π hfix)
  · intro h π hfix
    ext x
    exact DFunLike.congr_fun (h π hfix) x

instance : Nominal A (SupportedFun A X Y) where
  finitelySupported f := by
    obtain ⟨S, hS⟩ := f.supported
    exact ⟨S, (supports_iff_toConjFun S f).2 hS⟩

def fromParam {P : Type z} [MulAction (Perm A) P]
    (f : P × X → Y) (hf : Equivariant A f) (p : P) (hp : FinitelySupported A p) :
    SupportedFun A X Y :=
  ofFun (fun x => f (p, x)) (finSupportedFun_fromParam f hf hp)

example (f g : SupportedFun A X Y) (h : ∀ x, f x = g x) : f = g := by ext x; exact h x
example (f g : SupportedFun A X Y) (h : f = g) (x : X) : f x = g x := by rw [h]
example (f : SupportedFun A X Y) (xs : List X) : xs.map f = xs.map (fun x => f x) := rfl

/-- A choice-dependent support certificate does not make the function data noncomputable. -/
def idWithLeastSupportProof [Infinite A] (f : SupportedFun A X Y) : SupportedFun A X Y :=
  ⟨f.toConjFun, ⟨f.supported.support, f.supported.supports_support⟩⟩

example [Infinite A] (f : SupportedFun A X Y) : idWithLeastSupportProof f = f := rfl

end SupportedFun

section UsabilityComparison

variable {A : Type u} {X : Type v} {Y : Type w} {P : Type z}
variable [MulAction (Perm A) X] [MulAction (Perm A) Y] [MulAction (Perm A) P]

theorem conjEvaluation_equivariant :
    Equivariant A (fun p : ConjFun (Perm A) X Y × X => p.1 p.2) := by
  intro π p
  simp

/-- Ordinary functions keep their exact ordinary types; only support-sensitive
consumers thread a certificate. Neither X nor Y is assumed nominal. -/
theorem ordinaryApplication (f : X → Y) (hf : FinSupportedFun A f)
    (x : X) (hx : FinitelySupported A x) : FinitelySupported A (f x) :=
  (((finSupportedFun_iff f).1 hf).prod hx).map conjEvaluation_equivariant

theorem bundledEvaluation_equivariant :
    Equivariant A (fun p : SupportedFun A X Y × X => p.1 p.2) := by
  intro π p
  simp

/-- The same theorem on a bundle obtains the function certificate from its field. -/
theorem bundledApplication (f : SupportedFun A X Y)
    (x : X) (hx : FinitelySupported A x) : FinitelySupported A (f x) :=
  ((Nominal.finitelySupported (A := A) f).prod hx).map bundledEvaluation_equivariant

/-- A higher-order nominal operation can receive a supported function directly. -/
def bundledEvaluation : SupportedFun A (SupportedFun A X Y × X) Y :=
  SupportedFun.ofFun (fun p => p.1 p.2)
    ⟨∅, (supportsFun_empty_iff _).2 bundledEvaluation_equivariant⟩

example (f : SupportedFun A X Y) (x : X) : bundledEvaluation (f, x) = f x := rfl

/-- Ordinary return values can stay ordinary, with evidence returned separately. -/
def ordinaryPartial (f : P × X → Y) (p : P) : X → Y := fun x => f (p, x)

theorem ordinaryPartial_supported (f : P × X → Y) (hf : Equivariant A f)
    (p : P) (hp : FinitelySupported A p) : FinSupportedFun A (ordinaryPartial f p) :=
  finSupportedFun_fromParam f hf hp

/-- Returning the value together with its evidence is already a form of bundle. -/
def certifiedPartial (f : P × X → Y) (hf : Equivariant A f)
    (p : P) (hp : FinitelySupported A p) : {g : X → Y // FinSupportedFun A g} :=
  ⟨ordinaryPartial f p, ordinaryPartial_supported f hf p hp⟩

example (f : P × X → Y) (hf : Equivariant A f) (p : P) (hp : FinitelySupported A p)
    (xs : List X) :
    xs.map (ordinaryPartial f p) = xs.map (SupportedFun.fromParam f hf p hp) := rfl

example (f g : X → Y) (h : f = g) (x : X) : f x = g x := by rw [h]
example (f g : SupportedFun A X Y) (h : f = g) (x : X) : f x = g x := by rw [h]

/-- Ordinary function equality can rewrite a consumer of a bundle after its
coercion is made explicit, without mentioning its proof field. -/
example (f : SupportedFun A X Y) (g : X → Y) (h : (f : X → Y) = g)
    (xs : List X) : xs.map f = xs.map g := by rw [h]

/-- Exact ordinary type annotations occasionally matter at a polymorphic API. -/
example (f : SupportedFun A X Y) : Function.comp (id : Y → Y) f = (f : X → Y) := rfl

end UsabilityComparison

section PredicateBridge

variable {A : Type u} {X : Type v} [MulAction (Perm A) X]

/-- Raw predicates need no action on Prop or on ordinary function arrows. -/
def SupportsPred (S : Finset A) (P : X → Prop) : Prop :=
  ∀ π : Perm A, (∀ a ∈ S, π a = a) → ∀ x, P (π • x) ↔ P x

def predicateObject (P : X → Prop) : ConjFun (Perm A) X (Discrete A Prop) :=
  ⟨fun x => Discrete.mk (P x)⟩

theorem supportsPred_iff (S : Finset A) (P : X → Prop) :
    SupportsPred S P ↔ Supports S (predicateObject (A := A) P) := by
  change SupportsPred S P ↔
    Supports S (ConjFun.mk (fun x => Discrete.mk (P x)) : ConjFun (Perm A) X (Discrete A Prop))
  rw [← supportsFun_iff]
  constructor
  · intro h π hfix x
    change Discrete.mk (P (π • x)) = Discrete.mk (P x)
    exact congrArg Discrete.mk (propext (h π hfix x))
  · intro h π hfix x
    exact Iff.of_eq (congrArg Discrete.val (h π hfix x))

end PredicateBridge

/-- Compilation exercises the proof-only support constructor with computable data. -/
def boolIdentity : SupportedFun Bool Bool Bool :=
  SupportedFun.ofFun id ⟨∅, (supportsFun_empty_iff id).2 (Equivariant.id Bool)⟩

#eval boolIdentity true

#print axioms ConjFun.smul_eq_iff
#print axioms ConjFun.curryEquiv
#print axioms ConjFun.curry_smul
#print axioms ConjFun.uncurry_smul
#print axioms supportsFun_iff
#print axioms finSupportedFun_fromParam
#print axioms contextBound
#print axioms SupportedFun.ofFun
#print axioms SupportedFun.fromParam
#print axioms SupportedFun.idWithLeastSupportProof
#print axioms pointwise_id_not_fixed
#print axioms ordinaryApplication
#print axioms bundledApplication
#print axioms bundledEvaluation
#print axioms supportsPred_iff

end F05Probe
