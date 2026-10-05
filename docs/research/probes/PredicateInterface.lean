import Nominal

/-!
Design-only PKG-01 probe, 2026-10-05, against 7fed53a.
This standalone file is not imported by a supported library target.
The sole representation field fixes the truth action explicitly; no instance
on bare Prop, functions or Set is installed. Definitions here are candidates,
not production API. Atom/domain/result universes remain independent.
-/
open Nominal.Core Nominal.Set

namespace PredicateInterface
universe u v w

@[instance_reducible]
def propNominal {α : Type u} [Name α] : Nominal α Prop where
  smul _ p := p
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  finSupp _ := ⟨∅, fun _ _ => rfl⟩

structure NPred (α : Type u) [Name α] (X : Type v) [Nominal α X] where
  toNFun : letI : Nominal α Prop := propNominal; NFun α X Prop

namespace NPred
variable {α : Type u} [Name α] {X : Type v} [Nominal α X]

instance : FunLike (NPred α X) X Prop := by
  letI : Nominal α Prop := propNominal
  exact {
  coe p := p.toNFun.toPFun.toFun
  coe_injective := by
    intro p q h
    have : p.toNFun = q.toNFun := NFun.ext (congrFun h)
    cases p; cases q; congr }

@[ext]
theorem ext {p q : NPred α X} (h : ∀ x, p x ↔ q x) : p = q :=
  DFunLike.ext p q (fun x => propext (h x))

theorem eq_iff {p q : NPred α X} : p = q ↔ ∀ x, p x ↔ q x :=
  ⟨fun h _ => h ▸ Iff.rfl, ext⟩

def ofNFun : (letI : Nominal α Prop := propNominal; NFun α X Prop) → NPred α X :=
  NPred.mk

@[simp] theorem ofNFun_apply
    (p : letI : Nominal α Prop := propNominal; NFun α X Prop) (x : X) :
    ofNFun p x ↔ p x := Iff.rfl

def nfunEquiv :
    NPred α X ≃ (letI : Nominal α Prop := propNominal; NFun α X Prop) where
  toFun := toNFun
  invFun := ofNFun
  left_inv _ := rfl
  right_inv _ := rfl

instance : PermType α (NPred α X) where
  smul π p := ⟨π • p.toNFun⟩
  one_smul p := by apply ext; intro x; change p ((1 : FinitePerm α)⁻¹ • x) ↔ p x; simp
  mul_smul π σ p := by
    apply ext; intro x
    change p ((π * σ)⁻¹ • x) ↔ p (σ⁻¹ • (π⁻¹ • x))
    rw [mul_inv_rev, mul_smul]

@[simp] theorem smul_apply (π : FinitePerm α) (p : NPred α X) (x : X) :
    (π • p) x ↔ p (π⁻¹ • x) := Iff.rfl

theorem supports_iff_toNFun {s : Finset α} {p : NPred α X} :
    supports s p ↔ supports s p.toNFun := by
  constructor
  · intro h π hπ; exact congrArg toNFun (h π hπ)
  · intro h π hπ; exact nfunEquiv.injective (h π hπ)

instance : Nominal α (NPred α X) where
  finSupp p := by
    obtain ⟨s, hs⟩ := Nominal.finSupp p.toNFun
    exact ⟨s, supports_iff_toNFun.mpr hs⟩

theorem supp_toNFun (p : NPred α X) : supp p.toNFun = supp p :=
  supp_map_injective ⟨fun _ _ => rfl⟩ nfunEquiv.injective p

def LogicalSupports (s : Finset α) (p : X → Prop) : Prop :=
  ∀ π : FinitePerm α, (∀ ⦃a⦄, a ∈ s → π a = a) → ∀ x, p (π • x) ↔ p x

def ofSupported (p : X → Prop) (h : ∃ s : Finset α, LogicalSupports s p) : NPred α X := by
  letI : Nominal α Prop := propNominal
  refine ofNFun (NFun.ofFun p ?_)
  obtain ⟨s, hs⟩ := h
  exact ⟨s, supports_pfun_iff.mpr (fun π hπ x => propext (hs π hπ x))⟩

@[simp] theorem ofSupported_apply (p : X → Prop)
    (h : ∃ s : Finset α, LogicalSupports s p) (x : X) : ofSupported p h x ↔ p x := Iff.rfl

-- A supported-subset view shares the same support certificate and has no
-- independent action on bare Set X.
def supportedSubsetEquiv :
    NPred α X ≃ {p : Set X // ∃ s : Finset α, LogicalSupports s p} where
  toFun p := ⟨fun x => p x, by
    let : Nominal α Prop := propNominal
    obtain ⟨s, hs⟩ := p.toNFun.finSupp_toPFun
    exact ⟨s, fun π hπ x => Iff.of_eq ((supports_pfun_iff.mp hs) π hπ x)⟩⟩
  invFun p := ofSupported p.val p.property
  left_inv p := by ext x; rfl
  right_inv p := by apply Subtype.ext; rfl

def precomp {Y : Type w} [Nominal α Y] (p : NPred α X) (f : NFun α Y X) :
    NPred α Y := by
  letI : Nominal α Prop := propNominal
  exact ofNFun (p.toNFun.comp f)

@[simp] theorem precomp_apply {Y : Type w} [Nominal α Y]
    (p : NPred α X) (f : NFun α Y X) (y : Y) : precomp p f y ↔ p (f y) := Iff.rfl

def singleton (x : X) : NPred α X := by
  letI : Nominal α Prop := propNominal
  exact ofNFun (NFun.fromParam (fun x y : X => x = y)
    ⟨fun π _ _ => propext (PermType.smul_eq_smul_iff_eq π)⟩ x)

@[simp] theorem singleton_apply (x y : X) : singleton x y ↔ x = y := Iff.rfl

-- A relation curry uses existing NFun.curry plus the equivariant adapter.
def curry {Y : Type w} [Nominal α Y] (r : NPred α (X × Y)) : NFun α X (NPred α Y) := by
  letI : Nominal α Prop := propNominal
  exact (NFun.curry r.toNFun).map ofNFun ⟨fun _ _ => rfl⟩

@[simp] theorem curry_apply {Y : Type w} [Nominal α Y]
    (r : NPred α (X × Y)) (x : X) (y : Y) : curry r x y ↔ r (x, y) := Iff.rfl

-- Both ordinary higher-order predicates and bundled higher-order functions work.
example (p : NPred α X) : (∀ x, p x) ↔ ∀ x, (p : X → Prop) x := Iff.rfl
example (p : NPred α X) (xs : List X) : xs.map p = xs.map (fun x => p x) := rfl
example (p q : NPred α X) (h : ∀ x, p x ↔ q x) : p = q := by ext x; exact h x
example (p : NPred α X) (x : X) : precomp p NFun.id x ↔ p x := by simp
example (F : NFun α X (NPred α X)) (x y : X) :
    (NFun.eval (F, x)) y ↔ F x y := Iff.rfl
example (p : NPred α X) (x : X) (h : p x) : singleton x x ∧ p x := by simp [h]

-- Direct comparison: explicit letI is sufficient for plain NFun-to-Prop.
example : letI : Nominal α Prop := propNominal
    ∀ (p q : NFun α X Prop), (∀ x, p x ↔ q x) → p = q := by
  let : Nominal α Prop := propNominal
  intro p q h
  exact NFun.ext (fun x => propext (h x))

end NPred

-- Two arbitrary atom carriers can coexist with no ambient Prop instance.
section TwoAtoms
variable {α : Type u} {β : Type w} [Name α] [Name β]
example (a : α) (b : β) :
    NPred.singleton a a ∧ NPred.singleton b b := by simp
example (p : NPred α α) (q : NPred β β) (a : α) (b : β) :
    (NPred.precomp p NFun.id a ↔ p a) ∧ (NPred.precomp q NFun.id b ↔ q b) := by simp
noncomputable example (p : NPred α α) (q : NPred β β) : Finset α × Finset β := (supp p, supp q)
end TwoAtoms

-- Compare a definitional abbreviation with the structure above. This fixes the
-- truth action and preserves existing NFun instances. Selected operation
-- adapters remain necessary, as the guarded checks immediately below show.
abbrev APred (α : Type u) [Name α] (X : Type v) [Nominal α X] :=
  letI : Nominal α Prop := propNominal (α := α)
  NFun α X Prop

section Abbreviation
variable {α : Type u} {β : Type w} [Name α] [Name β]
variable {X : Type v} [Nominal α X]
example (p : APred α X) (x : X) : Prop := p x
example : Nominal α (APred α X) := inferInstance
example (p q : APred α X) (h : ∀ x, p x ↔ q x) : p = q := by
  -- The abbreviation does not supply an ambient truth instance to NFun.ext.
  fail_if_success apply NFun.ext
  let : Nominal α Prop := propNominal
  apply NFun.ext
  intro x
  exact propext (h x)
example (p : APred α X) (x : X) : p x ↔ p x := by
  -- Nor does dot notation for existing operations infer that instance.
  fail_if_success have f := p.comp (NFun.id : NFun α X X)
  let : Nominal α Prop := propNominal
  have h : p.comp NFun.id x ↔ p x := by simp
  exact h
example (F : NFun α X (APred α X)) (x y : X) :
    NFun.eval (F, x) y ↔ F x y := Iff.rfl
example (p : APred α α) (q : APred β β) (a : α) (b : β) :
    (p a ∧ q b) ↔ (p a ∧ q b) := Iff.rfl
noncomputable example (p : APred α α) (q : APred β β) :
    Finset α × Finset β := (supp p, supp q)
end Abbreviation

-- The abbreviation needs named adapters for NFun operations that elaborate a
-- fresh codomain instance, but avoids duplicating FunLike/action/Nominal theory.
namespace APred
variable {α : Type u} [Name α] {X : Type v} [Nominal α X]

@[ext] theorem ext {p q : APred α X} (h : ∀ x, p x ↔ q x) : p = q :=
  DFunLike.ext p q (fun x => propext (h x))

@[simp] theorem smul_apply (π : FinitePerm α) (p : APred α X) (x : X) :
    (π • p) x ↔ p (π⁻¹ • x) := Iff.rfl

def ofSupported (p : X → Prop) (h : ∃ s : Finset α, NPred.LogicalSupports s p) : APred α X := by
  letI : Nominal α Prop := propNominal
  refine NFun.ofFun p ?_
  obtain ⟨s, hs⟩ := h
  exact ⟨s, supports_pfun_iff.mpr (fun π hπ x => propext (hs π hπ x))⟩

@[simp] theorem ofSupported_apply (p : X → Prop)
    (h : ∃ s : Finset α, NPred.LogicalSupports s p) (x : X) : ofSupported p h x ↔ p x := Iff.rfl

def toSet (p : APred α X) : Set X := fun x => p x

@[simp] theorem mem_toSet (p : APred α X) (x : X) : x ∈ p.toSet ↔ p x := Iff.rfl

def supportedSubsetEquiv :
    APred α X ≃ {p : Set X // ∃ s : Finset α, NPred.LogicalSupports s p} where
  toFun p := ⟨p.toSet, by
    let : Nominal α Prop := propNominal
    obtain ⟨s, hs⟩ := p.finSupp_toPFun
    exact ⟨s, fun π hπ x => Iff.of_eq ((supports_pfun_iff.mp hs) π hπ x)⟩⟩
  invFun p := ofSupported p.val p.property
  left_inv p := by ext x; rfl
  right_inv p := by apply Subtype.ext; rfl

theorem toSet_smul (π : FinitePerm α) (p : APred α X) (x : X) :
    x ∈ (π • p).toSet ↔ ∃ y, y ∈ p.toSet ∧ π • y = x := by
  change p (π⁻¹ • x) ↔ ∃ y, p y ∧ π • y = x
  constructor
  · intro h; exact ⟨π⁻¹ • x, h, by simp⟩
  · rintro ⟨y, hy, rfl⟩; simpa using hy

def fromParam {Z : Type w} [Nominal α Z] (R : Z → X → Prop)
    (hR : EquivariantRel α R) (z : Z) : APred α X := by
  letI : Nominal α Prop := propNominal
  exact NFun.fromParam R ⟨fun π z x => propext (hR.smul_iff π z x)⟩ z

@[simp] theorem fromParam_apply {Z : Type w} [Nominal α Z] (R : Z → X → Prop)
    (hR : EquivariantRel α R) (z : Z) (x : X) : fromParam R hR z x ↔ R z x := Iff.rfl

def precomp {Y : Type w} [Nominal α Y] (p : APred α X) (f : NFun α Y X) : APred α Y := by
  letI : Nominal α Prop := propNominal
  exact p.comp f

@[simp] theorem precomp_apply {Y : Type w} [Nominal α Y]
    (p : APred α X) (f : NFun α Y X) (y : Y) : p.precomp f y ↔ p (f y) := Iff.rfl

theorem supp_precomp_le {Y : Type w} [Nominal α Y] (p : APred α X) (f : NFun α Y X) :
    supp (p.precomp f) ⊆ supp p ∪ supp f := by
  let : Nominal α Prop := propNominal
  exact NFun.supp_comp_le p f

def curry {Y : Type w} [Nominal α Y] (r : APred α (X × Y)) : NFun α X (APred α Y) := by
  letI : Nominal α Prop := propNominal
  exact NFun.curry r

@[simp] theorem curry_apply {Y : Type w} [Nominal α Y]
    (r : APred α (X × Y)) (x : X) (y : Y) : r.curry x y ↔ r (x, y) := Iff.rfl

example (p q : APred α X) (h : ∀ x, p x ↔ q x) : p = q := by ext x; exact h x
example (p : APred α X) (x : X) : p.precomp NFun.id x ↔ p x := by simp
example {Y : Type w} [Nominal α Y] (r : APred α (X × Y)) (x : X) (y : Y) :
    r.curry x y ↔ r (x, y) := by simp
end APred

section AliasTwoAtoms
variable {α : Type u} {β : Type w} [Name α] [Name β]
example (p : APred α α) (q : APred β β) (a : α) (b : β) :
    (p.precomp NFun.id a ↔ p a) ∧ (q.precomp NFun.id b ↔ q b) := by simp
example (a : α) (b : β) :
    APred.fromParam Eq equivariantRel_eq a a ∧ APred.fromParam Eq equivariantRel_eq b b := by simp
end AliasTwoAtoms

#check NPred
#check NPred.curry
#print axioms NPred.nfunEquiv
#print axioms NPred.supp_toNFun
#print axioms NPred.singleton
#print axioms NPred.curry
#print axioms NPred.supportedSubsetEquiv
#print axioms APred.curry
#check APred
#print axioms APred.supportedSubsetEquiv
#print axioms APred.toSet_smul
#print axioms APred.supp_precomp_le

end PredicateInterface
