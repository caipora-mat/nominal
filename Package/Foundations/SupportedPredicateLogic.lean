/-
Copyright (c) 2026 Nominal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nominal contributors
-/
import Package.Foundations.SupportedPredicate

/-!
# Logical operations on supported predicates

The transferred Boolean algebra computes as ordinary logic. Precomposition and
sections reuse the ordinary function/predicate support calculus; a section needs
only its particular parameter's certificate. Whole-carrier quantification instead
reindexes the quantified variable, with no nominality or nonemptiness premise.

Supported collections have unions and intersections by guarded quantification
over supported predicates, whose evaluation is jointly invariant. This retains
every bound of the collection, without asserting arbitrary external completeness.
Complement preserves exact support. The other operations can erase dependence,
so their least-support laws give inclusions rather than equalities.
-/

namespace NominalPackage
namespace SupportedPred
universe u v w

variable {A : Type u} {X : Type v} {Y : Type w}
variable [MulAction (Perm A) X] [MulAction (Perm A) Y]

theorem le_def (p q : SupportedPred A X) : p ≤ q ↔ ∀ x, p x → q x := Iff.rfl

@[simp] theorem bot_apply (x : X) : (⊥ : SupportedPred A X) x ↔ False := Iff.rfl
@[simp] theorem top_apply (x : X) : (⊤ : SupportedPred A X) x ↔ True := Iff.rfl
@[simp] theorem inf_apply (p q : SupportedPred A X) (x : X) :
    (p ⊓ q) x ↔ p x ∧ q x := Iff.rfl
@[simp] theorem sup_apply (p q : SupportedPred A X) (x : X) :
    (p ⊔ q) x ↔ p x ∨ q x := Iff.rfl
@[simp] theorem compl_apply (p : SupportedPred A X) (x : X) : pᶜ x ↔ ¬p x := Iff.rfl
@[simp] theorem himp_apply (p q : SupportedPred A X) (x : X) :
    (p ⇨ q) x ↔ (p x → q x) := Iff.rfl
@[simp] theorem sdiff_apply (p q : SupportedPred A X) (x : X) :
    (p \ q) x ↔ p x ∧ ¬q x := Iff.rfl

@[simp] theorem coe_bot : ((⊥ : SupportedPred A X) : X → Prop) = (fun _ : X => False) := rfl
@[simp] theorem coe_top : ((⊤ : SupportedPred A X) : X → Prop) = (fun _ : X => True) := rfl
@[simp] theorem coe_inf (p q : SupportedPred A X) :
    ((p ⊓ q : SupportedPred A X) : X → Prop) = (fun x => p x ∧ q x) := rfl
@[simp] theorem coe_sup (p q : SupportedPred A X) :
    ((p ⊔ q : SupportedPred A X) : X → Prop) = (fun x => p x ∨ q x) := rfl
@[simp] theorem coe_compl (p : SupportedPred A X) :
    ((pᶜ : SupportedPred A X) : X → Prop) = (fun x => ¬p x) := rfl
@[simp] theorem coe_himp (p q : SupportedPred A X) :
    ((p ⇨ q : SupportedPred A X) : X → Prop) = (fun x => p x → q x) := rfl
@[simp] theorem coe_sdiff (p q : SupportedPred A X) :
    ((p \ q : SupportedPred A X) : X → Prop) = (fun x => p x ∧ ¬q x) := rfl

/-- Logical equivalence, derived from the existing Boolean operations. -/
def biimp (p q : SupportedPred A X) : SupportedPred A X := (p ⇨ q) ⊓ (q ⇨ p)

@[simp] theorem biimp_apply (p q : SupportedPred A X) (x : X) :
    p.biimp q x ↔ (p x ↔ q x) := ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.mp, h.mpr⟩⟩
@[simp] theorem coe_biimp (p q : SupportedPred A X) :
    (p.biimp q : X → Prop) = (fun x => p x ↔ q x) :=
  funext fun x => propext (biimp_apply p q x)

/-- Precompose with an ordinary map carrying conjugation-support evidence. -/
def precomp (p : SupportedPred A Y) (f : X → Y) (hf : FinitelySupportedMap A f) :
    SupportedPred A X := ofFun A (p ∘ f) (p.supported.precomp hf)

def precompMap (p : SupportedPred A Y) (f : SupportedMap A X Y) : SupportedPred A X :=
  p.precomp f f.certificate

/-- Fix a parameter using its individual certificate; its carrier need not be nominal. -/
def «section» (R : SupportedPred A (Y × X)) (y : Y) (hy : FinitelySupported A y) :
    SupportedPred A X := ofFun A (fun x => R (y,x)) (R.supported.section hy)

/-- Quantify over the entire acted carrier, including empty or non-nominal carriers. -/
def all (R : SupportedPred A (X × Y)) : SupportedPred A X :=
  ofFun A (fun x => ∀ y, R (x,y)) R.supported.all

def ex (R : SupportedPred A (X × Y)) : SupportedPred A X :=
  ofFun A (fun x => ∃ y, R (x,y)) R.supported.ex

@[simp] theorem precomp_apply (p : SupportedPred A Y) (f : X → Y)
    (hf : FinitelySupportedMap A f) (x : X) : p.precomp f hf x ↔ p (f x) := Iff.rfl
@[simp] theorem precompMap_apply (p : SupportedPred A Y) (f : SupportedMap A X Y) (x : X) :
    p.precompMap f x ↔ p (f x) := Iff.rfl
@[simp] theorem section_apply (R : SupportedPred A (Y × X)) (y : Y)
    (hy : FinitelySupported A y) (x : X) : R.section y hy x ↔ R (y,x) := Iff.rfl
@[simp] theorem all_apply (R : SupportedPred A (X × Y)) (x : X) :
    R.all x ↔ ∀ y, R (x,y) := Iff.rfl
@[simp] theorem ex_apply (R : SupportedPred A (X × Y)) (x : X) :
    R.ex x ↔ ∃ y, R (x,y) := Iff.rfl

@[simp] theorem coe_precomp (p : SupportedPred A Y) (f : X → Y)
    (hf : FinitelySupportedMap A f) : (p.precomp f hf : X → Prop) = (fun x => p (f x)) := rfl
@[simp] theorem coe_precompMap (p : SupportedPred A Y) (f : SupportedMap A X Y) :
    (p.precompMap f : X → Prop) = (fun x => p (f x)) := rfl
@[simp] theorem coe_section (R : SupportedPred A (Y × X)) (y : Y) (hy : FinitelySupported A y) :
    (R.section y hy : X → Prop) = (fun x => R (y,x)) := rfl
/-- Match literal parameter certificates without changing finite support's reducibility. -/
@[simp] theorem coe_section_exists (R : SupportedPred A (Y × X)) (y : Y)
    (hy : ∃ S : Finset A, Supports S y) :
    (R.section y hy : X → Prop) = (fun x => R (y,x)) := rfl
@[simp] theorem coe_all (R : SupportedPred A (X × Y)) :
    (R.all : X → Prop) = (fun x => ∀ y, R (x,y)) := rfl
@[simp] theorem coe_ex (R : SupportedPred A (X × Y)) :
    (R.ex : X → Prop) = (fun x => ∃ y, R (x,y)) := rfl

/- The bound comes from collection membership alone: evaluation is jointly invariant. -/
private theorem supports_unionBody {S : Finset A} {C : SupportedPred A (SupportedPred A X)}
    (hC : SupportsPred S (fun p => C p)) :
    SupportsPred S (fun xp : X × SupportedPred A X => C xp.2 ∧ xp.2 xp.1) :=
  fun π hfix xp => and_congr (hC π hfix xp.2) (smul_apply_smul π xp.2 xp.1)

private theorem supports_interBody {S : Finset A} {C : SupportedPred A (SupportedPred A X)}
    (hC : SupportsPred S (fun p => C p)) :
    SupportsPred S (fun xp : X × SupportedPred A X => C xp.2 → xp.2 xp.1) :=
  fun π hfix xp => imp_congr (hC π hfix xp.2) (smul_apply_smul π xp.2 xp.1)

/-- Union of a supported collection, by existentially quantifying guarded evaluation. -/
def collectionUnion (C : SupportedPred A (SupportedPred A X)) : SupportedPred A X :=
  (ofFun A (fun xp : X × SupportedPred A X => C xp.2 ∧ xp.2 xp.1) (by
    obtain ⟨S, hS⟩ := C.supported
    exact ⟨S, supports_unionBody hS⟩)).ex

/-- Intersection of a supported collection, by universally quantifying guarded evaluation. -/
def collectionInter (C : SupportedPred A (SupportedPred A X)) : SupportedPred A X :=
  (ofFun A (fun xp : X × SupportedPred A X => C xp.2 → xp.2 xp.1) (by
    obtain ⟨S, hS⟩ := C.supported
    exact ⟨S, supports_interBody hS⟩)).all

@[simp] theorem collectionUnion_apply (C : SupportedPred A (SupportedPred A X)) (x : X) :
    C.collectionUnion x ↔ ∃ p, C p ∧ p x := Iff.rfl
@[simp] theorem collectionInter_apply (C : SupportedPred A (SupportedPred A X)) (x : X) :
    C.collectionInter x ↔ ∀ p, C p → p x := Iff.rfl
@[simp] theorem coe_collectionUnion (C : SupportedPred A (SupportedPred A X)) :
    (C.collectionUnion : X → Prop) = (fun x => ∃ p, C p ∧ p x) := rfl
@[simp] theorem coe_collectionInter (C : SupportedPred A (SupportedPred A X)) :
    (C.collectionInter : X → Prop) = (fun x => ∀ p, C p → p x) := rfl

/-! ## Operator action laws -/

@[simp] theorem smul_bot (π : Perm A) : π • (⊥ : SupportedPred A X) = ⊥ := by ext x; rfl
@[simp] theorem smul_top (π : Perm A) : π • (⊤ : SupportedPred A X) = ⊤ := by ext x; rfl
theorem smul_inf (π : Perm A) (p q : SupportedPred A X) :
    π • (p ⊓ q) = (π • p) ⊓ (π • q) := by ext x; rfl
theorem smul_sup (π : Perm A) (p q : SupportedPred A X) :
    π • (p ⊔ q) = (π • p) ⊔ (π • q) := by ext x; rfl
theorem smul_compl (π : Perm A) (p : SupportedPred A X) :
    π • pᶜ = (π • p)ᶜ := by ext x; rfl
theorem smul_himp (π : Perm A) (p q : SupportedPred A X) :
    π • (p ⇨ q) = (π • p) ⇨ (π • q) := by ext x; rfl
theorem smul_sdiff (π : Perm A) (p q : SupportedPred A X) :
    π • (p \ q) = (π • p) \ (π • q) := by ext x; rfl
theorem smul_biimp (π : Perm A) (p q : SupportedPred A X) :
    π • p.biimp q = (π • p).biimp (π • q) := by ext x; rfl

@[simp] theorem smul_le_smul_iff (π : Perm A) (p q : SupportedPred A X) :
    π • p ≤ π • q ↔ p ≤ q := by
  simp only [le_def, smul_apply]
  constructor
  · intro h x
    simpa only [inv_smul_smul] using h (π • x)
  · intro h x
    exact h _

theorem precompMap_smul (π : Perm A) (p : SupportedPred A Y) (f : SupportedMap A X Y) :
    (π • p).precompMap (π • f) = π • p.precompMap f := by
  ext x
  simp only [precompMap_apply, smul_apply, SupportedMap.smul_apply, inv_smul_smul]

theorem section_smul (π : Perm A) (R : SupportedPred A (Y × X)) (y : Y)
    (hy : FinitelySupported A y) :
    (π • R).section (π • y) (hy.smul π) = π • R.section y hy := by
  ext x
  simp only [section_apply, smul_apply, Prod.smul_mk, inv_smul_smul]

theorem all_smul (π : Perm A) (R : SupportedPred A (X × Y)) :
    (π • R).all = π • R.all := by
  ext x
  change (∀ y, R (π⁻¹ • x, π⁻¹ • y)) ↔ ∀ y, R (π⁻¹ • x, y)
  constructor
  · intro h y
    simpa only [inv_smul_smul] using h (π • y)
  · intro h y
    exact h _

theorem ex_smul (π : Perm A) (R : SupportedPred A (X × Y)) :
    (π • R).ex = π • R.ex := by
  ext x
  change (∃ y, R (π⁻¹ • x, π⁻¹ • y)) ↔ ∃ y, R (π⁻¹ • x, y)
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨π⁻¹ • y, hy⟩
  · rintro ⟨y, hy⟩
    exact ⟨π • y, by simpa only [inv_smul_smul] using hy⟩

theorem collectionUnion_smul (π : Perm A) (C : SupportedPred A (SupportedPred A X)) :
    (π • C).collectionUnion = π • C.collectionUnion := by
  ext x
  change (∃ p, C (π⁻¹ • p) ∧ p x) ↔ ∃ p, C p ∧ p (π⁻¹ • x)
  constructor
  · rintro ⟨p, hp, hx⟩
    exact ⟨π⁻¹ • p, hp, (smul_apply_smul π⁻¹ p x).2 hx⟩
  · rintro ⟨p, hp, hx⟩
    exact ⟨π • p, by simpa only [inv_smul_smul] using hp, hx⟩

theorem collectionInter_smul (π : Perm A) (C : SupportedPred A (SupportedPred A X)) :
    (π • C).collectionInter = π • C.collectionInter := by
  ext x
  change (∀ p, C (π⁻¹ • p) → p x) ↔ ∀ p, C p → p (π⁻¹ • x)
  constructor
  · intro h p hp
    exact h (π • p) (by simpa only [inv_smul_smul] using hp)
  · intro h p hp
    exact (smul_apply_smul π⁻¹ p x).1 (h (π⁻¹ • p) hp)

/-! ## Sufficient bounds -/

variable {S T : Finset A} {p q : SupportedPred A X}

theorem supports_bot : Supports (∅ : Finset A) (⊥ : SupportedPred A X) :=
  (supports_iff _ _).2 (supportsPred_const A X False)
theorem supports_top : Supports (∅ : Finset A) (⊤ : SupportedPred A X) :=
  (supports_iff _ _).2 (supportsPred_const A X True)

theorem supports_compl_iff (S : Finset A) (p : SupportedPred A X) :
    Supports S pᶜ ↔ Supports S p := by
  rw [supports_iff, supports_iff]
  exact supportsPred_not_iff S p

section UnionBounds
variable [DecidableEq A]

theorem supports_inf (hp : Supports S p) (hq : Supports T q) : Supports (S ∪ T) (p ⊓ q) :=
  (supports_iff _ _).2 (((supports_iff _ _).1 hp).and ((supports_iff _ _).1 hq))
theorem supports_sup (hp : Supports S p) (hq : Supports T q) : Supports (S ∪ T) (p ⊔ q) :=
  (supports_iff _ _).2 (((supports_iff _ _).1 hp).or ((supports_iff _ _).1 hq))
theorem supports_himp (hp : Supports S p) (hq : Supports T q) : Supports (S ∪ T) (p ⇨ q) :=
  (supports_iff _ _).2 (((supports_iff _ _).1 hp).imp ((supports_iff _ _).1 hq))
theorem supports_sdiff (hp : Supports S p) (hq : Supports T q) : Supports (S ∪ T) (p \ q) :=
  (supports_iff _ _).2 (((supports_iff _ _).1 hp).and ((supports_iff _ _).1 hq).not)
theorem supports_biimp (hp : Supports S p) (hq : Supports T q) :
    Supports (S ∪ T) (p.biimp q) := by
  apply (supports_iff _ _).2
  simpa only [biimp_apply] using ((supports_iff _ _).1 hp).iff ((supports_iff _ _).1 hq)

theorem supports_precomp {p : SupportedPred A Y} {f : X → Y} {hf : FinitelySupportedMap A f}
    (hp : Supports S p) (hfT : SupportsMap T f) : Supports (S ∪ T) (p.precomp f hf) :=
  (supports_iff _ _).2 (((supports_iff _ _).1 hp).precomp hfT)

theorem supports_precompMap {p : SupportedPred A Y} {f : SupportedMap A X Y}
    (hp : Supports S p) (hf : Supports T f) : Supports (S ∪ T) (p.precompMap f) :=
  supports_precomp hp ((SupportedMap.supports_iff _ _).1 hf)

theorem supports_section {R : SupportedPred A (Y × X)} {y : Y} {hy : FinitelySupported A y}
    (hR : Supports S R) (hyT : Supports T y) : Supports (S ∪ T) (R.section y hy) :=
  (supports_iff _ _).2 (((supports_iff _ _).1 hR).section hyT)
end UnionBounds

theorem supports_all {R : SupportedPred A (X × Y)} (hR : Supports S R) : Supports S R.all :=
  (supports_iff _ _).2 ((supports_iff _ _).1 hR).all
theorem supports_ex {R : SupportedPred A (X × Y)} (hR : Supports S R) : Supports S R.ex :=
  (supports_iff _ _).2 ((supports_iff _ _).1 hR).ex

theorem supports_collectionUnion {C : SupportedPred A (SupportedPred A X)} (hC : Supports S C) :
    Supports S C.collectionUnion :=
  (supports_iff _ _).2 (supports_unionBody ((supports_iff _ _).1 hC)).ex
theorem supports_collectionInter {C : SupportedPred A (SupportedPred A X)} (hC : Supports S C) :
    Supports S C.collectionInter :=
  (supports_iff _ _).2 (supports_interBody ((supports_iff _ _).1 hC)).all

/-! ## Least-support consequences -/

section LeastSupport
variable [Infinite A]

@[simp] theorem support_bot : support A (⊥ : SupportedPred A X) = ∅ :=
  Finset.subset_empty.mp (support_minimal A supports_bot)
@[simp] theorem support_top : support A (⊤ : SupportedPred A X) = ∅ :=
  Finset.subset_empty.mp (support_minimal A supports_top)

@[simp] theorem support_compl (p : SupportedPred A X) : support A pᶜ = support A p :=
  le_antisymm
    (support_minimal A ((supports_compl_iff _ _).2 (supports_support A p)))
    (support_minimal A ((supports_compl_iff _ _).1 (supports_support A pᶜ)))

section UnionBounds
variable [DecidableEq A]

theorem support_inf_subset (p q : SupportedPred A X) :
    support A (p ⊓ q) ⊆ support A p ∪ support A q :=
  support_minimal A (supports_inf (supports_support A p) (supports_support A q))
theorem support_sup_subset (p q : SupportedPred A X) :
    support A (p ⊔ q) ⊆ support A p ∪ support A q :=
  support_minimal A (supports_sup (supports_support A p) (supports_support A q))
theorem support_himp_subset (p q : SupportedPred A X) :
    support A (p ⇨ q) ⊆ support A p ∪ support A q :=
  support_minimal A (supports_himp (supports_support A p) (supports_support A q))
theorem support_sdiff_subset (p q : SupportedPred A X) :
    support A (p \ q) ⊆ support A p ∪ support A q :=
  support_minimal A (supports_sdiff (supports_support A p) (supports_support A q))
theorem support_biimp_subset (p q : SupportedPred A X) :
    support A (p.biimp q) ⊆ support A p ∪ support A q :=
  support_minimal A (supports_biimp (supports_support A p) (supports_support A q))

theorem support_precomp_subset (p : SupportedPred A Y) (f : X → Y)
    (hf : FinitelySupportedMap A f) :
    support A (p.precomp f hf) ⊆ support A p ∪ hf.toObject.support :=
  support_minimal A (supports_precomp (supports_support A p)
    ((supportsMap_iff _ _).2 hf.toObject.supports_support))

theorem support_precompMap_subset (p : SupportedPred A Y) (f : SupportedMap A X Y) :
    support A (p.precompMap f) ⊆ support A p ∪ support A f :=
  support_minimal A (supports_precompMap (supports_support A p) (supports_support A f))

theorem support_section_subset (R : SupportedPred A (Y × X)) (y : Y)
    (hy : FinitelySupported A y) : support A (R.section y hy) ⊆ support A R ∪ hy.support :=
  support_minimal A (supports_section (supports_support A R) hy.supports_support)
end UnionBounds

theorem support_all_subset (R : SupportedPred A (X × Y)) : support A R.all ⊆ support A R :=
  support_minimal A (supports_all (supports_support A R))
theorem support_ex_subset (R : SupportedPred A (X × Y)) : support A R.ex ⊆ support A R :=
  support_minimal A (supports_ex (supports_support A R))
theorem support_collectionUnion_subset (C : SupportedPred A (SupportedPred A X)) :
    support A C.collectionUnion ⊆ support A C :=
  support_minimal A (supports_collectionUnion (supports_support A C))
theorem support_collectionInter_subset (C : SupportedPred A (SupportedPred A X)) :
    support A C.collectionInter ⊆ support A C :=
  support_minimal A (supports_collectionInter (supports_support A C))
end LeastSupport

end SupportedPred
end NominalPackage
