/-
Copyright (c) 2026 Nominal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nominal contributors
-/
import Package.Foundations.FunctionAction
import Package.Foundations.Freshness

/-!
# Ordinary function support certificates

These certificates concern conjugation, not the pointwise action on bare arrows.
Sufficient bounds and existential witnesses need no nominal carriers. Least
support and freshness reuse the evidence for the corresponding function object.
-/

namespace NominalPackage
universe u v w z t

/-- An ordinary map commutes with permutations fixing the finite atom bound. -/
def SupportsMap {A : Type u} {X : Type v} {Y : Type w}
    [MulAction (Perm A) X] [MulAction (Perm A) Y] (S : Finset A) (f : X → Y) : Prop :=
  ∀ π : Perm A, (∀ a ∈ S, π a = a) → ∀ x, f (π • x) = π • f x

/-- Existence of a finite conjugation-support bound for an ordinary map.
This alias stays reducible so literal existential evidence works with constructor simp. -/
abbrev FinitelySupportedMap (A : Type u) {X : Type v} {Y : Type w}
    [MulAction (Perm A) X] [MulAction (Perm A) Y] (f : X → Y) : Prop :=
  ∃ S : Finset A, SupportsMap S f

variable {A : Type u} {X : Type v} {Y : Type w} {Z : Type z}
variable [MulAction (Perm A) X] [MulAction (Perm A) Y] [MulAction (Perm A) Z]
variable {S T : Finset A} {f : X → Y} {g : Y → Z} {x : X}

/-- The logical certificate is exactly support in the conjugation carrier. -/
theorem supportsMap_iff (S : Finset A) (f : X → Y) :
    SupportsMap S f ↔ Supports S (FunctionObject.ofFun (Perm A) f) :=
  (FunctionObject.supports_iff (Perm A) (S : Set A) f).symm

theorem finitelySupportedMap_iff (A : Type u) {X : Type v} {Y : Type w}
    [MulAction (Perm A) X] [MulAction (Perm A) Y] (f : X → Y) :
    FinitelySupportedMap A f ↔ FinitelySupported A (FunctionObject.ofFun (Perm A) f) :=
  exists_congr fun S => supportsMap_iff S f

theorem FinitelySupportedMap.toObject (hf : FinitelySupportedMap A f) :
    FinitelySupported A (FunctionObject.ofFun (Perm A) f) := (finitelySupportedMap_iff A f).1 hf

theorem supportsMap_empty_iff (A : Type u) {X : Type v} {Y : Type w}
    [MulAction (Perm A) X] [MulAction (Perm A) Y] (f : X → Y) :
    SupportsMap (∅ : Finset A) f ↔ Equivariant A f := by
  simp only [SupportsMap, Finset.notMem_empty, IsEmpty.forall_iff, implies_true,
    forall_const, Equivariant]

/-- Package equivariance uses Mathlib's existing bundle when a map value is wanted. -/
def Equivariant.toMulActionHom (hf : Equivariant A f) : X →[Perm A] Y := ⟨f, hf⟩
@[simp] theorem Equivariant.toMulActionHom_apply (hf : Equivariant A f) (x : X) :
    hf.toMulActionHom x = f x := rfl

theorem equivariant_coe_mulActionHom (h : X →[Perm A] Y) : Equivariant A (h : X → Y) := h.map_smul

theorem SupportsMap.mono (hf : SupportsMap S f) (hST : S ⊆ T) : SupportsMap T f :=
  (supportsMap_iff T f).2 (supports_mono hST ((supportsMap_iff S f).1 hf))
theorem SupportsMap.finitelySupported (hf : SupportsMap S f) : FinitelySupportedMap A f := ⟨S, hf⟩

theorem SupportsMap.apply_same (hf : SupportsMap S f) (hx : Supports S x) : Supports S (f x) := by
  intro π hfix
  have he := hf π (fun _ ha => hfix ha) x
  rw [hx π hfix] at he
  exact he.symm

theorem supportsMap_id (A : Type u) (X : Type v) [MulAction (Perm A) X] :
    SupportsMap (∅ : Finset A) (_root_.id : X → X) := (supportsMap_empty_iff A _).2 (Equivariant.id A)

theorem supportsMap_const {y : Y} (hy : Supports S y) : SupportsMap S (Function.const X y) :=
  fun π hfix _ => (hy π (fun _ ha => hfix _ ha)).symm

theorem supportsMap_const_iff [Nonempty X] (S : Finset A) (y : Y) :
    SupportsMap S (Function.const X y) ↔ Supports S y := by
  refine ⟨?_, supportsMap_const⟩
  intro h π hfix
  obtain ⟨x⟩ := ‹Nonempty X›
  exact (h π (fun _ ha => hfix ha) x).symm

theorem supportsMap_of_isEmpty [IsEmpty X] (S : Finset A) (f : X → Y) : SupportsMap S f :=
  fun _ _ x => isEmptyElim x

theorem SupportsMap.comp_same (hg : SupportsMap S g) (hf : SupportsMap S f) :
    SupportsMap S (g ∘ f) := by
  intro π hfix x
  change g (f (π • x)) = π • g (f x)
  rw [hf π hfix, hg π hfix]

theorem supportsMap_pair_iff (S : Finset A) (f : X → Y) (h : X → Z) :
    SupportsMap S (fun x => (f x, h x)) ↔ SupportsMap S f ∧ SupportsMap S h := by
  constructor
  · intro hp
    exact ⟨fun π hfix x => congrArg Prod.fst (hp π hfix x),
      fun π hfix x => congrArg Prod.snd (hp π hfix x)⟩
  · rintro ⟨hf, hh⟩ π hfix x
    exact Prod.ext (hf π hfix x) (hh π hfix x)

theorem SupportsMap.section_same {P : Type t} [MulAction (Perm A) P]
    {F : P × X → Y} {p : P} (hF : SupportsMap S F) (hp : Supports S p) :
    SupportsMap S (fun x => F (p,x)) := by
  intro π hfix x
  have he := hF π hfix (p,x)
  simpa only [Prod.smul_mk, hp π (fun _ ha => hfix _ ha)] using he

theorem Equivariant.supportsMap_section {P : Type t} [MulAction (Perm A) P]
    {F : P × X → Y} (hF : Equivariant A F) {p : P} (hp : Supports S p) :
    SupportsMap S (fun x => F (p,x)) :=
  SupportsMap.section_same (fun π _ x => hF π x) hp

section FiniteBounds
variable [DecidableEq A]
open scoped Pointwise

theorem SupportsMap.apply (hf : SupportsMap S f) (hx : Supports T x) : Supports (S ∪ T) (f x) :=
  (hf.mono Finset.subset_union_left).apply_same (supports_mono Finset.subset_union_right hx)
theorem SupportsMap.comp (hg : SupportsMap S g) (hf : SupportsMap T f) : SupportsMap (S ∪ T) (g ∘ f) :=
  (hg.mono Finset.subset_union_left).comp_same (hf.mono Finset.subset_union_right)
theorem SupportsMap.pair {h : X → Z} (hf : SupportsMap S f) (hh : SupportsMap T h) :
    SupportsMap (S ∪ T) (fun x => (f x, h x)) :=
  (supportsMap_pair_iff _ _ _).2 ⟨hf.mono Finset.subset_union_left, hh.mono Finset.subset_union_right⟩
theorem SupportsMap.section {P : Type t} [MulAction (Perm A) P]
    {F : P × X → Y} {p : P} (hF : SupportsMap S F) (hp : Supports T p) :
    SupportsMap (S ∪ T) (fun x => F (p,x)) :=
  (hF.mono Finset.subset_union_left).section_same (supports_mono Finset.subset_union_right hp)

theorem supportsMap_smul_iff (π : Perm A) (S : Finset A) (f : X → Y) :
    SupportsMap (π • S) (fun x => π • f (π⁻¹ • x)) ↔ SupportsMap S f := by
  rw [supportsMap_iff, supportsMap_iff]
  exact supports_smul_iff π S (FunctionObject.ofFun (Perm A) f)
end FiniteBounds

theorem FinitelySupportedMap.apply (hf : FinitelySupportedMap A f) (hx : FinitelySupported A x) :
    FinitelySupported A (f x) := by
  classical
  obtain ⟨S, hS⟩ := hf
  obtain ⟨T, hT⟩ := hx
  exact (hS.apply hT).finitelySupported
theorem FinitelySupportedMap.comp (hg : FinitelySupportedMap A g) (hf : FinitelySupportedMap A f) :
    FinitelySupportedMap A (g ∘ f) := by
  classical
  obtain ⟨S, hS⟩ := hg
  obtain ⟨T, hT⟩ := hf
  exact (hS.comp hT).finitelySupported
theorem FinitelySupportedMap.pair {h : X → Z} (hf : FinitelySupportedMap A f)
    (hh : FinitelySupportedMap A h) : FinitelySupportedMap A (fun x => (f x, h x)) := by
  classical
  obtain ⟨S, hS⟩ := hf
  obtain ⟨T, hT⟩ := hh
  exact (hS.pair hT).finitelySupported
theorem FinitelySupportedMap.section {P : Type t} [MulAction (Perm A) P]
    {F : P × X → Y} {p : P} (hF : FinitelySupportedMap A F) (hp : FinitelySupported A p) :
    FinitelySupportedMap A (fun x => F (p,x)) := by
  classical
  obtain ⟨S, hS⟩ := hF
  obtain ⟨T, hT⟩ := hp
  exact (hS.section hT).finitelySupported

theorem finitelySupportedMap_const {y : Y} (hy : FinitelySupported A y) :
    FinitelySupportedMap A (Function.const X y) := by
  obtain ⟨S, hS⟩ := hy
  exact ⟨S, supportsMap_const hS⟩

theorem finitelySupportedMap_const_iff [Nonempty X] (y : Y) :
    FinitelySupportedMap A (Function.const X y) ↔ FinitelySupported A y :=
  exists_congr fun S => supportsMap_const_iff S y

/-- Renaming a supported ordinary map transports its certificate. -/
theorem FinitelySupportedMap.smul (hf : FinitelySupportedMap A f) (π : Perm A) :
    FinitelySupportedMap A (fun x => π • f (π⁻¹ • x)) :=
  (finitelySupportedMap_iff A _).2 (hf.toObject.smul π)

theorem Equivariant.finitelySupportedMap (hf : Equivariant A f) : FinitelySupportedMap A f :=
  ⟨∅, (supportsMap_empty_iff A f).2 hf⟩

theorem Equivariant.finitelySupportedMap_section {P : Type t} [MulAction (Perm A) P]
    {F : P × X → Y} (hF : Equivariant A F) {p : P} (hp : FinitelySupported A p) :
    FinitelySupportedMap A (fun x => F (p,x)) := hF.finitelySupportedMap.section hp

theorem supportsMap_curry_iff (S : Finset A) (f : X × Y → Z) :
    SupportsMap S (fun x => FunctionObject.ofFun (Perm A) (fun y => f (x,y))) ↔ SupportsMap S f := by
  rw [supportsMap_iff, supportsMap_iff]
  exact FunctionObject.supports_curry_iff (S : Set A) _
theorem supportsMap_uncurry_iff (S : Finset A) (H : X → FunctionObject (Perm A) Y Z) :
    SupportsMap S (fun p : X × Y => H p.1 p.2) ↔ SupportsMap S H := by
  rw [supportsMap_iff, supportsMap_iff]
  exact FunctionObject.supports_uncurry_iff (S : Set A) _
theorem FinitelySupportedMap.curry {f : X × Y → Z} (hf : FinitelySupportedMap A f) :
    FinitelySupportedMap A (fun x => FunctionObject.ofFun (Perm A) (fun y => f (x,y))) := by
  obtain ⟨S, hS⟩ := hf
  exact ⟨S, (supportsMap_curry_iff S f).2 hS⟩
theorem FinitelySupportedMap.uncurry {H : X → FunctionObject (Perm A) Y Z} (hH : FinitelySupportedMap A H) :
    FinitelySupportedMap A (fun p : X × Y => H p.1 p.2) := by
  obtain ⟨S, hS⟩ := hH
  exact ⟨S, (supportsMap_uncurry_iff S H).2 hS⟩

section LeastSupport
variable [Infinite A]

private theorem support_eq_of_iff {x : X} {y : Y} (hx : FinitelySupported A x)
    (hy : FinitelySupported A y) (h : ∀ S : Finset A, Supports S x ↔ Supports S y) : hx.support = hy.support :=
  le_antisymm (hx.support_minimal ((h _).2 hy.supports_support))
    (hy.support_minimal ((h _).1 hx.supports_support))

theorem FinitelySupportedMap.support_eq_empty_iff (hf : FinitelySupportedMap A f) :
    hf.toObject.support = ∅ ↔ Equivariant A f := by
  rw [hf.toObject.support_eq_empty_iff]
  exact forall_congr' (fun π => FunctionObject.smul_eq_iff π _)

theorem FinitelySupportedMap.support_curry {f : X × Y → Z} (hf : FinitelySupportedMap A f) :
    hf.curry.toObject.support = hf.toObject.support :=
  support_eq_of_iff _ _ (fun S => FunctionObject.supports_curry_iff (S : Set A) _)
theorem FinitelySupportedMap.support_uncurry {H : X → FunctionObject (Perm A) Y Z}
    (hH : FinitelySupportedMap A H) : hH.uncurry.toObject.support = hH.toObject.support :=
  support_eq_of_iff _ _ (fun S => FunctionObject.supports_uncurry_iff (S : Set A) _)
theorem FinitelySupportedMap.support_const (X : Type v) [MulAction (Perm A) X] [Nonempty X]
    {y : Y} (hy : FinitelySupported A y) :
    (finitelySupportedMap_const (X := X) hy).toObject.support = hy.support :=
  support_eq_of_iff _ _ (fun S => (supportsMap_iff S _).symm.trans (supportsMap_const_iff S y))

variable [DecidableEq A]

theorem FinitelySupportedMap.support_apply_subset (hf : FinitelySupportedMap A f)
    (hx : FinitelySupported A x) : (hf.apply hx).support ⊆ hf.toObject.support ∪ hx.support :=
  (hf.apply hx).support_minimal (((supportsMap_iff _ f).2 hf.toObject.supports_support).apply hx.supports_support)
theorem FinitelySupportedMap.support_comp_subset (hg : FinitelySupportedMap A g) (hf : FinitelySupportedMap A f) :
    (hg.comp hf).toObject.support ⊆ hg.toObject.support ∪ hf.toObject.support :=
  (hg.comp hf).toObject.support_minimal ((supportsMap_iff _ _).1
    (((supportsMap_iff _ g).2 hg.toObject.supports_support).comp ((supportsMap_iff _ f).2 hf.toObject.supports_support)))
theorem FinitelySupportedMap.support_section_subset {P : Type t} [MulAction (Perm A) P]
    {F : P × X → Y} {p : P} (hF : FinitelySupportedMap A F) (hp : FinitelySupported A p) :
    (hF.section hp).toObject.support ⊆ hF.toObject.support ∪ hp.support :=
  (hF.section hp).toObject.support_minimal ((supportsMap_iff _ _).1
    (((supportsMap_iff _ F).2 hF.toObject.supports_support).section hp.supports_support))
theorem FinitelySupportedMap.support_pair {h : X → Z} (hf : FinitelySupportedMap A f)
    (hh : FinitelySupportedMap A h) :
    (hf.pair hh).toObject.support = hf.toObject.support ∪ hh.toObject.support := by
  apply le_antisymm
  · exact (hf.pair hh).toObject.support_minimal ((supportsMap_iff _ _).1
      (((supportsMap_iff _ f).2 hf.toObject.supports_support).pair ((supportsMap_iff _ h).2 hh.toObject.supports_support)))
  · have hs := (supportsMap_pair_iff _ f h).1 ((supportsMap_iff _ _).2 (hf.pair hh).toObject.supports_support)
    exact Finset.union_subset_iff.mpr
      ⟨hf.toObject.support_minimal ((supportsMap_iff _ _).1 hs.1), hh.toObject.support_minimal ((supportsMap_iff _ _).1 hs.2)⟩
end LeastSupport

theorem FinitelySupportedMap.freshWith_apply [Infinite A] (hf : FinitelySupportedMap A f)
    (hx : FinitelySupported A x) {z : Z} (hz : FinitelySupported A z)
    (hF : hf.toObject.FreshWith hz) (hX : hx.FreshWith hz) : (hf.apply hx).FreshWith hz := by
  classical
  exact Finset.disjoint_of_subset_left (hf.support_apply_subset hx) (Finset.disjoint_union_left.mpr ⟨hF, hX⟩)

theorem FinitelySupportedMap.fresh_apply [Infinite A] (hf : FinitelySupportedMap A f)
    (hx : FinitelySupported A x) {a : A} (hF : hf.toObject.Fresh a) (hX : hx.Fresh a) :
    (hf.apply hx).Fresh a := by
  classical
  rw [FinitelySupported.fresh_iff_notMem_support] at *
  exact fun ha => (Finset.mem_union.mp (hf.support_apply_subset hx ha)).elim hF hX
end NominalPackage
