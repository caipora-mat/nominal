/-
Copyright (c) 2026 Nominal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nominal contributors
-/
import Package.Foundations.Canonical

/-!
# Freshness

`Fresh A x y` says that the least supports of two nominal elements are disjoint.
`hx.FreshWith hy` retains the same relation for individually supported elements,
and `hx.Fresh a` is its canonical-atom specialization. All refer to the selected
actions and a common explicit atom type, with independent carrier universes.
Generic laws need no decidable equality; swaps and Finset contexts retain it.
No additional action, nominality instance, notation or freshness tactic is installed.
-/

namespace NominalPackage

universe u v w z
open scoped Pointwise

section SupportedPairs

variable {A : Type u} {X : Type v} {Y : Type w}
variable [MulAction (Perm A) X] [MulAction (Perm A) Y] [Infinite A]
variable {x : X} {y : Y}

/-- Two individually supported elements are fresh when their least supports are disjoint. -/
def FinitelySupported.FreshWith (hx : FinitelySupported A x)
    (hy : FinitelySupported A y) : Prop := Disjoint hx.support hy.support

theorem FinitelySupported.freshWith_iff_disjoint_support
    (hx : FinitelySupported A x) (hy : FinitelySupported A y) :
    hx.FreshWith hy ↔ Disjoint hx.support hy.support := Iff.rfl

/-- Freshness is symmetric, even between different carriers. -/
theorem FinitelySupported.freshWith_comm
    (hx : FinitelySupported A x) (hy : FinitelySupported A y) :
    hx.FreshWith hy ↔ hy.FreshWith hx := disjoint_comm

/-- Self-freshness characterizes empty least support. -/
theorem FinitelySupported.freshWith_self_iff (hx : FinitelySupported A x) :
    hx.FreshWith hx ↔ hx.support = ∅ := Finset.disjoint_self_iff_empty _

/-- Disjoint sufficient bounds characterize freshness; clients need not compute least supports. -/
theorem FinitelySupported.freshWith_iff_exists_disjoint_supports
    (hx : FinitelySupported A x) (hy : FinitelySupported A y) :
    hx.FreshWith hy ↔
      ∃ S T : Finset A, Supports S x ∧ Supports T y ∧ Disjoint S T := by
  constructor
  · intro h
    exact ⟨hx.support, hy.support, hx.supports_support, hy.supports_support, h⟩
  · rintro ⟨S, T, hS, hT, hST⟩
    exact hST.mono (hx.support_minimal hS) (hy.support_minimal hT)

theorem FinitelySupported.freshWith_of_supports
    (hx : FinitelySupported A x) (hy : FinitelySupported A y)
    {S T : Finset A} (hS : Supports S x) (hT : Supports T y) (hST : Disjoint S T) :
    hx.FreshWith hy :=
  (hx.freshWith_iff_exists_disjoint_supports hy).2 ⟨S, T, hS, hT, hST⟩

/-- Simultaneous renaming preserves and reflects disjoint dependence on atoms. -/
@[simp] theorem FinitelySupported.freshWith_smul_iff
    (hx : FinitelySupported A x) (hy : FinitelySupported A y) (π : Perm A) :
    (hx.smul π).FreshWith (hy.smul π) ↔ hx.FreshWith hy := by
  classical
  change Disjoint _ _ ↔ Disjoint _ _
  rw [hx.support_smul, hy.support_smul, Perm.smul_finset, Perm.smul_finset]
  exact Finset.disjoint_image π.toEquiv.injective

theorem FinitelySupported.freshWith_smul_right_iff
    (hx : FinitelySupported A x) (hy : FinitelySupported A y) (π : Perm A) :
    hx.FreshWith (hy.smul π) ↔ (hx.smul π⁻¹).FreshWith hy := by
  simpa only [smul_inv_smul] using (hx.smul π⁻¹).freshWith_smul_iff hy π

variable {Z : Type z} [MulAction (Perm A) Z] {z : Z}

@[simp] theorem FinitelySupported.freshWith_prod_left_iff
    (hx : FinitelySupported A x) (hy : FinitelySupported A y) (hz : FinitelySupported A z) :
    (hx.prod hy).FreshWith hz ↔ hx.FreshWith hz ∧ hy.FreshWith hz := by
  classical
  change Disjoint _ _ ↔ Disjoint _ _ ∧ Disjoint _ _
  rw [hx.support_prod hy, Finset.disjoint_union_left]

@[simp] theorem FinitelySupported.freshWith_prod_right_iff
    (hx : FinitelySupported A x) (hy : FinitelySupported A y) (hz : FinitelySupported A z) :
    hx.FreshWith (hy.prod hz) ↔ hx.FreshWith hy ∧ hx.FreshWith hz := by
  classical
  change Disjoint _ _ ↔ Disjoint _ _ ∧ Disjoint _ _
  rw [hy.support_prod hz, Finset.disjoint_union_right]

/-- An equivariant image can lose support, so freshness is preserved but need not reflect. -/
theorem FinitelySupported.freshWith_map_left
    (hx : FinitelySupported A x) (hy : FinitelySupported A y)
    {f : X → Z} (hf : Equivariant A f) (h : hx.FreshWith hy) :
    (hx.map hf).FreshWith hy := h.mono_left (hx.support_map_subset hf)

theorem FinitelySupported.freshWith_map_right
    (hx : FinitelySupported A x) (hy : FinitelySupported A y)
    {f : Y → Z} (hf : Equivariant A f) (h : hx.FreshWith hy) :
    hx.FreshWith (hy.map hf) := h.mono_right (hy.support_map_subset hf)

end SupportedPairs

section Elementwise

variable {A : Type u} {X : Type v}
variable [MulAction (Perm A) X] [Infinite A]
variable {x : X} {S : Finset A}

/-- Atom freshness is the canonical-atom specialization of two-element freshness. -/
def FinitelySupported.Fresh (hx : FinitelySupported A x) (a : A) : Prop :=
  (Nominal.finitelySupported (A := A) a).FreshWith hx

theorem FinitelySupported.fresh_iff_notMem_support
    (hx : FinitelySupported A x) (a : A) :
    hx.Fresh a ↔ a ∉ hx.support := by
  change Disjoint (NominalPackage.support A a) hx.support ↔ a ∉ hx.support
  rw [support_atom, Finset.disjoint_singleton_left]

/-- Any support certificate for the atom gives the same specialization. -/
theorem FinitelySupported.freshWith_atom_left_iff {a : A}
    (ha : FinitelySupported A a) (hx : FinitelySupported A x) :
    ha.FreshWith hx ↔ hx.Fresh a := Iff.rfl

/-- Avoiding any sufficient finite bound establishes freshness. -/
theorem FinitelySupported.fresh_of_supports (hx : FinitelySupported A x)
    (hS : Supports S x) {a : A} (ha : a ∉ S) : hx.Fresh a :=
  (hx.fresh_iff_notMem_support a).2 (fun h => ha (hx.support_minimal hS h))

/-- Simultaneous renaming preserves and reflects atom freshness. -/
@[simp] theorem FinitelySupported.fresh_smul_iff
    (hx : FinitelySupported A x) (π : Perm A) (a : A) :
    (hx.smul π).Fresh (π a) ↔ hx.Fresh a :=
  (Nominal.finitelySupported (A := A) a).freshWith_smul_iff hx π

/-- Transfer renaming from the supported element to the inverse image of the atom. -/
theorem FinitelySupported.fresh_smul_iff_inv
    (hx : FinitelySupported A x) (π : Perm A) (a : A) :
    (hx.smul π).Fresh a ↔ hx.Fresh (π⁻¹ a) := by
  simpa only [Perm.apply_inv_apply] using hx.fresh_smul_iff π (π⁻¹ a)

/-- Swapping fresh endpoints fixes the element, including when they coincide. -/
theorem FinitelySupported.swap_smul_eq_of_fresh [DecidableEq A]
    (hx : FinitelySupported A x) {a b : A}
    (ha : hx.Fresh a) (hb : hx.Fresh b) : Perm.swap a b • x = x :=
  swap_smul_eq_of_supports hx.supports_support
    ((hx.fresh_iff_notMem_support a).1 ha) ((hx.fresh_iff_notMem_support b).1 hb)

/-- Product freshness is componentwise even without nominality of the carriers. -/
@[simp] theorem FinitelySupported.fresh_prod_iff
    {Y : Type w} [MulAction (Perm A) Y] {y : Y}
    (hx : FinitelySupported A x) (hy : FinitelySupported A y) (a : A) :
    (hx.prod hy).Fresh a ↔ hx.Fresh a ∧ hy.Fresh a :=
  (Nominal.finitelySupported (A := A) a).freshWith_prod_right_iff hx hy

/-- Infinite atoms supply a fresh atom for each individually supported element. -/
theorem FinitelySupported.exists_fresh (hx : FinitelySupported A x) :
    ∃ a : A, hx.Fresh a := by
  obtain ⟨a, ha⟩ := Finset.exists_notMem hx.support
  exact ⟨a, (hx.fresh_iff_notMem_support a).2 ha⟩

/-- Choose fresh for the element while avoiding an additional explicit finite set.
The union is a proof-local witness, so no decidable-equality parameter is needed. -/
theorem FinitelySupported.exists_fresh_notMem
    (hx : FinitelySupported A x) (S : Finset A) :
    ∃ a : A, a ∉ S ∧ hx.Fresh a := by
  classical
  obtain ⟨a, ha⟩ := Finset.exists_notMem (S ∪ hx.support)
  rw [Finset.notMem_union] at ha
  exact ⟨a, ha.1, (hx.fresh_iff_notMem_support a).2 ha.2⟩

/-- A finite atom set is fresh exactly when each member is fresh. -/
theorem FinitelySupported.freshWith_finset_left_iff [DecidableEq A]
    (S : Finset A) (hx : FinitelySupported A x) :
    (supports_finset A S).finitelySupported.FreshWith hx ↔ ∀ a ∈ S, hx.Fresh a := by
  simp only [hx.fresh_iff_notMem_support]
  change Disjoint _ hx.support ↔ _
  rw [← NominalPackage.support_eq A S (supports_finset A S).finitelySupported, support_finset]
  exact Finset.disjoint_left

theorem FinitelySupported.freshWith_finset_right_iff [DecidableEq A]
    (hx : FinitelySupported A x) (S : Finset A) :
    hx.FreshWith (supports_finset A S).finitelySupported ↔ ∀ a ∈ S, hx.Fresh a :=
  (hx.freshWith_comm _).trans (FinitelySupported.freshWith_finset_left_iff S hx)

end Elementwise

section NominalPairs

variable (A : Type u) {X : Type v} {Y : Type w}
variable [MulAction (Perm A) X] [MulAction (Perm A) Y]
variable [Infinite A] [Nominal A X] [Nominal A Y]

/-- Pitts' freshness relation: disjoint least supports of two nominal elements. -/
def Fresh (x : X) (y : Y) : Prop := Disjoint (support A x) (support A y)

theorem fresh_iff_disjoint_support (x : X) (y : Y) :
    Fresh A x y ↔ Disjoint (support A x) (support A y) := Iff.rfl

/-- Carrier and elementwise freshness agree for any two certificates of the same actions. -/
theorem fresh_iff_freshWith (x : X) (y : Y)
    (hx : FinitelySupported A x) (hy : FinitelySupported A y) :
    Fresh A x y ↔ hx.FreshWith hy := Iff.rfl

theorem fresh_comm (x : X) (y : Y) : Fresh A x y ↔ Fresh A y x := disjoint_comm

theorem fresh_self_iff (x : X) : Fresh A x x ↔ support A x = ∅ :=
  Finset.disjoint_self_iff_empty _

theorem fresh_iff_exists_disjoint_supports (x : X) (y : Y) :
    Fresh A x y ↔ ∃ S T : Finset A, Supports S x ∧ Supports T y ∧ Disjoint S T :=
  (Nominal.finitelySupported (A := A) x).freshWith_iff_exists_disjoint_supports
    (Nominal.finitelySupported (A := A) y)

theorem fresh_of_disjoint_supports {x : X} {y : Y} {S T : Finset A}
    (hS : Supports S x) (hT : Supports T y) (hST : Disjoint S T) : Fresh A x y :=
  (fresh_iff_exists_disjoint_supports A x y).2 ⟨S, T, hS, hT, hST⟩

@[simp] theorem fresh_smul_both_iff (π : Perm A) (x : X) (y : Y) :
    Fresh A (π • x) (π • y) ↔ Fresh A x y :=
  (Nominal.finitelySupported (A := A) x).freshWith_smul_iff
    (Nominal.finitelySupported (A := A) y) π

theorem fresh_smul_right_iff (π : Perm A) (x : X) (y : Y) :
    Fresh A x (π • y) ↔ Fresh A (π⁻¹ • x) y :=
  (Nominal.finitelySupported (A := A) x).freshWith_smul_right_iff
    (Nominal.finitelySupported (A := A) y) π

variable {Z : Type z} [MulAction (Perm A) Z] [Nominal A Z]

@[simp] theorem fresh_prod_left_iff (x : X) (y : Y) (z : Z) :
    Fresh A (x, y) z ↔ Fresh A x z ∧ Fresh A y z :=
  (Nominal.finitelySupported (A := A) x).freshWith_prod_left_iff
    (Nominal.finitelySupported (A := A) y) (Nominal.finitelySupported (A := A) z)

@[simp] theorem fresh_prod_right_iff (x : X) (y : Y) (z : Z) :
    Fresh A x (y, z) ↔ Fresh A x y ∧ Fresh A x z :=
  (Nominal.finitelySupported (A := A) x).freshWith_prod_right_iff
    (Nominal.finitelySupported (A := A) y) (Nominal.finitelySupported (A := A) z)

theorem fresh_map_left {f : X → Z} (hf : Equivariant A f) {x : X} {y : Y}
    (h : Fresh A x y) : Fresh A (f x) y :=
  (Nominal.finitelySupported (A := A) x).freshWith_map_left
    (Nominal.finitelySupported (A := A) y) hf h

theorem fresh_map_right {f : Y → Z} (hf : Equivariant A f) {x : X} {y : Y}
    (h : Fresh A x y) : Fresh A x (f y) :=
  (Nominal.finitelySupported (A := A) x).freshWith_map_right
    (Nominal.finitelySupported (A := A) y) hf h

end NominalPairs

section NominalCarriers

variable (A : Type u) {X : Type v}
variable [MulAction (Perm A) X] [Infinite A] [Nominal A X]

theorem fresh_iff_notMem_support (a : A) (x : X) :
    Fresh A a x ↔ a ∉ support A x :=
  (Nominal.finitelySupported (A := A) x).fresh_iff_notMem_support a

/-- Carrier freshness agrees with any elementwise certificate of the same value/action. -/
theorem fresh_iff (a : A) (x : X) (hx : FinitelySupported A x) :
    Fresh A a x ↔ hx.Fresh a := Iff.rfl

theorem fresh_of_supports {x : X} {S : Finset A}
    (hS : Supports S x) {a : A} (ha : a ∉ S) : Fresh A a x :=
  (Nominal.finitelySupported (A := A) x).fresh_of_supports hS ha

@[simp] theorem fresh_smul_iff (π : Perm A) (a : A) (x : X) :
    Fresh A (π a) (π • x) ↔ Fresh A a x :=
  (Nominal.finitelySupported (A := A) x).fresh_smul_iff π a

theorem fresh_smul_iff_inv (π : Perm A) (a : A) (x : X) :
    Fresh A a (π • x) ↔ Fresh A (π⁻¹ a) x :=
  (Nominal.finitelySupported (A := A) x).fresh_smul_iff_inv π a

theorem swap_smul_eq_of_fresh [DecidableEq A] {x : X} {a b : A}
    (ha : Fresh A a x) (hb : Fresh A b x) : Perm.swap a b • x = x :=
  (Nominal.finitelySupported (A := A) x).swap_smul_eq_of_fresh ha hb

@[simp] theorem fresh_prod_iff {Y : Type w}
    [MulAction (Perm A) Y] [Nominal A Y] (a : A) (x : X) (y : Y) :
    Fresh A a (x, y) ↔ Fresh A a x ∧ Fresh A a y :=
  (Nominal.finitelySupported (A := A) x).fresh_prod_iff
    (Nominal.finitelySupported (A := A) y) a

/-- Choose a fresh atom using the nominality certificate. -/
theorem exists_fresh (x : X) : ∃ a : A, Fresh A a x :=
  (Nominal.finitelySupported (A := A) x).exists_fresh

/-- Choose fresh for a nominal context and outside a supplied finite exclusion set. -/
theorem exists_fresh_notMem (S : Finset A) (x : X) :
    ∃ a : A, a ∉ S ∧ Fresh A a x :=
  (Nominal.finitelySupported (A := A) x).exists_fresh_notMem S

end NominalCarriers

/-- Freshness for a canonical atom is inequality. -/
@[simp] theorem fresh_atom_iff (A : Type u) [Infinite A] (a b : A) :
    Fresh A a b ↔ a ≠ b := by
  rw [fresh_iff_notMem_support, support_atom, Finset.mem_singleton]

/-- Every atom is fresh for discrete data. -/
@[simp] theorem fresh_discrete (A : Type u) [Infinite A]
    {X : Type v} (a : A) (d : Discrete A X) : Fresh A a d := by
  rw [fresh_iff_notMem_support, support_discrete]
  exact Finset.notMem_empty a

/-- Freshness for a finite atom set is ordinary nonmembership. -/
@[simp] theorem fresh_finset_iff (A : Type u) [Infinite A] [DecidableEq A]
    (a : A) (S : Finset A) : Fresh A a S ↔ a ∉ S := by
  rw [fresh_iff_notMem_support, support_finset]

/-- Freshness against an atom on the right is the same nonmembership condition. -/
theorem fresh_atom_right_iff (A : Type u) {X : Type v}
    [MulAction (Perm A) X] [Infinite A] [Nominal A X] (x : X) (a : A) :
    Fresh A x a ↔ a ∉ support A x :=
  (fresh_comm A x a).trans (fresh_iff_notMem_support A a x)

@[simp] theorem fresh_discrete_left (A : Type u) {D : Type v} {X : Type w}
    [MulAction (Perm A) X] [Infinite A] [Nominal A X] (d : Discrete A D) (x : X) :
    Fresh A d x := by
  rw [fresh_iff_disjoint_support, support_discrete]
  exact disjoint_bot_left

@[simp] theorem fresh_discrete_right (A : Type u) {X : Type v} {D : Type w}
    [MulAction (Perm A) X] [Infinite A] [Nominal A X] (x : X) (d : Discrete A D) :
    Fresh A x d := (fresh_comm A d x).1 (fresh_discrete_left A d x)

@[simp] theorem fresh_finset_left_iff (A : Type u) {X : Type v}
    [MulAction (Perm A) X] [Infinite A] [Nominal A X] [DecidableEq A]
    (S : Finset A) (x : X) : Fresh A S x ↔ ∀ a ∈ S, Fresh A a x := by
  simp only [fresh_iff_notMem_support]
  rw [fresh_iff_disjoint_support, support_finset]
  exact Finset.disjoint_left

@[simp] theorem fresh_finset_right_iff (A : Type u) {X : Type v}
    [MulAction (Perm A) X] [Infinite A] [Nominal A X] [DecidableEq A]
    (x : X) (S : Finset A) : Fresh A x S ↔ ∀ a ∈ S, Fresh A a x :=
  (fresh_comm A x S).trans (fresh_finset_left_iff A S x)

@[simp] theorem fresh_finsets_iff (A : Type u) [Infinite A] [DecidableEq A]
    (S T : Finset A) : Fresh A S T ↔ Disjoint S T := by
  rw [fresh_iff_disjoint_support, support_finset, support_finset]

end NominalPackage
