/-
Copyright (c) 2026 Nominal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nominal contributors
-/
import Package.Foundations.Nominal

/-!
# Canonical nominality and support

These certificates refer to the existing canonical atom, discrete, product and
finite-set actions. They introduce no action and require no infinite atom type.
Finite atom sets retain the consumer's `Pointwise` scope and decidable equality.
Over infinite atoms, the exact least supports follow by both inclusions.
The product equation also applies to individually supported components.
-/

namespace NominalPackage

universe u v w

/-- Its singleton supports an atom under the inherited permutation action. -/
theorem supports_atom (A : Type u) (a : A) : Supports ({a} : Finset A) a :=
  MulAction.supports_of_mem (Perm A) (Finset.mem_singleton_self a)

/-- Discrete data is supported by the empty bound, regardless of its contents. -/
theorem supports_discrete (A : Type u) {X : Type v} (d : Discrete A X) :
    Supports (∅ : Finset A) d :=
  (supports_empty_iff d).2 (fun _ => rfl)

instance instNominalAtom (A : Type u) : Nominal A A where
  finitelySupported a := (supports_atom A a).finitelySupported

instance instNominalDiscrete (A : Type u) (X : Type v) :
    Nominal A (Discrete A X) where
  finitelySupported d := (supports_discrete A d).finitelySupported

instance instNominalProd (A : Type u) {X : Type v} {Y : Type w}
    [MulAction (Perm A) X] [MulAction (Perm A) Y]
    [Nominal A X] [Nominal A Y] : Nominal A (X × Y) where
  finitelySupported p := (Nominal.finitelySupported (A := A) p.1).prod
    (Nominal.finitelySupported (A := A) p.2)

open scoped Pointwise

/-- A finite atom set supports itself under the existing image action. -/
theorem supports_finset (A : Type u) [DecidableEq A] (S : Finset A) :
    Supports S S := by
  apply (supports_iff S S).2
  intro π hfix
  rw [Perm.smul_finset]
  exact (Finset.image_congr (fun a ha => hfix a ha)).trans Finset.image_id'

/-- Nominality of the existing scoped finite-set image action. -/
theorem instNominalFinset (A : Type u) [DecidableEq A] : Nominal A (Finset A) where
  finitelySupported S := (supports_finset A S).finitelySupported

scoped[Pointwise] attribute [instance] NominalPackage.instNominalFinset

/-- An atom's least support is its singleton under the canonical action. -/
@[simp] theorem support_atom (A : Type u) [Infinite A] (a : A) :
    support A a = {a} := by
  classical
  apply le_antisymm (support_minimal A (supports_atom A a))
  apply Finset.singleton_subset_iff.mpr
  by_contra ha
  obtain ⟨b, hb⟩ := Finset.exists_notMem (insert a (support A a))
  simp only [Finset.mem_insert, not_or] at hb
  have hfix := swap_smul_eq_of_supports (supports_support A a) ha hb.2
  exact hb.1 (by simpa only [Perm.smul_atom, Perm.swap_apply_left] using hfix)

/-- Discrete values have empty least support, with no assumptions on their data. -/
@[simp] theorem support_discrete (A : Type u) [Infinite A]
    {X : Type v} (d : Discrete A X) : support A d = ∅ :=
  (support_eq_empty_iff A d).2 (fun _ => rfl)

/-- Product least support is exactly the union, even without nominal carriers. -/
theorem FinitelySupported.support_prod {A : Type u} {X : Type v} {Y : Type w}
    [MulAction (Perm A) X] [MulAction (Perm A) Y]
    [Infinite A] [DecidableEq A] {x : X} {y : Y}
    (hx : FinitelySupported A x) (hy : FinitelySupported A y) :
    (hx.prod hy).support = hx.support ∪ hy.support := by
  apply le_antisymm
  · exact (hx.prod hy).support_minimal (supports_prod hx.supports_support hy.supports_support)
  · have h := (supports_prod_iff (hx.prod hy).support x y).1 (hx.prod hy).supports_support
    exact Finset.union_subset_iff.mpr ⟨hx.support_minimal h.1, hy.support_minimal h.2⟩

/-- Least support under the componentwise action is the union of component supports. -/
@[simp] theorem support_prod (A : Type u) {X : Type v} {Y : Type w}
    [MulAction (Perm A) X] [MulAction (Perm A) Y]
    [Infinite A] [DecidableEq A] [Nominal A X] [Nominal A Y]
    (x : X) (y : Y) : support A (x, y) = support A x ∪ support A y :=
  (Nominal.finitelySupported (A := A) x).support_prod (Nominal.finitelySupported (A := A) y)

/-- A finite atom set is its own least support under the existing image action.
For the reverse inclusion, swapping a member with an atom outside both the set
and a proposed supporting bound contradicts image fixation. -/
@[simp] theorem support_finset (A : Type u) [Infinite A] [DecidableEq A]
    (S : Finset A) : support A S = S := by
  apply le_antisymm (support_minimal A (supports_finset A S))
  intro a ha
  by_contra haL
  obtain ⟨b, hb⟩ := Finset.exists_notMem (S ∪ support A S)
  rw [Finset.notMem_union] at hb
  have hfix := swap_smul_eq_of_supports (supports_support A S) haL hb.2
  have hmem : b ∈ Perm.swap a b • S := by
    rw [Perm.smul_finset]
    simpa only [Perm.swap_apply_left] using Finset.mem_image_of_mem (Perm.swap a b) ha
  exact hb.1 (hfix ▸ hmem)

end NominalPackage
