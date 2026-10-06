import Package.Foundations.Canonical
import Mathlib.Data.Finset.Disjoint

/-!
Research probe, 2026-10-06: natural generalizations of the Package foundation.
Checked against Lean/Mathlib v4.34.1 (Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612).
This file is standalone research evidence, outside production Package imports.
See docs/research/2026-10-06-foundation-generalizations.md for status and limits.
-/

open NominalPackage
open scoped Pointwise

namespace CanonicalGeneralizationProbe

universe u v w z

variable {A : Type u} {X : Type v} {Y : Type w} {Z : Type z}
variable [MulAction (Perm A) X] [MulAction (Perm A) Y] [MulAction (Perm A) Z]
variable [Infinite A]
variable {x : X} {y : Y} {z : Z}

def FreshWithP (hx : FinitelySupported A x) (hy : FinitelySupported A y) : Prop :=
  Disjoint hx.support hy.support

def AtomFreshP (hx : FinitelySupported A x) (a : A) : Prop := a ∉ hx.support

def FreshP (A : Type u) {X : Type v} {Y : Type w}
    [MulAction (Perm A) X] [MulAction (Perm A) Y]
    [Infinite A] [Nominal A X] [Nominal A Y] (x : X) (y : Y) : Prop :=
  Disjoint (support A x) (support A y)

theorem freshWith_iff_exists_disjoint_supports
    (hx : FinitelySupported A x) (hy : FinitelySupported A y) :
    FreshWithP hx hy ↔
      ∃ S T : Finset A, Supports S x ∧ Supports T y ∧ Disjoint S T := by
  constructor
  · intro h
    exact ⟨hx.support, hy.support, hx.supports_support, hy.supports_support, h⟩
  · rintro ⟨S, T, hS, hT, hST⟩
    exact hST.mono (hx.support_minimal hS) (hy.support_minimal hT)

theorem fresh_iff_exists_disjoint_supports
    [Nominal A X] [Nominal A Y] :
    FreshP A x y ↔
      ∃ S T : Finset A, Supports S x ∧ Supports T y ∧ Disjoint S T :=
  freshWith_iff_exists_disjoint_supports
    (Nominal.finitelySupported (A := A) x) (Nominal.finitelySupported (A := A) y)

theorem freshWith_map_right (hx : FinitelySupported A x) (hy : FinitelySupported A y)
    {f : Y → Z} (hf : Equivariant A f) (h : FreshWithP hx hy) :
    FreshWithP hx (hy.map hf) :=
  h.mono_right (hy.support_map_subset hf)

theorem freshWith_map_left (hx : FinitelySupported A x) (hy : FinitelySupported A y)
    {f : X → Z} (hf : Equivariant A f) (h : FreshWithP hx hy) :
    FreshWithP (hx.map hf) hy :=
  h.mono_left (hx.support_map_subset hf)

theorem freshWith_finset_left_iff [DecidableEq A]
    (S : Finset A) (hx : FinitelySupported A x) :
    FreshWithP (supports_finset A S).finitelySupported hx ↔
      ∀ a ∈ S, AtomFreshP hx a := by
  change Disjoint _ hx.support ↔ ∀ a ∈ S, a ∉ hx.support
  rw [← support_eq A S (supports_finset A S).finitelySupported, support_finset]
  exact Finset.disjoint_left

theorem freshWith_finset_right_iff [DecidableEq A]
    (S : Finset A) (hx : FinitelySupported A x) :
    FreshWithP hx (supports_finset A S).finitelySupported ↔
      ∀ a ∈ S, AtomFreshP hx a := by
  change Disjoint hx.support _ ↔ ∀ a ∈ S, a ∉ hx.support
  rw [← support_eq A S (supports_finset A S).finitelySupported, support_finset]
  exact Finset.disjoint_right

theorem fresh_atom_iff [Nominal A X] (a : A) (x : X) :
    FreshP A a x ↔ a ∉ support A x := by
  change Disjoint (support A a) (support A x) ↔ _
  rw [support_atom, Finset.disjoint_singleton_left]

theorem fresh_finset_left_iff [DecidableEq A] [Nominal A X]
    (S : Finset A) (x : X) :
    FreshP A S x ↔ ∀ a ∈ S, FreshP A a x := by
  simp only [fresh_atom_iff]
  change Disjoint (support A S) (support A x) ↔ _
  rw [support_finset]
  exact Finset.disjoint_left

theorem fresh_finset_right_iff [DecidableEq A] [Nominal A X]
    (S : Finset A) (x : X) :
    FreshP A x S ↔ ∀ a ∈ S, FreshP A a x := by
  simp only [fresh_atom_iff]
  change Disjoint (support A x) (support A S) ↔ _
  rw [support_finset]
  exact Finset.disjoint_right

#print axioms freshWith_iff_exists_disjoint_supports
#print axioms freshWith_map_right
#print axioms freshWith_finset_left_iff
#print axioms fresh_finset_left_iff
#check Disjoint.mono
#check Disjoint.mono_left
#check Disjoint.mono_right
#check Finset.disjoint_left
#check Finset.disjoint_right
#check Finset.disjoint_singleton_left
#check Finset.disjoint_union_left
#check Finset.disjoint_image

end CanonicalGeneralizationProbe

namespace CanonicalGeneralizationProbe

universe u v w

-- An equivariant constant can strictly increase freshness, so the forward law
-- cannot be upgraded to reflection without an additional support-reflection hypothesis.
theorem constant_loses_support (A : Type u) [Infinite A] (a : A) :
    Equivariant A (fun _ : A => (Discrete.mk () : Discrete A Unit)) ∧
      FreshP A a (Discrete.mk () : Discrete A Unit) ∧ ¬FreshP A a a := by
  refine ⟨fun _ _ => rfl, ?_, ?_⟩
  · change Disjoint (support A a) (support A (Discrete.mk () : Discrete A Unit))
    rw [support_discrete]
    exact disjoint_bot_right
  · rw [fresh_atom_iff, support_atom]
    simp

-- No DecidableEq A or nominality assumption is needed when S is merely an
-- explicit bound, rather than an element of the scoped Finset action.
theorem disjoint_bound_iff_atoms {A : Type u} {X : Type v}
    [MulAction (Perm A) X] [Infinite A] {x : X}
    (hx : FinitelySupported A x) (S : Finset A) :
    Disjoint S hx.support ↔ ∀ a ∈ S, AtomFreshP hx a :=
  Finset.disjoint_left

#print axioms constant_loses_support
#check freshWith_iff_exists_disjoint_supports
#check freshWith_map_right
#check freshWith_finset_left_iff
#check fresh_finset_left_iff
#check disjoint_bound_iff_atoms

end CanonicalGeneralizationProbe
