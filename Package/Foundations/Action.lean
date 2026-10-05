/-
Copyright (c) 2026 Nominal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nominal contributors
-/
import Package.Foundations.Permutation
import Mathlib.Algebra.Group.Action.End
import Mathlib.Algebra.Group.Subgroup.Actions
import Mathlib.Algebra.Group.Action.Prod
import Mathlib.Algebra.Group.Action.Pointwise.Finset

/-!
# Selected actions and equivariant functions

The atom action is Mathlib's permutation action restricted to `permSubgroup A`.
Products use the standard componentwise action. Finite-set consumers explicitly
open the `Pointwise` scope. No action on an arbitrary external carrier is inferred.

`Discrete A X` makes the trivial action a distinct carrier. Bare permutation
groups retain left multiplication, and bare functions retain pointwise action.
`Equivariant A f` is an unbundled property and names its atom type explicitly.
-/

namespace NominalPackage

universe u v w z

namespace Perm

variable {A : Type u}

/-- The inherited canonical action on atoms computes by application. -/
@[simp] theorem smul_atom (π : Perm A) (a : A) : π • a = π a := rfl

section Finsets

open scoped Pointwise

variable [DecidableEq A]

/-- Finite atom sets use Mathlib's scoped image action. -/
theorem smul_finset (π : Perm A) (S : Finset A) : π • S = S.image π := rfl

/-- Membership in a renamed finite set is membership of the inverse image. -/
theorem mem_smul_finset (π : Perm A) (S : Finset A) (a : A) :
    a ∈ π • S ↔ π⁻¹ a ∈ S := Finset.inv_smul_mem_iff.symm

end Finsets
end Perm

/-- A distinct copy of `X` carrying the trivial atom-permutation action. -/
structure Discrete (A : Type u) (X : Type v) : Type v where
  /-- The underlying data, with no implicit claim about any action on `X`. -/
  val : X

namespace Discrete

variable {A : Type u} {X : Type v}

instance : MulAction (Perm A) (Discrete A X) where
  smul _ d := d
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

@[simp] theorem smul_mk (π : Perm A) (x : X) :
    π • (mk x : Discrete A X) = mk x := rfl

@[simp] theorem smul_val (π : Perm A) (d : Discrete A X) : (π • d).val = d.val := rfl

/-- The ordinary type equivalence; it does not identify independently chosen actions. -/
def equiv (A : Type u) (X : Type v) : Discrete A X ≃ X where
  toFun := val
  invFun := mk
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem equiv_apply (d : Discrete A X) : equiv A X d = d.val := rfl
@[simp] theorem equiv_symm_apply (x : X) : (equiv A X).symm x = mk x := rfl

end Discrete

/-- An ordinary map commutes with the selected atom-permutation actions. -/
def Equivariant (A : Type u) {X : Type v} {Y : Type w}
    [MulAction (Perm A) X] [MulAction (Perm A) Y] (f : X → Y) : Prop :=
  ∀ (π : Perm A) x, f (π • x) = π • f x

namespace Equivariant

variable {A : Type u} {X : Type v} {Y : Type w} {Z : Type z}
variable [MulAction (Perm A) X] [MulAction (Perm A) Y] [MulAction (Perm A) Z]

theorem id (A : Type u) {X : Type v} [MulAction (Perm A) X] :
    Equivariant A (_root_.id : X → X) := fun _ _ => rfl

theorem comp {g : Y → Z} {f : X → Y} (hg : Equivariant A g) (hf : Equivariant A f) :
    Equivariant A (g ∘ f) := by
  intro π x
  change g (f (π • x)) = π • g (f x)
  rw [hf, hg]

theorem fst (A : Type u) {X : Type v} {Y : Type w}
    [MulAction (Perm A) X] [MulAction (Perm A) Y] :
    Equivariant A (Prod.fst : X × Y → X) := fun _ _ => rfl

theorem snd (A : Type u) {X : Type v} {Y : Type w}
    [MulAction (Perm A) X] [MulAction (Perm A) Y] :
    Equivariant A (Prod.snd : X × Y → Y) := fun _ _ => rfl

theorem pair {f : X → Y} {g : X → Z} (hf : Equivariant A f) (hg : Equivariant A g) :
    Equivariant A (fun x => (f x, g x)) := by
  intro π x
  exact Prod.ext (hf π x) (hg π x)

end Equivariant
end NominalPackage
