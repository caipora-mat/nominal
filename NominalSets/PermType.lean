import NominalSets.FinitePerm.Basic
import NominalSets.Name

/-!
# Permutation Types

A **permutation type** (also called a *nominal set without the finite-support condition*,
or a *Perm-set*) is a type `X` equipped with an action of the group `FinitePerm α` of
finite permutations of a name type `α`.

Formally this is just a `MulAction (FinitePerm α) X`, but we introduce the typeclass
`PermType` to:

1. Give a convenient single bundled constraint for the nominal-sets library.
2. Provide a uniform `•` notation via the existing `MulAction` infrastructure.
3. Collect basic instances (atoms, products, sums, functions) in one place.

## Main definitions

* `PermType α X` — typeclass asserting that `X` carries a `FinitePerm α`-action.
* Basic instances: atoms `α`, `Prop`, products, sums, function spaces.

## Notation

We inherit `•` from `MulAction`. Given `π : FinitePerm α` and `x : X`, write `π • x`.

## References

* [A. M. Pitts, *Nominal Sets*][Pitts2013], Chapter 2.
-/

open Equiv

variable {α : Type*} [Name α]

/-- A **permutation type** is a type `X` equipped with an action of the group
`FinitePerm α` of finite permutations. This is a thin wrapper around
`MulAction (FinitePerm α) X` that gives a convenient single typeclass -/
class PermType (α : Type*) [Name α] (X : Type*) extends MulAction (FinitePerm α) X

namespace PermType

/-! ### Canonical action on atoms -/

/-- The atoms `α` form a permutation type: a finite permutation acts on `α` by
direct application, i.e., `π • a = π.val a`. -/
instance instAtoms : PermType α α where
  smul π a := π.val a
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

@[simp, grind =]
theorem atoms_smul (π : FinitePerm α) (a : α) :
    (π • a : α) = π.val a :=
  rfl

/-! ### Product -/

/-- The Cartesian product of two permutation types is a permutation type,
with the component-wise action `π • (x, y) = (π • x, π • y)`. -/
instance instProd {X Y : Type*} [PermType α X] [PermType α Y] :
    PermType α (X × Y) where
  smul π p := (π • p.1, π • p.2)
  one_smul p := by simp
  mul_smul π σ p := by simp [mul_smul]

@[simp, grind =]
theorem prod_smul (X Y : Type*) [PermType α X] [PermType α Y]
    (π : FinitePerm α) (x : X) (y : Y) :
    π • (x, y) = (π • x, π • y) :=
  rfl

/-! ### Function space

#### The diamond problem

The permutation action on `X → Y` is:

  `(π • f) x = π • f (π⁻¹ • x)`

However, Mathlib already provides `Pi.instSMul`, which gives a *pointwise* action on
any `ι → α` whenever `SMul M α`:

  `(π • f) x = π • f x`   -- Pi.instSMul

Because `PermType α (X → Y)` extends `MulAction (FinitePerm α) (X → Y)`, which in turn
gives a `SMul (FinitePerm α) (X → Y)`, both instances become available for `X → Y`.
Lean's instance search then faces a **diamond**: it may synthesise `Pi.instSMul` before
`instFun`, yielding the wrong action.

To avoid this conflict entirely, the action is wrapped in the newtype `PFun α X Y`
(a transparent copy of `X → Y`) rather than being placed on the bare function type.
The old instance `instFun` is kept below for reference and for use in proofs that
explicitly request it.
-/

/-- `PFun α X Y` is a **newtype wrapper** around `X → Y` carrying the action
`(π • f) x = π • f (π⁻¹ • x)`.

The wrapper is needed because Mathlib's `Pi.instSMul` already equips the type
`X → Y` with a *pointwise* action `(π • f) x = π • f x`, causing a diamond when
we try to register the conjugation action directly on `X → Y`. -/
def PFun (α : Type*) [Name α] (X Y : Type*) := X → Y

namespace PFun

/-- Coerce a plain function into a `PFun`. -/
def mk {X Y : Type*} (f : X → Y) : PFun α X Y := f

/-- Apply a `PFun` to an argument. -/
instance instFunLike {X Y : Type*} : FunLike (PFun α X Y) X Y where
  coe f := f
  coe_injective' _ _ h := h

@[simp] theorem mk_apply {X Y : Type*} (f : X → Y) (x : X) : PFun.mk (α := α) f x = f x := rfl

/-- The conjugation action on `PFun α X Y`:
`(π • f) x = π • f (π⁻¹ • x)`. -/
instance instPermType {X Y : Type*} [PermType α X] [PermType α Y] :
    PermType α (PFun α X Y) where
  smul π f x := π • f (π⁻¹ • x)
  one_smul f := by
    funext x
    change (1 : FinitePerm α) • f (1⁻¹ • x) = f x
    simp [one_smul]
  mul_smul π σ f := by
    funext x
    change (π * σ) • f ((π * σ)⁻¹ • x) = π • σ • f (σ⁻¹ • π⁻¹ • x)
    rw [mul_inv_rev, mul_smul, mul_smul]

@[simp]
theorem smul_apply {X Y : Type*} [PermType α X] [PermType α Y]
    (π : FinitePerm α) (f : PFun α X Y) (x : X) :
    (π • f) x = π • f (π⁻¹ • x) := rfl

end PFun

/-! #### Legacy: conjugation action directly on `X → Y`

The instance below equips the bare function type with the conjugation action.
It is **not** registered as a global `PermType` instance to avoid the diamond
with `Pi.instSMul`; use `PFun` instead. It is kept here for use in proofs
that need to call it explicitly. -/

/-- Conjugation action on `X → Y` (not a global instance; see `PFun`). -/
def funPermType {X Y : Type*} [PermType α X] [PermType α Y] :
    PermType α (X → Y) where
  smul π f x := π • f (π⁻¹ • x)
  one_smul f := by
    funext x
    change (1 : FinitePerm α) • f (1⁻¹ • x) = f x
    simp [one_smul]
  mul_smul π σ f := by
    funext x
    change (π * σ) • f ((π * σ)⁻¹ • x) = π • σ • f (σ⁻¹ • π⁻¹ • x)
    rw [mul_inv_rev, mul_smul, mul_smul]

-- Note: Mathlib's `Pi.instSMul` (pointwise action) conflicts with the conjugation
-- action defined in `instFun`. We state `fun_smul` using `@SMul.smul _ _ instFun.toSMul`
-- to pin the right instance, avoiding the ambiguity.
-- @[simp]
-- theorem fun_smul {X Y : Type*} [PermType α X] [PermType α Y]
--     (π : FinitePerm α) (f : X → Y) (x : X) :
--     @SMul.smul _ _ instFun.toSMul π f x = π • f (π⁻¹ • x) := rfl

/-! ### Basic equivariance lemmas -/

section

variable {X : Type*} [PermType α X]

/-- The action of the identity permutation is trivial. -/
theorem one_smul' (x : X) : (1 : FinitePerm α) • x = x :=
  one_smul _ x

/-- The action is compatible with multiplication in `FinitePerm α`. -/
theorem mul_smul' (π σ : FinitePerm α) (x : X) : (π * σ) • x = π • σ • x :=
  mul_smul π σ x

/-- Applying a permutation and then its inverse recovers the original element. -/
theorem inv_smul_smul (π : FinitePerm α) (x : X) : π⁻¹ • π • x = x := by
  rw [← mul_smul, inv_mul_cancel, one_smul]

/-- Applying a permutation after its inverse recovers the original element. -/
theorem smul_inv_smul (π : FinitePerm α) (x : X) : π • π⁻¹ • x = x := by
  rw [← mul_smul, mul_inv_cancel, one_smul]

/-- The permutation action is injective: if `π • x = π • y` then `x = y`. -/
theorem smul_left_cancel (π : FinitePerm α) {x y : X} (h : π • x = π • y) : x = y := by
  have := congr_arg (π⁻¹ • ·) h
  simp only [inv_smul_smul] at this
  exact this

/-- Two elements are related by the action iff they are in the same orbit. -/
theorem smul_eq_iff_eq_inv_smul (π : FinitePerm α) (x y : X) :
    π • x = y ↔ x = π⁻¹ • y := by
  constructor
  · rintro rfl; simp
  · rintro rfl; simp

end

end PermType
