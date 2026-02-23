import NominalSets.Wheels
import NominalSets.Name
import NominalSets.FinitePerm

/-!
# Permutation Types

A **name permutation type** (also called a *nominal set without the finite-support condition*,
or a *Perm-set*) is a type `X` equipped with an action of the group `FinitePerm α` of finite permutations of a name type `α`.

## Main definitions

* `PermType α X` — typeclass asserting that `X` carries a `FinitePerm α`-action.
* `PFun α X Y` — newtype wrapper for `X → Y` carrying the conjugation action `(π • f) x = π • f (π⁻¹ • x)`, avoiding a diamond with Mathlib's `Pi.instSMul`.
* `PermType.movedFinset π` — the finite set of atoms moved by `π`, as a `Finset α`.

## Instances

* `PermType.instAtoms` — atoms `α` act on themselves by direct application (`π • a = π a`).
* `PermType.instProd` — component-wise action on `X × Y` (`π • (x, y) = (π • x, π • y)`).
* `PermType.instOption` — `Option X` carries the action fixing `none` and acting on `some x` by `π • some x = some (π • x)`.
* `PermType.instUnit` — `Unit` carries the trivial action (a `def`, not a global `instance`, because `α` cannot be inferred from `Unit` alone).
* `PermType.instFinset` — image action on `Finset α` (`π • s = s.image π`).
* `PermType.instConjFinitePerm` — action on `FinitePerm α` (`π • σ = π * σ * π⁻¹`).
* `PFun.instCoe` — coercion from `X → Y` to `PFun α X Y`.
* `PFun.instFunLike` — `PFun α X Y` elements can be applied directly as functions via `FunLike`.
* `PFun.instPermType` — action on `PFun α X Y` (`(π • f) x = π • f (π⁻¹ • x)`).

## Main results

* `PermType.inv_smul_smul` / `PermType.smul_inv_smul` — applying a permutation and its inverse (in either order) recovers the original element.
* `PermType.smul_injective` — the action of any permutation is injective.
* `PermType.smul_eq_iff_eq_inv_smul` — `π • x = y ↔ x = π⁻¹ • y`.
* `PermType.mem_smul_finset_iff` — `a ∈ π • s ↔ π⁻¹ • a ∈ s`.
* `PermType.mem_movedFinset` — `a ∈ movedFinset π ↔ π a ≠ a`.
* `PermType.movedFinset_eq_empty_iff_one` — a permutation with no moved atoms is the identity.
* `PermType.movedFinset_inv` — `π` and `π⁻¹` move the same atoms.
* `PermType.movedFinset_mul_subset` — moved atoms of `π * σ` are contained in the union of those of `π` and `σ`.
* `PermType.movedFinset_conj_smul` — `movedFinset (π • σ) = π • movedFinset σ` (equivariance of the moved-point set under conjugation).

## Notation

We inherit `•` from `MulAction`. Given `π : FinitePerm α` and `x : X`, write `π • x`

## References

* [A. M. Pitts, *Nominal Sets*][Pitts2013], Chapter 1.
-/

/-- A **permutation type** is a type `X` equipped with an action of the group `FinitePerm α` of finite permutations -/
class PermType (α : outParam Type*) [Name α] (X : Type*) extends MulAction (FinitePerm α) X

variable {α : Type*} [ist : Name α]

namespace PermType

variable {X Y : Type*} [PermType α X] [PermType α Y]

/-! ### Canonical action on atoms -/

/-- The atoms `α` form a permutation type: a finite permutation acts on `α` by direct application, i.e., `π • a = π a`. -/
instance instAtoms : PermType α α where
  smul π a := π a
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

@[simp, grind =]
theorem atoms_smul (π : FinitePerm α) (a : α) : (π • a : α) = π a := rfl

/-! ### Product -/

/-- The Cartesian product of two permutation types is a permutation type, with the component-wise action `π • (x, y) = (π • x, π • y)`. -/
instance instProd : PermType α (X × Y) where
  smul π p := (π • p.1, π • p.2)
  one_smul p := by simp
  mul_smul π σ p := by simp [mul_smul]

@[simp, grind =]
theorem prod_smul (X Y : Type*) [PermType α X] [PermType α Y]
    (π : FinitePerm α) (x : X) (y : Y) : π • (x, y) = (π • x, π • y) := rfl

/-! ### Unit -/

/-- `Unit` carries the trivial permutation action.

This is a `def` rather than a global `instance` because `α` cannot be inferred from `Unit` alone — Lean's `outParam` mechanism requires `α` to be determined
from the target type, but `Unit` does not mention `α`. Use `letI := instUnit` at call sites where `α` is already known. -/
def instUnit : PermType α Unit where
  smul _ _ := ()
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

theorem unit_smul (π : FinitePerm α) (u : Unit) : letI : PermType α Unit := instUnit; π • u = () := rfl

/-! ### Option -/

/-- `Option X` carries the permutation action that fixes `none` and acts on `some x` by `π • some x = some (π • x)`. -/
instance instOption : PermType α (Option X) where
  smul π o := o.map (π • ·)
  one_smul o := by
    cases o with
    | none => rfl
    | some x => change some ((1 : FinitePerm α) • x) = some x; rw [one_smul]
  mul_smul π σ o := by
    cases o with
    | none => rfl
    | some x => change some ((π * σ) • x) = some (π • σ • x); rw [mul_smul]

@[simp, grind =]
theorem option_smul_none (π : FinitePerm α) : π • (none : Option X) = none := rfl

@[simp, grind =]
theorem option_smul_some {X : Type*} [PermType α X] (π : FinitePerm α) (x : X) : π • (some x : Option X) = some (π • x) := rfl

/-! ### Function space

#### The diamond problem

The permutation action on `X → Y` is:

  `(π • f) x = π • f (π⁻¹ • x)`

However, Mathlib already provides `Pi.instSMul`, which gives a *pointwise* action on any `ι → α` whenever `SMul M α`:

  `(π • f) x = π • f x`   -- Pi.instSMul

Because `PermType α (X → Y)` extends `MulAction (FinitePerm α) (X → Y)`, which in turn
gives a `SMul (FinitePerm α) (X → Y)`, both instances become available for `X → Y`.
Lean's instance search then faces a **diamond**: it may synthesise `Pi.instSMul` before
`instFun`, yielding the wrong action.

To avoid this conflict entirely, the action is wrapped in the newtype `PFun α X Y` rather than being placed on the bare function type.
The old instance `instFun` is kept below for reference and for use in proofs that explicitly request it.
-/

/-- `PFun α X Y` is a **newtype wrapper** around `X → Y` carrying the action `(π • f) x = π • f (π⁻¹ • x)` -/
structure PFun (α : Type*) [Name α] (X Y : Type*) where
  toFun : X → Y

namespace PFun

/-- Coerce a plain function into a `PFun`. -/
instance instCoe {X Y : Type*} : Coe (X → Y) (PFun α X Y) := ⟨PFun.mk⟩

/-- Apply a `PFun` to an argument. -/
instance instFunLike {X Y : Type*} : FunLike (PFun α X Y) X Y where
  coe f := f.toFun
  coe_injective' f g h := by cases f; cases g; congr

@[ext]
theorem ext {X Y : Type*} {f g : PFun α X Y} (h : ∀ x, f x = g x) : f = g := DFunLike.ext f g h

@[simp] theorem coe_mk {X Y : Type*} (f : X → Y) (x : X) : (PFun.mk f : PFun α X Y) x = f x := rfl

@[simp] theorem coe_apply {X Y : Type*} (f : X → Y) (x : X) : (f : PFun α X Y) x = f x := rfl

/-- The action on `PFun α X Y`: `(π • f) x = π • f (π⁻¹ • x)`. -/
instance instPermType {X Y : Type*} [PermType α X] [PermType α Y] :
    PermType α (PFun α X Y) where
  smul π f := ⟨fun x => π • f (π⁻¹ • x)⟩
  one_smul f := by
    ext x
    change (1 : FinitePerm α) • f (1⁻¹ • x) = f x
    simp [one_smul]
  mul_smul π σ f := by
    ext x
    change (π * σ) • f ((π * σ)⁻¹ • x) = π • (σ • f (σ⁻¹ • (π⁻¹ • x)))
    rw [mul_inv_rev, mul_smul, mul_smul]

@[simp, grind =]
theorem smul_apply {X Y : Type*} [PermType α X] [PermType α Y] (π : FinitePerm α) (f : PFun α X Y) (x : X) :
  (π • f) x = π • f (π⁻¹ • x) := rfl

end PFun

/-! #### PROBLEM: action directly on `X → Y`

The instance below equips the bare function type with an action.
It is **not** registered as a global `PermType` instance to avoid the diamond
with `Pi.instSMul`; use `PFun` instead. It is kept here for documentation -/

/- action on `X → Y` (not a global instance; see `PFun`). -/
-- def funPermType {X Y : Type*} [PermType α X] [PermType α Y] :
--     PermType α (X → Y) where
--   smul π f x := π • f (π⁻¹ • x)
--   one_smul f := by
--     funext x
--     change (1 : FinitePerm α) • f (1⁻¹ • x) = f x
--     simp [one_smul]
--   mul_smul π σ f := by
--     funext x
--     change (π * σ) • f ((π * σ)⁻¹ • x) = π • σ • f (σ⁻¹ • π⁻¹ • x)
--     rw [mul_inv_rev, mul_smul, mul_smul]

-- Note: Mathlib's `Pi.instSMul` (pointwise action) conflicts with the conjugation
-- action defined in `instFun`. We state `fun_smul` using `@SMul.smul _ _ instFun.toSMul`
-- to pin the right instance, avoiding the ambiguity.
-- @[simp]
-- theorem fun_smul {X Y : Type*} [PermType α X] [PermType α Y]
--     (π : FinitePerm α) (f : X → Y) (x : X) :
--     @SMul.smul _ _ instFun.toSMul π f x = π • f (π⁻¹ • x) := rfl

/-! ### Finite sets of atoms -/

/-- Finite sets of atoms form a permutation type: `π • s = s.image π`. (i.e., `π • s = {π a | a ∈ s}`). -/
instance instFinset : PermType α (Finset α) where
  smul π s := s.image (π : α → α)
  one_smul s := by change s.image ((1 : FinitePerm α) : α → α) = s; simp
  mul_smul π σ s := by
    change s.image ((π * σ : FinitePerm α) : α → α) =
         (s.image (σ : α → α)).image (π : α → α)
    simp [coe_mul, Finset.image_image]

@[simp]
theorem finset_smul (π : FinitePerm α) (s : Finset α) : π • s = s.image (π : α → α) := rfl

/-- Membership in `π • s`: `a ∈ π • s ↔ ∃ b ∈ s, π • b = a`. -/
@[simp]
theorem mem_finset_smul {π : FinitePerm α} {s : Finset α} {a : α} : a ∈ π • s ↔ ∃ b ∈ s, π • b = a := by
  simp [finset_smul, Finset.mem_image, PermType.atoms_smul]

@[simp]
theorem mem_smul_finset_iff {π : FinitePerm α} {s : Finset α} {a : α} : a ∈ π • s ↔ π⁻¹ • a ∈ s := by
  simp only [finset_smul, Finset.mem_image, PermType.atoms_smul]
  constructor
  · rintro ⟨b, hb, rfl⟩
    simpa [PermType.atoms_smul] using hb
  · intro h
    exact ⟨π⁻¹ • a, h, by simp [PermType.atoms_smul]⟩

/-! ### Action on finite permutations -/

/-- `FinitePerm α` is a permutation type via: `π • σ = π * σ * π⁻¹`. -/
instance instConjFinitePerm : PermType α (FinitePerm α) where
  smul π σ := π * σ * π⁻¹
  one_smul σ := by change 1 * σ * 1⁻¹ = σ; simp
  mul_smul π τ σ := by
    change π * τ * σ * (π * τ)⁻¹ = π * (τ * σ * τ⁻¹) * π⁻¹
    simp [mul_inv_rev, mul_assoc]

@[simp, grind =]
theorem conj_smul (π σ : FinitePerm α) : π • σ = π * σ * π⁻¹ := rfl

/-! ### Basic lemmas -/

section

variable {X : Type*} [PermType α X]

/-- The action of the identity permutation is trivial. -/
@[simp, grind =]
theorem one_smul' (x : X) : (1 : FinitePerm α) • x = x := one_smul _ x

/-- The action is compatible with multiplication in `FinitePerm α`. -/
@[grind =, grind =_]
theorem mul_smul' (π σ : FinitePerm α) (x : X) : (π * σ) • x = π • σ • x := mul_smul π σ x

/-- Applying a permutation and then its inverse recovers the original element. -/
@[simp, grind =]
theorem inv_smul_smul (π : FinitePerm α) (x : X) : π⁻¹ • π • x = x := by
  rw [← mul_smul, inv_mul_cancel, one_smul]

/-- Applying a permutation after its inverse recovers the original element. -/
@[simp, grind =]
theorem smul_inv_smul (π : FinitePerm α) (x : X) : π • π⁻¹ • x = x := by
  rw [← mul_smul, mul_inv_cancel, one_smul]

/-- The permutation action is injective -/
@[grind .]
theorem smul_injective (π : FinitePerm α) {x y : X} (h : π • x = π • y) : x = y := by
  have := congr_arg (π⁻¹ • ·) h
  simp only [inv_smul_smul] at this
  exact this

/-- Two elements are related by the action iff they are in the same orbit. -/
@[grind .]
theorem smul_eq_iff_eq_inv_smul (π : FinitePerm α) (x y : X) : π • x = y ↔ x = π⁻¹ • y := by
  constructor
  · rintro rfl; simp
  · rintro rfl; simp

end

/-! ### Moved-point set -/

/-- The finite set of atoms moved by a finite permutation. -/
@[reducible]
noncomputable def movedFinset (π : FinitePerm α) : Finset α := π.property.toFinset

omit [Name α] in
@[simp]
theorem mem_movedFinset {π : FinitePerm α} {a : α} : a ∈ movedFinset π ↔ π a ≠ a := by
  simp only [movedFinset, Set.Finite.mem_toFinset, Equiv.Perm.movedPoints,
             Set.mem_setOf_eq, DFunLike.coe]

/-- A finite permutation with no moved points is the identity. -/
theorem movedFinset_eq_empty_iff_one {σ : FinitePerm α} : movedFinset σ = ∅ ↔ σ = 1 := by
  constructor
  · intro h
    apply Subtype.ext
    apply Equiv.Perm.ext
    intro c
    by_contra hne
    have : c ∈ movedFinset σ := mem_movedFinset.mpr hne
    simp [h] at this
  · rintro rfl
    ext a
    simp [movedFinset, Equiv.Perm.movedPoints]

/-- The identity permutation moves no atoms. -/
@[simp]
theorem movedFinset_one : movedFinset (1 : FinitePerm α) = ∅ := movedFinset_eq_empty_iff_one.mpr rfl

omit [Name α] in
/-- A permutation and its inverse move the same atoms. -/
@[simp]
theorem movedFinset_inv (π : FinitePerm α) : movedFinset π⁻¹ = movedFinset π := by
  ext a
  simp only [mem_movedFinset]
  constructor
  · intro h hπ
    exact h (by have := inv_apply_self π a; rw [hπ] at this; exact this)
  · intro h hπ
    exact h (by have := apply_inv_self π a; rw [hπ] at this; exact this)

/-- The moved-point set of a product is contained in the union of the factors' moved-point sets. -/
theorem movedFinset_mul_subset (π σ : FinitePerm α) : movedFinset (π * σ) ⊆ movedFinset π ∪ movedFinset σ := by
  intro a ha
  simp only [mem_movedFinset, mul_apply, Finset.mem_union] at ha ⊢
  by_contra h
  push_neg at h
  obtain ⟨h₁, h₂⟩ := h
  exact ha (by rw [h₂, h₁])

theorem movedFinset_conj_smul (π σ : FinitePerm α) : movedFinset (π • σ) = π • movedFinset σ := by
  ext a
  simp only [conj_smul, mem_movedFinset, mul_apply, finset_smul, Finset.mem_image]
  constructor
  · intro ha
    exact ⟨π⁻¹ a, fun heq ↦ ha (by rw [heq, apply_inv_self]), apply_inv_self π a⟩
  · rintro ⟨b, hb, rfl⟩
    intro heq
    apply hb
    have := congr_arg (π⁻¹ ·) heq
    simp only [inv_apply_self] at this
    exact this

end PermType
