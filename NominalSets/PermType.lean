import NominalSets.Wheels
import NominalSets.Name
import NominalSets.FinitePerm

/-!
# Permutation Types

A **name permutation type** (also called a *nominal set without the finite-support condition*,
or a *Perm-set*) is a type `X` equipped with an action of the group `FinitePerm α` of finite
permutations of a name type `α`.

## Main definitions

* `PermType α X` — typeclass asserting that `X` carries a `FinitePerm α`-action.
* `PermType.movedFinset π` — the finite set of atoms moved by `π`, as a `Finset α`.

The function-space action and its newtype wrapper `PFun α X Y` live in `NominalSets.PFun`.

## Instances

* `PermType.instAtoms` — atoms `α` act on themselves by direct application (`π • a = π a`).
* `PermType.instProd` — component-wise action on `X × Y` (`π • (x, y) = (π • x, π • y)`).
* `PermType.instOption` — `Option X` carries the action fixing `none` and acting on `some x`
  by `π • some x = some (π • x)`.
* `PermType.instUnit` — `Unit` carries the trivial action (a `def`, not a global `instance`,
  because `α` cannot be inferred from `Unit` alone; use `letI := instUnit` at call sites).
* `PermType.instFinset` — image action on `Finset α` (`π • s = s.image π`).
* `PermType.instConjFinitePerm` — conjugation action on `FinitePerm α` (`π • σ = π * σ * π⁻¹`).
* `PermType.instPermTypeSum` — component-wise action on `X ⊕ Y`
  (`π • inl x = inl (π • x)`, `π • inr y = inr (π • y)`).

## Main results

### Basic action lemmas
* `PermType.inv_smul_smul` / `PermType.smul_inv_smul` — applying a permutation and its inverse
  (in either order) recovers the original element.
* `PermType.smul_injective` — the action of any permutation is injective.
* `PermType.smul_surjective` / `PermType.smul_bijective` — the action is surjective and bijective.
* `PermType.smul_eq_iff_eq_inv_smul` — `π • x = y ↔ x = π⁻¹ • y`.
* `PermType.inv_smul_eq_iff` — `π⁻¹ • x = y ↔ x = π • y`.
* `PermType.smul_ne_iff` — `π • x ≠ π • y ↔ x ≠ y`.

### Finset action
* `PermType.mem_finset_smul` — `a ∈ π • s ↔ ∃ b ∈ s, π • b = a`.
* `PermType.mem_smul_finset_iff` — `a ∈ π • s ↔ π⁻¹ • a ∈ s`.
* `PermType.finset_smul_empty` — `π • ∅ = ∅`.
* `PermType.finset_smul_singleton` — `π • {a} = {π a}`.
* `PermType.finset_smul_union` — `π • (s ∪ t) = π • s ∪ π • t`.

### Sum action
* `PermType.sum_smul_inl` / `PermType.sum_smul_inr` — action on sum injections.

### Moved-point set
* `PermType.mem_movedFinset` — `a ∈ movedFinset π ↔ π a ≠ a`.
* `PermType.fixed_of_not_mem_movedFinset` — atoms outside `movedFinset π` are fixed points.
* `PermType.movedFinset_eq_empty_iff_one` — a permutation with no moved atoms is the identity.
* `PermType.movedFinset_inv` — `π` and `π⁻¹` move the same atoms.
* `PermType.movedFinset_mul_subset` — moved atoms of `π * σ` are contained in the union of
  those of `π` and `σ`.
* `PermType.movedFinset_conj_smul` — `movedFinset (π • σ) = π • movedFinset σ`
  (equivariance of the moved-point set under conjugation).

## References

* [A. M. Pitts, *Nominal Sets*][Pitts2013], Chapter 1.
-/

namespace NominalSets

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

/-- The action of `π` on atoms is function application: `π • a = π a`. -/
@[simp, grind =]
theorem atoms_smul (π : FinitePerm α) (a : α) : (π • a : α) = π a := rfl

/-! ### Product -/

/-- The Cartesian product of two permutation types is a permutation type, with the component-wise action `π • (x, y) = (π • x, π • y)`. -/
instance instProd : PermType α (X × Y) where
  smul π p := (π • p.1, π • p.2)
  one_smul p := by simp
  mul_smul π σ p := by simp [mul_smul]

/-- The action on a product applies component-wise: `π • (x, y) = (π • x, π • y)`. -/
@[simp, grind =]
theorem prod_smul (π : FinitePerm α) (x : X) (y : Y) : π • (x, y) = (π • x, π • y) := rfl

/-! ### Unit -/

/-- `Unit` carries the trivial permutation action.

This is a `def` rather than a global `instance` because `α` cannot be inferred from `Unit` alone — Lean's `outParam` mechanism requires `α` to be determined
from the target type, but `Unit` does not mention `α`. Use `letI := instUnit` at call sites where `α` is already known. -/
def instUnit : PermType α Unit where
  smul _ _ := ()
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

/-- Every permutation acts trivially on `Unit`. -/
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

/-- Every permutation fixes `none`. -/
@[simp, grind =]
theorem option_smul_none (π : FinitePerm α) : π • (none : Option X) = none := rfl

/-- The action on `some x` is `π • some x = some (π • x)`. -/
@[simp, grind =]
theorem option_smul_some (π : FinitePerm α) (x : X) : π • (some x : Option X) = some (π • x) := rfl

/-! ### Function space

The permutation action on functions is defined in `NominalSets.PFun` via the newtype `PFun α X Y`
to avoid a diamond with Mathlib's `Pi.instSMul`. See that module for details. -/

/-! ### Finite sets of atoms -/

/-- Finite sets of atoms form a permutation type: `π • s = s.image π`. (i.e., `π • s = {π a | a ∈ s}`). -/
instance instFinset : PermType α (Finset α) where
  smul π s := s.image (π : α → α)
  one_smul s := by change s.image ((1 : FinitePerm α) : α → α) = s; simp
  mul_smul π σ s := by
    change s.image ((π * σ : FinitePerm α) : α → α) =
         (s.image (σ : α → α)).image (π : α → α)
    simp [coe_mul, Finset.image_image]

/-- The action on a finite set of atoms is the image: `π • s = s.image π`. -/
@[simp, grind =]
theorem finset_smul (π : FinitePerm α) (s : Finset α) : π • s = s.image (π : α → α) := rfl

/-- Membership in `π • s`: `a ∈ π • s ↔ ∃ b ∈ s, π • b = a`. -/
@[simp, grind =]
theorem mem_finset_smul {π : FinitePerm α} {s : Finset α} {a : α} : a ∈ π • s ↔ ∃ b ∈ s, π • b = a := by
  simp [finset_smul, Finset.mem_image, PermType.atoms_smul]

/-- Membership in `π • s` after pulling back: `a ∈ π • s ↔ π⁻¹ • a ∈ s`. -/
@[simp, grind =]
theorem mem_smul_finset_iff {π : FinitePerm α} {s : Finset α} {a : α} : a ∈ π • s ↔ π⁻¹ • a ∈ s := by
  simp only [finset_smul, Finset.mem_image, PermType.atoms_smul]
  constructor
  · rintro ⟨b, hb, rfl⟩
    simpa [PermType.atoms_smul] using hb
  · intro h
    exact ⟨π⁻¹ • a, h, by simp [PermType.atoms_smul]⟩

/-- The action on the empty finset is the empty finset. -/
@[simp]
theorem finset_smul_empty (π : FinitePerm α) : π • (∅ : Finset α) = ∅ := by
  simp [finset_smul]

/-- The action on a singleton `{a}` gives `{π a}`. -/
@[simp]
theorem finset_smul_singleton (π : FinitePerm α) (a : α) : π • ({a} : Finset α) = {π a} := by
  simp [finset_smul]

/-- The action distributes over union: `π • (s ∪ t) = π • s ∪ π • t`. -/
@[simp]
theorem finset_smul_union (π : FinitePerm α) (s t : Finset α) : π • (s ∪ t) = π • s ∪ π • t := by
  simp [finset_smul, Finset.image_union]

/-! ### Action on finite permutations -/

/-- `FinitePerm α` is a permutation type via: `π • σ = π * σ * π⁻¹`. -/
instance instConjFinitePerm : PermType α (FinitePerm α) where
  smul π σ := π * σ * π⁻¹
  one_smul σ := by change 1 * σ * 1⁻¹ = σ; simp
  mul_smul π τ σ := by
    change π * τ * σ * (π * τ)⁻¹ = π * (τ * σ * τ⁻¹) * π⁻¹
    simp [mul_inv_rev, mul_assoc]

/-- The conjugation action: `π • σ = π * σ * π⁻¹`. -/
@[simp, grind =]
theorem conj_smul (π σ : FinitePerm α) : π • σ = π * σ * π⁻¹ := rfl

/-! ### Sum nominal instance (prerequisite for structural properties) -/

/-- The sum of two permutation types is a permutation type, acting on each summand separately. -/
instance instPermTypeSum {X Y : Type*} [PermType α X] [PermType α Y] : PermType α (X ⊕ Y) where
  smul π s := s.map (π • ·) (π • ·)
  one_smul s := by
    cases s <;> simp only [HSMul.hSMul, SMul.smul, Sum.map, Sum.elim_inl, Sum.elim_inr,
      Function.comp] <;> congr 1 <;> exact one_smul _ _
  mul_smul π σ s := by
    cases s <;> simp only [HSMul.hSMul, SMul.smul, Sum.map, Sum.elim_inl, Sum.elim_inr,
      Function.comp] <;> congr 1 <;> exact mul_smul _ _ _

/-- The action on the left injection: `π • inl x = inl (π • x)`. -/
@[simp, grind =]
theorem sum_smul_inl {X Y : Type*} [PermType α X] [PermType α Y]
    (π : FinitePerm α) (x : X) :
    π • (Sum.inl x : X ⊕ Y) = Sum.inl (π • x) := rfl

/-- The action on the right injection: `π • inr y = inr (π • y)`. -/
@[simp, grind =]
theorem sum_smul_inr {X Y : Type*} [PermType α X] [PermType α Y]
    (π : FinitePerm α) (y : Y) :
    π • (Sum.inr y : X ⊕ Y) = Sum.inr (π • y) := rfl

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
theorem smul_eq_iff_eq_inv_smul {π : FinitePerm α} {x y : X} : π • x = y ↔ x = π⁻¹ • y := by
  constructor
  · rintro rfl; simp
  · rintro rfl; simp

@[grind .]
theorem inv_smul_eq_iff (π : FinitePerm α) (x y : X) : π⁻¹ • x = y ↔ x = π • y := by
  constructor
  · rintro rfl; simp
  · rintro rfl; simp

/-- The permutation action on `X` is surjective. -/
theorem smul_surjective (π : FinitePerm α) : Function.Surjective ((π • ·) : X → X) :=
  fun y => ⟨π⁻¹ • y, smul_inv_smul π y⟩

/-- The permutation action on `X` is bijective. -/
theorem smul_bijective (π : FinitePerm α) : Function.Bijective ((π • ·) : X → X) :=
  ⟨fun {_ _} h => smul_injective π h, smul_surjective π⟩

/-- The permutation action preserves inequality: `π • x ≠ π • y ↔ x ≠ y`. -/
theorem smul_ne_iff (π : FinitePerm α) {x y : X} : π • x ≠ π • y ↔ x ≠ y := by
  constructor
  · intro h heq; exact h (congrArg (π • ·) heq)
  · intro h heq; exact h (smul_injective π heq)

end

/-! ### Moved-point set -/

/-- The finite set of atoms moved by a finite permutation. -/
@[reducible]
noncomputable def movedFinset (π : FinitePerm α) : Finset α := π.property.toFinset

omit [Name α] in
/-- Membership in `movedFinset π`: `a ∈ movedFinset π ↔ π a ≠ a`. -/
@[simp]
theorem mem_movedFinset {π : FinitePerm α} {a : α} : a ∈ movedFinset π ↔ π a ≠ a := by
  simp only [movedFinset, Set.Finite.mem_toFinset, Equiv.Perm.movedPoints,
             Set.mem_setOf_eq, DFunLike.coe]

omit [Name α] in
/-- An atom not in `movedFinset σ` is a fixed point of `σ`. -/
theorem fixed_of_not_mem_movedFinset {σ : FinitePerm α} {a : α} (h : a ∉ movedFinset σ) : σ a = a := by
  rwa [mem_movedFinset, not_not] at h

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

@[simp]
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

end NominalSets
