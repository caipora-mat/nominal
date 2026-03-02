import NominalSets.PermType

/-!
# Equivariant Functions and Relations

A function `f : X → Y` between perm-sets is **equivariant** if it commutes with the
action of every finite permutation: `f (π • x) = π • f x`. This file introduces
`structure`-based predicates following the `Continuous`/`ContinuousMap` dual-layer
pattern in Mathlib: named `Prop` predicates that prevent auto-unfolding and support
dot notation. The bundled layer is provided downstream by `NFun` (finitely supported
functions) rather than a separate `EquivariantMap` type.

## Main definitions

* `IsEquivariant f` — single-field `structure` asserting `f (π • x) = π • f x` for all `π, x`.
* `IsEquivariant₂ f` — single-field `structure` asserting `f (π • x) (π • y) = π • f x y` for all `π, x, y`.
* `EquivariantRel R` — single-field `structure` asserting `R (π • x) (π • y) ↔ R x y` for all `π, x, y`.
* `EquivariantPred P` — `abbrev` for `∀ π x, P (π • x) ↔ P x`.

## Main results

### IsEquivariant

* `isEquivariant_id` — the identity function is equivariant.
* `isEquivariant_const` — a constant function is equivariant when the constant is fixed by all permutations.
* `IsEquivariant.comp` — composition of equivariant functions is equivariant.
* `IsEquivariant.prod` — pairing two equivariant functions gives an equivariant function into the product.
* `isEquivariant_fst` / `isEquivariant_snd` — product projections are equivariant.
* `isEquivariant_inl` / `isEquivariant_inr` — sum injections are equivariant.

### IsEquivariant₂

* `IsEquivariant₂.left` — fix the right argument (when fixed by all permutations) to get a unary equivariant function.
* `IsEquivariant₂.right` — fix the left argument (when fixed by all permutations) to get a unary equivariant function.

### EquivariantRel

* `EquivariantRel.smul` — forward direction: an equivariant relation is preserved by the action.
* `EquivariantRel.of_smul` — backward direction: if the relation holds on acted elements it holds on the originals.
* `EquivariantRel.comp_left` — pre-composing an equivariant relation with an equivariant function on the left.
* `EquivariantRel.comp_right` — pre-composing an equivariant relation with an equivariant function on the right.

## References

* [A. M. Pitts, *Nominal Sets*][Pitts2013], Section 2.3.
-/

namespace NominalSets

variable {α : Type*} [Name α]

/-! ### Equivariant functions -/

/-- A function `f : X → Y` between perm-sets is **equivariant** if it commutes with the
finite-permutation action: `f (π • x) = π • f x` for every `π : FinitePerm α`.

Defined as a single-field `structure` (like `Continuous`) so that Lean does not
auto-unfold it and so that dot notation (`hf.map_smul`) works. -/
structure IsEquivariant {X : Type*} {Y : Type*} [PermType α X] [PermType α Y]
    (f : X → Y) : Prop where
  /-- An equivariant function commutes with the action. -/
  map_smul : ∀ (π : FinitePerm α) (x : X), f (π • x) = π • f x

/-- A binary function `f : X → Y → Z` between perm-sets is **equivariant** if it commutes
with the simultaneous action: `f (π • x) (π • y) = π • f x y` for every `π`. -/
structure IsEquivariant₂ {X : Type*} {Y : Type*} {Z : Type*} [PermType α X] [PermType α Y]
   [PermType α Z] (f : X → Y → Z) : Prop where
  /-- An equivariant binary function commutes with the action on both arguments. -/
  map_smul : ∀ (π : FinitePerm α) (x : X) (y : Y), f (π • x) (π • y) = π • f x y

/-! ### Equivariant relations -/

/-- A binary relation `R : X → Y → Prop` is **equivariant** if it is invariant under the
simultaneous permutation action on both arguments: `R (π • x) (π • y) ↔ R x y` for
every `π : FinitePerm α`. This is a generalisation of Pitts' Definition 3.8 from
`R : α → X → Prop` to arbitrary perm-set arguments. -/
structure EquivariantRel {X : Type*} {Y : Type*} [PermType α X] [PermType α Y]
    (R : X → Y → Prop) : Prop where
  /-- An equivariant relation is invariant under the simultaneous action. -/
  smul_iff : ∀ (π : FinitePerm α) (x : X) (y : Y), R (π • x) (π • y) ↔ R x y

/-- A unary predicate `P : X → Prop` is **equivariant** if it is invariant under the
permutation action: `P (π • x) ↔ P x` for every `π : FinitePerm α`. -/
abbrev EquivariantPred {X : Type*} [PermType α X] (P : X → Prop) : Prop :=
  ∀ (π : FinitePerm α) (x : X), P (π • x) ↔ P x

/-! ### Basic API — IsEquivariant -/

section API

variable {X : Type*} [PermType α X]
variable {Y : Type*} [PermType α Y]
variable {Z : Type*} [PermType α Z]

/-- The identity function is equivariant. -/
theorem isEquivariant_id : IsEquivariant (α := α) (id : X → X) where
  map_smul _ _ := rfl

/-- A constant function is equivariant when the constant is fixed by all permutations. -/
theorem isEquivariant_const {y : Y} (hy : ∀ π : FinitePerm α, π • y = y) :
    IsEquivariant (α := α) (fun _ : X ↦ y) where
  map_smul π _ := (hy π).symm

/-- The composition of two equivariant functions is equivariant. -/
theorem IsEquivariant.comp {g : Y → Z} {f : X → Y}
    (hg : IsEquivariant (α := α) g) (hf : IsEquivariant (α := α) f) :
    IsEquivariant (α := α) (g ∘ f) where
  map_smul π x := by simp [Function.comp, hf.map_smul, hg.map_smul]

/-- Pairing two equivariant functions gives an equivariant function into the product. -/
theorem IsEquivariant.prod {f : X → Y} {g : X → Z}
    (hf : IsEquivariant (α := α) f) (hg : IsEquivariant (α := α) g) :
    IsEquivariant (α := α) (fun x ↦ (f x, g x)) where
  map_smul π x := by simp [hf.map_smul, hg.map_smul]

/-- The first projection is equivariant. -/
theorem isEquivariant_fst : IsEquivariant (α := α) (Prod.fst : X × Y → X) where
  map_smul π p := by simp

/-- The second projection is equivariant. -/
theorem isEquivariant_snd : IsEquivariant (α := α) (Prod.snd : X × Y → Y) where
  map_smul π p := by simp

/-- The left injection into a sum is equivariant. -/
theorem isEquivariant_inl : IsEquivariant (α := α) (Sum.inl : X → X ⊕ Y) where
  map_smul π x := by simp

/-- The right injection into a sum is equivariant. -/
theorem isEquivariant_inr : IsEquivariant (α := α) (Sum.inr : Y → X ⊕ Y) where
  map_smul π y := by simp

/-! ### IsEquivariant₂ -/

theorem IsEquivariant₂.left {f : X → Y → Z} (hf : IsEquivariant₂ (α := α) f)
    {y : Y} (hy : ∀ π : FinitePerm α, π • y = y) :
    IsEquivariant (α := α) (f · y) where
  map_smul π x := by
    conv_lhs => rw [show y = π • y from (hy π).symm]
    rw [hf.map_smul]

theorem IsEquivariant₂.right {f : X → Y → Z} (hf : IsEquivariant₂ (α := α) f)
    {x : X} (hx : ∀ π : FinitePerm α, π • x = x) :
    IsEquivariant (α := α) (f x) where
  map_smul π y := by
    conv_lhs => rw [show x = π • x from (hx π).symm]
    rw [hf.map_smul]

/-! ### Basic API — EquivariantRel -/

/-- Forward direction: an equivariant relation is preserved by the action. -/
@[grind .] theorem EquivariantRel.smul {R : X → Y → Prop} (hR : EquivariantRel (α := α) R)
    (π : FinitePerm α) {x : X} {y : Y} (h : R x y) : R (π • x) (π • y) :=
  (hR.smul_iff π x y).mpr h

/-- Backward direction: if an equivariant relation holds on acted elements, it holds
on the originals. -/
@[grind .] theorem EquivariantRel.of_smul {R : X → Y → Prop} (hR : EquivariantRel (α := α) R)
    (π : FinitePerm α) {x : X} {y : Y} (h : R (π • x) (π • y)) : R x y :=
  (hR.smul_iff π x y).mp h

/-- Pre-composing an equivariant relation with an equivariant function on the left. -/
theorem EquivariantRel.comp_left {R : Y → Z → Prop} {f : X → Y}
    (hR : EquivariantRel (α := α) R) (hf : IsEquivariant (α := α) f) :
    EquivariantRel (α := α) (fun x z ↦ R (f x) z) where
  smul_iff π x z := by rw [hf.map_smul]; exact hR.smul_iff π (f x) z

/-- Pre-composing an equivariant relation with an equivariant function on the right. -/
theorem EquivariantRel.comp_right {R : X → Z → Prop} {g : Y → Z}
    (hR : EquivariantRel (α := α) R) (hg : IsEquivariant (α := α) g) :
    EquivariantRel (α := α) (fun x y ↦ R x (g y)) where
  smul_iff π x y := by rw [hg.map_smul]; exact hR.smul_iff π x (g y)

end API

end NominalSets
