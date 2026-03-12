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

* `IsEquivariant α f` — single-field `structure` asserting `f (π • x) = π • f x` for all `π, x`.
* `IsEquivariant₂ α f` — single-field `structure` asserting `f (π • x) (π • y) = π • f x y` for all `π, x, y`.
* `EquivariantRel α R` — single-field `structure` asserting `R (π • x) (π • y) ↔ R x y` for all `π, x, y`.
* `EquivariantPred α P` — `abbrev` for `∀ π x, P (π • x) ↔ P x`.

## Main results

### IsEquivariant

* `isEquivariant_id` — the identity function is equivariant.
* `isEquivariant_const` — a constant function is equivariant when the constant is fixed by all permutations.
* `IsEquivariant.comp` — composition of equivariant functions is equivariant.
* `IsEquivariant.prod` — pairing two equivariant functions gives an equivariant function into the product.
* `isEquivariant_fst` / `isEquivariant_snd` — product projections are equivariant.
* `isEquivariant_inl` / `isEquivariant_inr` — sum injections are equivariant.
* `isEquivariant_sum_elim` — case analysis on a sum is equivariant.
* `isEquivariant_option_elim` — eliminating an option is equivariant.
* `isEquivariant_some` — `Option.some` is equivariant.
* `isEquivariant_option_map` — `Option.map` with an equivariant function is equivariant.
* `isEquivariant_prod_map` — `Prod.map` of two equivariant functions is equivariant.
* `IsEquivariant.map_smul_inv` — inverse form of equivariance: `f (π⁻¹ • x) = π⁻¹ • f x`.
* `IsEquivariant.uncurry` — uncurrying an equivariant function on products yields a binary equivariant function.

### IsEquivariant₂

* `isEquivariant₂_smul` — the permutation action `(· • ·)` is an equivariant binary function.
* `IsEquivariant₂.curry` — currying a binary equivariant function (converse of `uncurry`).
* `IsEquivariant₂.left` — fix the right argument (when fixed by all permutations) to get a unary equivariant function.
* `IsEquivariant₂.right` — fix the left argument (when fixed by all permutations) to get a unary equivariant function.
* `IsEquivariant₂.comp_pre_left` — pre-composing with an equivariant function on the left argument.
* `IsEquivariant₂.comp_pre_right` — pre-composing with an equivariant function on the right argument.
* `IsEquivariant₂.comp_post` — post-composing an equivariant₂ function with an equivariant function.
* `IsEquivariant₂.flip` — flipping arguments of a binary equivariant function.

### EquivariantRel

* `equivariantRel_eq` — equality is an equivariant relation.
* `EquivariantRel.smul_iff'` — standalone biconditional: `R (π • x) (π • y) ↔ R x y`.
* `EquivariantRel.smul` — forward direction: an equivariant relation is preserved by the action.
* `EquivariantRel.of_smul` — backward direction: if the relation holds on acted elements it holds on the originals.
* `EquivariantRel.comp_left` — pre-composing an equivariant relation with an equivariant function on the left.
* `EquivariantRel.comp_right` — pre-composing an equivariant relation with an equivariant function on the right.
* `EquivariantRel.comp_both` — pre-composing with equivariant functions on both arguments.
* `EquivariantRel.and` — conjunction of equivariant relations is equivariant.
* `EquivariantRel.or` — disjunction of equivariant relations is equivariant.
* `EquivariantRel.not` — negation of an equivariant relation is equivariant.
* `EquivariantRel.imp` — implication of two equivariant relations is equivariant.
* `EquivariantRel.iff` — biconditional of two equivariant relations is equivariant.
* `EquivariantRel.flip` — flipping arguments of an equivariant relation.
* `IsEquivariant.toEquivariantRel_graph` — the graph of an equivariant function is equivariant.
* `EquivariantRel.forall_right` — universally quantifying the right argument preserves equivariance.
* `EquivariantRel.exists_right` — existentially quantifying the right argument preserves equivariance.

### EquivariantPred

* `EquivariantPred.smul_iff'` — standalone biconditional: `P (π • x) ↔ P x`.
* `EquivariantPred.smul` — forward direction: an equivariant predicate is preserved by the action.
* `EquivariantPred.of_smul` — backward direction: if the predicate holds on an acted element it holds on the original.
* `EquivariantPred.toEquivariantRel` — lift a predicate to an equivariant relation on the left.
* `EquivariantPred.toEquivariantRel_right` — lift a predicate to an equivariant relation on the right.
* `EquivariantPred.not` — negation of an equivariant predicate is equivariant.
* `EquivariantPred.and` — conjunction of two equivariant predicates is equivariant.
* `EquivariantPred.or` — disjunction of two equivariant predicates is equivariant.
* `EquivariantPred.comp` — pre-composing an equivariant predicate with an equivariant function.

### Finset utilities

* `finset_smul_filter` — `π • (s.filter p) = (π • s).filter p` when `p` is an equivariant predicate.

## References

* [A. M. Pitts, *Nominal Sets*][Pitts2013], Section 2.3.
-/

namespace NominalSets

variable {α : Type*} [Name α]

/-! ### Equivariant functions -/

/-- A function `f : X → Y` between perm-sets is **equivariant** if it commutes with the
finite-permutation action: `f (π • x) = π • f x` for every `π : FinitePerm α`.

Defined as a single-field `structure` (like `Continuous`) so that Lean does not auto-unfold it and so that dot notation (`hf.map_smul`) works. -/
structure IsEquivariant (α : Type*) [Name α] {X : Type*} {Y : Type*} [PermType α X] [PermType α Y] (f : X → Y) : Prop where
  /-- An equivariant function commutes with the action. -/
  map_smul : ∀ (π : FinitePerm α) (x : X), f (π • x) = π • f x

/-- A binary function `f : X → Y → Z` between perm-sets is **equivariant** if it commutes with the simultaneous action: `f (π • x) (π • y) = π • f x y` for every `π`. -/
structure IsEquivariant₂ (α : Type*) [Name α] {X : Type*} {Y : Type*} {Z : Type*} [PermType α X] [PermType α Y] [PermType α Z] (f : X → Y → Z) : Prop where
  /-- An equivariant binary function commutes with the action on both arguments. -/
  map_smul : ∀ (π : FinitePerm α) (x : X) (y : Y), f (π • x) (π • y) = π • f x y

/-! ### Equivariant relations -/

/-- A binary relation `R : X → Y → Prop` is **equivariant** if it is invariant under the simultaneous permutation action on both arguments: `R (π • x) (π • y) ↔ R x y` for
every `π : FinitePerm α`. This is a generalisation of Pitts' Definition 3.8 from `R : α → X → Prop` to arbitrary perm-set arguments. -/
structure EquivariantRel (α : Type*) [Name α] {X : Type*} {Y : Type*} [PermType α X] [PermType α Y] (R : X → Y → Prop) : Prop where
  /-- An equivariant relation is invariant under the simultaneous action. -/
  smul_iff : ∀ (π : FinitePerm α) (x : X) (y : Y), R (π • x) (π • y) ↔ R x y

/-- A unary predicate `P : X → Prop` is **equivariant** if it is invariant under the permutation action: `P (π • x) ↔ P x` for every `π : FinitePerm α`. -/
abbrev EquivariantPred (α : Type*) [Name α] {X : Type*} [PermType α X] (P : X → Prop) : Prop := ∀ (π : FinitePerm α) (x : X), P (π • x) ↔ P x

/-! ### IsEquivariant "API" -/

section API

variable {X : Type*} [PermType α X]
variable {Y : Type*} [PermType α Y]
variable {Z : Type*} [PermType α Z]

/-- The identity function is equivariant. -/
theorem isEquivariant_id : IsEquivariant α (id : X → X) where
  map_smul _ _ := rfl

/-- A constant function is equivariant when the constant is fixed by all permutations. -/
theorem isEquivariant_const {y : Y} (hy : ∀ π : FinitePerm α, π • y = y) : IsEquivariant α (fun _ : X ↦ y) where
  map_smul π _ := (hy π).symm

/-- The composition of two equivariant functions is equivariant. -/
theorem IsEquivariant.comp {g : Y → Z} {f : X → Y} (hg : IsEquivariant α g) (hf : IsEquivariant α f) : IsEquivariant α (g ∘ f) where
  map_smul π x := by simp [Function.comp, hf.map_smul, hg.map_smul]

/-- Pairing two equivariant functions gives an equivariant function into the product. -/
theorem IsEquivariant.prod {f : X → Y} {g : X → Z} (hf : IsEquivariant α f) (hg : IsEquivariant α g) : IsEquivariant α (fun x ↦ (f x, g x)) where
  map_smul π x := by simp [hf.map_smul, hg.map_smul]

/-- The first projection is equivariant. -/
theorem isEquivariant_fst : IsEquivariant α (Prod.fst : X × Y → X) where
  map_smul π p := by simp

/-- The second projection is equivariant. -/
theorem isEquivariant_snd : IsEquivariant α (Prod.snd : X × Y → Y) where
  map_smul π p := by simp

/-- The left injection into a sum is equivariant. -/
theorem isEquivariant_inl : IsEquivariant α (Sum.inl : X → X ⊕ Y) where
  map_smul π x := by simp

/-- The right injection into a sum is equivariant. -/
theorem isEquivariant_inr : IsEquivariant α (Sum.inr : Y → X ⊕ Y) where
  map_smul π y := by simp

/-- Case analysis on a sum preserves equivariance. -/
theorem isEquivariant_sum_elim {f : X → Z} {g : Y → Z} (hf : IsEquivariant α f) (hg : IsEquivariant α g) : IsEquivariant α (Sum.elim f g) where
  map_smul π s := by cases s <;> simp [hf.map_smul, hg.map_smul]

/-- Eliminating an option is equivariant when the default is fixed by all permutations. -/
theorem isEquivariant_option_elim {y : Y} (hy : ∀ π : FinitePerm α, π • y = y) {f : X → Y} (hf : IsEquivariant α f) : IsEquivariant α (fun o : Option X ↦ o.elim y f) where
  map_smul π o := by cases o <;> simp [hf.map_smul, hy]

/-- `Option.some` is equivariant. -/
theorem isEquivariant_some : IsEquivariant α (some : X → Option X) where
  map_smul π x := by simp

/-- `Option.map` with an equivariant function is equivariant. -/
theorem isEquivariant_option_map {f : X → Y} (hf : IsEquivariant α f) : IsEquivariant α (Option.map f : Option X → Option Y) where
  map_smul π o := by cases o <;> simp [hf.map_smul]

/-- `Prod.map` of two equivariant functions is equivariant. -/
theorem isEquivariant_prod_map {W : Type*} [PermType α W] {V : Type*} [PermType α V]
    {f : X → W} {g : Y → V} (hf : IsEquivariant α f) (hg : IsEquivariant α g) : IsEquivariant α (Prod.map f g) where
  map_smul π p := by simp [Prod.map, hf.map_smul, hg.map_smul]

/-- Inverse form of equivariance. -/
theorem IsEquivariant.map_smul_inv {f : X → Y} (hf : IsEquivariant α f) (π : FinitePerm α) (x : X) : f (π⁻¹ • x) = π⁻¹ • f x :=
  hf.map_smul π⁻¹ x

/-- Uncurrying an equivariant function on products yields a binary equivariant function. -/
theorem IsEquivariant.uncurry {f : X × Y → Z} (hf : IsEquivariant α f) : IsEquivariant₂ α (Function.curry f) where
  map_smul π x y := by
    simp only [Function.curry]
    rw [show (π • x, π • y) = π • (x, y) from (PermType.prod_smul π x y).symm]
    exact hf.map_smul π (x, y)

/-! ### IsEquivariant₂ -/

/-- The permutation action `(· • ·) : FinitePerm α → X → X` is an equivariant binary function
(with respect to the conjugation action on `FinitePerm α`). -/
theorem isEquivariant₂_smul : IsEquivariant₂ α ((· • ·) : FinitePerm α → X → X) where
  map_smul π σ x := calc
    (π • σ) • (π • x) = (π * σ * π⁻¹) • (π • x) := by rw [PermType.conj_smul]
    _ = π • (σ • (π⁻¹ • (π • x))) := by rw [PermType.mul_smul', PermType.mul_smul']
    _ = π • σ • x := by rw [PermType.inv_smul_smul]

theorem IsEquivariant₂.left {f : X → Y → Z} (hf : IsEquivariant₂ α f) {y : Y} (hy : ∀ π : FinitePerm α, π • y = y) : IsEquivariant α (f · y) where
  map_smul π x := by
    conv_lhs => rw [show y = π • y from (hy π).symm]
    rw [hf.map_smul]

theorem IsEquivariant₂.right {f : X → Y → Z} (hf : IsEquivariant₂ α f) {x : X} (hx : ∀ π : FinitePerm α, π • x = x) : IsEquivariant α (f x) where
  map_smul π y := by
    conv_lhs => rw [show x = π • x from (hx π).symm]
    rw [hf.map_smul]

/-- Currying a binary equivariant function yields an equivariant function on products.
Converse of `IsEquivariant.uncurry`. -/
theorem IsEquivariant₂.curry {f : X → Y → Z} (hf : IsEquivariant₂ α f) : IsEquivariant α (Function.uncurry f) where
  map_smul π p := by
    simp only [Function.uncurry]
    exact hf.map_smul π p.1 p.2

/-- Pre-composing an equivariant binary function with an equivariant function on the
left argument. -/
theorem IsEquivariant₂.comp_pre_left {W : Type*} [PermType α W] {f : X → Y → Z} {g : W → X}
    (hf : IsEquivariant₂ α f) (hg : IsEquivariant α g) : IsEquivariant₂ α (fun w y ↦ f (g w) y) where
  map_smul π w y := by rw [hg.map_smul, hf.map_smul]

/-- Pre-composing an equivariant binary function with an equivariant function on the
right argument. -/
theorem IsEquivariant₂.comp_pre_right {W : Type*} [PermType α W] {f : X → Y → Z} {g : W → Y}
    (hf : IsEquivariant₂ α f) (hg : IsEquivariant α g) : IsEquivariant₂ α (fun x w ↦ f x (g w)) where
  map_smul π x w := by rw [hg.map_smul, hf.map_smul]

/-- Post-composing an equivariant binary function with an equivariant unary function. -/
theorem IsEquivariant₂.comp_post {W : Type*} [PermType α W] {f : X → Y → Z} {g : Z → W}
    (hf : IsEquivariant₂ α f) (hg : IsEquivariant α g) : IsEquivariant₂ α (fun x y ↦ g (f x y)) where
  map_smul π x y := by rw [hf.map_smul, hg.map_smul]

/-- Flipping the arguments of a binary equivariant function gives a binary equivariant function. -/
theorem IsEquivariant₂.flip {f : X → Y → Z} (hf : IsEquivariant₂ α f) : IsEquivariant₂ α (fun y x ↦ f x y) where
  map_smul π y x := hf.map_smul π x y

/-! ### EquivariantRel "API" -/

/-- Equality is an equivariant relation. -/
theorem equivariantRel_eq : EquivariantRel α (Eq : X → X → Prop) where
  smul_iff π _ _ := ⟨fun h ↦ PermType.smul_injective π h, fun h ↦ congrArg (π • ·) h⟩

/-- Standalone biconditional form of `EquivariantRel.smul_iff`, usable as a rewrite. -/
theorem EquivariantRel.smul_iff' {R : X → Y → Prop} (hR : EquivariantRel α R) (π : FinitePerm α) (x : X) (y : Y) : R (π • x) (π • y) ↔ R x y :=
  hR.smul_iff π x y

/-- Forward direction: an equivariant relation is preserved by the action. -/
@[grind .] theorem EquivariantRel.smul {R : X → Y → Prop} (hR : EquivariantRel α R) (π : FinitePerm α) {x : X} {y : Y} (h : R x y) : R (π • x) (π • y) :=
  (hR.smul_iff π x y).mpr h

/-- Backward direction: if an equivariant relation holds on acted elements, it holds
on the originals. -/
@[grind .] theorem EquivariantRel.of_smul {R : X → Y → Prop} (hR : EquivariantRel α R) (π : FinitePerm α) {x : X} {y : Y} (h : R (π • x) (π • y)) : R x y :=
  (hR.smul_iff π x y).mp h

/-- Pre-composing an equivariant relation with an equivariant function on the left. -/
theorem EquivariantRel.comp_left {R : Y → Z → Prop} {f : X → Y} (hR : EquivariantRel α R) (hf : IsEquivariant α f) :
    EquivariantRel α (fun x z ↦ R (f x) z) where
  smul_iff π x z := by rw [hf.map_smul]; exact hR.smul_iff π (f x) z

/-- Pre-composing an equivariant relation with an equivariant function on the right. -/
theorem EquivariantRel.comp_right {R : X → Z → Prop} {g : Y → Z} (hR : EquivariantRel α R) (hg : IsEquivariant α g) :
    EquivariantRel α (fun x y ↦ R x (g y)) where
  smul_iff π x y := by rw [hg.map_smul]; exact hR.smul_iff π x (g y)

/-- Pre-composing an equivariant relation with equivariant functions on both arguments. -/
theorem EquivariantRel.comp_both {W : Type*} [PermType α W] {R : Y → Z → Prop} {f : X → Y} {g : W → Z} (hR : EquivariantRel α R) (hf : IsEquivariant α f) (hg : IsEquivariant α g) :
    EquivariantRel α (fun x w ↦ R (f x) (g w)) where
  smul_iff π x w := by rw [hf.map_smul, hg.map_smul]; exact hR.smul_iff π (f x) (g w)

/-- The conjunction of two equivariant relations is equivariant. -/
theorem EquivariantRel.and {R S : X → Y → Prop} (hR : EquivariantRel α R) (hS : EquivariantRel α S) : EquivariantRel α (fun x y ↦ R x y ∧ S x y) where
  smul_iff π x y := by rw [hR.smul_iff', hS.smul_iff']

/-- The disjunction of two equivariant relations is equivariant. -/
theorem EquivariantRel.or {R S : X → Y → Prop} (hR : EquivariantRel α R) (hS : EquivariantRel α S) : EquivariantRel α (fun x y ↦ R x y ∨ S x y) where
  smul_iff π x y := by rw [hR.smul_iff', hS.smul_iff']

/-- The negation of an equivariant relation is equivariant. -/
theorem EquivariantRel.not {R : X → Y → Prop} (hR : EquivariantRel α R) : EquivariantRel α (fun x y ↦ ¬ R x y) where
  smul_iff π x y := by rw [hR.smul_iff']

/-- The implication of two equivariant relations is equivariant. -/
theorem EquivariantRel.imp {R S : X → Y → Prop} (hR : EquivariantRel α R) (hS : EquivariantRel α S) : EquivariantRel α (fun x y ↦ R x y → S x y) where
  smul_iff π x y := by
    constructor
    · intro h hr; exact (hS.smul_iff' π x y).mp (h ((hR.smul_iff' π x y).mpr hr))
    · intro h hr; exact (hS.smul_iff' π x y).mpr (h ((hR.smul_iff' π x y).mp hr))

/-- The biconditional of two equivariant relations is equivariant. -/
theorem EquivariantRel.iff {R S : X → Y → Prop} (hR : EquivariantRel α R) (hS : EquivariantRel α S) : EquivariantRel α (fun x y ↦ R x y ↔ S x y) where
  smul_iff π x y := by
    constructor
    · intro h; exact ⟨fun hs ↦ (hS.smul_iff' π x y).mp (h.mp ((hR.smul_iff' π x y).mpr hs)),
                       fun hr ↦ (hR.smul_iff' π x y).mp (h.mpr ((hS.smul_iff' π x y).mpr hr))⟩
    · intro h; exact ⟨fun hs ↦ (hS.smul_iff' π x y).mpr (h.mp ((hR.smul_iff' π x y).mp hs)),
                       fun hr ↦ (hR.smul_iff' π x y).mpr (h.mpr ((hS.smul_iff' π x y).mp hr))⟩

/-- Flipping the arguments of an equivariant relation gives an equivariant relation. -/
theorem EquivariantRel.flip {R : X → Y → Prop} (hR : EquivariantRel α R) : EquivariantRel α (fun y x ↦ R x y) where
  smul_iff π y x := hR.smul_iff π x y

/-- The graph of an equivariant function is an equivariant relation. -/
theorem IsEquivariant.toEquivariantRel_graph {f : X → Y} (hf : IsEquivariant α f) : EquivariantRel α (fun x y ↦ f x = y) :=
  equivariantRel_eq.comp_left hf

/-- Universally quantifying the right argument of an equivariant relation gives an equivariant predicate. -/
theorem EquivariantRel.forall_right {R : X → Y → Prop} (hR : EquivariantRel α R) : EquivariantPred α (fun x ↦ ∀ y, R x y) :=
  fun π x ↦ ⟨
    fun h y ↦ (hR.smul_iff π x y).mp (h (π • y)),
    fun h y ↦ by have := (hR.smul_iff π x (π⁻¹ • y)).mpr (h (π⁻¹ • y)); rwa [PermType.smul_inv_smul] at this⟩

/-- Existentially quantifying the right argument of an equivariant relation gives an equivariant predicate. -/
theorem EquivariantRel.exists_right {R : X → Y → Prop} (hR : EquivariantRel α R) : EquivariantPred α (fun x ↦ ∃ y, R x y) :=
  fun π x ↦ ⟨
    fun ⟨y, hy⟩ ↦ ⟨π⁻¹ • y, (hR.smul_iff π x (π⁻¹ • y)).mp (by rwa [PermType.smul_inv_smul])⟩,
    fun ⟨y, hy⟩ ↦ ⟨π • y, (hR.smul_iff π x y).mpr hy⟩⟩

/-! ### EquivariantPred "API" -/

/-- Standalone biconditional form of an equivariant predicate, usable as a rewrite. -/
theorem EquivariantPred.smul_iff' {P : X → Prop} (hP : EquivariantPred α P) (π : FinitePerm α) (x : X) : P (π • x) ↔ P x :=
  hP π x

/-- Forward direction: an equivariant predicate is preserved by the action. -/
theorem EquivariantPred.smul {P : X → Prop} (hP : EquivariantPred α P) (π : FinitePerm α) {x : X} (h : P x) : P (π • x) :=
  (hP π x).mpr h

/-- Backward direction: if an equivariant predicate holds on an acted element, it holds on the original. -/
theorem EquivariantPred.of_smul {P : X → Prop} (hP : EquivariantPred α P) (π : FinitePerm α) {x : X} (h : P (π • x)) : P x :=
  (hP π x).mp h

/-- An equivariant predicate on `X` lifts to an equivariant relation that ignores the second argument. -/
theorem EquivariantPred.toEquivariantRel {P : X → Prop} (hP : EquivariantPred α P) : EquivariantRel α (fun x (_ : Y) ↦ P x) where
  smul_iff π x _ := hP π x

/-- An equivariant predicate on `Y` lifts to an equivariant relation that ignores the first argument. -/
theorem EquivariantPred.toEquivariantRel_right {P : Y → Prop} (hP : EquivariantPred α P) : EquivariantRel α (fun (_ : X) y ↦ P y) where
  smul_iff π _ y := hP π y

/-- The negation of an equivariant predicate is equivariant. -/
theorem EquivariantPred.not {P : X → Prop} (hP : EquivariantPred α P) :
    EquivariantPred α (fun x ↦ ¬ P x) :=
  fun π x ↦ by change ¬ P (π • x) ↔ ¬ P x; rw [hP.smul_iff']

/-- The conjunction of two equivariant predicates is equivariant. -/
theorem EquivariantPred.and {P Q : X → Prop} (hP : EquivariantPred α P) (hQ : EquivariantPred α Q) :
    EquivariantPred α (fun x ↦ P x ∧ Q x) :=
  fun π x ↦ by change P (π • x) ∧ Q (π • x) ↔ P x ∧ Q x; rw [hP.smul_iff', hQ.smul_iff']

/-- The disjunction of two equivariant predicates is equivariant. -/
theorem EquivariantPred.or {P Q : X → Prop} (hP : EquivariantPred α P) (hQ : EquivariantPred α Q) :
    EquivariantPred α (fun x ↦ P x ∨ Q x) :=
  fun π x ↦ by change P (π • x) ∨ Q (π • x) ↔ P x ∨ Q x; rw [hP.smul_iff', hQ.smul_iff']

/-- Pre-composing an equivariant predicate with an equivariant function. -/
theorem EquivariantPred.comp {P : Y → Prop} {f : X → Y} (hP : EquivariantPred α P) (hf : IsEquivariant α f) :
    EquivariantPred α (fun x ↦ P (f x)) :=
  fun π x ↦ by change P (f (π • x)) ↔ P (f x); rw [hf.map_smul, hP.smul_iff']

/-! ### Finset filtering by equivariant predicates -/

/-- The permutation action on `Finset α` commutes with filtering by an equivariant predicate:
    `π • (s.filter p) = (π • s).filter p` when `p` is invariant under the action. -/
theorem finset_smul_filter (π : FinitePerm α) (s : Finset α) (p : α → Bool) (hp : EquivariantPred α (fun a : α => p a = true)) :
    π • (s.filter (fun a => p a)) = (π • s).filter (fun a => p a) := by
  ext b
  simp only [PermType.mem_smul_finset_iff, Finset.mem_filter, PermType.atoms_smul]
  rw [show (p (π⁻¹ b) = true) = (p b = true) from propext (hp π⁻¹ b)]

end API

end NominalSets
