import NominalSets.PermType

/-!
# Nominal Function Space (`PFun`)

`PFun α X Y` is a **newtype wrapper** around `X → Y` carrying the conjugation action
`(π • f) x = π • f (π⁻¹ • x)`, which is the correct equivariant action on function spaces
in the theory of nominal sets.

## Why a newtype?

Mathlib already provides `Pi.instSMul`, which gives a *pointwise* action on any `ι → α`
whenever `SMul M α`:

  `(π • f) x = π • f x`   -- Pi.instSMul

Because `PermType α (X → Y)` extends `MulAction (FinitePerm α) (X → Y)`, which in turn
gives a `SMul (FinitePerm α) (X → Y)`, both instances would become available for `X → Y`.
Lean's instance search would then face a **diamond**: it may synthesise `Pi.instSMul` before
`instFun`, yielding the wrong action.

To avoid this conflict entirely, the action is wrapped in the newtype `PFun α X Y` rather
than being placed on the bare function type.

## Main definitions

* `PFun α X Y` — newtype wrapper for `X → Y` with conjugation action.
* `PFun.comp` — composition of `PFun`s.
* `PFun.id` — identity `PFun`.
* `PFun.const` — constant `PFun` returning a fixed value.
* `PFun.compFun` — compose a `PFun` with a plain function on the right.
* `PFun.funComp` — compose a plain function with a `PFun` on the left.

## Instances

* `PFun.instCoe` — coercion from `X → Y` to `PFun α X Y`.
* `PFun.instFunLike` — `PFun α X Y` elements can be applied directly as functions via `FunLike`.
* `PFun.instPermType` — action on `PFun α X Y` (`(π • f) x = π • f (π⁻¹ • x)`).

## Main results

* `PFun.smul_apply` — `(π • f) x = π • f (π⁻¹ • x)`.
* `PFun.smul_apply_smul` — `(π • f) (π • x) = π • f x`.
* `PFun.smul_id` — the identity `PFun` is a fixed point: `π • PFun.id = PFun.id`.
* `PFun.smul_const` — the action on a constant `PFun` acts on the output: `π • const y = const (π • y)`.
* `PFun.smul_comp` — the action distributes over composition: `π • (g ∘ f) = (π • g) ∘ (π • f)`.
* `PFun.smul_compFun` — the action distributes over `compFun` (conjugating the plain function).
* `PFun.smul_funComp` — the action distributes over `funComp` (conjugating the plain function).
* `PFun.comp_assoc` — composition is associative.
* `PFun.comp_id` / `PFun.id_comp` — identity laws.

## References

* [A. M. Pitts, *Nominal Sets*][Pitts2013], Chapter 1.
-/

namespace NominalSets

variable {α : Type*} [Name α]

/-- `PFun α X Y` is a **newtype wrapper** around `X → Y` carrying the action
`(π • f) x = π • f (π⁻¹ • x)`. -/
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

theorem pfun_ext_iff {X Y : Type*} {f g : PFun α X Y} : f = g ↔ ∀ x, f x = g x :=
  ⟨fun h x => congrFun (congrArg DFunLike.coe h) x, ext⟩

@[simp] theorem coe_mk {X Y : Type*} (f : X → Y) (x : X) : (PFun.mk f : PFun α X Y) x = f x := rfl

@[simp] theorem coe_apply {X Y : Type*} (f : X → Y) (x : X) : (f : PFun α X Y) x = f x := rfl

theorem mk_injective {X Y : Type*} {f g : X → Y}
    (h : (PFun.mk f : PFun α X Y) = PFun.mk g) : f = g :=
  congrArg PFun.toFun h

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

@[simp]
theorem smul_apply_smul {X Y : Type*} [PermType α X] [PermType α Y]
    (π : FinitePerm α) (f : PFun α X Y) (x : X) :
    (π • f) (π • x) = π • f x := by simp

/-! ### Composition -/

/-- Composition of `PFun`s: `(g ∘ f) x = g (f x)`. -/
def comp {X Y Z : Type*} (g : PFun α Y Z) (f : PFun α X Y) : PFun α X Z :=
  ⟨fun x => g (f x)⟩

@[simp]
theorem comp_apply {X Y Z : Type*} (g : PFun α Y Z) (f : PFun α X Y) (x : X) :
    g.comp f x = g (f x) := rfl

/-- Composition is associative. -/
theorem comp_assoc {W X Y Z : Type*} (h : PFun α Y Z) (g : PFun α X Y) (f : PFun α W X) :
    (h.comp g).comp f = h.comp (g.comp f) := rfl

/-- The identity `PFun`. -/
def id {X : Type*} : PFun α X X := ⟨_root_.id⟩

@[simp]
theorem id_apply {X : Type*} (x : X) : (PFun.id : PFun α X X) x = x := rfl

/-- The identity `PFun` is a fixed point of the action. -/
@[simp]
theorem smul_id {X : Type*} [PermType α X] (π : FinitePerm α) :
    π • (PFun.id : PFun α X X) = PFun.id := by ext x; simp

/-- Composing with the identity on the right. -/
@[simp]
theorem comp_id {X Y : Type*} (f : PFun α X Y) : f.comp PFun.id = f := rfl

/-- Composing with the identity on the left. -/
@[simp]
theorem id_comp {X Y : Type*} (f : PFun α X Y) : (PFun.id).comp f = f := rfl

/-- The permutation action distributes over composition:
`π • (g ∘ f) = (π • g) ∘ (π • f)`. -/
@[simp, grind =]
theorem smul_comp {X Y Z : Type*} [PermType α X] [PermType α Y] [PermType α Z]
    (π : FinitePerm α) (g : PFun α Y Z) (f : PFun α X Y) :
    π • g.comp f = (π • g).comp (π • f) := by
  ext x
  simp [comp_apply, smul_apply]

/-- A `PFun` composed with a plain function on the right. -/
def compFun {X Y Z : Type*} (g : PFun α Y Z) (f : X → Y) : PFun α X Z :=
  g.comp ⟨f⟩

@[simp]
theorem compFun_apply {X Y Z : Type*} (g : PFun α Y Z) (f : X → Y) (x : X) :
    g.compFun f x = g (f x) := rfl

/-- The action distributes over `compFun`: the plain function is conjugated. -/
@[simp]
theorem smul_compFun {X Y Z : Type*} [PermType α X] [PermType α Y] [PermType α Z]
    (π : FinitePerm α) (g : PFun α Y Z) (f : X → Y) :
    π • g.compFun f = (π • g).compFun (fun x => π • f (π⁻¹ • x)) := by
  ext x; simp [compFun_apply, smul_apply]

/-- A plain function composed with a `PFun` on the left. -/
def funComp {X Y Z : Type*} (g : Y → Z) (f : PFun α X Y) : PFun α X Z :=
  (⟨g⟩ : PFun α Y Z).comp f

@[simp]
theorem funComp_apply {X Y Z : Type*} (g : Y → Z) (f : PFun α X Y) (x : X) :
    funComp g f x = g (f x) := rfl

/-- The action distributes over `funComp`: the plain function is conjugated. -/
@[simp]
theorem smul_funComp {X Y Z : Type*} [PermType α X] [PermType α Y] [PermType α Z]
    (π : FinitePerm α) (g : Y → Z) (f : PFun α X Y) :
    π • funComp g f = funComp (fun y => π • g (π⁻¹ • y)) (π • f) := by
  ext x; simp [funComp_apply, smul_apply]

/-! ### Constant `PFun` -/

/-- The constant `PFun` returning `y` for every input. -/
def const {X Y : Type*} (y : Y) : PFun α X Y := ⟨fun _ => y⟩

@[simp]
theorem const_apply {X Y : Type*} (y : Y) (x : X) : (const y : PFun α X Y) x = y := rfl

/-- The action on a constant `PFun` acts on the output value. -/
@[simp]
theorem smul_const {X Y : Type*} [PermType α X] [PermType α Y]
    (π : FinitePerm α) (y : Y) :
    π • (const y : PFun α X Y) = const (π • y) := by ext x; simp [const_apply]

end PFun

end NominalSets
