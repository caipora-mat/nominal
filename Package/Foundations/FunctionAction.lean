/-
Copyright (c) 2026 Nominal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nominal contributors
-/
import Package.Foundations.ActionSupport
import Mathlib.GroupTheory.GroupAction.Hom
import Mathlib.Algebra.Group.Action.Prod

/-!
# Full function objects with conjugation

The group parameter selects a distinct carrier without raising its universe.
Ordinary arrows retain Mathlib's pointwise action. No finite-support claim is
made for an arbitrary function object.
-/

namespace NominalPackage
universe u v w z t

/-- All maps from X to Y, on a carrier reserved for conjugation by G. -/
structure FunctionObject (G : Type u) (X : Type v) (Y : Type w) : Type (max v w) where
  /-- The ordinary map, with no support certificate. -/
  toFun : X → Y

namespace FunctionObject
variable {G : Type u} {X : Type v} {Y : Type w} {Z : Type z}

instance : FunLike (FunctionObject G X Y) X Y where
  coe := toFun
  coe_injective := by rintro ⟨f⟩ ⟨g⟩ h; cases h; rfl

@[ext] theorem ext {F H : FunctionObject G X Y} (h : ∀ x, F x = H x) : F = H :=
  DFunLike.ext F H h

/-- Explicitly select the function-space action carrier; no support is inferred. -/
def ofFun (G : Type u) (f : X → Y) : FunctionObject G X Y := ⟨f⟩

@[simp] theorem ofFun_apply (f : X → Y) (x : X) : ofFun G f x = f x := rfl
@[simp] theorem coe_ofFun (f : X → Y) : (ofFun G f : X → Y) = f := rfl

/-- An ordinary type equivalence, not in general equivariant to pointwise arrows. -/
def equiv (G : Type u) (X : Type v) (Y : Type w) : FunctionObject G X Y ≃ (X → Y) where
  toFun F := F
  invFun := ofFun G
  left_inv _ := rfl
  right_inv _ := rfl

/-- Identity as a function object. -/
def id (G : Type u) (X : Type v) : FunctionObject G X X := ofFun G _root_.id
/-- Constant functions; this constructor does not assert support of the value. -/
def const (G : Type u) (X : Type v) (y : Y) : FunctionObject G X Y := ofFun G (Function.const X y)
/-- Ordinary composition on full function objects. -/
def comp (H : FunctionObject G Y Z) (F : FunctionObject G X Y) : FunctionObject G X Z :=
  ofFun G (H ∘ F)
/-- Pointwise pairing of two function objects. -/
def pair (F : FunctionObject G X Y) (H : FunctionObject G X Z) : FunctionObject G X (Y × Z) :=
  ofFun G (fun x => (F x, H x))
/-- Evaluation is ordinary application. -/
def eval (p : FunctionObject G X Y × X) : Y := p.1 p.2
/-- Full-space curry has no support or inhabitance premise. -/
def curry (F : FunctionObject G (X × Y) Z) : FunctionObject G X (FunctionObject G Y Z) :=
  ofFun G (fun x => ofFun G (Function.curry F x))
/-- Full-space uncurrying. -/
def uncurry (H : FunctionObject G X (FunctionObject G Y Z)) : FunctionObject G (X × Y) Z :=
  ofFun G (Function.uncurry (fun x y => H x y))

@[simp] theorem id_apply (x : X) : id G X x = x := rfl
@[simp] theorem const_apply (y : Y) (x : X) : const G X y x = y := rfl
@[simp] theorem comp_apply (H : FunctionObject G Y Z) (F : FunctionObject G X Y) (x : X) :
    H.comp F x = H (F x) := rfl
@[simp] theorem pair_apply (F : FunctionObject G X Y) (H : FunctionObject G X Z) (x : X) :
    F.pair H x = (F x, H x) := rfl
@[simp] theorem eval_apply (p : FunctionObject G X Y × X) : eval p = p.1 p.2 := rfl
@[simp] theorem curry_apply (F : FunctionObject G (X × Y) Z) (x : X) (y : Y) :
    F.curry x y = F (x, y) := rfl
@[simp] theorem uncurry_apply (H : FunctionObject G X (FunctionObject G Y Z)) (p : X × Y) :
    H.uncurry p = H p.1 p.2 := rfl
@[simp] theorem coe_id : (id G X : X → X) = _root_.id := rfl
@[simp] theorem coe_const (y : Y) : (const G X y : X → Y) = Function.const X y := rfl
@[simp] theorem coe_comp (H : FunctionObject G Y Z) (F : FunctionObject G X Y) :
    (H.comp F : X → Z) = H ∘ F := rfl
@[simp] theorem coe_pair (F : FunctionObject G X Y) (H : FunctionObject G X Z) :
    (F.pair H : X → Y × Z) = fun x => (F x, H x) := rfl
@[simp] theorem coe_curry_apply (F : FunctionObject G (X × Y) Z) (x : X) :
    (F.curry x : Y → Z) = Function.curry (F : X × Y → Z) x := rfl
@[simp] theorem coe_uncurry (H : FunctionObject G X (FunctionObject G Y Z)) :
    (H.uncurry : X × Y → Z) = Function.uncurry (fun x y => H x y) := rfl

@[simp] theorem comp_id (F : FunctionObject G X Y) : F.comp (id G X) = F := rfl
@[simp] theorem id_comp (F : FunctionObject G X Y) : (id G Y).comp F = F := rfl
theorem comp_assoc {W : Type t} (K : FunctionObject G Z W)
    (H : FunctionObject G Y Z) (F : FunctionObject G X Y) :
    (K.comp H).comp F = K.comp (H.comp F) := rfl
@[simp] theorem uncurry_curry (F : FunctionObject G (X × Y) Z) : F.curry.uncurry = F := by ext p; rfl
@[simp] theorem curry_uncurry (H : FunctionObject G X (FunctionObject G Y Z)) :
    H.uncurry.curry = H := by ext x y; rfl

/-- The ordinary full-space curry equivalence, including empty domains. -/
def curryEquiv (G : Type u) (X : Type v) (Y : Type w) (Z : Type z) :
    FunctionObject G (X × Y) Z ≃ FunctionObject G X (FunctionObject G Y Z) where
  toFun := curry
  invFun := uncurry
  left_inv := uncurry_curry
  right_inv := curry_uncurry

/-- Nonemptiness is needed for nontrivial codomains; empty constants all coincide. -/
theorem const_injective_iff :
    Function.Injective (const G X : Y → FunctionObject G X Y) ↔ Nonempty X ∨ Subsingleton Y := by
  classical
  constructor
  · intro h
    by_cases hx : Nonempty X
    · exact Or.inl hx
    · exact Or.inr ⟨fun y z => h (ext fun x => (hx ⟨x⟩).elim)⟩
  · rintro (hx | hy) y z h
    · let := hx
      exact Function.const_injective (congrArg (fun F : FunctionObject G X Y => (F : X → Y)) h)
    · exact hy.elim y z

section Action
variable [DivisionMonoid G] [MulAction G X] [MulAction G Y]

instance : MulAction G (FunctionObject G X Y) where
  smul g F := ⟨fun x => g • F (g⁻¹ • x)⟩
  one_smul F := by
    ext x
    change (1 : G) • F ((1 : G)⁻¹ • x) = F x
    simp
  mul_smul g h F := by
    ext x
    change (g * h) • F ((g * h)⁻¹ • x) = g • (h • F (h⁻¹ • (g⁻¹ • x)))
    simp only [mul_inv_rev, mul_smul]

@[simp] theorem smul_apply (g : G) (F : FunctionObject G X Y) (x : X) :
    (g • F) x = g • F (g⁻¹ • x) := rfl

theorem smul_const (g : G) (y : Y) : g • const G X y = const G X (g • y) := rfl

variable [MulAction G Z]
theorem smul_pair (g : G) (F : FunctionObject G X Y) (H : FunctionObject G X Z) :
    g • F.pair H = (g • F).pair (g • H) := rfl
theorem curry_smul (g : G) (F : FunctionObject G (X × Y) Z) :
    (g • F).curry = g • F.curry := rfl
theorem uncurry_smul (g : G) (H : FunctionObject G X (FunctionObject G Y Z)) :
    (g • H).uncurry = g • H.uncurry := rfl

variable {B : Type t} [SMul G B]
/-- Full curry preserves and reflects any sufficient bound. -/
theorem supports_curry_iff (S : Set B) (F : FunctionObject G (X × Y) Z) :
    MulAction.Supports G S F.curry ↔ MulAction.Supports G S F :=
  ActionSupport.supports_map_iff curry curry_smul (curryEquiv G X Y Z).injective S F

/-- Full uncurry preserves and reflects any sufficient bound. -/
theorem supports_uncurry_iff (S : Set B) (H : FunctionObject G X (FunctionObject G Y Z)) :
    MulAction.Supports G S H.uncurry ↔ MulAction.Supports G S H :=
  ActionSupport.supports_map_iff uncurry uncurry_smul (curryEquiv G X Y Z).symm.injective S H
end Action

section Group
variable [Group G] [MulAction G X] [MulAction G Y]

@[simp] theorem smul_apply_smul (g : G) (F : FunctionObject G X Y) (x : X) :
    (g • F) (g • x) = g • F x := by simp

/-- Fixing a function object means commuting with this particular group element. -/
theorem smul_eq_iff (g : G) (F : FunctionObject G X Y) :
    g • F = F ↔ ∀ x, F (g • x) = g • F x := by
  constructor
  · intro h x
    simpa using (DFunLike.congr_fun h (g • x)).symm
  · intro h
    ext x
    simpa using (h (g⁻¹ • x)).symm

theorem smul_id (g : G) : g • id G X = id G X := by ext x; simp

variable [MulAction G Z]
theorem smul_comp (g : G) (H : FunctionObject G Y Z) (F : FunctionObject G X Y) :
    g • H.comp F = (g • H).comp (g • F) := by ext x; simp

/-- Evaluation bundled using Mathlib's equivariant-map interface. -/
def evalHom (G : Type u) (X : Type v) (Y : Type w)
    [Group G] [MulAction G X] [MulAction G Y] : (FunctionObject G X Y × X) →[G] Y where
  toFun := eval
  map_smul' g p := by simp

@[simp] theorem evalHom_apply (p : FunctionObject G X Y × X) : evalHom G X Y p = p.1 p.2 := rfl

variable (G) in
/-- An ordinary map's fixer equation characterizes conjugation support. -/
theorem supports_iff {B : Type t} [SMul G B] (S : Set B) (f : X → Y) :
    MulAction.Supports G S (ofFun G f) ↔
      ∀ g : G, (∀ b ∈ S, g • b = b) → ∀ x, f (g • x) = g • f x := by
  constructor
  · intro h g hg
    exact (smul_eq_iff g (ofFun G f)).1 (h g (fun _ hb => hg _ hb))
  · intro h g hg
    exact (smul_eq_iff g (ofFun G f)).2 (h g (fun _ hb => hg hb))
end Group
end FunctionObject
end NominalPackage
