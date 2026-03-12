import Nominal.Set.PFun
import Nominal.Set.Nominal
import Nominal.Set.Freshness

/-!
# Finitely Supported Functions

Not every function between nominal sets is finitely supported under the
action `(π • f) x = π • f (π⁻¹ • x)`. The type `NFun α X Y` ("nominal function")
wraps a `PFun α X Y` together with a proof of finite support, yielding a nominal set
of finitely supported functions.

## Main definitions

* `NFun α X Y` — `structure` wrapping a `PFun α X Y` together with a proof of finite support; the type of finitely supported functions from `X` to `Y`.
* `NFun.ofFun` — construct an `NFun` from a bare function and a finite-support proof.
* `NFun.ofSupports` — construct an `NFun` from a `PFun` and an explicit support set.
* `NFun.id` — the identity nominal function.
* `NFun.const` — the constant nominal function.
* `NFun.comp` — composition of nominal functions.
* `NFun.map` — post-composition with an equivariant function.
* `NFun.comap` — pre-composition with an equivariant function.
* `NFun.prod` — pairing of nominal functions.
* `NFun.eval` — the evaluation map `(f, x) ↦ f x`.
* `NFun.curry` — currying an equivariant function into a nominal function.

## Instances

* `NFun.instCoe` — coerce an `NFun` to its underlying `PFun`.
* `NFun.instFunLike` — `NFun α X Y` can be applied as functions via `FunLike`.
* `NFun.instPermType` — conjugation action on `NFun α X Y`: `(π • f) x = π • f (π⁻¹ • x)`.
* `NFun.instNominal` — `NFun α X Y` forms a nominal set.

## Main results

### Computation lemmas

* `NFun.ext` — extensionality: two `NFun`s are equal iff they agree pointwise.
* `NFun.toPFun_apply` — applying `f.toPFun` equals applying `f` directly.
* `NFun.mk_apply` — applying an `NFun` built with `mk` reduces to the underlying `PFun`.
* `NFun.ofFun_apply` / `NFun.ofSupports_apply` — computation lemmas for smart constructors.
* `NFun.ofSupports_supports` — the support set passed to `ofSupports` indeed supports the result.
* `NFun.id_apply` / `NFun.const_apply` / `NFun.comp_apply` — reduction lemmas for categorical combinators.
* `NFun.map_apply` — `(f.map g hg) x = g (f x)`.
* `NFun.comap_apply` — `(f.comap g hg) x = f (g x)`.
* `NFun.prod_apply` — `(f.prod g) x = (f x, g x)`.
* `NFun.eval_apply` — `eval p = p.1 p.2`.
* `NFun.curry_apply_apply` — `(curry f) z x = f (z, x)`.

### Permutation action

* `NFun.smul_toPFun` — `(π • f).toPFun = π • f.toPFun`.
* `NFun.smul_apply` — `(π • f) x = π • f (π⁻¹ • x)`.
* `NFun.smul_apply_smul` — `(π • f) (π • x) = π • f x`.
* `NFun.smul_const` — `π • const y = const (π • y)`.
* `NFun.smul_comp` — action distributes over composition.
* `NFun.smul_map` — action distributes over `map`.
* `NFun.smul_comap` — action distributes over `comap`.
* `NFun.smul_prod` — action distributes over pairing.

### Support and freshness

* `NFun.supports_iff_toPFun` — support for an `NFun` is equivalent to support for its underlying `PFun`.
* `NFun.supp_eq_empty_iff'` — `supp f = ∅` iff `f (π • x) = π • f x` for all `π, x`.
* `NFun.supp_eq_empty_iff_isEquivariant` — `supp f = ∅` iff `IsEquivariant α f`.
* `NFun.supports_apply` — if `s` supports `f` and `t` supports `x`, then `s ∪ t` supports `f x`.
* `NFun.supp_apply_le` — `supp (f x) ⊆ supp f ∪ supp x`.
* `NFun.supp_const` — `supp (const y) = supp y` (requires `Nonempty X`).
* `NFun.supp_const_le` — `supp (const y) ⊆ supp y` (unconditional).
* `NFun.supp_comp_le` — `supp (g.comp f) ⊆ supp g ∪ supp f`.
* `NFun.supp_map_le` — `supp (f.map g hg) ⊆ supp f`.
* `NFun.supp_comap_le` — `supp (f.comap g hg) ⊆ supp f`.
* `NFun.supp_prod_le` — `supp (f.prod g) ⊆ supp f ∪ supp g`.
* `NFun.supp_curry_le` — `supp (curry f) ⊆ supp f`.
* `NFun.fresh_apply` — if `a # f` and `a # x`, then `a # f x`.
* `NFun.fresh_const` — `a # (const y) ↔ a # y` (requires `Nonempty X`).
* `NFun.fresh_const_of_fresh` — if `a # y` then `a # const y` (unconditional direction).
* `NFun.fresh_comp` — if `a # g` and `a # f`, then `a # g.comp f`.

### Category and CCC laws

* `NFun.comp_assoc` — composition is associative.
* `NFun.comp_id` / `NFun.id_comp` — identity laws for composition.
* `NFun.comp_const` / `NFun.const_comp` — composition with constant functions.
* `NFun.map_id` — `f.map id isEquivariant_id = f`.
* `NFun.map_comp` — `map` composes covariantly: `(f.map g).map h = f.map (h ∘ g)`.
* `NFun.supp_id` — the support of the identity is empty.
* `NFun.supp_eval` — `supp eval = ∅`.
* `NFun.supp_comp_eq_of_equivariant_surjective` — support equality for surjective equivariant compositions.
* `NFun.const_injective` — `const` is injective (requires `Nonempty X`).
* `NFun.isEquivariant_eval` — the evaluation function is equivariant.
* `NFun.eval_curry` — β law: `eval ((curry f) z, x) = f (z, x)`.
* `NFun.curry_eval` — η law: currying the uncurried evaluation recovers `g`.

## References

* [A. M. Pitts, *Nominal Sets*][Pitts2013], Chapter 2.
-/

namespace Nominal.Set
open Core

open MulAction PermType

variable {α : Type*} [Name α]

/-- `NFun α X Y` is the type of **finitely supported** functions from `X` to `Y`,
wrapping a `PFun α X Y` (conjugation action) together with a proof of finite support. -/
structure NFun (α : Type*) [Name α] (X Y : Type*) [Nominal α X] [Nominal α Y] extends (PFun α X Y) where
  finSupp_toPFun : FinSupported toPFun

namespace NFun

variable {X Y : Type*} [Nominal α X] [Nominal α Y] (f : NFun α X Y)

/-- Coerce an `NFun` to its underlying `PFun`. -/
instance instCoe : Coe (NFun α X Y) (PFun α X Y) := ⟨NFun.toPFun⟩

/-- `NFun α X Y` can be applied as a function via `FunLike`. -/
instance instFunLike : FunLike (NFun α X Y) X Y where
  coe f := f.toPFun
  coe_injective' f g h := by
    have hpf : f.toPFun = g.toPFun := PFun.ext (congrFun h)
    cases f; cases g; congr

/-- Extensionality: two `NFun`s are equal if they agree pointwise. -/
@[ext]
theorem ext {f g : NFun α X Y} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext f g h

/-- Applying `f.toPFun` is the same as applying `f` directly. -/
@[simp] theorem toPFun_apply (f : NFun α X Y) (x : X) : f.toPFun x = f x := rfl

/-- Applying an `NFun` built with `mk` reduces to the underlying `PFun`. -/
@[simp] theorem mk_apply (f : PFun α X Y) (h : FinSupported f) (x : X) : (NFun.mk f h : NFun α X Y) x = f x := rfl

/-- Construct an `NFun` from a bare function and a finite-support proof. -/
def ofFun (f : X → Y) (hf : FinSupported (f : PFun α X Y)) : NFun α X Y := ⟨(f : PFun α X Y), hf⟩

/-- Construct an `NFun` from a `PFun` and an explicit support set. -/
def ofSupports (f : PFun α X Y) (s : Finset α) (hs : supports s f) : NFun α X Y := ⟨f, ⟨s, hs⟩⟩

/-- Applying `ofFun f hf` is the same as applying `f`. -/
@[simp] theorem ofFun_apply (f : X → Y) (hf : FinSupported (f : PFun α X Y)) (x : X) : (ofFun f hf) x = f x := rfl

/-- Applying `ofSupports f s hs` is the same as applying `f`. -/
@[simp] theorem ofSupports_apply (f : PFun α X Y) (s : Finset α) (hs : supports s f) (x : X) :
  (ofSupports f s hs) x = f x := rfl

/-! ### PermType and Nominal instances -/

/-- `NFun α X Y` is a permutation type under the conjugation action `(π • f) x = π • f (π⁻¹ • x)`. -/
instance instPermType : PermType α (NFun α X Y) where
  smul π f :=
    ⟨π • f.toPFun, by
      obtain ⟨s, hs⟩ := f.finSupp_toPFun
      exact ⟨π • s, supports_smul π hs⟩⟩
  one_smul f := by
    ext x
    change (1 : FinitePerm α) • f (1⁻¹ • x) = f x
    simp [one_smul]
  mul_smul π σ f := by
    ext x
    change (π * σ) • f ((π * σ)⁻¹ • x) = π • (σ • f (σ⁻¹ • (π⁻¹ • x)))
    rw [mul_inv_rev, mul_smul, mul_smul]

/-- The underlying `PFun` of `π • f` is `π • f.toPFun`. -/
@[simp] theorem smul_toPFun (π : FinitePerm α) (f : NFun α X Y) : (π • f).toPFun = π • f.toPFun := rfl

/-- The conjugation action applied pointwise: `(π • f) x = π • f (π⁻¹ • x)`. -/
@[simp] theorem smul_apply (π : FinitePerm α) (f : NFun α X Y) (x : X) : (π • f) x = π • f (π⁻¹ • x) := rfl

/-- Applying `π • f` to `π • x` equals `π • (f x)`. -/
@[simp] theorem smul_apply_smul (π : FinitePerm α) (f : NFun α X Y) (x : X) : (π • f) (π • x) = π • f x := by simp

/-- Support for an `NFun` is equivalent to support for its underlying `PFun`. -/
theorem supports_iff_toPFun {s : Finset α} {f : NFun α X Y} : supports s f ↔ supports s (f : PFun α X Y) := by
  constructor
  · intro hs π hπ
    have := congrArg NFun.toPFun (hs π hπ)
    simpa using this
  · intro hs π hπ
    ext x
    have := congrFun (congrArg DFunLike.coe (hs π hπ)) x
    simpa using this

/-- `s` supports `ofSupports f s hs`. -/
theorem ofSupports_supports (f : PFun α X Y) (s : Finset α) (hs : supports s f) : supports s (ofSupports f s hs) :=
  supports_iff_toPFun.mpr hs

/-- `NFun α X Y` is a nominal set: each `f` is finitely supported. -/
instance instNominal : Nominal α (NFun α X Y) where
  __ := instPermType
  finSupp f := by
    obtain ⟨s, hs⟩ := f.finSupp_toPFun
    exact ⟨s, supports_iff_toPFun.mpr hs⟩

/-! ### Categorical combinators -/

section Combinators

variable {X Y Z W : Type*} [Nominal α X] [Nominal α Y] [Nominal α Z] [Nominal α W]

/-- The identity nominal function. -/
def id : NFun α X X := ofSupports PFun.id ∅ supports_pfun_id

/-- The identity nominal function applies as the identity. -/
@[simp] theorem id_apply (x : X) : (NFun.id : NFun α X X) x = x := rfl

/-- The constant nominal function returning `y`. -/
def const (y : Y) : NFun α X Y := ofSupports (PFun.const y) (supp y) (supports_pfun_const y)

/-- The constant nominal function always returns `y`. -/
@[simp] theorem const_apply (y : Y) (x : X) : (NFun.const y : NFun α X Y) x = y := rfl

/-- Composition of nominal functions. -/
def comp (g : NFun α Y Z) (f : NFun α X Y) : NFun α X Z :=
  ofSupports (g.toPFun.comp f.toPFun) (supp g ∪ supp f)
    (supports_pfun_comp (supports_iff_toPFun.mp (supp_supports g))
                        (supports_iff_toPFun.mp (supp_supports f)))

/-- Composition applies by composing the underlying functions. -/
@[simp] theorem comp_apply (g : NFun α Y Z) (f : NFun α X Y) (x : X) : (g.comp f) x = g (f x) := rfl

/-- Composition is associative. -/
theorem comp_assoc (h : NFun α Z W) (g : NFun α Y Z) (f : NFun α X Y) : (h.comp g).comp f = h.comp (g.comp f) := by ext; rfl

/-- `f ∘ id = f`. -/
@[simp] theorem comp_id (f : NFun α X Y) : f.comp NFun.id = f := by ext; rfl

/-- `id ∘ f = f`. -/
@[simp] theorem id_comp (f : NFun α X Y) : NFun.id.comp f = f := by ext; rfl

/-- Composing with a constant function yields a constant function. -/
@[simp] theorem comp_const (g : NFun α Y Z) (y : Y) :
    g.comp (NFun.const y : NFun α X Y) = NFun.const (g y) := by ext; rfl

/-- A constant function absorbs pre-composition. -/
@[simp] theorem const_comp (z : Z) (f : NFun α X Y) :
    (NFun.const z : NFun α Y Z).comp f = NFun.const z := by ext; rfl

/-- Post-compose an `NFun` with an equivariant function. Pitts Lemma 2.12(i): equivariant maps preserve finite support. -/
def map (g : Y → Z) (hg : IsEquivariant α g) (f : NFun α X Y) : NFun α X Z :=
  ⟨PFun.funComp g f.toPFun, by
    obtain ⟨s, hs⟩ := f.finSupp_toPFun
    exact ⟨s, by
      rw [supports_pfun_iff] at hs ⊢
      intro π hπ x
      simp [hg.map_smul π, hs π hπ x]⟩⟩

/-- Applying `map g hg f` reduces to `g (f x)`. -/
@[simp] theorem map_apply (g : Y → Z) (hg : IsEquivariant α g) (f : NFun α X Y) (x : X) : (f.map g hg) x = g (f x) := rfl

/-- Pre-compose an `NFun` with an equivariant function. -/
def comap (g : Z → X) (hg : IsEquivariant α g) (f : NFun α X Y) : NFun α Z Y :=
  ⟨PFun.compFun f.toPFun g, by
    obtain ⟨s, hs⟩ := f.finSupp_toPFun
    exact ⟨s, by
      rw [supports_pfun_iff] at hs ⊢
      intro π hπ x
      simp [hg.map_smul π, hs π hπ (g x)]⟩⟩

/-- Applying `comap g hg f` reduces to `f (g x)`. -/
@[simp] theorem comap_apply (g : Z → X) (hg : IsEquivariant α g) (f : NFun α X Y) (x : Z) :
    (f.comap g hg) x = f (g x) := rfl

/-- Pair two nominal functions into one targeting a product. Thm 2.19: Nom is cartesian closed, so products of morphisms exist. -/
def prod (f : NFun α X Y) (g : NFun α X Z) : NFun α X (Y × Z) :=
  ⟨PFun.mk (fun x ↦ (f x, g x)), by
    obtain ⟨s, hs⟩ := f.finSupp_toPFun
    obtain ⟨t, ht⟩ := g.finSupp_toPFun
    exact ⟨s ∪ t, by
      rw [supports_pfun_iff] at hs ht ⊢
      intro π hπ x
      exact Prod.ext
        (hs π (fun a ha ↦ hπ (Finset.mem_union_left _ ha)) x)
        (ht π (fun a ha ↦ hπ (Finset.mem_union_right _ ha)) x)⟩⟩

/-- Applying `prod f g` gives a pair. -/
@[simp] theorem prod_apply (f : NFun α X Y) (g : NFun α X Z) (x : X) : (f.prod g) x = (f x, g x) := rfl

/-- The evaluation map `(f, x) ↦ f x` as a nominal function `NFun α X Y × X → Y`. Pitts Eq (2.13): app is equivariant. -/
def eval : NFun α (NFun α X Y × X) Y :=
  ofSupports (PFun.mk (fun p ↦ p.1 p.2)) ∅ (by
    rw [supports_pfun_iff]
    intro π _ ⟨f, x⟩
    simp)

/-- The evaluation map applies `f` to `x`. -/
@[simp] theorem eval_apply (p : NFun α X Y × X) : (eval : NFun α (NFun α X Y × X) Y) p = p.1 p.2 := rfl

/-- Auxiliary: given `f : NFun α (Z × X) Y` and `z : Z`, build the partial application as an `NFun`. -/
private def curryAux {Z : Type*} [Nominal α Z]
    (f : NFun α (Z × X) Y) (z : Z) : NFun α X Y :=
  ⟨PFun.mk (fun x ↦ f (z, x)),
    ⟨supp z ∪ supp f, by
      rw [supports_pfun_iff]
      intro π hπ x
      have hπz : π • z = z := supp_supports z π (fun a ha ↦ hπ (Finset.mem_union_left _ ha))
      have hπf : π • f = f := supp_supports f π (fun a ha ↦ hπ (Finset.mem_union_right _ ha))
      calc f (z, π • x)
        _ = f (π • z, π • x) := by rw [hπz]
        _ = f (π • (z, x)) := by rw [PermType.prod_smul]
        _ = (π • f) (π • (z, x)) := by rw [hπf]
        _ = π • f (z, x) := smul_apply_smul π f (z, x)⟩⟩

/-- Curry an `NFun` of type `Z × X → Y` into `Z → NFun α X Y`. Pitts Eq (2.14) / Thm 2.19 (cartesian closure of Nom). -/
def curry {Z : Type*} [Nominal α Z] (f : NFun α (Z × X) Y) : NFun α Z (NFun α X Y) :=
  ⟨PFun.mk (fun z ↦ curryAux f z),
    ⟨supp f, by
      rw [supports_pfun_iff]
      intro π hπ z
      have hπf : π • f = f := supp_supports f π hπ
      ext x
      change f (π • z, x) = π • f (z, π⁻¹ • x)
      calc f (π • z, x)
        _ = f (π • z, π • (π⁻¹ • x)) := by rw [PermType.smul_inv_smul]
        _ = f (π • (z, π⁻¹ • x)) := by rw [PermType.prod_smul]
        _ = (π • f) (π • (z, π⁻¹ • x)) := by rw [hπf]
        _ = π • f (z, π⁻¹ • x) := smul_apply_smul π f (z, π⁻¹ • x)⟩⟩

/-- Applying `curry f` to `z` and then `x` equals `f (z, x)`. -/
@[simp] theorem curry_apply_apply {Z : Type*} [Nominal α Z] (f : NFun α (Z × X) Y) (z : Z) (x : X) :
    (NFun.curry f) z x = f (z, x) := rfl

/-- The action sends a constant function to the constant function at the acted value. -/
@[simp] theorem smul_const (π : FinitePerm α) (y : Y) : π • (NFun.const y : NFun α X Y) = NFun.const (π • y) := by ext; simp

/-- The permutation action distributes over composition. -/
@[simp] theorem smul_comp (π : FinitePerm α) (g : NFun α Y Z) (f : NFun α X Y) : π • (g.comp f) = (π • g).comp (π • f) := by ext; simp

/-- The permutation action distributes over post-composition with an equivariant function. -/
@[simp] theorem smul_map (π : FinitePerm α) (g : Y → Z) (hg : IsEquivariant α g)
    (f : NFun α X Y) : π • (f.map g hg) = (π • f).map g hg := by
  ext x; simp [hg.map_smul]

/-- The permutation action distributes over pre-composition with an equivariant function. -/
@[simp] theorem smul_comap (π : FinitePerm α) (g : Z → X) (hg : IsEquivariant α g)
    (f : NFun α X Y) : π • (f.comap g hg) = (π • f).comap g hg := by
  ext x; simp [hg.map_smul]

/-- The permutation action distributes over pairing. -/
@[simp] theorem smul_prod (π : FinitePerm α) (f : NFun α X Y) (g : NFun α X Z) : π • (f.prod g) = (π • f).prod (π • g) := by
  ext x
  · simp
  · simp

/-- Mapping by the identity is the identity. -/
@[simp] theorem map_id (f : NFun α X Y) : f.map _root_.id isEquivariant_id = f := by ext; rfl

/-- Mapping composes covariantly. -/
theorem map_comp (g : Y → Z) (hg : IsEquivariant α g) (h : Z → W) (hh : IsEquivariant α h)
    (f : NFun α X Y) : (f.map g hg).map h hh = f.map (h ∘ g) (hh.comp hg) := by ext; rfl

/-- The support of the identity is empty. -/
@[simp] theorem supp_id : supp (NFun.id : NFun α X X) = ∅ :=
  supp_eq_empty_iff.mpr (fun _ ↦ by ext; simp)

/-- The evaluation map is equivariant, hence has empty support. Pitts Eq (2.13). -/
@[simp] theorem supp_eval : supp (eval : NFun α (NFun α X Y × X) Y) = ∅ :=
  supp_eq_empty_iff.mpr (fun _ ↦ by ext; simp)

/-- Post-composing with an equivariant function doesn't enlarge support. Pitts Lemma 2.12(i). -/
theorem supp_map_le (g : Y → Z) (hg : IsEquivariant α g) (f : NFun α X Y) : supp (f.map g hg) ⊆ supp f := by
  intro a ha
  rw [mem_supp] at ha ⊢
  intro s hs
  apply ha s
  intro π hπ
  have hf := hs π hπ
  calc π • (f.map g hg)
    _ = (π • f).map g hg := smul_map π g hg f
    _ = f.map g hg := by rw [hf]

/-- Pre-composing with an equivariant function doesn't enlarge support. Pitts Lemma 2.12(i). -/
theorem supp_comap_le (g : Z → X) (hg : IsEquivariant α g) (f : NFun α X Y) : supp (f.comap g hg) ⊆ supp f := by
  intro a ha
  rw [mem_supp] at ha ⊢
  intro s hs
  apply ha s
  intro π hπ
  have hf := hs π hπ
  calc π • (f.comap g hg)
    _ = (π • f).comap g hg := smul_comap π g hg f
    _ = f.comap g hg := by rw [hf]

/-- The support of a paired function is bounded by the union of supports. -/
theorem supp_prod_le (f : NFun α X Y) (g : NFun α X Z) : supp (f.prod g) ⊆ supp f ∪ supp g :=
  supp_le (by
    intro π hπ
    rw [smul_prod]
    have hf := supp_supports f π (fun a ha ↦ hπ (Finset.mem_union_left _ ha))
    have hg := supp_supports g π (fun a ha ↦ hπ (Finset.mem_union_right _ ha))
    exact congrArg₂ NFun.prod hf hg)

/-- The support of a curried function is bounded by the support of the original. Pitts Eq (2.14): curry f is supported by supp f. -/
theorem supp_curry_le {Z : Type*} [Nominal α Z] (f : NFun α (Z × X) Y) : supp (NFun.curry f) ⊆ supp f :=
  supp_le (supports_iff_toPFun.mpr (by
    rw [supports_pfun_iff]
    intro π hπ z
    have hπf : π • f = f := supp_supports f π hπ
    ext x
    change f (π • z, x) = π • f (z, π⁻¹ • x)
    calc f (π • z, x)
      _ = f (π • z, π • (π⁻¹ • x)) := by rw [PermType.smul_inv_smul]
      _ = f (π • (z, π⁻¹ • x)) := by rw [PermType.prod_smul]
      _ = (π • f) (π • (z, π⁻¹ • x)) := by rw [hπf]
      _ = π • f (z, π⁻¹ • x) := smul_apply_smul π f (z, π⁻¹ • x)))

end Combinators

/-! ### Key theorems -/

section SuppTheorems

variable {X Y : Type*} [Nominal α X] [Nominal α Y]

/-- `supp f = ∅` if and only if `f` is equivariant: `f (π • x) = π • f x` for all `π, x`. -/
theorem supp_eq_empty_iff' {f : NFun α X Y} : supp f = ∅ ↔ ∀ (π : FinitePerm α) (x : X), f (π • x) = π • f x := by
  rw [supp_eq_empty_iff]
  constructor
  · intro hfix π x
    have := congrArg (fun g : NFun α X Y ↦ g (π • x)) (hfix π)
    simpa using this.symm
  · intro heq π
    ext x
    have := heq π (π⁻¹ • x)
    simpa [PermType.smul_inv_smul] using this.symm

/-- `supp f = ∅` if and only if `f` is equivariant in the sense of `IsEquivariant`. -/
theorem supp_eq_empty_iff_isEquivariant {f : NFun α X Y} : supp f = ∅ ↔ IsEquivariant α (f : X → Y) :=
  supp_eq_empty_iff'.trans ⟨fun h ↦ ⟨h⟩, fun h ↦ h.map_smul⟩

/-- If `s` supports `f` and `t` supports `x`, then `s ∪ t` supports `f x`. -/
theorem supports_apply {s t : Finset α} (f : NFun α X Y) (x : X) (hs : supports s f) (ht : supports t x) :
  supports (s ∪ t) (f x) := by
  intro π hπ
  have hπs : ∀ ⦃a⦄, a ∈ s → π • a = a := fun a ha ↦
    hπ (Finset.mem_coe.mpr (Finset.mem_union_left _ (Finset.mem_coe.mp ha)))
  have hπt : ∀ ⦃a⦄, a ∈ t → π • a = a := fun a ha ↦
    hπ (Finset.mem_coe.mpr (Finset.mem_union_right _ (Finset.mem_coe.mp ha)))
  have hx : π • x = x := ht π hπt
  have hsPFun : supports s f.toPFun := supports_iff_toPFun.mp hs
  have hcomm := (supports_pfun_iff.mp hsPFun) π (fun ⦃a⦄ ha ↦ by
    simp only [← PermType.atoms_smul]; exact hπs (Finset.mem_coe.mpr ha)) x
  change π • f.toPFun x = f.toPFun x
  rw [← hcomm, hx]

/-- The support of `f x` is contained in `supp f ∪ supp x`. -/
theorem supp_apply_le (f : NFun α X Y) (x : X) : supp (f x) ⊆ supp f ∪ supp x :=
  supp_le (supports_apply f x (supp_supports f) (supp_supports x))

/-- If `a` is fresh for both `f` and `x`, then `a` is fresh for `f x`. -/
theorem fresh_apply {a : α} {f : NFun α X Y} {x : X} (hf : a # f) (hx : a # x) : a # f x := by
  rw [fresh_atom_left] at hf hx ⊢
  intro h
  have := supp_apply_le f x h
  rw [Finset.mem_union] at this
  exact this.elim hf hx

/-- The support of a constant nominal function equals the support of its value (assuming `X` is nonempty). -/
@[simp] theorem supp_const [Nonempty X] (y : Y) : supp (NFun.const y : NFun α X Y) = supp y := by
  apply Finset.Subset.antisymm
  · exact supp_le (supports_iff_toPFun.mpr (supports_pfun_const y))
  · intro a ha
    rw [mem_supp] at ha ⊢
    intro s hs
    exact ha s (by
      intro π hπ
      have h₂ : π • (NFun.const y : NFun α X Y) = NFun.const y := hs π hπ
      rw [smul_const] at h₂
      have := congrFun (congrArg DFunLike.coe h₂) (Classical.arbitrary X)
      simpa using this)

/-- The support of a constant nominal function is contained in the support of its value. -/
theorem supp_const_le (y : Y) : supp (NFun.const y : NFun α X Y) ⊆ supp y :=
  supp_le (supports_iff_toPFun.mpr (supports_pfun_const y))

/-- Freshness for a constant nominal function reduces to freshness for its value (assuming `X` is nonempty). -/
@[simp] theorem fresh_const [Nonempty X] {a : α} {y : Y} : a # (NFun.const y : NFun α X Y) ↔ a # y := by
  simp [supp_const]

/-- If `a # y`, then `a` is fresh for the constant nominal function at `y`. -/
theorem fresh_const_of_fresh {a : α} {y : Y} (h : a # y) : a # (NFun.const y : NFun α X Y) :=
  fresh_of_supp_subset (supp_const_le y) h

/-- The support of a composition is contained in the union of supports. -/
theorem supp_comp_le {Z : Type*} [Nominal α Z] (g : NFun α Y Z) (f : NFun α X Y) : supp (g.comp f) ⊆ supp g ∪ supp f :=
  supp_le (supports_iff_toPFun.mpr
    (supports_pfun_comp (supports_iff_toPFun.mp (supp_supports g))
                        (supports_iff_toPFun.mp (supp_supports f))))

/-- If `f` is equivariant and surjective, composing with it preserves support.
    Pitts Lemma 2.12: equivariant surjections reflect support. -/
theorem supp_comp_eq_of_equivariant_surjective {Z : Type*} [Nominal α Z] (g : NFun α Y Z) (f : NFun α X Y)
    (hf_equiv : IsEquivariant α (f : X → Y)) (hf_surj : Function.Surjective f) : supp (g.comp f) = supp g := by
  apply Finset.Subset.antisymm
  · have hf_eq := supp_eq_empty_iff_isEquivariant.mpr hf_equiv
    calc supp (g.comp f) ⊆ supp g ∪ supp f := supp_comp_le g f
      _ = supp g ∪ ∅ := by rw [hf_eq]
      _ = supp g := Finset.union_empty _
  · intro a ha
    rw [mem_supp] at ha ⊢
    intro s hs
    apply ha s
    intro π hπ
    ext x
    obtain ⟨x₀, hx₀⟩ := hf_surj x
    have hcomp := congrFun (congrArg DFunLike.coe (hs π hπ)) x₀
    simp only [smul_apply] at hcomp
    calc (π • g) x = π • g (π⁻¹ • x) := rfl
      _ = π • g (π⁻¹ • (f x₀)) := by rw [hx₀]
      _ = π • g (f (π⁻¹ • x₀)) := by rw [hf_equiv.map_smul]
      _ = g (f x₀) := hcomp
      _ = g x := by rw [hx₀]

/-- If `a` is fresh for both `g` and `f`, then `a` is fresh for their composition.
    API completeness: freshness analogue of `supp_comp_le`. -/
theorem fresh_comp {Z : Type*} [Nominal α Z] {a : α} {g : NFun α Y Z} {f : NFun α X Y}
    (hg : a # g) (hf : a # f) : a # g.comp f := by
  rw [fresh_atom_left] at hg hf ⊢
  intro h
  have := supp_comp_le g f h
  rw [Finset.mem_union] at this
  exact this.elim hg hf

/-- The constant function constructor is injective (assuming the domain is nonempty).
    API completeness: injectivity of `const`. -/
theorem const_injective [Nonempty X] {y₁ y₂ : Y} (h : (NFun.const y₁ : NFun α X Y) = NFun.const y₂) : y₁ = y₂ := by
  have := congrFun (congrArg DFunLike.coe h) (Classical.arbitrary X)
  simpa using this

end SuppTheorems

/-! ### Equivariance and CCC laws -/

section CCCLaws

variable {X Y Z : Type*} [Nominal α X] [Nominal α Y] [Nominal α Z]

/-- The evaluation function is equivariant.
    Pitts Eq (2.13), predicate form. -/
theorem isEquivariant_eval : IsEquivariant α (fun p : NFun α X Y × X ↦ p.1 p.2) :=
  ⟨fun π ⟨f, x⟩ ↦ by simp⟩

/-- The β law of the cartesian closed structure: evaluating a curried function
    recovers the original. Pitts Thm 2.19 (CCC adjunction). -/
@[simp] theorem eval_curry (f : NFun α (Z × X) Y) (z : Z) (x : X) :
    (eval : NFun α (NFun α X Y × X) Y) ((NFun.curry f) z, x) = f (z, x) := rfl

/-- The η law: currying the evaluation of `g` recovers `g`.
    Pitts Thm 2.19 (CCC adjunction, uniqueness direction). -/
theorem curry_eval (g : NFun α Z (NFun α X Y)) :
    NFun.curry (NFun.mk (PFun.mk (fun p : Z × X ↦ g p.1 p.2))
      ⟨supp g, by
        rw [supports_pfun_iff]
        intro π hπ ⟨z, x⟩
        have hg : π • g = g := supp_supports g π hπ
        calc g (π • z) (π • x)
          _ = (π • g) (π • z) (π • x) := by rw [hg]
          _ = (π • (g z (π⁻¹ • (π • x)))) := by simp
          _ = π • g z x := by simp⟩) = g := by
  ext z x; rfl

end CCCLaws

end NFun

end Nominal.Set
