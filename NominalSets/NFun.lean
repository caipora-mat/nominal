import NominalSets.Nominal
import NominalSets.Freshness

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
* `NFun.id_apply` / `NFun.const_apply` / `NFun.comp_apply` — reduction lemmas for categorical combinators.

### Permutation action

* `NFun.smul_toPFun` — `(π • f).toPFun = π • f.toPFun`.
* `NFun.smul_apply` — `(π • f) x = π • f (π⁻¹ • x)`.
* `NFun.smul_apply_smul` — `(π • f) (π • x) = π • f x`.
* `NFun.smul_const` — `π • const y = const (π • y)`.

### Support and freshness

* `NFun.supports_iff_toPFun` — support for an `NFun` is equivalent to support for its underlying `PFun`.
* `NFun.supp_eq_empty_iff'` — `supp f = ∅` iff `f (π • x) = π • f x` for all `π, x`.
* `NFun.supp_eq_empty_iff_isEquivariant` — `supp f = ∅` iff `IsEquivariant f`.
* `NFun.supports_apply` — if `s` supports `f` and `t` supports `x`, then `s ∪ t` supports `f x`.
* `NFun.supp_apply_le` — `supp (f x) ⊆ supp f ∪ supp x`.
* `NFun.fresh_apply` — if `a # f` and `a # x`, then `a # f x`.

### Category laws

* `NFun.comp_assoc` — composition is associative.
* `NFun.comp_id` / `NFun.id_comp` — identity laws for composition.
* `NFun.supp_id` — the support of the identity is empty.

## References

* [A. M. Pitts, *Nominal Sets*][Pitts2013], Chapter 2.
-/

namespace NominalSets

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
theorem comp_assoc (h : NFun α Z W) (g : NFun α Y Z) (f : NFun α X Y) :
    (h.comp g).comp f = h.comp (g.comp f) := by ext; rfl

/-- `f ∘ id = f`. -/
@[simp] theorem comp_id (f : NFun α X Y) : f.comp NFun.id = f := by ext; rfl

/-- `id ∘ f = f`. -/
@[simp] theorem id_comp (f : NFun α X Y) : NFun.id.comp f = f := by ext; rfl

/-- The action sends a constant function to the constant function at the acted value. -/
@[simp] theorem smul_const (π : FinitePerm α) (y : Y) :
    π • (NFun.const y : NFun α X Y) = NFun.const (π • y) := by ext; simp

/-- The support of the identity is empty. -/
@[simp] theorem supp_id : supp (NFun.id : NFun α X X) = ∅ :=
  supp_eq_empty_iff.mpr (fun _ ↦ by ext; simp)

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
theorem supp_eq_empty_iff_isEquivariant {f : NFun α X Y} : supp f = ∅ ↔ IsEquivariant (α := α) (f : X → Y) :=
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

end SuppTheorems

end NFun

end NominalSets
