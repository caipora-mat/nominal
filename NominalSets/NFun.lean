import NominalSets.Nominal
import NominalSets.Freshness

/-!
# Finitely Supported Functions

Not every function between nominal sets is finitely supported under the
action `(π • f) x = π • f (π⁻¹ • x)`. The type `NFun α X Y` ("nominal function")
wraps a `PFun α X Y` together with a proof of finite support, yielding a nominal set
of finitely supported functions.

## Main definitions

* `NFun α X Y` — the type of finitely supported functions from `X` to `Y`.
* `NFun.ofFun` — construct an `NFun` from a bare function and a finite-support proof.
* `NFun.ofSupports` — construct an `NFun` from a function and an explicit support set.

## Instances

* `NFun.instFunLike` — `NFun α X Y` can be applied as functions via `FunLike`.
* `NFun.instPermType` — conjugation action on `NFun α X Y`.
* `NFun.instNominal` — `NFun α X Y` forms a nominal set.

## Main results

* `NFun.supports_iff_toPFun` — support for `NFun` is equivalent to support for
  the underlying `PFun`.
* `NFun.supp_eq_empty_iff` — `supp f = ∅` iff `f` is equivariant.
* `NFun.supports_apply` — if `s` supports `f` and `t` supports `x`, then `s ∪ t`
  supports `f x`.
* `NFun.supp_apply_le` — `supp (f x) ⊆ supp f ∪ supp x`.

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

instance instCoe : Coe (NFun α X Y) (PFun α X Y) := ⟨NFun.toPFun⟩

instance instFunLike : FunLike (NFun α X Y) X Y where
  coe f := f.toPFun
  coe_injective' f g h := by
    have hpf : f.toPFun = g.toPFun := PFun.ext (congrFun h)
    cases f; cases g; congr

@[ext]
theorem ext {f g : NFun α X Y} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext f g h

@[simp] theorem toPFun_apply (f : NFun α X Y) (x : X) : f.toPFun x = f x := rfl

@[simp] theorem mk_apply (f : PFun α X Y) (h : FinSupported f) (x : X) :
    (NFun.mk f h : NFun α X Y) x = f x := rfl

/-- Construct an `NFun` from a bare function and a finite-support proof. -/
def ofFun (f : X → Y) (hf : FinSupported (f : PFun α X Y)) : NFun α X Y :=
  ⟨(f : PFun α X Y), hf⟩

/-- Construct an `NFun` from a `PFun` and an explicit support set. -/
def ofSupports (f : PFun α X Y) (s : Finset α) (hs : supports s f) : NFun α X Y :=
  ⟨f, ⟨s, hs⟩⟩

/-! ### PermType and Nominal instances -/

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

@[simp] theorem smul_toPFun (π : FinitePerm α) (f : NFun α X Y) :
    (π • f).toPFun = π • f.toPFun := rfl

@[simp] theorem smul_apply (π : FinitePerm α) (f : NFun α X Y) (x : X) :
    (π • f) x = π • f (π⁻¹ • x) := rfl

@[simp] theorem smul_apply_smul (π : FinitePerm α) (f : NFun α X Y) (x : X) :
    (π • f) (π • x) = π • f x := by simp

/-- Support for an `NFun` is equivalent to support for its underlying `PFun`. -/
theorem supports_iff_toPFun {s : Finset α} {f : NFun α X Y} :
    supports s f ↔ supports s (f : PFun α X Y) := by
  constructor
  · intro hs π hπ
    have := congrArg NFun.toPFun (hs π hπ)
    simpa using this
  · intro hs π hπ
    ext x
    have := congrFun (congrArg DFunLike.coe (hs π hπ)) x
    simpa using this

instance instNominal : Nominal α (NFun α X Y) where
  __ := instPermType
  finSupp f := by
    obtain ⟨s, hs⟩ := f.finSupp_toPFun
    exact ⟨s, supports_iff_toPFun.mpr hs⟩

/-! ### Key theorems -/

section SuppTheorems

variable {X Y : Type*} [Nominal α X] [Nominal α Y]

/-- `supp f = ∅` if and only if `f` is equivariant: `f (π • x) = π • f x` for all `π, x`. -/
theorem supp_eq_empty_iff' {f : NFun α X Y} :
    supp f = ∅ ↔ ∀ (π : FinitePerm α) (x : X), f (π • x) = π • f x := by
  rw [supp_eq_empty_iff]
  constructor
  · intro hfix π x
    have := congrArg (fun g : NFun α X Y ↦ g (π • x)) (hfix π)
    simpa using this.symm
  · intro heq π
    ext x
    have := heq π (π⁻¹ • x)
    simpa [PermType.smul_inv_smul] using this.symm

/-- If `s` supports `f` and `t` supports `x`, then `s ∪ t` supports `f x`. -/
theorem supports_apply {s t : Finset α} (f : NFun α X Y) (x : X)
    (hs : supports s f) (ht : supports t x) : supports (s ∪ t) (f x) := by
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
  supp_le _ (supports_apply f x (supp_supports f) (supp_supports x))

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
