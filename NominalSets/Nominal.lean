import NominalSets.Support
import NominalSets.PFun
import Mathlib.GroupTheory.GroupAction.Support
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Empty
import Mathlib.Data.Finset.Image
import Mathlib.Logic.Equiv.Basic

/-!
# Nominal Sets

A **nominal set** is a permutation type in which every element has **finite support**:
there exists a finite set of atoms that supports it in the sense of `MulAction.Supports`.

This file defines the `Nominal` typeclass, the least-support function `supp`, and the
basic nominal instances. Support machinery (`supports`, `FinSupported`, `supports_iff_swap`,
`supports_inter`, `supports_smul`) is imported from `NominalSets.Support`.

## Main definitions

* `Nominal α X` — typeclass: a `PermType α X` in which every element is finitely supported.
* `supp x` — the least finite support of `x`, as a `Finset α` (intersection of all finite supports).

## Instances

* `Nominal.instAtoms` — atoms `α` form a nominal set (atom `a` is supported by `{a}`).
* `Nominal.instProd` — products of nominal sets are nominal (support is the union of supports).
* `Nominal.instOption` — `Option X` is nominal (`none` has empty support; `some x` inherits the support of `x`).
* `Nominal.instUnit` — `Unit` is a nominal set (the unique element has empty support; not a global `instance` because `α` cannot be inferred from `Unit`).
* `Nominal.instFinsetNominal` — finite sets of atoms form a nominal set (each `s` is supported by itself).
* `Nominal.instConjNominal` — finite permutations form a nominal set under the conjugation action (each `σ` is supported by its moved-point set `movedFinset σ`).
* `Nominal.instNominalSum` — sums of nominal sets are nominal (each injection preserves the support of its argument).

## Main results

### Support membership and characterisation

* `mem_supp` — `a ∈ supp x ↔ ∀ s, supports s x → a ∈ s`.
* `not_mem_supp` — `a ∉ supp x ↔ ∃ s, supports s x ∧ a ∉ s`.
* `coe_supp` — `(supp x : Set α) = suppSet x` (the support as a set equals the intersection of all finite supports).
* `supp_supports` — `supp x` is itself a support for `x`.
* `supp_le` — `supp x` is the least finite support: every finite support `s` satisfies `supp x ⊆ s`.
* `supp_le_iff` — `supp x ⊆ s ↔ supports s x` (biconditional form of `supp_le`).
* `supp_eq_empty_iff` — `supp x = ∅ ↔ ∀ π, π • x = x` (globally fixed elements have empty support).

### Equivariance and monotonicity

* `supp_equivariant` — `π • supp x = supp (π • x)`.
* `supp_smul_eq` — `supp (π • x) = π • supp x` (symmetric form).
* `supp_map_le` — if `f` is equivariant then `supp (f x) ⊆ supp x`.

### Support computations

* `Nominal.finset_supports_self` — every finite set of atoms `s : Finset α` supports itself.
* `Nominal.finitePerm_supports_self` — every finite permutation `σ` is supported by its moved-point set `movedFinset σ`.
* `supp_atom` — `supp a = {a}` for any atom `a : α`.
* `supp_finset` — `supp s = s` for any finite set of atoms `s : Finset α`.
* `supp_finitePerm` — `supp σ = movedFinset σ` for any finite permutation `σ` (Pitts, Prop 2.14).
* `supp_prod` — `supp (x, y) = supp x ∪ supp y`.
* `supp_none` — `supp none = ∅`.
* `supp_some` — `supp (some x) = supp x`.
* `supp_unit` — `supp u = ∅` for `u : Unit` (requires `letI := Nominal.instUnit`).
* `supp_inl` — `supp (Sum.inl x) = supp x`.
* `supp_inr` — `supp (Sum.inr y) = supp y`.

### Nominal functions (`PFun`)

* `supports_pfun_iff` — `supports s f ↔ ∀ π fixing s, ∀ x, f (π • x) = π • f x`.

## References

* [A. M. Pitts, *Nominal Sets*][Pitts2013], Chapter 2.
-/

namespace NominalSets

/-- A **nominal set** is a permutation type in which every element is finitely supported.

`α` is an `outParam` (as in `PermType`) so that Lean can infer the atom type from `X` alone.
This lets callers write `supp x` rather than `supp  x`. The trade-off is that each type `X` may have at most one `Nominal` instance (one atom type `α`) -/
class Nominal (α : outParam Type*) [Name α] (X : Type*) extends PermType α X where
  finSupp : ∀ x : X, FinSupported  x

namespace Nominal

variable {α : Type*} [Name α]

variable {X Y : Type*}

/-- Atoms form a nominal set: atom `a` is supported by the singleton `{a}`. -/
instance instAtoms : Nominal α α where
  __ := PermType.instAtoms
  finSupp a := ⟨{a}, fun π h ↦ by
    simp only [PermType.atoms_smul]
    apply h
    simp⟩

/-- Products of nominal sets are nominal: take the union of the respective supports. -/
instance instProd [Nominal α X] [Nominal α Y] : Nominal α (X × Y) where
  __ := PermType.instProd
  finSupp := by
    rintro ⟨x, y⟩
    obtain ⟨sx, hsx⟩ := Nominal.finSupp x
    obtain ⟨sy, hsy⟩ := Nominal.finSupp y
    exact ⟨sx ∪ sy, supports_prod hsx hsy⟩

/-- `Unit` is a nominal set: the unique element is supported by the empty set.

This is a `def` rather than a global `instance` because `α` cannot be inferred from `Unit` alone (same reason as `PermType.instUnit`). -/
def instUnit : Nominal α Unit where
  __ := PermType.instUnit
  finSupp _ := ⟨∅, fun _ _ ↦ rfl⟩

/-- `Option X` is a nominal set: `none` is supported by `∅`, and `some x` is supported by the support of `x`. -/
instance instOption [Nominal α X] : Nominal α (Option X) where
  __ := PermType.instOption
  finSupp o := by
    cases o with
    | none => exact ⟨∅, fun _ _ ↦ rfl⟩
    | some x =>
      obtain ⟨s, hs⟩ := Nominal.finSupp x
      exact ⟨s, fun π hπ ↦ by simp [hs π hπ]⟩

/-- Every finite set of atoms `s` is supported by itself: any permutation fixing `s` fixes `s` as a set element. -/
theorem finset_supports_self (s : Finset α) : supports s s := by
  intro π hfix
  ext a
  simp only [PermType.finset_smul, Finset.mem_image]
  constructor
  · rintro ⟨b, hb, rfl⟩
    have : (π : α → α) b = b := by
      simpa [PermType.atoms_smul] using hfix (Finset.mem_coe.mpr hb)
    rwa [this]
  · intro ha
    exact ⟨a, ha, by simpa [PermType.atoms_smul] using hfix (Finset.mem_coe.mpr ha)⟩

/-- Finite sets of atoms form a nominal set: every `s : Finset α` is supported by itself. -/
instance instFinsetNominal : Nominal α (Finset α) where
  __ := PermType.instFinset
  finSupp s := ⟨s, finset_supports_self s⟩

/-- Every finite permutation `σ` is supported by its moved-point set `movedFinset σ`: any swap of two fixed points of `σ` conjugates trivially. -/
theorem finitePerm_supports_self (σ : FinitePerm α) : supports (PermType.movedFinset σ) σ := by
  rw [supports_iff_swap]
  intro a b ha hb
  rw [PermType.conj_smul, swap_inv]
  exact swap_conj_eq_of_fixed (PermType.fixed_of_not_mem_movedFinset ha)
                               (PermType.fixed_of_not_mem_movedFinset hb)

/-- Finite permutations form a nominal set: each `σ` is supported by `movedFinset σ`. -/
instance instConjNominal : Nominal α (FinitePerm α) where
  __ := PermType.instConjFinitePerm
  finSupp σ := ⟨PermType.movedFinset σ, finitePerm_supports_self σ⟩

/-! ### Sum -/

/-- Sums of nominal sets are nominal: each injection preserves the support of its argument. -/
instance instNominalSum {X Y : Type*} [Nominal α X] [Nominal α Y] :
    Nominal α (X ⊕ Y) where
  __ := PermType.instPermTypeSum
  finSupp s := by
    cases s with
    | inl x =>
      obtain ⟨sx, hsx⟩ := Nominal.finSupp x
      exact ⟨sx, fun π hπ ↦ by simp [PermType.sum_smul_inl, hsx π hπ]⟩
    | inr y =>
      obtain ⟨sy, hsy⟩ := Nominal.finSupp y
      exact ⟨sy, fun π hπ ↦ by simp [PermType.sum_smul_inr, hsy π hπ]⟩

end Nominal

/-! ## The least support: `supp x`

For any nominal set `X` and element `x : X`, the intersection of all finite supports of `x`
is itself a finite support of `x`, and it is contained in every other finite support.
This is the **least support** `supp x`, also written `supp(x)` in the literature.
-/

section Supp

open MulAction

variable {α : Type*} [Name α] {X : Type*} [Nominal α X]

/-- The **support** `suppSet x` is the intersection of all finite supports of `x`. This is a `Set α`; use `supp x` for the corresponding `Finset α`. -/
private def suppSet (x : X) : Set α := ⋂ (s : Finset α) (_ : supports s x), (s : Set α)

/-- Membership in `suppSet x`: an atom belongs iff it belongs to every finite support of `x`. -/
private theorem mem_suppSet {x : X} {a : α} : a ∈ suppSet x ↔ ∀ (s : Finset α), supports s x → a ∈ s := by
  simp only [suppSet, Set.mem_iInter, Finset.mem_coe]

/-- `suppSet x` is contained in every finite support of `x`. -/
private theorem suppSet_subset {x : X} (s : Finset α) (hs : supports s x) : suppSet x ⊆ (s : Set α) := by
  intro a ha
  exact Finset.mem_coe.mpr ((mem_suppSet.mp ha) s hs)

/-- `suppSet x` is a finite set (it is a subset of any one finite support). -/
private theorem suppSet_finite (x : X) : (suppSet x).Finite := by
  have ⟨s, hs⟩ : FinSupported x := @Nominal.finSupp α _ X _ x
  exact Set.Finite.subset (Finset.finite_toSet s) (suppSet_subset s hs)

/-- The **least support** of `x`, as a `Finset α`. Equal to the intersection of all finite supports. -/
noncomputable def supp (x : X) : Finset α :=
  (suppSet_finite x).toFinset

/-- Membership in `supp x`: an atom belongs iff it belongs to every finite support of `x`. -/
@[simp]
theorem mem_supp {x : X} {a : α} : a ∈ supp x ↔ ∀ (s : Finset α), supports s x → a ∈ s := by
  simp [supp, Set.Finite.mem_toFinset, mem_suppSet]

/-- Negated membership in `supp x`: an atom is outside the support iff some finite support omits it. -/
theorem not_mem_supp {x : X} {a : α} : a ∉ supp x ↔ ∃ s, supports s x ∧ a ∉ s := by
  constructor
  · intro h
    rw [mem_supp] at h
    push_neg at h
    exact h
  · rintro ⟨s, hs, ha⟩ hmem
    exact ha (mem_supp.mp hmem s hs)

/-- `supp x`, viewed as a set, equals `suppSet x`. -/
@[simp]
theorem coe_supp (x : X) : (supp x : Set α) = suppSet x := Set.Finite.coe_toFinset _

/-- `supp x` supports `x`: every permutation fixing `supp x` also fixes `x`. -/
theorem supp_supports (x : X) : supports (supp x) x := by
  rw [supports_iff_swap]
  intro a b ha hb
  -- a ∉ supp x means ∃ s₁ with supports s₁ x and a ∉ s₁
  rw [mem_supp] at ha hb
  push_neg at ha hb
  obtain ⟨s₁, hs₁, ha₁⟩ := ha
  obtain ⟨s₂, hs₂, hb₂⟩ := hb
  -- The intersection s₁ ∩ s₂ also supports x
  have hint : supports (s₁ ∩ s₂) x := supports_inter hs₁ hs₂
  -- a ∉ s₁ ∩ s₂ (since a ∉ s₁)
  have ha' : a ∉ (s₁ ∩ s₂ : Finset α) := fun h ↦ ha₁ (Finset.mem_inter.mp h).1
  -- b ∉ s₁ ∩ s₂ (since b ∉ s₂)
  have hb' : b ∉ (s₁ ∩ s₂ : Finset α) := fun h ↦ hb₂ (Finset.mem_inter.mp h).2
  -- By supports_iff_swap, swap a b • x = x
  exact (supports_iff_swap.mp hint) a b ha' hb'

/-- `supp x` is the **least** finite support of `x`: every finite support `s` of `x` satisfies `supp x ⊆ s`. -/
theorem supp_le {x : X} (s : Finset α) (hs : supports s x) : supp x ⊆ s := by
  intro a ha
  exact (mem_supp.mp ha) s hs

/-- `supp x ⊆ s` if and only if `s` supports `x`. -/
theorem supp_le_iff {x : X} {s : Finset α} : supp x ⊆ s ↔ supports s x :=
  ⟨fun h ↦ supports_mono h (supp_supports x), fun h ↦ supp_le s h⟩

/-- If `f` is equivariant (`f (π • x) = π • f x` for all `π`), then `supp (f x) ⊆ supp x`. -/
theorem supp_map_le {Y : Type*} [Nominal α Y] (f : X → Y)
    (hf : ∀ (π : FinitePerm α) (x : X), f (π • x) = π • f x) (x : X) :
    supp (f x) ⊆ supp x := by
  apply supp_le
  intro π hπ
  rw [← hf]
  congr 1
  exact supp_supports x π hπ

/-- If `f` is equivariant and injective, then `supp (f x) = supp x`. -/
theorem supp_map_injective {Y : Type*} [Nominal α Y] {f : X → Y}
    (hf : ∀ (π : FinitePerm α) (x : X), f (π • x) = π • f x)
    (hinj : Function.Injective f) (x : X) :
    supp (f x) = supp x := by
  apply le_antisymm
  · exact supp_map_le f hf x
  · apply supp_le
    intro π hπ
    exact hinj ((hf π x).symm ▸ supp_supports (f x) π hπ)

/-- The support function is equivariant: `π • supp x = supp (π • x)`. -/
@[simp]
theorem supp_equivariant (π : FinitePerm α) (x : X) : π • supp x = supp (π • x) := by
  apply le_antisymm
  · have hsup : supports (π⁻¹ • supp (π • x)) x := by
      have h := supports_smul π⁻¹ (supp_supports (π • x))
      rwa [PermType.inv_smul_smul] at h
    have hle : supp x ⊆ π⁻¹ • supp (π • x) := supp_le _ hsup
    calc π • supp x
        ⊆ π • (π⁻¹ • supp (π • x)) := by
            simp only [PermType.finset_smul]
            exact Finset.image_subset_image hle
      _ = supp (π • x)              := by
            rw [← mul_smul, mul_inv_cancel, one_smul]
  · exact supp_le (π • supp x) (supports_smul π (supp_supports x))

/-- Symmetric form of `supp_equivariant`: `supp (π • x) = π • supp x`. -/
theorem supp_smul_eq (π : FinitePerm α) (x : X) : supp (π • x) = π • supp x :=
  (supp_equivariant π x).symm

/-- Membership in the support of a permuted element: `b ∈ supp (π • x) ↔ π⁻¹ • b ∈ supp x`. -/
@[simp]
theorem mem_supp_smul {x : X} (π : FinitePerm α) (b : α) :
    b ∈ supp (π • x) ↔ π⁻¹ • b ∈ supp x := by
  rw [← supp_equivariant, PermType.mem_smul_finset_iff]

/-- `supp x = ∅` if and only if every permutation fixes `x`. -/
theorem supp_eq_empty_iff {x : X} : supp x = ∅ ↔ ∀ π : FinitePerm α, π • x = x := by
  constructor
  · intro h π
    have : supports ∅ x := h ▸ supp_supports x
    exact this π (fun a ha ↦ by simp at ha)
  · intro h
    rw [Finset.eq_empty_iff_forall_notMem]
    intro a
    simp only [mem_supp]
    push_neg
    exact ⟨∅, fun π _ ↦ h π, Finset.notMem_empty a⟩

/-- The support of the unique element of `Unit` is empty.

This uses `Nominal.instUnit` (a `def`, not a global `instance`) because `α` cannot be inferred from `Unit`. -/
@[simp]
theorem supp_unit (u : Unit) : @supp α _ Unit Nominal.instUnit u = ∅ := by
  letI : Nominal α Unit := Nominal.instUnit
  exact Finset.subset_empty.mp (supp_le ∅ (fun _ _ ↦ rfl))

/-- The support of a pair is the union of the supports. -/
@[simp]
theorem supp_prod {Y : Type*} [Nominal α Y] (x : X) (y : Y) : supp (x, y) = supp x ∪ supp y := by
  apply le_antisymm
  · exact supp_le _ (supports_prod (supp_supports x) (supp_supports y))
  · intro a ha
    rw [Finset.mem_union] at ha
    rw [mem_supp]
    intro s hs
    rcases ha with hx | hy
    · apply (mem_supp.mp hx) s
      intro π hπ
      have := hs π hπ
      simp only [PermType.prod_smul, Prod.mk.injEq] at this
      exact this.1
    · apply (mem_supp.mp hy) s
      intro π hπ
      have := hs π hπ
      simp only [PermType.prod_smul, Prod.mk.injEq] at this
      exact this.2

/-- The support of `none` is empty. -/
@[simp]
theorem supp_none {X : Type*} [Nominal α X] : supp (none : Option X) = ∅ :=
  Finset.subset_empty.mp (supp_le ∅ (fun _ _ ↦ rfl))

/-- The support of `some x` equals the support of `x`. -/
@[simp]
theorem supp_some {X : Type*} [Nominal α X] (x : X) : supp (some x) = supp x :=
  supp_map_injective (fun π x ↦ by simp) (Option.some_injective X) x

/-- The least support of an atom `a` is the singleton `{a}`. -/
@[simp]
theorem supp_atom (a : α) : supp (α := α) a = {a} := by
  apply le_antisymm
  · exact supp_le {a} (fun π h ↦ by
      simp only [PermType.atoms_smul]
      exact h (Finset.mem_coe.mpr (Finset.mem_singleton.mpr rfl)))
  · intro b hb
    rw [Finset.mem_singleton] at hb
    rw [hb, mem_supp]
    intro s hs
    by_contra ha
    pick_new c (s ∪ {a})
    simp only [Finset.mem_union, Finset.mem_singleton, not_or] at cNew
    obtain ⟨hcs, hca⟩ := cNew
    have hfix := (supports_iff_swap.mp hs) a c ha hcs
    rw [swap_apply_left] at hfix
    exact hca hfix

/-- The least support of a finite set of atoms `s` is `s` itself. -/
@[simp]
theorem supp_finset (s : Finset α) : supp (α := α) s = s := by
  apply le_antisymm
  · exact supp_le s (Nominal.finset_supports_self s)
  · intro a ha
    rw [mem_supp]
    intro t ht
    by_contra hat
    pick_new b (t ∪ s)
    simp only [Finset.mem_union, not_or] at bNew
    obtain ⟨hbt, hbs⟩ := bNew
    have hfix := (supports_iff_swap.mp ht) a b hat hbt
    -- swap a b • s = s, but a ∈ s so b = (a b) • a ∈ (a b) • s = s, contradicting b ∉ s
    have : b ∈ s := by
      have hmem : b ∈ swap a b • s := by
        rw [PermType.finset_smul, Finset.mem_image]
        exact ⟨a, ha, by simp [swap]⟩
      rwa [hfix] at hmem
    exact hbs this

/-- The least support of a finite permutation `σ` is its moved-point set `movedFinset σ`. -/
@[simp]
theorem supp_finitePerm (σ : FinitePerm α) : supp σ = PermType.movedFinset σ := by
  apply le_antisymm
  · exact supp_le _ (Nominal.finitePerm_supports_self σ)
  · intro a ha
    rw [mem_supp]
    intro s hs
    by_contra hat
    rw [PermType.mem_movedFinset] at ha
    -- Since a ∉ s and σ a ≠ a, we need to show contradiction.
    -- We also need σ a ∉ s: if σ a ∈ s, then since s supports σ under conjugation,
    -- any swap of two atoms outside s fixes σ. In particular swap a (σ a) would fix σ,
    -- but we'll use a fresh atom instead.
    -- Pick b fresh from s ∪ movedFinset σ
    pick_new b (s ∪ PermType.movedFinset σ)
    simp only [Finset.mem_union, not_or] at bNew
    obtain ⟨hbs, hbm⟩ := bNew
    -- b is a fixed point of σ
    have hfixb : σ b = b := PermType.fixed_of_not_mem_movedFinset hbm
    -- swap a b fixes s (both a, b ∉ s), so swap a b • σ = σ (conjugation)
    have hconj := (supports_iff_swap.mp hs) a b hat hbs
    -- swap a b • σ = σ means swap a b * σ * swap a b = σ
    rw [PermType.conj_smul, swap_inv] at hconj
    -- Evaluate hconj at a: (swap a b * σ * swap a b) a = σ a
    -- LHS = swap a b (σ (swap a b a)) = swap a b (σ b) = swap a b b = a
    -- So σ a = a, contradicting ha.
    have := congr_arg (· a) hconj
    simp only [mul_apply, swap_apply_left', hfixb, swap_apply_right'] at this
    exact ha this.symm

/-- The support of `Sum.inl x` equals the support of `x`. -/
@[simp]
theorem supp_inl {X Y : Type*} [Nominal α X] [Nominal α Y] (x : X) :
    supp (Sum.inl x : X ⊕ Y) = supp x :=
  supp_map_injective (fun π x ↦ by simp) (@Sum.inl_injective X Y) x

/-- The support of `Sum.inr y` equals the support of `y`. -/
@[simp]
theorem supp_inr {X Y : Type*} [Nominal α X] [Nominal α Y] (y : Y) :
    supp (Sum.inr y : X ⊕ Y) = supp y :=
  supp_map_injective (fun π y ↦ by simp) (@Sum.inr_injective X Y) y

end Supp

/-! ## Nominal functions (`PFun`) -/

section PFunSupport

open MulAction PermType

variable {α : Type*} [Name α] {X Y : Type*} [PermType α X] [PermType α Y]

/-- A finite set `s` supports `f : PFun α X Y` if and only if every permutation fixing `s`
commutes with `f`: `f (π • x) = π • f x` for all `x`. -/
theorem supports_pfun_iff {s : Finset α} {f : PFun α X Y} :
    supports s f ↔ ∀ π : FinitePerm α, (∀ ⦃a⦄, a ∈ s → π a = a) → ∀ x : X, f (π • x) = π • f x := by
  constructor
  · intro hsup π hfix x
    have hf : π • f = f := hsup π (fun a ha ↦ by
      rw [PermType.atoms_smul]
      exact hfix (Finset.mem_coe.mp ha))
    have := congrFun (congrArg DFunLike.coe hf) (π • x)
    simp only [PFun.smul_apply, PermType.inv_smul_smul] at this
    exact this.symm
  · intro hcomm π hfix
    ext x
    change π • f (π⁻¹ • x) = f x
    have hfix' : ∀ ⦃a⦄, a ∈ s → π⁻¹ a = a := by
      intro a ha
      have := hfix (Finset.mem_coe.mpr ha)
      rw [PermType.atoms_smul] at this
      have := congr_arg (π⁻¹ ·) this
      simp at this
      exact this.symm
    rw [hcomm π⁻¹ hfix' x, PermType.smul_inv_smul]

/-- The identity `PFun` is supported by `∅`. -/
theorem supports_pfun_id : supports (∅ : Finset α) (PFun.id : PFun α X X) :=
  supports_pfun_iff.mpr fun _ _ x ↦ by simp

/-- Composition of `PFun`s: if `s` supports `g` and `t` supports `f`, then `s ∪ t`
supports `g.comp f`. -/
theorem supports_pfun_comp {Z : Type*} [PermType α Z]
    {s t : Finset α} {g : PFun α Y Z} {f : PFun α X Y}
    (hg : supports s g) (hf : supports t f) :
    supports (s ∪ t) (g.comp f) := by
  rw [supports_pfun_iff]
  intro π hπ x
  have hg' := (supports_pfun_iff.mp hg) π (fun a ha ↦ hπ (Finset.mem_union_left _ ha))
  have hf' := (supports_pfun_iff.mp hf) π (fun a ha ↦ hπ (Finset.mem_union_right _ ha))
  simp only [PFun.comp_apply, hf' x, hg']

end PFunSupport

section PFunSupportNominal

open MulAction PermType

variable {α : Type*} [Name α] {X Y : Type*} [Nominal α X] [Nominal α Y]

/-- A constant `PFun` returning `y` is supported by `supp y`. -/
theorem supports_pfun_const (y : Y) :
    supports (supp y) (PFun.const y : PFun α X Y) := by
  rw [supports_pfun_iff]
  intro π hπ x
  simp only [PFun.const_apply]
  exact (supp_supports y π (fun a ha ↦ by
    rw [PermType.atoms_smul]; exact hπ (Finset.mem_coe.mp ha))).symm

end PFunSupportNominal

end NominalSets
