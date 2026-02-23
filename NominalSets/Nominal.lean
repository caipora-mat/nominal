import NominalSets.Support
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
* `Nominal.instOption` — `Option X` is nominal (`none` has empty support; `some x` inherits
  the support of `x`).
* `Nominal.instUnit` — `Unit` is a nominal set (the unique element has empty support; not a
  global `instance` because `α` cannot be inferred from `Unit`).
* `Nominal.instFinsetNominal` — finite sets of atoms form a nominal set (each `s` is supported
  by itself).

## Main results

* `Nominal.finset_supports_self` — every finite set of atoms `s : Finset α` supports itself.
* `mem_supp` — `a ∈ supp x ↔ ∀ s, supports s x → a ∈ s`.
* `coe_supp` — `(supp x : Set α) = suppSet x` (the support as a set equals the intersection
  of all finite supports).
* `supp_supports` — `supp x` is itself a support for `x`.
* `supp_le` — `supp x` is the least finite support: every finite support `s` satisfies
  `supp x ⊆ s`.
* `supp_equivariant` — `π • supp x = supp (π • x)`.

## References

* [A. M. Pitts, *Nominal Sets*][Pitts2013], Chapter 2.
-/

namespace NominalSets

/-- A **nominal set** is a permutation type in which every element is finitely supported.

`α` is an `outParam` (as in `PermType`) so that Lean can infer the atom type from `X` alone.
This lets callers write `supp x` rather than `supp  x`. The trade-off is that each
type `X` may have at most one `Nominal` instance (one atom type `α`) -/
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
  finSupp := fun ⟨x, y⟩ ↦ by
    obtain ⟨sx, hsx⟩ := Nominal.finSupp  x
    obtain ⟨sy, hsy⟩ := Nominal.finSupp  y
    exact ⟨sx ∪ sy, fun π hπ ↦ by
      simp only [PermType.prod_smul]
      congr
      · exact hsx π (fun a ha ↦ hπ (Finset.mem_union_left _ ha))
      · exact hsy π (fun a ha ↦ hπ (Finset.mem_union_right _ ha))⟩

/-- `Unit` is a nominal set: the unique element is supported by the empty set.

This is a `def` rather than a global `instance` because `α` cannot be inferred
from `Unit` alone (same reason as `PermType.instUnit`). -/
def instUnit : Nominal α Unit where
  __ := PermType.instUnit
  finSupp _ := ⟨∅, fun _ _ ↦ rfl⟩

/-- `Option X` is a nominal set: `none` is supported by `∅`, and `some x` is
supported by the support of `x`. -/
instance instOption [Nominal α X] : Nominal α (Option X) where
  __ := PermType.instOption
  finSupp o := by
    cases o with
    | none => exact ⟨∅, fun _ _ ↦ rfl⟩
    | some x =>
      obtain ⟨s, hs⟩ := Nominal.finSupp x
      exact ⟨s, fun π hπ ↦ by simp [hs π hπ]⟩

/-- Every finite set of atoms `s` is supported by itself: any permutation fixing `s` fixes `s` as a set element. -/
theorem finset_supports_self (s : Finset α) :
    supports s s := by
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

end Nominal

/-! ## The least support: `supp x`

For any nominal set `X` and element `x : X`, the intersection of all finite supports of `x`
is itself a finite support of `x`, and it is contained in every other finite support.
This is the **least support** `supp x`, also written `supp(x)` in the literature.
-/

section Supp

open MulAction

variable {α : Type*} [Name α] {X : Type*} [Nominal α X]

/-- The **support** `suppSet x` is the intersection of all finite supports of `x`.
This is a `Set α`; use `supp x` for the corresponding `Finset α`. -/
private def suppSet (x : X) : Set α :=
  ⋂ (s : Finset α) (_ : supports s x), (s : Set α)

/-- Membership in `suppSet x`: an atom belongs iff it belongs to every finite support of `x`. -/
private theorem mem_suppSet {x : X} {a : α} :
    a ∈ suppSet x ↔ ∀ (s : Finset α), supports s x → a ∈ s := by
  simp only [suppSet, Set.mem_iInter, Finset.mem_coe]

/-- `suppSet x` is contained in every finite support of `x`. -/
private theorem suppSet_subset {x : X} (s : Finset α) (hs : supports s x) :
    suppSet x ⊆ (s : Set α) := by
  intro a ha
  exact Finset.mem_coe.mpr ((mem_suppSet.mp ha) s hs)

/-- `suppSet x` is a finite set (it is a subset of any one finite support). -/
private theorem suppSet_finite (x : X) : (suppSet x).Finite := by
  have ⟨s, hs⟩ : FinSupported x := @Nominal.finSupp α _ X _ x
  exact Set.Finite.subset (Finset.finite_toSet s) (suppSet_subset s hs)

/-- The **least support** of `x`, as a `Finset α`.
Equal to the intersection of all finite supports. -/
noncomputable def supp (x : X) : Finset α :=
  (suppSet_finite x).toFinset

/-- Membership in `supp x`: an atom belongs iff it belongs to every finite support of `x`. -/
@[simp]
theorem mem_supp {x : X} {a : α} :
    a ∈ supp x ↔ ∀ (s : Finset α), supports s x → a ∈ s := by
  simp [supp, Set.Finite.mem_toFinset, mem_suppSet]

/-- `supp x`, viewed as a set, equals `suppSet x`. -/
@[simp]
theorem coe_supp (x : X) : (supp x : Set α) = suppSet x :=
  Set.Finite.coe_toFinset _

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
  have hint : supports (s₁ ∩ s₂) x := supports_inter s₁ s₂ x hs₁ hs₂
  -- a ∉ s₁ ∩ s₂ (since a ∉ s₁)
  have ha' : a ∉ (s₁ ∩ s₂ : Finset α) := fun h ↦ ha₁ (Finset.mem_inter.mp h).1
  -- b ∉ s₁ ∩ s₂ (since b ∉ s₂)
  have hb' : b ∉ (s₁ ∩ s₂ : Finset α) := fun h ↦ hb₂ (Finset.mem_inter.mp h).2
  -- By supports_iff_swap, swap a b • x = x
  exact (supports_iff_swap.mp hint) a b ha' hb'

/-- `supp x` is the **least** finite support of `x`:
every finite support `s` of `x` satisfies `supp x ⊆ s`. -/
theorem supp_le {x : X} (s : Finset α) (hs : supports s x) :
    supp x ⊆ s := by
  intro a ha
  exact (mem_supp.mp ha) s hs

/-- The support function is equivariant: `π • supp x = supp (π • x)`. -/
@[simp]
theorem supp_equivariant (π : FinitePerm α) (x : X) :
    π • supp x = supp (π • x) := by
  apply le_antisymm
  · -- Direction: π • supp x ⊆ supp (π • x)
    -- supports_smul with π⁻¹ on (π • x): π⁻¹ • supp(π • x) supports π⁻¹ • (π • x) = x
    have hsup : supports (π⁻¹ • supp (π • x)) x := by
      have h := supports_smul π⁻¹ (supp_supports (π • x))
      rwa [PermType.inv_smul_smul] at h
    -- supp x ⊆ π⁻¹ • supp(π • x) by minimality
    have hle : supp x ⊆ π⁻¹ • supp (π • x) := supp_le _ hsup
    -- Apply π • (monotone) and cancel π * π⁻¹
    calc π • supp x
        ⊆ π • (π⁻¹ • supp (π • x)) := by
            simp only [PermType.finset_smul]
            exact Finset.image_subset_image hle
      _ = supp (π • x)              := by
            rw [← mul_smul, mul_inv_cancel, one_smul]
  · -- Direction: supp (π • x) ⊆ π • supp x
    -- π • supp x supports π • x (by supports_smul), so supp_le applies
    exact supp_le (π • supp x) (supports_smul π (supp_supports x))

/-- `supp x = ∅` if and only if every permutation fixes `x`. -/
theorem supp_eq_empty_iff {x : X} :
    supp x = ∅ ↔ ∀ π : FinitePerm α, π • x = x := by
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

/-- The support of a pair is the union of the supports. -/
theorem supp_prod {Y : Type*} [Nominal α Y] (x : X) (y : Y) :
    supp (x, y) = supp x ∪ supp y := by
  apply le_antisymm
  · exact supp_le _ (fun π hπ ↦ by
      simp only [PermType.prod_smul, Prod.mk.injEq]
      exact ⟨supp_supports x π (fun a ha ↦ hπ (Finset.mem_coe.mpr (Finset.mem_union_left _ ha))),
             supp_supports y π (fun a ha ↦ hπ (Finset.mem_coe.mpr (Finset.mem_union_right _ ha)))⟩)
  · intro a ha
    rw [Finset.mem_union] at ha
    rw [mem_supp]
    intro s hs
    rcases ha with hx | hy
    · exact (mem_supp.mp hx) s (fun π hπ ↦ by
        have := hs π hπ; simp only [PermType.prod_smul, Prod.mk.injEq] at this; exact this.1)
    · exact (mem_supp.mp hy) s (fun π hπ ↦ by
        have := hs π hπ; simp only [PermType.prod_smul, Prod.mk.injEq] at this; exact this.2)

end Supp

end NominalSets

-- TODO: below alternative way of defining suppSet. Don't know which one is better
-- /-! ### Support: definition and properties -/

-- section Supp

-- variable [Nominal α X]

-- /-- The set of atoms belonging to every finite support of `x`. -/
-- def suppSet (x : X) : Set α :=
--   {a | ∀ s : Finset α, supports  (↑s) x → a ∈ s}

-- theorem suppSet_finite (x : X) : (suppSet  x).Finite := by
--   obtain ⟨s₀, hs₀⟩ := Nominal.finSupp  x
--   exact s₀.finite_toSet.subset fun a ha => ha s₀ hs₀

-- /-- The **support** of `x` in a nominal set: the intersection of all finite supports.
-- This is the smallest finite set of atoms supporting `x`. -/
-- noncomputable def supp (x : X) : Finset α :=
--   (suppSet_finite  x).toFinset

-- @[simp]
-- theorem mem_supp {x : X} {a : α} :
--     a ∈ supp  x ↔ ∀ s : Finset α, supports  (↑s) x → a ∈ s := by
--   simp [supp, suppSet, Set.Finite.mem_toFinset]

-- /-- `supp x` supports `x`: every permutation fixing `supp x` pointwise also fixes `x`. -/
-- theorem supp_supports (x : X) : supports  (↑(supp  x)) x := by
--   rw [supports_iff_swap]
--   intro a₁ a₂ ha₁ ha₂
--   simp only [Finset.mem_coe, mem_supp] at ha₁ ha₂
--   push_neg at ha₁ ha₂
--   obtain ⟨s₁, hs₁, ha₁⟩ := ha₁
--   obtain ⟨s₂, hs₂, ha₂⟩ := ha₂
--   exact (supports_iff_swap.mp (supports_inter s₁ s₂ x hs₁ hs₂)) a₁ a₂
--     (by simp only [Finset.mem_coe, Finset.mem_inter]; tauto)
--     (by simp only [Finset.mem_coe, Finset.mem_inter]; tauto)

-- /-- `supp x` is contained in every finite support of `x`: it is the least finite support. -/
-- theorem supp_least {x : X} {s : Finset α}
--     (hs : supports  (↑s) x) : supp  x ⊆ s := fun _ ha ↦
--   (mem_supp.mp ha) s hs

-- end Supp
