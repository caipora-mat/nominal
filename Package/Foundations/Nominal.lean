/-
Copyright (c) 2026 Nominal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nominal contributors
-/
import Package.Foundations.Support
import Mathlib.Order.Minimal

/-!
# Nominality and least support

`Nominal A X` certifies finite supportedness for the already selected action;
it contains no action or chosen bound. Over infinite atoms, each individually
finitely supported element has a unique least finite support. Mathlib's
well-founded Finset order supplies a minimal bound, and `supports_inter` turns
minimality into leastness. No decidable-equality parameter enters the choice.
`hx.support` needs only support of one element; `support A x` uses a carrier
certificate and agrees with every elementwise certificate for the same action.
Least support need not be strong support: element fixation implies only setwise
preservation of the support, not pointwise fixation of its atoms.
-/

namespace NominalPackage

universe u v w

/-- Every element of the selected action has a finite supporting bound. -/
class Nominal (A : Type u) (X : Type v) [MulAction (Perm A) X] : Prop where
  /-- Support existence is proof-only; no supporting set is stored as data. -/
  finitelySupported : ∀ x : X, FinitelySupported A x

/-- An equivariant surjection transfers nominality between already selected
actions. Preimages are used only inside the proof of finite supportedness. -/
theorem Equivariant.nominal_of_surjective {A : Type u} {X : Type v} {Y : Type w}
    [MulAction (Perm A) X] [MulAction (Perm A) Y] [Nominal A X] {f : X → Y}
    (hf : Equivariant A f) (hsurj : Function.Surjective f) : Nominal A Y := by
  constructor
  intro y
  obtain ⟨x, rfl⟩ := hsurj y
  exact (Nominal.finitelySupported (A := A) x).map hf

variable {A : Type u} {X : Type v}
variable [MulAction (Perm A) X] [Infinite A]
variable {x : X} {S : Finset A}

/-- An individually supported element has a unique least finite supporting set.
Infinitude is used only by the delivered binary-intersection theorem. -/
theorem FinitelySupported.exists_least_support (hx : FinitelySupported A x) :
    ∃! S : Finset A, Supports S x ∧
      ∀ T : Finset A, Supports T x → S ⊆ T := by
  classical
  obtain ⟨S, hS⟩ := exists_minimal_of_wellFoundedLT (fun S : Finset A => Supports S x) hx
  have hleast : ∀ T : Finset A, Supports T x → S ⊆ T := by
    intro T hT
    exact le_trans (hS.le_of_le (supports_inter hS.prop hT) Finset.inter_subset_left)
      Finset.inter_subset_right
  refine ⟨S, ⟨hS.prop, hleast⟩, ?_⟩
  intro T hT
  exact le_antisymm (hT.2 S hS.prop) (hleast T hT.1)

/-- Least support of an individually finitely supported element. The certificate
is required: unsupported elements receive no default support. -/
noncomputable def FinitelySupported.support (hx : FinitelySupported A x) : Finset A :=
  hx.exists_least_support.exists.choose

/-- The chosen least bound supports its element. -/
theorem FinitelySupported.supports_support (hx : FinitelySupported A x) :
    Supports hx.support x :=
  hx.exists_least_support.exists.choose_spec.1

/-- Least support is contained in every finite supporting bound. -/
theorem FinitelySupported.support_minimal (hx : FinitelySupported A x)
    (hS : Supports S x) : hx.support ⊆ S :=
  hx.exists_least_support.exists.choose_spec.2 S hS

/-- A finite bound supports the element exactly when it contains its least support. -/
theorem FinitelySupported.supports_iff_support_subset
    (hx : FinitelySupported A x) (S : Finset A) : Supports S x ↔ hx.support ⊆ S :=
  ⟨hx.support_minimal, fun h => supports_mono h hx.supports_support⟩

/-- Any independently established least support agrees with the chosen one. -/
theorem FinitelySupported.support_unique (hx : FinitelySupported A x)
    (hS : Supports S x) (hmin : ∀ T : Finset A, Supports T x → S ⊆ T) :
    hx.support = S :=
  le_antisymm (hx.support_minimal hS) (hmin _ hx.supports_support)

/-- Changing the proof of finite supportedness does not change least support. -/
theorem FinitelySupported.support_eq (hx hx' : FinitelySupported A x) :
    hx.support = hx'.support := rfl

/-- Empty least support characterizes invariance under every finite permutation. -/
theorem FinitelySupported.support_eq_empty_iff (hx : FinitelySupported A x) :
    hx.support = ∅ ↔ ∀ π : Perm A, π • x = x := by
  constructor
  · intro h
    apply (supports_empty_iff x).1
    simpa only [h] using hx.supports_support
  · intro h
    exact le_antisymm (hx.support_minimal ((supports_empty_iff x).2 h))
      (Finset.empty_subset _)

/-- An equivariant image can lose atoms of support; equality is not asserted. -/
theorem FinitelySupported.support_map_subset {Y : Type w} [MulAction (Perm A) Y]
    {f : X → Y} (hx : FinitelySupported A x) (hf : Equivariant A f) :
    (hx.map hf).support ⊆ hx.support :=
  (hx.map hf).support_minimal (supports_map hf hx.supports_support)

section Transport

variable [DecidableEq A]
open scoped Pointwise

/-- Least support renames by the existing finite-set image action. The proof
uses transport of supporting bounds in both directions, not commutation. -/
theorem FinitelySupported.support_smul (hx : FinitelySupported A x) (π : Perm A) :
    (hx.smul π).support = π • hx.support := by
  apply le_antisymm
  · exact (hx.smul π).support_minimal (supports_smul hx.supports_support π)
  · apply Finset.smul_finset_subset_iff.mpr
    apply hx.support_minimal
    simpa only [inv_smul_smul] using supports_smul (hx.smul π).supports_support π⁻¹

end Transport

open scoped Pointwise in
/-- An atom belongs to image support exactly when it belongs to the support of
every individually supported preimage in the same fiber. One supported preimage
suffices; neither carrier nominality nor surjectivity is assumed. -/
theorem FinitelySupported.mem_support_map_iff
    {A : Type u} {X : Type v} {Y : Type w}
    [MulAction (Perm A) X] [MulAction (Perm A) Y] [Infinite A]
    {x : X} {f : X → Y}
    (hx : FinitelySupported A x) (hf : Equivariant A f) (a : A) :
    a ∈ (hx.map hf).support ↔
      ∀ (z : X) (hz : FinitelySupported A z), f z = f x → a ∈ hz.support := by
  classical
  constructor
  · intro ha z hz heq
    have hS : Supports hz.support (f x) := by
      simpa only [heq] using supports_map hf hz.supports_support
    exact (hx.map hf).support_minimal hS ha
  · intro h
    by_contra ha
    obtain ⟨b, hb⟩ := Finset.exists_notMem (insert a hx.support)
    have hbS : b ∉ hx.support := fun hmem => hb (Finset.mem_insert_of_mem hmem)
    have hbI : b ∉ (hx.map hf).support := fun hmem => hbS (hx.support_map_subset hf hmem)
    have hfix : Perm.swap a b • f x = f x :=
      swap_smul_eq_of_supports (hx.map hf).supports_support ha hbI
    have heq : f (Perm.swap a b • x) = f x := (hf (Perm.swap a b) x).trans hfix
    have hmem := h (Perm.swap a b • x) (hx.smul (Perm.swap a b)) heq
    rw [hx.support_smul (Perm.swap a b), Perm.mem_smul_finset,
      Perm.swap_inv, Perm.swap_apply_left] at hmem
    exact hbS hmem

section NominalCarriers

variable (A) [Nominal A X]

/-- Least support using the carrier's proof-only nominality certificate.
The atom type is explicit; this is the elementwise operation with no new choice. -/
noncomputable def support (x : X) : Finset A :=
  (Nominal.finitelySupported (A := A) x).support

/-- Carrier and elementwise support agree for every support-existence proof. -/
theorem support_eq (x : X) (hx : FinitelySupported A x) : support A x = hx.support :=
  (Nominal.finitelySupported (A := A) x).support_eq hx

/-- The least support of an element of a nominal carrier supports it. -/
theorem supports_support (x : X) : Supports (support A x) x :=
  (Nominal.finitelySupported (A := A) x).supports_support

/-- Every finite supporting bound contains the carrier operation's support. -/
theorem support_minimal {x : X} {S : Finset A} (hS : Supports S x) : support A x ⊆ S :=
  (Nominal.finitelySupported (A := A) x).support_minimal hS

/-- Finite supporting bounds are precisely the supersets of least support. -/
theorem supports_iff_support_subset (x : X) (S : Finset A) :
    Supports S x ↔ support A x ⊆ S :=
  (Nominal.finitelySupported (A := A) x).supports_iff_support_subset S

/-- Empty least support is universal permutation invariance. -/
theorem support_eq_empty_iff (x : X) :
    support A x = ∅ ↔ ∀ π : Perm A, π • x = x :=
  (Nominal.finitelySupported (A := A) x).support_eq_empty_iff

/-- Equivariant maps between nominal carriers can only decrease support. -/
theorem support_map_subset {Y : Type w} [MulAction (Perm A) Y] [Nominal A Y]
    {f : X → Y} (hf : Equivariant A f) (x : X) : support A (f x) ⊆ support A x :=
  (Nominal.finitelySupported (A := A) x).support_map_subset hf

open scoped Pointwise

/-- Carrier least support commutes with renaming, using scoped finite-set images. -/
theorem support_smul [DecidableEq A] (π : Perm A) (x : X) :
    support A (π • x) = π • support A x :=
  (Nominal.finitelySupported (A := A) x).support_smul π

end NominalCarriers

end NominalPackage
