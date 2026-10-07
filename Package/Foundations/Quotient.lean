/-
Copyright (c) 2026 Nominal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nominal contributors
-/
import Package.Foundations.QuotientAction
import Package.Foundations.Nominal

/-!
# Canonical nominal quotients

The canonical projection preserves every sufficient finite support and individual
support certificate. Source nominality transfers through its surjectivity.
Each result fixes the constructed action: no instance certifies an unrelated
action on the same quotient carrier. Least-support inclusion needs infinite
atoms; the preceding projection and nominality contracts do not. Over infinite
atoms, a class in a nominal quotient has support equal to the set intersection
of its representatives' supports. No representative is claimed to attain it.
-/

namespace NominalPackage.QuotientAction

universe u v

variable (A : Type u) {X : Type v} [MulAction (Perm A) X]

/-- The ordinary projection is equivariant for the constructed quotient action. -/
theorem equivariant_mk (s : Setoid X) (hs : SMulInvariant (Perm A) s) :
    letI := QuotientAction.mulAction s hs
    Equivariant A (Quotient.mk s) :=
  mk_smul s hs

/-- The projection retains every sufficient finite bound. -/
theorem supports_mk (s : Setoid X) (hs : SMulInvariant (Perm A) s)
    {S : Finset A} {x : X} (hS : Supports S x) :
    letI := QuotientAction.mulAction s hs
    Supports S (Quotient.mk s x) := by
  let _ := QuotientAction.mulAction s hs
  exact supports_map (equivariant_mk A s hs) hS

/-- Individual support passes to a class without nominality of the whole source. -/
theorem finitelySupported_mk (s : Setoid X) (hs : SMulInvariant (Perm A) s)
    {x : X} (hx : FinitelySupported A x) :
    letI := QuotientAction.mulAction s hs
    FinitelySupported A (Quotient.mk s x) := by
  let _ := QuotientAction.mulAction s hs
  exact hx.map (equivariant_mk A s hs)

/-- Nominality of the canonical action, supplied as an explicit certificate. -/
theorem nominal [Nominal A X] (s : Setoid X) (hs : SMulInvariant (Perm A) s) :
    letI := QuotientAction.mulAction s hs
    Nominal A (Quotient s) := by
  let _ := QuotientAction.mulAction s hs
  exact (equivariant_mk A s hs).nominal_of_surjective Quotient.mk_surjective

/-- Quotienting can decrease least support; the carrier form uses source
nominality and the induced quotient certificate. -/
theorem support_mk_subset [Infinite A] [Nominal A X]
    (s : Setoid X) (hs : SMulInvariant (Perm A) s) (x : X) :
    letI := QuotientAction.mulAction s hs
    letI := QuotientAction.nominal A s hs
    support A (Quotient.mk s x) ⊆ support A x := by
  let _ := QuotientAction.mulAction s hs
  let _ := QuotientAction.nominal A s hs
  exact support_map_subset A (equivariant_mk A s hs) x

/-- Class support is the intersection of representative supports, as a set of
atoms. Quotient induction specializes the general supported-fiber theorem. -/
theorem support_eq_iInter [Infinite A] [Nominal A X]
    (s : Setoid X) (hs : SMulInvariant (Perm A) s) (c : Quotient s) :
    letI := QuotientAction.mulAction s hs
    letI := QuotientAction.nominal A s hs
    (support A c : Set A) =
      ⋂ x : {x : X // Quotient.mk s x = c}, (support A x.val : Set A) := by
  let _ := QuotientAction.mulAction s hs
  let _ := QuotientAction.nominal A s hs
  induction c using Quotient.inductionOn with
  | h x =>
    ext a
    simp only [Set.mem_iInter, Finset.mem_coe]
    have h := (Nominal.finitelySupported (A := A) x).mem_support_map_iff
      (equivariant_mk A s hs) a
    constructor
    · intro ha y
      exact h.1 ha y.val (Nominal.finitelySupported (A := A) y.val) y.property
    · intro ha
      apply h.2
      intro z hz heq
      simpa only [support_eq A z hz] using ha ⟨z, heq⟩

end NominalPackage.QuotientAction
