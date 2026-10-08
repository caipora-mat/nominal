/-
Copyright (c) 2026 Nominal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nominal contributors
-/
import Package.Foundations.PredicateSupport

/-!
# Logical support and quantification

Ordinary logical connectives preserve common sufficient bounds; separate bounds
combine by finite union. Negation also reflects support, by classical reasoning.

Quantifying a jointly supported relation over an entire acted carrier preserves
its bound: the action reindexes the quantified variable bijectively. Neither
carrier needs to be nominal or nonempty. Restricted quantification uses these
same results on the combined implication or conjunction body, without requiring
separate support of the guard.

For an external index in an arbitrary Sort, the uniform family laws instead
require one bound supporting every section. Individually supported sections need
not have such a common bound. No action on the external index is needed.
-/

namespace NominalPackage
universe u v w i

variable {A : Type u} {X : Type v} {Y : Type w}
variable [MulAction (Perm A) X] [MulAction (Perm A) Y]
variable {S T : Finset A} {p q : X → Prop} {R : X × Y → Prop}

/-- Every constant truth value has empty support. -/
theorem supportsPred_const (A : Type u) (X : Type v) [MulAction (Perm A) X]
    (b : Prop) : SupportsPred (∅ : Finset A) (fun _ : X => b) :=
  fun _ _ _ => Iff.rfl

theorem SupportsPred.not (hp : SupportsPred S p) : SupportsPred S (fun x => ¬p x) :=
  fun π hfix x => not_congr (hp π hfix x)

/-- Complement preserves and reflects the same sufficient bound. -/
theorem supportsPred_not_iff (S : Finset A) (p : X → Prop) :
    SupportsPred S (fun x => ¬p x) ↔ SupportsPred S p := by
  classical
  exact ⟨fun h => by simpa only [not_not] using h.not, SupportsPred.not⟩

theorem SupportsPred.and_same (hp : SupportsPred S p) (hq : SupportsPred S q) :
    SupportsPred S (fun x => p x ∧ q x) :=
  fun π hfix x => and_congr (hp π hfix x) (hq π hfix x)

theorem SupportsPred.or_same (hp : SupportsPred S p) (hq : SupportsPred S q) :
    SupportsPred S (fun x => p x ∨ q x) :=
  fun π hfix x => or_congr (hp π hfix x) (hq π hfix x)

theorem SupportsPred.imp_same (hp : SupportsPred S p) (hq : SupportsPred S q) :
    SupportsPred S (fun x => p x → q x) :=
  fun π hfix x => imp_congr (hp π hfix x) (hq π hfix x)

theorem SupportsPred.iff_same (hp : SupportsPred S p) (hq : SupportsPred S q) :
    SupportsPred S (fun x => p x ↔ q x) :=
  fun π hfix x => iff_congr (hp π hfix x) (hq π hfix x)

section Bounds
variable [DecidableEq A]

theorem SupportsPred.and (hp : SupportsPred S p) (hq : SupportsPred T q) :
    SupportsPred (S ∪ T) (fun x => p x ∧ q x) :=
  (hp.mono Finset.subset_union_left).and_same (hq.mono Finset.subset_union_right)

theorem SupportsPred.or (hp : SupportsPred S p) (hq : SupportsPred T q) :
    SupportsPred (S ∪ T) (fun x => p x ∨ q x) :=
  (hp.mono Finset.subset_union_left).or_same (hq.mono Finset.subset_union_right)

theorem SupportsPred.imp (hp : SupportsPred S p) (hq : SupportsPred T q) :
    SupportsPred (S ∪ T) (fun x => p x → q x) :=
  (hp.mono Finset.subset_union_left).imp_same (hq.mono Finset.subset_union_right)

theorem SupportsPred.iff (hp : SupportsPred S p) (hq : SupportsPred T q) :
    SupportsPred (S ∪ T) (fun x => p x ↔ q x) :=
  (hp.mono Finset.subset_union_left).iff_same (hq.mono Finset.subset_union_right)
end Bounds

theorem FinitelySupportedPred.const (A : Type u) (X : Type v) [MulAction (Perm A) X]
    (b : Prop) : FinitelySupportedPred A (fun _ : X => b) :=
  (supportsPred_const A X b).finitelySupported

theorem FinitelySupportedPred.not (hp : FinitelySupportedPred A p) :
    FinitelySupportedPred A (fun x => ¬p x) := by
  obtain ⟨S, hS⟩ := hp
  exact hS.not.finitelySupported

theorem FinitelySupportedPred.and (hp : FinitelySupportedPred A p)
    (hq : FinitelySupportedPred A q) : FinitelySupportedPred A (fun x => p x ∧ q x) := by
  classical
  obtain ⟨S, hS⟩ := hp
  obtain ⟨T, hT⟩ := hq
  exact (hS.and hT).finitelySupported

theorem FinitelySupportedPred.or (hp : FinitelySupportedPred A p)
    (hq : FinitelySupportedPred A q) : FinitelySupportedPred A (fun x => p x ∨ q x) := by
  classical
  obtain ⟨S, hS⟩ := hp
  obtain ⟨T, hT⟩ := hq
  exact (hS.or hT).finitelySupported

theorem FinitelySupportedPred.imp (hp : FinitelySupportedPred A p)
    (hq : FinitelySupportedPred A q) : FinitelySupportedPred A (fun x => p x → q x) := by
  classical
  obtain ⟨S, hS⟩ := hp
  obtain ⟨T, hT⟩ := hq
  exact (hS.imp hT).finitelySupported

theorem FinitelySupportedPred.iff (hp : FinitelySupportedPred A p)
    (hq : FinitelySupportedPred A q) : FinitelySupportedPred A (fun x => p x ↔ q x) := by
  classical
  obtain ⟨S, hS⟩ := hp
  obtain ⟨T, hT⟩ := hq
  exact (hS.iff hT).finitelySupported

/-- Universal quantification reindexes the entire acted carrier, including an empty one. -/
theorem SupportsPred.all (hR : SupportsPred S R) :
    SupportsPred S (fun x => ∀ y, R (x,y)) := by
  intro π hfix x
  constructor
  · intro h y
    exact (hR π hfix (x,y)).1 (h (π • y))
  · intro h y
    simpa only [Prod.smul_mk, smul_inv_smul] using
      (hR π hfix (x,π⁻¹ • y)).2 (h _)

/-- Existential quantification preserves the joint relation's sufficient bound. -/
theorem SupportsPred.ex (hR : SupportsPred S R) :
    SupportsPred S (fun x => ∃ y, R (x,y)) := by
  intro π hfix x
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨π⁻¹ • y, (hR π hfix (x,π⁻¹ • y)).1 ?_⟩
    simpa only [Prod.smul_mk, smul_inv_smul] using hy
  · rintro ⟨y, hy⟩
    exact ⟨π • y, (hR π hfix (x,y)).2 hy⟩

theorem FinitelySupportedPred.all (hR : FinitelySupportedPred A R) :
    FinitelySupportedPred A (fun x => ∀ y, R (x,y)) := by
  obtain ⟨S, hS⟩ := hR
  exact hS.all.finitelySupported

theorem FinitelySupportedPred.ex (hR : FinitelySupportedPred A R) :
    FinitelySupportedPred A (fun x => ∃ y, R (x,y)) := by
  obtain ⟨S, hS⟩ := hR
  exact hS.ex.finitelySupported

/-- A common bound supports universal quantification over an action-free index. -/
theorem SupportsPred.iAll {I : Sort i} {P : I → X → Prop}
    (h : ∀ j, SupportsPred S (P j)) : SupportsPred S (fun x => ∀ j, P j x) :=
  fun π hfix x => forall_congr' (fun j => h j π hfix x)

/-- A common bound supports existential quantification over an action-free index. -/
theorem SupportsPred.iEx {I : Sort i} {P : I → X → Prop}
    (h : ∀ j, SupportsPred S (P j)) : SupportsPred S (fun x => ∃ j, P j x) :=
  fun π hfix x => exists_congr (fun j => h j π hfix x)

end NominalPackage
