import Nominal.Set.Nominal
import Nominal.Set.Freshness

/-!
# Quotient Sets

Given a nominal set `X` and an **equivariant equivalence relation** `∼` on `X`,
the quotient `X/∼` inherits a permutation action and is itself a nominal set.

## Main definitions

* `IsEquivariantSetoid α X s` — typeclass asserting that `s : Setoid X` is equivariant
  with respect to the `FinitePerm α` action: `x ≈ y → π • x ≈ π • y`.
* `instSMulQuotient` — the permutation action on `Quotient s`: `π • ⟦x⟧ = ⟦π • x⟧`.
* `instPermTypeQuotient` — `Quotient s` is a `PermType` (Section 1.7, eq. 1.43).
* `instNominalQuotient` — `Quotient s` is a `Nominal` set (Section 2.9).

## Main results

* `quotient_smul_mk` — `π • ⟦x⟧ = ⟦π • x⟧` (`@[simp]`).
* `quotient_mk_equivariant` — `Quotient.mk s` is equivariant.
* `supp_quotient_mk_le` — `supp ⟦x⟧ ⊆ supp x` (Lemma 2.12(i)).
* `supp_quotient_eq_sInter` — `supp ⟦x⟧ = ⋂ {supp x' | x ≈ x'}` (Proposition 2.30).
* `quotient_lift_equivariant` — lifted functions preserve equivariance.
* `quotient_map_equivariant` — mapped functions preserve equivariance.

## References

* [A. M. Pitts, *Nominal Sets*][Pitts2013], Sections 1.7 and 2.9.
-/

namespace Nominal.Set
open Core MulAction PermType

universe u

/-! ### Equivariant setoids -/

/-- A setoid on a perm-set is **equivariant** when the equivalence relation is
invariant under the permutation action: `x ≈ y → π • x ≈ π • y` for all
`π : FinitePerm α`. This is the condition from Pitts, Section 1.7 that makes
the quotient action `π • [x]_∼ = [π • x]_∼` well-defined. -/
class IsEquivariantSetoid (α : Type*) [Name α] (X : Type*) [PermType α X] (s : Setoid X) : Prop where
  equivariant_rel : ∀ (π : FinitePerm α) {x y : X}, s.r x y → s.r (π • x) (π • y)

section

variable {α : Type u} [Name α] {X : Type u} [PermType α X]
variable {s : Setoid X} [IsEquivariantSetoid α X s]

namespace IsEquivariantSetoid

/-- The backward direction: `s.r (π • x) (π • y) → s.r x y`, obtained by applying `equivariant_rel` to `π⁻¹`. -/
theorem equivariant_rel_rev (π : FinitePerm α) {x y : X} (h : s.r (π • x) (π • y)) : s.r x y := by
  have h' := equivariant_rel π⁻¹ h
  simp only [PermType.inv_smul_smul] at h'
  exact h'

/-- Equivariance as a biconditional: `s.r (π • x) (π • y) ↔ s.r x y`. -/
theorem equivariant_rel_iff (π : FinitePerm α) {x y : X} : s.r (π • x) (π • y) ↔ s.r x y :=
  ⟨equivariant_rel_rev π, equivariant_rel π⟩

/-- Bridge to the project's `EquivariantRel` structure. -/
theorem equivariantRel : EquivariantRel α s.r where
  smul_iff π _ _ := equivariant_rel_iff π

end IsEquivariantSetoid

end

/-! ### Permutation action on quotients (Pitts, Section 1.7, eq. 1.43) -/

section PermAction

variable {α : Type u} [Name α] {X : Type u} [PermType α X]
variable (s : Setoid X) [IsEquivariantSetoid α X s]

/-- The permutation action on `Quotient s`: `π • ⟦x⟧ = ⟦π • x⟧`.
Well-defined because `s` is equivariant. -/
instance instSMulQuotient : SMul (FinitePerm α) (Quotient s) where
  smul π := Quotient.map (π • ·) (fun _ _ h ↦ IsEquivariantSetoid.equivariant_rel π h)

/-- The action on quotient representatives: `π • ⟦x⟧ = ⟦π • x⟧`. -/
@[simp]
theorem quotient_smul_mk (π : FinitePerm α) (x : X) : π • (⟦x⟧ : Quotient s) = ⟦π • x⟧ := rfl

/-! ### PermType instance -/

/-- `Quotient s` is a `PermType` under the lifted action (Section 1.7). -/
instance instPermTypeQuotient : PermType α (Quotient s) where
  one_smul q := by induction q using Quotient.ind with | _ x => simp [one_smul]
  mul_smul π σ q := by induction q using Quotient.ind with | _ x => simp [mul_smul]

/-- The quotient map `Quotient.mk s` is equivariant (Section 1.7, eq. 1.44). -/
theorem quotient_mk_equivariant : IsEquivariant α (Quotient.mk s) where
  map_smul π x := (quotient_smul_mk s π x).symm

end PermAction

/-! ### Nominal instance (Pitts, Section 2.9) -/

section NominalQuotient

variable {α : Type u} [Name α] {X : Type u} [Nominal α X]
variable (s : Setoid X) [IsEquivariantSetoid α X s]

/-- `Quotient s` is a nominal set when `X` is nominal and `s` is equivariant
(Section 2.9). Follows from Lemma 2.12(iii): the surjective equivariant image
of a nominal set is nominal. -/
instance instNominalQuotient : Nominal α (Quotient s) where
  toPermType := instPermTypeQuotient s
  finSupp q := by
    exact finSupported_of_surjective (quotient_mk_equivariant s)
      Quotient.mk_surjective q

/-- `supp ⟦x⟧ ⊆ supp x`: the support of a quotient element is contained in the support of any representative (Lemma 2.12(i)). -/
theorem supp_quotient_mk_le (x : X) : supp (⟦x⟧ : Quotient s) ⊆ supp x :=
  supp_map_le (quotient_mk_equivariant s) x

/-- **Proposition 2.30**: the support of an equivalence class is the intersection
of the supports of all its representatives: `supp ⟦x⟧ = ⋂ {supp x' | x ≈ x'}`.

Stated at the `Set α` level because the intersection ranges over possibly infinitely many representatives. -/
theorem supp_quotient_eq_sInter (x : X) :
    (supp (⟦x⟧ : Quotient s) : Set α) = ⋂ x' ∈ {x' | s.r x x'}, (supp x' : Set α) := by
  ext a
  simp only [Set.mem_iInter, Set.mem_ofPred_eq, Finset.mem_coe]
  constructor
  · -- ⊆: supp ⟦x⟧ ⊆ supp x' for every x' ≈ x
    intro ha x' hxx'
    have : (⟦x⟧ : Quotient s) = ⟦x'⟧ := Quotient.sound hxx'
    rw [this] at ha
    exact supp_quotient_mk_le s x' ha
  · -- ⊇: if a ∈ supp x' for all x' ≈ x, then a ∈ supp ⟦x⟧
    -- Contrapositive: if a ∉ supp ⟦x⟧, find x' ≈ x with a ∉ supp x'
    intro ha
    by_contra ha_not
    -- Choose a' ∉ supp a ∪ supp ⟦x⟧ ∪ supp x (i.e. fresh for (a, ⟦x⟧, x))
    set q : Quotient s := ⟦x⟧
    pick_new a' (supp (α := α) a ∪ supp q ∪ supp x)
    simp only [Finset.mem_union, supp_atom, Finset.mem_singleton] at a'New
    push Not at a'New
    obtain ⟨⟨ha'_ne, ha'_q⟩, ha'_x⟩ := a'New
    -- Since a, a' ∉ supp ⟦x⟧, we have swap a a' • ⟦x⟧ = ⟦x⟧
    have hq : swap a a' • q = q :=
      swap_smul_eq_of_support ha_not ha'_q
    -- So ⟦swap a a' • x⟧ = ⟦x⟧, meaning swap a a' • x ≈ x
    change swap a a' • (⟦x⟧ : Quotient s) = ⟦x⟧ at hq
    rw [quotient_smul_mk] at hq
    have hrel : @Setoid.r _ s x (swap a a' • x) := Quotient.exact hq.symm
    -- Apply our hypothesis: a ∈ supp (swap a a' • x)
    have hmem := ha (swap a a' • x) hrel
    -- But a ∉ supp (swap a a' • x) because a' ∉ supp x
    rw [mem_supp_smul, swap_inv, swap_apply_left] at hmem
    exact ha'_x hmem

end NominalQuotient

/-! ### Equivariance of lifted and mapped functions (Section 1.7) -/

section QuotientLift

variable {α : Type u} [Name α] {X : Type u} [PermType α X]
variable (s : Setoid X) [IsEquivariantSetoid α X s]

/-- If `f : X → Y` is equivariant and respects `∼`, then `Quotient.lift f hf` is equivariant (Section 1.7). -/
theorem quotient_lift_equivariant {Y : Type u} [PermType α Y] {f : X → Y} (hf_equiv : IsEquivariant α f)
    (hf_resp : ∀ x y, @Setoid.r _ s x y → f x = f y) : IsEquivariant α (Quotient.lift f hf_resp) where
  map_smul π q := by
    induction q using Quotient.ind with
    | _ x =>
      simp only [quotient_smul_mk, Quotient.lift_mk]
      exact hf_equiv.map_smul π x

/-- If `f : X → Y` is equivariant and maps `s`-related elements to `t`-related
elements, then `Quotient.map f hf` is equivariant (Section 1.7, generalisation). -/
theorem quotient_map_equivariant {Y : Type u} [PermType α Y] {t : Setoid Y} [IsEquivariantSetoid α Y t]
    {f : X → Y} (hf_equiv : IsEquivariant α f) (hf_resp : ∀ x y, @Setoid.r _ s x y → @Setoid.r _ t (f x) (f y)) :
    IsEquivariant α (Quotient.map f hf_resp) where
  map_smul π q := by
    induction q using Quotient.ind with
    | _ x =>
      simp only [quotient_smul_mk, Quotient.map_mk]
      exact congrArg _ (hf_equiv.map_smul π x)

end QuotientLift

end Nominal.Set
