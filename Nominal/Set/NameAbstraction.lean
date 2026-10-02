import Nominal.Set.NFun
import Nominal.Set.FreshQuantifier

import Mathlib.Data.Finset.Basic

/-!
# Name Abstraction

The **name abstraction** `[A]X` (written `NameAbs α X` in Lean) is the quotient of
`α × X` by **α-equivalence**: two pairs `(a₁, x₁)` and `(a₂, x₂)` are identified
when, for cofinitely many fresh atoms `c`,

    swap a₁ c • x₁ = swap a₂ c • x₂.

This captures the idea of "a name `a` bound in `x`", where the specific choice of
binder name is irrelevant up to consistent renaming.

## Main definitions

* `AlphaEqv a₁ x₁ a₂ x₂` — the α-equivalence relation on `α × X` (eq. 4.7).
* `AlphaSetoid` — the `Setoid` instance on `α × X` induced by `AlphaEqv`.
* `NameAbs α X` — the quotient type `[A]X` (Definition 4.4).
* `abs a x` — the canonical constructor `⟪a⟫ x : NameAbs α X`.
* `NameAbs.ind` — induction principle: every element is `⟪a⟫ x` for some `a`, `x`.
* `NameAbs.ind₂` — binary induction principle.
* `NameAbs.instDecidableAlphaEqv` — decidability of α-equivalence (when `X` has `DecidableEq`).
* `NameAbs.instDecidableEqNameAbs` — decidable equality on `NameAbs α X` (when `X` has `DecidableEq`).

## Notation

* `⟪a⟫ x` — scoped notation for `abs a x`.

## Instances

* `NameAbs.instSMul` — permutation action: `π • ⟪a⟫ x = ⟪π • a⟫ (π • x)`.
* `NameAbs.instPermType` — `NameAbs α X` is a `PermType`.
* `NameAbs.instNominal` — `NameAbs α X` is a nominal set (Proposition 4.5).

## Main results

### α-Equivalence
* `alphaEqv_refl` — α-equivalence is reflexive.
* `alphaEqv_symm` — α-equivalence is symmetric.
* `alphaEqv_trans` — α-equivalence is transitive.
* `alphaEqv_equivariant` — α-equivalence is preserved by the permutation action.
* `alphaEqv_iff_abs_eq` — `AlphaEqv a₁ x₁ a₂ x₂ ↔ ⟪a₁⟫ x₁ = ⟪a₂⟫ x₂`.

### Equality characterisations (Pitts, Lemmas 4.2 and 4.3)
* `abs_eq_iff_freshQuantifier` — `⟪a₁⟫ x₁ = ⟪a₂⟫ x₂ ↔ И c, swap a₁ c • x₁ = swap a₂ c • x₂`.
* `abs_same_name_iff` — same-binder injectivity: `⟪a⟫ x₁ = ⟪a⟫ x₂ ↔ x₁ = x₂`.
* `abs_eq_iff` — full equality characterisation (Lemma 4.3).
* `abs_eq_iff_of_ne` — `⟪a₁⟫ x₁ = ⟪a₂⟫ x₂ ↔ a₁ # x₂ ∧ x₁ = swap a₁ a₂ • x₂` when `a₁ ≠ a₂`.
* `abs_eq_iff_of_fresh` — `⟪a₁⟫ x₁ = ⟪a₂⟫ x₂ ↔ x₁ = swap a₁ a₂ • x₂` when `a₁ ≠ a₂` and `a₁ # x₂`.
* `abs_eq_iff_exists` — equality via an existential fresh witness (eq. 4.8).
* `abs_eq_iff_forall` — equality via a universal fresh witness (eq. 4.8).

### Action and support (Pitts, Definition 4.4, Proposition 4.5)
* `abs_equivariant` — `π • ⟪a⟫ x = ⟪π • a⟫ (π • x)` (eq. 4.10).
* `swap_smul_abs` — `swap a b • ⟪a⟫ x = ⟪b⟫ (swap a b • x)`.
* `supp_abs` — `supp (⟪a⟫ x) = supp x \ {a}` (Proposition 4.5).
* `supp_abs_subset` — `supp (⟪a⟫ x) ⊆ supp x`.
* `supp_abs_ssubset` — `supp (⟪a⟫ x) ⊂ supp (a, x)`.
* `abs_supports_sdiff` — `supp x \ {a}` supports `⟪a⟫ x`.
* `supports_body_of_supports_abs` — if `s` supports `⟪a⟫ x`, then `s ∪ {a}` supports `x`.

### Freshness (eq. 4.11)
* `fresh_abs` — `a' # ⟪a⟫ x ↔ a' = a ∨ a' # x`.
* `fresh_binder_abs` — the binder is always fresh for its own abstraction: `a # ⟪a⟫ x`.
* `fresh_abs_of_ne` — if `a' # ⟪a⟫ x` and `a' ≠ a`, then `a' # x`.
* `supp_abs_eq_empty_iff` — `supp ⟪a⟫ x = ∅ ↔ supp x ⊆ {a}`.
* `abs_rename` — `a # x` and `b # x` imply `⟪a⟫ x = ⟪b⟫ x`.
* `abs_eq_swap` — `b # x` implies `⟪a⟫ x = ⟪b⟫ (swap a b • x)`.

### Fresh representatives and binary induction
* `exists_fresh_rep` — every abstraction has a representative with binder fresh for `z`.
* `exists_fresh_rep₂` — every pair of abstractions shares a common binder fresh for `z`.
* `ind_someAny_forall` — induction choosing a representative fresh for a given `z`.
* `ind₂` — binary induction on two abstractions.
* `abs_injective` — `abs a` is injective.
* `abs_surjective` — the uncurried constructor `abs` is surjective.

The freshness condition for binders (Theorem 4.15, Corollary 4.17) and structural
properties of `[A]_` live in `FCB.lean`.

## References

* [A. M. Pitts, *Nominal Sets*][Pitts2013], Chapter 4, Sections 4.1–4.3.
-/

namespace Nominal.Set
open Core

open MulAction PermType

universe u

variable {α : Type u} [Name α] {X : Type u} [Nominal α X]

/-! ### α-Equivalence (Pitts, Section 4.2, eq. 4.7) -/

/-- **α-equivalence** on `α × X`: two pairs `(a₁, x₁)` and `(a₂, x₂)` are α-equivalent
when, for cofinitely many atoms `c`, `swap a₁ c • x₁ = swap a₂ c • x₂`. -/
def AlphaEqv (a₁ : α) (x₁ : X) (a₂ : α) (x₂ : X) : Prop := И c, swap a₁ c • x₁ = swap a₂ c • x₂

/-- α-equivalence is reflexive. -/
theorem alphaEqv_refl (a : α) (x : X) : AlphaEqv a x a x :=
  freshQuantifier_of_forall (fun _ ↦ rfl)

/-- α-equivalence is symmetric. -/
theorem alphaEqv_symm {a₁ a₂ : α} {x₁ x₂ : X} (h : AlphaEqv a₁ x₁ a₂ x₂) : AlphaEqv a₂ x₂ a₁ x₁ :=
  freshQuantifier_mono (fun _ h ↦ h.symm) h

/-- α-equivalence is transitive. -/
theorem alphaEqv_trans {a₁ a₂ a₃ : α} {x₁ x₂ x₃ : X} (h₁₂ : AlphaEqv a₁ x₁ a₂ x₂) (h₂₃ : AlphaEqv a₂ x₂ a₃ x₃) : AlphaEqv a₁ x₁ a₃ x₃ := by
  have h := freshQuantifier_and.mpr ⟨h₁₂, h₂₃⟩
  exact freshQuantifier_mono (fun c ⟨h1, h2⟩ ↦ h1.trans h2) h

/-- The setoid on `α × X` induced by α-equivalence. -/
instance AlphaSetoid : Setoid (α × X) where
  r := fun p q ↦ AlphaEqv p.1 p.2 q.1 q.2
  iseqv := {
    refl := fun p ↦ alphaEqv_refl p.1 p.2
    symm := fun h ↦ alphaEqv_symm h
    trans := fun h₁ h₂ ↦ alphaEqv_trans h₁ h₂
  }

/-! ### The quotient type and constructor (Pitts, Definition 4.4) -/

/-- **Name abstraction**: the quotient of `α × X` by α-equivalence.
Represents "a name `a` bound in `x`", up to consistent renaming. -/
def NameAbs (α : Type u) [Name α] (X : Type u) [Nominal α X] : Type u := Quotient (AlphaSetoid (α := α) (X := X))

/-- Construct a name abstraction from a binder `a` and a body `x`. -/
def abs (a : α) (x : X) : NameAbs α X := Quotient.mk (AlphaSetoid (α := α) (X := X)) (a, x)

/-- Notation: `⟪a⟫ x` for `abs a x`. -/
scoped notation:max "⟪" a "⟫" x:arg => abs a x

namespace NameAbs

/-- Every name abstraction is of the form `abs a x`. -/
@[elab_as_elim]
theorem ind {P : NameAbs α X → Prop} (h : ∀ a x, P ⟪a⟫x) : ∀ F, P F := Quotient.ind (fun ⟨a, x⟩ ↦ h a x)

/-! ### Equality characterisation (Pitts, Lemmas 4.2 and 4.3) -/

/-- α-equivalence is equivariant: if `AlphaEqv a₁ x₁ a₂ x₂`, then
`AlphaEqv (π • a₁) (π • x₁) (π • a₂) (π • x₂)`. -/
theorem alphaEqv_equivariant {a₁ a₂ : α} {x₁ x₂ : X} (π : FinitePerm α) (h : AlphaEqv a₁ x₁ a₂ x₂) : AlphaEqv (π • a₁) (π • x₁) (π • a₂) (π • x₂) := by
  simp only [AlphaEqv, freshQuantifier_iff] at h ⊢
  -- The bad set for π maps to bad set: {d | ¬…} ⊆ π '' {c | ¬…}
  apply Set.Finite.subset (h.image (π : α → α))
  intro d hd
  simp only [Set.mem_ofPred_eq] at hd
  -- Witness c = π⁻¹ • d, so π • c = d
  refine ⟨π⁻¹ • d, ?_, PermType.smul_inv_smul π d⟩
  intro heq
  apply hd
  conv_lhs => rw [show d = π • (π⁻¹ • d) from (PermType.smul_inv_smul π d).symm]
  conv_rhs => rw [show d = π • (π⁻¹ • d) from (PermType.smul_inv_smul π d).symm]
  rw [swap_smul_equivariant, swap_smul_equivariant]
  exact congrArg (π • ·) heq

/-- Equality via the freshness quantifier (eq. 4.7 / 4.8):
`⟪a₁⟫ x₁ = ⟪a₂⟫ x₂ ↔ (И c, swap a₁ c • x₁ = swap a₂ c • x₂)`. -/
theorem abs_eq_iff_freshQuantifier {a₁ a₂ : α} {x₁ x₂ : X} : ⟪a₁⟫x₁ = ⟪a₂⟫x₂ ↔ (И c, swap a₁ c • x₁ = swap a₂ c • x₂) :=
  ⟨fun h ↦ Quotient.exact h, fun h ↦ Quotient.sound h⟩

/-- Bridge between `AlphaEqv` and quotient equality:
`AlphaEqv a₁ x₁ a₂ x₂ ↔ ⟪a₁⟫ x₁ = ⟪a₂⟫ x₂`. -/
theorem alphaEqv_iff_abs_eq {a₁ a₂ : α} {x₁ x₂ : X} : AlphaEqv a₁ x₁ a₂ x₂ ↔ ⟪a₁⟫x₁ = ⟪a₂⟫x₂ :=
  abs_eq_iff_freshQuantifier.symm

/-- Same-binder injectivity: `⟪a⟫ x₁ = ⟪a⟫ x₂ ↔ x₁ = x₂` (Lemma 4.2). -/
@[simp]
theorem abs_same_name_iff {a : α} {x₁ x₂ : X} : ⟪a⟫x₁ = ⟪a⟫x₂ ↔ x₁ = x₂ := by
  rw [abs_eq_iff_freshQuantifier]
  -- goal: AlphaEqv a x₁ a x₂ ↔ x₁ = x₂
  constructor
  · intro h
    -- h : И c, swap a c • x₁ = swap a c • x₂; pick any such c
    obtain ⟨c, hc⟩ := freshQuantifier_exists h
    -- swap a c is an involution: apply it to both sides
    have := congr_arg (swap a c • ·) hc
    simp only [smul_smul, swap_mul_self, one_smul] at this
    exact this
  · rintro rfl
    exact alphaEqv_refl a x₁

/-- Full equality characterisation (Lemma 4.3):
`⟪a₁⟫ x₁ = ⟪a₂⟫ x₂` iff either `a₁ = a₂ ∧ x₁ = x₂`, or `a₁ ≠ a₂` with
`a₁ # (a₂, x₂)` and `x₁ = swap a₁ a₂ • x₂`. -/
theorem abs_eq_iff {a₁ a₂ : α} {x₁ x₂ : X} :
    ⟪a₁⟫x₁ = ⟪a₂⟫x₂ ↔ (a₁ = a₂ ∧ x₁ = x₂) ∨ (a₁ ≠ a₂ ∧ a₁ # (a₂, x₂) ∧ x₁ = swap a₁ a₂ • x₂) := by
  constructor
  · -- Forward: abs a₁ x₁ = abs a₂ x₂ → ...
    intro h
    by_cases heq : a₁ = a₂
    · -- Case a₁ = a₂
      subst heq; left; exact ⟨rfl, abs_same_name_iff.mp h⟩
    · -- Case a₁ ≠ a₂: get witness c # (a₁, x₁, a₂, x₂) with swap equation
      right
      obtain ⟨c, hswap_eq, hcfresh⟩ := freshQuantifier_exists
        (freshQuantifier_and.mpr ⟨Quotient.exact h, fresh_atom_cofinite (a₁, x₁, a₂, x₂)⟩)
      simp only [fresh_prod_right, fresh_atoms] at hcfresh
      obtain ⟨hca₁, hcx₁, hca₂, hcx₂⟩ := hcfresh
      -- a₁ # x₂: if a₁ ∈ supp x₂ then a₁ ∈ supp (swap a₂ c • x₂) = supp (swap a₁ c • x₁),
      -- but a₁ ∉ supp (swap a₁ c • x₁) since swap sends a₁ ↦ c and c ∉ supp x₁.
      have ha₁x₂ : a₁ # x₂ := by
        rw [fresh_atom_left]; intro ha₁_supp
        have h₁ : a₁ ∉ supp (swap a₁ c • x₁) := by
          rw [mem_supp_smul, swap_inv, swap_apply_left]
          exact (fresh_atom_left c x₁).mp hcx₁
        have h₂ : a₁ ∈ supp (swap a₂ c • x₂) := by
          rw [mem_supp_smul, swap_inv]
          convert ha₁_supp using 1
          exact swap_apply_of_ne heq (Ne.symm hca₁)
        exact h₁ (hswap_eq ▸ h₂)
      refine ⟨heq, fresh_prod_right.mpr ⟨(fresh_atoms a₁ a₂).mpr heq, ha₁x₂⟩, ?_⟩
      -- x₁ = swap a₁ a₂ • x₂ via three-cycle factorisation
      have hperm : swap a₁ c * swap a₂ c = swap a₁ a₂ * swap a₁ c := by
        have := (swap_triple_factorization heq (Ne.symm hca₁) (Ne.symm hca₂)).symm
        rw [← this, mul_assoc, swap_mul_self, mul_one]
      calc x₁ = swap a₁ c • swap a₁ c • x₁ := by rw [← mul_smul, swap_mul_self, one_smul]
        _ = (swap a₁ c * swap a₂ c) • x₂   := by rw [hswap_eq, mul_smul]
        _ = swap a₁ a₂ • swap a₁ c • x₂    := by rw [hperm, mul_smul]
        _ = swap a₁ a₂ • x₂                := by rw [fresh_swap ha₁x₂ hcx₂]
  · -- Backward: ... → abs a₁ x₁ = abs a₂ x₂
    rintro (⟨rfl, rfl⟩ | ⟨hne, hfresh, rfl⟩)
    · rfl
    · -- a₁ ≠ a₂, a₁ # (a₂, x₂), x₁ = swap a₁ a₂ • x₂
      -- Need: И c, swap a₁ c • swap a₁ a₂ • x₂ = swap a₂ c • x₂
      simp only [fresh_prod_right, fresh_atoms] at hfresh
      obtain ⟨_, ha₁x₂⟩ := hfresh
      apply Quotient.sound
      change AlphaEqv a₁ (swap a₁ a₂ • x₂) a₂ x₂
      unfold AlphaEqv
      apply freshQuantifier_mono _ (fresh_atom_cofinite (swap a₁ a₂ • x₂, a₁, a₂, x₂))
      intro c hcfresh
      simp only [fresh_prod_right, fresh_atoms] at hcfresh
      obtain ⟨_, hca₁, hca₂, hcx₂⟩ := hcfresh
      have hperm : swap a₁ c * swap a₁ a₂ = swap a₂ c * swap a₁ c := by
        apply Subtype.ext; apply Equiv.Perm.ext; intro d
        simp only [swap_coe, Subgroup.coe_mul, Equiv.Perm.mul_apply, Equiv.swap_apply_def]
        split_ifs <;> simp_all
      rw [← mul_smul, hperm, mul_smul, fresh_swap ha₁x₂ hcx₂]

/-- When binders differ: `⟪a₁⟫ x₁ = ⟪a₂⟫ x₂ ↔ a₁ # x₂ ∧ x₁ = swap a₁ a₂ • x₂`. Simplification of `abs_eq_iff` when `a₁ ≠ a₂`. -/
theorem abs_eq_iff_of_ne {a₁ a₂ : α} {x₁ x₂ : X} (hne : a₁ ≠ a₂) : ⟪a₁⟫x₁ = ⟪a₂⟫x₂ ↔ a₁ # x₂ ∧ x₁ = swap a₁ a₂ • x₂ := by
  rw [abs_eq_iff]
  constructor
  · rintro (⟨rfl, _⟩ | ⟨_, hfresh, hswap⟩)
    · exact absurd rfl hne
    · exact ⟨fresh_prod_right.mp hfresh |>.2, hswap⟩
  · rintro ⟨hfresh, hswap⟩
    exact .inr ⟨hne, fresh_prod_right.mpr ⟨(fresh_atoms a₁ a₂).mpr hne, hfresh⟩, hswap⟩

/-- When `a₁ # x₂` is already known and `a₁ ≠ a₂`: `⟪a₁⟫ x₁ = ⟪a₂⟫ x₂ ↔ x₁ = swap a₁ a₂ • x₂`. -/
theorem abs_eq_iff_of_fresh {a₁ a₂ : α} {x₁ x₂ : X} (hne : a₁ ≠ a₂) (hfresh : a₁ # x₂) :
    ⟪a₁⟫x₁ = ⟪a₂⟫x₂ ↔ x₁ = swap a₁ a₂ • x₂ := by
  rw [abs_eq_iff_of_ne hne]
  exact ⟨And.right, fun h ↦ ⟨hfresh, h⟩⟩

/-! ### Permutation action (Pitts, Definition 4.4, eq. 4.10) -/

/-- The permutation action on name abstractions: `π • ⟪a⟫ x = ⟪π • a⟫ (π • x)` (eq. 4.10). -/
instance instSMul : SMul (FinitePerm α) (NameAbs α X) where
  smul := fun π F ↦ Quotient.liftOn F
    (fun ⟨a, x⟩ ↦ ⟪(π • a)⟫(π • x))
    (fun ⟨a₁, x₁⟩ ⟨a₂, x₂⟩ h ↦ by
      simp only
      rw [abs_eq_iff_freshQuantifier]
      exact alphaEqv_equivariant π h)

@[simp]
theorem abs_equivariant (π : FinitePerm α) (a : α) (x : X) : π • ⟪a⟫x = ⟪(π • a)⟫(π • x) := rfl

/-- Swap action on abstraction specialized to the binder: `swap a b • ⟪a⟫ x = ⟪b⟫ (swap a b • x)`. -/
@[simp]
theorem swap_smul_abs (a b : α) (x : X) :
    swap a b • ⟪a⟫x = ⟪b⟫(swap a b • x) := by
  simp

/-- `NameAbs α X` is a `PermType` under the lifted permutation action. -/
instance instPermType : PermType α (NameAbs α X) where
  one_smul F := by induction F using ind with | _ a x => simp [one_smul]
  mul_smul π σ F := by induction F using ind with | _ a x => simp [mul_smul]

/-! ### Support and Nominal instance (Pitts, Proposition 4.5) -/

/-- If `s` supports `⟪a⟫ x`, then `s ∪ {a}` supports `x`. -/
theorem supports_body_of_supports_abs {a : α} {x : X} {s : Finset α} (hs : supports s ⟪a⟫x) : supports (s ∪ {a}) x := by
  rw [supports_iff_swap] at hs ⊢
  intro a₁ a₂ ha₁ ha₂
  simp only [Finset.mem_union, Finset.mem_singleton, not_or] at ha₁ ha₂
  have hsabs := hs a₁ a₂ ha₁.1 ha₂.1
  simp only [abs_equivariant] at hsabs
  have hfix_a : (swap a₁ a₂) • a = a := swap_apply_of_ne (Ne.symm ha₁.2) (Ne.symm ha₂.2)
  rw [hfix_a] at hsabs
  exact abs_same_name_iff.mp hsabs

/-- `supp x \ {a}` supports `⟪a⟫ x`. -/
theorem abs_supports_sdiff (a : α) (x : X) : supports (supp x \ {a}) ⟪a⟫x := by
  rw [supports_iff_swap]
  intro a₁ a₂ ha₁ ha₂
  simp only [Finset.mem_sdiff, Finset.mem_singleton, not_and, not_not] at ha₁ ha₂
  -- ha₁ : a₁ ∈ supp x → a₁ = a,  ha₂ : a₂ ∈ supp x → a₂ = a
  simp only [abs_equivariant]
  -- Derive freshness from ∉ supp x (contrapositive of haᵢ)
  have hfresh₁ : a₁ ≠ a → a₁ # x := fun h ↦ (fresh_atom_left a₁ x).mpr (mt ha₁ h)
  have hfresh₂ : a₂ ≠ a → a₂ # x := fun h ↦ (fresh_atom_left a₂ x).mpr (mt ha₂ h)
  by_cases hne₁ : a₁ = a <;> by_cases hne₂ : a₂ = a
  · -- a₁ = a, a₂ = a
    simp [hne₁, hne₂]
  · -- a₁ = a, a₂ ≠ a
    rw [hne₁, swap_apply_left, abs_eq_iff]
    exact .inr ⟨hne₂, fresh_prod_right.mpr ⟨(fresh_atoms a₂ a).mpr hne₂, hfresh₂ hne₂⟩,
      by rw [swap_comm]⟩
  · -- a₁ ≠ a, a₂ = a
    rw [hne₂, swap_apply_right, abs_eq_iff]
    exact .inr ⟨hne₁, fresh_prod_right.mpr ⟨(fresh_atoms a₁ a).mpr hne₁, hfresh₁ hne₁⟩, rfl⟩
  · -- a₁ ≠ a, a₂ ≠ a
    rw [swap_apply_of_ne (Ne.symm hne₁) (Ne.symm hne₂), fresh_swap (hfresh₁ hne₁) (hfresh₂ hne₂)]

/-- `NameAbs α X` is a nominal set (Proposition 4.5). -/
instance instNominal : Nominal α (NameAbs α X) where
  toPermType := instPermType
  finSupp := by
    intro F
    induction F using ind with | _ a x => exact ⟨supp x \ {a}, abs_supports_sdiff a x⟩

/-- `supp (⟪a⟫ x) = supp x \ {a}` (Proposition 4.5, eq. 4.11). -/
@[simp]
theorem supp_abs (a : α) (x : X) : supp ⟪a⟫x = supp x \ {a} := by
  apply Finset.Subset.antisymm
  · -- supp (abs a x) ⊆ supp x \ {a}: abs_supports_sdiff gives the support directly
    exact supp_le (abs_supports_sdiff a x)
  · -- supp x \ {a} ⊆ supp (abs a x): if b ≠ a and b ∈ supp x, then b ∈ every support of abs a x
    intro b hb
    simp only [Finset.mem_sdiff, Finset.mem_singleton] at hb
    rw [mem_supp]
    intro s hs
    -- s ∪ {a} supports x (by supports_body_of_supports_abs), so b ∈ s ∪ {a}, so b ∈ s
    have hsa : supports (s ∪ {a}) x := supports_body_of_supports_abs hs
    have hbsa : b ∈ s ∪ {a} := supp_le hsa (mem_supp.mpr (fun t ht ↦ supp_le ht hb.1))
    simp only [Finset.mem_union, Finset.mem_singleton] at hbsa
    exact hbsa.resolve_right hb.2

/-- `a' # ⟪a⟫ x ↔ a' = a ∨ a' # x` (eq. 4.11). -/
@[simp]
theorem fresh_abs {a a' : α} {x : X} : a' # ⟪a⟫x ↔ a' = a ∨ a' # x := by
  simp only [fresh_atom_left, supp_abs, Finset.mem_sdiff, Finset.mem_singleton, not_and, not_not,
    fresh_atom_left]
  tauto

/-- If `a'` is fresh for `⟪a⟫ x` and `a' ≠ a`, then `a'` is fresh for `x`.
Extraction from `fresh_abs` for the `a' ≠ a` case. -/
theorem fresh_abs_of_ne {a a' : α} {x : X} (habs : a' # ⟪a⟫x) (hne : a' ≠ a) : a' # x :=
  (fresh_abs.mp habs).resolve_left hne

/-- The abstraction `⟪a⟫ x` has empty support iff `supp x ⊆ {a}`. -/
theorem supp_abs_eq_empty_iff {a : α} {x : X} : supp ⟪a⟫x = ∅ ↔ supp x ⊆ {a} := by
  simp [Finset.sdiff_eq_empty_iff_subset]

/-- `supp (⟪a⟫ x) ⊆ supp x`: the support of an abstraction is contained in
the support of the body. Weaker than `supp_abs` but sometimes more convenient. -/
theorem supp_abs_subset (a : α) (x : X) : supp ⟪a⟫x ⊆ supp x := by simp [Finset.sdiff_subset]

/-! ### Equality via ∃ and ∀ (Pitts, eq. 4.8) -/

/-- Equality of abstractions via ∃ (Some/Any, eq. 4.8):
`⟪a₁⟫ x₁ = ⟪a₂⟫ x₂ ↔ ∃ c # (a₁, x₁, a₂, x₂), swap a₁ c • x₁ = swap a₂ c • x₂`. -/
theorem abs_eq_iff_exists {a₁ a₂ : α} {x₁ x₂ : X} :
    ⟪a₁⟫x₁ = ⟪a₂⟫x₂ ↔ ∃ c, c # (a₁, x₁, a₂, x₂) ∧ swap a₁ c • x₁ = swap a₂ c • x₂ := by
  constructor
  · intro h
    exact freshQuantifier_exists
      (freshQuantifier_and.mpr ⟨fresh_atom_cofinite _, abs_eq_iff_freshQuantifier.mp h⟩)
  · intro ⟨c, hcfresh, hceq⟩
    rw [abs_eq_iff_freshQuantifier]
    exact someAny_freshQuantifier_of_forall
      (someAny_forall_of_exists equivariantRel_swap_smul_eq ⟨c, hcfresh, hceq⟩)

/-- Equality of abstractions via ∀ (Some/Any, eq. 4.8):
`⟪a₁⟫ x₁ = ⟪a₂⟫ x₂ ↔ ∀ c, c # (a₁, x₁, a₂, x₂) → swap a₁ c • x₁ = swap a₂ c • x₂`. -/
theorem abs_eq_iff_forall {a₁ a₂ : α} {x₁ x₂ : X} :
    ⟪a₁⟫x₁ = ⟪a₂⟫x₂ ↔ ∀ c, c # (a₁, x₁, a₂, x₂) → swap a₁ c • x₁ = swap a₂ c • x₂ := by
  constructor
  · intro h
    obtain ⟨c, hcfresh, hceq⟩ := abs_eq_iff_exists.mp h
    exact someAny_forall_of_exists equivariantRel_swap_smul_eq ⟨c, hcfresh, hceq⟩
  · intro hAll
    obtain ⟨c, hcfresh⟩ := freshQuantifier_exists (fresh_atom_cofinite (a₁, x₁, a₂, x₂))
    exact abs_eq_iff_exists.mpr ⟨c, hcfresh, hAll c hcfresh⟩

/-! ### Utility lemmas -/

/-- Instantiate `abs_eq_iff_forall` at a specific fresh witness `c`.
Extracts `swap a₁ c • x₁ = swap a₂ c • x₂` directly from `⟪a₁⟫x₁ = ⟪a₂⟫x₂`. -/
theorem abs_eq_mp_at {a₁ a₂ : α} {x₁ x₂ : X} (h : ⟪a₁⟫x₁ = ⟪a₂⟫x₂)
    {c : α} (hc : c # (a₁, x₁, a₂, x₂)) : swap a₁ c • x₁ = swap a₂ c • x₂ :=
  abs_eq_iff_forall.mp h c hc

/-- Introduce an abstraction equality from a swap equality at a fresh witness.
Converse of `abs_eq_mp_at`. -/
theorem abs_eq_of_swap {a₁ a₂ : α} {x₁ x₂ : X}
    {c : α} (hc : c # (a₁, x₁, a₂, x₂)) (h : swap a₁ c • x₁ = swap a₂ c • x₂) :
    ⟪a₁⟫x₁ = ⟪a₂⟫x₂ :=
  abs_eq_iff_exists.mpr ⟨c, hc, h⟩

/-- The binder is always fresh for its own abstraction. -/
@[simp]
theorem fresh_binder_abs (a : α) (x : X) : a # ⟪a⟫x := by simp [supp_abs]

/-- Two binders that are both fresh for `x` give the same abstraction: `⟪a⟫ x = ⟪b⟫ x` when `a # x` and `b # x`. -/
theorem abs_rename {a b : α} {x : X} (ha : a # x) (hb : b # x) : ⟪a⟫x = ⟪b⟫x := by
  by_cases hab : a = b
  · simp [hab]
  · rw [abs_eq_iff]
    exact .inr ⟨hab, fresh_prod_right.mpr ⟨(fresh_atoms a b).mpr hab, ha⟩,
      (fresh_swap ha hb).symm⟩

/-- Binder renaming via swap: `⟪a⟫ x = ⟪b⟫ (swap a b • x)` when `b # x`. Directed form of one case of `abs_eq_iff`. Does not require `a # x`. -/
theorem abs_eq_swap {a b : α} {x : X} (hb : b # x) : ⟪a⟫x = ⟪b⟫(swap a b • x) := by
  by_cases hab : a = b
  · simp [hab]
  · rw [abs_eq_iff_of_ne hab]
    refine ⟨?_, (swap_smul_swap_smul a b x).symm⟩
    rw [fresh_smul_left, swap_inv, swap_apply_left]
    exact hb

/-- Support of an abstraction is strictly smaller than that of the pair, when `a` actually occurs in `supp x`. -/
theorem supp_abs_ssubset {a : α} {x : X} : supp ⟪a⟫x ⊂ supp (a, x) := by
  simp only [supp_abs, supp_prod, supp_atom]
  constructor
  · exact Finset.sdiff_subset.trans Finset.subset_union_right
  · intro h
    have := h (Finset.mem_union_left _ (Finset.mem_singleton_self a))
    simp at this

/-- Choose a representative with binder fresh for any given `z` (Lemma 4.24). Every abstraction `F` can be written as `⟪a⟫ x` with `a # z`. -/
theorem exists_fresh_rep (F : NameAbs α X) {Z : Type u} [Nominal α Z] (z : Z) : ∃ a x, a # z ∧ F = ⟪a⟫x := by
  induction F using ind with | _ a x =>
  -- Pick b ∉ supp z ∪ supp x ∪ {a}; so b # z, b # x, and b ≠ a
  pick_new b (supp z ∪ supp x ∪ {a})
  simp only [Finset.mem_union, Finset.mem_singleton, not_or] at bNew
  obtain ⟨⟨hbz, hbx⟩, hba⟩ := bNew
  refine ⟨b, swap a b • x, (fresh_atom_left b z).mpr hbz, ?_⟩
  -- Show ⟪a⟫x = ⟪b⟫(swap a b • x) via abs_eq_iff (second case: a ≠ b)
  rw [abs_eq_iff]
  refine .inr ⟨Ne.symm hba, fresh_prod_right.mpr ⟨(fresh_atoms a b).mpr (Ne.symm hba), ?_⟩,
    (swap_smul_swap_smul a b x).symm⟩
  -- a # (swap a b • x): rewrite as (swap a b • a) # (swap a b • (swap a b • x)), i.e. b # x
  rw [show (swap a b • x) = (swap a b) • x from rfl,
      ← fresh_equivariant_iff (swap a b) (x := a) (y := (swap a b) • x),
      swap_apply_left, swap_smul_swap_smul]
  exact (fresh_atom_left b x).mpr hbx

/-- Induction with freshness side-condition (∀ form): for any `z`, every element of `NameAbs α X` can be written `⟪a⟫ x` with `a # z`. -/
@[elab_as_elim]
theorem ind_someAny_forall {P : NameAbs α X → Prop} {Z : Type u} [Nominal α Z] (z : Z) (h : ∀ a x, a # z → P ⟪a⟫x) : ∀ F, P F := by
  intro F
  obtain ⟨a, x, haz, rfl⟩ := exists_fresh_rep F z
  exact h a x haz

/-! ### Binary induction and surjectivity -/

/-- Binary induction on `NameAbs`: every pair of abstractions is of the form `(⟪a⟫ x, ⟪b⟫ y)` for some `a, x, b, y`. -/
@[elab_as_elim]
theorem ind₂ {P : NameAbs α X → NameAbs α X → Prop} (h : ∀ a₁ x₁ a₂ x₂, P ⟪a₁⟫x₁ ⟪a₂⟫x₂) : ∀ F G, P F G :=
  fun F G ↦ ind (fun a x ↦ ind (fun b y ↦ h a x b y) G) F

/-- Every pair of abstractions `F, G` can be written `⟪a⟫ x`, `⟪a⟫ y` with a common binder `a # z`. Combines two applications of `exists_fresh_rep`. -/
theorem exists_fresh_rep₂ (F G : NameAbs α X) {Z : Type u} [Nominal α Z] (z : Z) :
    ∃ a x y, a # z ∧ F = ⟪a⟫x ∧ G = ⟪a⟫y := by
  obtain ⟨a, x, haz, rfl⟩ := exists_fresh_rep F (z, G)
  have haG : a # G := (fresh_prod_right.mp haz).2
  have haz' : a # z := (fresh_prod_right.mp haz).1
  induction G using ind with | _ b y =>
  rw [fresh_abs] at haG
  obtain rfl | hay := haG
  · exact ⟨a, x, y, haz', rfl, rfl⟩
  · exact ⟨a, x, swap b a • y, haz', rfl, abs_eq_swap hay⟩

/-- `abs a` is injective: `⟪a⟫ x₁ = ⟪a⟫ x₂ → x₁ = x₂`. `Function.Injective` form of `abs_same_name_iff`. -/
theorem abs_injective (a : α) : Function.Injective (abs a : X → NameAbs α X) :=
  fun _ _ h ↦ abs_same_name_iff.mp h

/-- The constructor `abs` (uncurried) is surjective. -/
theorem abs_surjective : Function.Surjective (fun p : α × X ↦ abs p.1 p.2) :=
  fun F ↦ ind (fun a x ↦ ⟨(a, x), rfl⟩) F

/-! ### Decidability -/

/-- α-equivalence is decidable when the body type has decidable equality.
Picks a fresh witness `c` and checks `swap a₁ c • x₁ = swap a₂ c • x₂`; by Some/Any (Pitts 3.9), one fresh witness suffices. -/
noncomputable instance instDecidableAlphaEqv [DecidableEq X] (a₁ : α) (x₁ : X) (a₂ : α) (x₂ : X) : Decidable (AlphaEqv a₁ x₁ a₂ x₂) :=
  let c := Classical.choose (supp (a₁, x₁, a₂, x₂)).exists_notMem
  let hc := Classical.choose_spec (supp (a₁, x₁, a₂, x₂)).exists_notMem
  let hfresh : c # (a₁, x₁, a₂, x₂) := (fresh_atom_left c _).mpr hc
  if h : swap a₁ c • x₁ = swap a₂ c • x₂ then
    isTrue (abs_eq_iff_freshQuantifier.mp (abs_eq_iff_exists.mpr ⟨c, hfresh, h⟩))
  else
    isFalse (fun hα ↦ h (abs_eq_iff_forall.mp (abs_eq_iff_freshQuantifier.mpr hα) c hfresh))

/-- `NameAbs α X` has decidable equality when `X` does. -/
noncomputable instance instDecidableEqNameAbs [DecidableEq X] : DecidableEq (NameAbs α X) :=
  fun F G ↦ Quotient.recOnSubsingleton₂ F G fun ⟨a₁, x₁⟩ ⟨a₂, x₂⟩ ↦
    decidable_of_iff (AlphaEqv a₁ x₁ a₂ x₂) abs_eq_iff_freshQuantifier.symm

/-- Parametric abstraction uniqueness: given two derivations at alpha-equivalent
binder-body pairs (via a relation `R` equivariant for swaps fixing `A`),
relates their outputs via NameAbs equality.

This captures the common lam-case pattern from uniqueness proofs (e.g.,
`RecRel.unique`). The caller provides:
- `swap_equiv`: proof that `R` is equivariant for swaps `(a, b)` with `a, b # A`
- `ha, hb`: freshness of the two binders w.r.t. `A`
- `habs`: the binder-body pairs are alpha-equivalent (`⟪a⟫u = ⟪b⟫w`)
- `hw`: a derivation at the second body `w`
- `ih`: the uniqueness IH at the first body `u` -/
theorem abs_unique_parametric
    {X Y : Type u} [Nominal α X] [Nominal α Y]
    {R : Finset α → X → Y → Prop}
    (swap_equiv : ∀ {A : Finset α} {a b : α}, a # A → b # A →
      ∀ {t y}, R A t y → R A (swap a b • t) (swap a b • y))
    {A : Finset α} {a b : α} {u w : X} {u' w' : Y}
    (ha : a # A) (hb : b # A)
    (habs : (⟪a⟫u : NameAbs α X) = ⟪b⟫w)
    (hw : R A w w')
    (ih : ∀ {y₂}, R A u y₂ → u' = y₂) :
    (⟪a⟫u' : NameAbs α Y) = ⟪b⟫w' := by
  choose_fresh c from A a u b w u' w'
  have hc_in : c # (a, u, b, w) :=
    fresh_prod_right.mpr ⟨cFresh2, fresh_prod_right.mpr ⟨cFresh3,
      fresh_prod_right.mpr ⟨cFresh4, cFresh5⟩⟩⟩
  have habs_c := abs_eq_mp_at habs hc_in
  have hse := swap_equiv ha cFresh1 (habs_c ▸ swap_equiv hb cFresh1 hw)
  rw [swap_smul_swap_smul] at hse
  exact abs_eq_of_swap
    (fresh_prod_right.mpr ⟨cFresh2, fresh_prod_right.mpr ⟨cFresh6,
      fresh_prod_right.mpr ⟨cFresh4, cFresh7⟩⟩⟩)
    (by rw [ih hse, swap_smul_swap_smul])

end NameAbs

end Nominal.Set
