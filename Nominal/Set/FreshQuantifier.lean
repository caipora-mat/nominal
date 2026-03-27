import Nominal.Set.Nominal
import Nominal.Set.Freshness
import Nominal.Set.Equivariant
import Nominal.Set.NFun

import Mathlib.Order.Filter.Cofinite

/-!
# The Freshness Quantifier

The **freshness quantifier** `И a, ϕ a` asserts that a property `ϕ` holds for all but
finitely many atoms — equivalently, that the set `{a | ϕ a}` is cofinite. This is
Pitts' Definition 3.8.

The key result is the **Some/Any theorem** (Pitts, Theorem 3.9): for an equivariant
relation `R` and a nominal-set element `x`, the following are equivalent:

1. `∃ a, a # x ∧ R a x`   ("some fresh atom satisfies `R`")
2. `∀ a, a # x → R a x`   ("any fresh atom satisfies `R`")
3. `И a, R a x`           ("cofinitely many atoms satisfy `R`")

This equivalence justifies reading `И a, ϕ a` as "for some/any fresh `a`, `ϕ a`".

## Main definitions

* `FreshQuantifier p` — `∀ᶠ a in Filter.cofinite, p a`, i.e., `p` holds for all but finitely many atoms.
* `FC F` — freshness condition (partial): `И a, ∃ x, F a = some x ∧ a # x`.
* `FCT F` — freshness condition (total): `И a, a # F a`.

## Notation

* `И a, ϕ` — scoped notation for `FreshQuantifier (fun a ↦ ϕ)`.
* `fresh[F | h]` — scoped notation for `freshF F h` (Pitts, Notation 3.12).
* `freshT[F | h]` — scoped notation for `freshFT F h` (Pitts, Notation 3.12).

## Main results

### Basic API
* `freshQuantifier_iff` — `(И a, p a) ↔ Set.Finite {a | ¬ p a}`.
* `freshQuantifier_mono` — monotonicity: `(∀ a, p a → q a) → (И a, p a) → (И a, q a)`.
* `freshQuantifier_and` — `(И a, p a ∧ q a) ↔ (И a, p a) ∧ (И a, q a)`.
* `freshQuantifier_of_forall` — if `p a` holds for all `a`, then `И a, p a`.
* `freshQuantifier_exists` — `(И a, p a) → ∃ a, p a`.
* `freshQuantifier_not` — `(И a, ¬ p a) ↔ Set.Finite {a | p a}`.
* `freshQuantifier_imp` — `(И a, p a → q a) → (И a, p a) → (И a, q a)`.
* `freshQuantifier_congr` — `(∀ a, p a ↔ q a) → (И p ↔ И q)`.
* `freshQuantifier_true` — `И a, True`.
* `freshQuantifier_false` — `¬ (И a, False)`.
* `freshQuantifier_iff_exists_finset` — `(И a, p a) ↔ ∃ s : Finset α, ∀ a ∉ s, p a`.
* `freshQuantifier_or_left` — `(И a, p a) → (И a, p a ∨ q a)`.
* `freshQuantifier_or_right` — `(И a, q a) → (И a, p a ∨ q a)`.

### Proposition 3.10 (Boolean algebra of И for finitely supported predicates)
* `freshQuantifier_or` — `(И a, p a ∨ q a) ↔ (И a, p a) ∨ (И a, q a)`.
* `freshQuantifier_neg` — `¬ (И a, p a) ↔ (И a, ¬ p a)`.
* `freshQuantifier_not_of_freshQuantifier_neg` — `(И a, ¬ p a) → ¬ (И a, p a)` (unconditional).
* `freshQuantifier_imp_iff` — `(И a, p a → q a) ↔ ((И a, p a) → (И a, q a))`.

### Some/Any theorem (Pitts, Theorem 3.9)
* `someAny_exists_of_freshQuantifier` — `(И a, R a x) → ∃ a, a # x ∧ R a x`.
* `someAny_forall_of_exists` — `(∃ a, a # x ∧ R a x) → ∀ a, a # x → R a x` (under equivariance).
* `someAny_freshQuantifier_of_forall` — `(∀ a, a # x → R a x) → И a, R a x`.
* `someAny_exists` — `(И a, R a x) ↔ (∃ a, a # x ∧ R a x)` (under equivariance).
* `someAny_forall` — `(И a, R a x) ↔ (∀ a, a # x → R a x)` (under equivariance).
* `someAny` — `(∀ a, a # x → R a x) ↔ (∃ a, a # x ∧ R a x)` (under equivariance).
* `equivariantRel_swap_fix` — the relation `fun a (c, x) ↦ swap c a • x = x` is equivariant.

### Freshness via И
* `fresh_iff_freshQuantifier` — `a # x ↔ (И a', swap a a' • x = x)`.
* `freshQuantifier_fresh` — `И a, a # x` (bridge to `fresh_atom_cofinite`).

### Quantifier commutation (Pitts, Exercise 3.1)
* `freshQuantifier_exists_comm` — `(∃ x, И a, R a x) → (И a, ∃ x, R a x)`.
* `freshQuantifier_forall_comm` — `(И a, ∀ x, R a x) → (∀ x, И a, R a x)`.

### Freshness Theorem (Pitts, Theorem 3.11)
* `freshQuantifier_some_unique` — if `И a, F a = some x` and `И a, F a = some x'`, then `x = x'`.
* `freshQuantifier_eq_unique` — if `И a, F a = x` and `И a, F a = x'`, then `x = x'`.
* `freshnessTheorem` — partial version: `(И a, ∃ x, F a = some x ∧ a # x) → ∃ x, (И a, F a = some x) ∧ supp x ⊆ supp F`.
* `freshF` — the unique element determined by the partial freshness theorem.
* `freshF_spec` — `И a, F a = some (freshF F hFC)`.
* `supp_freshF_le` — `supp (freshF F hFC) ⊆ supp F`.
* `freshF_unique` — if `И a, F a = some x`, then `x = freshF F hFC`.
* `freshnessTheorem_total` — total version: `(И a, a # F a) → ∃ x, (И a, F a = x) ∧ supp x ⊆ supp F`.
* `freshFTotal` — the unique element determined by the total freshness theorem.
* `freshFTotal_spec` — `И a, F a = freshFTotal F hFC`.
* `supp_freshFTotal_le` — `supp (freshFTotal F hFC) ⊆ supp F`.
* `freshFTotal_unique` — if `И a, F a = x`, then `x = freshFTotal F hFC`.

### Equivariance of freshness conditions and fresh operations
* `freshQuantifier_smul_iff` — `(И a, p a) ↔ (И a, p (π⁻¹ • a))`.
* `FC_smul` — `FC F → FC (π • F)`.
* `FCT_smul` — `FCT F → FCT (π • F)`.
* `freshF_smul` — `freshF (π • F) _ = π • freshF F _`.
* `freshFT_smul` — `freshFT (π • F) _ = π • freshFT F _`.

## References

* [A. M. Pitts, *Nominal Sets*][Pitts2013], Definition 3.8, Theorem 3.9, and Theorem 3.11.
-/

namespace Nominal.Set
open Core

open MulAction Filter

variable {α : Type*} [Name α]

/-! ### The freshness quantifier -/

/-- The **freshness quantifier**: `FreshQuantifier p` holds when `p a` is true for all but
finitely many atoms `a`. Equivalently, `{a | ¬ p a}` is finite. wraps Mathlib's `Filter.cofinite`. -/
def FreshQuantifier (p : α → Prop) : Prop := ∀ᶠ a in (Filter.cofinite : Filter α), p a

/-- Notation: `И a, ϕ` means `FreshQuantifier (fun a ↦ ϕ)`. -/
scoped notation "И " x ", " φ => FreshQuantifier (fun x ↦ φ)
scoped notation "И " x " : " t ", " φ => FreshQuantifier (fun (x : t) ↦ φ)

/-! ### Basic API -/

omit [Name α] in
/-- `И a, p a` iff the set of atoms where `p` fails is finite. -/
theorem freshQuantifier_iff {p : α → Prop} : (И a, p a) ↔ Set.Finite {a | ¬ p a} := Filter.eventually_cofinite

omit [Name α] in
/-- Monotonicity: if `p a → q a` for all `a`, then `И a, p a → И a, q a`. -/
theorem freshQuantifier_mono {p q : α → Prop} (h : ∀ a, p a → q a) (hp : И a, p a) : (И a, q a) := hp.mono h

omit [Name α] in
/-- `И a, p a ∧ q a` iff both `И a, p a` and `И a, q a`. -/
@[simp] theorem freshQuantifier_and {p q : α → Prop} :
  (И a, p a ∧ q a) ↔ (И a, p a) ∧ (И a, q a) := Filter.eventually_and

omit [Name α] in
/-- A universally true property satisfies the freshness quantifier. -/
theorem freshQuantifier_of_forall {p : α → Prop} (h : ∀ a, p a) : (И a, p a) := Eventually.of_forall h

/-- The freshness quantifier implies existence. -/
theorem freshQuantifier_exists {p : α → Prop} (h : И a, p a) : ∃ a, p a := h.exists

omit [Name α] in
/-- `И a, ¬ p a` iff the set `{a | p a}` is finite. -/
theorem freshQuantifier_not {p : α → Prop} : (И a, ¬ p a) ↔ Set.Finite {a | p a} := by
  rw [freshQuantifier_iff]
  constructor <;> (intro h; convert h using 1; ext a; simp)

omit [Name α] in
/-- Modus ponens for the freshness quantifier: `(И a, p a → q a) → (И a, p a) → И a, q a`. -/
theorem freshQuantifier_imp {p q : α → Prop} (h₁ : И a, p a → q a) (h₂ : И a, p a) : И a, q a :=
  h₂.mp h₁

omit [Name α] in
/-- Congruence: if `p a ↔ q a` for all `a`, then `И p ↔ И q`. -/
theorem freshQuantifier_congr {p q : α → Prop} (h : ∀ a, p a ↔ q a) : (И a, p a) ↔ (И a, q a) :=
  eventually_congr (Eventually.of_forall h)

omit [Name α] in
/-- The freshness quantifier holds trivially for `True`. -/
@[simp] theorem freshQuantifier_true : (И _ : α, True) := freshQuantifier_of_forall (fun _ ↦ trivial)

/-- The freshness quantifier does not hold for `False`. -/
@[simp] theorem freshQuantifier_false : ¬ (И _ : α, False) := fun h ↦ (freshQuantifier_exists h).elim (fun _ ↦ id)

omit [Name α] in
/-- `И a, p a` iff there is a finite exception set outside of which `p` holds. Pitts, Lemma 3.7, reformulated with `Finset`. -/
theorem freshQuantifier_iff_exists_finset {p : α → Prop} : (И a, p a) ↔ ∃ s : Finset α, ∀ a, a ∉ s → p a := by
  rw [freshQuantifier_iff]
  constructor
  · intro h
    exact ⟨h.toFinset, fun a ha ↦ by
      by_contra hp
      exact ha (h.mem_toFinset.mpr hp)⟩
  · intro ⟨s, hs⟩
    exact (Finset.finite_toSet s).subset (fun a ha ↦ by
      simp only [Set.mem_setOf_eq] at ha
      exact Finset.mem_coe.mpr (by by_contra h; exact ha (hs a h)))

omit [Name α] in
/-- `И a, p a` implies `И a, p a ∨ q a` unconditionally (monotonicity). -/
theorem freshQuantifier_or_left {p q : α → Prop} (hp : И a, p a) : (И a, p a ∨ q a) :=
  freshQuantifier_mono (fun _ ha ↦ Or.inl ha) hp

omit [Name α] in
/-- `И a, q a` implies `И a, p a ∨ q a` unconditionally (monotonicity). -/
theorem freshQuantifier_or_right {p q : α → Prop} (hq : И a, q a) : (И a, p a ∨ q a) :=
  freshQuantifier_mono (fun _ ha ↦ Or.inr ha) hq

omit [Name α] in
/-- `И a, p a ∨ q a` iff `(И a, p a) ∨ (И a, q a)`, for finitely supported predicates
    (i.e. when the truth sets are either finite or cofinite). Pitts, Proposition 3.10, equation (3.9). -/
theorem freshQuantifier_or {p q : α → Prop}
    (hp : Set.Finite {a | p a} ∨ Set.Finite {a | ¬ p a}) (hq : Set.Finite {a | q a} ∨ Set.Finite {a | ¬ q a}) :
    (И a, p a ∨ q a) ↔ (И a, p a) ∨ (И a, q a) := by
  rw [freshQuantifier_iff, freshQuantifier_iff, freshQuantifier_iff]
  constructor
  · intro h
    by_contra hcon
    push_neg at hcon
    obtain ⟨hnp, hnq⟩ := hcon
    have hp_fin : Set.Finite {a | p a} := hp.resolve_right hnp
    have hq_fin : Set.Finite {a | q a} := hq.resolve_right hnq
    have : ¬ Set.Finite {a | ¬ (p a ∨ q a)} := by
      intro hfin
      have : Set.Finite ({a | ¬ p a}) := by
        apply Set.Finite.subset (hfin.union hq_fin)
        intro a ha
        simp only [Set.mem_setOf_eq] at ha ⊢
        simp only [Set.mem_union, Set.mem_setOf_eq]
        by_cases hqa : q a
        · exact Or.inr hqa
        · exact Or.inl (fun h ↦ ha (h.elim id (fun hq ↦ absurd hq hqa)))
      exact hnp this
    exact this h
  · intro h
    cases h with
    | inl hp =>
      exact hp.subset (fun a ha ↦ by
        simp only [Set.mem_setOf_eq] at ha ⊢
        exact fun h ↦ ha (Or.inl h))
    | inr hq =>
      exact hq.subset (fun a ha ↦ by
        simp only [Set.mem_setOf_eq] at ha ⊢
        exact fun h ↦ ha (Or.inr h))

/-- For finitely supported predicates: `¬ (И a, p a) ↔ (И a, ¬ p a)`.
    Pitts, Proposition 3.10, equation (3.7). Requires the truth set of `p` to be either finite or cofinite. -/
theorem freshQuantifier_neg {p : α → Prop} (hfs : Set.Finite {a | p a} ∨ Set.Finite {a | ¬ p a}) :
    ¬ (И a, p a) ↔ (И a, ¬ p a) := by
  rw [freshQuantifier_iff, freshQuantifier_not]
  constructor
  · exact fun hnp ↦ hfs.resolve_right (fun hfin ↦ hnp hfin)
  · intro hfin hneg
    exact (hfin.infinite_compl).elim hneg

/-- If `И a, ¬ p a` then `¬ (И a, p a)`, unconditionally. Forward direction of
    `freshQuantifier_neg` without the finite-support hypothesis. -/
theorem freshQuantifier_not_of_freshQuantifier_neg {p : α → Prop} (h : И a, ¬ p a) : ¬ (И a, p a) := by
  intro hp
  obtain ⟨a, hna, hpa⟩ := freshQuantifier_exists (freshQuantifier_and.mpr ⟨h, hp⟩)
  exact hna hpa

omit [Name α] in
/-- `(И a, p a → q a) ↔ ((И a, p a) → (И a, q a))` for finitely supported predicates. Pitts, Proposition 3.10, equation (3.10). -/
theorem freshQuantifier_imp_iff {p q : α → Prop} (hp : Set.Finite {a | p a} ∨ Set.Finite {a | ¬ p a}) :
    (И a, p a → q a) ↔ ((И a, p a) → (И a, q a)) := by
  constructor
  · exact fun h₁ h₂ ↦ freshQuantifier_imp h₁ h₂
  · intro h
    rw [freshQuantifier_iff]
    cases hp with
    | inl hp_fin =>
      exact hp_fin.subset (fun a ha ↦ by
        simp only [Set.mem_setOf_eq] at ha ⊢
        exact (Classical.not_imp.mp ha).1)
    | inr hnp_fin =>
      have hfqp : (И a, p a) := freshQuantifier_iff.mpr hnp_fin
      have hfqq : (И a, q a) := h hfqp
      rw [freshQuantifier_iff] at hfqq
      exact hfqq.subset (fun a ha ↦ by
        simp only [Set.mem_setOf_eq] at ha ⊢
        exact (Classical.not_imp.mp ha).2)

section SomeAny

variable {X : Type*} [Nominal α X]

/-! ### The Some/Any Theorem (Pitts, Theorem 3.9) -/

/-- **(И → ∃ fresh)** If `R a x` holds for all but finitely many `a`, then there exists an atom fresh for `x` satisfying `R`. -/
theorem someAny_exists_of_freshQuantifier {R : α → X → Prop} {x : X} (h : И a, R a x) : ∃ a, a # x ∧ R a x := by
  rw [freshQuantifier_iff] at h
  have hfin : Set.Finite ({a | ¬ R a x} ∪ (supp x)) := h.union (Finset.finite_toSet _)
  pick_new a (hfin.toFinset)
  simp only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_setOf_eq,
             Finset.mem_coe, not_or, not_not] at aNew
  exact ⟨a, (fresh_atom_left a x).mpr aNew.2, aNew.1⟩

/-- **(∃ fresh → ∀ fresh)** If some fresh atom satisfies an equivariant `R`, then every fresh atom satisfies `R` -/
theorem someAny_forall_of_exists {R : α → X → Prop} {x : X} (hEquiv : EquivariantRel α R) (hEx : ∃ a, a # x ∧ R a x) : ∀ a, a # x → R a x := by
  obtain ⟨a₀, ha₀fresh, ha₀R⟩ := hEx
  intro b hbfresh
  have hfix : swap a₀ b • x = x := fresh_swap ha₀fresh hbfresh
  have := (hEquiv.smul_iff (swap a₀ b) a₀ x).mpr ha₀R
  rw [hfix, swap_apply_left] at this
  assumption

/-- **(∀ fresh → И)** If every fresh atom satisfies `R`, then `R a x` holds for all but finitely many `a` -/
theorem someAny_freshQuantifier_of_forall {R : α → X → Prop} {x : X} (hAll : ∀ a, a # x → R a x) : И a, R a x := by
  rw [freshQuantifier_iff]
  apply Set.Finite.subset (Finset.finite_toSet (supp x))
  intro a ha
  simp only [Set.mem_setOf_eq] at ha
  by_contra h
  exact ha (hAll a ((fresh_atom_left a x).mpr h))

/-- **Some/Any — existential form** (Pitts, Theorem 3.9): for an equivariant relation,
`И a, R a x` iff some fresh atom satisfies `R`. -/
theorem someAny_exists {R : α → X → Prop} {x : X} (hEquiv : EquivariantRel α R) : (И a, R a x) ↔ (∃ a, a # x ∧ R a x) :=
  ⟨someAny_exists_of_freshQuantifier,
   fun h ↦ someAny_freshQuantifier_of_forall (someAny_forall_of_exists hEquiv h)⟩

/-- **Some/Any — universal form** (Pitts, Theorem 3.9): for an equivariant relation,
`И a, R a x` iff every fresh atom satisfies `R`. -/
theorem someAny_forall {R : α → X → Prop} {x : X} (hEquiv : EquivariantRel α R) : (И a, R a x) ↔ (∀ a, a # x → R a x) :=
  ⟨fun h ↦ someAny_forall_of_exists hEquiv (someAny_exists_of_freshQuantifier h),
   someAny_freshQuantifier_of_forall⟩

/-- **Some/Any — some ↔ any** (Pitts, Theorem 3.9): under equivariance, the existential-fresh
and universal-fresh formulations are equivalent. -/
theorem someAny {R : α → X → Prop} {x : X} (hEquiv : EquivariantRel α R) : (∀ a, a # x → R a x) ↔ (∃ a, a # x ∧ R a x) :=
  (someAny_forall hEquiv).symm.trans (someAny_exists hEquiv)

/-- The relation `R a (c, x) = swap c a • x = x` is equivariant. This is the key equivariance fact used in `fresh_iff_freshQuantifier` and `NameAbstraction`. -/
theorem equivariantRel_swap_fix : EquivariantRel α (fun (a : α) (p : α × X) ↦ swap p.1 a • p.2 = p.2) where
  smul_iff π a p := by
    simp only [Prod.smul_fst, Prod.smul_snd]
    rw [swap_smul_equivariant, smul_left_cancel_iff]

/-! ### Freshness via the freshness quantifier -/

/-- `a # x` iff swapping `a` with any atom leaves `x` fixed for cofinitely many atoms. -/
theorem fresh_iff_freshQuantifier {a : α} {x : X} : a # x ↔ (И a', swap a a' • x = x) := by
  constructor
  · intro ha
    rw [freshQuantifier_iff]
    apply (Finset.finite_toSet (supp x)).subset
    intro b hb
    simp only [Set.mem_setOf_eq] at hb
    simp only [Finset.mem_coe]
    by_contra hb_supp
    exact hb (fresh_swap ha ((fresh_atom_left b x).mpr hb_supp))
  · intro h
    rw [freshQuantifier_iff] at h
    have hfin : Set.Finite ({a' | ¬ swap a a' • x = x} ∪ (supp x)) := h.union (Finset.finite_toSet _)
    pick_new b hfin.toFinset
    simp only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_setOf_eq,
               Finset.mem_coe, not_or, not_not] at bNew
    obtain ⟨hswap_fix, hb_supp⟩ := bNew
    rw [fresh_atom_left]
    intro ha_supp
    apply hb_supp
    have : b ∈ supp (swap a b • x) := by
      rw [← supp_equivariant, PermType.mem_smul_finset_iff]
      simp only [swap_inv, swap_apply_right]
      exact ha_supp
    rwa [hswap_fix] at this

/-! ### Convenience lemmas connecting И with freshness -/

/-- For any nominal-set element `x`, cofinitely many atoms are fresh for `x`. Bridge between `fresh_atom_cofinite` and `FreshQuantifier`. -/
theorem freshQuantifier_fresh (x : X) : (И a : α, a # x) := fresh_atom_cofinite x

omit [Name α] [Nominal α X] in
/-- `(∃ x, И a, R a x) → (И a, ∃ x, R a x)`. Pitts, Exercise 3.1, equation (3.26). -/
theorem freshQuantifier_exists_comm {Y : Type*} {R : α → Y → Prop} (h : ∃ x, И a, R a x) : И a, ∃ x, R a x := by
  obtain ⟨x, hx⟩ := h
  exact freshQuantifier_mono (fun a ha ↦ ⟨x, ha⟩) hx

omit [Name α] [Nominal α X] in
/-- `(И a, ∀ x, R a x) → (∀ x, И a, R a x)`. Pitts, Exercise 3.1, equation (3.27). -/
theorem freshQuantifier_forall_comm {Y : Type*} {R : α → Y → Prop} (h : И a, ∀ x, R a x) : ∀ x, И a, R a x :=
  fun x ↦ freshQuantifier_mono (fun _ ha ↦ ha x) h

end SomeAny

section FreshnessTheorem

/-! ### The Freshness Theorem (Pitts, Theorem 3.11)

The **freshness theorem** says that any finitely supported function `F` satisfying the **freshness condition** is *eventually constant*:
there is a unique element `x` with `И a, F a = x` (or `И a, F a = some x` in the partial case) and `supp x ⊆ supp F`.

We prove two versions:
- **Partial**: `F : NFun α α (Option X)` with condition `FC F`, i.e. `И a, ∃ x, F a = some x ∧ a # x`.
- **Total**: `F : NFun α α X` with condition `FCT F`, i.e. `И a, a # F a`.

## References

* [A. M. Pitts, *Nominal Sets*][Pitts2013], Theorem 3.11.
-/

variable {X : Type*} [Nominal α X]

/-- The **freshness condition** (partial version): for cofinitely many atoms `a`,
`F a` is defined and `a` is fresh for the value. This is the hypothesis required by the partial freshness theorem (`freshnessTheorem`, `freshF`). -/
def FC (F : NFun α α (Option X)) : Prop := И a, ∃ x, F a = some x ∧ a # x

/-- The **freshness condition** (total version): for cofinitely many atoms `a`,
`a` is fresh for `F a`. This is the hypothesis required by the total freshness theorem (`freshnessTheorem_total`, `freshFT`). -/
def FCT (F : NFun α α X) : Prop := И a, a # F a

/-! #### Partial version (`NFun α α (Option X)`) -/

/-- **Uniqueness** for cofinitely-equal `Option`-valued functions: if `F a = some x` and `F a = some x'` for cofinitely many `a`, then `x = x'`. -/
theorem freshQuantifier_some_unique {F : NFun α α (Option X)} {x x' : X} (hx : И a, F a = some x) (hx' : И a, F a = some x') : x = x' := by
  obtain ⟨a, ha, ha'⟩ := freshQuantifier_exists (freshQuantifier_and.mpr ⟨hx, hx'⟩)
  exact Option.some.inj (ha ▸ ha')

/-- **Freshness Theorem — partial version** (Pitts, Theorem 3.11). If `F : α →ᶠˢ Option X` satisfies the freshness condition —
for cofinitely many atoms `a`, `F a` is defined and `a` is fresh for the value — then there is a unique `x : X` with `И a, F a = some x`, and `supp x ⊆ supp F`. -/
theorem freshnessTheorem (F : NFun α α (Option X)) (hFC : FC F) : ∃ fresh : X, (И a, F a = some fresh) ∧ supp fresh ⊆ supp F := by
  -- Intersect with (И a, a # F) to get both conditions
  have hBoth : И a, a # F ∧ (∃ x, F a = some x ∧ a # x) := freshQuantifier_and.mpr ⟨fresh_atom_cofinite F, hFC⟩
  -- Extract witness a₀ with a₀ # F, F a₀ = some x₀, a₀ # x₀
  obtain ⟨a₀, ha₀F, x₀, hFa₀, ha₀x₀⟩ := freshQuantifier_exists hBoth
  refine ⟨x₀, ?_, ?_⟩
  -- Part 1: И a, F a = some x₀
  · apply freshQuantifier_mono (fun b hb ↦ ?_) hBoth
    obtain ⟨hbF, y, hFb, hby⟩ := hb
    by_cases heq : b = a₀
    · subst heq; exact hFa₀
    · -- swap a₀ b fixes F since a₀ # F and b # F
      have hFix : swap a₀ b • F = F := fresh_swap ha₀F hbF
      -- F b = (swap a₀ b • F) b = swap a₀ b • F a₀ = swap a₀ b • some x₀ = some (swap a₀ b • x₀)
      have hFb_eq : F b = some (swap a₀ b • x₀) := by
        have key := NFun.smul_apply_smul (swap a₀ b) F a₀
        rw [swap_apply_left, hFix, hFa₀] at key
        simpa using key
      -- b # x₀ follows from b # F a₀ (via NFun.fresh_apply) and F a₀ = some x₀
      have hb_x₀ : b # x₀ := by
        have := NFun.fresh_apply hbF ((fresh_atoms b a₀).mpr heq)
        rwa [hFa₀, fresh_some] at this
      rw [hFb_eq, swap_comm, fresh_swap hb_x₀ ha₀x₀]
  -- Part 2: supp x₀ ⊆ supp F
  · intro c hc
    have h_le := NFun.supp_apply_le F (a₀ : α)
    rw [supp_atom] at h_le
    have hc_Fa₀ : c ∈ supp (F a₀) := by rw [hFa₀, supp_some]; exact hc
    have := h_le hc_Fa₀
    rw [Finset.mem_union, Finset.mem_singleton] at this
    exact this.elim id fun h ↦ absurd (h ▸ hc) ((fresh_atom_left a₀ x₀).mp ha₀x₀)

/-- The unique element determined by the freshness theorem (partial version, Notation 3.12):
given `F : α →ᶠˢ Option X` satisfying the freshness condition, `freshF F` is the unique `x`
with `И a, F a = some x`.

In informal notation (Pitts, Notation 3.12), this is written `fresh a in F a`. -/
noncomputable def freshF (F : NFun α α (Option X)) (hFC : FC F) : X := (freshnessTheorem F hFC).choose

/-- `fresh[F | h]` stands for `freshF F h`, the unique element determined by a finitely supported function `F` satisfying the
freshness condition `h`. -/
scoped notation "fresh[" F " | " h "]" => freshF F h

/-- The defining property: `F a = some (freshF F hFC)` for cofinitely many `a`. -/
theorem freshF_spec (F : NFun α α (Option X)) (hFC : FC F) : И a, F a = some (freshF F hFC) :=
  (freshnessTheorem F hFC).choose_spec.1

/-- Support bound: `supp (freshF F hFC) ⊆ supp F`. -/
theorem supp_freshF_le (F : NFun α α (Option X)) (hFC : FC F) : supp (freshF F hFC) ⊆ supp F :=
  (freshnessTheorem F hFC).choose_spec.2

/-- Uniqueness: if `И a, F a = some x`, then `x = freshF F hFC`. -/
theorem freshF_unique (F : NFun α α (Option X)) (hFC : FC F) {x : X} (hx : И a, F a = some x) : x = freshF F hFC :=
  freshQuantifier_some_unique hx (freshF_spec F hFC)

/-! #### Total version (`NFun α α X`) -/

/-- **Uniqueness** for cofinitely-equal functions: if `F a = x` and `F a = x'` for cofinitely many `a`, then `x = x'`. -/
theorem freshQuantifier_eq_unique {F : NFun α α X} {x x' : X} (hx : И a, F a = x) (hx' : И a, F a = x') : x = x' := by
  obtain ⟨a, ha, ha'⟩ := freshQuantifier_exists (freshQuantifier_and.mpr ⟨hx, hx'⟩)
  exact ha ▸ ha'

/-- **Freshness Theorem — total version** (Pitts, Theorem 3.11). If `F : α →ᶠˢ X` satisfies `И a, a # F a`, then there is a unique `x : X`
with `И a, F a = x`, and `supp x ⊆ supp F`. -/
theorem freshnessTheorem_total (F : NFun α α X) (hFC : FCT F) : ∃ x : X, (И a, F a = x) ∧ supp x ⊆ supp F := by
  -- Intersect with (И a, a # F)
  have hBoth : И a, a # F ∧ a # F a :=
    freshQuantifier_and.mpr ⟨fresh_atom_cofinite F, hFC⟩
  -- Extract witness a₀ with a₀ # F, a₀ # F a₀
  obtain ⟨a₀, ha₀F, ha₀Fa₀⟩ := freshQuantifier_exists hBoth
  refine ⟨F a₀, ?_, ?_⟩
  -- Part 1: И a, F a = F a₀
  · apply freshQuantifier_mono (fun b hb ↦ ?_) hBoth
    obtain ⟨hbF, _hbFb⟩ := hb
    by_cases heq : b = a₀
    · exact congr_arg F heq
    · -- swap a₀ b fixes F
      have hFix : swap a₀ b • F = F := fresh_swap ha₀F hbF
      -- F b = swap a₀ b • F a₀
      have hFb_eq : F b = swap a₀ b • F a₀ := by
        have key := NFun.smul_apply_smul (swap a₀ b) F a₀
        rw [swap_apply_left, hFix] at key
        exact key
      -- b # F a₀ follows from b # F and b # a₀ via NFun.fresh_apply
      have hb_Fa₀ : b # F a₀ := NFun.fresh_apply hbF ((fresh_atoms b a₀).mpr heq)
      rw [hFb_eq, swap_comm, fresh_swap hb_Fa₀ ha₀Fa₀]
  -- Part 2: supp (F a₀) ⊆ supp F
  · intro c hc
    have h_le := NFun.supp_apply_le F (a₀ : α)
    rw [supp_atom] at h_le
    have := h_le hc
    rw [Finset.mem_union, Finset.mem_singleton] at this
    exact this.elim id fun h ↦ absurd (h ▸ hc) ((fresh_atom_left a₀ (F a₀)).mp ha₀Fa₀)

/-- The unique element determined by the freshness theorem (total version, Notation 3.12):
given `F : α →ᶠˢ X` with `И a, a # F a`, `freshFT F` is the unique `x` with `И a, F a = x`.

In informal notation (Pitts, Notation 3.12), this is written `fresh a in F a`. -/
noncomputable def freshFT (F : NFun α α X) (hFC : FCT F) : X := (freshnessTheorem_total F hFC).choose

/-- Notation 3.12: `freshT[F | h]` stands for `freshFT F h`, the unique element determined
by a finitely supported function `F` satisfying the freshness condition `h`. -/
scoped notation "freshT[" F " | " h "]" => freshFT F h

/-- The defining property: `F a = freshFTotal F hFC` for cofinitely many `a`. -/
theorem freshFTotal_spec (F : NFun α α X) (hFC : FCT F) : И a, F a = freshFT F hFC :=
  (freshnessTheorem_total F hFC).choose_spec.1

/-- Support bound: `supp (freshFTotal F hFC) ⊆ supp F`. -/
theorem supp_freshFTotal_le (F : NFun α α X) (hFC : FCT F) : supp (freshFT F hFC) ⊆ supp F :=
  (freshnessTheorem_total F hFC).choose_spec.2

/-- Uniqueness: if `И a, F a = x`, then `x = freshFTotal F hFC`. -/
theorem freshFTotal_unique (F : NFun α α X) (hFC : FCT F) {x : X} (hx : И a, F a = x) : x = freshFT F hFC :=
  freshQuantifier_eq_unique hx (freshFTotal_spec F hFC)

/-! #### Equivariance of freshness conditions and fresh operations -/

/-- The freshness condition `FC` is preserved by the permutation action. -/
theorem FC_smul (π : FinitePerm α) {F : NFun α α (Option X)} (h : FC F) : FC (π • F) := by
  unfold FC at *
  -- Strategy: {a | ¬ ∃ x, (π • F) a = some x ∧ a # x} is finite
  -- because it's the image under π of {a | ¬ ∃ x, F a = some x ∧ a # x}
  rw [freshQuantifier_iff] at *
  have : {a | ¬ ∃ x, (π • F) a = some x ∧ a # x} ⊆
      (fun a ↦ π • a) '' {a | ¬ ∃ x, F a = some x ∧ a # x} := by
    intro a ha
    simp only [Set.mem_setOf_eq, Set.mem_image] at ha ⊢
    refine ⟨π⁻¹ • a, ?_, by simp⟩
    intro ⟨x, hx, hfresh⟩
    apply ha
    refine ⟨π • x, ?_, ?_⟩
    · have := NFun.smul_apply_smul π F (π⁻¹ • a)
      rw [smul_inv_smul] at this
      rw [this, hx]; simp
    · exact (fresh_smul_left a π x).mpr hfresh
  exact (h.image _).subset this

/-- The freshness condition `FCT` is preserved by the permutation action. -/
theorem FCT_smul (π : FinitePerm α) {F : NFun α α X} (h : FCT F) : FCT (π • F) := by
  unfold FCT at *
  rw [freshQuantifier_iff] at *
  have : {a | ¬ a # (π • F) a} ⊆ (fun a ↦ π • a) '' {a | ¬ a # F a} := by
    intro a ha
    simp only [Set.mem_setOf_eq, Set.mem_image] at ha ⊢
    refine ⟨π⁻¹ • a, ?_, by simp⟩
    intro hfresh
    apply ha
    have : (π • F) a = π • F (π⁻¹ • a) := NFun.smul_apply π F a
    rw [this]
    exact (fresh_smul_left a π (F (π⁻¹ • a))).mpr hfresh
  exact (h.image _).subset this

/-- Equivariance of И: `(И a, p a) ↔ (И a, p (π⁻¹ • a))`. -/
theorem freshQuantifier_smul_iff (π : FinitePerm α) {p : α → Prop} :
    (И a, p a) ↔ (И a, p (π⁻¹ • a)) := by
  constructor
  · intro h
    rw [freshQuantifier_iff] at *
    have : {a | ¬ p (π⁻¹ • a)} ⊆ (fun a ↦ π • a) '' {a | ¬ p a} := by
      intro a ha
      simp only [Set.mem_setOf_eq, Set.mem_image] at ha ⊢
      exact ⟨π⁻¹ • a, ha, by simp⟩
    exact (h.image _).subset this
  · intro h
    rw [freshQuantifier_iff] at *
    have : {a | ¬ p a} ⊆ (fun a ↦ π⁻¹ • a) '' {a | ¬ p (π⁻¹ • a)} := by
      intro a ha
      simp only [Set.mem_setOf_eq, Set.mem_image] at ha ⊢
      exact ⟨π • a, by simpa using ha, by simp⟩
    exact (h.image _).subset this

theorem freshQuantifier_smul_shift {p : α → Prop} (π : FinitePerm α) (h : И a, p a) : И a, p (π⁻¹ • a) :=
  (freshQuantifier_smul_iff π).mp h

/-- Equivariance of `freshF`: `freshF (π • F) _ = π • freshF F _`. -/
theorem freshF_smul (π : FinitePerm α) (F : NFun α α (Option X)) (hFC : FC F) (hFC' : FC (π • F)) :
    freshF (π • F) hFC' = π • freshF F hFC := by
  have hspec := freshF_spec F hFC
  -- Show И a, (π • F) a = some (π • freshF F hFC)
  have hshifted : И a, (π • F) a = some (π • freshF F hFC) := by
    apply freshQuantifier_mono (fun a ha ↦ ?_) (freshQuantifier_smul_shift π hspec)
    simp only [NFun.smul_apply]
    rw [ha]; simp
  exact (freshF_unique (π • F) hFC' hshifted).symm

/-- Equivariance of `freshFT`: `freshFT (π • F) _ = π • freshFT F _`. -/
theorem freshFT_smul (π : FinitePerm α) (F : NFun α α X) (hFC : FCT F) (hFC' : FCT (π • F)) :
    freshFT (π • F) hFC' = π • freshFT F hFC := by
  have hspec := freshFTotal_spec F hFC
  have hshifted : И a, (π • F) a = π • freshFT F hFC := by
    apply freshQuantifier_mono (fun a ha ↦ ?_) (freshQuantifier_smul_shift π hspec)
    simp only [NFun.smul_apply]
    rw [ha]
  exact (freshFTotal_unique (π • F) hFC' hshifted).symm

end FreshnessTheorem

end Nominal.Set
