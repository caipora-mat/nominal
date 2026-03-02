import NominalSets.Nominal
import NominalSets.Freshness
import NominalSets.Equivariant

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

* `FreshQuantifier p` — `∀ᶠ a in Filter.cofinite, p a`, i.e., `p` holds for all but
  finitely many atoms.

## Notation

* `И a, ϕ` — scoped notation for `FreshQuantifier (fun a ↦ ϕ)`.

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

## References

* [A. M. Pitts, *Nominal Sets*][Pitts2013], Definition 3.8 and Theorem 3.9.
-/

namespace NominalSets

open MulAction Filter

variable {α : Type*} [Name α]

/-! ### The freshness quantifier -/

/-- The **freshness quantifier**: `FreshQuantifier p` holds when `p a` is true for all but
finitely many atoms `a`. Equivalently, `{a | ¬ p a}` is finite. wraps Mathlib's `Filter.cofinite`. -/
def FreshQuantifier (p : α → Prop) : Prop := ∀ᶠ a in (Filter.cofinite : Filter α), p a

/-- Notation: `И a, ϕ` means `FreshQuantifier (fun a ↦ ϕ)`. -/
scoped notation "И " x ", " φ => FreshQuantifier (fun x ↦ φ)

/-! ### Basic API -/

omit [Name α] in
/-- `И a, p a` iff the set of atoms where `p` fails is finite. -/
theorem freshQuantifier_iff {p : α → Prop} : FreshQuantifier p ↔ Set.Finite {a | ¬ p a} := Filter.eventually_cofinite

omit [Name α] in
/-- Monotonicity: if `p a → q a` for all `a`, then `И a, p a → И a, q a`. -/
theorem freshQuantifier_mono {p q : α → Prop} (h : ∀ a, p a → q a) (hp : FreshQuantifier p) : FreshQuantifier q := hp.mono h

omit [Name α] in
/-- `И a, p a ∧ q a` iff both `И a, p a` and `И a, q a`. -/
@[simp] theorem freshQuantifier_and {p q : α → Prop} :
  FreshQuantifier (fun a ↦ p a ∧ q a) ↔ FreshQuantifier p ∧ FreshQuantifier q := Filter.eventually_and

omit [Name α] in
/-- A universally true property satisfies the freshness quantifier. -/
theorem freshQuantifier_of_forall {p : α → Prop} (h : ∀ a, p a) : FreshQuantifier p := Eventually.of_forall h

/-- The freshness quantifier implies existence. -/
theorem freshQuantifier_exists {p : α → Prop} (h : FreshQuantifier p) : ∃ a, p a := h.exists

omit [Name α] in
/-- `И a, ¬ p a` iff the set `{a | p a}` is finite. -/
theorem freshQuantifier_not {p : α → Prop} : FreshQuantifier (fun a ↦ ¬ p a) ↔ Set.Finite {a | p a} := by
  rw [freshQuantifier_iff]
  constructor <;> (intro h; convert h using 1; ext a; simp)

omit [Name α] in
/-- Modus ponens for the freshness quantifier: `(И a, p a → q a) → (И a, p a) → И a, q a`. -/
theorem freshQuantifier_imp {p q : α → Prop} (h₁ : И a, p a → q a) (h₂ : И a, p a) : И a, q a :=
  h₂.mp h₁

omit [Name α] in
/-- Congruence: if `p a ↔ q a` for all `a`, then `И p ↔ И q`. -/
theorem freshQuantifier_congr {p q : α → Prop} (h : ∀ a, p a ↔ q a) :
    FreshQuantifier p ↔ FreshQuantifier q :=
  eventually_congr (Eventually.of_forall h)

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
theorem someAny_forall_of_exists {R : α → X → Prop} {x : X} (hEquiv : EquivariantRel R) (hEx : ∃ a, a # x ∧ R a x) : ∀ a, a # x → R a x := by
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
theorem someAny_exists {R : α → X → Prop} {x : X} (hEquiv : EquivariantRel R) : (И a, R a x) ↔ (∃ a, a # x ∧ R a x) :=
  ⟨someAny_exists_of_freshQuantifier,
   fun h ↦ someAny_freshQuantifier_of_forall (someAny_forall_of_exists hEquiv h)⟩

/-- **Some/Any — universal form** (Pitts, Theorem 3.9): for an equivariant relation,
`И a, R a x` iff every fresh atom satisfies `R`. -/
theorem someAny_forall {R : α → X → Prop} {x : X} (hEquiv : EquivariantRel R) : (И a, R a x) ↔ (∀ a, a # x → R a x) :=
  ⟨fun h ↦ someAny_forall_of_exists hEquiv (someAny_exists_of_freshQuantifier h),
   someAny_freshQuantifier_of_forall⟩

/-- **Some/Any — some ↔ any** (Pitts, Theorem 3.9): under equivariance, the existential-fresh
and universal-fresh formulations are equivalent. -/
theorem someAny {R : α → X → Prop} {x : X} (hEquiv : EquivariantRel R) : (∀ a, a # x → R a x) ↔ (∃ a, a # x ∧ R a x) :=
  (someAny_forall hEquiv).symm.trans (someAny_exists hEquiv)

/-- The relation `R a (c, x) = swap c a • x = x` is equivariant. This is the
key equivariance fact used in `fresh_iff_freshQuantifier` and `NameAbstraction`. -/
theorem equivariantRel_swap_fix : EquivariantRel (α := α) (fun (a : α) (p : α × X) ↦ swap p.1 a • p.2 = p.2) where
  smul_iff π a p := by
    simp only [Prod.smul_fst, Prod.smul_snd]
    have key : swap (π • p.1) (π • a) • (π • p.2) = π • (swap p.1 a • p.2) := by
      rw [← swap_equivariant, PermType.conj_smul, mul_smul, mul_smul, PermType.inv_smul_smul]
    rw [key, smul_left_cancel_iff]

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

end SomeAny

end NominalSets
