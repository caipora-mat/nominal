import NominalSets.Nominal
import NominalSets.Freshness
import NominalSets.Equivariant
import NominalSets.NFun

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
* `fresh[F | h]` — scoped notation for `freshFT F h` (Pitts, Notation 3.12).

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

### Freshness Theorem (Pitts, Theorem 3.11)
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

## References

* [A. M. Pitts, *Nominal Sets*][Pitts2013], Definition 3.8, Theorem 3.9, and Theorem 3.11.
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

/-- The relation `R a (c, x) = swap c a • x = x` is equivariant. This is the
key equivariance fact used in `fresh_iff_freshQuantifier` and `NameAbstraction`. -/
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
`F a` is defined and `a` is fresh for the value. This is the hypothesis
required by the partial freshness theorem (`freshnessTheorem`, `freshF`). -/
def FC (F : NFun α α (Option X)) : Prop := И a, ∃ x, F a = some x ∧ a # x

/-- The **freshness condition** (total version): for cofinitely many atoms `a`,
`a` is fresh for `F a`. This is the hypothesis required by the total freshness
theorem (`freshnessTheorem_total`, `freshFT`). -/
def FCT (F : NFun α α X) : Prop := И a, a # F a

/-! #### Partial version (`NFun α α (Option X)`) -/

/-- **Uniqueness** for cofinitely-equal `Option`-valued functions: if `F a = some x` and `F a = some x'` for cofinitely many `a`, then `x = x'`. -/
theorem freshQuantifier_some_unique {F : NFun α α (Option X)} {x x' : X} (hx : И a, F a = some x) (hx' : И a, F a = some x') : x = x' := by
  obtain ⟨a, ha, ha'⟩ := freshQuantifier_exists (freshQuantifier_and.mpr ⟨hx, hx'⟩)
  exact Option.some.inj (ha ▸ ha')

/-- **Freshness Theorem — partial version** (Pitts, Theorem 3.11). If `F : α →ᶠˢ Option X` satisfies the freshness condition —
for cofinitely many atoms `a`, `F a` is defined and `a` is fresh for the value — then there is a unique `x : X` with `И a, F a = some x`,
and `supp x ⊆ supp F`. -/
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
      -- b # x₀ (since supp x₀ = supp(some x₀) = supp(F a₀) ⊆ supp F ∪ {a₀}, b # F, b ≠ a₀)
      have hb_x₀ : b # x₀ := by
        rw [fresh_atom_left]
        intro hb_mem
        have h_le := NFun.supp_apply_le F (a₀ : α)
        rw [supp_atom] at h_le
        have : b ∈ supp (F a₀) := by rw [hFa₀, supp_some]; exact hb_mem
        have := h_le this
        rw [Finset.mem_union, Finset.mem_singleton] at this
        exact this.elim ((fresh_atom_left b F).mp hbF) fun h ↦ heq h
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
      -- b # F a₀
      have hb_Fa₀ : b # F a₀ := by
        rw [fresh_atom_left]
        intro hb_mem
        have h_le := NFun.supp_apply_le F (a₀ : α)
        rw [supp_atom] at h_le
        have := h_le hb_mem
        rw [Finset.mem_union, Finset.mem_singleton] at this
        exact this.elim ((fresh_atom_left b F).mp hbF) fun h ↦ heq h
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

end FreshnessTheorem

end NominalSets
