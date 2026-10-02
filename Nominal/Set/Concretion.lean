import Nominal.Set.NameAbstraction

/-!
# Concretion for Name Abstractions

Given a name abstraction `F : NameAbs α X`, the **concretion** `F ⊙ a` attempts to
extract the body of `F` at atom `a`. It returns `some x` when `a` is the binder or
is fresh for the body, and `none` otherwise.

This file also provides the **functorial map** `liftAbs` that lifts an equivariant
function `f : X → Y` to `NameAbs α X → NameAbs α Y`, and proves the **extensionality**
principle for name abstractions (equation 4.16).

## Main definitions

* `concreteAt F a` — concretion of `F : NameAbs α X` at atom `a`, as `Option X`.
* `concreteAt_val F a ha` — noncomputable accessor extracting the body at a fresh atom.
* `liftAbs hf` — functorial map `⟪a⟫ x ↦ ⟪a⟫ f x` for equivariant `f : X → Y`.
* `liftAbsEquiv hf hg hfg hgf` — equivalence `NameAbs α X ≃ NameAbs α Y` from an equivariant bijection.
* `concreteAt_nfun F` — package concretion as `α →ᶠˢ Option X`.

## Notation

* `F ⊙ a` — scoped left-associative notation for `concreteAt F a`.

## Main results

### Basic concretion API (Pitts, Definition 4.7 / Proposition 4.9)
* `concreteAt_abs_self` — `(⟪a⟫ x) ⊙ a = some x`.
* `concreteAt_abs_fresh` — if `a' ≠ a` and `a' # x`, then `(⟪a⟫ x) ⊙ a' = some (swap a a' • x)`.
* `concreteAt_abs_not_fresh` — if `a' ≠ a` and `a' ∈ supp x`, then `(⟪a⟫ x) ⊙ a' = none`.
* `concreteAt_abs_eq` — `(⟪a⟫ x) ⊙ a' = some x` when `a' = a`.
* `concreteAt_abs` — unified computation rule covering all three cases.
* `concreteAt_eq_none_of_not_fresh` — `¬ a # F → F ⊙ a = none`.
* `concreteAt_none_iff` — `F ⊙ a = none ↔ ¬ a # F`.
* `concreteAt_isSome_iff` — `(F ⊙ a).isSome = true ↔ a # F`.
* `concreteAt_isNone_iff` — `(F ⊙ a).isNone = true ↔ ¬ a # F`.
* `concreteAt_injective` — `F ⊙ a = some y` and `F ⊙ a = some z` imply `y = z`.
* `abs_concreteAt_eq_forall` — `∀ a, a # F → ∃ y, F ⊙ a = some y ∧ F = ⟪a⟫ y` (Proposition 4.9).
* `abs_concreteAt_eq_exists` — `∃ a, a # F ∧ ∃ y, F ⊙ a = some y ∧ F = ⟪a⟫ y`.
* `abs_concreteAt_eq_freshQuantifier` — `И a, ∃ y, F ⊙ a = some y ∧ F = ⟪a⟫ y` (equation 4.15).
* `abs_of_concreteAt_eq_some` — `F ⊙ a = some y → F = ⟪a⟫ y`.
* `concreteAt_some_iff` — `F ⊙ a = some y ↔ a # F ∧ F = ⟪a⟫ y`.
* `concreteAt_abs_some_iff'` — full characterisation of `(⟪a⟫ x) ⊙ a' = some y` on representatives.
* `concreteAt_abs_none_iff` — `(⟪a⟫ x) ⊙ a' = none ↔ a' ≠ a ∧ a' ∈ supp x`.
* `concreteAt_get` — `F = ⟪a⟫ ((F ⊙ a).get h)` when `a # F`.
* `concreteAt_val_eq` — `F ⊙ a = some (concreteAt_val F a ha)`.
* `abs_concreteAt_val` — `F = ⟪a⟫ (concreteAt_val F a ha)`.
* `concreteAt_congr` — congruence of concretion in the abstraction argument.
* `concreteAt_abs_of_both_fresh` — when both binder and target are fresh for the body, concretion returns the body.
* `concreteAt_smul_abs_self` — `(π • ⟪a⟫ x) ⊙ (π • a) = some (π • x)`.
* `concreteAt_equivariant` — `π • (F ⊙ a) = (π • F) ⊙ (π • a)`.
* `concreteAt_swap` — `(swap a b • F) ⊙ c = swap a b • (F ⊙ (swap a b • c))`.
* `fresh_of_concreteAt_eq_some` — if `F ⊙ a = some y`, `b ≠ a`, `b # F`, then `b # y`.
* `supp_concreteAt_le` — if `F ⊙ a = some y`, then `supp y ⊆ supp F ∪ {a}`.
* `supp_concreteAt_option_le` — `supp (F ⊙ a) ⊆ supp F ∪ {a}`.
* `fresh_concreteAt` — if `b # F` and `b ≠ a`, then `b # (F ⊙ a)`.
* `concreteAt_eq_iff` — `F ⊙ a = G ⊙ a ↔ (¬ a # F ∧ ¬ a # G) ∨ (∃ y, F ⊙ a = some y ∧ G ⊙ a = some y)`.
* `isEquivariant_concreteAt` — concretion is equivariant as a binary operation.

### Extensionality (Pitts, equation 4.16)
* `nameAbs_ext` — `F = G ↔ (И c, F ⊙ c = G ⊙ c)`.
* `nameAbs_ext_iff` — alias for `nameAbs_ext` following Mathlib `_ext_iff` naming.
* `nameAbs_ext_forall` — `F = G ↔ ∀ c, c # (F, G) → F ⊙ c = G ⊙ c`.
* `nameAbs_ext_exists` — `F = G ↔ ∃ c, c # (F, G) ∧ F ⊙ c = G ⊙ c`.
* `equivariantRel_concreteAt_eq` — the relation `fun c (F, G) ↦ F ⊙ c = G ⊙ c` is equivariant.

### Functorial map
* `liftAbs` — lift an equivariant function `f : X → Y` to `NameAbs α X → NameAbs α Y`.
* `liftAbs_abs` — `liftAbs hf (⟪a⟫ x) = ⟪a⟫ f x`.
* `liftAbs_equivariant` — `liftAbs hf (π • F) = π • liftAbs hf F`.
* `isEquivariant_liftAbs` — `liftAbs hf` is equivariant (packaged as `IsEquivariant`).
* `liftAbs_unique` — any function agreeing on representatives equals `liftAbs hf`.
* `liftAbs_concreteAt` — `(liftAbs hf F) ⊙ a = Option.map f (F ⊙ a)` when `a # F`.
* `liftAbs_concreteAt_forall` — forall form of `liftAbs_concreteAt`.
* `liftAbs_concreteAt_freshQuantifier` — И-version: `И a, (liftAbs hf F) ⊙ a = Option.map f (F ⊙ a)`.
* `liftAbs_concreteAt_eq` — `(liftAbs hf F) ⊙ a = Option.map f (F ⊙ a)` for all `a` (requires injectivity).
* `liftAbs_concreteAt_some` — extracts the preimage when concretion returns `some`.
* `supp_liftAbs_le` — `supp (liftAbs hf F) ⊆ supp F`.
* `supp_liftAbs_eq` — `supp (liftAbs hf F) = supp F` when `f` is injective.
* `fresh_liftAbs` — if `a # F` then `a # liftAbs hf F`.
* `liftAbs_id` — `liftAbs isEquivariant_id = id`.
* `liftAbs_comp` — `liftAbs hg (liftAbs hf F) = liftAbs (hg.comp hf) F`.
* `liftAbs_comp_fun` — function-level: `liftAbs hg ∘ liftAbs hf = liftAbs (hg.comp hf)`.
* `liftAbs_ext` — `liftAbs hf = liftAbs hg ↔ f = g`.
* `liftAbs_const_abs` — `liftAbs` of a constant equivariant function.
* `liftAbs_injective` — injective `f` implies injective `liftAbs hf`.
* `liftAbs_surjective` — surjective `f` implies surjective `liftAbs hf`.
* `liftAbs_bijective` — bijective `f` implies bijective `liftAbs hf`.
* `liftAbsEquiv` — package `liftAbs` as an `Equiv` from an equivariant bijection.
* `liftAbsEquiv_abs` — `liftAbsEquiv … (⟪a⟫ x) = ⟪a⟫ f x`.
* `liftAbsEquiv_equivariant` — `liftAbsEquiv` is equivariant.

### Concretion–bind interaction
* `concreteAt_bind_equivariant` — `π • ((F ⊙ a) >>= g) = ((π • F) ⊙ (π • a)) >>= fun x => π • g (π⁻¹ • x)`.
* `concreteAt_bind_of_fix` — simplified form when `π` fixes `F` and `g` is equivariant.

### Concretion as a finitely-supported function (Pitts, equation 4.13)
* `concreteAt_nfun` — package concretion as `α →ᶠˢ Option X`.
* `concreteAt_nfun_apply` — `concreteAt_nfun F a = F ⊙ a`.
* `concreteAt_nfun_equivariant` — `π • concreteAt_nfun F = concreteAt_nfun (π • F)`.
* `isEquivariant_concreteAt_nfun` — `concreteAt_nfun` is equivariant (packaged).
* `concreteAt_nfun_injective` — the embedding `[A]X → (A →ᶠˢ Option X)` is injective.
* `supp_concreteAt_nfun` — `supp (concreteAt_nfun F) = supp F`.

## References

* [A. M. Pitts, *Nominal Sets*][Pitts2013], Definition 4.7, Proposition 4.9, equations 4.15–4.16.
-/

namespace Nominal.Set
open Core

open MulAction PermType

universe u

variable {α : Type u} [Name α] {X : Type u} [Nominal α X]

namespace NameAbs

/-! ### Concretion (Pitts, Definition 4.7 / Proposition 4.9) -/

/-- **Concretion** of a name abstraction at atom `a`: if `a` is the binder, returns the body;
otherwise returns `none`. -/
noncomputable def concreteAt (F : NameAbs α X) (a' : α) : Option X :=
  Quotient.liftOn F
    (fun ⟨a, x⟩ ↦
      if a' = a then some x
      -- a # x is not decidable since it is defined ∩ for any set. Even though supp isn't computable
      -- since it is a finset, set membership is decidable.
      else if a' ∉ supp x then some (swap a a' • x)
      else none)
    (fun ⟨a₁, x₁⟩ ⟨a₂, x₂⟩ h ↦ by
      have heq : ⟪a₁⟫x₁ = ⟪a₂⟫x₂ := Quotient.sound h
      rw [abs_eq_iff] at heq
      rcases heq with ⟨rfl, rfl⟩ | ⟨hne, hfresh, rfl⟩
      · rfl
      · -- a₁ ≠ a₂, a₁ # (a₂, x₂), body is swap a₁ a₂ • x₂
        simp only [fresh_prod_right, fresh_atoms] at hfresh
        obtain ⟨_, ha₁x₂⟩ := hfresh
        by_cases ha₁ : a' = a₁
        · subst ha₁
          have ha'x₂ : a' ∉ supp x₂ := (fresh_atom_left a' x₂).mp ha₁x₂
          simp only [↓reduceIte, hne, ha'x₂, not_false_eq_true, ↓reduceIte]
          rw [swap_comm]
        · by_cases ha₂ : a' = a₂
          · subst ha₂
            have ha'ne : a' ≠ a₁ := Ne.symm hne
            have ha'notin : a' ∉ supp (swap a₁ a' • x₂) :=
              (fresh_atom_left ..).mp ((fresh_smul_left a' (swap a₁ a') x₂).mpr
                (by rw [swap_inv, swap_apply_right]; exact ha₁x₂))
            simp only [ha'ne, ha'notin, not_false_eq_true, ↓reduceIte, swap_smul_swap_smul]
          · -- a' ≠ a₁, a' ≠ a₂: swap a₁ a₂ fixes a', so membership is the same
            have hfix : (swap a₁ a₂) • a' = a' :=
              swap_apply_of_ne (fun h ↦ ha₁ h) (fun h ↦ ha₂ h)
            have hmem' : a' ∈ supp (swap a₁ a₂ • x₂) ↔ a' ∈ supp x₂ := by
              rw [mem_supp_smul, swap_inv, hfix]
            simp only [ha₁, ha₂, ↓reduceIte]
            -- align the decidable condition on both sides
            simp only [show a' ∉ supp (swap a₁ a₂ • x₂) ↔ a' ∉ supp x₂ from not_congr hmem']
            split_ifs with hfx
            · rfl
            · congr 1
              calc swap a₁ a' • swap a₁ a₂ • x₂
                  = (swap a₁ a' * swap a₁ a₂) • x₂ := by rw [mul_smul]
                _ = (swap a₂ a' * swap a₁ a') • x₂ := by rw [swap_mul_swap_comm hne ha₁ ha₂]
                _ = swap a₂ a' • (swap a₁ a' • x₂) := by rw [mul_smul]
                _ = swap a₂ a' • x₂ := by rw [fresh_swap ha₁x₂ ((fresh_atom_left a' x₂).mpr hfx)]
            )

/-- Notation `F ⊙ a` for concretion of `F` at `a`. -/
scoped infixl:90 " ⊙ " => Nominal.Set.NameAbs.concreteAt

/-- Concretion of `⟪a⟫ x` at `a` returns `some x`. -/
@[simp]
theorem concreteAt_abs_self (a : α) (x : X) : ⟪a⟫x ⊙ a = some x := by
  unfold concreteAt abs
  simp only [Quotient.liftOn_mk, ↓reduceIte]

/-- If `a' ≠ a` and `a' # x`, then concretion at `a'` gives `some (swap a a' • x)`. -/
@[simp]
theorem concreteAt_abs_fresh {a a' : α} {x : X} (hne : a' ≠ a) (hfresh : a' # x) : ⟪a⟫x ⊙ a' = some (swap a a' • x) := by
  unfold concreteAt abs
  simp only [Quotient.liftOn_mk, hne, ↓reduceIte, (fresh_atom_left a' x).mp hfresh, not_false_eq_true]

/-- If `a' ≠ a` and `a' ∈ supp x`, then concretion at `a'` gives `none`. -/
@[simp]
theorem concreteAt_abs_not_fresh {a a' : α} {x : X} (hne : a' ≠ a) (hmem : a' ∈ supp x) : ⟪a⟫x ⊙ a' = none := by
  unfold concreteAt abs
  simp only [Quotient.liftOn_mk, hne, ↓reduceIte]
  exact ite_eq_right (not_not.mpr hmem)

/-- **Proposition 4.9, universal version**: for *any* `a # F`, the concretion of `F` at `a`
gives some `y` and `F = ⟪a⟫ y`. (Same conclusion as `abs_concreteAt_eq` but universally quantified over all fresh atoms.) -/
theorem abs_concreteAt_eq_forall {F : NameAbs α X} : ∀ a : α, a # F → ∃ y, F ⊙ a = some y ∧ F = ⟪a⟫y := by
  intro a ha
  induction F using ind with | _ b y =>
  rw [fresh_abs] at ha
  rcases ha with rfl | hay
  · -- a = b: concretion at binder
    exact ⟨y, concreteAt_abs_self a y, rfl⟩
  · -- a # y, a ≠ b (if a = b then a ∈ supp (⟪a⟫ y) but a # ⟪a⟫ y, contradiction)
    by_cases hab : a = b
    · subst hab; exact ⟨y, concreteAt_abs_self a y, rfl⟩
    · refine ⟨swap b a • y, concreteAt_abs_fresh hab hay, ?_⟩
      rw [abs_eq_iff]
      have hbsy : b # swap b a • y := by
        rw [fresh_smul_left, swap_inv, swap_apply_left]; exact hay
      exact Or.inr ⟨Ne.symm hab,
        fresh_prod_right.mpr ⟨(fresh_atoms b a).mpr (Ne.symm hab), hbsy⟩,
        (swap_smul_swap_smul b a y).symm⟩

/-- There exists a fresh atom witnessing Proposition 4.9:
`∃ a, a # F ∧ ∃ y, F ⊙ a = some y ∧ F = ⟪a⟫ y`. -/
theorem abs_concreteAt_eq_exists {F : NameAbs α X} : ∃ a, a # F ∧ ∃ y, F ⊙ a = some y ∧ F = ⟪a⟫y := by
  obtain ⟨a, ha⟩ := exists_fresh_atom (α := α) F
  exact ⟨a, ha, abs_concreteAt_eq_forall a ha⟩

/-- Freshness-quantified version of Proposition 4.9 (equation 4.15):
`И a, ∃ y, F ⊙ a = some y ∧ F = ⟪a⟫ y`. -/
theorem abs_concreteAt_eq_freshQuantifier {F : NameAbs α X} : И a, ∃ y, F ⊙ a = some y ∧ F = ⟪a⟫y :=
  freshQuantifier_mono (fun a ha => abs_concreteAt_eq_forall a ha) (fresh_atom_cofinite F)

/-- If `a` is not fresh for `F`, then `F ⊙ a = none`. -/
theorem concreteAt_eq_none_of_not_fresh {F : NameAbs α X} {a : α} (ha : ¬ a # F) : F ⊙ a = none := by
  induction F using ind with | _ b y =>
  simp only [fresh_abs, not_or, not_fresh_iff] at ha
  exact concreteAt_abs_not_fresh ha.1 ha.2

/-- Concretion is `none` iff the atom is not fresh. -/
@[simp]
theorem concreteAt_none_iff {F : NameAbs α X} {a : α} : F ⊙ a = none ↔ ¬ a # F :=
  ⟨fun h ha => by obtain ⟨y, hy, _⟩ := abs_concreteAt_eq_forall _ ha; simp [hy] at h,
   concreteAt_eq_none_of_not_fresh⟩

/-- Concretion is `some` iff the atom is fresh. -/
@[simp]
theorem concreteAt_isSome_iff {F : NameAbs α X} {a : α} : (F ⊙ a).isSome = true ↔ a # F := by
  simp only [Option.isSome_iff_ne_none, ne_eq, concreteAt_none_iff, not_not]

/-- Variant of `concreteAt_abs_self` with an explicit equality hypothesis. -/
theorem concreteAt_abs_eq {a a' : α} {x : X} (h : a' = a) : ⟪a⟫x ⊙ a' = some x :=
  h ▸ concreteAt_abs_self a x

/-- Unified computation rule for concretion at a representative (equation 4.14): covers all three cases (`a' = a`, `a' # x`, `a' ∈ supp x`) in one statement. -/
theorem concreteAt_abs (a a' : α) (x : X) :
    ⟪a⟫x ⊙ a' = if a' = a then some x
                    else if a' ∉ supp x then some (swap a a' • x)
                    else none := by
  by_cases h₁ : a' = a
  · simp [h₁]
  · by_cases h₂ : a' ∉ supp x
    · simp [h₁, h₂, concreteAt_abs_fresh h₁ ((fresh_atom_left a' x).mpr h₂)]
    · push Not at h₂
      simp [h₁, h₂, concreteAt_abs_not_fresh h₁ h₂]

/-- Injectivity of concretion: if two concretions at the same atom give `some`, the results agree. -/
theorem concreteAt_injective {F : NameAbs α X} {a : α} {y z : X} (hy : F ⊙ a = some y) (hz : F ⊙ a = some z) : y = z :=
  Option.some_injective _ (hy ▸ hz)

/-- If concretion at `a` returns `some y`, then `F = ⟪a⟫ y`. -/
theorem abs_of_concreteAt_eq_some {F : NameAbs α X} {a : α} {y : X} (h : F ⊙ a = some y) : F = ⟪a⟫y := by
  have ha : a # F := concreteAt_isSome_iff.mp (by simp [h])
  obtain ⟨y', hy', heq⟩ := abs_concreteAt_eq_forall _ ha
  rw [heq]; congr 1
  exact concreteAt_injective hy' h

/-- Extracting the concretion value when `a # F`: `Option.get` of `F ⊙ a` recovers the body witnessed by `abs_concreteAt_eq`. -/
theorem concreteAt_get {F : NameAbs α X} {a : α} (_ha : a # F) (h : (F ⊙ a).isSome := by simp [concreteAt_isSome_iff, _ha]) :
    F = ⟪a⟫((F ⊙ a).get h) :=
  abs_of_concreteAt_eq_some (Option.some_get h).symm

/-- Concretion is equivariant: `π • (F ⊙ a) = (π • F) ⊙ (π • a)`. -/
@[simp]
theorem concreteAt_equivariant (π : FinitePerm α) (F : NameAbs α X) (a : α) : π • (F ⊙ a) = (π • F) ⊙ (π • a) := by
  induction F using ind with | _ b x =>
  simp only [abs_equivariant]
  by_cases hab : a = b
  · subst hab; simp
  · by_cases hfx : a # x
    · simp only [concreteAt_abs_fresh hab hfx,
          concreteAt_abs_fresh ((smul_ne_iff π).mpr hab)
            ((fresh_equivariant_iff π).mpr hfx),
          option_smul_some]
      congr 1
      rw [swap_smul_equivariant]
    · have hmem := not_fresh_iff.mp hfx
      have hπmem : π • a ∈ supp (π • x) :=
        not_fresh_iff.mp (by rwa [fresh_equivariant_iff])
      rw [concreteAt_abs_not_fresh hab hmem, option_smul_none,
          concreteAt_abs_not_fresh ((smul_ne_iff π).mpr hab) hπmem]

/-! ### Additional concretion API -/

/-- Noncomputable accessor: extract the body of `F` at a fresh atom `a`. This avoids the repeated `obtain ⟨y, hy, _⟩ := abs_concreteAt_eq_forall` pattern. -/
noncomputable def concreteAt_val (F : NameAbs α X) (a : α) (ha : a # F) : X :=
  (F ⊙ a).get (concreteAt_isSome_iff.mpr ha)

/-- `concreteAt_val` satisfies `F ⊙ a = some (concreteAt_val F a ha)`. -/
theorem concreteAt_val_eq (F : NameAbs α X) (a : α) (ha : a # F) : F ⊙ a = some (concreteAt_val F a ha) :=
  (Option.some_get (concreteAt_isSome_iff.mpr ha)).symm

/-- `concreteAt_val` reconstructs the abstraction: `F = ⟪a⟫ (concreteAt_val F a ha)`. -/
theorem abs_concreteAt_val (F : NameAbs α X) (a : α) (ha : a # F) : F = ⟪a⟫(concreteAt_val F a ha) :=
  abs_of_concreteAt_eq_some (concreteAt_val_eq F a ha)

/-- Congruence of concretion in the abstraction argument. -/
theorem concreteAt_congr {F G : NameAbs α X} (h : F = G) (a : α) : F ⊙ a = G ⊙ a :=
  h ▸ rfl

/-- When both the binder and the target atom are fresh for the body,
concretion returns the body itself (the swap is trivial by freshness). -/
theorem concreteAt_abs_of_both_fresh {a a' : α} {x : X} (ha : a # x) (ha' : a' # x) : ⟪a⟫x ⊙ a' = some x := by
  by_cases h : a' = a
  · subst h; simp
  · rw [concreteAt_abs_fresh h ha', fresh_swap ha ha']

/-- Concretion of a permuted abstraction at the permuted binder returns the
permuted body. -/
@[simp]
theorem concreteAt_smul_abs_self (π : FinitePerm α) (a : α) (x : X) : (π • ⟪a⟫x) ⊙ (π • a) = some (π • x) := by
  simp [abs_equivariant]

/-- Concretion at a representative is `none` iff the atom differs from the binder
and belongs to the support of the body. -/
theorem concreteAt_abs_none_iff {a a' : α} {x : X} : ⟪a⟫x ⊙ a' = none ↔ a' ≠ a ∧ a' ∈ supp x := by
  rw [concreteAt_none_iff, fresh_abs, not_or]
  exact and_congr_right fun hne ↦ not_fresh_iff

/-- Full characterization of `(⟪a⟫ x) ⊙ a' = some y` on representatives:
either `a' = a` and `y = x`, or `a' ≠ a`, `a' # x`, and `y = swap a a' • x`. -/
theorem concreteAt_abs_some_iff' {a a' : α} {x : X} {y : X} :
    ⟪a⟫x ⊙ a' = some y ↔
      (a' = a ∧ y = x) ∨ (a' ≠ a ∧ a' # x ∧ y = swap a a' • x) := by
  constructor
  · intro h
    by_cases h₁ : a' = a
    · subst h₁; simp at h; exact Or.inl ⟨rfl, h.symm⟩
    · by_cases h₂ : a' # x
      · rw [concreteAt_abs_fresh h₁ h₂] at h
        exact Or.inr ⟨h₁, h₂, (Option.some_injective _ h).symm⟩
      · rw [concreteAt_abs_not_fresh h₁ (not_fresh_iff.mp h₂)] at h
        exact absurd h nofun
  · rintro (⟨rfl, rfl⟩ | ⟨hne, hfresh, rfl⟩)
    · simp
    · exact concreteAt_abs_fresh hne hfresh

/-- Full characterisation of `F ⊙ a = some y`: the atom is fresh and the abstraction equals `⟪a⟫ y`. -/
theorem concreteAt_some_iff {F : NameAbs α X} {a : α} {y : X} : F ⊙ a = some y ↔ a # F ∧ F = ⟪a⟫y := by
  constructor
  · exact fun h ↦ ⟨concreteAt_isSome_iff.mp (by simp [h]), abs_of_concreteAt_eq_some h⟩
  · rintro ⟨ha, rfl⟩
    obtain ⟨z, hz, habs⟩ := abs_concreteAt_eq_forall _ ha
    rwa [abs_same_name_iff.mp habs.symm] at hz

/-- Concretion `isNone` iff the atom is not fresh. Complement of `concreteAt_isSome_iff`. -/
@[simp]
theorem concreteAt_isNone_iff {F : NameAbs α X} {a : α} : (F ⊙ a).isNone = true ↔ ¬ a # F := by
  simp [Option.isNone_iff_eq_none, concreteAt_none_iff]

/-- Freshness transfers through concretion: if `b ≠ a`, `b # F`, and `F ⊙ a = some y`,
then `b # y`. (When `b = a` the conclusion can fail, e.g. `(⟪a⟫ a) ⊙ a = some a`.) -/
theorem fresh_of_concreteAt_eq_some {F : NameAbs α X} {a : α} {y : X} (h : F ⊙ a = some y) {b : α} (hba : b ≠ a) (hb : b # F) : b # y := by
  have habs := abs_of_concreteAt_eq_some h
  rw [habs, fresh_abs] at hb
  exact hb.elim (fun h ↦ absurd h hba) id

/-- Support bound for the concretion value: if `F ⊙ a = some y`, then `supp y ⊆ supp F ∪ {a}`. -/
theorem supp_concreteAt_le {F : NameAbs α X} {a : α} {y : X} (h : F ⊙ a = some y) : supp y ⊆ supp F ∪ {a} := by
  have habs := abs_of_concreteAt_eq_some h
  intro b hb
  by_cases hba : b = a
  · exact Finset.mem_union_right _ (Finset.mem_singleton.mpr hba)
  · refine Finset.mem_union_left _ ?_
    rw [habs, supp_abs]
    exact Finset.mem_sdiff.mpr ⟨hb, by simp [hba]⟩

/-- Concretion commutes with swap: specialisation of `concreteAt_equivariant` to `π = swap a b`. -/
theorem concreteAt_swap (a b : α) (F : NameAbs α X) (c : α) : (swap a b • F) ⊙ c = swap a b • (F ⊙ (swap a b • c)) := by
  have h := concreteAt_equivariant (swap a b) F (swap a b • c)
  simp only [smul_smul, swap_mul_self, one_smul] at h
  exact h.symm

/-- Support bound for `F ⊙ a` as an element of `Option X`: `supp (F ⊙ a) ⊆ supp F ∪ {a}`. -/
theorem supp_concreteAt_option_le {F : NameAbs α X} {a : α} : supp (F ⊙ a) ⊆ supp F ∪ {a} := by
  cases h : F ⊙ a with
  | none => simp [supp_none, Finset.empty_subset]
  | some y =>
    simp only [supp_some]
    exact fun b hb ↦ supp_concreteAt_le h hb

/-- Freshness for concretion as `Option X`: if `b # F` and `b ≠ a`, then `b # (F ⊙ a)`. -/
theorem fresh_concreteAt {F : NameAbs α X} {a b : α} (hbF : b # F) (hba : b ≠ a) : b # (F ⊙ a) := by
  rw [fresh_atom_left]
  intro hmem
  have := supp_concreteAt_option_le hmem
  simp only [Finset.mem_union, Finset.mem_singleton] at this
  exact this.elim ((fresh_atom_left b F).mp hbF) hba

/-- Pointwise concretion agreement: `F ⊙ a = G ⊙ a` iff either both are `none` or both are `some` with equal values. -/
theorem concreteAt_eq_iff {F G : NameAbs α X} {a : α} :
    F ⊙ a = G ⊙ a ↔ (¬ a # F ∧ ¬ a # G) ∨ (∃ y, F ⊙ a = some y ∧ G ⊙ a = some y) := by
  constructor
  · intro h
    by_cases haF : a # F
    · obtain ⟨y, hy, _⟩ := abs_concreteAt_eq_forall _ haF
      exact Or.inr ⟨y, hy, h ▸ hy⟩
    · have haG : ¬ a # G := by
        intro haG
        obtain ⟨y, hy, _⟩ := abs_concreteAt_eq_forall _ haG
        rw [← h, concreteAt_none_iff.mpr haF] at hy
        exact absurd hy nofun
      exact Or.inl ⟨haF, haG⟩
  · rintro (⟨haF, haG⟩ | ⟨y, hyF, hyG⟩)
    · rw [concreteAt_none_iff.mpr haF, concreteAt_none_iff.mpr haG]
    · rw [hyF, hyG]

/-- Concretion is equivariant as a binary operation (packaged as `IsEquivariant`). -/
theorem isEquivariant_concreteAt : IsEquivariant α (fun (p : NameAbs α X × α) ↦ p.1 ⊙ p.2) where
  map_smul π p := by
    obtain ⟨F, a⟩ := p
    simp only [Prod.smul_fst, Prod.smul_snd]
    exact (concreteAt_equivariant π F a).symm

/-! ### Extensionality (Pitts, equation 4.16) -/

/-- **Name-abstraction extensionality**: two abstractions are equal iff for fresh-enough
atoms `c`, their concretions at `c` agree. -/
theorem nameAbs_ext {F G : NameAbs α X} : F = G ↔ (И c, F ⊙ c = G ⊙ c) := by
  constructor
  · intro h; subst h; exact freshQuantifier_of_forall (fun _ ↦ rfl)
  · intro hFQ
    induction F using ind with | _ a₁ x₁ =>
    induction G using ind with | _ a₂ x₂ =>
    apply Quotient.sound
    change AlphaEqv a₁ x₁ a₂ x₂; unfold AlphaEqv
    have hfreshFQ : FreshQuantifier (fun c ↦ c # (a₁, x₁, a₂, x₂)) := fresh_atom_cofinite (a₁, x₁, a₂, x₂)
    apply freshQuantifier_mono _ (freshQuantifier_and.mpr ⟨hfreshFQ, hFQ⟩)
    intro c ⟨hcfresh, hceq⟩
    simp only [fresh_prod_right, fresh_atoms] at hcfresh
    obtain ⟨hca₁, hcx₁, hca₂, hcx₂⟩ := hcfresh
    have h₁ : ⟪a₁⟫x₁ ⊙ c = some (swap a₁ c • x₁) := concreteAt_abs_fresh hca₁ hcx₁
    have h₂ : ⟪a₂⟫x₂ ⊙ c = some (swap a₂ c • x₂) := concreteAt_abs_fresh hca₂ hcx₂
    rw [h₁, h₂] at hceq
    exact Option.some_injective _ hceq

/-- The relation `fun c (F, G) ↦ F ⊙ c = G ⊙ c` is equivariant. -/
theorem equivariantRel_concreteAt_eq :
    EquivariantRel α (fun (c : α) (p : NameAbs α X × NameAbs α X) ↦ p.1 ⊙ c = p.2 ⊙ c) where
  smul_iff π c p := by
    simp only [Prod.smul_fst, Prod.smul_snd]
    rw [← concreteAt_equivariant, ← concreteAt_equivariant, smul_left_cancel_iff]

/-- Extensionality (forall form): two abstractions are equal iff for every atom `c`
fresh for both, their concretions at `c` agree. Uses `someAny` (Pitts 3.9). -/
theorem nameAbs_ext_forall {F G : NameAbs α X} : F = G ↔ ∀ c, c # (F, G) → F ⊙ c = G ⊙ c := by
  rw [nameAbs_ext]
  exact someAny_forall (x := (F, G)) equivariantRel_concreteAt_eq

/-- Extensionality (exists form): two abstractions are equal iff there exists an atom `c`
fresh for both at which their concretions agree. Uses `someAny` (Pitts 3.9). -/
theorem nameAbs_ext_exists {F G : NameAbs α X} : F = G ↔ ∃ c, c # (F, G) ∧ F ⊙ c = G ⊙ c := by
  rw [nameAbs_ext_forall]
  exact someAny (x := (F, G)) equivariantRel_concreteAt_eq

/-- Alias for `nameAbs_ext` following Mathlib `_ext_iff` naming convention. -/
theorem nameAbs_ext_iff {F G : NameAbs α X} : F = G ↔ (И c, F ⊙ c = G ⊙ c) :=
  nameAbs_ext

/-! ### Functorial action (map) -/

/-- Functorial map: given an equivariant function `f : X → Y`, lift it to
`NameAbs α X → NameAbs α Y` by `⟪a⟫ x ↦ ⟪a⟫ f x`. -/
noncomputable def liftAbs {Y : Type u} [Nominal α Y] {f : X → Y} (hf : IsEquivariant α f) : NameAbs α X → NameAbs α Y :=
  fun F ↦ Quotient.liftOn F
    (fun p ↦ ⟪p.1⟫(f p.2))
    (fun ⟨a₁, x₁⟩ ⟨a₂, x₂⟩ h ↦ by
      have heq : ⟪a₁⟫x₁ = ⟪a₂⟫x₂ := Quotient.sound h
      rw [abs_eq_iff] at heq
      rcases heq with ⟨rfl, rfl⟩ | ⟨hne, hfresh, hrename⟩
      · rfl
      · rw [abs_eq_iff]
        refine Or.inr ⟨hne, ?_, ?_⟩
        · simp only [fresh_prod_right, fresh_atoms] at hfresh ⊢
          exact ⟨hfresh.1, fresh_of_equivariant hf hfresh.2⟩
        · rw [hrename, hf.map_smul])

/-- `liftAbs` commutes with `abs`: `liftAbs hf (⟪a⟫ x) = ⟪a⟫ f x`. -/
@[simp]
theorem liftAbs_abs {Y : Type u} [Nominal α Y] {f : X → Y} (hf : IsEquivariant α f) (a : α) (x : X) :
  liftAbs hf ⟪a⟫x = ⟪a⟫(f x) := rfl

/-- `liftAbs` is equivariant. -/
@[simp]
theorem liftAbs_equivariant {Y : Type u} [Nominal α Y] {f : X → Y} (hf : IsEquivariant α f) (π : FinitePerm α) (F : NameAbs α X) :
  liftAbs hf (π • F) = π • liftAbs hf F := by
  induction F using ind with | _ a x => simp [hf.map_smul]

/-- Uniqueness of `liftAbs`: any function that agrees with `liftAbs hf` on al representatives must equal it. -/
theorem liftAbs_unique {Y : Type u} [Nominal α Y] {f : X → Y} (hf : IsEquivariant α f)
    (g : NameAbs α X → NameAbs α Y) (hg : ∀ (a : α) (x : X), g ⟪a⟫x = ⟪a⟫(f x)) : g = liftAbs hf := by
  funext F; induction F using ind with | _ a x =>
  rw [hg, liftAbs_abs]

/-- Map–concretion interaction for fresh atoms: `(liftAbs hf F) ⊙ a = Option.map f (F ⊙ a)` when `a # F`. -/
theorem liftAbs_concreteAt {Y : Type u} [Nominal α Y] {f : X → Y} (hf : IsEquivariant α f) (F : NameAbs α X) (a : α) (ha : a # F) :
    (liftAbs hf F) ⊙ a = Option.map f (F ⊙ a) := by
  induction F using ind with | _ b x =>
  rw [liftAbs_abs]
  rw [fresh_abs] at ha
  rcases ha with rfl | hax
  · simp
  · have hfx : a # f x := fresh_of_equivariant hf hax
    by_cases hab : a = b
    · subst hab; simp
    · simp only [concreteAt_abs_fresh hab hax, concreteAt_abs_fresh hab hfx,
        Option.map_some, hf.map_smul]

/-- Support bound for `liftAbs`: `supp (liftAbs hf F) ⊆ supp F`. -/
theorem supp_liftAbs_le {Y : Type u} [Nominal α Y] {f : X → Y} (hf : IsEquivariant α f) (F : NameAbs α X) :
    supp (liftAbs hf F) ⊆ supp F := by
  induction F using ind with | _ a x =>
  simp only [liftAbs_abs, supp_abs]
  exact Finset.sdiff_subset_sdiff (supp_map_le hf x) (Finset.Subset.refl _)

/-- И-quantified version of `liftAbs_concreteAt`: for cofinitely many `a`, `(liftAbs hf F) ⊙ a = Option.map f (F ⊙ a)`. -/
theorem liftAbs_concreteAt_freshQuantifier {Y : Type u} [Nominal α Y] {f : X → Y} (hf : IsEquivariant α f) (F : NameAbs α X) :
    И a, (liftAbs hf F) ⊙ a = Option.map f (F ⊙ a) :=
  freshQuantifier_mono (fun a ha ↦ liftAbs_concreteAt hf F a ha) (fresh_atom_cofinite F)

/-- `liftAbs id` is the identity. -/
@[simp]
theorem liftAbs_id : liftAbs (isEquivariant_id : IsEquivariant α (id : X → X)) = id := by
  funext F; induction F using ind with | _ a x => simp

/-- `liftAbs` composes: `liftAbs hg ∘ liftAbs hf = liftAbs (hg.comp hf)`. -/
theorem liftAbs_comp {Y Z : Type u} [Nominal α Y] [Nominal α Z] {f : X → Y} (hf : IsEquivariant α f) {g : Y → Z} (hg : IsEquivariant α g)
    (F : NameAbs α X) : liftAbs hg (liftAbs hf F) = liftAbs (hg.comp hf) F := by
  induction F using ind with | _ a x => simp

/-- If `f` is injective, then `liftAbs hf` is injective. -/
theorem liftAbs_injective {Y : Type u} [Nominal α Y] {f : X → Y} (hf : IsEquivariant α f) (hinj : Function.Injective f) :
    Function.Injective (liftAbs hf) := by
  intro F G h
  rw [nameAbs_ext]
  have hFQ := nameAbs_ext.mp h
  apply freshQuantifier_mono _ (freshQuantifier_and.mpr ⟨fresh_atom_cofinite F,
    freshQuantifier_and.mpr ⟨fresh_atom_cofinite G, hFQ⟩⟩)
  intro c ⟨hcF, hcG, hceq⟩
  rw [liftAbs_concreteAt hf F c hcF, liftAbs_concreteAt hf G c hcG] at hceq
  exact Option.map_injective hinj hceq

/-- If `f` is surjective, then `liftAbs hf` is surjective. -/
theorem liftAbs_surjective {Y : Type u} [Nominal α Y] {f : X → Y} (hf : IsEquivariant α f) (hsurj : Function.Surjective f) :
    Function.Surjective (liftAbs hf) := by
  intro G; induction G using ind with | _ a y =>
  obtain ⟨x, rfl⟩ := hsurj y
  exact ⟨⟪a⟫x, liftAbs_abs hf a x⟩

/-! ### Additional liftAbs API -/

/-- `liftAbs hf` is equivariant (packaged as `IsEquivariant`). -/
theorem isEquivariant_liftAbs {Y : Type u} [Nominal α Y] {f : X → Y} (hf : IsEquivariant α f) : IsEquivariant α (liftAbs hf) where
  map_smul π F := liftAbs_equivariant hf π F

/-- Freshness transfers through `liftAbs`: if `a # F` then `a # liftAbs hf F`. -/
theorem fresh_liftAbs {Y : Type u} [Nominal α Y] {f : X → Y} (hf : IsEquivariant α f) {F : NameAbs α X} {a : α} (ha : a # F) :
    a # liftAbs hf F :=
  fresh_of_supp_subset (supp_liftAbs_le hf F) ha

/-- If `f` is bijective, then `liftAbs hf` is bijective. -/
theorem liftAbs_bijective {Y : Type u} [Nominal α Y] {f : X → Y} (hf : IsEquivariant α f) (hbij : Function.Bijective f) : Function.Bijective (liftAbs hf) :=
  ⟨liftAbs_injective hf hbij.1, liftAbs_surjective hf hbij.2⟩

/-- Map–concretion interaction for injective `f`: `(liftAbs hf F) ⊙ a = Option.map f (F ⊙ a)`
for all atoms `a`. Injectivity ensures `supp (f x) = supp x`, so the none/some cases align. -/
@[simp]
theorem liftAbs_concreteAt_eq {Y : Type u} [Nominal α Y] {f : X → Y} (hf : IsEquivariant α f) (hinj : Function.Injective f)
    (F : NameAbs α X) (a : α) : (liftAbs hf F) ⊙ a = Option.map f (F ⊙ a) := by
  induction F using ind with | _ b x =>
  rw [liftAbs_abs]
  by_cases hab : a = b
  · subst hab; simp
  · by_cases hax : a # x
    · have hfx : a # f x := fresh_of_equivariant hf hax
      simp [concreteAt_abs_fresh hab hax, concreteAt_abs_fresh hab hfx, hf.map_smul]
    · have hax' : a ∈ supp x := not_fresh_iff.mp hax
      have hfx' : a ∈ supp (f x) := by
        rw [supp_map_injective hf hinj]; exact hax'
      simp [concreteAt_abs_not_fresh hab hax', concreteAt_abs_not_fresh hab hfx']

/-- Support equality for `liftAbs` when `f` is injective:
`supp (liftAbs hf F) = supp F`. -/
theorem supp_liftAbs_eq {Y : Type u} [Nominal α Y] {f : X → Y} (hf : IsEquivariant α f) (hinj : Function.Injective f)
    (F : NameAbs α X) : supp (liftAbs hf F) = supp F := by
  induction F using ind with | _ a x =>
  simp only [liftAbs_abs, supp_abs]
  rw [supp_map_injective hf hinj]

/-! ### Additional liftAbs–concretion interaction -/

/-- Forall form of `liftAbs_concreteAt`: for all `a # F`, `(liftAbs hf F) ⊙ a = Option.map f (F ⊙ a)`. -/
theorem liftAbs_concreteAt_forall {Y : Type u} [Nominal α Y] {f : X → Y} (hf : IsEquivariant α f) (F : NameAbs α X) :
    ∀ a, a # F → (liftAbs hf F) ⊙ a = Option.map f (F ⊙ a) :=
  fun a ha ↦ liftAbs_concreteAt hf F a ha

/-- If `a # F` and `(liftAbs hf F) ⊙ a = some z`, then there exists `y`
with `f y = z` and `F ⊙ a = some y`.  This is a direct consequence of `liftAbs_concreteAt`. -/
theorem liftAbs_concreteAt_some {Y : Type u} [Nominal α Y] {f : X → Y} (hf : IsEquivariant α f)
    {F : NameAbs α X} {a : α} {z : Y} (haF : a # F) (h : (liftAbs hf F) ⊙ a = some z) : ∃ y, f y = z ∧ F ⊙ a = some y := by
  rw [liftAbs_concreteAt hf F a haF] at h
  cases hFa : F ⊙ a with
  | none => simp [hFa] at h
  | some y => simp only [hFa, Option.map_some, Option.some.injEq] at h; exact ⟨y, h, rfl⟩

/-- Extensionality for `liftAbs`: `liftAbs hf = liftAbs hg` iff `f = g`. -/
theorem liftAbs_ext {Y : Type u} [Nominal α Y] {f g : X → Y} (hf : IsEquivariant α f) (hg : IsEquivariant α g) :
    liftAbs hf = liftAbs hg ↔ f = g := by
  constructor
  · intro h
    funext x
    obtain ⟨a, ha⟩ := exists_fresh_atom (α := α) x
    have : liftAbs hf ⟪a⟫x = liftAbs hg ⟪a⟫x := congrFun h _
    simp only [liftAbs_abs, abs_same_name_iff] at this
    exact this
  · intro h; subst h; rfl

/-- `liftAbs` of a constant equivariant function on representatives. -/
theorem liftAbs_const_abs {Y : Type u} [Nominal α Y] {y : Y} (hy : IsEquivariant α (fun (_ : X) ↦ y)) (a : α) (x : X) :
    liftAbs hy ⟪a⟫x = ⟪a⟫y := by
  simp

/-- Function-level composition law for `liftAbs`:
`liftAbs hg ∘ liftAbs hf = liftAbs (hg.comp hf)`. -/
theorem liftAbs_comp_fun {Y Z : Type u} [Nominal α Y] [Nominal α Z] {f : X → Y} (hf : IsEquivariant α f) {g : Y → Z} (hg : IsEquivariant α g) :
    liftAbs hg ∘ liftAbs hf = liftAbs (hg.comp hf) :=
  funext (liftAbs_comp hf hg)

/-! ### Functorial equivalence -/

/-- Package `liftAbs` as an `Equiv` when the underlying equivariant function is
bijective. This gives `[A]X ≃ [A]Y` from any equivariant bijection, simplifying
constructions of structural isos like `prodEquiv`, `sumEquiv`, etc. in FCB.
API completeness for `liftAbs_bijective` (Pitts, Lemma 4.10). -/
noncomputable def liftAbsEquiv {Y : Type u} [Nominal α Y]
    {f : X → Y} (hf : IsEquivariant α f) {g : Y → X} (hg : IsEquivariant α g)
    (hfg : Function.LeftInverse g f) (hgf : Function.RightInverse g f) :
    NameAbs α X ≃ NameAbs α Y where
  toFun := liftAbs hf
  invFun := liftAbs hg
  left_inv F := by
    induction F using ind with | _ a x =>
    simp [hfg x]
  right_inv G := by
    induction G using ind with | _ a y =>
    simp [hgf y]

/-- `liftAbsEquiv` on representatives: `liftAbsEquiv hf hg hfg hgf (⟪a⟫ x) = ⟪a⟫ f x`. -/
@[simp]
theorem liftAbsEquiv_abs {Y : Type u} [Nominal α Y]
    {f : X → Y} (hf : IsEquivariant α f) {g : Y → X} (hg : IsEquivariant α g)
    (hfg : Function.LeftInverse g f) (hgf : Function.RightInverse g f)
    (a : α) (x : X) : liftAbsEquiv hf hg hfg hgf ⟪a⟫x = ⟪a⟫(f x) :=
  liftAbs_abs hf a x

/-- `liftAbsEquiv` is equivariant. -/
theorem liftAbsEquiv_equivariant {Y : Type u} [Nominal α Y]
    {f : X → Y} (hf : IsEquivariant α f) {g : Y → X} (hg : IsEquivariant α g)
    (hfg : Function.LeftInverse g f) (hgf : Function.RightInverse g f)
    (π : FinitePerm α) (F : NameAbs α X) :
    liftAbsEquiv hf hg hfg hgf (π • F) = π • liftAbsEquiv hf hg hfg hgf F :=
  liftAbs_equivariant hf π F

/-! ### Concretion–bind interaction -/

/-- Concretion composes with `Option.bind` equivariantly:
`π • ((F ⊙ a) >>= g) = ((π • F) ⊙ (π • a)) >>= fun x => π • g (π⁻¹ • x)`.
This is the key equivariance lemma for the `z ⊙ a >>= ...` pattern used in
FCB.lean (equation 4.34) for `liftFCB_nfun`. -/
theorem concreteAt_bind_equivariant {Y : Type u} [Nominal α Y]
    (π : FinitePerm α) (F : NameAbs α X) (a : α) (g : X → Option Y) :
    π • ((F ⊙ a) >>= g) = ((π • F) ⊙ (π • a)) >>= fun x => π • g (π⁻¹ • x) := by
  rw [← concreteAt_equivariant]
  cases h : F ⊙ a with
  | none => simp
  | some x =>
    change π • g x = (some (π • x) >>= fun x => π • g (π⁻¹ • x))
    simp

/-- Simplified form of `concreteAt_bind_equivariant` when `π` fixes `F` and `g`
is equivariant: `(F ⊙ (π • a)) >>= g = π • ((F ⊙ a) >>= g)`.
This is the exact pattern needed in the `liftFCB_nfun` supports proof. -/
theorem concreteAt_bind_of_fix {Y : Type u} [Nominal α Y]
    (π : FinitePerm α) (F : NameAbs α X) (a : α) (g : X → Option Y) (hπF : π • F = F)
    (hg : ∀ x, g (π • x) = π • g x) : (F ⊙ (π • a)) >>= g = π • ((F ⊙ a) >>= g) := by
  conv_lhs => rw [← hπF, ← concreteAt_equivariant]
  cases h : F ⊙ a with
  | none => simp
  | some x =>
    change g (π • x) = π • g x
    exact hg x

/-! ### Concretion as a finitely-supported function (Pitts, equation 4.13) -/

/-- Package concretion as a finitely-supported function `α →ᶠˢ Option X`,
realizing the inclusion `[A]X ⊆ (A ⇀_fs X)` from equation 4.13. -/
noncomputable def concreteAt_nfun (F : NameAbs α X) : NFun α α (Option X) :=
  NFun.ofSupports ⟨fun a ↦ F ⊙ a⟩ (supp F) (by
    rw [supports_pfun_iff]
    intro π hπ a
    calc F ⊙ (π • a)
        = π • (F ⊙ a) := by rw [concreteAt_equivariant]; congr 1; exact (supp_supports F π hπ).symm
      _ = π • (F ⊙ a) := rfl)

/-- `concreteAt_nfun F a = F ⊙ a`. -/
@[simp]
theorem concreteAt_nfun_apply (F : NameAbs α X) (a : α) :
    concreteAt_nfun F a = F ⊙ a := rfl

/-- `concreteAt_nfun` is equivariant: `π • concreteAt_nfun F = concreteAt_nfun (π • F)`. -/
theorem concreteAt_nfun_equivariant (π : FinitePerm α) (F : NameAbs α X) :
    π • concreteAt_nfun F = concreteAt_nfun (π • F) := by
  apply NFun.ext; intro a
  change π • (F ⊙ (π⁻¹ • a)) = (π • F) ⊙ a
  rw [concreteAt_equivariant π F (π⁻¹ • a), PermType.smul_inv_smul]

/-- `concreteAt_nfun` is equivariant (packaged as `IsEquivariant`). -/
theorem isEquivariant_concreteAt_nfun : IsEquivariant α (concreteAt_nfun : NameAbs α X → NFun α α (Option X)) where
  map_smul π F := (concreteAt_nfun_equivariant π F).symm

/-- The embedding `concreteAt_nfun : NameAbs α X → NFun α α (Option X)` is injective.
This follows from extensionality (`nameAbs_ext`) and says that different name
abstractions give different concretion functions (Pitts, Section 4.3, equation 4.13). -/
theorem concreteAt_nfun_injective : Function.Injective (concreteAt_nfun : NameAbs α X → NFun α α (Option X)) := by
  intro F G h
  rw [nameAbs_ext]
  apply freshQuantifier_mono (fun a ha ↦ ?_) (fresh_atom_cofinite F)
  have : concreteAt_nfun F a = concreteAt_nfun G a := congrFun (congrArg DFunLike.coe h) a
  exact this

/-- Support of `concreteAt_nfun F` equals `supp F`. -/
theorem supp_concreteAt_nfun (F : NameAbs α X) : supp (concreteAt_nfun F) = supp F :=
  supp_map_injective isEquivariant_concreteAt_nfun concreteAt_nfun_injective F

end NameAbs

end Nominal.Set
