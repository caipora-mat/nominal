import NominalSets.FCB

/-!
# Structural isomorphisms of the name abstraction functor

This file collects the structural isomorphisms and adjunctions of the name abstraction
functor `[A]_`, together with the separated product, left adjoint, right adjoint, and
generalized name abstraction.

**Note:** All definitions and theorems whose bodies are `sorry` are present as stubs with
correct signatures; their proofs are deferred.

## Main definitions

### Structural isomorphisms
* `NameAbs.absAtomEquiv` — the equivalence `[A]A ≃ A ⊕ Unit` (Example 4.18).
* `NameAbs.prodEquiv` — the equivalence `[A](X × Y) ≃ [A]X × [A]Y` (eq. 4.28).
* `NameAbs.sumEquiv` — the equivalence `[A](X ⊕ Y) ≃ [A]X ⊕ [A]Y` (eq. 4.27).
* `NameAbs.discreteEquiv hdisc` — `[A]X ≃ X` when every element of `X` has empty support
  (eq. 4.12).
* `NameAbs.unitEquiv` — `[A]Unit ≃ Unit` (special case of `discreteEquiv`).
* `NameAbs.expEquiv` — the equivalence `[A](X →ᶠˢ Y) ≃ [A]X →ᶠˢ [A]Y` (Proposition 4.14).
* `NameAbs.absAbsAtomEquiv` — `[A]([A]A) ≃ [A]A ⊕ [A]Unit` (Exercise 4.1 extended).

### Enriched functor (Remark 4.11)
* `NameAbs.liftAbs_NFun` — the enriched action `(X →ᶠˢ Y) → ([A]X →ᶠˢ [A]Y)`.

### Separated product and left adjunction (Pitts, Theorem 4.12)
* `NameAbs.SepProd α X` — the separated product `{ (x, a) | x # a }`.
* `NameAbs.adjCounit` — the counit `SepProd α ([A]X) → X` (eq. 4.20).
* `NameAbs.adjUnit` — the unit `X → [A](SepProd α X)` (Theorem 4.12).
* `NameAbs.adjCurry` — the currying map of the left adjunction (eq. 4.22).
* `NameAbs.sepProdAbsEquiv` — `SepProd α ([A]X) ≃ α × X` (Exercise 4.2).
* `NameAbs.sepProdDistribEquiv` — `[A](X₁ * X₂) ≃ [A]X₁ * X₂ ⊕ X₁ * [A]X₂` (Exercise 4.6).

### Right adjoint (Pitts, Theorem 4.13)
* `NameAbs.RightAdj α X` — the right adjoint `{ f : α →ᶠˢ X | ∀ a, a # f a }` (eq. 4.23).
* `NameAbs.rightAdjCounit` — the counit `[A](R X) → X` (eq. 4.24).
* `NameAbs.rightAdjUnit` — the unit `Y → R([A]Y)` (eq. 4.26).

### Generalized abstraction (Section 4.6)
* `NameAbs.GenAlphaEqv` — generalized alpha-equivalence (Definition 4.20).
* `NameAbs.GenNameAbs` — the quotient `[X]Y` (Definition 4.20).

## Main results

### Structural isomorphisms
* `absAtomEquiv_abs_eq` — `absAtomEquiv (abs a a) = Sum.inr ()`.
* `absAtomEquiv_abs_ne` — `a ≠ a' → absAtomEquiv (abs a a') = Sum.inl a'`.
* `absAtomEquiv_symm_inr` — inverse on `Sum.inr ()`.
* `absAtomEquiv_symm_inl` — inverse on `Sum.inl a'`.
* `absAtomEquiv_injective` / `absAtomEquiv_surjective` — explicit inj/surj.
* `absAtomEquiv_equivariant` — equivariance of `absAtomEquiv`.
* `prodEquiv_abs` — `prodEquiv (abs a (x, y)) = (abs a x, abs a y)`.
* `prodEquiv_symm_abs` — inverse computation with fresh renaming.
* `prodEquiv_equivariant` — equivariance of `prodEquiv`.
* `sumEquiv_inl` / `sumEquiv_inr` — computation on tagged values.
* `sumEquiv_equivariant` — equivariance of `sumEquiv`.
* `discreteEquiv_abs` — `discreteEquiv hdisc (abs a x) = x`.
* `discreteEquiv_symm` — inverse: `discreteEquiv.symm x = abs a x`.
* `discreteEquiv_equivariant` — equivariance of `discreteEquiv`.
* `expEquiv_abs_abs` — `expEquiv (abs a f) (abs a x) = abs a (f x)`.
* `expEquiv_equivariant` — equivariance of `expEquiv`.
* `abs_self_eq` — `abs a a = abs a' a'` (all self-bindings in `[A]A` are equal).
* `abs_abs_ne` — `a ≠ a' → abs a (abs a a) ≠ abs a (abs a' a)`.

### Left adjunction (Theorem 4.12)
* `adjCounit_adjCurry` / `adjCurry_adjCounit` — triangle identities.
* `adjUnit_equivariant` — equivariance of the unit.
* `adjCurry_eq_abs` — computation rule for `adjCurry`.
* `sepProdAbsEquiv_mk` / `sepProdAbsEquiv_symm_mk` — computation rules.
* `sepProdAbsEquiv_equivariant` — equivariance.

### Right adjunction (Theorem 4.13)
* `rightAdjCounit_eq` / `rightAdjUnit_val_apply` — computation rules.
* `rightAdj_counit_unit` / `rightAdj_unit_counit` — triangle identities.
* `rightAdj_characterization` — eq. 4.26 characterization.

### Negative results
* `not_enriched_left_adjunction` — `_ * A ⊣ [A]_` is NOT Nom-enriched (Exercise 4.7).
* `not_enriched_right_adjunction` — `[A]_ ⊣ R` is NOT Nom-enriched (Exercise 4.7).

### Generalized abstraction (Section 4.6)
* `supp_genAbs` — `supp ⟨x⟩y = supp y \ supp x` (Proposition 4.23).
* `genAbs_exists_fresh_rep` — fresh representative lemma (Lemma 4.24).
* `genAbsAtomEquiv` — `[A]Y ≅ GenNameAbs A Y` (Remark 4.21, Exercise 4.8).
* `genAlphaEqv_iff_bounded_support` — bounded support characterization (Exercise 4.8).
* `genAbs_finset_not_preserve_prod` — `[P_f A]_` does not preserve products (Example 4.25).

## References

* [A. M. Pitts, *Nominal Sets*][Pitts2013], Chapter 4, Sections 4.3–4.6.
-/

namespace NominalSets

open MulAction PermType

universe u

variable {α : Type u} [Name α] {X : Type u} [Nominal α X]

namespace NameAbs

/-! ### Structural isomorphisms -/

section Structural

variable {Y : Type u} [Nominal α Y]

/-! #### `[A]A ≅ A ⊕ Unit` (Pitts, Example 4.18, eq. 4.40) -/

/-- The name abstraction of atoms: `[A]A ≅ A ⊕ Unit`.
Sends `⟪a⟫ a ↦ inr ()` (self-binding) and `⟪a⟫ a' ↦ inl a'` (when `a ≠ a'`). -/
noncomputable def absAtomEquiv : NameAbs α α ≃ (α ⊕ Unit) where
  toFun := sorry
  invFun := sorry
  left_inv := sorry
  right_inv := sorry

@[simp]
theorem absAtomEquiv_abs_eq (a : α) :
    absAtomEquiv (abs a a) = Sum.inr () := sorry

@[simp]
theorem absAtomEquiv_abs_ne {a a' : α} (h : a ≠ a') :
    absAtomEquiv (abs a a') = Sum.inl a' := sorry

/-- `absAtomEquiv` commutes with the permutation action (equivariance). -/
theorem absAtomEquiv_equivariant (π : FinitePerm α) (F : NameAbs α α) :
    absAtomEquiv (π • F) = Sum.map (π • ·) id (absAtomEquiv F) := sorry

/-- Inverse of `absAtomEquiv` on `Sum.inr ()`: produces a self-binding.
    Pitts, Example 4.18. -/
@[simp]
theorem absAtomEquiv_symm_inr :
    absAtomEquiv.symm (Sum.inr () : α ⊕ Unit) =
      abs (Classical.arbitrary α) (Classical.arbitrary α) := sorry

/-- Inverse of `absAtomEquiv` on `Sum.inl a'`: `⟪a⟫a'` for some fresh `a`.
    Pitts, Example 4.18. -/
theorem absAtomEquiv_symm_inl (a' : α) :
    ∃ a, a ≠ a' ∧ absAtomEquiv.symm (Sum.inl a') = abs a a' := sorry

/-- `absAtomEquiv` is injective (part of Example 4.18). -/
theorem absAtomEquiv_injective :
    Function.Injective (absAtomEquiv : NameAbs α α → α ⊕ Unit) :=
  absAtomEquiv.injective

/-- `absAtomEquiv` is surjective (part of Example 4.18). -/
theorem absAtomEquiv_surjective :
    Function.Surjective (absAtomEquiv : NameAbs α α → α ⊕ Unit) :=
  absAtomEquiv.surjective

/-! #### Preservation of products (Pitts, eq. 4.28, Exercise 4.4) -/

/-- `[A](X × Y) ≅ [A]X × [A]Y` (eq. 4.28).
Since `[A]_` is a right adjoint, it preserves limits — in particular products. -/
noncomputable def prodEquiv :
    NameAbs α (X × Y) ≃ NameAbs α X × NameAbs α Y where
  toFun := sorry
  invFun := sorry
  left_inv := sorry
  right_inv := sorry

@[simp]
theorem prodEquiv_abs (a : α) (x : X) (y : Y) :
    prodEquiv (abs a (x, y)) = (abs a x, abs a y) := sorry

/-- `prodEquiv` commutes with the permutation action (equivariance). -/
theorem prodEquiv_equivariant (π : FinitePerm α) (F : NameAbs α (X × Y)) :
    prodEquiv (π • F) = π • prodEquiv F := sorry

/-- The inverse of `prodEquiv` uses fresh renaming to pair abstractions:
    `prodEquiv.symm (⟪a₁⟫x₁, ⟪a₂⟫x₂) = fresh a in ⟪a⟫((a a₁)·x₁, (a a₂)·x₂)`.
    Pitts, Exercise 4.4. -/
theorem prodEquiv_symm_abs (a₁ : α) (x₁ : X) (a₂ : α) (y₂ : Y) :
    ∃ a, a # (a₁, x₁, a₂, y₂) ∧
      prodEquiv.symm (abs a₁ x₁, abs a₂ y₂) =
        abs a (swap a a₁ • x₁, swap a a₂ • y₂) := sorry

/-! #### Preservation of coproducts (Pitts, eq. 4.27, Exercise 4.5) -/

/-- `[A](X ⊕ Y) ≅ [A]X ⊕ [A]Y` (eq. 4.27).
Since `[A]_` has a right adjoint (Theorem 4.13), it preserves colimits — in particular
coproducts. -/
noncomputable def sumEquiv :
    NameAbs α (X ⊕ Y) ≃ NameAbs α X ⊕ NameAbs α Y where
  toFun := sorry
  invFun := sorry
  left_inv := sorry
  right_inv := sorry

@[simp]
theorem sumEquiv_inl (a : α) (x : X) :
    sumEquiv (abs a (Sum.inl x) : NameAbs α (X ⊕ Y)) = Sum.inl (abs a x) := sorry

@[simp]
theorem sumEquiv_inr (a : α) (y : Y) :
    sumEquiv (abs a (Sum.inr y) : NameAbs α (X ⊕ Y)) = Sum.inr (abs a y) := sorry

/-- `sumEquiv` commutes with the permutation action (equivariance). -/
theorem sumEquiv_equivariant (π : FinitePerm α) (F : NameAbs α (X ⊕ Y)) :
    sumEquiv (π • F) = π • sumEquiv F := sorry

/-! #### Discrete nominal sets (Pitts, Example 4.6) -/

/-- For discrete `X` (empty support for all elements), `[A]X ≅ X` (eq. 4.12). -/
noncomputable def discreteEquiv (hdisc : ∀ (x : X), supp x = ∅) :
    NameAbs α X ≃ X where
  toFun := sorry
  invFun := sorry
  left_inv := sorry
  right_inv := sorry

@[simp]
theorem discreteEquiv_abs (hdisc : ∀ (x : X), supp x = ∅) (a : α) (x : X) :
    discreteEquiv hdisc (abs a x) = x := sorry

/-- `discreteEquiv` commutes with the permutation action (equivariance). -/
theorem discreteEquiv_equivariant (hdisc : ∀ (x : X), supp x = ∅)
    (π : FinitePerm α) (F : NameAbs α X) :
    discreteEquiv hdisc (π • F) = π • discreteEquiv hdisc F := sorry

/-- Inverse of `discreteEquiv`: sends `x` to `⟪a⟫x` for any `a`, since all
    such abstractions are equal when `supp x = ∅`.
    Pitts, Example 4.6. -/
theorem discreteEquiv_symm (hdisc : ∀ (x : X), supp x = ∅) (x : X) (a : α) :
    discreteEquiv hdisc (abs a x) = x := sorry

/-! #### Nested abstractions (Pitts, Exercise 4.1) -/

/-- All self-bindings in `[A]A` are equal: `⟪a⟫a = ⟪a'⟫a'`. This is the unique element
mapping to `Sum.inr ()` under `absAtomEquiv`. -/
theorem abs_self_eq (a a' : α) : abs a a = abs a' (a' : α) := sorry

/-- `⟪a⟫(⟪a⟫a) ≠ ⟪a⟫(⟪a'⟫a)` when `a ≠ a'` (Exercise 4.1). -/
theorem abs_abs_ne {a a' : α} (h : a ≠ a') :
    abs a (abs a a) ≠ abs a (abs a' a) := sorry

end Structural

/-! ### Preservation of exponentials (Pitts, Proposition 4.14) -/

/-- `[A](X →ᶠˢ Y) ≅ [A]X →ᶠˢ [A]Y` (Proposition 4.14). -/
noncomputable def expEquiv {Y : Type u} [Nominal α Y] :
    NameAbs α (NFun α X Y) ≃ NFun α (NameAbs α X) (NameAbs α Y) where
  toFun := sorry
  invFun := sorry
  left_inv := sorry
  right_inv := sorry

/-- Forward direction of `expEquiv` applied to `⟪a⟫f` and `⟪a⟫x`:
    `expEquiv (⟪a⟫f) (⟪a⟫x) = ⟪a⟫(f x)`.
    Pitts, Proposition 4.14, eq. 4.29. -/
@[simp]
theorem expEquiv_abs_abs {Y : Type u} [Nominal α Y]
    (a : α) (f : NFun α X Y) (x : X) :
    expEquiv (abs a f) (abs a x) = abs a (f x) := sorry

/-- Backward direction: `expEquiv.symm f = fresh a in ⟪a⟫(λx. f(⟪a⟫x) @ a)`.
    Pitts, Proposition 4.14, eq. 4.30. -/
theorem expEquiv_symm_abs {Y : Type u} [Nominal α Y]
    (f : NFun α (NameAbs α X) (NameAbs α Y)) (a : α) (ha : a # f) :
    ∃ g, expEquiv.symm f = abs a g := sorry

/-- `expEquiv` is equivariant. -/
theorem expEquiv_equivariant {Y : Type u} [Nominal α Y]
    (π : FinitePerm α) (F : NameAbs α (NFun α X Y)) :
    expEquiv (π • F) = π • expEquiv F := sorry

/-! ### Enriched functor (Pitts, Remark 4.11) -/

/-- The enriched functorial action `(X →ᶠˢ Y) → ([A]X →ᶠˢ [A]Y)` making
    `[A]_` into a Nom-enriched functor (Remark 4.11, eq. 4.17). -/
noncomputable def liftAbs_NFun {Y : Type u} [Nominal α Y]
    (f : NFun α X Y) : NFun α (NameAbs α X) (NameAbs α Y) := sorry

/-- `liftAbs_NFun` is equivariant as a function on NFun. -/
theorem liftAbs_NFun_equivariant {Y : Type u} [Nominal α Y]
    (π : FinitePerm α) (f : NFun α X Y) :
    liftAbs_NFun (π • f) = π • liftAbs_NFun f := sorry

/-- `liftAbs_NFun` preserves identity. -/
@[simp]
theorem liftAbs_NFun_id :
    liftAbs_NFun (NFun.id : NFun α X X) = NFun.id := sorry

/-- `liftAbs_NFun` preserves composition. -/
theorem liftAbs_NFun_comp {Y Z : Type u} [Nominal α Y] [Nominal α Z]
    (g : NFun α Y Z) (f : NFun α X Y) :
    liftAbs_NFun (g.comp f) = (liftAbs_NFun g).comp (liftAbs_NFun f) := sorry

/-! ### `[A]_` preserves equalizers -/

/-- `[A]_` preserves equalizers: if `f x = g x` then `liftAbs f (⟪a⟫x) = liftAbs g (⟪a⟫x)`.
    Consequence of Theorem 4.12 (right adjoints preserve limits). -/
theorem liftAbs_equalizer {Y : Type u} [Nominal α Y]
    {f g : X → Y} (hf : IsEquivariant α f) (hg : IsEquivariant α g)
    (a : α) {x : X} (hfg : f x = g x) :
    liftAbs hf (abs a x) = liftAbs hg (abs a x) := sorry

/-! ### Separated product and adjunction (Pitts, Theorem 4.12) -/

section Adjunction

variable {Y : Type u} [Nominal α Y]

/-- The **separated product**: pairs `(x, a)` where `x # a`. This is the left adjoint
to the name abstraction functor `[A]_`. -/
def SepProd (α : Type u) [Name α] (X : Type u) [Nominal α X] :=
  { p : X × α // p.1 # p.2 }

noncomputable instance SepProd.instPermType : PermType α (SepProd α X) := sorry

noncomputable instance SepProd.instNominal : Nominal α (SepProd α X) := sorry

/-- Convenience constructor for `SepProd`. -/
def SepProd.mk' (x : X) (a : α) (h : x # a) : SepProd α X :=
  ⟨(x, a), h⟩

/-- The permutation action on `SepProd`: `π • (x, a) = (π • x, π • a)`. -/
theorem SepProd.smul_mk' (π : FinitePerm α) (x : X) (a : α) (h : x # a) :
    π • SepProd.mk' x a h = SepProd.mk' (π • x) (π • a) sorry := sorry

/-- Support of a separated product element: `supp (x, a) = supp x ∪ {a}`. -/
theorem SepProd.supp_mk' (x : X) (a : α) (h : x # a) :
    supp (SepProd.mk' x a h) = supp x ∪ {a} := sorry

/-- Freshness for separated product. -/
theorem SepProd.fresh_mk' {b : α} (x : X) (a : α) (h : x # a) :
    b # (SepProd.mk' x a h) ↔ b # x ∧ b ≠ a := sorry

/-- The counit of the adjunction `_ * A ⊣ [A]_` (Theorem 4.12, eq. 4.20):
concretion as a function `SepProd α ([A]X) → X`, sending `(z, a)` with `a # z`
to `z @ a`. -/
noncomputable def adjCounit (p : SepProd α (NameAbs α X)) : X := sorry

/-- `adjCounit` is equivariant. -/
theorem adjCounit_equivariant (π : FinitePerm α) (p : SepProd α (NameAbs α X)) :
    adjCounit (π • p) = π • adjCounit p := sorry

/-- The currying map of the adjunction `_ * A ⊣ [A]_` (Theorem 4.12, eq. 4.22):
given an equivariant `f : SepProd α X → Y`, produce `X → [A]Y` by
`y ↦ fresh a in ⟪a⟫(f(y, a))`. -/
noncomputable def adjCurry (f : SepProd α X → Y)
    (hf : ∀ (π : FinitePerm α) (p : SepProd α X), f (π • p) = π • f p) :
    X → NameAbs α Y := sorry

/-- `adjCurry` is equivariant. -/
theorem adjCurry_equivariant (f : SepProd α X → Y)
    (hf : ∀ (π : FinitePerm α) (p : SepProd α X), f (π • p) = π • f p)
    (π : FinitePerm α) (x : X) :
    adjCurry f hf (π • x) = π • adjCurry f hf x := sorry

/-- `adjCurry f y = ⟪a⟫(f(y, a))` when `a # y` (Theorem 4.12, eq. 4.22). -/
theorem adjCurry_eq_abs (f : SepProd α X → Y)
    (hf : ∀ (π : FinitePerm α) (p : SepProd α X), f (π • p) = π • f p)
    (x : X) (a : α) (ha : x # a) :
    adjCurry f hf x = abs a (f (SepProd.mk' x a ha)) := sorry

/-- The unit of the left adjunction `_ * A ⊣ [A]_` (Theorem 4.12):
    `η_X : X → [A](SepProd α X)` sending `x ↦ fresh a in ⟪a⟫(x, a)`. -/
noncomputable def adjUnit (x : X) : NameAbs α (SepProd α X) := sorry

/-- `adjUnit` is equivariant. -/
theorem adjUnit_equivariant (π : FinitePerm α) (x : X) :
    adjUnit (π • x) = π • (adjUnit x : NameAbs α (SepProd α X)) := sorry

/-- First triangle identity: `adjCounit ∘ (adjCurry f × id) = f` (Theorem 4.12). -/
theorem adjCounit_adjCurry (f : SepProd α X → Y)
    (hf : ∀ (π : FinitePerm α) (p : SepProd α X), f (π • p) = π • f p)
    (p : SepProd α X) :
    adjCounit ⟨(adjCurry f hf p.val.1, p.val.2), sorry⟩ = f p := sorry

/-- First triangle identity (variant with explicit freshness). -/
theorem adjCounit_adjCurry' (f : SepProd α X → Y)
    (hf : ∀ (π : FinitePerm α) (p : SepProd α X), f (π • p) = π • f p)
    (p : SepProd α X)
    (h : (adjCurry f hf p.val.1) # p.val.2) :
    adjCounit ⟨(adjCurry f hf p.val.1, p.val.2), h⟩ = f p := sorry

/-- Second triangle identity: `[A](adjCurry f) ∘ adjUnit = f` (Theorem 4.12). -/
theorem adjCurry_adjCounit (f : SepProd α X → Y)
    (hf : ∀ (π : FinitePerm α) (p : SepProd α X), f (π • p) = π • f p)
    (x : X) (a : α) (ha : x # a) :
    adjCounit ⟨(adjCurry f hf x, a), sorry⟩ = f (SepProd.mk' x a ha) := sorry

/-! #### Exercise 4.2: `A * [A]X ≅ A × X` -/

/-- `SepProd α ([A]X) ≅ α × X` (Exercise 4.2): the separated product of atoms with
name abstractions is isomorphic to the ordinary product. The forward map sends
`(F, a)` with `a # F` to `(a, F @ a)`, and the backward map sends `(a, x)` to
`(⟪a⟫x, a)`. -/
noncomputable def sepProdAbsEquiv :
    SepProd α (NameAbs α X) ≃ α × X where
  toFun := sorry
  invFun := sorry
  left_inv := sorry
  right_inv := sorry

/-- Forward direction: `sepProdAbsEquiv (F, a) = (a, F @ a)` (Exercise 4.2). -/
@[simp]
theorem sepProdAbsEquiv_mk (F : NameAbs α X) (a : α) (h : F # a) :
    sepProdAbsEquiv (SepProd.mk' F a h) =
      (a, concreteAt_val F a (by rwa [fresh_comm] at h)) := sorry

/-- Backward direction: `sepProdAbsEquiv.symm (a, x) = (⟪a⟫x, a)` (Exercise 4.2). -/
@[simp]
theorem sepProdAbsEquiv_symm_mk (a : α) (x : X) :
    sepProdAbsEquiv.symm (a, x) = SepProd.mk' (abs a x) a sorry := sorry

/-- `sepProdAbsEquiv` is equivariant. -/
theorem sepProdAbsEquiv_equivariant (π : FinitePerm α)
    (p : SepProd α (NameAbs α X)) :
    sepProdAbsEquiv (π • p) = π • sepProdAbsEquiv p := sorry

/-! #### Exercise 4.6: Leibniz rule for separated products -/

/-- `[A](X₁ * X₂) ≅ ([A]X₁) * X₂ ⊕ X₁ * ([A]X₂)` (Exercise 4.6).
    The name abstraction functor distributes through separated products
    analogously to the Leibniz rule for derivatives. -/
noncomputable def sepProdDistribEquiv :
    NameAbs α (SepProd α (X × Y)) ≃
      (SepProd α (NameAbs α X × Y) ⊕ SepProd α (X × NameAbs α Y)) := sorry

end Adjunction

/-! ### Right adjoint (Pitts, Theorem 4.13) -/

section RightAdjoint

variable {Y : Type u} [Nominal α Y]

/-- `R X = { f ∈ A →ᶠˢ X | ∀ a, a # f a }` (eq. 4.23). This is the right adjoint
to the name abstraction functor `[A]_`. -/
def RightAdj (α : Type u) [Name α] (X : Type u) [Nominal α X] :=
  { f : NFun α α X // ∀ a, a # f a }

noncomputable instance RightAdj.instPermType : PermType α (RightAdj α X) := sorry

noncomputable instance RightAdj.instNominal : Nominal α (RightAdj α X) := sorry

/-- Convenience constructor for `RightAdj`. -/
def RightAdj.mk' (f : NFun α α X) (hf : ∀ a, a # f a) : RightAdj α X :=
  ⟨f, hf⟩

/-- The permutation action on `RightAdj`: `(π • f) a = π • f (π⁻¹ • a)`. -/
theorem RightAdj.smul_val (π : FinitePerm α) (f : RightAdj α X) (a : α) :
    (π • f).val a = π • f.val (π⁻¹ • a) := sorry

/-- Support computation for `RightAdj`. -/
theorem RightAdj.supp_eq (f : RightAdj α X) :
    supp f = supp f.val := sorry

/-- The counit of the right adjunction `[A]_ ⊣ R` (Theorem 4.13, eq. 4.24):
`ε_X : [A](R X) → X` defined by `z ↦ fresh a in (z @ a) a`. -/
noncomputable def rightAdjCounit (z : NameAbs α (RightAdj α X)) : X := sorry

/-- `rightAdjCounit` is equivariant. -/
theorem rightAdjCounit_equivariant (π : FinitePerm α)
    (z : NameAbs α (RightAdj α X)) :
    rightAdjCounit (π • z) = π • rightAdjCounit z := sorry

/-- `rightAdjCounit z = (z @ a) a` for `a # z` (eq. 4.24). -/
theorem rightAdjCounit_eq {z : NameAbs α (RightAdj α X)} {a : α} (ha : a # z) :
    rightAdjCounit z = (concreteAt_val z a ha).val a := sorry

/-- The unit of the right adjunction `[A]_ ⊣ R` (Theorem 4.13, eq. 4.26):
`η_Y : Y → R([A]Y)` defined by `y ↦ (a ↦ ⟪a⟫y)`. -/
noncomputable def rightAdjUnit (y : Y) : RightAdj α (NameAbs α Y) := sorry

/-- `rightAdjUnit` is equivariant. -/
theorem rightAdjUnit_equivariant (π : FinitePerm α) (y : Y) :
    rightAdjUnit (π • y) = π • (rightAdjUnit y : RightAdj α (NameAbs α Y)) := sorry

/-- `rightAdjUnit y` sends each atom `a` to `⟪a⟫y` (eq. 4.26). -/
theorem rightAdjUnit_val_apply (y : Y) (a : α) :
    (rightAdjUnit y : RightAdj α (NameAbs α Y)).val a = abs a y := sorry

/-- The characterization eq. 4.26: for any equivariant `f : [A]Y → X`,
    the adjoint transpose `f-hat` satisfies `f-hat(y)(a) = f(⟪a⟫y)`. -/
theorem rightAdj_characterization {f : NameAbs α Y → X}
    (hf : IsEquivariant α f) (y : Y) (a : α) :
    (rightAdjUnit y : RightAdj α (NameAbs α Y)).val a = abs a y := sorry

/-! #### Triangle identities for `[A]_ ⊣ R` (Theorem 4.13) -/

/-- `rightAdjUnit` is equivariant as a bare function (needed for `liftAbs`). -/
theorem isEquivariant_rightAdjUnit :
    IsEquivariant α (rightAdjUnit : Y → RightAdj α (NameAbs α Y)) := sorry

/-- First triangle identity for the right adjunction `[A]_ ⊣ R`:
    `ε ∘ [A]η = id`. For all `F : [A]X` and fresh `a`, `(η(F@a))a = F@a`
    (Theorem 4.13). -/
theorem rightAdj_counit_unit (F : NameAbs α X) (a : α) (ha : a # F) :
    (rightAdjUnit (concreteAt_val F a ha) : RightAdj α (NameAbs α X)).val a =
      abs a (concreteAt_val F a ha) := sorry

/-- Second triangle identity for the right adjunction `[A]_ ⊣ R`:
    `R(ε) ∘ η = id`. For all `f : R X` and atom `a`, `ε(⟪a⟫f) = f a`
    (Theorem 4.13). -/
theorem rightAdj_unit_counit (f : RightAdj α X) (a : α) (ha : a # f) :
    rightAdjCounit (abs a f) = f.val a := sorry

end RightAdjoint

/-! ### Negative results (Exercise 4.7) -/

section Negative

variable {Y : Type u} [Nominal α Y]

/-- The left adjunction `_ * A ⊣ [A]_` is NOT a Nom-enriched adjunction:
    `(X * A) →ᶠˢ Y ≇ X →ᶠˢ ([A]Y)` in general.
    Pitts, Exercise 4.7. -/
theorem not_enriched_left_adjunction :
    ¬ ∀ (X Y : Type u) [Nominal α X] [Nominal α Y],
      Nonempty (NFun α (SepProd α X) Y ≃ NFun α X (NameAbs α Y)) := sorry

/-- The right adjunction `[A]_ ⊣ R` is NOT a Nom-enriched adjunction:
    `([A]X) →ᶠˢ Y ≇ X →ᶠˢ R Y` in general.
    Pitts, Exercise 4.7. -/
theorem not_enriched_right_adjunction :
    ¬ ∀ (X Y : Type u) [Nominal α X] [Nominal α Y],
      Nonempty (NFun α (NameAbs α X) Y ≃ NFun α X (RightAdj α Y)) := sorry

end Negative

/-! ### Generalized abstraction (Pitts, Section 4.6) -/

section Generalized

variable {Y : Type u} [Nominal α Y]

/-- Generalized alpha-equivalence: `π` witnesses `(x, y) ~_alpha (x', y')` when
    `π • (x, y) = (x', y')` and `π` fixes `supp y \ supp x` pointwise.
    Pitts, Section 4.6, Definition 4.20. -/
def GenAlphaEqv (π : FinitePerm α) (x : X) (y : Y) (x' : X) (y' : Y) : Prop :=
  π • x = x' ∧ π • y = y' ∧ ∀ a ∈ supp y \ supp x, π a = a

/-- Generalized alpha-equivalence as an existential. -/
def GenAlpha (x : X) (y : Y) (x' : X) (y' : Y) : Prop :=
  ∃ π, GenAlphaEqv π x y x' y'

/-- `GenAlpha` is an equivalence relation on `X × Y`.
    Pitts, Lemma 4.19. -/
theorem genAlpha_refl (x : X) (y : Y) : GenAlpha x y x y := sorry

theorem genAlpha_symm {x x' : X} {y y' : Y} (h : GenAlpha x y x' y') :
    GenAlpha x' y' x y := sorry

theorem genAlpha_trans {x₁ x₂ x₃ : X} {y₁ y₂ y₃ : Y}
    (h₁₂ : GenAlpha x₁ y₁ x₂ y₂) (h₂₃ : GenAlpha x₂ y₂ x₃ y₃) :
    GenAlpha x₁ y₁ x₃ y₃ := sorry

/-- `GenAlpha` is an equivariant equivalence relation.
    Pitts, Lemma 4.19. -/
theorem genAlpha_equivariant (π : FinitePerm α) {x x' : X} {y y' : Y}
    (h : GenAlpha x y x' y') :
    GenAlpha (π • x) (π • y) (π • x') (π • y') := sorry

/-- The setoid on `X × Y` induced by generalized alpha-equivalence. -/
def genAlphaSetoid (α : Type u) [Name α] (X : Type u) [Nominal α X]
    (Y : Type u) [Nominal α Y] : Setoid (X × Y) where
  r p q := GenAlpha p.1 p.2 q.1 q.2
  iseqv := ⟨fun p => genAlpha_refl p.1 p.2,
            fun h => genAlpha_symm h,
            fun h₁ h₂ => genAlpha_trans h₁ h₂⟩

/-- The quotient `[X]Y` of `X × Y` by generalized alpha-equivalence.
    Pitts, Definition 4.20. -/
def GenNameAbs (α : Type u) [Name α] (X : Type u) [Nominal α X]
    (Y : Type u) [Nominal α Y] : Type u :=
  Quotient (genAlphaSetoid α X Y)

/-- The canonical map `X × Y → [X]Y`. -/
def genAbs (x : X) (y : Y) : GenNameAbs α X Y :=
  Quotient.mk (genAlphaSetoid α X Y) (x, y)

/-- `supp ⟨x⟩y = supp y \ supp x` for generalized abstractions.
    Pitts, Proposition 4.23. -/
theorem supp_genAbs [Nominal α (GenNameAbs α X Y)] (x : X) (y : Y) :
    supp (genAbs x y : GenNameAbs α X Y) = supp y \ supp x := sorry

/-- Fresh representative lemma for generalized abstractions: for any finite
    set `A`, we can find a representative `⟨x⟩y` with `A ∩ supp x = ∅`.
    Pitts, Lemma 4.24. -/
theorem genAbs_exists_fresh_rep [Nominal α (GenNameAbs α X Y)]
    (z : GenNameAbs α X Y) (A : Finset α) :
    ∃ x y, Disjoint A (supp x) ∧ z = genAbs x y := sorry

/-- `(x, y) ~_alpha (x', y')` iff there exists `π` with `supp π ⊆ supp(x, x')`
    witnessing the generalized alpha-equivalence.
    Pitts, Exercise 4.8. -/
theorem genAlphaEqv_iff_bounded_support {x x' : X} {y y' : Y} :
    GenAlpha x y x' y' ↔
    (∃ π, supp π ⊆ supp x ∪ supp x' ∧ GenAlphaEqv π x y x' y') := sorry

/-- When `X = α` (atoms), generalized alpha-equivalence reduces to ordinary
    alpha-equivalence, so `[A]Y ≅ GenNameAbs α Y`.
    Pitts, Remark 4.21 and Exercise 4.8. -/
noncomputable def genAbsAtomEquiv :
    GenNameAbs α α Y ≃ NameAbs α Y := sorry

/-- Generalized functorial action: `[X]f(⟨x⟩y) = ⟨x⟩(f y)` when `x # f`.
    Pitts, Section 4.6, eq. 4.42. -/
noncomputable def genLiftAbs {Z : Type u} [Nominal α Z]
    (f : NFun α Y Z) : GenNameAbs α X Y → GenNameAbs α X Z := sorry

/-- The functor `[X]_ : Nom → Nom` has a right adjoint, generalizing
    Theorem 4.13. Pitts, Exercise 4.9. -/
def GenRightAdj (α : Type u) [Name α] (X : Type u) [Nominal α X]
    (Y : Type u) [Nominal α Y] : Type u := sorry

/-- `[P_f A]_` does NOT preserve products: the canonical map
    `[P_f A](X₁ × X₂) → [P_f A]X₁ × [P_f A]X₂` is not an isomorphism in general.
    Pitts, Example 4.25. -/
theorem genAbs_finset_not_preserve_prod :
    ¬ ∀ (X Y : Type u) [Nominal α X] [Nominal α Y],
      Nonempty (GenNameAbs α (Finset α) (X × Y) ≃
        GenNameAbs α (Finset α) X × GenNameAbs α (Finset α) Y) := sorry

end Generalized

end NameAbs

end NominalSets
