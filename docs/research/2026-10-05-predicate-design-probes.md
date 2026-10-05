# Predicate design probes for PKG-F01

Date: 2026-10-05. Standalone scratch evidence at
`76966b1f2e44f594517442b6572e33abaa9038e0`, pinned Lean/Mathlib 4.34.1.
No Package implementation or new production import is supplied by these probes.
Read the [readiness/design proposal](2026-10-05-pkg01-readiness.md) for the
recommended public boundary and the prerequisites these experiments leave open.

Each exact source below was compiled in `/tmp` with `lake env lean`, exit 0,
without diagnostics other than the requested `#check` / `#print axioms` output.
The sources are retained in Markdown to keep this design session's experiments
separate from production implementation and preserve every existing probe file.
Extract an individual Lean block to its named `/tmp` path to reproduce it.

These checks used built dependencies/imports. They are not a fresh project
build, dependency bootstrap, new Package audit, or a proof of every proposed
predicate operation. Standard axioms are `propext`, `Classical.choice` and
`Quot.sound`; all printed lists are confined to those axioms.

## Independent group-action experiment

`PackagePredicateGroup.SPred` checks as `Type w`, independently of the group
and atom universes. Its action and support equivalence do not require nominality
of the domain, atom infinitude or a global decidable equality assumption.
Classical finite-image selection remains in the support proof field. The
surjective-equivariant pullback theorem has independent domain/codomain
universes. The generic G is an isolation technique, not a proposed extra public
package parameter.

This file imports only Mathlib. It does not establish least-support existence,
swap characterization, fresh atom existence or Some/Any for an arbitrary group.
Those remain finite-permutation foundation obligations. It also does not supply
a complete persistent nominal-predicate API or quotient action implementation.


Command actually run:

```sh
lake env lean /tmp/PackagePredicateGroup.lean > /tmp/PackagePredicateGroup.log 2>&1
```

Source SHA-256: `cc27e8f8fba0f7ae1530009e3b31efbdbf6c7d347b26613ff2eefe62922de969`.

```lean
import Mathlib.GroupTheory.GroupAction.Support
import Mathlib.Data.Finset.Image
import Mathlib.Data.FunLike.Basic

/- Independent generic action probe: no Nominal import and no Prop action. -/
namespace PackagePredicateGroup
universe u v w z

def LogicalSupports (G : Type u) [Group G] {A : Type v} [MulAction G A]
    {X : Type w} [MulAction G X] (S : Finset A) (P : X → Prop) : Prop :=
  ∀ π : G, (∀ a ∈ S, π • a = a) → ∀ x, P (π • x) ↔ P x

structure SPred (G : Type u) [Group G] (A : Type v) [MulAction G A]
    (X : Type w) [MulAction G X] where
  toFun : X → Prop
  supported : ∃ S : Finset A, LogicalSupports G S toFun

namespace SPred
variable {G : Type u} [Group G] {A : Type v} [MulAction G A]
variable {X : Type w} [MulAction G X]
instance : FunLike (SPred G A X) X Prop where
  coe := toFun
  coe_injective p q h := by cases p; cases q; cases h; rfl
@[ext] theorem ext {p q : SPred G A X} (h : ∀ x, p x ↔ q x) : p = q :=
  DFunLike.ext _ _ (fun x => propext (h x))

def perm (π : G) (p : SPred G A X) : SPred G A X where
  toFun x := p (π⁻¹ • x)
  supported := by
    classical
    obtain ⟨S,hS⟩ := p.supported
    refine ⟨S.image (π • ·), fun σ hσ x => ?_⟩
    have hfix : ∀ a ∈ S, (π⁻¹ * σ * π) • a = a := by
      intro a ha
      have h := hσ (π • a) (Finset.mem_image.mpr ⟨a,ha,rfl⟩)
      simp only [mul_smul,h,inv_smul_smul]
    have h := hS (π⁻¹ * σ * π) hfix (π⁻¹ • x)
    change p.toFun (π⁻¹ • σ • x) ↔ p.toFun (π⁻¹ • x)
    simpa only [mul_smul, smul_inv_smul] using h
instance : MulAction G (SPred G A X) where
  smul := perm
  one_smul p := by ext x; change p ((1 : G)⁻¹ • x) ↔ p x; simp
  mul_smul π σ p := by
    ext x
    change p ((π * σ)⁻¹ • x) ↔ p (σ⁻¹ • (π⁻¹ • x))
    rw [mul_inv_rev,mul_smul]
@[simp] theorem smul_apply (π : G) (p : SPred G A X) (x : X) :
    (π • p) x ↔ p (π⁻¹ • x) := Iff.rfl

theorem supports_iff (S : Finset A) (p : SPred G A X) :
    MulAction.Supports G (S : Set A) p ↔ LogicalSupports G S p := by
  constructor
  · intro h π hπ x
    have hx := congrArg (fun q : SPred G A X => q (π • x)) (h π (fun a ha => hπ a ha))
    simpa only [smul_apply, inv_smul_smul] using (Iff.of_eq hx).symm
  · intro h π hπ
    ext x
    have hinv : ∀ a ∈ S, π⁻¹ • a = a := by
      intro a ha
      have := congrArg (π⁻¹ • ·) (hπ ha)
      simpa using this.symm
    exact h π⁻¹ hinv x

theorem pullback_support_iff {Y : Type z} [MulAction G Y]
    (q : X → Y) (hq : ∀ (π : G) x, q (π • x) = π • q x) (hsurj : Function.Surjective q)
    (P : Y → Prop) (S : Finset A) :
    LogicalSupports G S (fun x => P (q x)) ↔ LogicalSupports G S P := by
  constructor
  · intro h π hπ y
    obtain ⟨x,rfl⟩ := hsurj y
    simpa only [hq] using h π hπ x
  · intro h π hπ x
    simpa only [hq] using h π hπ (q x)

example (p q : SPred G A X) (h : ∀ x, p x ↔ q x) : p = q := by ext x; exact h x
example (p : SPred G A X) (xs : List X) : xs.map p = xs.map (fun x => p x) := rfl
end SPred
#check SPred
#check SPred.pullback_support_iff
#print axioms SPred.perm
#print axioms SPred.supports_iff
#print axioms SPred.pullback_support_iff
end PackagePredicateGroup
```


## Fresh-quantifier interchange counterexamples

This reference-based experiment proves failures even for jointly equivariant
equality and disequality relations. It uses the reference cofinite quantifier;
its result must be rederived for any replacement definition. It refutes the
specified equivalences, not the valid one-way laws or certified-bound Some/Any.

Command actually run:

```sh
lake env lean /tmp/PackagePredicateQuantifierFailures.lean > /tmp/PackagePredicateQuantifierFailures.log 2>&1
```

Source SHA-256: `8d893fd439ea1b81b9b79af5d5bb731284d380a3d26c42f2be5042bb4336a696`.

```lean
import Nominal.Set.FreshQuantifier
open Nominal.Core Nominal.Set
namespace PackagePredicateQuantifierFailures
universe u
variable {A : Type u} [Name A]
omit [Name A] in
theorem fresh_ne (x : A) : И a, a ≠ x := by
  apply freshQuantifier_iff_exists_finset.mpr
  exact ⟨{x}, fun a ha => by simpa using ha⟩
theorem not_fresh_eq (x : A) : ¬ (И a, a = x) := by
  intro h
  obtain ⟨a,ha,hne⟩ := freshQuantifier_exists (freshQuantifier_and.mpr ⟨h,fresh_ne x⟩)
  exact hne ha

theorem failed_exists_interchange :
    (И a : A, ∃ x : A, a = x) ∧ ¬ (∃ x : A, И a, a = x) := by
  constructor
  · exact freshQuantifier_of_forall (fun a => ⟨a,rfl⟩)
  · rintro ⟨x,hx⟩; exact not_fresh_eq x hx

theorem failed_forall_interchange :
    (∀ x : A, И a, a ≠ x) ∧ ¬ (И a : A, ∀ x : A, a ≠ x) := by
  constructor
  · exact fresh_ne
  · intro h
    obtain ⟨a,ha⟩ := freshQuantifier_exists h
    exact ha a rfl

-- Both relations satisfy joint equivariance: this hypothesis cannot repair interchange.
theorem eq_jointly_equivariant : EquivariantRel A (fun a x : A => a = x) :=
  equivariantRel_eq
theorem ne_jointly_equivariant : EquivariantRel A (fun a x : A => a ≠ x) :=
  ⟨fun π _ _ => not_congr (PermType.smul_eq_smul_iff_eq π)⟩
#print axioms failed_exists_interchange
#print axioms failed_forall_interchange
end PackagePredicateQuantifierFailures
```


## Supplementary direct-predicate comparison

This experiment specializes to the old atom/permutation group and imports
`Nominal.Set.Support`. It tests a direct proof-field predicate representation,
a supported-subset equivalence, joint universal quantification and two atom
carriers without an NFun representation or a nominal-domain assumption.
It is comparison evidence only: importing the old group here is not a proposed
Package dependency, and its closure still contains the old action classes.

Command actually run:

```sh
lake env lean /tmp/PackagePredicateDirect.lean > /tmp/PackagePredicateDirect.log 2>&1
```

Source SHA-256: `ffa29548972348fe25cb227c711678c5134276040c8b177fbe41a0366a0f8104`.

```lean
import Nominal.Set.Support

/- Design probe only. Uses the existing atom/permutation library, but no NFun,
   no Nominal-domain premise, no action on Prop/functions/Set, no outParam class. -/
open Nominal.Core Nominal.Set
namespace PackagePredicateDirect
universe u v w z
variable {α : Type u} [Name α]

def LogicalSupports {X : Type v} [MulAction (FinitePerm α) X]
    (S : Finset α) (P : X → Prop) : Prop :=
  ∀ π : FinitePerm α, (∀ ⦃a⦄, a ∈ S → π a = a) → ∀ x, P (π • x) ↔ P x

structure SPred (α : Type u) [Name α] (X : Type v) [MulAction (FinitePerm α) X] where
  toFun : X → Prop
  supported : ∃ S : Finset α, LogicalSupports S toFun

namespace SPred
variable {X : Type v} [MulAction (FinitePerm α) X]
instance : FunLike (SPred α X) X Prop where
  coe := toFun
  coe_injective p q h := by cases p; cases q; cases h; rfl
@[ext] theorem ext {p q : SPred α X} (h : ∀ x, p x ↔ q x) : p = q :=
  DFunLike.ext _ _ (fun x => propext (h x))

def perm (π : FinitePerm α) (p : SPred α X) : SPred α X where
  toFun x := p (π⁻¹ • x)
  supported := by
    obtain ⟨S,hS⟩ := p.supported
    refine ⟨π • S, fun σ hσ x => ?_⟩
    have hfix : ∀ a ∈ (S : Set α), (π⁻¹ * σ * π) • a = a :=
      PermType.conj_fixes_of_smul_fixes (fun a ha => hσ ha)
    have h := hS (π⁻¹ * σ * π) (fun a ha => hfix a ha) (π⁻¹ • x)
    change p.toFun (π⁻¹ • σ • x) ↔ p.toFun (π⁻¹ • x)
    simpa only [mul_smul, smul_inv_smul] using h

instance : MulAction (FinitePerm α) (SPred α X) where
  smul := perm
  one_smul p := by ext x; change p ((1 : FinitePerm α)⁻¹ • x) ↔ p x; simp
  mul_smul π σ p := by
    ext x
    change p ((π * σ)⁻¹ • x) ↔ p (σ⁻¹ • (π⁻¹ • x))
    rw [mul_inv_rev,mul_smul]
@[simp] theorem smul_apply (π : FinitePerm α) (p : SPred α X) (x : X) :
    (π • p) x ↔ p (π⁻¹ • x) := Iff.rfl

theorem supports_iff (S : Finset α) (p : SPred α X) :
    supports S p ↔ LogicalSupports S p := by
  constructor
  · intro h π hπ x
    have hx := congrArg (fun q : SPred α X => q (π • x)) (h π hπ)
    simpa only [smul_apply, inv_smul_smul] using (Iff.of_eq hx).symm
  · intro h π hπ
    ext x
    have hinv : ∀ ⦃a⦄, a ∈ S → π⁻¹ a = a := by
      intro a ha
      have := congrArg (fun b => π⁻¹ b) (hπ ha)
      simpa using this.symm
    exact h π⁻¹ hinv x

-- Inverse precomposition needs only equivariance and surjectivity, not quotient
-- implementation or finite support of individual domain elements.
omit [Name α] in
theorem pullback_support_iff {Y : Type w} [MulAction (FinitePerm α) Y]
    (q : X → Y) (hq : ∀ (π : FinitePerm α) x, q (π • x) = π • q x) (hsurj : Function.Surjective q)
    (P : Y → Prop) (S : Finset α) :
    LogicalSupports S (fun x => P (q x)) ↔ LogicalSupports S P := by
  constructor
  · intro h π hπ y
    obtain ⟨x,rfl⟩ := hsurj y
    simpa only [hq] using h π hπ x
  · intro h π hπ x
    simpa only [hq] using h π hπ (q x)

def toSubset (p : SPred α X) : Set X := fun x => p x
@[simp] theorem mem_toSubset (p : SPred α X) (x : X) : x ∈ p.toSubset ↔ p x := Iff.rfl

def supportedSubsetEquiv : SPred α X ≃ {P : Set X // ∃ S : Finset α, LogicalSupports S P} where
  toFun p := ⟨p.toSubset,p.supported⟩
  invFun p := ⟨p.val,p.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

-- Quantification over the whole acted-on carrier requires joint support only.
omit [Name α] in
theorem logicalSupport_forall {Y : Type w} [MulAction (FinitePerm α) Y]
    {S : Finset α} {R : X × Y → Prop} (h : LogicalSupports S R) :
    LogicalSupports S (fun x => ∀ y, R (x,y)) := by
  intro π hπ x
  constructor
  · intro hp y
    exact (h π hπ (x,y)).mp (hp (π • y))
  · intro hp y
    have hy := (h π hπ (x,π⁻¹ • y)).mpr (hp (π⁻¹ • y))
    simpa using hy

example (p q : SPred α X) (h : ∀ x, p x ↔ q x) : p = q := by ext x; exact h x
example (p : SPred α X) (xs : List X) : xs.map p = xs.map (fun x => p x) := rfl
example {β : Type z} [Name β] (p : SPred α α) (q : SPred β β) (a : α) (b : β) :
    (p a ∧ q b) ↔ (p a ∧ q b) := Iff.rfl
end SPred
#check SPred
#check SPred.logicalSupport_forall
#print axioms SPred.supports_iff
#print axioms SPred.pullback_support_iff
#print axioms SPred.supportedSubsetEquiv
end PackagePredicateDirect
```
