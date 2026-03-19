import NominalSets.Structural

/-!
# Nominal Algebraic Data Types

This file develops the theory of nominal algebraic signatures and their initial algebra
semantics, following Pitts' *Nominal Sets*, Chapter 8 (Sections 8.1–8.5).

**Status:** Stub. The infrastructure below is planned but not yet implemented.

## Planned development

### 1. Nominal algebraic signatures (Definition 8.3, 8.5)

A *nominal algebraic signature* `Σ` consists of:
- A finite set of *sort symbols* `S₁, …, Sₙ`, partitioned into *data sorts* and
  *name sorts* (each name sort is associated with a `Name` type).
- A finite set of *operation symbols*, each with an arity built from:
  - sort symbols `Sᵢ`
  - products `σ₁ × σ₂`
  - the unit type `1`
  - name abstraction `A . σ` (binding a name sort `A` in `σ`)

This requires an inductive type `NomSort` for sort expressions and a representation
of operation symbols with their arities.

### 2. Interpretation functor (Section 8.3, eq. 8.14)

Each sort expression `σ` is interpreted as a functor `⟦σ⟧ : Nom^n → Nom` by:
- `⟦Sᵢ⟧(X₁, …, Xₙ) = Xᵢ`           (projection)
- `⟦1⟧(X) = Unit`                      (terminal)
- `⟦σ₁ × σ₂⟧(X) = ⟦σ₁⟧(X) × ⟦σ₂⟧(X)` (product)
- `⟦A . σ⟧(X) = [A](⟦σ⟧(X))`          (name abstraction, the key clause)

The full signature functor `T : Nom^n → Nom^n` is assembled from the operation
symbols as a coproduct of products.

### 3. Initial algebra (Theorem 8.15)

The signature functor `T` has an initial algebra `μT`, giving the "free" nominal
algebraic data type. The proof uses:
- `[A]_` preserves colimits (left adjoint, Theorem 4.12) — needed for `sumEquiv`
- `[A]_` preserves limits (right adjoint, Theorem 4.13) — needed for `prodEquiv`
- Products and coproducts in `Nom` are computed pointwise
- The initial chain `0 → T(0) → T²(0) → …` stabilises at `ω`

### 4. Alpha-structural recursion (Theorem 8.17)

Given a nominal algebra `(Y, θ)` for signature `Σ`, there is a unique equivariant
homomorphism `fold : μT → Y`. The key step uses `liftFCB` / `liftFresh`
(Corollary 4.17) to handle the binding clause: if `θ` processes `[A]_`-arguments
via an FCB function, the recursion is well-defined.

### 5. Alpha-structural induction (Theorem 8.21)

An induction principle for `μT`: to prove a property `P` of all elements,
it suffices to check each operation symbol, where for binding arguments
`⟪a⟫x` one may assume `a` is fresh for any given finite set of parameters.

## Dependencies from `Structural.lean`

This file will rely on:
- `prodEquiv` / `sumEquiv` — to interpret products and coproducts under `[A]_`
- `expEquiv` — for exponential sorts (if added)
- `SepProd` / `adjCounit` / `adjCurry` — for the left adjunction
- `liftAbs_NFun` — for the enriched functorial action (planned)
- `FCB` / `liftFCB` / `liftFresh` from `FCB.lean` — for the recursion principle

## References

* [A. M. Pitts, *Nominal Sets*][Pitts2013], Chapter 8.
-/

/-!
## Dependency analysis and design decisions

### Upstream module status

| Module | Status | Key items used by this file |
|--------|--------|-----------------------------|
| `FCB.lean` | ✓ fully proven | `FCB`, `liftFCB`, `liftFresh`, `liftFreshParam` |
| `NameAbstraction.lean` | ✓ fully proven | `NameAbs`, `abs`, `ind`, `exists_fresh_rep`, `supp_abs` |
| `Concretion.lean` | ✓ fully proven | `liftAbs`, `liftAbs_abs`, `liftAbs_comp`, `liftAbs_id` |
| `Nominal.lean` | ✓ fully proven | `Nominal` instances for `α`, `X × Y`, `X ⊕ Y`, `Unit`, `Option` |
| `NFun.lean` | ✓ fully proven | `NFun`, `NFun.comp`, `NFun.id` |
| `FreshQuantifier.lean` | ✓ fully proven | `И`, `someAny`, `freshF` |
| `Structural.lean` | ✗ all sorry | `prodEquiv`, `sumEquiv`, `liftAbs_NFun`, `SepProd` |

### Design decisions

- **Single-sorted**: one atom type `α` (one name sort) and one data sort.
  Multi-sorted signatures (multiple data sorts, `Fin n → Type`) are a natural
  generalisation but substantially complicate the Lean types. Deferred.
- **Signature as a list**: `NomSig := List NomSortExpr`. Each entry is one
  operation symbol's arity; the target sort is always the unique data sort.
- **Interpretation via recursion on `NomSortExpr`**: the functor is built by
  structural recursion, producing nested `Prod`/`NameAbs`/`Unit` types.
- **Signature functor as nested `Sum`**: the coproduct of arities is realised
  as right-associated `Sum` types, with `Empty` as the base case.

### Plan

1. `NomSortExpr` — inductive type for sort expressions.
2. `interpSort` — interprets sort expressions as types; `interpSort.instNominal`.
3. `NomSig`, `sigFunctor` — signature and its coproduct interpretation.
4. `sigMap` — functorial action on morphisms (needed for initial chain).
5. `NomAlgebra` — structure packaging operation interpretations.
6. `InitialAlg` — the initial algebra (opaque, axiomatised via sorry).
7. `fold` / `fold_computation` / `fold_unique` — alpha-structural recursion.
8. `initialAlg_induction` — alpha-structural induction.
9. Lambda calculus example — `LambdaSig`, `Lambda`, constructors, recursion,
   induction, capture-avoiding substitution.
-/

namespace NominalSets

open MulAction PermType

universe u

variable {α : Type u} [Name α]

/-! ### Section 1: Sort expressions (Definition 8.3, 8.5) -/

/-- Sort expressions for a single-sorted nominal algebraic signature.

A sort expression describes the *arity shape* of an operation symbol.
- `data` refers to the single data sort (the recursive argument).
- `unit` is the terminal object `1`.
- `prod σ τ` is the cartesian product `σ × τ`.
- `nameAbs σ` is the name abstraction `[A]σ` (introduces a binding). -/
inductive NomSortExpr : Type where
  /-- The data sort (recursive position). -/
  | data : NomSortExpr
  /-- The unit sort (no data). -/
  | unit : NomSortExpr
  /-- Product of two sort expressions. -/
  | prod : NomSortExpr → NomSortExpr → NomSortExpr
  /-- Name abstraction: `[A]σ` binds an atom in `σ`. -/
  | nameAbs : NomSortExpr → NomSortExpr
  deriving Repr, DecidableEq, Inhabited

/-! ### Section 2: Interpretation of sort expressions (eq. 8.14) -/

/-- Interpret a sort expression as a type, given an atom type `α` and a carrier `X`
for the data sort.

- `data` is interpreted as `X` itself (the recursive position).
- `unit` is interpreted as `Unit`.
- `prod σ τ` is interpreted as the cartesian product.
- `nameAbs σ` is interpreted as `NameAbs α (⟦σ⟧)` — name abstraction. -/
noncomputable def interpSort (α : Type u) [Name α] (X : Type u) [Nominal α X] :
    NomSortExpr → Type u
  | .data      => X
  | .unit      => Unit
  | .prod σ τ  => interpSort α X σ × interpSort α X τ
  | .nameAbs σ => NameAbs α (interpSort α X σ)

/-- Every interpreted sort expression carries a canonical `Nominal` instance,
built by induction on the sort expression using the instances for
`Unit`, `Prod`, and `NameAbs` from upstream modules. -/
noncomputable instance interpSort.instNominal (α : Type u) [Name α] (X : Type u) [Nominal α X]
    (σ : NomSortExpr) : Nominal α (interpSort α X σ) := by
  induction σ with
  | data     => exact inferInstance
  | unit     => exact PermType.instUnit ▸ sorry
  | prod σ τ ihσ ihτ => exact @instNominalProd α _ _ ihσ _ ihτ
  | nameAbs σ ih => exact @NameAbs.instNominal α _ _ ih

/-- Every interpreted sort expression carries a canonical `PermType` instance. -/
noncomputable instance interpSort.instPermType (α : Type u) [Name α] (X : Type u) [Nominal α X]
    (σ : NomSortExpr) : PermType α (interpSort α X σ) :=
  (interpSort.instNominal α X σ).toPermType

/-! ### Section 3: Nominal signatures and signature functor -/

/-- A nominal algebraic signature (single-sorted, single name sort).

A signature is a list of sort expressions, one per operation symbol.
Each sort expression describes the arity of that operation; the target
sort is always the unique data sort.

For example, the lambda calculus signature is:
```
  [.data, .prod .data .data, .nameAbs .data]
```
corresponding to `var : A → Λ`, `app : Λ × Λ → Λ`, `lam : [A]Λ → Λ`. -/
abbrev NomSig := List NomSortExpr

/-- The signature functor: interprets a signature as a coproduct (nested `Sum`)
of the interpretations of each operation's arity.

Given a signature `[σ₁, σ₂, …, σₙ]` and a carrier `X`, this produces:
```
  ⟦σ₁⟧(X) ⊕ (⟦σ₂⟧(X) ⊕ (… ⊕ (⟦σₙ⟧(X) ⊕ Empty)))
```

The `Empty` base case ensures every signature (including the empty one) produces
a well-formed type. -/
noncomputable def sigFunctor (α : Type u) [Name α] (sig : NomSig) (X : Type u)
    [Nominal α X] : Type u :=
  match sig with
  | []        => Empty
  | σ :: rest => interpSort α X σ ⊕ sigFunctor α rest X

/-- The signature functor output is a nominal set. -/
noncomputable instance sigFunctor.instNominal (α : Type u) [Name α] (sig : NomSig)
    (X : Type u) [Nominal α X] : Nominal α (sigFunctor α sig X) := by
  induction sig with
  | nil => exact sorry -- Empty is trivially nominal (no elements)
  | cons σ rest ih =>
    exact @instNominalSum α _ _ (interpSort.instNominal α X σ) _ ih

/-- Functorial action of the signature functor on morphisms.

Given an equivariant map `f : X → Y`, this lifts it through each sort expression
to produce a map `sigFunctor α sig X → sigFunctor α sig Y`. The key case is
`nameAbs`, which uses `liftAbs` from `Concretion.lean`. -/
noncomputable def sigMap {X Y : Type u} [Nominal α X] [Nominal α Y]
    (sig : NomSig) (f : X → Y) (hf : IsEquivariant α f) :
    sigFunctor α sig X → sigFunctor α sig Y := sorry

/-- `sigMap` is equivariant. -/
theorem sigMap_equivariant {X Y : Type u} [Nominal α X] [Nominal α Y]
    (sig : NomSig) (f : X → Y) (hf : IsEquivariant α f) :
    IsEquivariant α (sigMap sig f hf) := sorry

/-- `sigMap` preserves identity. -/
theorem sigMap_id (sig : NomSig) (X : Type u) [Nominal α X] :
    sigMap (α := α) sig id isEquivariant_id = id := sorry

/-- `sigMap` preserves composition. -/
theorem sigMap_comp {X Y Z : Type u} [Nominal α X] [Nominal α Y] [Nominal α Z]
    (sig : NomSig) (f : X → Y) (hf : IsEquivariant α f)
    (g : Y → Z) (hg : IsEquivariant α g) :
    sigMap sig (g ∘ f) (hg.comp hf) = sigMap sig g hg ∘ sigMap sig f hf := sorry

/-! ### Section 4: Algebras for a nominal signature -/

/-- A nominal algebra for signature `sig` with carrier `Y`.

Packages an equivariant map from the signature functor applied to `Y`
back into `Y`. This is equivalent to providing one equivariant map
per operation symbol. -/
structure NomAlgebra (α : Type u) [Name α] (sig : NomSig) (Y : Type u) [Nominal α Y] where
  /-- The algebra structure map `T(Y) → Y`. -/
  str : sigFunctor α sig Y → Y
  /-- The structure map is equivariant. -/
  str_equivariant : IsEquivariant α str

/-- A homomorphism between two `sig`-algebras is an equivariant map
that commutes with the algebra structure maps. -/
structure NomAlgebra.Hom (α : Type u) [Name α] (sig : NomSig)
    {Y₁ Y₂ : Type u} [Nominal α Y₁] [Nominal α Y₂]
    (alg₁ : NomAlgebra α sig Y₁) (alg₂ : NomAlgebra α sig Y₂) where
  /-- The underlying equivariant map. -/
  map : Y₁ → Y₂
  /-- The map is equivariant. -/
  map_equivariant : IsEquivariant α map
  /-- The map commutes with algebra structure: `h ∘ θ₁ = θ₂ ∘ T(h)`. -/
  comm : ∀ x, map (alg₁.str x) = alg₂.str (sigMap sig map map_equivariant x)

/-! ### Section 5: Initial algebra (Theorem 8.15) -/

/-- The initial algebra for a nominal algebraic signature.

`InitialAlg α sig` is the carrier of the initial `sig`-algebra in the
category of nominal sets. Concretely, it is the set of finite syntax trees
for `sig`, quotiented by alpha-equivalence. For the lambda calculus signature,
this gives lambda-terms modulo alpha.

**Construction** (deferred): The initial chain
```
  ∅ → T(∅) → T²(∅) → ⋯
```
stabilises at `ω` because `T` preserves `ω`-colimits (each component is
a polynomial functor composed with `[A]_`, which preserves colimits as
a left adjoint via `sumEquiv`/`prodEquiv` from `Structural.lean`). -/
noncomputable def InitialAlg (α : Type u) [Name α] (sig : NomSig) : Type u := sorry

/-- The initial algebra is a nominal set. -/
noncomputable instance InitialAlg.instNominal (α : Type u) [Name α] (sig : NomSig) :
    Nominal α (InitialAlg α sig) := sorry

/-- The algebra structure on the initial algebra: `T(μT) ≅ μT`.

This is an isomorphism by Lambek's lemma (the structure map of an initial
algebra is always an isomorphism). -/
noncomputable def InitialAlg.algebra (α : Type u) [Name α] (sig : NomSig) :
    NomAlgebra α sig (InitialAlg α sig) := sorry

/-- The algebra structure map is an isomorphism (Lambek's lemma). -/
noncomputable def InitialAlg.algebraIso (α : Type u) [Name α] (sig : NomSig) :
    sigFunctor α sig (InitialAlg α sig) ≃ InitialAlg α sig := sorry

/-- The algebra isomorphism is equivariant. -/
theorem InitialAlg.algebraIso_equivariant (α : Type u) [Name α] (sig : NomSig) :
    IsEquivariant α (InitialAlg.algebraIso α sig) := sorry

/-! ### Section 6: Alpha-structural recursion (Theorem 8.17) -/

/-- Alpha-structural recursion: the unique equivariant homomorphism from the
initial algebra to any other `sig`-algebra.

Given a nominal algebra `(Y, θ)`, there exists a unique equivariant map
`fold : μT → Y` satisfying `fold ∘ constr = θ ∘ T(fold)`, where `constr`
is the algebra structure map of the initial algebra.

The binding case (for `nameAbs σ` arities) uses `liftFCB`/`liftFresh`
from `FCB.lean` (Corollary 4.17) to ensure the fold is well-defined on
alpha-equivalence classes. -/
noncomputable def fold {Y : Type u} [Nominal α Y]
    (sig : NomSig) (alg : NomAlgebra α sig Y) :
    InitialAlg α sig → Y := sorry

/-- `fold` is equivariant. -/
theorem fold_equivariant {Y : Type u} [Nominal α Y]
    (sig : NomSig) (alg : NomAlgebra α sig Y) :
    IsEquivariant α (fold sig alg) := sorry

/-- `fold` commutes with the algebra structure maps:
`fold alg (constr x) = alg.str (T(fold alg) x)`. -/
theorem fold_computation {Y : Type u} [Nominal α Y]
    (sig : NomSig) (alg : NomAlgebra α sig Y)
    (x : sigFunctor α sig (InitialAlg α sig)) :
    fold sig alg ((InitialAlg.algebra α sig).str x) =
      alg.str (sigMap sig (fold sig alg) (fold_equivariant sig alg) x) := sorry

/-- `fold` is the unique such homomorphism. -/
theorem fold_unique {Y : Type u} [Nominal α Y]
    (sig : NomSig) (alg : NomAlgebra α sig Y)
    (g : InitialAlg α sig → Y) (hg : IsEquivariant α g)
    (hcomm : ∀ x, g ((InitialAlg.algebra α sig).str x) =
      alg.str (sigMap sig g hg x)) :
    g = fold sig alg := sorry

/-- `fold` packaged as an algebra homomorphism. -/
noncomputable def foldHom {Y : Type u} [Nominal α Y]
    (sig : NomSig) (alg : NomAlgebra α sig Y) :
    NomAlgebra.Hom α sig (InitialAlg.algebra α sig) alg :=
  { map := fold sig alg
    map_equivariant := fold_equivariant sig alg
    comm := fold_computation sig alg }

/-! ### Section 7: Alpha-structural induction (Theorem 8.21) -/

/-- Alpha-structural induction for the initial algebra.

To prove a property `P` holds for all elements of `μT`, it suffices to show
that `P` is closed under each operation symbol. For operation symbols whose
arity contains a `nameAbs σ` component, the bound atom `a` in `⟪a⟫x` may be
chosen *fresh for any given finite set of parameters* — this is the nominal
strengthening that formalises the "Barendregt variable convention".

The freshness assumption is justified by `exists_fresh_rep` from
`NameAbstraction.lean` and the `someAny` theorem from `FreshQuantifier.lean`. -/
theorem initialAlg_induction (sig : NomSig)
    (P : InitialAlg α sig → Prop)
    (hP : EquivariantPred α P)
    (hstep : ∀ (x : sigFunctor α sig (InitialAlg α sig)),
      -- Assume P holds for all recursive subterms (encoded in the functor image)
      -- Then P holds for the constructed term
      P ((InitialAlg.algebra α sig).str x)) :
    ∀ t, P t := sorry

/-- Alpha-structural induction with freshness: a variant where the induction
hypothesis for binding positions allows choosing the bound atom fresh for
a given parameter `z : Z`.

This is the form most commonly used in practice (Pitts, Theorem 8.21). -/
theorem initialAlg_induction_fresh (sig : NomSig)
    (P : InitialAlg α sig → Prop)
    (hP : EquivariantPred α P)
    {Z : Type u} [Nominal α Z] (z : Z)
    (hstep : ∀ (x : sigFunctor α sig (InitialAlg α sig)),
      P ((InitialAlg.algebra α sig).str x)) :
    ∀ t, P t := sorry

/-! ### Section 8: Lambda calculus example -/

/-! We instantiate the generic machinery for the untyped lambda calculus:

- **Signature**: `var : A → Λ`, `app : Λ × Λ → Λ`, `lam : [A]Λ → Λ`.
- **Sort expressions**: `.data` (variable takes an atom = the data sort in
  disguise — we use `.data` and interpret atoms via the initial algebra),
  `.prod .data .data` (application), `.nameAbs .data` (lambda).

Note: Strictly speaking, `var` takes an atom `α`, not a recursive `data` argument.
For the signature functor we model the variable case with a dedicated `atom` sort
expression or by directly constructing the lambda calculus as a special case.
Here we take the direct approach.
-/

/-- The signature for the untyped lambda calculus.

- Operation 0: `var` — arity is `.data` (an atom, identified with the data sort
  at the level of the initial algebra which contains atoms as generators).
- Operation 1: `app` — arity is `.prod .data .data` (two recursive subterms).
- Operation 2: `lam` — arity is `.nameAbs .data` (a name abstraction of a subterm). -/
def LambdaSig : NomSig := [.data, .prod .data .data, .nameAbs .data]

/-- The type of untyped lambda-terms modulo alpha-equivalence. -/
noncomputable def Lambda (α : Type u) [Name α] : Type u := InitialAlg α LambdaSig

namespace Lambda

variable (α : Type u) [Name α]

/-- Lambda-terms form a nominal set with `supp(t) = FV(t)`. -/
noncomputable instance instNominal : Nominal α (Lambda α) :=
  InitialAlg.instNominal α LambdaSig

/-! #### Constructors -/

/-- Variable: injects an atom into the term language.
`var a` is the lambda-term consisting of the single free variable `a`. -/
noncomputable def var (a : α) : Lambda α := sorry

/-- Application: `app t₁ t₂` represents `(t₁ t₂)`. -/
noncomputable def app (t₁ t₂ : Lambda α) : Lambda α := sorry

/-- Lambda-abstraction: `lam ⟪a⟫t` represents `λa.t`, where `⟪a⟫t` is
the alpha-equivalence class of the pair `(a, t)`. -/
noncomputable def lam (body : NameAbs α (Lambda α)) : Lambda α := sorry

/-! #### Equivariance of constructors -/

@[simp] theorem var_equivariant (π : FinitePerm α) (a : α) :
    π • var α a = var α (π • a) := sorry

@[simp] theorem app_equivariant (π : FinitePerm α) (t₁ t₂ : Lambda α) :
    π • app α t₁ t₂ = app α (π • t₁) (π • t₂) := sorry

@[simp] theorem lam_equivariant (π : FinitePerm α) (body : NameAbs α (Lambda α)) :
    π • lam α body = lam α (π • body) := sorry

/-! #### Support -/

/-- The support of a variable is the singleton containing that atom. -/
@[simp] theorem supp_var (a : α) : supp (var α a) = {a} := sorry

/-- The support of an application is the union of the supports. -/
@[simp] theorem supp_app (t₁ t₂ : Lambda α) :
    supp (app α t₁ t₂) = supp t₁ ∪ supp t₂ := sorry

/-- The support of a lambda-abstraction removes the bound variable.
This is the key property: `FV(λa.t) = FV(t) \ {a}`. -/
@[simp] theorem supp_lam (a : α) (t : Lambda α) :
    supp (lam α ⟪a⟫t) = supp t \ {a} := sorry

/-! #### Injectivity and distinctness -/

theorem var_injective : Function.Injective (var α) := sorry

theorem app_injective :
    Function.Injective (fun p : Lambda α × Lambda α => app α p.1 p.2) := sorry

theorem lam_injective : Function.Injective (lam α) := sorry

theorem var_ne_app (a : α) (t₁ t₂ : Lambda α) : var α a ≠ app α t₁ t₂ := sorry

theorem var_ne_lam (a : α) (body : NameAbs α (Lambda α)) :
    var α a ≠ lam α body := sorry

theorem app_ne_lam (t₁ t₂ : Lambda α) (body : NameAbs α (Lambda α)) :
    app α t₁ t₂ ≠ lam α body := sorry

/-! #### Alpha-structural recursion for lambda terms -/

/-- Recursion principle for lambda-terms.

Given:
- `fvar : α → Y` (equivariant)
- `fapp : Y → Y → Y` (equivariant)
- `flam : NameAbs α Y → Y` (equivariant)

there exists a unique equivariant `rec : Lambda α → Y` satisfying:
```
  rec (var a)       = fvar a
  rec (app t₁ t₂)  = fapp (rec t₁) (rec t₂)
  rec (lam ⟪a⟫ t)  = flam ⟪a⟫ (rec t)
``` -/
noncomputable def rec {Y : Type u} [Nominal α Y]
    (fvar : α → Y) (hvar : IsEquivariant α fvar)
    (fapp : Y → Y → Y) (happ : IsEquivariant₂ α fapp)
    (flam : NameAbs α Y → Y) (hlam : IsEquivariant α flam) :
    Lambda α → Y := sorry

/-- `rec` is equivariant. -/
theorem rec_equivariant {Y : Type u} [Nominal α Y]
    (fvar : α → Y) (hvar : IsEquivariant α fvar)
    (fapp : Y → Y → Y) (happ : IsEquivariant₂ α fapp)
    (flam : NameAbs α Y → Y) (hlam : IsEquivariant α flam) :
    IsEquivariant α (rec α fvar hvar fapp happ flam hlam) := sorry

/-- Computation rule for `rec` at variables. -/
@[simp] theorem rec_var {Y : Type u} [Nominal α Y]
    (fvar : α → Y) (hvar : IsEquivariant α fvar)
    (fapp : Y → Y → Y) (happ : IsEquivariant₂ α fapp)
    (flam : NameAbs α Y → Y) (hlam : IsEquivariant α flam)
    (a : α) : rec α fvar hvar fapp happ flam hlam (var α a) = fvar a := sorry

/-- Computation rule for `rec` at applications. -/
@[simp] theorem rec_app {Y : Type u} [Nominal α Y]
    (fvar : α → Y) (hvar : IsEquivariant α fvar)
    (fapp : Y → Y → Y) (happ : IsEquivariant₂ α fapp)
    (flam : NameAbs α Y → Y) (hlam : IsEquivariant α flam)
    (t₁ t₂ : Lambda α) :
    rec α fvar hvar fapp happ flam hlam (app α t₁ t₂) =
      fapp (rec α fvar hvar fapp happ flam hlam t₁)
           (rec α fvar hvar fapp happ flam hlam t₂) := sorry

/-- Computation rule for `rec` at lambda-abstractions.

`liftAbs` lifts the equivariant `rec` function through the abstraction:
`rec (lam ⟪a⟫t) = flam ⟪a⟫(rec t)`. -/
@[simp] theorem rec_lam {Y : Type u} [Nominal α Y]
    (fvar : α → Y) (hvar : IsEquivariant α fvar)
    (fapp : Y → Y → Y) (happ : IsEquivariant₂ α fapp)
    (flam : NameAbs α Y → Y) (hlam : IsEquivariant α flam)
    (body : NameAbs α (Lambda α)) :
    rec α fvar hvar fapp happ flam hlam (lam α body) =
      flam (NameAbs.liftAbs
        (rec_equivariant α fvar hvar fapp happ flam hlam) body) := sorry

/-- Uniqueness of `rec`: any equivariant function satisfying the computation
rules must equal `rec`. -/
theorem rec_unique {Y : Type u} [Nominal α Y]
    (fvar : α → Y) (hvar : IsEquivariant α fvar)
    (fapp : Y → Y → Y) (happ : IsEquivariant₂ α fapp)
    (flam : NameAbs α Y → Y) (hlam : IsEquivariant α flam)
    (g : Lambda α → Y) (hg : IsEquivariant α g)
    (hg_var : ∀ a, g (var α a) = fvar a)
    (hg_app : ∀ t₁ t₂, g (app α t₁ t₂) = fapp (g t₁) (g t₂))
    (hg_lam : ∀ body, g (lam α body) = flam (NameAbs.liftAbs hg body)) :
    g = rec α fvar hvar fapp happ flam hlam := sorry

/-! #### Alpha-structural induction for lambda terms -/

/-- Alpha-structural induction for lambda-terms.

To prove `P(t)` for all `t : Lambda α`, it suffices to show:
1. `P(var a)` for all atoms `a`.
2. `P(t₁) ∧ P(t₂) → P(app t₁ t₂)` for all `t₁, t₂`.
3. For any parameters, choosing `a` fresh: `P(t) → P(lam ⟪a⟫ t)`. -/
theorem induction
    (P : Lambda α → Prop) (hP : EquivariantPred α P)
    (hvar : ∀ a, P (var α a))
    (happ : ∀ t₁ t₂, P t₁ → P t₂ → P (app α t₁ t₂))
    (hlam : ∀ (a : α) (t : Lambda α), P t → P (lam α ⟪a⟫t)) :
    ∀ t, P t := sorry

/-- Alpha-structural induction with freshness: the bound variable in the
`lam` case may be chosen fresh for any given parameter `z : Z`.

This is the "Barendregt variable convention" made rigorous:
in the `lam` case, one may assume `a # z` for the proof parameter `z`. -/
theorem induction_fresh
    (P : Lambda α → Prop) (hP : EquivariantPred α P)
    {Z : Type u} [Nominal α Z] (z : Z)
    (hvar : ∀ a, P (var α a))
    (happ : ∀ t₁ t₂, P t₁ → P t₂ → P (app α t₁ t₂))
    (hlam : ∀ (a : α) (t : Lambda α), a # z → P t → P (lam α ⟪a⟫t)) :
    ∀ t, P t := sorry

/-! #### Capture-avoiding substitution -/

/-- Capture-avoiding substitution `[x := s]t`, defined by alpha-structural
recursion. This is the canonical first application of the recursion principle.

The definition via `rec` is:
```
  [x := s](var a)       = if a = x then s else var a
  [x := s](app t₁ t₂)  = app ([x := s]t₁) ([x := s]t₂)
  [x := s](lam ⟪a⟫ t)  = lam ⟪a⟫ ([x := s]t)    -- valid when a # (x, s)
```

The `lam` clause satisfies FCB because for cofinitely many `a`, `a # (x, s)`,
ensuring no variable capture. -/
noncomputable def subst (x : α) (s : Lambda α) : Lambda α → Lambda α := sorry

/-- Substitution at a matching variable. -/
@[simp] theorem subst_var_eq (x : α) (s : Lambda α) :
    subst α x s (var α x) = s := sorry

/-- Substitution at a non-matching variable. -/
@[simp] theorem subst_var_ne (x : α) (s : Lambda α) (a : α) (hne : a ≠ x) :
    subst α x s (var α a) = var α a := sorry

/-- Substitution distributes over application. -/
@[simp] theorem subst_app (x : α) (s t₁ t₂ : Lambda α) :
    subst α x s (app α t₁ t₂) = app α (subst α x s t₁) (subst α x s t₂) := sorry

/-- Substitution passes through lambda when the bound variable is fresh.

This is the key equation: `[x := s](λa.t) = λa.([x := s]t)` when `a # (x, s)`.
The freshness condition `a # (x, s)` ensures no variable capture, and the
alpha-equivalence quotient guarantees such a representative always exists. -/
@[simp] theorem subst_lam (x : α) (s : Lambda α) (a : α) (t : Lambda α)
    (hfresh : a # (x, s)) :
    subst α x s (lam α ⟪a⟫t) = lam α ⟪a⟫(subst α x s t) := sorry

/-- Substitution is equivariant. -/
theorem subst_equivariant (x : α) (s : Lambda α) :
    IsEquivariant α (subst α x s) := sorry

/-- Substitution permutation law: `π • [x := s]t = [π • x := π • s](π • t)`. -/
theorem subst_smul (π : FinitePerm α) (x : α) (s t : Lambda α) :
    π • subst α x s t = subst α (π • x) (π • s) (π • t) := sorry

end Lambda

end NominalSets
