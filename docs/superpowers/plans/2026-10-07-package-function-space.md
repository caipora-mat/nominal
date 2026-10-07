# F05 Function-Space and Predicate-Input Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task. The author approved native execution with one fresh independent final review. Steps use checkbox syntax for tracking.

**Goal:** Deliver PKG-F05's approved hybrid function foundation, with general conjugation objects, ordinary map/predicate certificates, supported function values, exact admissible-curry contracts, public consumers, audited proofs and reconciled LaTeX.

**Architecture:** A Mathlib-level action/support layer supplies the full function carrier. Finite-permutation specializations connect ordinary inputs to existing elementwise support and freshness. A proof-field bundle restricts to supported functions without requiring nominal domain/codomain carriers; predicate logic and context-scanning automation remain outside this increment.

**Tech Stack:** Lean/Mathlib `v4.34.1`; Mathlib revision `d13f23b723b8a846827a245b89c10fc7d3f11612`; Lake, Python import coverage, the existing module-origin axiom audit, and LaTeX/latexmk.

**Spec:** [Approved F05 specification](../specs/2026-10-07-package-function-space-design.md). The author approved the written specification on 2026-10-07. The author subsequently approved this plan for native execution. All seven tasks, integrated checks, delivery reconciliation and the fresh independent final review are complete. F05 is delivered uncommitted.

## Global Constraints

- Work in `/home/fab/Documents/nominal/nominal` on `fasapa/nominal-package`. Planning inspected HEAD `32f3dba551761881409bbc7453054e214e582269`; the existing uncommitted F05 research, probes, article and specification must be preserved.
- No branch switching, commits, pushes, merges, publication, dependency upgrades or CI changes. Use the requested checkout; do not create a worktree or run a branch-finishing workflow. Per-task checkpoints below are verification records, not commits.
- All new implementation belongs under top-level `Package/`. Preserve `Nominal/`, `Instances/`, existing examples and `docs/roadmap.md`. The active tracker is `docs/nominal-package-roadmap.md`. Do not restart F02–F04.
- Retain `NominalPackage`, `Perm A`, selected actions and independent group/atom/domain/codomain universes. A phantom group or proof field must not raise a function carrier above `Type (max uX uY)`.
- Preserve bare function pointwise action, bare permutation left multiplication and existing selected actions. No alternate action on bare arrows or global action/nominality on Prop. No atom outParam. Finset/Set image actions retain the consumer's `Pointwise` scope.
- Ordinary inputs lead definitions and theorem entry points; supported bundles carry persistent support evidence. No implicit ordinary-to-supported conversion. Supply explicit A/G on ambiguous adapters and only one automatic coercion route, through FunLike to ordinary functions.
- Use particular support certificates whenever sufficient. `Infinite A` belongs to least support/freshness; visible finite unions/images retain equality decisions. Existential support witnesses use local classical reasoning inside proofs.
- Keep computable function bodies computable. Store support existence only in proof fields. Reuse Mathlib Support, FunLike/DFunLike, MulActionHom, Function.curry/uncurry and action restriction/transfer; do not duplicate generic infrastructure.
- Do not introduce sorry, admit, custom axioms, disabled kernel checking, broad instance-priority/reducibility changes or linter suppression. The audit permits only propext, Classical.choice and Quot.sound.
- Full curry is unrestricted; supported curry requires all sections supported, with individual parameter evidence or nominal parameter carrier as sufficient adapters. Never add nominality of the other carriers to repair a proof.
- Full predicate logic, Some/Any, surjective-equivariant predicate pullback/reflection, predicate quotient descent and final supported-predicate storage remain PKG-01. Binders/FCB, syntax, recursion and generators remain separate tasks.
- The context-bound rule accepts certified local/user-provided values and sufficient bounds. No scanner, capture macro, automatic arbitrary-global certification or least-support inference is implemented here.
- Develop/reconcile `docs/article/sections/functions.tex` alongside the mathematics. Keep task IDs, approvals, implementation stages, build logs, counts, cache conditions and review verdicts outside the article.
- Temporary consumers import only `Package`, use `set_option autoImplicit false` and meaningful conclusions, and live outside the repository. Do not add a persistent `Package/Examples` layer. Preserve historical scratch probes unchanged.

## Review Focus

- **Competing actions on the same underlying type:** identity must be invariant as a function object while the ordinary pointwise identity moves. Tasks 1–2 test both, plus explicit arrowAction and alternate selected domain actions.
- **Phantom inference and unrelated universes:** two atom sorts must coexist without accidental inference from the codomain or a universe equality. Tasks 1, 4 and 5 use explicitly quantified independent universes and mixed-atom consumers.
- **Empty domains and unsupported codomain values:** empty functions remain supported; constants reflect support only with the stated hypotheses. Tasks 3, 5 and 6 test empty and nonempty cases without carrier-wide nominality.
- **Certificates disappearing through coercions or proof choices:** ordinary rw/simp/ext and higher-order consumers must work without unfolding support proofs, including a constructor whose proof uses noncomputable support. Task 5 tests this explicitly.
- **Context overapproximation versus section admissibility:** extra certified captures may enlarge bounds, but neither arbitrary globals nor supported binary functions automatically yield supported sections. Tasks 3, 4 and 6 prove positive context consumers and negative projection/predicate examples.

## Files, dependencies and verification setup

| File | Responsibility and owner task |
| --- | --- |
| `Package/Foundations/ActionSupport.lean` (new) | Task 1: arbitrary-scalar injective support reflection and same-group support transport |
| `Package/Foundations/FunctionAction.lean` (new) | Task 1: full function carrier/action/FunLike; Task 2: combinators, curry and general support correspondence |
| `Package/Foundations/FunctionSupport.lean` (new) | Task 3: ordinary finite map certificates, particular-value support/freshness bounds, Mathlib hom adapters |
| `Package/Foundations/PredicateSupport.lean` (new) | Task 4: ordinary Prop certificates, renaming and discrete-truth/subset bridges |
| `Package/Foundations/SupportedFunction.lean` (new) | Task 5: supported values and core operations; Task 6: admissible currying |
| `Package.lean` | Export each new module when introduced |
| `Package/Tests/AxiomAudit.lean` | Task 7: representative prints; preserve its complete traversal and policy |
| `Package/README.md` | Task 7: actual public interface, assumptions, ordinary/bundled use and limitations |
| `docs/article/sections/functions.tex` | Tasks 1–6: reconcile corresponding mathematics and selected Lean correspondence |
| `docs/article/main.tex`, `sections/perspectives.tex` | Task 7: reconcile abstract/scope/cross-references; preserve grounded comparisons |
| Active roadmap, this plan, spec, research README/readiness/article-plan/F05 investigation | Task 7: current-state and evidence reconciliation, preserving historical records |

`ActionSupport.lean` is the small shared module permitted by spec §7: its lemmas
concern arbitrary scalar actions, not functions or atoms, and are reused by
function equivalences and the bundle embedding. This avoids placing general
support reflection in a function namespace or refactoring delivered F04.

Import direction:

```text
ActionSupport       → Mathlib.GroupTheory.GroupAction.Support
FunctionAction      → ActionSupport; Mathlib FunLike/Hom/Prod/Function machinery
FunctionSupport     → FunctionAction; Package.Foundations.Canonical/Freshness
PredicateSupport      → FunctionSupport
SupportedFunction   → FunctionSupport; Mathlib SubMulAction
Package             → all five new modules, plus its existing imports
```

No import from reference Nominal/Instances or research probes. The current
checker classifies `Package.Foundations.*` automatically; its implementation
and Lake configuration need no changes. If a proposed Mathlib import is not
actually needed, omit it; keep the above Package dependency direction.

Run tasks **1 → 2 → 3 → 4 → 5 → 6 → 7**. Tasks 4 and 5 are mathematically
independent after 3, but root owns shared exports/docs; parallel execution is
optional only if the selected method assigns disjoint ownership explicitly.

At execution start create a fresh directory using
`mktemp -d /tmp/nominal-package-f05-execution.XXXXXX`, record its path in this
plan's execution log, and use it wherever `$PKG_F05_CHECKS` appears below.
Record initial status and file hashes there before edits. Use these standalone
consumer files: `01Actions.lean`, `02FunctionLaws.lean`, `03MapSupport.lean`,
`04Predicates.lean`, `05SupportedValues.lean`, `06Curry.lean`,
`07Boundaries.lean`, `08PublicSignatures.lean`. Their exact assertions are
assigned below; implement ordinary proof bodies during execution.

Each test cycle first runs the new public-name consumer and records the expected
missing-declaration failure. Do not introduce placeholder production proofs to
make imports pass. Existing-theory fixtures must already work. A final negative
test is a proved nonexistence statement or a guarded intended elaboration error,
not a broken source file. Commands below are future checks, not checks run while
writing this plan.

## Task 1: General support adapters and full function action (F05a)

**Files:** Create ActionSupport.lean and FunctionAction.lean; update Package.lean
and the full-function-space article subsection. Tests: `01Actions.lean`.

**Interfaces:** Consume Mathlib `MulAction.Supports`, `FunLike`, `DFunLike.ext`
and the selected action laws. Produce the following under `NominalPackage`:

```text
ActionSupport.supports_map_iff
  [SMul M B] [SMul M X] [SMul M Y]
  (f : X → Y) (hf : ∀ m x, f (m • x) = m • f x)
  (hinj : Function.Injective f) (S : Set B) (x : X) :
  MulAction.Supports M S (f x) ↔ MulAction.Supports M S x
ActionSupport.supports_smul_iff
  [Group G] [MulAction G B] [MulAction G X]
  (g : G) (S : Set B) (x : X) :
  MulAction.Supports G (g • S) (g • x) ↔ MulAction.Supports G S x

structure FunctionObject (G : Type u) (X : Type v) (Y : Type w) : Type (max v w)
  toFun : X → Y
FunctionObject.ofFun (G) (f : X → Y) : FunctionObject G X Y
FunctionObject.equiv (G) (X) (Y) : FunctionObject G X Y ≃ (X → Y)
FunctionObject.ext : (∀ x, F x = H x) → F = H
```

Define the FunLike instance without action assumptions and the conjugation
MulAction instance under `DivisionMonoid G`, `MulAction G X/Y`. Export
`ofFun_apply`, `coe_ofFun`, `smul_apply`, `smul_apply_smul` and `smul_eq_iff`;
the last two use Group. Their formulas are exactly spec §§2–3.

- [x] **1. Write `01Actions.lean`** with independent universes and these assertions:
  `FunctionObject G X Y : Type (max v w)`; `ofFun G f x = f x` by rfl;
  `(g • F) x = g • F (g⁻¹ • x)`; `(g • f : X → Y) x = g • f x` by rfl;
  `(g • F) (g • x) = g • F x`; `g • F = F ↔ ∀ x, F (g • x) = g • F x`.
  Include a scalar-only injective-support reflection consumer and a noncommutative
  group transport consumer to exclude an accidental SMulCommClass premise.
- [x] **2. Run `lake env lean "$PKG_F05_CHECKS/01Actions.lean"`**; expect missing
  F05 declarations, with existing pointwise-action fixtures passing.
- [x] **3. Implement ActionSupport.lean** by injection cancellation and conjugating
  a pointwise fixer; adapt the proved generalization evidence, not Mathlib's
  commuting-action transport statement.
- [x] **4. Implement FunctionAction.lean's carrier/action/interface**. Expose the
  formula explicitly while constructing the instance if simp cannot unfold the
  operation under construction. Export modules through Package.
- [x] **5. Check action selection** using two separately selected actions on an
  external carrier in separate sections. Theorems must use each selected action;
  the ordinary type equivalence must not claim equivariance to pointwise arrows.
- [x] **6. Run `lake build Package.Foundations.ActionSupport Package.Foundations.FunctionAction Package`**,
  then the consumer; require exit 0 without new warnings. Inspect
  `#print axioms ActionSupport.supports_map_iff`, `.supports_smul_iff`, and
  `FunctionObject.smul_eq_iff` in the consumer.
- [x] **7. Reconcile article §Full function spaces** with actual generality and
  record the task checkpoint. Do not present DivisionMonoid curry as an
  exponential theorem; the categorical interpretation uses groups.

## Task 2: Full function operations and support correspondence (F05a)

**Files:** Extend FunctionAction.lean and the corresponding article sections.
Tests: `02FunctionLaws.lean`.

**Interfaces:** Consume Task 1. Produce ordinary computable operations:

```text
FunctionObject.id (G) (X) : FunctionObject G X X
FunctionObject.const (G) (X) (y : Y) : FunctionObject G X Y
FunctionObject.comp (H : FunctionObject G Y Z) (F : FunctionObject G X Y) : FunctionObject G X Z
FunctionObject.pair (F : FunctionObject G X Y) (H : FunctionObject G X Z) : FunctionObject G X (Y × Z)
FunctionObject.eval : FunctionObject G X Y × X → Y
FunctionObject.curry (F : FunctionObject G (X × Y) Z) : FunctionObject G X (FunctionObject G Y Z)
FunctionObject.uncurry (H : FunctionObject G X (FunctionObject G Y Z)) : FunctionObject G (X × Y) Z
FunctionObject.curryEquiv (G) (X) (Y) (Z) :
  FunctionObject G (X × Y) Z ≃ FunctionObject G X (FunctionObject G Y Z)
FunctionObject.evalHom (G) (X) (Y) : (FunctionObject G X Y × X) →[G] Y
```

Operations and inverse equations need no action; evalHom uses Group/actions.
Export application and coerced-function equations, `comp_assoc`, `comp_id`,
`id_comp`, `uncurry_curry`, `curry_uncurry`, `smul_id/const/comp/pair`,
`curry_smul`, `uncurry_smul`. Curry action equations retain DivisionMonoid;
identity fixation/evaluation/composition equivariance use Group. Pairing and
constants retain only the action hypotheses their formulas use.
Also produce the action-free `FunctionObject.const_injective_iff`:
`Injective (FunctionObject.const G X : Y → FunctionObject G X Y) ↔
Nonempty X ∨ Subsingleton Y`. Reuse pinned `Function.const_injective`
for the Nonempty case; the empty case is subsingleton extensionality.

With `[Group G] [SMul G B]` and actions on X/Y, export
`FunctionObject.supports_iff (G) (S : Set B) (f : X → Y)` equating object
support with `∀ g, (∀ b ∈ S, g • b = b) → ∀ x, f (g • x) = g • f x`.
Export `supports_curry_iff` and `supports_uncurry_iff` for arbitrary Set bounds;
they use the equivariant inverse maps, so DivisionMonoid suffices with the
appropriate actions. No atom or finite-support theory enters this module.

- [x] **1. Write `02FunctionLaws.lean`** asserting all seven operations' computation
  formulas from spec §3, both inverse equations, ordinary higher-order `List.map`
  use, and nested `ext x y`. Include `curry_smul` at DivisionMonoid generality and
  curry round trips on empty domains without Nonempty assumptions.
- [x] **2. Run its direct Lean command** and record missing operation/law failures.
- [x] **3. Implement the operations and laws** using ordinary Function.curry/uncurry,
  FunLike extensionality and Task 1 reflection for inverse maps. Reuse
  MulActionHom for evalHom; add no custom equivariant-map bundle.
- [x] **4. Add `identityActionsDiffer`**: conjugation fixes identity on Bool, while
  `Perm.swap false true • (id : Bool → Bool) ≠ id` under the ordinary action.
  Also assert explicit arrowAction computes by inverse precomposition only.
  Use `supports_iff` and both curry support equivalences in actual conclusions.
- [x] **5. Build FunctionAction and Package; run consumers 01–02** with exit 0.
  Print axioms for curryEquiv, evalHom and supports_iff. Normalize applications
  and coercions by simp; leave reverse conversion/action rewrites named if they
  would introduce loops.
- [x] **6. Reconcile the evaluation/curry exposition and record F05a's checkpoint.**

## Task 3: Ordinary supported-map inputs and context bounds (F05b)

**Files:** Create FunctionSupport.lean; update Package.lean and support/context
article subsections. Tests: `03MapSupport.lean`, start `07Boundaries.lean`.

**Interfaces:** Consume Task 2 and F04 support/least support/freshness. Define
`SupportsMap S f` and `FinitelySupportedMap A f` exactly as spec §4, with A
explicit on the existential predicate and no new ordinary-arrow action.
Produce these stable adapter and closure names:

```text
supportsMap_iff (S) (f) : SupportsMap S f ↔ Supports S (FunctionObject.ofFun (Perm A) f)
finitelySupportedMap_iff (A) (f) : FinitelySupportedMap A f ↔ FinitelySupported A (FunctionObject.ofFun (Perm A) f)
FinitelySupportedMap.toObject (hf : FinitelySupportedMap A f) : FinitelySupported A (FunctionObject.ofFun (Perm A) f)
supportsMap_empty_iff (A) (f) : SupportsMap ∅ f ↔ Equivariant A f
Equivariant.toMulActionHom (hf : Equivariant A f) : X →[Perm A] Y
equivariant_coe_mulActionHom (f : X →[Perm A] Y) : Equivariant A (f : X → Y)
```

Provide `SupportsMap.mono`, `.finitelySupported`, `.apply_same`, `.apply`,
`.comp`, `.pair`, `.section`, `supportsMap_id`, `supportsMap_const`,
`supportsMap_smul_iff`, and `Equivariant.supportsMap_section`. Their exact
premise/result bounds are the spec §4 table; `.apply_same` has one shared S;
`.section` uses `F : P × X → Y`, with output `x ↦ F (p,x)` and union S ∪ T.
Finite-existence counterparts are `FinitelySupportedMap.apply/comp/pair/section`,
`finitelySupportedMap_const`, and `Equivariant.finitelySupportedMap_section`.
Use local classical witnesses in these proof-producing declarations.

Also produce `FinitelySupportedMap.curry` taking `hf : FinitelySupportedMap A f`
for `f : X × Y → Z` to evidence for
`fun x => FunctionObject.ofFun (Perm A) (fun y => f (x,y))`; `.uncurry` takes
evidence for `H : X → FunctionObject (Perm A) Y Z` to evidence for
`fun p : X × Y => H p.1 p.2`. These are full-object codomains, not supported
bundles or ordinary pointwise nested arrows.

With Infinite A, name the least-support laws
`FinitelySupportedMap.support_apply_subset`, `.support_comp_subset`,
`.support_section_subset`, `.support_pair`, `.support_const`,
`.support_curry`, `.support_uncurry`, `.support_eq_empty_iff`.
Each denotes the existing support of `.toObject`; constants take the value
certificate and require Nonempty X for equality, and curry refers here to full
function objects. Export existential/full-object support preservation through
curry/uncurry as needed to type these results. Independently supplied output
certificates agree using F04 `.support_eq`; do not define another support choice.

In particular, with the inferred f/g/F/x/p and their corresponding certificates:

```text
hf.support_apply_subset hx : (hf.apply hx).support ⊆ hf.toObject.support ∪ hx.support
hg.support_comp_subset hf : (hg.comp hf).toObject.support ⊆ hg.toObject.support ∪ hf.toObject.support
hf.support_pair hg : (hf.pair hg).toObject.support = hf.toObject.support ∪ hg.toObject.support
hF.support_section_subset hp : (hF.section hp).toObject.support ⊆ hF.toObject.support ∪ hp.support
hf.support_curry : hf.curry.toObject.support = hf.toObject.support
hh.support_uncurry : hh.uncurry.toObject.support = hh.toObject.support
FinitelySupportedMap.support_const (X) hy [Nonempty X] :
  (finitelySupportedMap_const (X := X) hy).toObject.support = hy.support
hf.support_eq_empty_iff : hf.toObject.support = ∅ ↔ Equivariant A f
```

- [x] **1. Write `03MapSupport.lean`** using selected actions only. Assertions:
  map-certificate correspondence and its converse; evaluation union bound;
  existential support of `f x` from hf/hx; composition bound; exact pairing
  support; fixed-parameter support from joint equivariance and a single hp.
  Use no Nominal assumptions in these consumers.
- [x] **2. Add `contextBound`**: for equivariant `E : (P × Q) × X → Y`,
  `Supports S p`, `Supports T q`, and arbitrary finite U, prove
  `SupportsMap ((S ∪ T) ∪ U) (fun x => E ((p,q),x))` using the exported
  constructors. The proof must not invoke least support or Infinite A.
- [x] **3. Run the consumers before implementation**; require missing F05 names
  rather than unrelated fixture/type errors.
- [x] **4. Implement certificate definitions, correspondences and sufficient-bound
  constructors** through Task 2 and F04 map/product/transport laws. Add the
  Mathlib hom adapters here, avoiding changes to delivered Action.lean.
- [x] **5. Implement existential, least-support and freshness corollaries**. For
  supported z, `(hf.toObject).FreshWith hz` and `hx.FreshWith hz` imply
  `(hf.apply hx).FreshWith hz`; export this as
  `FinitelySupportedMap.freshWith_apply` and derive the atom `.fresh_apply`.
  No nominality of any participating full carrier is allowed.
- [x] **6. Test empty/constant boundaries**: `supportsMap_const_iff` with Nonempty X;
  `supportsMap_of_isEmpty` with IsEmpty X and arbitrary f; and the sharp
  `Function.Injective (Function.const X : Y → X → Y) ↔ Nonempty X ∨ Subsingleton Y`.
  Consume Task 2's `FunctionObject.const_injective_iff` for the full-object
  version, without actions. Prove empty
  function support is ∅ over infinite atoms even with unsupported codomain values.
- [x] **7. Build FunctionSupport and Package; run consumers 01–03 and the current
  boundary file.** Inspect exact #check signatures and representative axioms
  for evaluation, context support, pairing equality and heterogeneous freshness.
- [x] **8. Reconcile support/context and empty-domain article statements; record checkpoint.**

## Task 4: Predicate-input certificates with ordinary Prop (F05b)

**Files:** Create PredicateSupport.lean; update Package.lean and predicate/article
comparisons. Tests: `04Predicates.lean`, extend `07Boundaries.lean`.

**Interfaces:** Consume Task 3 and existing `Discrete A Prop`. Produce:

```text
SupportsPred (S : Finset A) (P : X → Prop) : Prop
FinitelySupportedPred (A) (P : X → Prop) : Prop := ∃ S, SupportsPred S P
renamePred (π : Perm A) (P : X → Prop) : X → Prop := fun x => P (π⁻¹ • x)
predicateObject (A) (P : X → Prop) : FunctionObject (Perm A) X (Discrete A Prop)
predicateObjectEquiv (A) (X) : (X → Prop) ≃ FunctionObject (Perm A) X (Discrete A Prop)
supportsPred_iff (S) (P) : SupportsPred S P ↔ Supports S (predicateObject A P)
supportsPred_iff_supportsMap (S) (P) : SupportsPred S P ↔ SupportsMap S (fun x => (Discrete.mk (P x) : Discrete A Prop))
supportsPred_iff_set (S) (P) : SupportsPred S P ↔ Supports S {x | P x}
```

The last contract fixes the scoped Mathlib Set image action. Use explicit
Set.ofPred construction where needed, not ambiguous ordinary-arrow ascription.
Export `predicateObject_apply`, `.val` application normalization,
`predicateObject_rename`, `renamePred_one`, `renamePred_mul`,
`renamePred_apply_smul`, and the equality with explicitly supplied arrowAction.
Define `SupportsPred` by the Iff equation in the spec; no Prop action premise.

Provide `SupportsPred.mono/precomp/section/finitelySupported`,
`supportsPred_empty_iff`, `supportsPred_smul_iff`,
`finitelySupportedPred_iff` (object correspondence), and finite-existence
precomp/section counterparts. Empty support is `∀ π x, P (π • x) ↔ P x`.
Precomp takes predicate bound S and map bound T; section takes relation bound
S and parameter bound T; both yield S ∪ T. Derive the jointly invariant section
adapter. No Boolean algebra, quantifier or descent operations are added.

- [x] **1. Write `04Predicates.lean`**: ordinary Iff rewriting; both directions of
  the discrete-truth and Set bridges; predicateObjectEquiv round trips; renaming
  computation; precomposition and section support; existential correspondence.
  Include simultaneous atom types A/B in independent universes, with explicit
  atom arguments and no ambient Prop action.
- [x] **2. Run it before implementation** and record missing predicate declarations.
- [x] **3. Implement the predicate interface** using propext/funext and the map
  certificate bridge. Use Mathlib direct-image membership, with no new Set instance.
- [x] **4. Add `supportsPred_eq_iff`** for `fun y => y = x`, equivalent to
  `Supports S x` on an arbitrary acted carrier. Specialize to the fixed-atom
  predicate: singleton support, exact singleton least support through its object
  over infinite atoms, and noninvariance given explicitly distinct a/b.
- [x] **5. Port negative consumers to the public API**: infinite true/false atom
  sets imply no finite predicate bound; the predicate `(n,b) ↦ b = true` on
  canonical atoms Nat × Bool is a concrete witness. Ordinary application and
  arbitrary Prop motives still typecheck. Prove fresh-selector nonexistence
  using map bounds; retain the stronger proof without an Infinite premise when
  the selector itself supplies the spare atom. Keep these counterexamples in
  temporary consumers, not a new broad production counterexample module.
- [x] **6. Build PredicateSupport and Package; run 04/07** and inspect axiom dependencies
  of the two correspondence theorems and the negative conclusions.
- [x] **7. Reconcile predicate/choice exposition and record the F05b checkpoint.**

## Task 5: Proof-field supported values and ordinary usability (F05c)

**Files:** Create SupportedFunction.lean; update Package.lean and supported-value
article correspondence. Tests: `05SupportedValues.lean`.

**Interfaces:** Consume Tasks 1–3, existing Nominal/Freshness, and Mathlib action
transfer. Produce the structure exactly as spec §5 and:

```text
SupportedMap.ofFun (A) (f : X → Y) (hf : FinitelySupportedMap A f) : SupportedMap A X Y
SupportedMap.ofSupports (A) (f : X → Y) (S : Finset A) (hS : SupportsMap S f) : SupportedMap A X Y
SupportedMap.ofEquivariant (A) (f : X → Y) (hf : Equivariant A f) : SupportedMap A X Y
SupportedMap.ofIsEmpty (A) (f : X → Y) [IsEmpty X] : SupportedMap A X Y
SupportedMap.supportedSubtypeEquiv (A) (X) (Y) :
  SupportedMap A X Y ≃ {F : FunctionObject (Perm A) X Y // FinitelySupported A F}
SupportedMap.supports_iff (S) (F) : Supports S F ↔ SupportsMap S (fun x => F x)
SupportedMap.supports_iff_toObject (S) (F) : Supports S F ↔ Supports S F.toObject
SupportedMap.support_toObject (F) [Infinite A] : support A F = F.supported.support
```

Define `SupportedMap.supportedSubaction A X Y` as the Mathlib SubMulAction
of finitely supported full objects. Its carrier supplies the supported subtype's
restriction action; prove the equivalence action-compatible. Supply
FunLike, ext, proof-witness irrelevance, computable conjugation, `toObject_smul`,
and Nominal A (SupportedMap A X Y), without Nominal X/Y or Infinite A.
Use Function.Injective.mulAction through toObject rather than duplicating
generic transfer laws. No automatic coercion to toObject.

Bundle operations: `id A X`, `const A X y hy`, `comp H F`, `pair F H`,
`eval A X Y : SupportedMap A (SupportedMap A X Y × X) Y`,
`fromParam E hE p hp : SupportedMap A X Y` for equivariant `E : P × X → Y`.
Give application/coercion formulas matching Task 2; support equations/bounds
reuse Task 3 and support reflection. `const` takes particular hy; provide
`constOfNominal A X y` as the nominal-carrier convenience adapter. Include
id/associativity laws, joint action laws, eval equivariance, identity/evaluation
empty support, exact pairing support, conditional constant equality and derived
application/composition/parameter freshness bounds.

- [x] **1. Write `05SupportedValues.lean`** with assertions for the structure's
  universe, support-subtype round trips/action compatibility, arbitrary proof
  witness equality, `Nominal A (SupportedMap A X Y)` under actions only, and
  independently supplied finite-support evidence agreeing on least support.
- [x] **2. Add ordinary consumers**: `xs.map (H.comp F) = (xs.map F).map H`,
  `rw [h]` for bundle equality and coerced-function equality, `ext x`, constructor
  application and whole-coercion simp; an ordinary theorem takes the same lambda
  as fromParam. A nominal higher-order consumer applies eval and uses its support.
- [x] **3. Run before implementation**, confirming missing bundle interfaces.
- [x] **4. Implement the bundle, action and correspondence**, then core operations.
  Route support proofs through the ordinary certificate interface; keep all
  existential witnesses in Prop. Export constructor simp rules robust to both
  named evidence and a literal existential proof.
- [x] **5. Add computation and empty-domain consumers**: use `A := Nat` and
  `X = Y := Discrete Nat Bool`; a computable identity applied to `Discrete.mk true`
  returns true after `.val`. Repackage it with a proof mentioning noncomputable
  least support and still evaluate it (Nat supplies Infinite for that proof).
  Build an empty-domain function without nominal
  Y or an unsupported value's certificate; prove empty support. Nonempty constant
  tests must use the exact support/reflection/injectivity hypotheses.
- [x] **6. Build SupportedFunction and Package; run 05/07**, with no warning or
  certificate unfolding in consumer proofs. Inspect representative constructor,
  nominality, support equality and evaluation axiom lists.
- [x] **7. Reconcile the article's function-value discussion and record checkpoint.**

## Task 6: Supported sections and exact currying (F05c)

**Files:** Extend SupportedFunction.lean and supported-currying exposition.
Tests: `06Curry.lean`, complete `07Boundaries.lean`.

**Interfaces:** Consume Task 5 and full curry from Task 2. Produce:

```text
SupportedMap.uncurry (H : SupportedMap A X (SupportedMap A Y Z)) : SupportedMap A (X × Y) Z
SupportedMap.curryAt (F : SupportedMap A (X × Y) Z) (x : X)
  (hx : FinitelySupported A x) : SupportedMap A Y Z
SupportedMap.SectionsSupported (F : SupportedMap A (X × Y) Z) : Prop :=
  ∀ x, FinitelySupportedMap A (fun y => F (x,y))
SupportedMap.curryWithSections (F) (hs : F.SectionsSupported) : SupportedMap A X (SupportedMap A Y Z)
SupportedMap.curry (F) [Nominal A X] : SupportedMap A X (SupportedMap A Y Z)
SupportedMap.curryEquiv (A) (X) (Y) (Z) [Nominal A X] :
  SupportedMap A (X × Y) Z ≃ SupportedMap A X (SupportedMap A Y Z)
```

No Nominal Y/Z, Nonempty or Infinite assumptions on these operations. Produce
`sectionsSupported_of_nominal`, `sectionsSupported_uncurry`,
`sectionsSupported_smul`, computation lemmas, `uncurry_curryWithSections`,
`curryWithSections_uncurry`, the nominal-domain inverse laws, `uncurry_injective`,
action compatibility and proof-witness independence. Use the explicit section
certificate on the right round trip rather than assuming X nominal.

Also define `sectionSubaction A X Y Z` using Mathlib SubMulAction with carrier
`{F | F.SectionsSupported}` and prove `admissibleCurryEquiv` from its carrier to
the curried supported carrier, with action compatibility. This is the exact
arbitrary-X correspondence in the spec, not a global arbitrary-subtype action.

For every finite S, export `supports_uncurry_iff` and
`supports_curryWithSections_iff`; general Set bounds follow from their
equivariant injective correspondence using Task 1. Derive `support_uncurry`,
`support_curryWithSections`, `support_curry` under Infinite A and
`support_curryAt_subset : support A (F.curryAt x hx) ⊆ support A F ∪ hx.support`.
Derive freshness preservation/equivalence from those exact equalities/bounds.

- [x] **1. Write `06Curry.lean`** testing computation, explicit-section inverse
  equations without Nominal X, nominal-domain convenience with arbitrary Y/Z,
  equivariance, exact support, nested ext, List.map of a section, and rewriting
  between different section proofs.
- [x] **2. Run before implementation** and confirm missing supported curry laws.
- [x] **3. Implement unconditional uncurry and curryAt** from evaluation and section
  bounds; prove uncurry injective by nested extensionality. Export their equations.
- [x] **4. Implement curryWithSections and both equivalences**. Obtain outer support
  by full curry plus reflection along the supported-section embedding, not a
  common bound on all individual sections. Prove stability under action and
  exact support before adding the nominal-domain convenience adapter.
- [x] **5. Complete boundary assertions**: projection `(p,x) ↦ p` is empty-supported,
  yet at an unsupported p its nonempty-domain section has no finite support.
  Use the concrete infinite/coinfinite atom subset from Task 4 for p. Conversely,
  a constant discrete-valued binary function has supported sections even on that
  non-nominal parameter carrier, and curryWithSections must accept it. Test an
  empty second domain too, where every section is supported without parameter
  evidence. Recheck the arbitrary-set complement-of-singleton counterexample.
- [x] **6. Build SupportedFunction and Package; run 06/07.** Print full signatures
  and axioms of curryWithSections, uncurry, both equivalences and exact support.
  Fail the task if proof convenience adds nominality or inhabitance assumptions.
- [x] **7. Reconcile article curry hypotheses/proof explanation and record F05c checkpoint.**

## Task 7: Public integration, manuscript and final review

**Files:** Package.lean, Package/Tests/AxiomAudit.lean, Package/README.md,
article entry point/sections, active roadmap, approved spec/plan and current
research records. Tests: all temporary consumers and `08PublicSignatures.lean`.

**Interfaces:** Consume the completed five modules; produce the public imported
foundation promised by the spec. Keep all audit/checker policies unchanged.

- [x] **1. Write `08PublicSignatures.lean`** assigning the headline declarations to
  the exact types in Tasks 1–6 with all action/universe parameters explicit.
  Include no-Infinite and no-Nominal consumers, a DivisionMonoid curry consumer,
  scalar-only support reflection, two atom sorts, and proofs using independently
  supplied support witnesses. Missing public exports must fail this check.
- [x] **2. Update the audit's representative prints** for ActionSupport transport/
  reflection, FunctionObject action/eval/curry, map/predicate correspondence,
  context/least support, bundle nominality/computation, admissible curry and
  exact support. Preserve the complete module-origin traversal, standard-axiom
  whitelist and zero-coverage rejection.
- [x] **3. Update Package/README.md** with actual names and a concise ordinary-input
  example, explicit context-bound construction, a returned supported section,
  and curry admission/empty-domain cautions. Explain explicit atom selection
  separately from support inference. Keep PKG-01 logic/descent and tooling deferred.
- [x] **4. Reconcile the article against final signatures**. Preserve the inspected
  Pitts/Urban/Swan sources and source-version distinctions. Add implementation
  correspondence only where now justified; no task/status/build material in LaTeX.
- [x] **5. Run integrated checks**, all requiring exit 0:

  ```sh
  lake build Package +Package.Tests.AxiomAudit
  lake env lean Package/Tests/AxiomAudit.lean
  python3 Package/Scripts/check-imports.py
  git diff --check
  ```

  Directly run all eight consumer files with `lake env lean`; report their
  actual results. The checker needs `--self-test` only if it was changed for a
  justified reason. Run latexmk from docs/article with a fresh output directory
  under `$PKG_F05_CHECKS/article`; inspect the final log for unresolved references
  and diagnostics. Compare baseline hashes/status to confirm unrelated work and
  dependency/reference sources are preserved. No clean dependency bootstrap is required.
- [x] **6. Obtain the review required by the selected execution method.** Native:
  one fresh independent read-only final review of the full F05 diff, contracts,
  consumers and article after validation. Subagent-driven: retain per-task
  reviews plus a fresh whole-change review. Fix confirmed issues within scope
  and rerun affected checks; no unrelated refactoring or extra review cycles.
- [x] **7. Reconcile every F05 acceptance row and phase checkbox** in the active
  roadmap, with commands actually run, axiom evidence, cache/rebuild conditions,
  review outcomes, temporary evidence path and uncommitted delivery status.
  Update current research/readiness summaries while retaining original evidence.
  Do not mark F06/PKG-01 complete. End with reviewable uncommitted changes.

## Plan self-review and handoff

Coverage: spec §§2–3 → Tasks 1–2; §4 including context bounds → Task 3;
§6 → Task 4; §5 → Tasks 5–6; §§7–9 → Task 7 and each task's article/checkpoint
step. All five Review Focus items have owning consumers. Empty constants,
sharp injectivity, unsupported sections, arbitrary sets and no-supported-choice
boundaries are assigned; no future public name is used without an owning task.
Signature tables are implementation contracts, not claims that declarations
already exist or that code snippets have been compiled during planning.

Selected execution method: **Native**, with the fresh independent final
review. The seven tasks share a narrow chain of type/action/coercion interfaces;
keeping their implementation in one context reduces repeated reconstruction.
Both review gates were explicitly approved before production edits. Leave the
implementation, this plan and approval records uncommitted.

## Execution record

Native execution evidence: `/tmp/nominal-package-f05-execution.dsh2fg3l/`.
The initial file hashes, progress ledger, RED/GREEN logs, eight public consumers,
README consumer, audit/build output and article PDF are retained there.
All seven tasks are complete. Integrated Package build (980 jobs), direct
production audit (573 declarations/14 defining modules, standard axioms only),
all eight public consumers and README consumer, import coverage (15+1) and
article compilation (33 pages, no diagnostics) pass. The independent final
review found no Critical, Important or Minor issues and independently checked
an additional two-atom-sort/same-carrier consumer. F05 is delivered uncommitted.

Recorded implementation decisions:

- Use the approved in-place checkout and temporary evidence directory; preserve
  all earlier dirty work and leave changes uncommitted, as explicitly requested.
- `FinitelySupportedMap` and `SupportedMap.SectionsSupported` are reducible
  aliases for their specified propositions. Literal existential/lambda evidence
  reproduced implicit-transparency failures under constructor/curry simp;
  focused RED/GREEN consumers justify this local choice. No mathematics changed,
  no existing support definition was modified and no global reducibility change
  was made. The tradeoff is intentionally visible unfolding of these proof aliases.


Final verification limits: project modules rebuilt as affected using cached
pinned dependencies; no clean dependency bootstrap or larger-client benchmark.
External Isabelle/Rocq builds and a complete re-audit of inherited bibliography
were not performed; principal Pitts/Urban comparisons were source-checked.
These limits were explicitly accepted as outside the delivery checks, not
silently counted as passing verification. There are no deferred review findings.
