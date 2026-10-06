# F04c Canonical Instances and Freshness Implementation Plan

**Historical plan with an approved follow-up:** the original five tasks below
are complete. The author subsequently approved general support-disjointness
freshness as a bounded extension and requested independent investigations of
other natural generalizations. That explicit instruction supersedes the
atom-only/no-binary-relation restriction in this original plan. Current types
and execution evidence are recorded in the specification's final section and
the active roadmap; the original plan signatures remain delivery history.

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking. Native execution with one fresh independent final review is already selected.

**Goal:** Deliver PKG-F04/F04c: canonical nominality certificates, exact support formulas, atom freshness and finite combined avoidance, with meaningful public-import consumers, audited proofs and matching LaTeX.

**Architecture:** Add Canonical.lean over the delivered Nominal module, then Freshness.lean over Canonical. Certify existing actions, prove exact support by both inclusions, and derive elementwise freshness before thin carrier adapters. Reuse Mathlib finite-set/infinite-type APIs and F04a/F04b throughout.

**Tech Stack:** Lean/Mathlib `v4.34.1`; Mathlib revision `d13f23b723b8a846827a245b89c10fc7d3f11612`; Lake, the existing Python import checker and module-origin axiom audit, LaTeX/latexmk.

**Spec:** [Approved F04c specification](../specs/2026-10-06-package-canonical-freshness-design.md). The author approved it on 2026-10-06. The author subsequently approved this written plan for native execution. Both approval gates are satisfied. All five tasks and integrated validation pass; independent final review findings are resolved. F04c is delivered, uncommitted.

## Global Constraints

- Work in `/home/fab/Documents/nominal/nominal` on `fasapa/nominal-package`. Planning inspected HEAD `68956dd23066c7c5c647345e5598b859ff97a10c`; F04a/F04b are committed there. Preserve the current uncommitted specification/tracker and all existing or subsequent tracked/untracked work.
- Do not commit, switch branches, push, publish, merge, change dependencies or add CI. Execute in the requested checkout; do not create a worktree or perform branch integration as a routine workflow step.
- Preserve `NominalPackage`, `Perm A`, independent universes, the pinned versions, the consumer's `Pointwise` scope and all existing action choices. New code belongs under `Package/`; preserve `Nominal/`, `Instances/`, existing examples and historical `docs/roadmap.md`.
- Reuse delivered `Supports`, `FinitelySupported`, proof-only `Nominal`, `hx.support` and `support A x`. Neither least-support construction, binary intersection nor conjugation transport is repeated. Preserve all five existing foundation modules.
- None of the four nominality certificates introduces a `MulAction` or requires `Infinite A`. Discrete data requires no action, equality or nominality of its underlying X. Product nominality uses `FinitelySupported.prod` and no atom equality.
- Finset's certificate is a proof theorem registered with `scoped[Pointwise] attribute [instance] NominalPackage.instNominalFinset`. Retain `DecidableEq A` for the existing image action. Other nominality instances have ordinary priority; add no priority override.
- Atom/discrete support formulas need only `Infinite A`. Visible product unions and the Finset action retain `DecidableEq A`. Each exact formula refers to the canonical action, and both inclusions must be proved.
- `hx.Fresh a` and `Fresh A a x` are the exact freshness interfaces; add no notation. Elementwise laws require no carrier-wide nominality. Carrier laws take A explicitly; Fresh has binder order A, X, action, infinitude, nominality, a, x.
- Generic freshness transport, product decomposition and existence add no `DecidableEq A`; classical equality stays inside proofs. Swaps retain decidable equality and have no endpoint-inequality premise.
- Preserve the exact definitions, arguments, names and simp attributes in the approved signatures below. Do not globally unfold support choice, freshness definitions, certificate bridges, quantified support or existence; inverse-image transport is a named rewrite, not a global simp rule.
- Use `Finset.exists_notMem` directly for explicit-set avoidance. Keep witness selection inside existential proofs; export no selector or claim of supported/equivariant selection.
- Allow only `propext`, `Classical.choice` and `Quot.sound` in audited dependencies. No `sorry`, `admit`, custom axioms, disabled kernel checking, weakened statements, broad reducibility changes or linter suppression.
- Temporary consumers import only `Package`; no standalone `Package/Examples` layer. Negative checks must verify the intended failure, and positive proofs must consume conclusions rather than prove True after a call.
- F04d owns quotient actions/support bounds. F05/PKG-01 own function objects, SupportsMap/SupportsPred, predicate bundles and Some/Any. Abstraction, FCB, recursion, generators, other containers and general binary freshness remain later work.
- Develop `docs/article/sections/freshness.tex`, with `sec:canonical-support` and `sec:freshness`, alongside Lean. Keep task IDs, approval/delivery narratives, commands, counts, cache conditions and review verdicts outside the manuscript.
- Root performs the native implementation, consumers, LaTeX and integration. Obtain one fresh independent final review after integrated validation. No per-task delegation or additional review gates are planned. Keep PKG-F04 open for F04d.

## Review Focus

- **Canonical actions versus arbitrary local actions:** a certificate must not certify an unrelated action on the same carrier. Task 1 checks explicit action parameters, ordinary action equations and guarded failures for replacement actions.
- **Assumption and universe leakage:** finite-atom nominality, arbitrary discrete data and generic freshness must not gain infinitude/equality/underlying-carrier assumptions. Tasks 1, 3 and 4 use independent universes and minimal contexts; Task 5 checks all exact signatures without a surrounding classical instance.
- **Evidence in a non-nominal carrier:** two proofs for the same element/action must agree, and supported pointwise constants must admit freshness without nominality of the function space. Tasks 2–4 retain the unsupported identity boundary and consume individual certificates.
- **Exact support versus a sufficient bound or strong support:** reverse containments, larger supplied bounds and unordered-pair symmetry are easy to confuse. Tasks 2 and 3 test actual least-support membership, strict larger bounds and both moved endpoints of a fixed pair.
- **Nested avoidance and renaming:** association, repeated contexts, inverse transport and coincident swap endpoints must compose predictably. Tasks 3 and 4 test both product associations, repeated components, separate transformed evidence, two successive fresh choices and resulting fixation.

## Files, ownership and task order

| File | Responsibility |
| --- | --- |
| `Package/Foundations/Canonical.lean` (new) | Tasks 1–2: canonical bounds/certificates and exact supports |
| `Package/Foundations/Freshness.lean` (new) | Tasks 3–4: evidence/carrier freshness, computation and existence |
| `Package.lean` | Tasks 1/3: explicitly export Canonical and Freshness after Nominal |
| `Package/Tests/AxiomAudit.lean` | Task 5: representative new prints; preserve complete module-origin traversal |
| `Package/README.md` | Task 5: actual calls, assumptions, scopes and boundaries |
| `docs/article/sections/freshness.tex` (new) | Tasks 1–4: concurrent mathematics; Task 5: final correspondence |
| `docs/article/main.tex`, `sections/introduction.tex` | Tasks 1–4: include the new section and reconcile abstract/scope |
| `docs/article/sections/foundations.tex`, `support.tex`, `perspectives.tex` | Focused cross-references and mathematical reconciliation |
| Active roadmap, approved spec and this plan | Approvals, executed steps, evidence and completion status |
| Research README, readiness and article-plan notes | Task 5: current-state reconciliation, preserving historical records |

Run **1 → 2 → 3 → 4 → 5**. Canonical imports only
`Package.Foundations.Nominal`; Freshness imports only
`Package.Foundations.Canonical`. Existing imports expose the needed Mathlib
APIs. No audit/checker policy, Lake, dependency or shared validation-script
change is expected.

Use `/tmp/nominal-f04c-execution/` for the execution snapshot, consuming Lean
files and logs. If it already exists, preserve it and choose a fresh suffixed
path, recording that substitution in commands. Every consumer uses namespace
`F04cChecks`, `set_option autoImplicit false`, independent universe variables
and only `import Package`. Keep classical equality and Pointwise local to the
specific assertions that need them.

Seven consumer files are assigned below: InstanceContracts, ActionCoherence,
CanonicalSupportContracts, BoundaryContracts, FreshnessContracts,
AvoidanceContracts and PublicSignatures. Table entries specify theorem names,
Lean assertions and necessary consumption; the implementer supplies proof
bodies without admissions. New-interface failures are observed before the
corresponding production declarations; existing-theory fixtures should already
pass. Task 5's article command is also used after each mathematical task.

## Task 1: Canonical finite support and nominality certificates

**Files:** Create Canonical.lean and freshness.tex; modify Package.lean,
main.tex and introduction.tex. Tests: InstanceContracts.lean and
ActionCoherence.lean in the execution directory.

**Interfaces:** Consume `Supports.finitelySupported`,
`Nominal.finitelySupported (A := A) x`, `FinitelySupported.prod`,
`supports_iff`, `supports_empty_iff`, `MulAction.supports_of_mem`, Finset
singleton/image laws and the delivered action equations. Produce exactly:

```lean
universe u v w

theorem supports_atom (A : Type u) (a : A) : Supports ({a} : Finset A) a

theorem supports_discrete (A : Type u) {X : Type v} (d : Discrete A X) :
    Supports (∅ : Finset A) d

instance instNominalAtom (A : Type u) : Nominal A A

instance instNominalDiscrete (A : Type u) (X : Type v) :
    Nominal A (Discrete A X)

instance instNominalProd (A : Type u) {X : Type v} {Y : Type w}
    [MulAction (Perm A) X] [MulAction (Perm A) Y]
    [Nominal A X] [Nominal A Y] : Nominal A (X × Y)

open scoped Pointwise

theorem supports_finset (A : Type u) [DecidableEq A] (S : Finset A) :
    Supports S S

theorem instNominalFinset (A : Type u) [DecidableEq A] : Nominal A (Finset A)

scoped[Pointwise] attribute [instance] NominalPackage.instNominalFinset
```

- [x] **Step 1: Record the execution baseline.** Read the approved spec and
  approved plan, recheck branch/HEAD/status, and snapshot/fingerprint every
  existing tracked/untracked file, including the uncommitted design documents.
  Use that snapshot for review, rather than attributing the full diff from HEAD
  to implementation. Run the baseline Package build, direct audit and import
  commands in Task 5; record actual cache conditions. Reuse the inspected API
  inventory unless source or pins changed.

- [x] **Step 2: Write InstanceContracts.lean.** Use the following assertions;
  no general `[Infinite A]` or `[DecidableEq A]` is present in the file context.

  | Name | Assertion and consumption |
  | --- | --- |
  | `atomCertificate` | For `a : A`, prove `FinitelySupported A a` from synthesized `Nominal A A` and its projection. |
  | `discreteCertificate` | For arbitrary `X : Type v` and `d : Discrete A X`, prove `FinitelySupported A d` using the new instance. X has no other instances. |
  | `productCertificate` | For selected component actions and `[Nominal A X] [Nominal A Y]`, prove `FinitelySupported A (x, y)` using product-instance synthesis. |
  | `finiteSetCertificate` | Under local Pointwise and `[DecidableEq A]`, prove `FinitelySupported A S` for `S : Finset A`; no infinitude. |
  | `atomBoundFixes`, `discreteBoundFixes`, `finiteSetBoundFixes` | Apply the three new `supports_*` results through `supports_iff`; conclude respectively `π • a = a` from `π a = a`, `π • d = d`, and `π • S = S` from `∀ a ∈ S, π a = a`. |
  | `finiteAndEmptyCarriers` | Consume nominality projections for Bool atoms, products of Bool atoms, and `Discrete A PEmpty.{v+1}`/`Discrete A PUnit.{v+1}`. Empty data is handled by a quantified d, with no invented inhabitant. |

- [x] **Step 3: Write ActionCoherence.lean.** Prove the six equations
  `π • a = π a`, `π • (x,y) = (π • x,π • y)`, `π • S = S.image π`,
  `π • (Discrete.mk d : Discrete A D) = Discrete.mk d`,
  `(π • σ : Perm A) = π * σ`, and `(π • f) x = π • f x`.
  Check coherent SMul/MulAction projections as in the retained F03a consumer.
  Guard the failure of Finset action synthesis before opening Pointwise and
  after closing a local Pointwise section; inside it synthesize both action
  and nominality and consume the latter. With an arbitrary explicit
  `act : MulAction (Perm A) C`, guard failure of `#synth @Nominal A C act`
  for C equal to A, Discrete A X, X × Y, and Finset A. For the product case
  provide nominal component actions, so failure specifically checks the
  unrelated product action. These are inference boundaries, not claims that
  those arbitrary actions are mathematically non-nominal.

- [x] **Step 4: Observe intended missing-interface failures.** Run
  `lake env lean /tmp/nominal-f04c-execution/InstanceContracts.lean` and
  the ActionCoherence command before creating Canonical.lean. Retain the
  missing-name/instance logs and separate them from fixture errors. Existing
  action equations and scope rejection should already pass; nominality
  consumers should fail only for the absent F04c instances/lemmas.

- [x] **Step 5: Draft canonical nominality in LaTeX.** Create freshness.tex
  with `sec:canonical-support`, explaining the four mathematical certificates
  and their finite bounds without infinitude. Describe arbitrary discrete data
  and the distinction between an action and a certificate. Include the file
  after support.tex and before perspectives.tex in main.tex; update the abstract
  and introduction to match this task's checked scope.

- [x] **Step 6: Implement Canonical.lean's first section.** Use the existing
  header/namespace conventions. Prove the atom bound by Mathlib support of a
  member and the discrete bound by empty-support invariance. For Finset, use
  `Perm.smul_finset`, `Finset.image_congr` and `image_id'` under Pointwise.
  Derive certificates with `.finitelySupported`; product nominality applies
  the delivered `.prod` to the class projections. Register only the Finset
  certificate with the scoped attribute. Export Canonical from Package.lean.

- [x] **Step 7: Verify the certificates and action boundaries.** Run
  `lake build +Package.Foundations.Canonical Package`, then both consumers.
  Require exit 0 with guarded negatives matching their intended diagnostics,
  no added atom/underlying-data assumptions and no new action instance.

- [x] **Step 8: Reconcile and compile the article.** Check this section's
  mathematical claims and assumptions against the checked bounds/certificates;
  run Task 5's latexmk command and resolve new diagnostics. Leave all changes
  uncommitted.

## Task 2: Exact canonical supports and their boundaries

**Files:** Extend Canonical.lean and freshness.tex; reconcile support.tex and
scope/cross-references as needed. Tests: CanonicalSupportContracts.lean and
BoundaryContracts.lean.

**Interfaces:** Consume Task 1's bounds/certificates, F04b support/minimality
and agreement, F04a `supports_prod`, `supports_prod_iff`,
`swap_smul_eq_of_supports`, and `Finset.exists_notMem`. Produce exactly:

```lean
universe u v w

@[simp] theorem support_atom (A : Type u) [Infinite A] (a : A) :
    support A a = {a}

@[simp] theorem support_discrete (A : Type u) [Infinite A]
    {X : Type v} (d : Discrete A X) : support A d = ∅

theorem FinitelySupported.support_prod {A : Type u} {X : Type v} {Y : Type w}
    [MulAction (Perm A) X] [MulAction (Perm A) Y]
    [Infinite A] [DecidableEq A] {x : X} {y : Y}
    (hx : FinitelySupported A x) (hy : FinitelySupported A y) :
    (hx.prod hy).support = hx.support ∪ hy.support

@[simp] theorem support_prod (A : Type u) {X : Type v} {Y : Type w}
    [MulAction (Perm A) X] [MulAction (Perm A) Y]
    [Infinite A] [DecidableEq A] [Nominal A X] [Nominal A Y]
    (x : X) (y : Y) : support A (x, y) = support A x ∪ support A y

open scoped Pointwise

@[simp] theorem support_finset (A : Type u) [Infinite A] [DecidableEq A]
    (S : Finset A) : support A S = S
```

- [x] **Step 1: Write CanonicalSupportContracts.lean.** Use these conclusions
  and the new formulas, rather than re-proving canonical supports in consumers.

  | Name | Assertion and consumption |
  | --- | --- |
  | `atomSingleton`, `discreteEmpty` | `support A a = {a}` and `support A (Discrete.mk d : Discrete A D) = ∅`; only `[Infinite A]`, no equality or underlying-D action. Also test arbitrary wrapped d. |
  | `productMemberIff` | `a ∈ support A (x,y) ↔ a ∈ support A x ∨ a ∈ support A y`, using `support_prod A x y` with independent component universes. Consume each implication. |
  | `individualProductExact` | `(hx.prod hy).support = hx.support ∪ hy.support`, using `.support_prod` with no carrier nominality. |
  | `independentProductEvidence` | For `hp : FinitelySupported A (x,y)`, prove `hp.support = hx.support ∪ hy.support` using certificate agreement and the elementwise formula. |
  | `finiteSetExact`, `finiteSetMembers` | `support A S = S`, then `a ∈ support A S ↔ a ∈ S`, consuming each membership direction under Pointwise. Include empty, singleton and nontrivial S. |
  | `canonicalEvidenceAgreement` | For supplied atom, discrete and Finset certificates, recover the same formulas using `support_eq A x hx`; add no duplicate production formulas. |

- [x] **Step 2: Write BoundaryContracts.lean.** Under Pointwise, prove the
  following exact approved consumer, using `support_finset A S` for both least
  support memberships, and the image/swap equations for fixation and movement:

```lean
theorem unordered_pair_boundary (A : Type u) [Infinite A] [DecidableEq A]
    (a b : A) (hab : a ≠ b) :
    let S : Finset A := {a, b}
    Perm.swap a b • S = S ∧
      a ∈ support A S ∧ b ∈ support A S ∧
      Perm.swap a b a ≠ a ∧ Perm.swap a b b ≠ b
```

  Retain `falseHasNoLeastSupport` from the checked F04b boundary source:
  both Bool singletons support false, their empty intersection does not,
  and no finite bound is least. Use new canonical `Nominal Bool Bool`
  synthesis rather than a new exported local certificate. Copy the relevant
  existing proofs into this public-import consumer; do not import scratch
  modules. Retain the supported pointwise constant, unsupported Nat identity
  and `¬ Nominal Nat (Nat → Nat)` conclusions. Guard failure of ordinary
  nominality synthesis for `Nat → Nat` and `Perm Nat`; no blanket certificate
  should appear. These tests do not redefine production actions.

- [x] **Step 3: Observe the formula failures.** Run both new consumers before
  adding the five formulas. Missing formula names are expected; isolate them
  from already passing finite-atom/action boundary proofs. Record the output.

- [x] **Step 4: Draft exact-support mathematics.** Extend
  `sec:canonical-support` with all four equations and both-inclusion proof
  ideas. Explain the fresh-swap reverse arguments for atoms and Finsets,
  projections for products, and the least empty bound for discrete data.
  Present the unordered-pair counterexample using its exact least support;
  cross-reference the existing Bool and setwise/pointwise distinctions.

- [x] **Step 5: Prove the five exact formulas.** For atoms, the singleton
  bound gives one inclusion; if a supporting T omits a, swap a with an atom
  outside `insert a T` to contradict support. Keep classical equality local.
  Discrete emptiness follows from `support_eq_empty_iff` or minimality of the
  empty bound. For products, prove the elementwise formula first: the union
  supports the pair, and a support of the pair supports both projections.
  Apply component minimality for the reverse inclusion, then derive the
  carrier formula by agreement. For Finset, S supports itself; if T supports
  S but omits `a ∈ S`, choose `b ∉ S ∪ T`. The outside swap fixes S while
  sending a to b, contradicting membership. Reuse existing support and swap
  results; add no pointwise-fixation converse.

- [x] **Step 6: Verify exactness and retained boundaries.** Run
  `lake build +Package.Foundations.Canonical Package`, followed by
  CanonicalSupportContracts, BoundaryContracts and InstanceContracts.
  Require exit 0 with both membership directions, the actual least-support
  counterexample and original assumptions intact. Action source remains unchanged.

- [x] **Step 7: Reconcile and compile the exposition.** Check the actual
  proof route, action and infinitude/equality distinctions, then compile with
  Task 5's article command and inspect the log. Do not claim freshness APIs
  as checked before Task 3.

## Task 3: Elementwise and carrier atom freshness

**Files:** Create Freshness.lean, export it from Package.lean, and extend
freshness.tex with `sec:freshness`. Reconcile introduction/abstract as needed.
Tests: FreshnessContracts.lean; extend BoundaryContracts.lean for constants.

**Interfaces:** Consume F04b support agreement/transport/minimality, Task 2
exact formulas, `swap_smul_eq_of_supports`, Finset image membership and
`notMem_union`. Produce these three approved blocks (separate contexts):

```lean
universe u v w
variable {A : Type u} {X : Type v}
variable [MulAction (Perm A) X] [Infinite A]
variable {x : X} {S : Finset A}

def FinitelySupported.Fresh (hx : FinitelySupported A x) (a : A) : Prop :=
  a ∉ hx.support

theorem FinitelySupported.fresh_iff_notMem_support
    (hx : FinitelySupported A x) (a : A) :
    hx.Fresh a ↔ a ∉ hx.support

theorem FinitelySupported.fresh_of_supports (hx : FinitelySupported A x)
    (hS : Supports S x) {a : A} (ha : a ∉ S) : hx.Fresh a

@[simp] theorem FinitelySupported.fresh_smul_iff
    (hx : FinitelySupported A x) (π : Perm A) (a : A) :
    (hx.smul π).Fresh (π a) ↔ hx.Fresh a

theorem FinitelySupported.fresh_smul_iff_inv
    (hx : FinitelySupported A x) (π : Perm A) (a : A) :
    (hx.smul π).Fresh a ↔ hx.Fresh (π⁻¹ a)

theorem FinitelySupported.swap_smul_eq_of_fresh [DecidableEq A]
    (hx : FinitelySupported A x) {a b : A}
    (ha : hx.Fresh a) (hb : hx.Fresh b) : Perm.swap a b • x = x

@[simp] theorem FinitelySupported.fresh_prod_iff
    {Y : Type w} [MulAction (Perm A) Y] {y : Y}
    (hx : FinitelySupported A x) (hy : FinitelySupported A y) (a : A) :
    (hx.prod hy).Fresh a ↔ hx.Fresh a ∧ hy.Fresh a
```

```lean
universe u v w
variable (A : Type u) {X : Type v}
variable [MulAction (Perm A) X] [Infinite A] [Nominal A X]

def Fresh (a : A) (x : X) : Prop :=
  (Nominal.finitelySupported (A := A) x).Fresh a

theorem fresh_iff_notMem_support (a : A) (x : X) :
    Fresh A a x ↔ a ∉ support A x

theorem fresh_iff (a : A) (x : X) (hx : FinitelySupported A x) :
    Fresh A a x ↔ hx.Fresh a

theorem fresh_of_supports {x : X} {S : Finset A}
    (hS : Supports S x) {a : A} (ha : a ∉ S) : Fresh A a x

@[simp] theorem fresh_smul_iff (π : Perm A) (a : A) (x : X) :
    Fresh A (π a) (π • x) ↔ Fresh A a x

theorem fresh_smul_iff_inv (π : Perm A) (a : A) (x : X) :
    Fresh A a (π • x) ↔ Fresh A (π⁻¹ a) x

theorem swap_smul_eq_of_fresh [DecidableEq A] {x : X} {a b : A}
    (ha : Fresh A a x) (hb : Fresh A b x) : Perm.swap a b • x = x

@[simp] theorem fresh_prod_iff {Y : Type w}
    [MulAction (Perm A) Y] [Nominal A Y] (a : A) (x : X) (y : Y) :
    Fresh A a (x, y) ↔ Fresh A a x ∧ Fresh A a y
```

```lean
universe u v

@[simp] theorem fresh_atom_iff (A : Type u) [Infinite A] (a b : A) :
    Fresh A a b ↔ a ≠ b

@[simp] theorem fresh_discrete (A : Type u) [Infinite A]
    {X : Type v} (a : A) (d : Discrete A X) : Fresh A a d

open scoped Pointwise

@[simp] theorem fresh_finset_iff (A : Type u) [Infinite A] [DecidableEq A]
    (a : A) (S : Finset A) : Fresh A a S ↔ a ∉ S
```

- [x] **Step 1: Write FreshnessContracts.lean.** Generic assertions have
  `[Infinite A]` and selected actions but no decidable equality or Pointwise.
  Introduce those only for swaps or a Finset context. Use these named tests:

  | Name | Assertion and required use |
  | --- | --- |
  | `evidenceNonmembership`, `carrierNonmembership` | Derive both directions between freshness and `a ∉ hx.support` / `a ∉ support A x` through the definition lemmas. |
  | `boundFresh`, `carrierBoundFresh` | From arbitrary `hS : Supports S x` and `a ∉ S`, conclude `hx.Fresh a` / `Fresh A a x` using the new bound laws. |
  | `transportForward`, `transportBack` | From `hx.Fresh a` conclude `(hx.smul π).Fresh (π a)`, and conversely, using opposite directions of `.fresh_smul_iff`. Repeat for carrier freshness. |
  | `inverseTransport`, `otherTransportEvidence` | Use `.fresh_smul_iff_inv` and its carrier form; for arbitrary `hπx : FinitelySupported A (π • x)`, prove `hπx.Fresh a ↔ hx.Fresh (π⁻¹ a)` by evidence agreement. |
  | `evidenceIndependence`, `carrierAgreement` | Prove `hx.Fresh a ↔ hx'.Fresh a` and `Fresh A a x ↔ hx.Fresh a`; use the named bridge without unfolding support choice. |
  | `nominalityIndependence` | For fixed act/inf and `n₁ n₂ : @Nominal A X act`, prove `@Fresh A X act inf n₁ a x ↔ @Fresh A X act inf n₂ a x`. |
  | `twoAtomParameters` | On X carrying both A/B actions and nominality, consume the two definition lemmas to obtain `(Fresh A a x ↔ a ∉ support A x) ∧ (Fresh B b x ↔ b ∉ support B x)` with independent universes. |
  | `freshSwapFixes`, `equalEndpointSwap` | From two fresh endpoints conclude `Perm.swap a b • x = x`; use the new law explicitly also with a = b and the same freshness proof twice. Test both evidence and carrier forms. |
  | `atomComputation`, `discreteComputation`, `finsetComputation` | Consume `Fresh A a b ↔ a ≠ b`, freshness for arbitrary discrete d, and `Fresh A a S ↔ a ∉ S`. In particular prove freshness for `Discrete.mk a` and nonfreshness of the atom a itself. |
  | `individualNestedDecomposition` | `(hx.prod (hy.prod hz)).Fresh a ↔ hx.Fresh a ∧ hy.Fresh a ∧ hz.Fresh a`, with no nominality or equality. Test the other association and the repeated context `(hx.prod hx)`. |
  | `nestedDecomposition` | `Fresh A a (x,(y,(S,(Discrete.mk d : Discrete A D)))) ↔ Fresh A a x ∧ Fresh A a y ∧ a ∉ S`; use only the directed computation/decomposition rules, with no underlying-D action. Test both implications and both product associations. |
  | `finiteSetAvoidance` | `Fresh A a (insert b (S ∪ T)) ↔ a ≠ b ∧ a ∉ S ∧ a ∉ T`, using Finset computation and ordinary membership laws. |

- [x] **Step 2: Add bound/evidence boundary consumers.** In
  FreshnessContracts, `largerBoundFixes` uses the sufficient bound `{b}` for
  discrete d, proves `support A d ⊂ {b}`, obtains freshness of endpoints
  outside `{b}`, and uses it to fix d by their swap. In BoundaryContracts,
  `constantFunctionFresh` uses the previously proved singleton support of
  `fun _ : Nat => c` to conclude freshness of every `a ≠ c`. Derive a
  fresh-swap fixation of that function from the new elementwise laws, while
  retaining `¬ Nominal Nat (Nat → Nat)`.

- [x] **Step 3: Observe the intended missing-freshness failures.** Run
  FreshnessContracts and the extended BoundaryContracts before adding
  Freshness.lean. Record missing F04c names independently of fixture errors.

- [x] **Step 4: Draft the freshness section.** Add `sec:freshness` to
  freshness.tex: least-support nonmembership, evidence/carrier agreement,
  sufficient bounds, simultaneous and inverse transport, fresh-swap fixation
  including equal endpoints, and canonical/nested-product decomposition.
  Explain proof-local classical equality and reuse of the preceding support
  results. Update abstract/introduction and relevant cross-references.

- [x] **Step 5: Implement elementwise freshness and laws.** Freshness.lean
  imports Canonical. Define `.Fresh` exactly as specified and prove its
  definition lemma. Bound freshness uses `.support_minimal`; transport uses
  local classical equality, `.support_smul` and the existing image membership
  iff. Obtain inverse-image transport by inverse cancellation. Fresh-swap
  fixation applies the delivered sufficient-bound theorem to
  `hx.supports_support`. Product decomposition applies `.support_prod` and
  `Finset.notMem_union`, again with equality only inside the proof.

- [x] **Step 6: Implement carrier adapters and computation.** Define Fresh
  with the specified class-projection body and binder order, prove agreement
  for arbitrary hx, and derive carrier laws from the elementwise ones.
  Derive canonical freshness from the exact support formulas. Add exactly
  the approved simp attributes and export Freshness from Package.lean.

- [x] **Step 7: Verify the freshness interface.** Run
  `lake build +Package.Foundations.Freshness Package`, then
  FreshnessContracts, BoundaryContracts and CanonicalSupportContracts.
  Require exit 0, including generic no-equality proofs, separate transformed
  certificates, equal-endpoint swaps and nested simplification. Resolve
  inference issues locally without changing the approved statements.

- [x] **Step 8: Reconcile and compile the exposition.** Match the checked
  names, definitions, action/certificate distinctions and proof dependencies;
  compile with Task 5's command and resolve new manuscript diagnostics.

## Task 4: Fresh existence and combined avoidance

**Files:** Extend Freshness.lean and freshness.tex; reconcile related scope
text as needed. Test: AvoidanceContracts.lean.

**Interfaces:** Consume `Finset.exists_notMem`, the two freshness definitions,
Task 3 product/canonical decomposition and swap fixation. Produce exactly:

```lean
universe u v
variable {A : Type u} {X : Type v}
variable [MulAction (Perm A) X] [Infinite A] {x : X}

theorem FinitelySupported.exists_fresh (hx : FinitelySupported A x) :
    ∃ a : A, hx.Fresh a

theorem FinitelySupported.exists_fresh_notMem
    (hx : FinitelySupported A x) (S : Finset A) :
    ∃ a : A, a ∉ S ∧ hx.Fresh a

variable (A) [Nominal A X]

theorem exists_fresh (x : X) : ∃ a : A, Fresh A a x

theorem exists_fresh_notMem (S : Finset A) (x : X) :
    ∃ a : A, a ∉ S ∧ Fresh A a x
```

- [x] **Step 1: Write AvoidanceContracts.lean.** Keep explicit finite exclusion
  bounds separate from Finset values used as nominal context components.

  | Name | Assertion and required use |
  | --- | --- |
  | `explicitFiniteAvoidance` | For `[Infinite A]` and `S : Finset A`, obtain `∃ a, a ∉ S` directly from `Finset.exists_notMem S`, without an action or equality premise. |
  | `individualFreshWitness`, `carrierFreshWitness` | Consume the two `exists_fresh` laws, eliminate the witnesses and conclude `∃ a, a ∉ hx.support` / `∃ a, a ∉ support A x`. |
  | `individualNestedAvoidance` | Using `(hx.prod (hy.prod hz)).exists_fresh_notMem S`, prove `∃ a, a ∉ S ∧ hx.Fresh a ∧ hy.Fresh a ∧ hz.Fresh a`. No carrier nominality, equality or Pointwise. |
  | `carrierAvoidance` | Consume `exists_fresh_notMem A S x` to obtain `∃ a, a ∉ S ∧ a ∉ support A x`, without equality. |
  | `nestedContextAvoidance` | Apply carrier existence to `(x,(y,(T,(Discrete.mk d : Discrete A D))))`, and derive `∃ a, a ∉ S ∧ Fresh A a x ∧ Fresh A a y ∧ a ∉ T`. Finset context T uses equality/Pointwise; D has no action requirement. |
  | `twoFreshSwapFixes` | Prove `∃ a b, a ∉ S ∧ b ∉ S ∧ a ≠ b ∧ Fresh A a x ∧ Fresh A b x ∧ Perm.swap a b • x = x`: choose a outside S, then b outside `insert a S`, and consume fresh-swap fixation. Add equality only for swaps/insert. |
  | `individualTwoFreshSwapFixes` | The same conclusion with `hx.Fresh` and no nominality, using the elementwise existence and swap laws. |
  | `twoFreshNestedSwapFixes` | Make the two choices for the nested context above; obtain nonmembership in S and T, freshness for x/y, and fixation of the whole context and each of x/y by the resulting swap. |

- [x] **Step 2: Observe the intended existence failures.** Run
  `lake env lean /tmp/nominal-f04c-execution/AvoidanceContracts.lean`
  before adding the four laws. Direct explicit-set avoidance should pass;
  new context-existence calls should fail on missing declarations.

- [x] **Step 3: Draft existence and combined avoidance.** Extend
  `sec:freshness` with the finite-union existence proof, explicit-set versus
  supported-context avoidance, a nested-product example and successive fresh
  choices producing swap fixation. State infinitude and the separation from
  any algorithm or equivariant/supported fresh selector.

- [x] **Step 4: Implement the four existence laws.** For `.exists_fresh`,
  apply `Finset.exists_notMem` to `hx.support`. For `.exists_fresh_notMem`,
  choose outside `S ∪ hx.support` with local classical equality and decompose
  nonmembership. Derive the carrier wrappers through the class projection
  and agreement. Add no alias for Mathlib's explicit-set theorem and no
  container-specific existence theorem or data-valued selector.

- [x] **Step 5: Verify meaningful avoidance.** Run
  `lake build +Package.Foundations.Freshness Package`, then AvoidanceContracts
  and FreshnessContracts. Require exit 0 with actual witness nonmembership,
  nested freshness, distinct successive choices and resulting swap fixation.

- [x] **Step 6: Reconcile and compile the exposition.** Check that context
  hypotheses and existence claims match the four implemented statements and
  their consumers. Compile with Task 5's command and inspect the final log.

## Task 5: Integrated acceptance, audit, documentation and final review

**Files:** Modify audit, Package README, active roadmap, approved spec/plan
and the research guide/readiness/article-plan notes. Reconcile the affected
article files. Test: PublicSignatures.lean plus all six preceding consumers.

**Interfaces:** Consume all **34** approved production declarations above.
Produce complete coverage of eight production source modules including the
root and one audit module; measure defining-module, declaration and job counts.
The unordered-pair theorem is a temporary consumer, not a 35th production API.

- [x] **Step 1: Check every exact signature and action boundary.** In
  PublicSignatures, assign all 34 public constants their approved types;
  inspect fully explicit `@` signatures and universe/binder output. Check
  absence of unnecessary equality/infinitude/nominality premises without
  installing classical instances around the checks. Verify Fresh's prescribed
  binder order, canonical concrete action arguments and scoped Finset instance
  registration. Rerun ActionCoherence after both modules are exported.

- [x] **Step 2: Extend representative audit output.** Add qualified
  `#print axioms` for all four certificates and five exact-support results,
  `FinitelySupported.Fresh`, `.fresh_of_supports`, `.fresh_smul_iff`,
  `.fresh_smul_iff_inv`, `.fresh_prod_iff`, `.swap_smul_eq_of_fresh`,
  `.exists_fresh`, `.exists_fresh_notMem`, `Fresh`, `fresh_iff` and
  `exists_fresh_notMem`. Preserve the module-origin traversal, private/generated
  coverage, zero-coverage rejection and exact standard-axiom allowlist.

- [x] **Step 3: Run integrated Lean checks after the final production edit.**
  Execute and inspect each result:
  ```sh
  lake build Package +Package.Tests.AxiomAudit
  lake env lean Package/Foundations/Canonical.lean
  lake env lean Package/Foundations/Freshness.lean
  lake env lean /tmp/nominal-f04c-execution/InstanceContracts.lean
  lake env lean /tmp/nominal-f04c-execution/ActionCoherence.lean
  lake env lean /tmp/nominal-f04c-execution/CanonicalSupportContracts.lean
  lake env lean /tmp/nominal-f04c-execution/BoundaryContracts.lean
  lake env lean /tmp/nominal-f04c-execution/FreshnessContracts.lean
  lake env lean /tmp/nominal-f04c-execution/AvoidanceContracts.lean
  lake env lean /tmp/nominal-f04c-execution/PublicSignatures.lean
  lake env lean Package/Tests/AxiomAudit.lean
  python3 Package/Scripts/check-imports.py
  ```
  Require exit 0, both new modules reached and only allowed axioms; resolve
  new diagnostics. Recheck retained F03a ActionContracts/NegativeContracts and
  F04b BoundaryContracts when available. If the checker changes, also run
  `python3 Package/Scripts/check-imports.py --self-test`. Record cache conditions;
  a cached audit module is supplemented by the direct traversal above.

- [x] **Step 4: Reconcile public documentation and mathematical claims.**
  Update Package/README.md with checked names/calls, minimal assumptions,
  Pointwise policy and evidence/carrier agreement. Update current research
  guide/readiness/article-plan paragraphs and the active tracker, preserving
  dated evidence and F04d/F05 boundaries. Compare article assumptions, proof
  ideas, selected declarations and limitations against actual source. Keep
  operational evidence in the tracker/plan rather than the manuscript.

- [x] **Step 5: Compile and inspect the final article.** From docs/article/:
  ```sh
  latexmk -pdf -interaction=nonstopmode -halt-on-error \
    -outdir=/tmp/nominal-package-article-build main.tex
  ```
  Create that output directory if needed; keep all generated files outside
  the source tree. Require successful compilation, resolved references and
  no unexplained new layout diagnostics. Inspect the canonical-support and
  freshness text separately for mathematical correspondence. Record whether
  the invocation rebuilt or reused existing outputs.

- [x] **Step 6: Check preservation and record evidence.** Compare all
  tracked/untracked files against the execution snapshot, including subsequent
  edits. Preserve the five delivered foundation modules, reference sources,
  historical roadmap, pins and unrelated work. Check document links/anchors,
  fences, all changed/untracked whitespace and `git diff --check`. If shared
  integration changes affect reference targets, separately run
  `lake build Nominal Instances Examples`,
  `lake env lean Examples/AxiomAudit.lean` and
  `python3 scripts/check-imports.py`; otherwise report source preservation
  without claiming a reference rebuild. Record actual commands, counts,
  cached/fresh-build limits and the execution diff; keep completion pending review.

- [x] **Step 7: Obtain one fresh independent final review.** Give one read-only
  reviewer the approved spec/plan, implementation diff against the execution
  snapshot, final sources including untracked files, seven consumers, baseline
  and integrated validation evidence, and the article. Request review of all
  five Review Focus items, both inclusions, exact hypotheses/signatures,
  meaningful counterexamples, scope/instance coherence, manuscript mathematics
  and preservation. Resolve findings natively and rerun affected checks.
  Mark F04c DONE only after code, consumers, audit, article and this review
  pass; keep PKG-F04 open for F04d. Leave all work uncommitted.

## Planning self-review and approval handoff

Task 1 owns canonical finite supportedness, nominality and action isolation.
Task 2 owns exact support, finite-atom/non-nominal boundaries and the unordered
pair. Task 3 owns evidence/carrier freshness, agreement, transport, swaps and
canonical/nested decomposition. Task 4 owns fresh existence and combined
avoidance. Task 5 owns all-signature/public-boundary validation, complete audit,
documentation, final article correspondence and one independent final review.
Each mathematical task includes concurrent LaTeX drafting and compilation.
All five Review Focus items have explicit consuming checks.

At plan approval, the seven Lean interface blocks were copied unchanged from
the specification, including the temporary unordered-pair contract. This plan
introduces no new production API or mathematical hypothesis. Self-review checks
coverage, step specificity, type/argument consistency, scope and proportion.
Consumer assertions are execution-time obligations, not already checked F04c
proofs. No production or article source has changed during planning.

**Written-plan approval and native execution are granted.** Use executing-plans in
this checkout, in task order; do not repeat specification approval or ask which
execution method or task to choose. The design-session builds/audits/article
checks remain historical to this planning turn. Planning validation is limited
to document consistency and preservation.

Planning checks confirm all seven Lean blocks match the approved specification
byte-for-byte and all 34 production declarations are assigned, with the
unordered-pair theorem retained as a temporary consumer. File comparison
preserves 116 of 118 existing files: only specification approval/status and
the active tracker changed, alongside this new plan. Branch/HEAD, historical
work log, Lean/article sources, reference code and dependency pins are preserved.
Document checks and fingerprints are under `/tmp/nominal-f04c-plan-d1f0h4eo/`.
No Lean build, audit or manuscript compilation was rerun during planning.

## Native execution evidence

Tasks 1–4 followed the consumer-first sequence. The new assertions failed on
missing interfaces before implementation, then passed after their code was
added. Fixture corrections preserved their conclusions: a namespace opening,
explicit conjunction construction, elimination of a redundant proof-irrelevant
rewrite, and specialized certificate-product rewrite arguments. Carrier-product
simp remains automatic. The LaTeX was developed and compiled with each task;
two long displays/headings were shortened without changing the mathematics.

**Recorded implementation adjustment:** the scoped Finset certificate uses a
proof theorem in place of the proposed def, with a fully qualified scoped
attribute. Pinned Lean's warnings/name resolution motivated the change. Its
public name/type/assumptions and scoped instance behavior are unchanged;
no linter, priority or reducibility setting was changed. The current interface
blocks reflect this declaration-kind correction.

The integrated 972-job Package build, direct Canonical/Freshness checks, all
seven temporary consumers, direct audit, import coverage and retained F03a
action/negative and F04b boundary consumers pass. The direct audit checks
178 production declarations from seven defining modules with only standard
axioms; coverage reaches eight production source modules and one audit.
The article has 20 pages and a clean final log. Dependencies were cached,
and changed project artifacts were rebuilt incrementally. No fresh full-project
build, dependency bootstrap or unchanged reference-library rebuild is claimed.

Execution snapshots, the progress ledger, commands and red/green logs are in
`/tmp/nominal-f04c-execution/`. Preserve them: the approved workflow leaves
changes uncommitted. Task 5 and the final independent review are complete.
The review found no Critical/Important issues and two Minors: stale tracker
wording and a Finset isolation guard tested without its scoped certificate
active. Both were corrected; the amended ActionCoherence consumer and document
checks pass. The reviewer independently ran all code/consumer/audit/coverage
checks and a fresh 20-page article build. Its report is retained under
`/tmp/nominal-f04c-review-V2nE2A/`. No second review or production proof change
was needed. PKG-F04 remains open for F04d.

The subsequent general-freshness extension uses the same supported modules and
validation policy. `Fresh` is now heterogeneous support disjointness, with
`hx.FreshWith hy` for two individual certificates and the old atom interface
derived from it. Eight public-import consumers, the 972-job build, direct
226-declaration audit and 8+1 import coverage pass. The article has 21 pages.
Four independent-research probes were retained under docs/research/probes and
rerun; their other proposals remain outside production imports. No original
F04c evidence was overwritten. Follow-up independent review found no Critical
or Important issues; its one minor article proof-description finding was
corrected and rechecked. The follow-up is complete, with no deferred findings
or additional foundation implementation. The report is retained at
`/tmp/nominal-final-review-Xr59FA/review.md`.
