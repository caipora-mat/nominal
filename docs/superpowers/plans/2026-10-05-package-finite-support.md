# F04a Finite Support Implementation Plan

**Article editorial correction:** manuscript passages follow the current
[research-article policy](../../research/2026-10-05-article-plan.md): selected
system/mathematical exposition and substantive comparisons, with no task IDs
or development/review/build diary. Article instructions below are amended
accordingly; the recorded execution history remains an internal record.

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking. The author approved the plan and selected native execution.

**Goal:** Deliver F04a of PKG-F04: finite support calculus for selected permutation actions, with meaningful consumers, an axiom audit and matching LaTeX exposition.

**Architecture:** Specialize Mathlib's `MulAction.Supports` to finite atom bounds in one new foundation module. Reuse F03b for the swap characterization, prove permutation transport by conjugation, and prove finite intersection using a spare atom. Preserve the permutation representation and all selected action instances.

**Tech Stack:** Lean/Mathlib 4.34.1; Mathlib revision `d13f23b723b8a846827a245b89c10fc7d3f11612`; Lake, the existing Python import checker and module-origin axiom audit, LaTeX/latexmk.

**Spec:** [Approved F04a specification](../specs/2026-10-05-package-finite-support-design.md). The author approved the written specification on 2026-10-05, then approved this plan by selecting native execution. Planning and execution checkout: `fasapa/nominal-package`, HEAD `34a83358739ab962e2b9d2035a21d67b2a896071`, with the preceding uncommitted F04a design documents preserved.

**Delivery:** All four tasks are complete. F04a is verified in the working tree,
with a clean independent final review and matching compiled article. All changes
remain uncommitted; PKG-F04 remains open for F04b–F04d.

## Global Constraints

- Preserve `NominalPackage`, `Perm A`, independent atom/carrier universes, the delivered F02/F03a/F03b interfaces and all existing action choices.
- New production code belongs under `Package/` and uses pinned Mathlib directly. Existing `Nominal/` and `Instances/` are optional references, not imports or API constraints.
- The historical `docs/roadmap.md` remains unchanged. Use PKG-F04/F04a and PKG-11 in the active `docs/nominal-package-roadmap.md`.
- No branch switch, commit, push, merge, publication, dependency upgrade or CI change is authorized. Work in the current checkout; preserve tracked and untracked work, including this plan and the approved spec.
- Lean is pinned to `v4.34.1`. Retain the Mathlib revision above, `lakefile.toml`, `lake-manifest.json`, current default targets, checker and old validation scripts.
- Persistent usage examples remain reserved for case studies; acceptance consumers will be temporary public-import files. Do not create a `Package/Examples` layer.
- Definitions/basic laws and existential closure require neither `DecidableEq A` nor `Infinite A`. Exposed finite-set union/image/intersection and swaps retain `DecidableEq A`; only `supports_inter` requires `Infinite A`.
- No carrier-wide supportedness, countability, nonemptiness or commuting-action assumption may be added. Use local classical equality inside proof-only existential witness construction.
- This supplies F04b's least-support construction and later equivariant clients without introducing nominality, least support, freshness, quotients, predicate bundles or another function-space action in this increment.
- No `sorry`, `admit`, custom axioms, disabled kernel checking or weakened statements. Only standard `propext`, `Classical.choice`, `Quot.sound` may occur in the audit.
- Do not mark the quantified `supports_iff` or `supports_iff_swap` expansions as global simp rules. Preserve instance/reducibility/linter policies.
- All manuscript writing remains LaTeX under `docs/article/`. Draft with the proofs and reconcile/compile before delivery; generated files stay outside the source tree.
- F04a completion does not complete PKG-F04 or authorize F04b–F04d. The prior F02/F03 approvals and completed results stand.

## Review Focus

- **Independent universes and explicit atom selection:** unrelated `A : Type u`, `X : Type v`, `Y : Type w` and nested products must work without atom `outParam` inference. Task 1's generic and nested-product consumers, then Task 4's signature checks, cover this.
- **Assumption leakage:** finite supportedness transport/product statements must remain usable without decidable equality; empty/singleton atom carriers must not acquire an infinitude requirement. Tasks 1/2 test these cases without those local instances.
- **Noncommuting actions:** Mathlib's commuting-action support lemma must not restrict transport. Task 2 combines transported singleton support with an explicit noncommuting three-atom calculation.
- **Least bounds versus sufficient bounds:** product equivalence is exact for a common bound; unions and equivariant images are sufficient bounds. Task 1 proves that a constant discrete image has both an inherited singleton bound and the strictly smaller empty bound.
- **Finite atoms and equal endpoints:** intersection needs its infinitude premise; swaps permit equal endpoints. Task 2 checks reflexive swaps; Task 3 proves both Bool singleton supports and failure of their intersection.

## Files, ownership and order

| File | Responsibility |
| --- | --- |
| `Package/Foundations/Support.lean` (new) | Tasks 1–3: definitions, support laws, transport, swap specialization and intersection |
| `Package.lean` | Task 1: explicitly export Support after the existing foundation imports |
| `Package/Tests/AxiomAudit.lean` | Task 4: representative prints; retain the existing whole-production traversal |
| `Package/README.md` | Task 4: actual API, assumptions and delivered boundary |
| `docs/article/sections/support.tex` (new) | Tasks 1–3: selected definitions/results/proof ideas; Task 4: mathematical correspondence |
| `docs/article/main.tex` | Task 1: include support section; Task 4: reconcile title/abstract/scope |
| `docs/article/sections/introduction.tex`, `docs/article/sections/foundations.tex` | Tasks 1–3: maintain accurate mathematical scope; Task 4: reconcile the scientific exposition |
| `docs/nominal-package-roadmap.md`, this plan and its specification | Record approvals, completed steps and actual F04a/PKG-11 evidence |
| `docs/research/README.md`, `docs/research/2026-10-05-pkg01-readiness.md`, `docs/research/2026-10-05-article-plan.md` | Task 4: reconcile delivered F04a and remaining F04b–F04d/F05/PKG-01 |

Run **1 → 2 → 3 → 4**. Tasks 1–3 share Support.lean and depend on the preceding
interfaces. Recommended native execution has root own Lean, temporary consumers
and trackers. An article worker may own the LaTeX files exclusively during a
task, with root reconciling its output before that task finishes. A fresh final
reviewer checks the whole increment after validation. If subagent-driven
execution is selected instead, dispatch these tasks sequentially with their
spec/plan context and review each before moving on; never overlap edits.

Temporary consumers use `/tmp/nominal-f04a-execution/`, namespace `F04aChecks`,
and only `import Package`. If that directory already exists, preserve it and
use a fresh suffixed directory, recording the actual path. Names below are
consumer assertions to prove, not a request for persistent testing infrastructure.
No consumer may introduce an admission, axiom or body that merely proves `True`.

## Task 1: Finite bounds and supported elements

**Files:** Create Support.lean and support.tex; modify Package.lean and the
article entry point/scope paragraphs. Temporary test: `BasicContracts.lean`.

**Interfaces:** Consume existing `Equivariant A f`, componentwise product and
explicit `Discrete` actions, plus Mathlib `MulAction.Supports`,
`MulAction.Supports.mono` and `MulAction.supports_of_mem`. Produce the following
signatures in `NominalPackage`, with independent `u v w`:

```lean
abbrev Supports {A : Type u} {X : Type v}
    [MulAction (Perm A) X] (S : Finset A) (x : X) : Prop :=
  MulAction.Supports (Perm A) (S : Set A) x
def FinitelySupported (A : Type u) {X : Type v}
    [MulAction (Perm A) X] (x : X) : Prop :=
  ∃ S : Finset A, Supports S x

variable {A : Type u} {X : Type v} {Y : Type w}
variable [MulAction (Perm A) X] [MulAction (Perm A) Y]
variable {S T : Finset A} {x : X} {y : Y} {f : X → Y}

theorem supports_iff (S : Finset A) (x : X) :
    Supports S x ↔ ∀ π : Perm A, (∀ a ∈ S, π a = a) → π • x = x
theorem supports_mono (hST : S ⊆ T) (hS : Supports S x) : Supports T x
theorem supports_empty_iff (x : X) :
    Supports (∅ : Finset A) x ↔ ∀ π : Perm A, π • x = x
theorem supports_map (hf : Equivariant A f) (hS : Supports S x) :
    Supports S (f x)
theorem supports_prod_iff (S : Finset A) (x : X) (y : Y) :
    Supports S (x, y) ↔ Supports S x ∧ Supports S y
theorem Supports.finitelySupported (hS : Supports S x) : FinitelySupported A x
theorem FinitelySupported.map (hx : FinitelySupported A x)
    (hf : Equivariant A f) : FinitelySupported A (f x)
theorem FinitelySupported.prod (hx : FinitelySupported A x)
    (hy : FinitelySupported A y) : FinitelySupported A (x, y)

-- Only this bound statement adds decidable equality.
theorem supports_prod [DecidableEq A] (hS : Supports S x) (hT : Supports T y) :
    Supports (S ∪ T) (x, y)
```

- [x] **Step 1: Record the execution baseline.** Read spec/plan, recheck
  branch/HEAD/status, hash existing tracked and untracked files and record the
  actual scratch directory. Preserve all preceding design work. Confirm that
  Support.lean is still absent; if new work is present, inspect and integrate
  it without overwriting it. Reuse the already inspected pinned APIs.

- [x] **Step 2: Write the basic public-import consumers.** In BasicContracts,
  prove the named assertions below with the new interfaces. Keep generic
  sections free of `DecidableEq`/`Infinite` unless specified, and use fully
  qualified `NominalPackage.Supports` where necessary to avoid Mathlib ambiguity.

  | Name | Assertion and required consumption |
  | --- | --- |
  | `mathlibSupportBoundary` | From `h : MulAction.Supports (Perm A) (S : Set A) x`, obtain `Supports S x`, and conversely, by definitional conversion |
  | `fixesEnlargedImage` | `hf : Equivariant A f`, `hS : Supports S x`, `hST : S ⊆ T`, `hfix : ∀ a ∈ T, π a = a` imply `π • f x = f x`; consume `supports_mono`, `supports_map`, and `supports_iff` |
  | `supportFromPointwise` | The explicit pointwise-fixer premise from `supports_iff` yields `Supports S x` via its reverse direction |
  | `emptyBound` | Prove `(∀ π : Perm A, π • x = x) ↔ Supports (∅ : Finset A) x` using both directions of `supports_empty_iff` |
  | `commonProductBound` | Consume each direction of `Supports S (x,y) ↔ Supports S x ∧ Supports S y`; use the resulting component bounds to prove component fixation by π |
  | `nestedProductBound` | With `[DecidableEq A]` and supports S/T/U for x/y/z, obtain `Supports ((S ∪ T) ∪ U) ((x,y),z)` via two uses of `supports_prod`; keep all four universes independent |
  | `existentialClosure` | From support bounds, obtain finite supportedness using `Supports.finitelySupported`; from `hx : FinitelySupported A x`, `hy : FinitelySupported A y`, `hf : Equivariant A f`, conclude `FinitelySupported A (f x,y)` using `.map` and `.prod`, with no equality instance |
  | `constantImageSmallerBound` | For `f := fun _ : A => (Discrete.mk true : Discrete A Bool)` and any a, obtain `Supports ({a} : Finset A) (f a)` via `supports_map` and atom membership support, also prove `Supports (∅ : Finset A) (f a)` and `(∅ : Finset A) ⊂ {a}` |
  | `emptyAtomsInvariant`, `singletonAtomsInvariant` | For arbitrary selected actions of `Perm PEmpty.{u+1}` and `Perm (Fin 1)` respectively, prove empty support and consume it to conclude `∀ π, π • x = x`; prove each permutation is identity by extensionality |

  A representative assertion should use the new facts as follows:
  ```lean
  theorem fixesEnlargedImage (hf : Equivariant A f) (hS : Supports S x)
      (hST : S ⊆ T) (π : Perm A) (hfix : ∀ a ∈ T, π a = a) :
      π • f x = f x :=
    (supports_iff T (f x)).1 (supports_map hf (supports_mono hST hS)) π hfix
  ```

- [x] **Step 3: Observe missing-interface failures.** Run
  `lake env lean /tmp/nominal-f04a-execution/BasicContracts.lean` before adding
  the declarations. Record missing qualified Package names; fix unrelated
  fixture errors separately. Preserve failing source/log snapshots without
  adding placeholders to production code.

- [x] **Step 4: Draft the basic mathematics.** Create support.tex with
  `sec:finite-support`, mathematical definitions before Lean encodings, and
  propositions for monotonicity, empty support, images and products. Explain
  finite support of an individual element, Mathlib reuse, the abbreviation
  alternatives and sufficient bounds. Mark proposed declarations until checked.
  Add `\input{sections/support}` after foundations in main.tex and adjust scope
  paragraphs to distinguish this draft from delivered F03b.

- [x] **Step 5: Implement the basic calculus.** Create Support.lean with
  imports `Package.Foundations.Action`, `Mathlib.GroupTheory.GroupAction.Support`
  and `Mathlib.Data.Set.Finite.Basic`. Follow existing header/namespace conventions.
  Implement the exact definitions and statements above using Mathlib monotonicity,
  the atom action equation, equivariance and componentwise action. Place the union
  bound in its equality section, then existential product closure outside it with
  local classical witness construction. Add the explicit Support import to
  Package.lean. Add no second support/fixer predicate.

- [x] **Step 6: Check the Lean deliverable.** Run
  `lake build +Package.Foundations.Support Package`,
  then the direct BasicContracts command; require exit 0 and resolve new
  diagnostics. Inspect the task's Lean diff and leave changes uncommitted.

- [x] **Step 7: Reconcile and compile the basic exposition.** Match the article
  propositions to the checked signatures, then compile with the manuscript command
  in Task 4. Require success and resolve any new reference/layout diagnostics.

## Task 2: Transport and the swap criterion

**Files:** Modify Support.lean and support.tex. Temporary test:
`TransportSwapContracts.lean`; retain BasicContracts.

**Interfaces:** Consume Task 1's finite-bound predicate, `supports_iff`,
existential supportedness and witness introduction. Consume F03b's
`Perm.forall_smul_eq_iff_swap_smul_eq (S : Set A) x`, the canonical atom/finite-set
equations and group/action inverse laws. With the same independent A/X and
selected action, produce:

```lean
-- In a section with [DecidableEq A] and open scoped Pointwise:
theorem supports_smul (hS : Supports S x) (π : Perm A) :
    Supports (π • S) (π • x)
theorem supports_smul_iff (π : Perm A) (S : Finset A) (x : X) :
    Supports (π • S) (π • x) ↔ Supports S x
theorem supports_iff_swap (S : Finset A) (x : X) :
    Supports S x ↔ ∀ a b : A, a ∉ S → b ∉ S → Perm.swap a b • x = x
theorem swap_smul_eq_of_supports (hS : Supports S x)
    {a b : A} (ha : a ∉ S) (hb : b ∉ S) : Perm.swap a b • x = x

-- Outside that section; no DecidableEq A or Infinite A:
theorem FinitelySupported.smul (hx : FinitelySupported A x) (π : Perm A) :
    FinitelySupported A (π • x)
theorem finitelySupported_smul_iff (π : Perm A) (x : X) :
    FinitelySupported A (π • x) ↔ FinitelySupported A x
```

- [x] **Step 1: Write transport/swap consumers.** In TransportSwapContracts,
  use only `import Package` and explicitly `open scoped Pointwise` for finite-set
  actions. Add these named assertions:

  | Name | Assertion and required consumption |
  | --- | --- |
  | `transportedFixation` | From `Supports S x` and σ fixing `π • S` pointwise, conclude `σ • (π • x) = π • x` using `supports_smul` and `supports_iff` |
  | `transportBack` | From `Supports (π • S) (π • x)`, recover `Supports S x` using `supports_smul_iff`; also consume its forward-transport direction |
  | `swapCriterionUse` | Outside-swap invariance and `hfix : ∀ a ∈ S, π a = a` imply `π • x = x` by the reverse swap criterion and `supports_iff` |
  | `supportedOutsideSwap`, `reflexiveOutsideSwap` | Derive `Perm.swap a b • x = x` from the forward criterion and the named consequence; include b = a without a distinctness premise |
  | `existentialTransport` | Without equality/infinitude instances, use `FinitelySupported.smul` and both directions of `finitelySupported_smul_iff` |
  | `noncommutingTransport` | On `Fin 3`, π = swap 0 1 and σ = swap 1 2 satisfy `(π * σ) 0 = 1` and `(σ * π) 0 = 2`; transport singleton support of 0 with π and simplify to `Supports ({1} : Finset (Fin 3)) (1 : Fin 3)` |
  | `finiteSwapCriterion` | Instantiate both directions of `supports_iff_swap` with A = Bool and an arbitrary selected result action, without an infinitude instance |

- [x] **Step 2: Observe the intended failures.** Run
  `lake env lean /tmp/nominal-f04a-execution/TransportSwapContracts.lean` before
  implementing the six new results. Record missing Task 2 names independently
  of any fixture mistake and preserve the failing version.

- [x] **Step 3: Draft transport and swap proofs.** Extend support.tex with
  `prop:support-transport` and `prop:support-swap-criterion`. Explain conjugation
  and the inverse direction; identify the specialization of the already checked
  F03b proposition by its existing label `prop:swap-invariance`. State no
  commutation, nominality or infinitude requirement. Explain why Mathlib's
  commuting-action lemma does not supply the desired contract.

- [x] **Step 4: Implement transport.** A σ fixing `π • S` makes
  `π⁻¹ * σ * π` fix S. Apply support of x and the action laws to obtain
  `σ • (π • x) = π • x`; use inverse transport for the equivalence. Reuse finite
  image membership and existing permutation equations. A private Set-level
  helper is allowed if useful; no larger fixing-subgroup API or public helper
  is needed. Derive the existential versions with local classical witnesses.

- [x] **Step 5: Specialize the swap interface.** Combine Task 1's
  `supports_iff` with F03b at `(S : Set A)`; project the equivalence for the
  named swap consequence. Do not repeat factorization or its list-action proof.

- [x] **Step 6: Verify the Lean results.** Run
  `lake build +Package.Foundations.Support Package`, then TransportSwapContracts
  and BasicContracts directly. Require exit 0 with the generic assumptions
  intact. The finite example must retain the explicit noncommutation calculation;
  do not resolve a proof
  failure by introducing `SMulCommClass` or changing an action.

- [x] **Step 7: Reconcile and compile the exposition.** Match the transport and
  swap statements/proofs to the checked declarations, compile with Task 4's
  manuscript command, resolve new diagnostics and inspect the task's diff.

## Task 3: Finite intersection and its atom boundary

**Files:** Modify Support.lean and support.tex. Temporary test:
`IntersectionContracts.lean`.

**Interfaces:** Consume `supports_iff_swap`, `swap_smul_eq_of_supports` and
`supports_empty_iff`, plus `Finset.exists_notMem`, `Perm.conj_swap`, swap
computation/inverse equations and `mul_smul`. Produce only this additional
public theorem, in namespace `NominalPackage`:

```lean
theorem supports_inter {A : Type u} [DecidableEq A] [Infinite A]
    {X : Type v} [MulAction (Perm A) X] {S T : Finset A} {x : X}
    (hS : Supports S x) (hT : Supports T x) : Supports (S ∩ T) x
```

- [x] **Step 1: Write the intersection and boundary consumers.** In
  IntersectionContracts use only `import Package`. Prove:

  | Name | Assertion and required consumption |
  | --- | --- |
  | `intersectionFixation` | `hS`, `hT` and π fixing `S ∩ T` imply `π • x = x`; consume `supports_inter` and `supports_iff` with independent universes and no nominality |
  | `disjointSupportsInvariant` | Add `hST : S ∩ T = ∅`; consume intersection and empty support to conclude `∀ π : Perm A, π • x = x` |
  | `overlappingAtomBounds` | On infinite A, pairwise distinct a,b,c have `{a,b} ∩ {a,c} = {a}`; derive supports of a from membership, intersect them, and use the result to show any π fixing a fixes that element |
  | `falseSupportedByFalse`, `falseSupportedByTrue` | Under canonical Bool atom action, prove `Supports ({false} : Finset Bool) false` and `Supports ({true} : Finset Bool) false`; the second uses injectivity of a bijection fixing true |
  | `falseNotEmptySupported` | Prove `¬ Supports (∅ : Finset Bool) false` using `Perm.swap false true` |
  | `finiteIntersectionFails` | Combine the two singleton supports with `{false} ∩ {true} = ∅` and the preceding negation to refute support by their intersection |

- [x] **Step 2: Check the intended pre-implementation result.** Run
  `lake env lean /tmp/nominal-f04a-execution/IntersectionContracts.lean`.
  Record the missing `supports_inter` failures. The Bool proofs use only Tasks
  1/2 and must already check; preserve the failing overall source/log. A guarded
  instance-search failure is not a substitute for the proved counterexample.

- [x] **Step 3: Draft the intersection mathematics.** In support.tex add
  `prop:finite-support-intersection` and `ex:finite-atom-intersection`. State
  finite bounds and infinite atoms explicitly, explain the spare atom and the
  Bool argument, and distinguish support from pointwise fixation of the bound
  by permutations that merely fix the element.

- [x] **Step 4: Implement the intersection proof.** Reduce to outside swaps.
  Handle a = b by identity; otherwise choose c outside `S ∪ T ∪ {a,b}` with
  `Finset.exists_notMem`. Each endpoint avoids at least one bound, so `swap a c`
  and `swap c b` fix x. Obtain
  `swap a c * swap c b * swap a c = swap a b` from
  `Perm.conj_swap (Perm.swap a c) c b` and existing equations, then apply
  `mul_smul`. Keep the identity local; export no new factorization/selection API.

- [x] **Step 5: Verify the mathematical deliverable.** Run
  `lake build +Package.Foundations.Support Package` and IntersectionContracts
  directly; require exit 0. Confirm the consumer uses the intersection theorem's
  conclusion and the Bool negation is a proved statement.

- [x] **Step 6: Reconcile and compile the exposition.** Match the intersection
  and Bool statements to the checked results and compile with Task 4's manuscript
  command. Require success and resolve new diagnostics. Keep least support and freshness
  explicitly deferred to later slices.

## Task 4: Public acceptance, audit and article delivery

**Files:** Modify audit, Package README, article exposition/scope, roadmap,
spec/plan status and the three research guides in the file table. Temporary
checks: `PublicSignatures.lean`, `ActionCoherence.lean`, and Tasks 1–3 consumers.

**Interfaces:** Consume all 18 approved declarations (two definitions and
sixteen theorems) from Tasks 1–3. Produce a verified public import, five production
source modules including the root, complete production audit coverage and an
accurate compiled `sec:finite-support` article section. Declaration counts are
measured, not prescribed.

- [x] **Step 1: Check signatures and preserved actions.** In PublicSignatures
  assign every public constant to its exact approved type, print universe
  parameters and confirm no extra instances appear. In ActionCoherence recheck
  `π • a = π a`, componentwise products, scoped finite-set images, discrete
  fixation, `(π • σ : Perm A) = π * σ`, and `(π • f) x = π • f x` for ordinary
  functions. Use actual equalities, not nominality assumptions. Reuse existing
  F03a coherence consumers if available and equivalent; otherwise write these
  six focused equations using only `import Package`.

- [x] **Step 2: Extend representative audit output.** Add `#print axioms` for
  `NominalPackage.supports_smul`, `supports_iff_swap`, `supports_inter`,
  `supports_map`, `supports_prod`, `FinitelySupported.smul` and
  `FinitelySupported.prod`, qualifying each with `NominalPackage`.
  Retain the module-origin traversal, zero-coverage rejection and standard-axiom
  allowlist. The new module must be reached through the public root; no audit
  filter or checker rewrite is expected.

- [x] **Step 3: Run the complete final code validation.** After the last
  production change, run these commands and inspect their full results:
  ```sh
  lake build Package +Package.Tests.AxiomAudit
  lake env lean /tmp/nominal-f04a-execution/BasicContracts.lean
  lake env lean /tmp/nominal-f04a-execution/TransportSwapContracts.lean
  lake env lean /tmp/nominal-f04a-execution/IntersectionContracts.lean
  lake env lean /tmp/nominal-f04a-execution/PublicSignatures.lean
  lake env lean /tmp/nominal-f04a-execution/ActionCoherence.lean
  lake env lean Package/Tests/AxiomAudit.lean
  python3 Package/Scripts/check-imports.py
  ```
  Require exit 0, five production source modules plus one audit module, full
  new-module coverage, permitted axioms only and no unresolved new diagnostics.
  If the checker changes, run `python3 Package/Scripts/check-imports.py --self-test`.
  Record cached/rebuilt conditions; direct audit execution is required even
  when its compiled artifact is cached.

- [x] **Step 4: Reconcile article and public documentation.** Replace draft
  claims with checked references only for delivered declarations; check every
  hypothesis, universe, action, finite-set operation and proof route. Include
  relevant Mathlib attribution and distinguish its support/finite-set laws
  from the nominal transport and intersection arguments. Update Package/README.md
  and the article introduction/abstract/title to explain the mathematical scope.
  Exclude stage identifiers, development chronology and operational evidence
  from the article. Keep historical revisions, checks and completion status
  in the roadmap and implementation notes.

- [x] **Step 5: Compile and inspect the manuscript.** From `docs/article/`:
  ```sh
  latexmk -pdf -interaction=nonstopmode -halt-on-error \
    -outdir=/tmp/nominal-package-article-build main.tex
  ```
  Require successful compilation, no unresolved references or new unexplained
  layout diagnostics. Inspect the resulting support-section text and verify
  mathematical correspondence separately from rendering. Keep all artifacts
  outside the source tree and record whether this invocation rebuilt anything.

- [x] **Step 6: Record delivery and preservation checks.** Update F04a/PKG-11
  evidence in the active roadmap, this plan/spec and research guides with actual
  commands, measured counts, review status and limits. Run `git diff --check`,
  untracked-file whitespace and local Markdown-link/anchor checks. Compare against
  the execution snapshot to confirm reference code, historical roadmap, old
  validation scripts and pins were preserved. Shared integration changes affecting
  reference targets require separate `lake build Nominal Instances Examples`,
  `lake env lean Examples/AxiomAudit.lean` and `python3 scripts/check-imports.py`;
  the planned Package-only changes do not affect those targets.

- [x] **Step 7: Obtain final independent review and resolve findings.** Give a
  fresh read-only reviewer the spec, plan, diff, actual verification evidence
  and article. Review theorem strength and consumers as well as successful
  compilation, especially the five Review Focus items. Resolve findings, rerun
  checks affected by any fixes and report remaining limitations. Mark F04a DONE
  only when code, consumers, audit, article and review obligations pass; retain
  PKG-F04 IN PROGRESS and F04b–F04d TODO. Do not commit or merge.

## Planning self-review and execution handoff

Coverage review maps definitions/basic support/product/image closure to Task 1;
conjugation, F03b specialization and support-existence transport to Task 2;
finite intersection and its counterexample to Task 3; and complete signatures,
coherence, audits, documentation and article reconciliation to Task 4. Every
Review Focus item has a named owning consumer. Article drafting belongs to
Tasks 1–3, not solely to final reconciliation. Signature names and assumptions
match the approved spec; no F04b–F04d or F05 implementation is included.

Self-review checked scope, step specificity, type consistency, missing edge cases
and proportion, with no uncovered specification obligation. Planning initially
created only documentation; the consumer assertions were elaborated during the
subsequent approved execution. Prior design-session baseline build/audit/LaTeX
results remain historical evidence, separate from the execution results below.

**Approved method: native execution.** The author selected this method after
reviewing the concrete plan. The three mathematical tasks extend one module in
dependency order and finish with one integrated independent review. Specification
and execution approval are both recorded; do not request them again.

## Native delivery evidence

All 18 approved declarations are implemented with their original assumptions.
The final Package build passed 969 jobs using cached dependencies; the direct
audit checked 104 production declarations in four defining modules with only
`propext`, `Classical.choice`, `Quot.sound`. The import checker reached five
production source modules and one audit module. All five current temporary
consumer/signature files and both retained F03a consumers passed.

Each mathematical task developed and compiled its corresponding LaTeX exposition.
The final reconciled manuscript has 26 pages with a clean log, and its source/
extracted text was checked against the Lean results. Independent final review
found no Critical, Important or Minor issues and independently reran code checks,
document/preservation checks and a fresh manuscript compilation. No fix pass or
mathematical contract revision was required.

Exact commands, cache limits and verification iterations are in the active
roadmap's native F04a delivery log. Scratch evidence remains under
`/tmp/nominal-f04a-execution/`; review logs are under
`/tmp/nominal-f04a-final-review/`. No fresh whole-project Lean build, dependency
bootstrap or rebuild of unchanged reference targets is claimed. Source hashes
confirm the reference library, historical roadmap and dependency pins were preserved.
