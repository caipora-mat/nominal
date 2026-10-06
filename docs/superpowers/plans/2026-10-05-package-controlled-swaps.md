# F03b Controlled Swaps Implementation Plan

**Article editorial correction:** manuscript passages follow the current
[research-article policy](../../research/2026-10-05-article-plan.md): selected
system/mathematical exposition and substantive comparisons, with no task IDs
or development/review/build diary. Article instructions below are amended
accordingly; the recorded execution history remains an internal record.

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development or superpowers:executing-plans to implement this plan task-by-task using the approved native execution method. Steps use checkbox syntax for tracking. The author approved this plan and selected native execution.

**Goal:** Deliver controlled swap factorization, arbitrary-set avoidance and the selected-action criterion, with matching checked LaTeX exposition, completing F03b of PKG-F03.

**Architecture:** Specialize pinned Mathlib's `mem_closure_isSwap` to swaps whose distinct endpoints lie in the original moved set, then extract an ordered endpoint-pair list using `Subgroup.closure_induction_left`. Export the permutation results from a new foundation module and consume them through the existing `MulAction (Perm A) X` interface. Preserve the existing permutation representation and all action instances.

**Tech Stack:** Lean/Mathlib 4.34.1; Mathlib revision `d13f23b723b8a846827a245b89c10fc7d3f11612`; existing Lake target, Python import checker, module-origin axiom audit and LaTeX/latexmk.

**Spec:** [Approved F03b specification](../specs/2026-10-05-package-controlled-swaps-design.md). The author approved the written specification, then approved this plan by selecting native execution. Planning checkout: `fasapa/nominal-package`, HEAD `3d2196a57b8964084dd58a65a0cb1c0be50b1592`.

## Global Constraints

- Preserve namespace `NominalPackage`, the finite-moved subgroup representation of `Perm A`, and `MulAction (Perm A) X`.
- New implementation belongs under `Package/` and imports Mathlib directly. Preserve the current Package import boundary; no reference/research imports.
- Retain pinned Lean/Mathlib 4.34.1, the manifest and existing Lake configuration/default targets.
- Atom and carrier universes are independent. Swaps retain `[DecidableEq A]`, with classical equality selectable locally. Add no `Infinite A`, countability, `Finite A`, `Fintype A`, `Nonempty A`, or nominality assumption to the four public results.
- Avoidance uses arbitrary `Set A`; neither that set nor its complement must be finite. Only each permutation's moved set is finite.
- No new atom/action class, action instance, support predicate, least support, freshness, fresh selection, nominality, predicate bundle, abstraction, recursion or generator belongs to this increment.
- No canonical factor list, executable factorization algorithm, minimum length or uniqueness is promised. The rightmost swap in a list product acts first.
- Work remains in the current checkout on `fasapa/nominal-package`. Preserve all existing tracked and untracked work. Do not switch branches, commit, push, merge, publish, upgrade dependencies or add CI.
- Keep `Nominal/`, `Instances/`, reference `Examples/`, historical `docs/roadmap.md`, original probes and old validation scripts unchanged.
- Persistent usage examples remain reserved for case studies. Use named temporary public-import checks, never a new Package/Examples layer or tests concluding `True`.
- No `sorry`, `admit`, custom axioms or disabled kernel checking. Only standard `propext`, `Classical.choice`, and `Quot.sound` are allowed by the audit.
- All manuscript content stays under `docs/article/` in LaTeX. Draft with the proofs; reconcile selected mathematical statements and compile before delivery. Record execution evidence outside the manuscript. Generated files stay outside the source tree.

## Review Focus

- **Original endpoint bound:** a factorization that only certifies intermediate moved sets is insufficient. Task 1 consumes the original bound at a fixed atom and requires all factors to fix it.
- **Composition order:** a single swap cannot detect reversal. Task 1 tests a noncommuting three-point product and its reverse.
- **Degenerate carriers and identity:** no hidden atom inhabitant or infinite-carrier assumption. Task 1 checks empty/singleton carriers and proves every controlled identity list is empty.
- **Arbitrary avoidance sets:** an unnoticed Finset restriction would weaken F04's input. Task 1 uses an explicitly infinite complement of two natural numbers; Task 2 also covers empty/universal sets.
- **Selected action and universes:** extra imports must preserve atom/product/Finset/discrete/self/pointwise actions. Task 2 uses independent universes, a nontrivial pair consumer and the retained F03a coherence checks.

## Files, ownership and order

| File | Responsibility |
| --- | --- |
| `Package/Foundations/SwapFactorization.lean` (new) | Task 1: controlled and avoiding factorization |
| `Package.lean` | Task 1: explicitly export the new module before Action |
| `Package/Foundations/Action.lean` | Task 2: import factorization and add action implication/equivalence |
| `Package/Tests/AxiomAudit.lean` | Task 3: print all four new results; retain whole-production traversal |
| `Package/README.md` | Task 3: exact public API, ordering, assumptions and verification limits |
| `docs/article/sections/foundations.tex` | Tasks 1/2: selected mathematics and proof ideas; Task 3: final mathematical correspondence |
| `docs/article/sections/introduction.tex`, `docs/article/main.tex` | Task 3: reconcile delivered scope and abstract |
| `docs/nominal-package-roadmap.md` | Task 3: F03b/F03 acceptance and PKG-11 evidence |
| `docs/research/README.md`, `docs/research/2026-10-05-pkg01-readiness.md`, `docs/research/2026-10-05-article-plan.md` | Task 3: current result and remaining F04/F05/PKG-01 work |

Tasks run **1 → 2 → 3**. Each mathematical task includes its article update.
For recommended native execution, root owns all Lean/tests/tracker edits; one
article worker may exclusively own the three LaTeX sources and work concurrently
from the exact signatures. Root reconciles its output before each task finishes.
One fresh final reviewer checks the complete increment. No competing writes to
shared files; no production changes before plan/execution agreement.

Temporary files below use `/tmp/nominal-f03b-execution/`. If that directory
already contains work, preserve it and use a fresh suffixed directory, recording
the actual path in all commands/evidence. This is scratch validation, not a
new maintained harness. Existing F03a checks are available at
`/tmp/nominal-f02-f03a-execution/ActionContracts.lean` and `NegativeContracts.lean`.

## Task 1: Controlled factorization and avoidance

**Files:** Create SwapFactorization; modify Package root and foundations.tex.
Temporary checks: `FactorizationContracts.lean` under the execution directory.

**Interfaces:** Consume existing `Perm`, `moved`, `moved_finite`, group/coercion
and swap equations. Produce these exact declarations in `NominalPackage.Perm`:

```lean
variable {A : Type u} [DecidableEq A]

theorem swap_factorization (π : Perm A) :
    ∃ l : List (A × A),
      (l.map (fun p => swap p.1 p.2)).prod = π ∧
      ∀ p ∈ l, p.1 ≠ p.2 ∧ p.1 ∈ π.moved ∧ p.2 ∈ π.moved

theorem swap_factorization_avoiding (π : Perm A) (S : Set A)
    (hfix : ∀ a ∈ S, π a = a) :
    ∃ l : List (A × A),
      (l.map (fun p => swap p.1 p.2)).prod = π ∧
      ∀ p ∈ l, p.1 ≠ p.2 ∧ p.1 ∉ S ∧ p.2 ∉ S
```

- [x] **Step 1: Record the execution baseline.** Recheck branch/HEAD/status,
  read the approved spec/plan and hash tracked plus untracked source/documents.
  Preserve the planning changes and any intervening work. Confirm the new module
  path is available; record toolchain and the actual scratch directory.

- [x] **Step 2: Write the public-import consumers.** In FactorizationContracts,
  use only `import Package`, namespace `F03bChecks`, and local classical equality
  where necessary. Write named proofs against the intended declarations:

  | Name | Required assertion/consumption |
  | --- | --- |
  | `factorsFixFixedAtom` | Given `π c = c`, obtain `l` with mapped product `π` and, for every `p ∈ l`, `p.1 ≠ p.2`, `p.1 ≠ c`, `p.2 ≠ c`, and `Perm.swap p.1 p.2 c = c`; use `swap_factorization` and its endpoint membership |
  | `identityControlledListEmpty` | For `l : List (A × A)`, if every endpoint lies in `(1 : Perm A).moved`, conclude `l = []`; apply this to a witness from `swap_factorization 1` and verify the empty mapped product equals `(1 : Perm A)` |
  | `emptyCarrierFactors`, `singletonCarrierFactors` | For every `π : Perm PEmpty.{u+1}` and `π : Perm (Fin 1)` respectively, consume controlled factorization to obtain `l = []` and mapped product `π` |
  | `finiteSwapFactors` | For `π := Perm.swap (0 : Fin 2) 1`, obtain a nonempty factor list whose product is π, with distinct endpoints in `{0,1}`; derive nonemptiness from the product equality and `π 0 = 1` |
  | `threePointOrder` | For `l : List (Fin 3 × Fin 3) := [(0,1),(1,2)]`, its mapped product sends `0 ↦ 1`, `1 ↦ 2`, `2 ↦ 0`; the reversed list sends `0 ↦ 2`. Obtain another list via controlled factorization at that product and use its product equality to derive the same three evaluations and inequality to the reversed product, without requiring the returned list to equal l |
  | `infiniteAvoidance` | For `S := ({0,1} : Set ℕ)ᶜ`, prove `S.Infinite` via `Set.Finite.infinite_compl`; `Perm.swap 0 1` fixes S pointwise, and `swap_factorization_avoiding` yields a nonempty list with product that swap and all distinct endpoints in `{0,1}` |

  Retain a generic arbitrary-`Set A` instantiation of the avoidance theorem,
  using its outside-endpoint facts to show each factor fixes every member of S.
  All list products use the expression from the Interfaces block, not a new
  public evaluator. Scratch tests may use local `let` names for that expression.

- [x] **Step 3: Observe the intended missing-interface failure.** Run
  `lake env lean /tmp/nominal-f03b-execution/FactorizationContracts.lean` before
  adding the new declarations. Record failures at the two missing theorem names;
  correct unrelated fixture syntax separately. Keep the failing source/log
  snapshots. No admissions or axioms may stand in for the missing results.

- [x] **Step 4: Draft the factorization mathematics in parallel.** In
  foundations.tex replace the post-transpositions deferral with
  `sec:controlled-swaps`, `prop:controlled-factorization`, and
  `prop:avoidance-factorization`. Mark the results prospective until checked.
  Explain endpoint control, empty product and rightmost-first order. Describe
  restricted generators and the Mathlib finite-set reduction, including strict
  decrease but not an exact one-point deletion for two-cycles.

- [x] **Step 5: Implement controlled factorization.** Create SwapFactorization
  with the existing header/namespace conventions and imports of
  `Package.Foundations.Permutation`, `Mathlib.GroupTheory.Perm.ClosureSwap`, and
  `Mathlib.Algebra.Group.Subgroup.Pointwise`; add only further direct Mathlib
  list imports required by actual elaboration. For fixed π define the restricted
  ambient generator predicate locally/private. Apply `mem_closure_isSwap` using
  `moved_finite` and the identity/swap orbit witnesses in the spec. Extract lists
  by `Subgroup.closure_induction_left`: empty list for identity, prepend for
  generators, same pair for inverse generators by `Equiv.swap_inv`. Keep the
  original moved set fixed throughout. Transfer via the existing subgroup
  inclusion and `map_list_prod`/subtype extensionality. No replacement group,
  public generator abstraction or copied cardinality induction is required.

- [x] **Step 6: Derive avoidance and export the module.** Prove the second
  signature by applying controlled factorization and contradicting `hfix` at
  any endpoint alleged to lie in S. Add the explicit new import to Package.lean.
  Docstrings state assumptions, original endpoint control, list order and
  nonuniqueness. Keep Permutation.lean's delivered implementation unchanged.

- [x] **Step 7: Verify and reconcile this mathematical increment.** Run
  `lake build Package` and the direct FactorizationContracts command. Expect
  exit 0, meaningful conclusions and no new diagnostics. Inspect both results
  with `#print axioms` in a temporary file; only the permitted standard axioms
  may occur. Reconcile the article propositions/proofs to the checked names
  and signatures, then compile using the article command in Task 3. Resolve
  introduced diagnostics and inspect the focused changes; leave them uncommitted.

## Task 2: Selected-action consequences and coherent public consumption

**Files:** Modify Action and foundations.tex. Create temporary
`ActionContracts.lean`; reuse both F03a temporary files unchanged.

**Interfaces:** Consume Task 1's avoiding factorization and existing group/action
laws. Produce these exact declarations in `NominalPackage.Perm`:

```lean
variable {A : Type u} [DecidableEq A]
variable {X : Type v} [MulAction (Perm A) X]

theorem smul_eq_of_swap_smul_eq (S : Set A) (x : X)
    (hswap : ∀ a b : A, a ∉ S → b ∉ S → swap a b • x = x)
    (π : Perm A) (hfix : ∀ a ∈ S, π a = a) :
    π • x = x

theorem forall_smul_eq_iff_swap_smul_eq (S : Set A) (x : X) :
    (∀ π : Perm A, (∀ a ∈ S, π a = a) → π • x = x) ↔
      (∀ a b : A, a ∉ S → b ∉ S → swap a b • x = x)
```

- [x] **Step 1: Add meaningful action consumers.** Use only `import Package`
  in the temporary ActionContracts file, with independent `u v w`. Add:

  | Name | Required assertion/consumption |
  | --- | --- |
  | `invariantPairProjections` | Given selected actions on `X : Type v`, `Y : Type w`, outside-swap invariance of `(x,y)`, and pointwise fixation of arbitrary `S : Set A` by π, conclude `π • x = x ∧ π • y = y`; apply the new implication to the pair and use projections |
  | `emptyAvoidanceCriterion` | `(∀ π : Perm A, π • x = x) ↔ (∀ a b : A, Perm.swap a b • x = x)` by specializing the new equivalence to `S = ∅` |
  | `universalAvoidance` | For any x, π and `hfix : ∀ a ∈ (Set.univ : Set A), π a = a`, conclude `π • x = x` using the new implication's vacuous outside-swap premise |
  | `distinctSwapsSuffice` | Given invariance only for distinct outside endpoints, conclude `π • x = x` when π fixes S; discharge equal endpoints using `swap_self` and `one_smul` |

  Exercise both directions of the equivalence in `emptyAvoidanceCriterion`.
  The generic pair consumer has no finite-support, finite-set or infinite-atom
  premise and does not unfold Package representation internals.

- [x] **Step 2: Observe missing action-interface failures.** Run
  `lake env lean /tmp/nominal-f03b-execution/ActionContracts.lean`. Record missing
  new action declarations before implementation, rather than an unrelated
  elaboration failure, and preserve this failing source/log snapshot.

- [x] **Step 3: Draft the action proposition concurrently.** After selected
  actions in foundations.tex, add `prop:swap-invariance` with the exact
  arbitrary-set equivalence. Explain list-product invariance and the converse
  third-point swap argument. Distinguish pointwise fixation from setwise
  preservation, and moved points from support in an arbitrary action. Identify
  the result as F04's input, with support theory still future work.

- [x] **Step 4: Implement both action results.** Import SwapFactorization in
  Action and place the new results in a section with only their needed equality
  and action instances. Prove the implication by list induction on an avoiding
  witness with `List.prod_nil`, `List.prod_cons`, `one_smul`, and `mul_smul`.
  For the converse, use `swap_apply_of_ne_of_ne` to fix every atom in S and apply
  the universal hypothesis. Add no action instance, helper support definition,
  broad simp rule or extra assumption to existing declarations.

- [x] **Step 5: Verify public consumption and instance coherence.** Run
  `lake build Package` and the new direct action check, then rerun the existing
  F03a ActionContracts and NegativeContracts commands. Their public-import
  checks cover atoms, independent-universe products, scoped Finsets, Discrete,
  bare permutation self-action and pointwise functions, plus the expected
  missing-action diagnostic. Expect exit 0 with no new diagnostics. If those
  historical scratch files are unavailable at execution, recreate just their
  named coherence/negative assertions in the current temporary file, not in
  Package. Print axioms for the two action results.

- [x] **Step 6: Reconcile and compile the action exposition.** Replace proposed
  status only for the now checked results; verify the exact assumptions,
  declaration names, both logical directions and proof explanation. Compile
  the article with the command below and resolve introduced diagnostics.

## Task 3: Audit, mathematical correspondence and delivery

**Files:** Update audit, Package README, three article sources, active roadmap,
and the three research notes listed in the ownership table. No new checker or
Lake configuration is expected.

**Interfaces:** Consume all four results and both tasks' direct public-import
checks. Produce verified coverage, measured axiom evidence and matching compiled
exposition; no additional mathematical API.

- [x] **Step 1: Extend the existing audit.** Add `#print axioms` for
  `NominalPackage.Perm.swap_factorization`, `.swap_factorization_avoiding`,
  `.smul_eq_of_swap_smul_eq`, and `.forall_smul_eq_iff_swap_smul_eq`, writing each
  fully qualified name. Retain the module-origin traversal and its existing
  simulated rejection tests. Check that the new module's private/generated
  declarations are covered automatically; do not replace the traversal with
  a four-name allowlist.

- [x] **Step 2: Update public documentation and provisional evidence.** Add
  the actual API and list convention to Package/README.md. Update the article
  abstract/introduction and relevant theorem references to describe the system
  and its mathematics. Put measured counts, verification status and historical
  comparisons in the roadmap, not an article evidence section.

- [x] **Step 3: Run final Package and consumer verification.** Execute:

  ```sh
  lake build Package +Package.Tests.AxiomAudit
  lake env lean /tmp/nominal-f03b-execution/FactorizationContracts.lean
  lake env lean /tmp/nominal-f03b-execution/ActionContracts.lean
  lake env lean /tmp/nominal-f02-f03a-execution/ActionContracts.lean
  lake env lean /tmp/nominal-f02-f03a-execution/NegativeContracts.lean
  lake env lean Package/Tests/AxiomAudit.lean
  python3 Package/Scripts/check-imports.py
  git diff --check
  ```

  Expect four production source modules (root plus three foundation modules),
  one audit module, positive measured declaration coverage and only the permitted
  axioms. Run the direct audit even if Lake reports a cached/replayed audit.
  Resolve diagnostics locally. If the checker changes, also run
  `python3 Package/Scripts/check-imports.py --self-test`. If shared integration
  changes, run the separate reference build, direct audit and import checker
  from the spec; source-preservation checks suffice when it stays unchanged.

- [x] **Step 4: Finalize and verify the LaTeX artifact.** Record verification
  output/cache conditions in the roadmap or this plan. Check the four Lean
  signatures against the three propositions, endpoint restrictions, product
  order, closure proof and decrease explanation. Create the output directory
  if needed; from `docs/article/` run:

  ```sh
  latexmk -pdf -interaction=nonstopmode -halt-on-error \
    -outdir=/tmp/nominal-package-article-build main.tex
  ```

  Inspect the final log for unresolved references/warnings/layout diagnostics
  and inspect rendered changed pages or extracted text. PDF compilation is
  separate from the mathematical correspondence check; require both. Keep
  all generated artifacts outside the repository.

- [x] **Step 5: Obtain an independent final review.** Review the complete
  increment against the approved spec, including statements, selected action,
  original-set endpoint invariant, imports, tests, axioms and article. Resolve
  findings and rerun only the affected checks; no unverified approval claim.
  For native execution use one fresh reviewer at this point. If the author
  chooses subagent-driven execution, retain its per-task reviews as well.

- [x] **Step 6: Record delivery and preserve unrelated work.** Update F03b
  checkboxes and PKG-F03 status only after all mathematical and article checks
  pass. Keep PKG-11 ongoing and F04/F05/PKG-01 pending. Record exact declarations,
  article labels, commands, measured counts, review outcome and remaining
  limitations in the active roadmap/research notes. Check links/fences and
  whitespace of tracked and untracked documents, run `git diff --check`, and
  compare hashes to the execution baseline. Distinguish changed uncommitted
  work, scratch evidence, cached/rebuilt project artifacts and any fresh build.
  Do not commit, push or start F04.

## Planning evidence and self-review

This plan uses the approved four-signature contract and the inspected Package
sources at `3d2196a`. The existing F03a temporary checks remain available and
import only Package. Pinned Mathlib source confirms restricted swap closure,
left closure induction and `Set.Finite.infinite_compl`. The design-phase
dependency probe is prior evidence, not a new factorization proof.

Coverage mapping: controlled factorization, original endpoints, identity/order/
finite carriers and infinite-set avoidance → Task 1; generic selected actions,
both equivalence directions, empty/universal sets and coherence → Task 2;
production/audit coverage, README/status and final independent review → Task 3.
Article mathematics belongs to Tasks 1/2 and internal validation/correspondence review to
Task 3. All Review Focus items have named checks. The Interfaces blocks preserve
the approved names, explicit parameters and independent universes exactly.
No standalone example layer, new foundation representation or F04 API is hidden
in this plan. The plan has been self-reviewed for coverage, types, executable
steps and proportion; native execution is complete with a clean independent final review.

## Execution agreement

Approved method: **native execution**, with root implementing Lean and tests,
an optional article worker under exclusive LaTeX ownership, and one fresh final
reviewer. The two mathematical tasks share a small, fixed interface and the
third verifies their combined delivery. The author selected this method after reviewing the plan.

The author approved this plan and selected native execution. Root implements the
Lean changes, a parallel worker owns the article, and a fresh reviewer checks
the completed increment. No commit, push or branch change is authorized.

## Execution result

All three tasks are complete. The four signatures were preserved. Product
transport maintains ambient equality through `toEquiv_mul` at each cons and
uses `Subtype.ext`, avoiding a separate `map_list_prod` rewrite without changing
the proof route. Temporary failures and verification records are retained in
`/tmp/nominal-f03b-execution/`. Final independent review found no Critical,
Important or Minor issues. The package roadmap records exact commands, the
81-declaration audit, four-plus-one source coverage and the 17-page compiled
article. Changes remain uncommitted as requested; no later increment was started.
