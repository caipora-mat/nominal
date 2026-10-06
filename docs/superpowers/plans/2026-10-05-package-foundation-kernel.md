# Package Foundation Kernel Implementation Plan

**Article editorial correction:** manuscript passages follow the current
[research-article policy](../../research/2026-10-05-article-plan.md): selected
system/mathematical exposition and substantive comparisons, with no task IDs
or development/review/build diary. Article instructions below are amended
accordingly; the recorded execution history remains an internal record.

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking. The user's no-commit instruction overrides the skills' commit steps.

**Goal:** Deliver PKG-F02 plus the approved F03a permutation/action kernel, with independently checked interfaces, coverage/auditing, and its accompanying LaTeX article section.

**Architecture:** A proved finite-moved subgroup of Mathlib permutations supplies the public `NominalPackage.Perm` carrier. Standard Mathlib actions and a distinct discrete-data structure supply the action interface, with separate production and audit imports. No reference-library imports or support theory are required by this increment.

**Tech Stack:** Lean `v4.34.1`, Mathlib `v4.34.1` (manifest revision `d13f23b723b8a846827a245b89c10fc7d3f11612`), Lake TOML, Python 3 standard library, LaTeX/latexmk.

**Spec:** [Approved F02 + F03a specification](../specs/2026-10-05-package-foundation-kernel-design.md). The user approved it, then requested a LaTeX article under `docs/article/` maintained alongside implementation. The user approved this plan and chose native execution. During execution the
user removed the standalone Package examples layer: persistent usage examples
are reserved for future case studies. This document incorporates that correction;
one-off compatibility proofs are retained only outside the repository.

## Global Constraints

- Retain pinned Lean and Mathlib 4.34.1 and the current Lake manifest.
- Use namespace `NominalPackage` and top-level implementation directory `Package/`. The conventional `Package.lean` root and minimal Lake registration are the only required implementation integration outside that directory.
- Depend directly on Mathlib. Import no `Nominal`, `Instances`, `Examples`, research probe or historical `NominalSets` module from Package production.
- Use standard `MulAction (Perm A) X`, not a new outParam action class. Atom A and carrier X may inhabit independent universes.
- Reuse Mathlib's product action and its `Pointwise`-scoped Finset image action. Consumers using finite-set scalar notation explicitly write `open scoped Pointwise`.
- Do not install conjugation on the bare permutation group, whose inherited self-action is left multiplication. Bare function actions remain pointwise.
- No admissions, custom axioms or disabled kernel checking. The allowed standard axioms are `propext`, `Classical.choice` and `Quot.sound`.
- Work on `fasapa/nominal-package`; recheck HEAD/status before execution. Preserve all tracked/untracked work, including the two original predicate probes. Do not switch branches, create a replacement checkout, commit, push, merge, publish, upgrade dependencies or add CI.
- Keep `Nominal/`, `Instances/`, `Examples/`, existing validation scripts and `docs/roadmap.md` unchanged. Retain `defaultTargets = ["Nominal", "Instances"]`.
- F03b swap-generation/support prerequisites, least support, freshness, quotient actions, predicates, binders, recursion and generation are outside this plan.
- All manuscript content under `docs/article/` is LaTeX. Update exposition with each mathematical task; distinguish paper arguments from implemented and kernel-checked declarations. Build products stay in `/tmp`.

## Review Focus

- **Finite/empty atom types:** basic permutation/action results must not acquire an accidental `Infinite` assumption; Task 1 tests `Fin 1` and universe-polymorphic empty atoms.
- **Degenerate swaps:** equal endpoints give identity and no moved points; Task 1 consumes both facts through the public interface.
- **Coercion/action coherence:** inference from the public root must agree with group laws even for products, finite sets, functions and permutation carriers; Task 2 proves the relevant computations and distinctions.
- **Auditable production:** the public root must expose actual proved declarations, including private dependency names; Task 3 audits production by module origin and rejects empty coverage.
- **Partial dependency-parser failure:** Lean's JSON mode can exit zero with a per-file error; Task 3 exercises that failure, malformed output and orphan/forbidden imports rather than trusting process status alone.

## File ownership and order

| File | Owner/task and purpose |
| --- | --- |
| `Package/Foundations/Permutation.lean` | Task 1: finite-moved subgroup and public permutation/swap API |
| `Package.lean` | Task 1 initially imports Permutation; Task 2 adds Action |
| `lakefile.toml` | Task 1 adds only `[[lean_lib]] name = "Package"` |
| `Package/Foundations/Action.lean` | Task 2: standard action interface, Discrete and equivariance |
| `Package/Tests/AxiomAudit.lean` | Task 3: imported module-origin audit and validator checks |
| `Package/Scripts/check-imports.py` | Task 3: inventory, dependency JSON, closure/policy check and self-tests |
| `Package/README.md` | Task 3: usage, actual validation commands, scope and build limits |
| `docs/article/main.tex` | Existing draft entry point; Task 3 checks mathematical scope and PDF rendering |
| `docs/article/sections/introduction.tex` | Tasks 1–3 maintain the actual implemented scope |
| `docs/article/sections/foundations.tex` | Tasks 1/2 refine mathematics and declaration correspondence; Task 3 verifies all implementation claims |
| `docs/nominal-package-roadmap.md` | Task 3 records F02/F03a delivery and remaining F03b obligations |

Tasks run in order **1 → 2 → 3**. Article edits belong to their owning task; an
article subagent may work in parallel only with explicit file ownership and
the implementer's actual declarations/results. No setup-only task counts as
foundation delivery. Each task leaves a compiling, reviewable increment; do
not add stub declarations for later tasks.

## Task 1: Finite permutations with a real Package consumer

**Files:** Create Permutation and the Package root. Keep public-import test
proofs only in `/tmp/nominal-f02-f03a-execution/ActionContracts.lean`. Modify `lakefile.toml` and the two article sections.

**Interfaces:**

- Consumes Mathlib `Equiv.Perm`, `Subgroup`, set finiteness and swaps; no atom class.
- Produces `permSubgroup (A : Type u) : Subgroup (Equiv.Perm A)` and
  `abbrev Perm (A : Type u) : Type u := ↥(permSubgroup A)`.
- Produces `Perm.toEquiv : Perm A → Equiv.Perm A`, one `FunLike (Perm A) A A`,
  `Perm.moved : Perm A → Set A`, and `Perm.swap [DecidableEq A] : A → A → Perm A`.
- Produces the exact permutation equations in the approved spec under these names:
  `Perm.ext`, `toEquiv_apply`, `one_apply`, `mul_apply`, `inv_apply_apply`,
  `apply_inv_apply`, `toEquiv_one`, `toEquiv_mul`, `toEquiv_inv`,
  `moved_finite`, `moved_one`, `moved_mul_subset`, `moved_inv`, `moved_conj`,
  `swap_apply_left`, `swap_apply_right`, `swap_apply_of_ne_of_ne`, `swap_self`,
  `swap_inv`, `swap_mul_self`, `conj_swap`, `moved_swap` (all in `Perm`).

- [x] **Step 1: Record the execution baseline.** Re-read the spec, current status,
  branch and relevant history. Hash existing tracked/untracked files before
  edits. Confirm the proposed Package paths do not contain intervening user
  work. Keep the two untracked predicate probes and research handoff unchanged.

- [x] **Step 2: Write named public-import consumers before their implementation.**
  Create `/tmp/nominal-f02-f03a-execution/ActionContracts.lean` with only `import Package`.
  Use namespace `NominalPackage.Examples` and independently quantified universes.
  The test declarations must prove these assertions, using the named public
  application/extensionality equations rather than unfolding the subgroup:

  ```text
  permutationRoundTrip (π σ : Perm A) (a : A) :
    (π * σ) (σ⁻¹ (π⁻¹ a)) = a
  conjugateSwap (π : Perm A) (a b : A) :
    π * Perm.swap a b * π⁻¹ = Perm.swap (π a) (π b)
  swapAvoidsThird (a b c : A) (hca : c ≠ a) (hcb : c ≠ b) :
    Perm.swap a b c = c
  reflexiveSwapMovesNothing (a : A) : Perm.moved (Perm.swap a a) = ∅
  inverseMovesSame (π : Perm A) : Perm.moved π⁻¹ = Perm.moved π
  ```

  Add a named theorem using `ext a` and `DFunLike.congr_fun` to recover a
  pointwise consequence; one using `(π : Equiv.Perm A)` and its group-coercion
  equations; and finite/empty atom specializations (`Fin 1`, `PEmpty.{u+1}`).
  Empty-atom extensionality proves every such permutation equals 1. None of
  these declarations may require `[Infinite A]`.

- [x] **Step 3: Observe the initial consumer failure.** Run
  `lake env lean /tmp/nominal-f02-f03a-execution/ActionContracts.lean`; before setup it should
  fail because `Package` is unavailable. Record that reason, not an unrelated
  syntax error. After registration, remaining red cases must identify a missing
  intended interface, never an admitted theorem.

- [x] **Step 4: Implement the subgroup and application interface.** In
  Permutation, establish moved-set identity/multiplication/inversion facts for
  raw `Equiv.Perm` first, then construct `permSubgroup`, then expose `Perm` and
  its group/function equations. Keep raw helper names inside NominalPackage.
  Use the inherited subtype coercion to `Equiv.Perm`; add no duplicate `CoeFun`
  or coercion chain. Support evidence is a proof field; do not choose a Finset.

  Start from `Mathlib.Algebra.Group.End`,
  `Mathlib.Algebra.Group.Subgroup.Defs`, and
  `Mathlib.Data.Set.Finite.Basic`; adjust direct Mathlib imports only as
  elaboration requires. `Nominal/Core/FinitePerm.lean:195–277` is reference
  material for this shape, not an import. Attribute adapted proofs.

- [x] **Step 5: Complete the moved-set and swap contract.** Prove every named
  equation in the Interfaces block, including finite moved sets, conjugation,
  both endpoint equations, third-point fixation and degenerate swaps.
  `Equiv.swap_apply_apply` states swap-of-images equals the conjugate, so use
  its symmetry for `Perm.conj_swap`. Use `Equiv.swap_apply_ne_self_iff` for
  moved points. Do not import `ClosureSwap` or add factorization theory.

- [x] **Step 6: Register and build the real target and consumer.** Add one Lake
  library entry with name Package; retain defaults/options/dependencies exactly.
  Add the production umbrella with only its actual current imports. Run `lake build Package`, then
  `lake env lean /tmp/nominal-f02-f03a-execution/ActionContracts.lean`. Expected: exit 0 and
  all named consumer proofs checked. Inspect representative `#print axioms`
  results during this task; the comprehensive audit arrives in Task 3.

- [x] **Step 7: Write the delivered permutation mathematics into the article.**
  Update the finite-moved subgroup, multiplication convention, moved-point and
  swap arguments in `foundations.tex` to match the actual declarations. Select
  details that explain the mathematical interface; omit implementation-status
  paragraphs and task identifiers. Keep operational evidence in this plan or
  the roadmap. Compile the manuscript
  with the LaTeX command in final verification; resolve diagnostics introduced
  by these edits. Review the focused diff without committing.

## Task 2: Canonical actions, equivariance and action distinctions

**Files:** Create Action and extend the public root and article sections. Extend
the temporary ActionContracts check and create a temporary NegativeContracts
check outside the repository; neither is a persistent Package module.

**Interfaces:**

- Consumes Task 1's `Perm`, application, swaps and group laws.
- Produces `Perm.smul_atom (π : Perm A) (a : A) : π • a = π a` using Mathlib's
  restricted permutation action, not a second custom atom-action instance.
- Exposes standard `one_smul`, `mul_smul`, inverse/cancellation, product
  constructor/projection and Finset empty/singleton/union equations through
  imports. Do not duplicate those generic theorems under new names.
- Produces `[DecidableEq A]` equations `Perm.smul_finset π S : π • S = S.image π`
  and `Perm.mem_smul_finset π S a : a ∈ π • S ↔ π⁻¹ a ∈ S`, in the documented
  Pointwise scope.
- Produces `structure Discrete (A : Type u) (X : Type v) : Type v` with `val : X`,
  its trivial action, `Discrete.smul_mk`, `Discrete.smul_val`, and
  `Discrete.equiv : Discrete A X ≃ X` with forward/inverse application equations.
- Produces `Equivariant (A : Type u) (f : X → Y) : Prop` under
  `[MulAction (Perm A) X] [MulAction (Perm A) Y]`, with definition
  `∀ π x, f (π • x) = π • f x`. A is an explicit input, not an outParam.
  Provide `Equivariant.id`, `.comp`, `.fst`, `.snd`, `.pair`; `.comp hg hf`
  certifies `g ∘ f`, and `.pair hf hg` certifies `fun x => (f x,g x)`.

- [x] **Step 1: Add named action consumers and observe missing-API failures.**
  Extend ActionContracts to prove pair renaming/projection and composed-map
  equivariance using the public operations, with independent carrier universes.
  Add a finite-set consumer with `open scoped Pointwise` in that file which,
  from `a ∈ S`, concludes `b ∈ Perm.swap a b • S`. Add named action laws for
  `Discrete A (PUnit.{v+1})`, `Discrete A (PEmpty.{v+1})`, and two unrelated
  atom carriers A/B in one section. Run the direct consumer; record missing
  Action/Discrete/equivariance declarations before implementing them.

- [x] **Step 2: Expose coherent standard actions.** Import the Package permutation
  module and Mathlib `Algebra.Group.Action.End`, `Algebra.Group.Subgroup.Actions`,
  `Algebra.Group.Action.Prod`, `Algebra.Group.Action.Pointwise.Finset`.
  `Equiv.Perm.applyMulAction` and the subgroup-restriction instance already
  supply the atom action. Prove its computation equation and the two finite-set
  equations; reuse `Prod.mulAction` and `Finset.mulActionFinset`.
  The latter is scoped, so document and test the consumer's scope explicitly.

- [x] **Step 3: Implement Discrete and the equivariance interface.** Keep A a
  phantom parameter, with carrier universe v. The sole new action instance is
  trivial on that distinct structure. Prove its ordinary equivalence to X but
  do not claim that equivalence equivariant to an independently acted-on X.
  Prove identity, composition, projections and pairing at independent universes.
  No support certificate or truth-action instance enters this module.

- [x] **Step 4: Add named counterexamples and a precise guarded rejection.**
  In NegativeContracts, assume `[DecidableEq A]` and `a ≠ b` where needed:

  ```text
  atomActionDiffersFromDiscrete :
    Perm.swap a b • a ≠ a ∧
    Perm.swap a b • (Discrete.mk a : Discrete A A) = Discrete.mk a
  groupActionIsNotConjugation :
    Perm.swap a b • (1 : Perm A) ≠
      Perm.swap a b * 1 * (Perm.swap a b)⁻¹
  functionActionIsPointwise :
    (Perm.swap a b • (id : A → A)) a ≠
      Perm.swap a b • id ((Perm.swap a b)⁻¹ • a)
  ```

  Define a small `ExternalData` structure, with no action, then guard the
  failure to synthesize `MulAction (Perm A) ExternalData`. Do not declare an
  axiom or install a local alternative action to make the negative examples
  work. These temporary proof checks do not enter the production audit or
  supported imports. Persistent usage examples belong to future case studies.

- [x] **Step 5: Check instance and downstream-import coherence.** Use only
  `import Package` in both consumer modules. Add named checks that scalar
  application inferred through `SMul` and through `MulAction` agrees for atoms,
  unequal-universe products, scoped finite atom sets, Discrete, functions and
  Perm itself. Use `rfl` where the instance paths are definitionally identical;
  do not hide a conflict with priorities or broad reducibility changes.
  Run `lake build Package` and both direct consumer commands;
  expected exit 0 with the guarded failure matching the intended diagnostic.

- [x] **Step 6: Update and compile the action exposition.** In foundations.tex,
  synchronize the action formulas, explicit atom parameter, independent
  universes, discrete-wrapper explanation and three negative distinctions
  with the actual public theorems. Cite their names in the implementation
  correspondence and retain support/quotients/binders as later work. Review
  the focused source/article diff without committing.

## Task 3: Coverage, axioms, mathematical correspondence and delivery

**Files:** Create AxiomAudit, check-imports.py and Package/README.md; update
article mathematical correspondence and `docs/nominal-package-roadmap.md`.

**Interfaces:**

- Consumes production root `Package` and its two foundation modules. Audit root
  is `Package.Tests.AxiomAudit`; no consumer root is required.
- Python API in the single checker file:
  `inventory(root: Path) -> dict[str, Path]`,
  `read_imports(paths: list[Path], cwd: Path) -> dict[Path, set[str]]`,
  `check(root: Path, imports: dict[Path, set[str]]) -> tuple[int, int]`,
  `self_test() -> None`, and `main() -> None`. Errors fail with a diagnostic
  naming the file/module/edge; success reports production/audit counts.
- CLI: `python3 Package/Scripts/check-imports.py` and the same with `--self-test`.
- Audit helpers (private, within AxiomAudit):
  `unexpectedAxioms (xs : Array Lean.Name) : Array Lean.Name` and
  `checkCount (production : Nat) : Except String Unit`.

- [x] **Step 1: Write the checker self-tests around its production functions.**
  Use temporary source trees, with no persistent extra harness. Require a
  successful production/audit closures, a production orphan, unclassified
  source (including an out-of-scope standalone example), missing Package import,
  forbidden reference import, production→audit edges, nested/commented-out imports, multiple valid import
  directives, `module` with `public import`, and a header-parser error.
  Test malformed JSON/result count/null result via the result-validation path.
  Observe failures before completing each corresponding validator.

- [x] **Step 2: Implement import discovery with the pinned Lean parser.**
  Batch `lake env lean --deps-json <sorted paths...>` using a subprocess argument
  list and repository cwd. Validate process status, JSON schema, entry count,
  each empty `errors` array and each non-null `result`; only then read
  `result.imports[*].module`. Deduplicate runtime/meta entries such as Init.
  The shell can return zero on file errors, so process status alone is invalid.

  This is header discovery, not a replacement for full compilation. Pinned Lean
  accepts one module identifier per import directive; multiple directives are
  supported, whereas `import A B` is a body/syntax error. Check the latter's
  expected rejection using a temporary file and direct Lean, then discard the
  fixture. Malformed/misplaced body imports are checked by the full build.
  Do not copy the old checker's narrow regex or create a second Lean parser.

- [x] **Step 3: Implement coverage and dependency policy.** Inventory every
  `Package/**/*.lean` plus `Package.lean`. Classify Package/Foundations and the
  public root as production, and the one audit module as audit. Reject any unclassified Lean source.
  Scan every file's imports before graph traversal, including orphan files;
  reject reference/research imports and missing Package targets. Only
  Package, Mathlib, Lean and Init roots are needed as direct imports in this
  increment. Production cannot import the audit. Check each category against its own root's closure, require both roots, and print the two module counts.
  Run `--self-test`, then the real checker; both must exit 0.

- [x] **Step 4: Implement and test the module-origin axiom audit.** Import
  Package and Lean.Util.CollectAxioms. Adapt the reference
  audit's environment traversal; inspect every imported Package-origin
  declaration, regardless of its namespace/private name, using `collectAxioms`.
  Use the same `unexpectedAxioms`/`checkCount` helpers in real traversal and
  simulated checks: allow the three standard names, reject `sorryAx` and a
  synthetic disallowed Name, reject a zero production count and accept a positive count.
  These are Name values, never introduced axioms. Print category declaration
  counts and contributing module counts; fail if production is absent. The current audit module's metaprogram helpers are tooling, not
  imported mathematical results to count as production coverage.

  Print representative axioms for `Perm.moved_conj`, `Perm.conj_swap`,
  `Perm.smul_atom`, `Discrete.smul_val` and `Equivariant.comp`.
  Run the direct audit after its imports have been built; expected exit 0,
  a nonzero production declaration count and no unexpected axiom dependencies.

- [x] **Step 5: Document actual usage and synchronize the LaTeX article.**
  Package/README.md records `import Package`, explicit `Pointwise` scope,
  audit commands, admitted dependencies, and the exact F03a limitation.
  In the article, replace only claims supported by this implementation with
  actual file/declaration names and verified status. Retain mathematical proofs
  as exposition, not as a substitute for Lean evidence. The manuscript must
  state that least support, predicates and the later case studies remain work
  ahead. Remove stale claims that Package is absent once it exists.

- [x] **Step 6: Run final independent-boundary verification.** Execute all
  commands below, inspect diagnostics and report the actual build/cache state.
  Resolve new warnings locally. Confirm source/import coverage and inspect
  theorem strengths, action choices and representative axiom lists together.

  ```sh
  lake build Package +Package.Tests.AxiomAudit
  lake env lean /tmp/nominal-f02-f03a-execution/ActionContracts.lean
  lake env lean /tmp/nominal-f02-f03a-execution/NegativeContracts.lean
  lake env lean Package/Tests/AxiomAudit.lean
  python3 Package/Scripts/check-imports.py --self-test
  python3 Package/Scripts/check-imports.py
  lake build Nominal Instances Examples
  lake env lean Examples/AxiomAudit.lean
  python3 scripts/check-imports.py
  git diff --check
  ```

  From `docs/article/`, also run:

  ```sh
  latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir=/tmp/nominal-package-article-build main.tex
  ```

  Ensure that output directory exists. Inspect the log for undefined references
  and layout diagnostics and inspect the rendered text/pages. Do not install or
  upgrade tools if unavailable; report that validation limit. No fresh-build
  claim is made from the baseline helper, which does not copy Package.

- [x] **Step 7: Record delivery and preserve the baseline.** Check hashes/diff
  against Task 1's baseline: only Package files/root, Lake registration,
  authorized article and package documentation may have changed. Include
  untracked files in checks. Update PKG-F02 acceptance/status only if all its
  coverage criteria pass; record F03a delivered while keeping PKG-F03 open for
  F03b. Keep F04/F05/PKG-01 incomplete. Record actual commands/counts and article
  validation in the package work log, then obtain the execution method's final
  independent review. Leave all changes uncommitted.

## Planning evidence and self-review

This plan is based on the approved spec and the current checkout at
`76966b1f2e44f594517442b6572e33abaa9038e0`. Source inspection confirmed Mathlib's
subgroup action, ordinary self/Pi actions, product and scoped Finset instances,
swap lemma orientation and Lean's discard of anonymous examples. Pinned Lake
default globs cover the root plus imports, so the explicit example/audit targets
are required. Actual `lake env lean --deps-json` inspection of three existing
files confirmed the ordered JSON schema and duplicate implicit Init entries;
that command did not elaborate their proofs or build Package.

Self-review mapping: permutation equations → Task 1; all action/universe/user
contracts and temporary negative checks → Task 2; Lake setup → Task 1; import/audit
coverage and final preservation → Task 3; article mathematics → Tasks 1/2;
article mathematical correspondence and PDF validation → Task 3. Every Review Focus item has an
owning task. Public names in temporary checks/audit refer to the Interfaces blocks.
No support theory, general function bundle, new parser framework, CI or
fresh-build helper has been introduced into the approved scope.

## Execution status

The user approved the plan and selected **native execution**. Root implements
all code; a subagent maintains the LaTeX article with disjoint ownership; one
fresh reviewer checks the complete increment. The user's later correction
removed the new Package examples directory and consumer-audit requirements.
Temporary interface checks remain scratch evidence only. No production
mathematical statement was weakened, and no additional approval is required.

All three tasks and the final independent review are complete. The review found
no Critical, Important or Minor findings. Task results and commands are recorded in
`/tmp/nominal-f02-f03a-execution/progress.md` and the package roadmap work log.
No commits, branch switches or merges are authorized.
