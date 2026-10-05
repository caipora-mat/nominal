# Nominal library roadmap and progress tracker

Last updated: 2026-10-05.

This document tracks the work needed to turn the current development into a
polished nominal library for Lean, with a lambda-calculus case study culminating
in Church–Rosser. It also records the longer path to a nominal package comparable
in purpose to Isabelle Nominal. It is a living tracker: completed work, verified
experiments, open defects, and proposed research are distinguished below.

The [2026-10-02 development review](reviews/2026-10-02-development-review.md)
records independently checked evidence, counterexamples, limitations, and release
criteria. Its finding IDs supplement, rather than replace, the task IDs here.

## 1. Agreed objectives and boundaries

- First deliverable: a reusable classical nominal library and a complete,
  readable lambda-calculus Church–Rosser development.
- Immediate priority, clarified during review: clean up the existing development,
  address the gaps needed by the lambda proof, and finish Church–Rosser. Learn
  the requirements for later metaprogramming/algebraic infrastructure from that
  case study; do not build a general package before completing it.
- Intended experience: reasoning about syntax and semantics with binders using
  justified Barendregt Variable Convention principles, close to pen-and-paper proofs.
- First binding scope: one atom sort, single binders, and nested binders.
- Classical reasoning, quotients, and noncomputable semantic operations are
  acceptable. Executable substitution and fresh-name generation are not release
  requirements.
- `NFun` usability is a major priority. The author's main pain is using nominal
  functions as ordinary functions: coercions, currying, composition, and rewriting.
  First-release expectations are reliable interfaces and focused support automation.
  Substantial general metaprogramming belongs later in the roadmap; it is not a
  prerequisite for starting or finishing the Church–Rosser proof.
- Generic initial-algebra theory is primarily a means to usable datatype generation.
  There is no deadline; prioritize correctness and evidence from actual clients.
- Work branch: `fasapa/next`. Preserve existing work and record integrations explicitly.
- Murillo's syntax and nominal-unification branch is outside this roadmap's scope.
- The raw `Nominal.Syntax` sketch is excluded from `fasapa/next` for now at the
  author's request. Its umbrella and two source modules are removed; the separate
  lambda-calculus case study remains supported.
- **CI is not required.** Validation uses local builds, compiling examples,
  targeted regression checks, and proof-dependency inspection. No task below
  requires introducing, extending, or removing CI workflows.
- Multiple atom sorts, simultaneous/generalized binders, dependent syntax, and
  a general datatype command are later work. They must not indefinitely delay
  the first finished research deliverable.

## 2. How to maintain this tracker

Each task has a stable ID. Preserve IDs when reorganizing the document so reviews,
commits, and discussion can refer to the same work.

Status vocabulary:

| Status | Meaning |
| --- | --- |
| DONE | The stated result was verified in the stated location; inspect the evidence before reusing it. |
| TODO | Work has not been completed. |
| IN PROGRESS | An owner is actively working on a concrete result; add a work-log entry. |
| BLOCKED | A specific unmet dependency prevents progress; name it and the unblocking action. |
| DEFERRED | Deliberately outside the first release; not an accidental omission. |

Use `[x]` only for a verified completed item. Unchecked items include both TODO and
DEFERRED work, distinguished by their parent task. A passing experiment is not
integration into `fasapa/next`. Compilation is not evidence that a theorem states
the intended mathematics, and source inspection is not a successful build.

When completing a task:

1. Record the declarations/files changed and the behavior or theorem delivered.
2. Record the command and result, or the specific mathematical review evidence.
3. State whether the work is in this branch, another branch, or a scratch copy.
4. Record commit IDs when available; do not describe uncommitted work as committed.
5. Update dependent tasks, the dashboard, and the work log. Record remaining
   limitations instead of silently weakening the completion criterion.

New findings should carry severity, evidence, practical impact, a suggested fix,
and a task ID. Distinguish confirmed defects, missing features, ergonomic problems,
research questions, and optional cleanup. Do not assign artificial completion
percentages to research problems.

## 3. Dashboard and dependency order

| Workstream | Current state | Completion condition |
| --- | --- | --- |
| B — Baseline and integration | B-01–B-05 complete in the delivered working tree | Complete local commands, persistent examples and fresh project-artifact validation |
| C — Core reliability | C-01–C-03 and C-05–C-07 complete for the first client; C-04 broader wrappers deferred | Contracts, coherence, hypotheses and limits demonstrated; no unused container expansion |
| N — Nominal-function interface | N-01–N-05 already integrated at `5434d4e`, revalidated by task 9 | Tutorial and persistent ordinary-function consumers; explicit proof escape hatches |
| M — Nominal-function metaprogramming | Focused support certificates and guarded prototype subset delivered; general elaboration deferred | Focused support automation for release; general infrastructure informed by the case study later |
| L — Lambda interface | L-01–L-03 complete for the first deliverable | Public quotient syntax, arbitrary-predicate induction, supported iteration/uniqueness and substitution laws |
| R — Reduction and Church–Rosser | R-01–R-07 complete | Open contextual results, client-boundary review, compiling tutorial and audits |
| D — Documentation and first release | D-01/D-02 delivered; D-03 correspondence recorded with external verification pending; D-04 local first-deliverable readiness complete | See task-9 delivery record; no commit, publication or external correction claimed |
| A — Generic algebraic construction | Sketch with placeholders and design defects | Correct signature semantics, carrier, induction, recursion |
| P — Generated nominal package | Future work | Verified generation of a supported class of binder datatypes |

Current dependency order after task 9:

1. B/C/N/L first-deliverable interfaces and R-01–R-07 are delivered; validate the
   complete source and examples with [local commands](validation.md).
2. D-01/D-02 provide the compiling tutorial and current documentation. D-04's
   readiness record distinguishes the uncommitted deliverable from publication.
3. D-03 still needs compatible external Rocq builds/assumption reports and
   separately authorized manuscript corrections. The pinned correspondence
   account does not claim those checks have been performed.
4. Use the completed client to guide later M, then A/P work. General elaboration,
   generic algebraic construction, multiple atom sorts and generalized binders
   remain deferred; no such work blocks this local first deliverable.

The task-9 [assessment and checklist](release-assessment.md) records why the
remaining interface work was justified. Confluence alone did not discharge it.

## 4. Evidence inventory

### Inspected revisions

| Source | Revision/location | Evidence |
| --- | --- | --- |
| Lean master | `1646471e9c2f36303fb087a933ff85ee73382d74` | Source review; original 4.28 build passed |
| Lean lambda experiment | `9f04655` on `origin/fasapa/lambda-calculus` | Source review; separate migrated 4.34.1 build passed |
| Lean algebraic sketch | `983adeb` on `origin/fasapa/algebraic` | Source review; direct import failures and separate normalized experiments, not a verified branch build |
| Historical freshness-task snapshot | `fasapa/next`, integrated baseline `62b945a`, with then-uncommitted C-01/C-02 repairs | Lambda integration was already present; this row records the earlier freshness task, not task-9 state |
| Task-9 deliverable | `fasapa/next`, `b74ad349fa1b0e77dbb59b8225abe84be8e5b617` plus uncommitted cleanup | Integrated Church–Rosser, public iterator contracts, compiling tutorial, module-origin axiom audit and complete local validation; see task-9 delivery record |
| Rocq main | `78f41a6c7ca1b55814b7b7c7d734ad4decaac523` | Source review; not rebuilt |
| Rocq article tag | `lsfa2025`, `fc7b95a47539fa2dc39f41f293c7d943a0d8b22d` | Source review: lambda/substitution text already present; two active permutation-instance admissions, filled in main |
| Article repository | `8c8c05d25f0918280fa2446a9ee78921bf9a8fa4` | Local TeX review and comparison with published paper |

The lambda and algebraic tips were respectively two commits and one commit ahead
of the inspected master. Recheck branch tips before future integrations.
The remote tips above were checked again during the development review.

### Proven infrastructure already present

| Area | Main files | Results to preserve and reuse |
| --- | --- | --- |
| Atoms and permutations | `Nominal/Core/Name.lean`, `FinitePerm.lean` | Parametric infinite atoms, finite permutations, swap factorization |
| Actions and equivariance | `Nominal/Set/PermType.lean`, `PFun.lean`, `Equivariant.lean` | Canonical actions, conjugation on functions/permutations, equivariant maps |
| Support and freshness | `Support.lean`, `Nominal.lean`, `Freshness/Basic.lean` | Least support, exact formulas, fresh names, support transport |
| Quantification | `FreshQuantifier.lean` | Cofinite quantifier, Some/Any, total and partial freshness theorems |
| Quotients and abstraction | `EquivalenceClass.lean`, `NameAbstraction.lean` | Equivariant quotients, abstraction equality, fresh representatives, support deletion |
| Binder elimination | `Concretion.lean`, `FCB.lean` | Concretion, abstraction maps/extensionality, FCB lifting, parameterized lifting |
| Supported functions | `NFun.lean`, `NFun/{Basic,Tactic}.lean` | Application, extensionality, composition, products, evaluation, currying, support bounds |
| Integrated lambda case study | `Instances/LambdaCalculus/{Basic,Induction,Recursion,Substitution}.lean` | Alpha quotient, support/free variables, strong term induction, recursion, substitution composition |

All paths above are now present in the `fasapa/next` working tree. `NFun.lean`
is the compatibility umbrella importing `NFun/Basic.lean` and `NFun/Tactic.lean`.
The latter includes the explicitly experimental `nfun` macro; its known failures
remain open, and proof-backed constructors remain available.

### Validation already obtained

- Original master: `lake build` passed on Lean/Mathlib 4.28.0, 977 jobs.
- Current core: `lake build` passed on Lean/Mathlib 4.34.1, 1003 jobs, including
  meaningful explicit-freshness regression examples. Style/reducibility warnings remain.
- Separate lambda export: `lake build Nominal Instances` passed on 4.34.1,
  1014 jobs, after compatibility fixes. This was separate-export evidence;
  subsequent working-tree integration is recorded below.
- `git diff --check` passed for the migration changes.
- Representative core results `supp_supports`, `someAny`, `supp_abs`, and
  `liftFCB_abs` depend only on `propext`, `Classical.choice`, and `Quot.sound`.
- The same axiom result was obtained for migrated lambda results `strong_ind`,
  `recNoContext_lam`, `subst_subst`, and `supp_eq_fv`; no `sorryAx` occurs in them.
- Scratch checks validated action-instance coherence, basic `NFun` usage, and the
  remaining automatic-freshness/nested-splitting limitations.
- Independent review found no concrete migration defect. Additional tests of the
  explicit-freshness fix covered four arguments, duplicates, mixed type/term
  expansion, and locals named like the tactic's internal variables.

These are recorded results from the initial assessment, not a claim that every
future working-tree state has been checked. Scratch files under `/tmp` are not
persistent project tests; promote important examples into the repository.

### Independent development review, 2026-10-02

The detailed [review](reviews/2026-10-02-development-review.md) independently
reproduced fresh project-artifact builds: core 1,003 jobs and migrated lambda
1,014 jobs, reusing cached pinned dependencies. This is not a clean-machine
dependency-bootstrap test or lambda integration. A project-namespace axiom sweep
checked 1,165 core declarations and 1,581 migrated core/lambda declarations with
no dependencies beyond `propext`, `Classical.choice`, and `Quot.sound`.

Confirmed findings and dispositions:

| Review findings | Evidence/remaining task |
| --- | --- |
| T-01/T-02/T-04 | `choose_fresh` loses shadowed locals in type expansion and automatic mode; scanning misses atoms/derived instances; single-result names differ from docs. Reproduced and repaired in C-01 below; original review evidence is retained. |
| T-03 | Unnamed splitting leaves nested conjunctions; named splitting fails on left-associated products. Reproduced and repaired in C-02 below; original review evidence is retained. |
| N-01/N-02/N-03 | Basic NFun application/coercion/curry works; uncurry/adapters need polish. Prototype macro fails on globals, let/match/nested scope and advertised syntax. N/M remain TODO. |
| L-01/L-02/L-03 | Quotient inversion and binder compatibility now delivered by roadmap L-01/R-01. Supported iterator polish, reduction, rule induction, and confluence remain open. |
| P-01 | Removing `seal Fresh in` reproduces a 200,000-heartbeat timeout; removing only `seal subst` passes on 4.34.1. Preserve boundaries pending targeted work; qualify the old necessity claim. |
| A-01 through A-09 | Existing signature defects reconfirmed; additional arbitrary-action support and bare-equivalence/product errors found. Algebraic work stays deferred. |
| H-01 through H-07 | Paper/draft corrections and versioned Rocq assumptions need reconciliation; no external source was modified. D-03 remains TODO. |

No mathematical theorem defect was found in the integrated core or migrated
lambda theory. Kernel-checked counterexamples establish that least support is
not strong support and that fixed-parameter substitution need not be equivariant.
Rocq `make` stops at missing `coq_makefile`; Rocq assumption printing, TeX builds,
and Isabelle builds were not performed. Those limits are not completed tasks.

### Initial integrated working-tree validation, 2026-10-02

This records the initial uncommitted integration on `fasapa/next`, before the
subsequent warning cleanup and raw Syntax removal recorded below. It is not merely
a repeat of the separate lambda export. Source tips remain core `2c45db8` and lambda
`9f04655`. Lean/Mathlib pins and the manifest remain at 4.34.1.

| Check | Result |
| --- | --- |
| `lake build` | Passed, 1,012 jobs; default targets include `Nominal` and `Instances` |
| `lake build Nominal Instances` | Passed, 1,012 jobs |
| Both commands in a fresh source/config copy | Passed, 1,012 jobs each; fresh project artifacts, cached pinned dependencies |
| Import closure from both supported roots | 32/32 source modules reached, including both NFun modules and all four lambda modules |
| Core and freshness consumers | Passed: coercion/composition/curry/extensionality, action coherence, four explicit fresh inputs, duplicates, mixed type/term expansion, hypothesis naming |
| Computational NFun checks | `const` and `comp` evaluations both returned `7` |
| Lambda and FCB consumers | Passed: nested NFun extensionality, equivariant constructor, shadowing, capture-avoiding substitution requiring binder renaming, total/guarded FCB independence |
| Headline `#print axioms` | `strong_ind`, `RecRel.unique`, `recNoContext_lam`, `subst_subst`, `supp_eq_fv`, `NFun.curry_eval`, core support/abstraction/FCB lifting, and both new FCB results use only the standard three axioms |
| Broad `Lean.collectAxioms` sweep | 1,636 declarations; zero dependencies beyond `propext`, `Classical.choice`, `Quot.sound` |
| Admission/check-bypass source scan | No active admissions, custom axioms, unsafe declarations, or kernel-check bypasses found in supported sources |
| Final diff review | `git diff --check` and new-source whitespace checks passed; independent code review found no actionable regressions; original freshness tactic, shared migration fixes, toolchain/manifest, `.codex/`, and dated review were preserved |

The broad sweep explicitly imports **both** `Nominal` and `Instances`, selecting
`Nominal.`, `_private.Nominal.`, `LambdaCalculus.`, and `_private.Instances.`.
The prior lambda-only scratch sweep did not import `Nominal.Syntax`; its historical
1,581 count is not the integrated full-closure count. The new temporary audit fails
if any unexpected dependency is found, including `sorryAx`.

Temporary evidence: `/tmp/nominal-integration.rqa1ks9r/` contains the fresh copy,
module inventory, `CoreExamples.lean`, `FreshnessExamples.lean`, `LambdaExamples.lean`,
`FCBExamples.lean`, and `Axioms.lean`. Each probe was run with `lake env lean`.
Build logs are `/tmp/nominal-integration-build.log`,
`/tmp/nominal-integration-explicit-build.log`,
`/tmp/nominal-integration-fresh-build.log`, and
`/tmp/nominal-integration-fresh-explicit-build.log`; the broad sweep is recorded in
`/tmp/nominal-integration-axioms.log`. These temporary files are not a persistent
validation target or a clean-environment dependency-bootstrap test.

### Warning cleanup and raw Syntax exclusion, 2026-10-02

The author requested warning cleanup before committing and then excluded the raw
`Nominal.Syntax` sketch from this branch. `Nominal/Syntax.lean` and its `LPerm`/`Terms`
modules are removed, along with the root import. No supported core or lambda module
depended on the sketch. The lambda case study and its public theorem statements remain.

The previous default build emitted 32 warnings. Their dispositions are:

- Deprecated lambda tactic/theorem names use `push Not`, `Set.mem_ofPred`, and
  `ite_eq_right`; theorem statements and freshness hypotheses are unchanged.
- Six explicit discrete-action/nominal structures now have `@[instance_reducible]`.
  They remain opt-in definitions, not global instances; consumer checks verify
  instance search does not select them automatically and their actions still compute.
- The established `Nominal.Set.Nominal` name is intentional. Only the class command
  and its own namespace disable `linter.dupNamespace`, with an inline explanation.
  Independent review checked restoration after `end Nominal`. Other linters remain active.
- Proof-local instance bindings use `let` where inlining is unnecessary. The redundant
  `rw`/`assumption` sequence uses `rwa`, removing the informational suggestion.
- Missing-header warnings belonged to the raw Syntax files, which are now excluded.

Final validation: `lake build` and `lake build Nominal Instances` both passed with
**zero warnings**, 1,009 jobs each, in both the working tree and a fresh project-artifact
copy with cached pinned dependencies. The final import closure reaches **29/29** modules.
The both-root axiom sweep checked **1,581** declarations with zero dependencies beyond
`propext`, `Classical.choice`, and `Quot.sound`; the lower count reflects Syntax removal.
Headline axioms and the NFun, freshness, FCB, shadowing/capture-avoidance examples all
passed again; computational NFun examples still return `7`. `git diff --check` passed.

Logs: `/tmp/nominal-warning-final-{build,explicit-build,fresh-build,fresh-explicit-build}.log`
and `/tmp/nominal-warning-final-axioms.log`. The final fresh copy, module inventory,
and discrete-structure probe are under `/tmp/nominal-warnings.sbyvaqaj/`.
The same temporary integration consumer probes were rerun. No commit or push was made.

## 5. B — Baseline and integration

### B-01 — Upgrade the core [DONE]

- [x] Pin Lean and Mathlib to stable v4.34.1 and regenerate `lake-manifest.json`.
- [x] Adapt `DFunLike.coe_injective` and deprecated imports/theorem/tactic names.
- [x] Preserve conjugation on finite permutations despite Mathlib's higher-priority
  multiplication action, with coherent `SMul` and `MulAction` instances.
- [x] Preserve computational `NFun.const` and `NFun.comp` by keeping least-support
  witnesses inside erased proof fields.
- [x] Repair quotient proof elaboration without changing public mathematical statements.
- [x] Build the core and review the migration independently.

Evidence: validation inventory above; recorded in commit `2c45db8` and independently
rebuilt during review. Future version upgrades should be separate, verified changes.

### B-02 — Repair explicit fresh-name selection [DONE]

- [x] Reproduce failure of `choose_fresh a from b` for an atom `b`.
- [x] Generate direct membership proofs into the left-associated support union,
  avoiding simplification of the supports themselves.
- [x] Add single-atom and mixed atom/body examples consuming all generated facts.

Files: `Nominal/Set/Freshness/Tactic.lean`, committed in `2c45db8`. This narrow fix
does not fix automatic scanning, shadowed-local identity during type expansion,
or recursive splitting; those were subsequently repaired by C-01 and C-02 below.

### B-03 — Verify the lambda migration separately [DONE]

- [x] Port a separate lambda-branch export to 4.34.1 without changing theorem statements.
- [x] Build both `Nominal` and `Instances` and inspect headline theorem axioms.
- [x] Save the source migration patch during the separate verification (historical).

The separately verified migration targeted lambda commit `9f04655` with the
4.34.1 toolchain and matching Mathlib manifest. The author subsequently deleted
the saved patch; it is not a current repository artifact or build dependency.
B-04 records the integrated source and its independent validation.

### B-04 — Integrate the lambda results [DONE]

Dependencies: B-01, B-03. Locations: `Nominal/Set/*`, `Instances/*`, `lakefile.toml`.

- [x] Compare current branch tips and distinguish shared fixes from branch-only changes.
- [x] Integrate reusable freshness, swap, abstraction, and FCB lemmas.
- [x] Integrate the four lambda modules and their umbrella imports.
- [x] Reconcile the `NFun` split without losing the current computability fixes.
- [x] Review newly public FCB helper declarations; expose a deliberate supported API.
- [x] Keep the experimental `nfun` macro's limitations explicit.
- [x] Build `Nominal` and `Instances` together and recheck headline theorem dependencies.

Done when: the checked lambda case study is part of `fasapa/next`, with its
integration revision and successful local commands recorded.

Evidence (2026-10-02): uncommitted `fasapa/next` working tree based on `2c45db8`,
with lambda source `9f04655`; local and remote tips were rechecked before validation.
The four case-study modules and both umbrellas are integrated. The current
freshness tactic/regressions, conjugation priorities, quotient compatibility,
and computational `NFun.const`/`comp` constructions are preserved.

Public additions include `mul_swap_conj`, `fresh_of_supp_subset_finset`,
`NameAbs.abs_eq_mp_at`, `abs_eq_of_swap`, `abs_unique_parametric`, and
`FCB_total_val_indep`/`FCB_guarded_val_indep`. The two FCB statements preserve their
freshness/support hypotheses. Existing FCB implementation helpers remain private;
`freshQuantifier_smul_shift` also retains its existing privacy. NFun gains the
branch's notation, `ofCaptures`, `equivariant`, and FCB support facilities, with
its Basic/Tactic split and legacy umbrella. `nfun` behavior is unchanged and its
actual syntax and limitations are documented. No `NFun.fromParam` declaration
exists in the integrated source; the dated review's mention is not an API promise.

Both default and explicit builds passed, complete source coverage was checked,
and consuming examples/headline axioms passed; see the integrated validation
record in section 4. No reduction, Church–Rosser, unrelated tactic repair, general
elaborator, algebraic infrastructure, CI, commit, or push is part of this integration.

### B-05 — Make local validation complete and reproducible [DONE]

Dependency: B-04. Locations: `lakefile.toml`, README, a small local examples/test target.

- [x] Include both supported libraries in default local builds, or document an
  equally explicit command that cannot silently omit the case study.
- [x] Establish a persistent target for important usage/regression examples.
- [x] Document clean-environment dependency setup and build commands.
- [x] Confirm every supported source module is reached by an intended build target.
- [x] Classify remaining warnings; fix genuine problems and document deliberate design choices.

Done when: another developer can verify all supported code locally from the
tracked files and pinned dependencies. No CI service or workflow is required.

Task-9 delivery: default `Nominal`/`Instances` and the explicit `Examples`
umbrella reach every supported source. The coverage audit discovered and added
previously orphaned `LambdaConstructors` and `LambdaInterface` examples, along
with `Tutorial`, `CoreContracts`, and `AxiomAudit`. `scripts/check-imports.py`
checks the closure (37 library modules, 15 example modules including umbrellas).
[Validation instructions](validation.md) include pinned dependency setup and
`scripts/fresh-build.py`, which rebuilds current source with fresh project
artifacts and cached dependencies. A clean dependency bootstrap was **not run**;
the setup documentation and fresh-project evidence must not be described as one.
The delivered source/documentation remains uncommitted by request.

## 6. C — Core reliability and mathematical interface

### C-01 — Reliable automatic `choose_fresh` [DONE]

Dependency: B-02. File: `Nominal/Set/Freshness/Tactic.lean`.

- [x] Select the intended atom type consistently and diagnose ambiguous contexts.
- [x] Discover candidate locals using instance synthesis, including atom-only
  contexts and derived products, abstractions, and nominal functions.
- [x] Preserve `FVarId`/expression identity instead of reconstructing locals from
  `userName`; cover shadowing in both automatic mode and explicit `from X` expansion.
- [x] Skip irrelevant/auxiliary declarations and prevent speculative elaboration
  from leaking metavariable assignments into the proof state.
- [x] Preserve explicit `from`, type expansion, duplicates, and hypothesis naming.
- [x] Align documentation with the actual generated names, including the single-item case.

Done when: examples require and obtain freshness for every requested object;
negative cases report a useful reason instead of silently suggesting all locals
were covered.

Delivered in the uncommitted working tree based on integrated `62b945a`:

- Both automatic scanning and `from X` preserve elaborated expressions/FVarIds,
  including same-name locals with the same or different types. Explicit expressions
  are elaborated once; mixed type/term expansion, input order, and duplicates remain.
- Candidate discovery synthesizes `Nominal` instances, including atoms, products,
  abstractions, and NFuns. Registered local `Name`/`Nominal` instances and ordinary
  instance inference supply candidate atom types. Automatic mode requires one active
  sort; explicit mode requires one common sort for all inputs. Unused sorts are harmless.
  Conflicting local instances are checked even through derived products: fixed-sort
  checks filter incompatible local nominal instances, and proof generation retains
  the selected instances as well as the original object expressions.
- Speculative checks restore metavariable state. Scans/type expansion skip auxiliary
  and implementation declarations, instance/class declarations, proofs, types, and
  locals with unresolved expression metavariables in their types. Explicit terms
  must elaborate and have suitable nominal instances.
- Names are consistently `aFresh1`, … or `h1`, … with `with h`, including a single
  input. Atom/hypothesis collisions, empty selections/type expansions, incompatible
  inputs, and atom ambiguity produce diagnostics; no silent renaming of chosen names.

Verification: `Examples/Freshness.lean` contains consuming theorems for all these
paths, exact-message negative tests, and tests injecting unresolved/auxiliary locals.
See the shared verification record below. Remaining limits: ordinary global instance
priorities apply; alternative global instance derivations are not exhaustively searched.
The tactic does not solve unresolved local types or implement multi-sort freshness.

### C-02 — Complete and predictable `split_fresh` [DONE]

File: `Nominal/Set/Freshness/Tactic.lean`. Independent of C-01.

- [x] Recursively expose every freshness leaf in nested products on either side.
- [x] Define behavior for explicit names, name-count mismatches, and nonsplittable inputs.
- [x] Replace or supplement `True`-valued examples with proofs using every leaf.
- [x] Check nested tuples, existing similarly named hypotheses, and mixed left/right products.
- [x] Cover both conjunction associations: the flat named form previously failed on
  left-nested products, independently of the unnamed form's shallow splitting.

Done when: unnamed and named forms satisfy their documented behavior.

Delivered in the same uncommitted working tree:

- Recursive theorem applications expose every leaf of left/right-associated products
  on either side, including product-valued variables. Reducible freshness predicates
  are recognized, and concrete projections reduce to their components so downstream
  rewriting (including existing FCB clients) continues to work.
- Ordering is right-side components first, then left-side components, each left to
  right: `(a,b) # (c,d)` yields `a # c`, `b # c`, `a # d`, `b # d`.
- Unnamed output is `h_1`, `h_2`, …, skipping occupied names. Explicit names must
  match the leaf count exactly and be distinct and unused (including the source name).
  Too few/many names, collisions, duplicates, non-freshness inputs, and freshness
  without products are errors. The source is cleared unless another declaration or
  the goal depends on it, in which case it is retained.
- Persistent proofs consume all leaves for both associations, both sides, product
  variables, collisions, and dependent-source retention; negative tests pin diagnostics.

Remaining limits: splitting uses the standard nominal product instances and freshness
lemmas; it is not a general conjunction/destructuring or arbitrary-action tactic.

#### C-01/C-02 verification record — 2026-10-02

The defects were reproduced against the integrated baseline before editing the tactic.
The original shadowing failures, missed atom/derived locals, shallow unnamed splitting,
and left-associated named failure are retained in the scratch log
`/tmp/nominal-freshness-before.log`; the single-item indexed convention was confirmed
and its documentation corrected. The dated development review remains historical.

Persistent validation: `Examples.lean`, `Examples/Freshness.lean`, and the explicit
`Examples` target in `lakefile.toml`. The 39 named theorems use the resulting facts or
check negative behavior inside completed proofs. Their in-file axiom audit rejects
anything beyond `propext`, `Classical.choice`, and `Quot.sound`. The earlier `True`-valued
smoke tests in the tactic module are replaced by this consumer suite.

| Check | Result |
| --- | --- |
| `lake env lean Examples/Freshness.lean` | Passed, including diagnostic/state-isolation checks and the example axiom audit |
| `lake build Examples` | Passed, 1,004 jobs, no warnings |
| `lake build Nominal Instances Examples` | Passed, 1,012 jobs, no warnings; both supported libraries and the regression target |
| Broad `Lean.collectAxioms` sweep importing `Nominal`, `Instances`, and `Examples` | 1,623 project/example declarations; no dependencies beyond the standard three axioms |
| Admission/kernel-bypass source scan | No admissions, custom axioms, unsafe declarations, or kernel-check bypasses in supported sources/examples |
| Larger consuming probes, default proof heartbeat limits | 16 explicit/automatic inputs: 1.51/1.44 s; 64: 4.70/4.52 s; 64 split leaves (8×8): 1.26 s; all passed |
| Final whitespace/diff review | `git diff --check` and new-file whitespace checks passed; focused independent code review found no remaining blocker |

Timings include process startup and are local spot checks, not a complexity guarantee.
The support-union membership construction remains quadratic in the number of selected
inputs. Splitting produces the Cartesian product of leaves when both sides are products.
No proof heartbeat increase, admission, new axiom, dependency upgrade, CI, integration,
commit, or push was introduced. Builds reuse pinned cached dependencies; clean-machine
bootstrap remains B-05 work. The default targets remain `Nominal` and `Instances`;
run `lake build Examples` explicitly for regressions.

Temporary broader evidence: `/tmp/NominalFreshnessAxioms.lean`,
`/tmp/nominal-freshness-axioms.log`, `/tmp/nominal-freshness-build.log`, and
`/tmp/nominal-freshness-performance.log`. The proof-dependency sweep's unlimited
heartbeat setting applies only to audit traversal, not to library/example proofs.

### C-03 — Supply instances needed by actual client proofs [DONE — client inventory; extensions DEFERRED]

Dependencies: completed L/R clients. Locations: `PermType.lean`, `Nominal.lean`,
`Examples/CoreContracts.lean`, and the lambda consumers.

- [x] Identify the actual contexts: atoms, products and finite atom sets suffice
  for the completed open-term confluence proof and tutorial.
- [x] Verify existing action/support/freshness behavior and definitional projection
  coherence for these contexts, supported functions, abstraction and quotients.
- [x] Record that no new list/discrete/container instance is required by this client.
- [ ] DEFERRED: general containers, invariant subtypes and finite maps; supply
  laws and exact support/freshness formulas when a concrete client requires them.

Done criterion met for the first client: representative contexts work without
ad hoc infrastructure. Unit/Bool nominal structures remain explicit choices;
Nat/Int have explicit permutation actions, not general nominal instances.

### C-04 — Bridge Some/Any and freshness interfaces [DEFERRED — broader wrappers; client subset delivered]

Files: `FreshQuantifier.lean`, `FCB.lean`; consume existing Some/Any and support results.

- [ ] Derive convenient Some/Any formulations for supported predicates and fixed parameters.
- [ ] Provide all-fresh-input computation and pairwise independence corollaries
  for the total/partial freshness theorem where not already available.
- [ ] Connect cofinite FCB assumptions with suitable fresh-witness formulations.
- [x] Document when disjunction, negation, and implication laws require finite/cofinite
  hypotheses; do not present unrestricted cofinite quantification as self-dual.

Done when: the practical formulations used in Rocq/paper proofs can be invoked
without manually rebuilding finite-exception sets. Check for existing equivalents first.

Task-9 inventory: `someAny_exists`, `someAny_forall`, and
`someAny_forall_of_exists` already handle equivariant relations with fixed nominal
parameters collected in a product. `Examples/CoreContracts.lean` demonstrates
these without rebuilding exception sets; module docs explain finite/cofinite
Boolean hypotheses. Broader supported-predicate adapters, all-fresh total/partial
freshness computation and FCB fresh-witness wrappers remain optional later API
work, unused by the confluence client. This task is not marked complete.

### C-05 — Audit public theory, assumptions, and coherence [DONE]

Files: all `Nominal/Core` and `Nominal/Set` modules. Can proceed alongside N/L/R.

- [x] Review statements as well as proofs: support minimality versus strong support,
  freshness hypotheses, empty domains, nonempty assumptions, and totality requirements.
- [x] Inspect exported theorem axioms and distinguish standard foundations from admissions.
- [x] Review priorities and definitional equality of action projections, especially
  finite permutations, `PFun`, `NFun`, products, and quotient instances.
- [x] Check theorem names, duplicate results, unnecessary assumptions, and simp loops.
- [x] Document why ordinary function actions and conjugation wrappers remain distinct.

Done when: concrete findings have fixes or explicitly justified dispositions,
with no silent weakening of theorem statements or addition of unproved assumptions.

### C-06 — Clarify abstraction and binder elimination [DONE]

Files: `NameAbstraction.lean`, `Concretion.lean`, `FCB.lean`.

- [x] Correct documentation that confuses a different binder with a nonfresh atom:
  concretion at a different fresh atom returns a renamed body.
- [x] Identify the smallest useful public interface for equality, fresh representatives,
  concretion, FCB independence, lifting, and uniqueness.
- [x] Provide small examples using parameterized lifting and explaining its hypotheses.
- [x] Reuse existing results instead of reproving lambda-specific copies where practical.

Done when: users can eliminate an abstraction with explicit, understandable obligations,
without depending on implementation details of the quotient or lifting construction.

### C-07 — Record generality limits [DONE for first release; extensions DEFERRED]

- [x] Document the default atom/action choice induced by `outParam`.
- [x] Document shared-universe restrictions in generic equivariant quotient
  instances, abstraction, concretion, and FCB.
- [ ] DEFERRED: identify a concrete larger-universe or multi-sort example before changing APIs.
- [x] Defer universe generalization and tagged/multiple atom sorts unless they block
  an agreed first-release client.

Done for the first release when: limitations are accurate and examples remain
within them. Generalization is a separate later task, not an implicit release blocker.

## 7. N — Natural use of nominal functions

This workstream addresses the primary reported pain before attempting broad
capture inference. Existing `NFun` application, composition, currying, nested
`ext`, and higher-order use were verified before changes and are now persistent examples.
The objective is a coherent, discoverable interface, not a claim these operations
are entirely absent.

### N-01 — Establish usage benchmarks [DONE]

Delivered in `Examples/NFun.lean`, `Examples/NFunSupport.lean`, and
`Examples/NFunLambda.lean`, imported by the existing `Examples` target.

- [x] Preserve working examples of application, function coercion, nested `ext`,
  composition, and currying.
- [x] Record failing or awkward examples for uncurrying, partial application,
  passing NFuns to ordinary higher-order lemmas, and rewriting function equality.
- [x] Include concrete substitution handlers and binder-recursion clients.
- [x] Record annotation burden, wrapper exposure, error quality, and representative
  elaboration cost before changes; compare the same examples afterward.

Done when: improvement can be judged from concrete Lean programs and proofs,
with successful behavior and limitations both documented.

### N-02 — Coercion, extensionality, and rewriting interface [DONE]

Dependency: N-01. Files: `PFun.lean`, `NFun.lean` or integrated `NFun/Basic.lean`.

- [x] Choose and document normal forms for applications and function coercions.
- [x] Add missing bridge lemmas for coercions of composition, currying, and constructors.
- [x] Make equality-to-pointwise reasoning discoverable: `DFunLike.congr_fun` works
  on NFun equality where ordinary `congrFun` expects equality of plain functions.
- [x] Verify rewriting beneath ordinary lambdas and in higher-order arguments.
- [x] Preserve `ext x y` for nested NFuns; add a new tactic only if it solves an
  identified problem beyond existing extensionality support.
- [x] Orient simp lemmas to terminate and avoid repeatedly crossing wrapper boundaries.

Done when: benchmark proofs routinely use application, `simp`, `rw`, and `ext`
without exposing structure fields or support certificates.

### N-03 — Uncurrying, partial application, and composition [DONE]

Dependencies: N-01, N-02.

- [x] Provide a public `uncurry` interface, its application equation, and inverse laws
  with the existing `curry`, reusing the evaluation/composition infrastructure.
- [x] Expose appropriate support bounds and equivariance facts for these operations.
- [x] Provide convenient partial application of nominal and jointly equivariant functions.
- [x] Add an unambiguous composition interface or notation if the benchmarks justify it.
- [x] Verify behavior with captured parameters, empty domains where relevant, and
  higher-order nominal results; preserve genuinely necessary nonempty hypotheses.

Done when: moving between pair-based and curried handlers is routine and coherent
with ordinary function equality and composition.

### N-04 — Equivariant and supported function adapters [DONE]

Dependencies: N-02, N-03. Files: `Equivariant.lean`, `NFun` modules.

- [x] Inventory existing constructors/adapters and identify only the missing conversions.
- [x] Support the common path from a jointly equivariant operation to a supported
  operation with fixed nominal parameters.
- [x] Supply application, support, and freshness lemmas for each public adapter.
- [x] Keep fixed-parameter support distinct from empty-support equivariance.
- [x] Avoid a global conjugation instance on ordinary function spaces that conflicts
  with pointwise actions.

Done when: clients can cross the ordinary/equivariant/supported interfaces with
explicit mathematical meaning and little repetitive boilerplate.

### N-05 — Control unfolding and elaborate efficiently [DONE]

Dependencies: N-01 through N-04; coordinate with L-03 and M.

- [x] Preserve existing `seal` boundaries until replacements are justified by measurements.
- [x] Expose computation lemmas so proofs do not unfold the recursion construction.
- [x] Keep noncomputable support witnesses in proof fields when an operation's data
  component is computable; do not label every adapter noncomputable unnecessarily.
- [x] Profile concrete slow examples; replace brittle broad automation with focused lemmas.
- [x] Document required type annotations and remove them only when inference stays predictable.

Done when: the benchmark suite is stable and performance improvements are
supported by observations rather than speculative global option changes.

Review evidence: removing only `seal Fresh in` from the migrated substitution
module reproduces a default-heartbeat timeout; removing only `seal subst` passes
on 4.34.1. The old claim that both are necessary must be qualified, without
silently removing either boundary. Explicit fresh-selection probes at 4/16/64
arguments pass; their single-run timings are recorded in review finding P-01.

### N-01–N-05 delivery evidence, 2026-10-02

These are uncommitted changes based on `0277d3d`, layered over the ongoing
L-01/R-01 work. The representation, `FunLike` instance, `PFun` conjugation,
ordinary function actions, computational `const`/`comp`, and seals are preserved.
The starting source had `equivariant`/`ofCaptures` but no `fromParam`; this inventory
supersedes the historical review's branch-level adapter description.

Public additions in `NFun/Basic.lean`:

- `uncurry`, `uncurry_apply`, `curry_uncurry`, `uncurry_curry`; the original
  `curry_eval` statement remains compatible and delegates to the new inverse law.
- `coe_*` equations for constructors, identity/constants, comp/map/comap/prod/eval,
  curry partial application, and uncurry. Applied wrappers normalize to applications;
  explicit function coercions normalize to ordinary functions, without reverse
  simp rules or support-proof unfolding. Use existing `ext`/`DFunLike.congr_fun`.
- `smul_curry`, `smul_uncurry`, their equivariance predicates, exact `supp_curry`
  and `supp_uncurry`, and freshness equivalences; no nonempty assumptions added.
  `supp_curry_apply_le`/`fresh_curry_apply` give only bounds for fixed arguments.
- `IsEquivariant.toNFun` and `NFun.fromParam f hf p` for
  `hf : IsEquivariant₂ α f`, with computation/coercion/support/freshness laws and
  `smul_fromParam`. Fixed parameters contribute support; joint equivariance does
  not imply the fixed-parameter function has empty support.
- `supp_equivariant`, `fresh_equivariant`, `supp_ofSupports_le`,
  `supp_ofCaptures_le`, and the corresponding fresh constructors.

The substitution variable support certificate is now `supports_nfun from x s`.
Its constructor uses `ofFun` with the support witness inside its proof field:
passing noncomputable `supp s` as an explicit `ofSupports` data argument was
experimentally rejected by Lean's computability check. App/lam handlers use
`equivariant`; support and FCB obligations reuse public lemmas. All substitution
statements and existing lambda-interface work are preserved. The lambda consumers
include a real iterator and a collision requiring binder renaming.

Performance probes use Lean/Mathlib 4.34.1 and cached dependencies, unchanged
heartbeat limits, five direct Lean runs per variant. Exact six-statement benchmark
proofs and instrumentation are retained in `Examples/NFun.lean`. The old Basic
module was rebuilt from `0277d3d` in an isolated import overlay for the baseline;
missing-API and simp failures were reproduced there. Internal tactic heartbeat
counts (raw counter units, not the user-facing heartbeat limit) were:

| Consumer | Before | After |
| --- | ---: | ---: |
| Composition function coercion (`rfl` → `simp`) | 11,074 | 24,284 |
| Partial function coercion (`rfl` → `simp`) | 12,560 | 21,265 |
| Curry action | 488,500 | 47,992 |
| Partial support bound | 71,145 | 28,317 |
| Equivariant support | 38,025 | 19,807–19,819 |
| Nested extensionality (unchanged proof) | 58,254 | 58,268 |

Whole-process median/range: six-statement benchmark 0.912s (0.901–1.993s)
→ 0.876s (0.874–0.882s); substitution module 1.510s (1.493–1.555s)
→ 1.388s (1.370–1.430s) in the final rerun. These include startup/import, a baseline outlier, and
concurrent-development noise; they do not establish a general speedup. The
focused action/support proofs improve while convenient coercion simp costs more
than `rfl`. No seal removal or global transparency/heartbeat change was needed.

Final local verification: `lake build Nominal Instances Examples` passes
without warnings (1,015 jobs, incremental project rebuild using cached pinned
dependencies). The three new example files are persistent targets, including
five guarded computational evaluations returning `7` and per-file axiom audits.
Existing `Examples/LambdaConstructors.lean` and `Examples/LambdaInterface.lean`
also pass direct Lean checks. Representative new public laws and substitution
results use only `propext`, `Classical.choice`, and `Quot.sound`; a broad audit
checks 1,683 project declarations with no unexpected axioms. `git diff --check`,
new-file whitespace checks, and documentation link checks pass. No clean dependency
bootstrap was attempted. No commit or push was made.

Independent review confirmed the mathematical interfaces and identified two
tactic issues: sibling-goal isolation and grouped typed-binder diagnostics.
Both have passing regression tests and fixes. Final coverage checks added proved
rules for evaluation/map/comap/parameter application; explicit rule syntax accepts
reversed equations such as `[← hf.map_smul]`. No proof certificates or ordinary
function support assumptions are synthesized without kernel-checked evidence.

Remaining ergonomic limits: explicitly state nominal function types at API
boundaries; `Function.uncurry` does not automatically adapt an NFun-valued
codomain (use `f.uncurry` or an explicit lambda). Ordinary `Function.curry` and
`Function.uncurry` definitions may be supplied to simp when comparing their
function-level normal forms with lambdas. Raw `NFun.mk` with a literal existential
proof can expose an implicit-transparency mismatch: use a typed
`hf : FinSupported f` or public constructors instead. Necessary nonempty-domain
hypotheses on constant support equality/injectivity remain unchanged.

## 8. M — Nominal-function metaprogramming

The lambda branch's syntax-only `nfun` macro is a prototype. It can mistake global
identifiers for captured variables and does not reliably track every binding form.
The substitution handlers now exercise the focused proof-producing interface.
A successful prototype build therefore does not establish general usability.
The author has chosen to finish Church–Rosser and learn the general tooling
requirements from it. M-02's general elaborator and broad M-04 automation can
follow that proof. Small certified support automation may be added when a
concrete handler/proof needs it; the whole M workstream is not a release gate.

### M-01 — Define the supported surface language [DONE — focused first-release contract]

Dependencies: N-01, N-02. Initial home: the integrated `Nominal/Set/NFun/Tactic.lean`;
split into focused elaborator modules only when responsibilities warrant it.

- [x] Write intended examples before committing to syntax: nominal lambdas,
  composition, currying, partial application, and fixed parameters.
- [x] Specify expected-type behavior and how ordinary, equivariant, and nominal functions interact.
- [x] Define explicit capture/support/proof escape hatches and unsupported cases.
- [x] Document the agreed first-release subset: reliable NFun interfaces and
  focused support automation, with general lambda elaboration following later.

Done when: the user-facing contract is understandable and benchmarked against
actual client code, including failures and diagnostics.

### M-02 — Implement expression-aware elaboration [DEFERRED]

Dependencies: M-01 and the relevant N interfaces.

- [ ] Elaborate with expected types and inspect actual local-variable identities.
- [ ] Track binders through nested lambdas, tuple patterns, `let`, and `match`.
- [ ] Distinguish globals, local parameters, instance arguments, and genuine captures.
- [ ] Avoid unsolved metavariables, accidental capture, and leaked speculative assignments.
- [ ] Produce certified combinator applications or explicit proof obligations.

Done when: alpha-renaming local Lean variables does not change capture behavior,
and lexical-scope tests cover shadowing, nested patterns, qualified globals,
unused parameters, and inferred instances.

### M-03 — Automate support and equivariance obligations [IN PROGRESS; focused subset delivered]

Dependencies: M-01, N-04; reuse C-04/C-06 as appropriate. A focused theorem/tactic
interface can precede M-02; general capture-driven elaboration depends on M-02.

- [x] Establish a controlled registry of proved support/equivariance lemmas.
- [x] Cover identity, constants, constructors, pairs, application, composition,
  currying, and supported conditional operations needed by the benchmarks.
- [x] Infer sound support upper bounds from captured nominal parameters.
- [x] Recognize proved equivariant globals without assuming every global is equivariant.
- [x] Reject or expose obligations for arbitrary ordinary functions, which need not
  have finite support.
- [x] Keep generated proofs inspectable and provide local, actionable diagnostics.

Done when: both successful and deliberately unsupported examples behave correctly;
no admission, trusted oracle, or unjustified support assumption is introduced.

Delivered subset: `supports_nfun [rules] from captures` proves explicit
`supports S (PFun.mk f)` certificates using capture inclusions and the
`nfun_simp` registry of proved action/computation equations. Capture expressions
retain local identities. Union order/association, duplicate/compound captures,
atom singletons, local inclusion/support evidence, and equality-tested conditionals
are covered. Quotient lambda constructor equations are registered in their module.
Failures restore tactic state and identify missing bounds or remaining action
obligations; explicit proof construction remains available.

Automatic `nfun` remains syntax-based: the documented single-binder subset is
benchmarked, and automatic `let`/`match`/nested-function and multiple-binder forms
receive early errors. Explicit capture syntax bypasses automatic scope discovery
but still requires a proved certificate. Globals are not assumed equivariant;
use explicit rules, `equivariant`, or `hf.toNFun`. Explicit empty support uses
`ofSupports`/`ofCaptures`, not an empty capture-list syntax.

- [ ] General capture-driven support/equivariance search and binder-aware
  expected-type elaboration remain deferred with M-02; this delivery does not
  establish general lambda elaboration or complete M-04.

### M-04 — Connect tooling to binder recursion [DEFERRED — general automation; focused client delivered]

Dependencies: M-03, L-02, L-03.

- [x] Construct recursion handlers through the supported user-facing function interface.
- [ ] Generate routine support bounds and freshness/FCB obligations from verified lemmas.
- [x] Expose stable constructor equations and uniqueness principles for resulting functions.
- [x] Rewrite the substitution example to exercise the tooling end to end.
- [x] Retain a direct theorem-level route when an obligation is beyond automation.

Done when: real binder-recursive definitions validate the tooling, not only toy
examples. General datatype generation is not a prerequisite.

Task 9 reuses the existing `supports_nfun` substitution variable handler and
proof-backed constructor functions, and adds public iterator computation/support/
uniqueness consumers. Automated inference of general binder FCB obligations is
not claimed; explicit theorem proofs remain the supported escape hatch.

## 9. L — Lambda interface consolidation

### L-01 — Stabilize quotient syntax and BVC term induction [DONE]

Dependency: B-04. Files: `Instances/LambdaCalculus/Basic.lean`, `Induction.lean`.

- [x] Document raw versus quotient syntax and the intended public constructor API.
- [x] Preserve constructor disjointness/injectivity, abstraction equality, and
  support equal to free variables.
- [x] Expose variable/application injectivity and constructor disjointness at
  quotient level in the basic API; clients should not need raw `AEq` inversion
  or imports of recursion internals for these results.
- [x] Demonstrate `strong_ind` with arbitrary nominal contexts and its finite-set variant.
- [x] Show that predicates on quotient terms do not need an additional equivariance hypothesis.
- [x] Add a nested-binder example avoiding external parameters and previously chosen binders.

Done when: ordinary syntax proofs do not manipulate raw alpha-equivalence witnesses.

Delivered in the uncommitted working tree based on `0277d3d`:

- `Term.var_inj`, `app_inj`, and same-binder `lam_inj` are directed simp rules
  in `Basic.lean`. Existing `var_ne_app`, `var_ne_lam`, and `app_ne_lam` were
  relocated from `Recursion.lean`, preserving names/statements; `app_ne_var`,
  `lam_ne_var`, and `lam_ne_app` complete symmetric discrimination.
- Existing `term_lam_eq_iff` remains the `NameAbs` bridge. `lam_eq_swap`,
  `lam_eq_iff_at_fresh`, `exists_lam_eq_at_fresh` (unique body), and
  `lam_eq_iff_common_fresh` support chosen-binder inversion and alignment.
  Freshness is for the lambda term, not its body: the original binder is allowed.
  Renaming/alignment lemmas are intentionally not simp rules.
- `RecRel.inv_var` and `RecRel.inv_app` now consume the basic quotient API.
  `Induction.lean`, including arbitrary-predicate/context `strong_ind` and
  `strong_ind_finset`, is unchanged.
- [Basic-only consumers](../Examples/LambdaConstructors.lean) cover constructor
  discrimination, the abstraction bridge, prescribed and common fresh binders,
  arbitrary external avoidance, and shadowing. In
  [interface consumers](../Examples/LambdaInterface.lean), `freshBinders` produces
  a certificate for every nested binder, using an arbitrary nominal parameter
  `external : X` and enlarged contexts `(external, insert a A)`. Its predicate
  captures `external` without an equivariance hypothesis. `freshConstructorView`
  demonstrates the finite-set induction variant.

Verification and remaining scope are recorded under R-01 below.

### L-02 — Clarify the recursion contract [DONE]

Dependency: B-04. File: `Instances/LambdaCalculus/Recursion.lean`.

- [x] Document exactly which handlers, support bounds, and FCB hypotheses the recursor requires.
- [x] Audit totality, functionality, constructor equations, and independence of representatives.
- [x] Distinguish the existing iterator from primitive recursion supplying original subterms.
- [x] Supply the needed returned `NFun`/support and functional uniqueness interfaces:
  the earlier graph-only interface now has public contracts and avoidance-set independence.
- [x] Add the needed interface results without undertaking a generic categorical redesign.

Done when: the public recursor can be applied and reasoned about without reading
its relational implementation. Stronger recursion interfaces remain demand-driven.

Delivered: `recNoContext_unique` accepts an arbitrary ordinary candidate function
and a separate finite avoidance bound; `recNoContext_independent` compares valid
bounds without requiring inclusion. `recNoContext_supports`, `recNoContextNFun`,
its `[simp]` application equation, and `supp_recNoContextNFun_le` expose supported
iteration. `Examples/NFunLambda.lean` and the tutorial use these contracts without
graph witnesses. No primitive recursion, new axiom, or seal change was introduced.

### L-03 — Use substitution as the interface benchmark [DONE — first-deliverable benchmark]

Dependencies: L-01, L-02, N-02 through N-04.
File: `Instances/LambdaCalculus/Substitution.lean`.

- [x] Preserve computation, forget, freshness, equivariance, composition, and support theorems.
- [x] Refactor handler construction and ordinary-function use through the improved NFun API.
- [x] Add capture-avoidance examples that actually require binder renaming.
- [x] Present the composition proof with readable avoidance assumptions and stable simp rules.
- [ ] DEFERRED: extend M-04 only when a further client justifies more automation.

Done when: the example both proves the right theorems and demonstrates the intended
library experience. Executability is not required.

L-01/R-01 preserved these existing laws and added `captureAvoidance` in
`Examples/LambdaInterface.lean`: substituting `a := var b` into `lam b (var a)`
requires renaming its binder. Task 9 completes the handler/iterator benchmark: the existing
`supports_nfun` variable handler and equivariant constructor handlers are retained,
and the tutorial proves composition of supported substitution functions using
`ext` and `subst_subst`. The existing composition proof already uses strong term
induction with an explicit avoidance set; it is retained rather than rewritten
for cosmetic reasons. Its distinctness and freshness hypotheses remain unchanged.

## 10. R — Reduction and Church–Rosser

Recommended route: parallel reduction, substitution compatibility, and a diamond
or triangle argument. Then connect its closure to beta reduction. Isabelle's
[nominal Takahashi development](https://isabelle.in.tum.de/website-Isabelle2025/dist/library/HOL/HOL-Nominal-Examples/CR_Takahashi.html)
is a reference for proof organization and freshness obligations. It uses complete
development; choosing that particular presentation remains a decision below.

### R-01 — Binder-renaming and inversion tools [DONE]

Dependencies: L-01, existing substitution results; can proceed before full M work.

- [x] Prove a precisely hypothesized binder-renaming/substitution compatibility lemma.
- [x] Supply convenient constructor inversion at a chosen fresh binder.
- [x] Reuse existing interfaces rather than duplicate abstraction equality,
  substitution equivariance, or composition (proof dependencies clarified below).
- [x] Test identical binders, distinct binders, shadowing, and freshness for replacements.

Done when: reduction proofs can align representatives without returning to raw syntax.

Inventory and delivered equations (`LambdaCalculus.Term`, `Substitution.lean`):

- Existing `subst_lam_rename` equates substitutions of whole lambda terms;
  it does not establish compatibility of contraction bodies. Its statement is
  preserved, with its proof simplified through `term_lam_eq_iff` and
  `NameAbs.abs_eq_swap`.
- New `subst_rename (a b) (t s) (hb : b # lam a t)` proves
  `t[a := s] = (swap a b • t)[b := s]`. The hypothesis is exactly
  `b = a ∨ b # t`; neither binder must be fresh for `s`.
- New `subst_eq_of_lam_eq (a b) (t u s) (h : lam a t = lam b u)` proves
  `t[a := s] = u[b := s]`, with no freshness premise at all. Its proof consumes
  `lam_eq_iff_at_fresh` and `subst_rename`.
- New simp rule `subst_var_self (t) (a)` gives `t[a := var a] = t`;
  `subst_var_eq_swap (a b) (t) (hb : b # lam a t)` gives
  `t[a := var b] = swap a b • t`. The latter is not a simp rule.
- Existing computation, freshness, joint equivariance, composition, and support
  laws were inventoried and retained without statement changes. The compatibility
  proof uses strong term induction and computation, choosing inner binders fresh
  for both substitution atoms and the replacement. It does not use
  `subst_equivariant` or `subst_subst` as proof dependencies, nor impose their
  potentially irrelevant side conditions on the result. Existing seals remain.

Persistent consumers include `contractionWithOpenReplacement`, whose replacement
contains **both** binder atoms freely and whose conclusion verifies that neither
is fresh for it, as well as same-binder contraction, arbitrary equal abstractions,
shadowing, variable renaming, and capture avoidance. The examples use only public
interfaces; no raw alpha-equivalence or recursion implementation is unfolded.

Verification (2026-10-02, uncommitted `fasapa/next` based on `0277d3d`):

- Affected Basic, Recursion, and Substitution modules compiled; independent
  statement/proof review found no overstrong assumptions or incompatible simp rules.
- `lake build Nominal Instances` and explicit consumer targets
  `lake build Nominal Instances Examples.Freshness Examples.LambdaConstructors Examples.LambdaInterface`
  passed. These are incremental working-tree builds with cached pinned dependencies,
  not clean dependency bootstraps.
- `lake env lean Examples/LambdaConstructors.lean` and
  `lake env lean Examples/LambdaInterface.lean` passed. Their persistent axiom
  audits reject admissions and additional axioms in the clients and public lambda API.
- Principal constructor/inversion and all four new substitution results were
  checked with `#print axioms`: only `propext`, `Classical.choice`, `Quot.sound`.
- A both-root axiom sweep (`lake env lean /tmp/NominalLambdaInterfaceAudit.lean`)
  checked 1,606 project declarations, including private core/lambda declarations,
  with no unexpected axioms. The final explicit build passed without warnings
  (1,012 jobs, mostly cached); both supported libraries alone report 1,009 jobs.
- `git diff --check` and whitespace checks on new/untracked changed files passed;
  existing induction, dependency pins, freshness tactics, and unrelated user files
  remain unchanged.

Remaining scope: this establishes the syntax and contraction equations needed to
start R-02. No beta/parallel relation, reduction inversion, strong rule induction,
or confluence theorem is claimed. R-03 must transport derivation premises and
conclusions under binder renaming; strong term induction alone does not supply it.
L-02 and the remaining L-03/NFun polish are still open.

### R-02 — Define beta and parallel reduction [DONE]

Dependencies: L-01, R-01, L-03's existing mathematical interface (all available).
Implementation plan (2026-10-05, working tree based on `5434d4e`):

1. Add `Instances/LambdaCalculus/Beta.lean`: unrestricted contraction using
   `Term.subst`, both application contexts, lambda context; equivariance,
   support/freshness preservation, and public constructor inversion.
2. Add `Instances/LambdaCalculus/Parallel.lean`: variable, application, lambda,
   and contraction reducing both premises; reflexivity and nominal properties.
   Use ordinary derivation induction, with no implicit fresh-binder assumptions.
3. Inventory pinned Mathlib closures, then expose beta reflexive-transitive
   reduction and equivalence closure in a focused closure module.
4. Add `Examples/LambdaReduction.lean`, umbrella imports, and axiom audits.
   Check open terms, all contexts, capture avoidance, alpha-renamed contraction,
   simultaneous parallel contraction, and absence of variable beta successors.
5. Build all supported libraries and examples; independently review statements,
   inspect principal axioms, check whitespace/import coverage, and record evidence.

The user supplied the mathematical specification and authorized autonomous work
in the current branch, with no commits. Existing uncommitted files are preserved.
Baseline `lake build Nominal Instances Examples` passed (1,015 jobs, cached).

- [x] Define full contextual beta reduction on quotient terms, including reduction under lambdas.
- [x] Define parallel reduction with clearly stated binder/freshness conventions.
- [x] Define or reuse appropriate reflexive-transitive and convertibility closures.
- [x] Prove reduction equivariance and the needed support/freshness preservation facts.
- [x] Check that the definitions are independent of the chosen alpha representatives.
- [x] Contraction rules are unrestricted: no fresh-binder premises are imposed,
  so no comparison with a restricted relation is necessary.

Done when: the rules express the intended untyped lambda calculus, rather than an
accidentally restricted evaluation strategy, and basic examples compile.

Delivered declarations (all under `LambdaCalculus.Term`):

- `Beta.lean`: inductive `Beta` with `beta`, `app_left`, `app_right`, and `lam`.
  The `beta a t s` rule contracts `app (lam a t) s` to `t[a := s]` for every
  binder, body, and argument. `Beta.equivariant`/`equivariant_iff` permute both
  endpoints; `supp_le` proves target support is contained in source support;
  `fresh` preserves atom freshness. `not_var`, `app_iff`, and `lam_iff` give
  public constructor facts using only quotient APIs. `beta_of_lam_eq` consumes
  R-01's `subst_eq_of_lam_eq` with an arbitrary replacement.
- `Parallel.lean`: inductive `Parallel` with `var`, `app`, `lam`, and `beta`.
  The contraction premises are `Parallel t t'` and `Parallel s s'`, and its
  target is `t'[a := s']`. Proved `Parallel.refl`, `equivariant`,
  `equivariant_iff`, `supp_le`, `fresh`, `fresh_left`, `var_iff`, `app_iff`, and
  `lam_iff`. `beta_rename` transports the body premise by a swap and reuses
  `subst_rename`; source-abstraction freshness propagates to the reduced
  abstraction, without imposing freshness on the argument.
- `ReductionClosure.lean`: `BetaStar := Relation.ReflTransGen Beta` and
  `BetaEq := Relation.EqvGen Beta`. The inventory used the pinned Mathlib
  `Mathlib/Logic/Relation.lean` at revision
  `d13f23b723b8a846827a245b89c10fc7d3f11612` (v4.34.1).
  Existing `ReflTransGen.lift`, `lift'`, `mono`, and
  `EqvGen.reflTransGen_le_eqvGen` supply the required closure infrastructure
  and support later inclusion/correspondence proofs. `BetaStar.refl`, `single`,
  `trans`, `app_left`, `app_right`, `app`, `lam`, `equivariant`,
  `equivariant_iff`, `supp_le`, and `fresh` form its basic interface.
  `BetaEq.refl`, `symm`, `trans`, `of_beta`, `of_betaStar`, `app_left`,
  `app_right`, `lam`, `equivariant`, and `equivariant_iff` expose conversion.
  Support/freshness monotonicity is deliberately confined to forward reduction.
- Scoped notation in `LambdaCalculus`: `→β`, `⇉`, `→β*`, and `≡β`.
  The `Instances.LambdaCalculus` umbrella imports all three new modules, so
  the default `Instances` target reaches every new reduction declaration.
- `Examples/LambdaReduction.lean`, imported by `Examples.lean`, contains 15
  named consumer theorems. They cover identity/open contraction, both application
  positions, reduction beneath lambdas, capture avoidance retaining a free atom,
  alpha-equivalent binders with unrestricted replacements, and parallel
  contraction reducing both body and argument. `variableHasNoBetaSuccessor`
  is the negative beta example; `parallelTwoStepsNotOne` proves an explicit
  counterexample to parallel transitivity. `contextualSequence` consumes
  closure composition; `conversionCanIntroduceFreeAtoms` reverses an erasing
  contraction to demonstrate the limit of support preservation.

Verification (2026-10-05, uncommitted `fasapa/next` based on `5434d4e`):

- Targeted builds of all three modules and direct elaboration of all four new
  Lean files passed without diagnostics. The initial identity/no-variable beta
  consumer failed on the absent API before implementation and passed afterward.
- `lake build Nominal Instances Examples Examples.LambdaConstructors Examples.LambdaInterface`
  passed without warnings (1,021 jobs, incremental project build using cached
  pinned dependencies). No clean dependency bootstrap was attempted.
- `lake env lean Examples/LambdaReduction.lean` passed, including a persistent
  audit rejecting any axioms beyond `propext`, `Classical.choice`, and `Quot.sound`
  in the examples and public lambda declarations.
- `lake env lean /tmp/NominalR02Axioms.lean` inspected 20 principal results with
  `#print axioms`: beta nominal properties/inversion/binder compatibility,
  parallel reflexivity/nominal properties/inversion/renaming, and closure
  nominal properties/inclusion. Every result uses only the standard three
  axioms, with no `sorryAx` or custom assumptions.
- `lake env lean --deps Instances/LambdaCalculus.lean` lists all seven
  case-study modules; root imports and the `Examples` import were also checked.
- Independent statement/proof review found no mathematical or implementation
  defects. The reviewer independently compiled all four new files, checked
  unrestricted rules and both parallel premises, and confirmed that inversion
  exposes actual derivation binders without assuming BVC rule induction.
- `git diff --check`, explicit whitespace/conflict checks for the new untracked
  Lean files and roadmap, admission/raw-quotient scans, and documentation link
  checks passed. Existing README changes and unrelated untracked files were
  preserved; no core/NFun changes, dependency changes, CI, commits, or pushes.

Remaining work: R-03 must generalize induction over derivations to arbitrary
nominal contexts and supply fresh case analysis with all premise derivations
transported coherently. The present `lam_iff` lemmas retain existential binders;
they are not chosen-fresh-binder inversion. No missing syntax/substitution
interface blocked R-02. R-04 parallel substitution compatibility, R-05 diamond,
and R-06 closure correspondence/Church–Rosser remain unimplemented.

### R-03 — Fresh rule induction and inversion [DONE]

Dependencies: R-01, R-02, C-01/C-02 (available).
Delivered in [ReductionInduction.lean](../Instances/LambdaCalculus/ReductionInduction.lean)
and [ReductionInversion.lean](../Instances/LambdaCalculus/ReductionInversion.lean),
exported by `Instances.LambdaCalculus` and `Instances`.

- [x] Derive induction over reduction derivations generalized over an arbitrary nominal context.
- [x] Give binder cases freshness assumptions for the ambient parameters they must avoid.
- [x] Transport premise derivations and conclusions together under renaming.
- [x] Handle beta contraction's substitution result coherently with the renamed binder.
- [x] Provide usable fresh case analysis/inversion lemmas and application examples.

Done when: induction hypotheses cover every premise derivation required by the
confluence proof. Existing strong induction over terms is not a replacement for this task.
Do not assume that the paper's variable convention automatically justifies rule induction.

Delivered declarations (2026-10-05; uncommitted `fasapa/next` based on `026a54e`):

- `Term.Beta.strong_ind` and `Term.Parallel.strong_ind` take an arbitrary
  `P : Term α → Term α → Z → Prop`, with `Z : Type v` and `[Nominal α Z]`.
  The context universe is independent of the atoms' universe. There is no
  equivariance, support, or nominal-instance requirement on `P` or its captures.
  Each recursive premise supplies its derivation and `∀ d, P source target d`.
  Lambda handlers receive `a # z`; contraction handlers also receive `a # s`
  and, for parallel contraction, `a # s'`. Both parallel contraction IHs are
  present. `Beta.strong_ind_finset` and `Parallel.strong_ind_finset` specialize
  to an endpoint predicate and a fixed avoidance set, exposing `a ∉ A`.
- The proof strengthens ordinary derivation induction to all permutations and
  contexts. In lambda cases both body endpoints and the premise derivation are
  renamed. Parallel contraction renames only its body premise; its argument
  premise is left unchanged by that binder renaming. `subst_rename` identifies
  the substituted targets with the same replacement, and the existing support
  preservation results supply freshness for reducts. No binder is required to
  be fresh for its own body, and neither relation's definition was changed.
- Both `Term.Beta` and `Term.Parallel` provide `lam_iff_at_fresh`,
  `lam_iff_same`, `lam_lam_iff`, `lam_iff_common_fresh`, `lam_iff_fresh`,
  `app_iff_at_fresh`, and `app_iff_fresh`. The chosen-binder form permits the
  existing binder and requires freshness for the abstraction/function, not the
  body or argument. Context forms obtain a fresh common binder; application
  contraction witnesses also avoid the argument endpoints. Beta application
  inversion retains left, right, and contraction alternatives; parallel
  application inversion retains both congruence and contraction, which can overlap.
  All proofs use public quotient constructor/abstraction and renaming APIs.

Persistent consumers in [LambdaFreshReduction.lean](../Examples/LambdaFreshReduction.lean),
included in the `Examples` target:

- `betaTree` / `parallelTree` construct example-only fresh derivation certificates.
  Their lambda and contraction-body IHs are applied at `insert a A`, so a
  fixed-context IH would not suffice. `nestedBetaBinders` starts with repeated
  binder names and avoids an external atom/term; `parallelBodyAndArgument` uses
  genuine contractions in both recursive premises.
- `parallelFreshWhen` reproves freshness preservation with an arbitrary captured
  predicate `q : α → Prop`, using fresh binder facts and both contraction IHs.
  `betaFreshViaFinset` demonstrates the finite-set wrapper and uses its
  nonmembership assumption. These are examples, not duplicate library results.
- `alphaRenamedBetaInversion` / `alphaRenamedParallelInversion` align explicitly
  distinct binder presentations at a fresh common name. `nestedParallelInversion`
  uses arbitrary `X : Type v` context data and extends it with an outer binder.
  `sameBinderInBody`, `sameBinderInArgument`, and
  `parallelApplicationAlternativesOverlap` cover bound occurrences, open
  replacements containing the chosen binder, and overlapping Omega alternatives.

Verification:

- `lake env lean` passed without diagnostics for both new modules, the new
  consumer file, and the existing standalone `LambdaConstructors.lean` and
  `LambdaInterface.lean` clients.
- `lake build Nominal Instances Examples` passed without diagnostics (1,022 jobs).
  This was an incremental project build with the pinned local dependency cache;
  the affected modules/consumers were recompiled. `lakefile.toml` still makes
  `Nominal` and `Instances` the two default supported targets. No dependency
  upgrades or clean dependency bootstrap were performed.
- Explicit `#print axioms` inspection of all 18 new public induction/inversion
  results reports only `propext`, `Classical.choice`, and `Quot.sound`.
  A broader audit of 1,790 core/lambda declarations found no additional axioms.
  The persistent public-lambda and new-consumer audits also pass; there is no
  `sorryAx`, custom axiom, or disabled kernel checking in the new proofs.
- Independent source/statement review confirmed arbitrary predicates/contexts,
  all generalized premise IHs, consistent endpoint transport, unrestricted
  replacements, and overlapping inversion alternatives. `git diff --check`,
  new-file whitespace checks, and documentation link/content checks passed.

R-04 readiness: use context `(x, r, r')` and motive
`P t t' (x, r, r') := r ⇉ r' → t[x := r] ⇉ t'[x := r']`.
The fresh lambda handler permits both `subst_lam` equations. In contraction,
the two IHs supply related substituted bodies and arguments, while
`subst_subst a x t' s' r'` needs exactly `a ≠ x` and `a # r'`, already supplied
by context freshness. This checks compatibility for both related subjects and
related replacements, rather than just a fixed replacement.

Remaining scope: R-04's full compatibility theorem, diamond, closure
correspondence, and Church–Rosser are not implemented here. Contexts must be
nominal (hence finitely supported), with one atom sort and single/nested binders;
the predicate itself remains unrestricted. No generic rule-induction generator,
CI changes, commits, or pushes were added. Earlier R-02/review descriptions of
missing fresh rule induction remain historical records superseded by this entry.

### R-04 — Parallel reduction commutes with substitution [DONE]

Dependencies: R-03 and existing substitution composition (available).
Delivered in [ParallelSubstitution.lean](../Instances/LambdaCalculus/ParallelSubstitution.lean),
exported by `Instances.LambdaCalculus` and `Instances`.

- [x] Prove that related subjects and replacements remain related after substitution.
- [x] Use fresh rule induction to discharge lambda and beta cases.
- [x] Reuse the separate freshness/renaming interfaces; no new helper lemma is needed.
- [x] Check the hypotheses are sufficient without imposing unnecessary closedness.
- [x] Derive subject-only and replacement-only compatibility from reflexivity.
- [x] Retain meaningful capture-avoidance, shadowing, and contraction/composition examples.

Done when: simultaneous compatibility holds for open terms and arbitrary
substitution variables, without restrictions on external finite nominal contexts.

Delivered declarations (2026-10-05; uncommitted `fasapa/next` based on `8a01417`,
preserving pre-existing README, example-import, and documentation changes):

- `Term.Parallel.subst (ht : t ⇉ t') (hs : s ⇉ s') (x : α)` proves
  `t[x := s] ⇉ t'[x := s']`. All four endpoints are arbitrary quotient terms;
  there are no freshness, closedness, or distinctness hypotheses in this theorem.
- `Term.Parallel.subst_left ht x s` fixes the replacement, using `Parallel.refl s`.
  `Term.Parallel.subst_right hs t x` fixes the subject, using `Parallel.refl t`.
  A source inventory found no existing compatibility result to duplicate.
- The proof uses `Term.Parallel.strong_ind` with context `(x, r, r')` and motive
  `r ⇉ r' → t[x := r] ⇉ t'[x := r']`. Both replacements, their relation premise,
  and the variable remain generalized through the recursive hypotheses. The
  variable, application, lambda, and contraction handlers are all present.
  Local binder freshness gives `a # (x, r)` and `a # (x, r')` for the lambda
  computation rules. Renaming and freshness preservation are already justified
  inside the reused rule-induction principle.
- In the contraction handler, both premise IHs give related substituted bodies
  and related substituted arguments. The forward equation
  `subst_subst a x t' s' r'` rewrites
  `(t'[a := s'])[x := r']` to `(t'[x := r'])[a := s'[x := r']]`.
  Its exact hypotheses are `a ≠ x` and `a # r'`, both obtained from context
  freshness. This is exactly the result of `Parallel.beta a` applied to the two
  IHs. Independent mathematical review checked the argument order, direction,
  both premises, and every local hypothesis separately from compilation.

Persistent consumers in
[LambdaParallelSubstitution.lean](../Examples/LambdaParallelSubstitution.lean),
included in `Examples`, use public quotient/reduction/substitution APIs:
`bothContract` includes inequalities certifying genuine subject and replacement
contractions; `captureAvoidance` computes an alpha-renamed target and proves its
colliding atom remains free; `repeatedBinderShadowing` computes substitution
around two binders with the substitution variable's name and reduces beneath
them; `fixedReplacement` and `fixedSubject` exercise the corollaries.
`contractionComposition` has genuine body, argument, and replacement contractions;
the replacement contains the displayed contraction binder freely, so the proof
also exercises fresh renaming before composition. An `identity` helper completes
the seven named consumer proofs, all covered by a rejecting axiom audit.

Verification:

- `lake env lean Instances/LambdaCalculus/ParallelSubstitution.lean` and
  `lake env lean Examples/LambdaParallelSubstitution.lean` pass without diagnostics.
  Existing standalone `Examples/LambdaConstructors.lean` and
  `Examples/LambdaInterface.lean` also pass direct elaboration.
- `lake build Nominal Instances Examples` passes without diagnostics (1,024 jobs).
  This is an incremental project build using pinned Lean/Mathlib 4.34.1 cached
  dependencies; the new module, consumer, and affected dependents were compiled.
  The two supported default targets remain `Nominal` and `Instances`.
- Explicit `#print axioms` for all three public results reports exactly
  `propext`, `Classical.choice`, and `Quot.sound`. A broad audit of 1,793
  core/lambda declarations and the persistent public-lambda/consumer audits pass.
  There are no admissions, new custom axioms, or disabled kernel checks.
- Independent proof and example review found no issues. `git diff --check`,
  new-file whitespace checks, import coverage, documentation link/content checks,
  and comparison against the initial working-tree files pass.

R-05 is ready to consume simultaneous compatibility. Parallel diamond, complete
development, closure correspondence, and Church–Rosser remain unimplemented;
this task selects no confluence route. Existing one-sort/single-or-nested-binder
scope, dependency versions, and seal/transparency boundaries are unchanged.
No clean dependency bootstrap, CI changes, commits, or pushes were performed.
Earlier R-03/review descriptions of pending R-04 work remain historical records.

### R-05 — Establish the confluence argument [DONE]

Dependencies: R-04 (available); decision Q-01 resolved in favor of direct diamond.
Delivered in [ParallelDiamond.lean](../Instances/LambdaCalculus/ParallelDiamond.lean),
exported by `Instances.LambdaCalculus` and `Instances`.

- [x] Choose direct parallel diamond and record the concrete interface reasons.
- [x] Prove a common parallel reduct for any pair of parallel steps on open quotient terms.
- [x] Cover variables, lambdas, application/congruence pairs, both mixed overlaps,
  and contraction/contraction with justified binder alignment.
- [x] Retain explicit open-term peaks, alpha-renamed binders, and axiom audits.
- [x] Mark complete development as unnecessary for this deliverable. Its quotient
  recursion, computation/renaming facts, and triangle theorem are not implemented
  or required by the selected route.

Done when: parallel reduction has a proved diamond property, directly or as a
corollary of the triangle result, with all overlapping lambda/redex cases handled.

Delivered declaration (2026-10-05; uncommitted `fasapa/next` based on `5732f32`,
preserving pre-existing README, example-import, and documentation changes):

```lean
Term.Parallel.diamond {t t₁ t₂ : Term α}
    (h₁ : t ⇉ t₁) (h₂ : t ⇉ t₂) : Relation.Join Term.Parallel t₁ t₂
```

Mathlib's `Relation.Join` is exactly `∃ p, t₁ ⇉ p ∧ t₂ ⇉ p` here. Both edges
are the existing parallel relation, without a reflexive-transitive closure.
The theorem quantifies over arbitrary quotient terms and atom types with
`[Name α]`; it has no closedness, freshness, or global variable-convention premise.

Proof route and API inventory:

- `Parallel.strong_ind` uses the competing target as nominal context and the
  motive `P t t' u := t ⇉ u → Relation.Join Parallel t' u`. Every recursive
  hypothesis therefore accepts a new competing target and derivation. The
  lambda/contraction binders avoid that context locally; no freshness escapes
  into the public statement.
- Existing `var_iff`, `app_iff`, `app_iff_at_fresh`, `lam_iff_same`,
  `lam_lam_iff`, `Term.lam_inj`, and constructor lemmas suffice. The chosen-binder
  inversion API already transports derivations under alpha-renaming. No new
  alignment lemma, raw `AEq` proof, or quotient-representative manipulation is needed.
- Variables join using `Parallel.refl`. Lambdas invert at the induction binder,
  join their bodies, and rebuild with `Parallel.lam`. Application/congruence
  pairs join the components independently with `Parallel.app`.
- For congruence/contraction, the function IH joins two lambda reducts. Lambda
  inversion exposes a common body at the contraction binder, even though the
  original derivations may have used different representatives. The witness is
  the joined body with the joined argument substituted; its edges use
  `Parallel.beta` and the simultaneous `Parallel.subst` theorem from R-04.
- For contraction/congruence and contraction/contraction, application inversion
  at the induction binder aligns the competing contraction. The required
  `a # Term.lam a t` is always available from `fresh_term_lam_of_eq`; it does
  not demand freshness for the body or argument. Only after alignment does
  `Term.lam_inj` identify source bodies. The two premise IHs yield a substituted
  joining term, with `Parallel.subst` on each contraction side.
- This handles the potentially difficult mixed overlap with the existing
  function IH; no stronger body induction hypothesis or syntax recursion is
  needed. Takahashi complete development would add quotient recursion and
  computation/renaming obligations without a concrete advantage for R-05.
  The iterator/primitive-recursion distinction remains unchanged.

Persistent consumers in
[LambdaParallelDiamond.lean](../Examples/LambdaParallelDiamond.lean), included
in `Examples`, contain six named proofs and the example-only `identityApp`
abbreviation. `mixedPeak` gives the explicit common reduct `s'` for arbitrary
open related arguments; `mixedPeakBothOrders` invokes `diamond` in both orders.
`bothContract` reduces opposite redexes in both bodies and arguments, proves
those premise targets differ, and gives the explicit open join
`app (app (var z) (var w)) (var y)`. `alphaRenamedPeak` aligns distinct outer
lambda binders and retains a free atom. `alphaRenamedContractions` uses distinct
binders for two contraction rules, proves their targets differ, and joins at
`var a` even though `a` is the first binder and occurs freely in the argument.
The `identity` helper and all consumers are covered by a rejecting axiom audit.

Verification:

- `lake env lean Instances/LambdaCalculus/ParallelDiamond.lean` and
  `lake env lean Examples/LambdaParallelDiamond.lean` pass without diagnostics.
  Existing standalone `Examples/LambdaConstructors.lean` and
  `Examples/LambdaInterface.lean` also pass direct elaboration.
- `lake build Nominal Instances Examples` passes without diagnostics (1,026 jobs).
  This is an incremental project build with the pinned Lean/Mathlib 4.34.1
  dependency cache; the new module, consumers, and affected dependents were
  compiled. `Nominal` and `Instances` remain the two default supported targets.
- `#print axioms Term.Parallel.diamond` (inside `LambdaCalculus`) reports exactly
  `propext`, `Classical.choice`, and `Quot.sound`. The explicit audit and the
  persistent public-lambda/consumer audits reject any additional axiom; no
  `sorryAx`, custom axiom, or disabled kernel check is introduced.
- Independent mathematical review checks all six proof branches, arbitrary
  open quotient endpoints, common-binder inversion before injectivity, and
  both joining edges separately from compilation. A scratch consumer confirms
  the public theorem elaborates directly against the explicit existential type.
  A separate example review confirms distinct body/argument reducts, explicit
  open joins, both mixed orientations, and alpha-renamed lambda/contraction peaks.
- `git diff --check`, new-file whitespace checks, documentation local-link/content
  checks, and public/example import coverage pass. Comparison with the initial
  README, example-import, and roadmap snapshots confirms focused updates that
  retain the pre-existing work and task history.

At completion of R-05, beta/parallel closure correspondence, beta confluence,
Church–Rosser for convertibility, and normal-form uniqueness remained
unimplemented; R-06 below records their subsequent delivery.
Dependency versions, existing mathematical
statements, and seal/transparency boundaries are preserved. No general
metaprogramming, CI changes, clean dependency bootstrap, commits, or pushes were
performed. Earlier entries describing diamond as pending remain historical records.

### R-06 — Transfer to beta and state Church–Rosser [DONE]

Dependencies: R-02, R-05 (both complete). Delivered in
[ChurchRosser.lean](../Instances/LambdaCalculus/ChurchRosser.lean), exported by
`Instances.LambdaCalculus` and `Instances` and reached by the default build.

- [x] Prove inclusion of a beta step in parallel reduction and of parallel reduction
  in the reflexive-transitive closure of beta reduction.
- [x] Relate the two reflexive-transitive closures and derive beta confluence.
- [x] State Church–Rosser for beta convertibility explicitly, with joinability as conclusion.
- [x] Reuse general relation lemmas from Mathlib when their statements match.
- [x] Derive uniqueness of normal forms and explain that existence/termination is not claimed.

Done when: headline confluence, Church–Rosser, and normal-form uniqueness theorems
build with explicit statements and no hidden termination or closed-term assumption.

Delivered declarations (2026-10-05; uncommitted `fasapa/next` based on `ba0eacd`,
preserving pre-existing README, example-import, and documentation changes):

```lean
Term.Beta.to_parallel (h : t →β s) : t ⇉ s
Term.Parallel.to_betaStar (h : t ⇉ s) : t →β* s
Term.betaStar_iff_parallelStar :
  (t →β* s) ↔ Relation.ReflTransGen Term.Parallel t s
Term.betaStar_eq_parallelStar :
  (Term.BetaStar : Term α → Term α → Prop) = Relation.ReflTransGen Term.Parallel

Term.Parallel.confluent
  (h₁ : Relation.ReflTransGen Term.Parallel t t₁)
  (h₂ : Relation.ReflTransGen Term.Parallel t t₂) :
  Relation.Join (Relation.ReflTransGen Term.Parallel) t₁ t₂
Term.BetaStar.confluent (h₁ : t →β* t₁) (h₂ : t →β* t₂) :
  ∃ p, t₁ →β* p ∧ t₂ →β* p
Term.BetaEq.church_rosser (h : t ≡β s) : ∃ p, t →β* p ∧ s →β* p
Term.BetaEq.iff_join : (t ≡β s) ↔ ∃ p, t →β* p ∧ s →β* p

Term.BetaNormal (t : Term α) : Prop := ∀ s, ¬ t →β s
Term.BetaNormal.eq_of_betaStar (ht : Term.BetaNormal t) (h : t →β* s) : s = t
Term.BetaStar.normal_unique (h₁ : t →β* t₁) (h₂ : t →β* t₂)
  (hn₁ : Term.BetaNormal t₁) (hn₂ : Term.BetaNormal t₂) : t₁ = t₂
Term.BetaEq.normal_unique (h : t ≡β s)
  (ht : Term.BetaNormal t) (hs : Term.BetaNormal s) : t = s
```

Here all term parameters are arbitrary `Term α`, with only `{α : Type u}` and
`[Name α]`. The notation `≡β` remains the existing `Term.BetaEq`, definitionally
`Relation.EqvGen Term.Beta`: generating steps, reflexivity, symmetry, and
transitivity are all present. Confluence has two directed premises from one
source; Church–Rosser instead has a conversion premise. Normality rules out
**every** outgoing step, including self-loops. The final equalities are equality
of quotient terms. There is no closedness, freshness, evaluation-strategy,
termination, or existence-of-normal-forms premise, and no one-step beta diamond
claim.

Proof route and Mathlib inventory (pinned 4.34.1,
`d13f23b723b8a846827a245b89c10fc7d3f11612`):

- Ordinary derivation induction embeds beta in parallel, using `Parallel.refl`
  for unchanged components. Induction on parallel sequentializes applications
  with the existing `BetaStar.app` and lambdas with `BetaStar.lam`. A parallel
  contraction first reduces its body under the lambda and its argument, then
  appends the resulting single beta contraction. No substitution or fresh
  induction theorem needs to be repeated.
- `Relation.ReflTransGen.mono` and `Relation.reflTransGen_closed` give both
  closure directions. No new closure definition, notation, or contextual
  closure helper was introduced.
- `Relation.church_rosser` lifts the established parallel diamond to closure
  confluence: its asymmetric joining-edge hypothesis is met by wrapping the
  two parallel edges in `ReflGen.single` and `ReflTransGen.single`. The closure
  correspondence transports both inputs and both outputs to beta sequences.
- `Relation.equivalence_join` makes beta joinability an equivalence relation.
  `Relation.EqvGen.mono` and `Equivalence.eqvGen_iff` send the existing conversion
  to that relation. Conversely, two directed paths to a common reduct give a
  conversion by reversing the second path.
- `Relation.reflTransGen_iff_eq` already says a path from an irreducible term
  ends at that same term. Applying it to the two joining paths gives both
  uniqueness theorems, without an induction on termination or a normalization
  assumption.

Persistent consumers in
[LambdaChurchRosser.lean](../Examples/LambdaChurchRosser.lean), included in
`Examples`, contain nine named proofs and the example-only `identityApp`
abbreviation. `duplicatingPeak` contracts either the outer redex or argument of
`(λa. a a) ((λb. b) x)`, proves the immediate reducts unequal, and displays `x x`
as a common reduct with `x` free. The duplicated branch takes two beta steps.
`duplicatingPeakConfluence` applies the public confluence theorem to this peak;
`forwardBackwardConversion` explicitly composes a forward sequence with a
reversed sequence and invokes Church–Rosser. `simultaneousContractionSequence`
uses both inclusions on a parallel contraction with genuine reductions in its
body and argument. `openUnderLambda` reduces under an outer binder while
retaining a free atom. `applicationNormal`, `normalReductUnique`, and
`convertibleNormalUnique` identify arbitrary normal reducts or normal
convertibles of the displayed source with `x x`, using public inversion and
both uniqueness theorems. The `identity` helper and all clients are covered by
the persistent rejecting axiom audit.

Verification:

- Direct `lake env lean` elaboration of `Instances/LambdaCalculus/ChurchRosser.lean`
  and `Examples/LambdaChurchRosser.lean` passes without diagnostics. Existing
  standalone `Examples/LambdaConstructors.lean` and `Examples/LambdaInterface.lean`
  also pass. A scratch consumer checks the headline APIs at explicit existential
  and Mathlib-closure types through `import Instances`.
- `lake build Nominal Instances Examples` passes without diagnostics (1,028
  jobs), compiling new code and affected dependents. This is an incremental
  project build using the pinned Lean/Mathlib 4.34.1 dependency cache, not a
  clean dependency bootstrap. `Nominal` and `Instances` remain the two default
  supported targets; all twelve lambda modules are exported.
- `#print axioms` for all eleven new theorems reports exactly `propext`,
  `Classical.choice`, and `Quot.sound`. The broad audit checks 1,806 project
  declarations without nonstandard dependencies. The persistent example audit
  rejects additional axioms in the closure correspondence, confluence,
  Church–Rosser, uniqueness, and all new clients. No `sorryAx`, custom axiom,
  or disabled kernel check was introduced.
- Independent mathematical review separately checks exact statement strength,
  both closure directions, unrestricted open quotient endpoints, conversion
  versus confluence, and exclusion of normal-term self-loops. Independent client
  review confirms distinct branches, concrete paths and common reducts, both
  conversion directions, genuine parallel premises, and non-vacuous uniqueness
  consumers. Neither review found a mathematical defect.
- `git diff --check`, new-file whitespace checks, local documentation-link and
  import-coverage checks pass. Initial README/example-import/roadmap snapshots
  were compared to the final changes to preserve earlier work and task history.

R-06 meets its completion criterion. Existing statements and seal/transparency
boundaries are unchanged. No new NFun, recursion, metaprogramming, algebraic, CI,
dependency, commit, or push work was needed. This completes task 8's mathematical
results, not the polished library release; remaining client/tutorial work follows.

### R-07 — Validate the case study as a library client [DONE]

Dependencies: R-06 (complete) and the relevant N/L work.

- [x] Present the mathematical reduction/confluence proof through supported nominal interfaces.
- [x] Retain meaningful open/contextual beta, bidirectional conversion, and normal-form clients.
- [x] Identify any remaining raw-representative manipulations and isolate unavoidable internals.
- [x] Record repeated boilerplate as concrete API/automation follow-up tasks.
- [x] Inspect headline theorem axioms and build the entire case study locally.

Done when: the case study demonstrates both mathematical correctness and the
claimed natural binder-reasoning experience.

Mathematical validation delivered with R-06 (2026-10-05, working tree based on
`ba0eacd`): all headline theorems, persistent consumers, independent statement
review, complete supported build, and axiom checks above pass. The beta transfer
and Church–Rosser clients use public constructors, substitution laws, reduction
inversion, and Mathlib closure interfaces, with no raw `AEq`, quotient lifting,
or recursive-implementation unfolding. The R-04/R-05 proofs already isolate the
BVC reasoning in fresh rule induction/inversion. This final transfer needed no
new nominal wrapper or support-automation helper.

Task 9 completes the broader client review. Raw alpha/quotient reasoning is
confined to `Basic` and the implementation of strong induction; relational
iteration and extraction stay in `Recursion`. Substitution unfolds its definition
for the initial lambda equation and then seals it. Reduction, inversion, parallel
compatibility/diamond and closure transfer consume public APIs. The genuinely
duplicated fixed-function action proof is now `NFun.apply_smul_of_fixed`, shared
by the support tactic, FCB and iterator. Remaining finite-set freshness unpacking
is optional ergonomics work, not a defect or a generalized-elaborator requirement.

The compiling tutorial covers arbitrary term/rule predicates, nested avoidance,
required alpha renaming, NFun composition, iterator contracts and the full
confluence chain. See [the final assessment](release-assessment.md), D-01/D-02
and the task-9 validation record below.

## 11. D — Documentation, research correspondence, and first release

### D-01 — Keep module/API documentation truthful [DONE]

- [x] Remove absent structural-isomorphism claims from the current root README.
- [x] Reconcile documentation after integration: `Term.Beta` now exists; remove
  obsolete module paths, unsupported structural claims and nonexistent names.
- [x] Document supported versus experimental modules and the classical/computational boundary.
- [x] Add concise examples for atoms, support, fresh selection, abstraction, NFun usage,
  fresh term induction, recursion, and fresh rule induction.
- [x] Ensure user-facing names agree with actual declarations and generated hypotheses.

Done when: documented examples compile and the module map describes the checked tree.

### D-02 — Write the end-to-end tutorial [DONE]

Dependencies: N-02/N-03, L, R; optional tooling demonstrations depend on M.
Proposed location: a compiling example module plus `docs/tutorial.md`.

- [x] Explain alpha-equated syntax and prove a simple alpha-renaming equality.
- [x] Show a capture-avoiding substitution example and the substitution composition proof.
- [x] Show the difference between term induction and reduction-derivation induction.
- [x] Present the Church–Rosser argument and identify where BVC-style reasoning is justified.
- [x] Provide links to the underlying general library lemmas for each proof pattern.

Done when: a reader can reproduce the examples locally without learning quotient
implementation details first.

### D-03 — Reconcile Rocq and article claims [TODO — external checks pending; correspondence delivered]

Sources: [Rocq repository](https://github.com/fasapa/nominal),
[article repository](https://github.com/fasapa/nominal-sets-article), local TeX,
and [published paper](https://arxiv.org/html/2509.25883v1).

- [x] Maintain a theorem correspondence between Rocq, published releases, current Rocq main,
  Lean core, and lambda example; record unmatched results or deliberate differences.
- [x] Explain supplied supports versus least supports, setoids versus quotients,
  swap lists versus finite bijections, and function extensionality/classical choice.
- [x] Reconcile older statements that alpha induction remains unfinished with current
  Rocq source and the article-linked tag: both already contain identical
  `alpha_ind`, `alpha_rec`, and substitution source, but the tag actively admits
  `PermPermT`/`PermNominal`; main fills those proofs.
- [ ] Rebuild compatible Rocq/stdpp versions and print actual theorem assumptions;
  the review could not run Rocq (`coq_makefile` unavailable). Do not infer every
  theorem's exact dependency set merely from an imported admitted declaration.
- [x] Keep the tag's excluded/deleted `ExtensionalSupportedFunctions.v` experiment
  separate from its supported target: its record-extensionality axiom conflicts
  with observable support data. Commented admissions and `ATOMIC` requirements
  realized by `Atom` are different cases.
- [x] Record the excluded Rocq `Concretion.v` sketch's representative-dependence
  problem with supplied support bounds; syntax repair alone would not validate it.
- [x] Track the equation (3) correction: least support is not strong support.
  Swapping distinct `a,b` fixes `{a,b}` while moving its support pointwise.
- [x] Recheck claims about `Prop`, Some/Any, and structural induction against the
  precise constructive assumptions, rather than extrapolating an interface limitation.
- [x] Check the manuscript's “equivalent to WLPO” wording against the exact theorem
  cited; distinguish an implication from an established equivalence.
- [ ] Correct the action-composition convention and the claim that nominal endpoints
  suffice to make arbitrary ordinary functions finitely supported.
- [ ] Identify manuscript entry points and included sections. Correct extended-draft
  alpha-rule bodies, motive/handler types, and the identification of an arbitrary
  avoidance set with predicate support; distinguish chosen from least support.
- [x] Separate paper corrections from repository code changes and record which
  article versions have actually been amended.

Done when: the follow-up account accurately distinguishes inherited mathematics,
changed foundations, implemented results, and new contributions. Article files
were not modified during the initial review.

Task-9 [research correspondence](research-correspondence.md) rechecks the pinned
main/tag source differences, active project membership, exact lambda/substitution
source identity, manuscript entry points and the published v1 formulas. It records
Swan's precise implication, not an equivalence. No external source was edited.
Rocq/coqc/coq_makefile/opam are unavailable; compatible external builds and actual
`Print Assumptions` remain unverified. The unchecked correction/publication items
are separate external work, not claims resolved by Lean's build.

### D-04 — Close the first research deliverable [DONE — local first-deliverable readiness; not published]

Dependencies: B-05, required C/N/L work, R-07, D-01/D-02.

- [x] Complete the agreed minimum N/M features (Q-02), informed by the finished
  lambda proof; do not require general elaboration or algebraic infrastructure.
- [x] Run all supported local builds/examples and inspect representative proof dependencies.
- [x] Resolve confirmed release-blocking defects and record remaining limitations.
- [x] Make supported dependencies, instructions, and experimental boundaries explicit.
- [x] Record the final source revision and reproducible verification commands.
- [x] State the research contribution without unsupported novelty/priority claims.

Done when: the classical core and the Church–Rosser client are usable and reproducible,
with NFun ergonomics demonstrated by the tutorial. No CI requirement is part of this gate.
The detailed review's first-release criteria also require full open-term/contextual
reduction, explicit convertibility-to-joinability, and no hidden termination or
closedness restriction. The historical review itself completed no implementation; task-9 delivery and
verification are recorded below.

### Task-9 delivery record — 2026-10-05

Scope: C-03/C-05/C-06/C-07, revalidation of N-01–N-05 and the focused M subset,
L-02/L-03, R-07, B-05 and D. Base revision
`b74ad349fa1b0e77dbb59b8225abe84be8e5b617`; all task-9 changes remain uncommitted.
Existing README edits, documentation, `.codex/` and `AGENTS.md` were preserved.

- `NFun.apply_smul_of_fixed` replaces genuinely duplicated action proofs in
  the support tactic, FCB and iterator; existing adapters/instances remain intact.
- Public iterator uniqueness, valid-bound independence, support and NFun results
  hide relational witnesses from client proofs. Candidate uniqueness requires no
  support/equivariance hypothesis; distinct bounds need not be nested.
- The tutorial exercises application, higher-order use, curry/uncurry, partial
  application, composition, rewriting, kernel-checked support construction,
  iteration/uniqueness, capture avoidance, composition, fresh term/rule induction,
  parallel compatibility/diamond, closures, Church–Rosser and normal uniqueness.
- CoreContracts checks definitional action coherence, conjugation versus ordinary
  pointwise action, least versus strong support, parameterized Some/Any and FCB,
  concretion renaming, and finite/cofinite logical hypotheses. Existing NFun
  empty-domain tests and freshness shadowing/diagnostic consumers remain passing.
- Documentation removes obsolete `NominalSets.*`/structural references, corrects
  the `freshFT` name, concretion's renamed-body case and projection-lift hypotheses,
  and records classical/noncomputable and atom/universe boundaries.
- The explicit example umbrella now includes previously orphaned constructor and
  term-interface clients as well as the new tutorial, core contracts and audit.
  The import check reaches all 37 library and 15 example modules.
- The audit selects declarations by source module, including 45 declarations
  outside the namespace-only historical scans. All 1,859 declarations pass;
  22 headline `#print axioms` results report only `propext`, `Classical.choice`,
  `Quot.sound`. No admission/custom-axiom/disabled-check addition was found.
- The complete build passes 1,033 jobs. Individually discovered example header
  warnings and the audit comment-placement warning were fixed without suppression.
  The final fresh source/config snapshot rebuilt all 1,033 jobs without
  warnings/errors, reused pinned dependency artifacts, and reran the full audit.
  Source/config SHA-256:
  `c3d05a4d32303bf10ec56952487916ac6aae92077a962184000f7c13f63d4170`;
  snapshot `/tmp/nominal-fresh-5t8pueey`. Script plus audit wall time was 43.25s,
  a local observation rather than a comparative performance claim.
- No seal, representation, dependency version or action priority changed. No
  elaboration speedup is claimed. The literal existential `ofFun` certificate
  simplification limitation is documented; a named `FinSupported` theorem permits
  normal `simp` in the tutorial while keeping the function computable.

See [the assessment](release-assessment.md), [tutorial](tutorial.md),
[validation instructions](validation.md) and
[pinned research correspondence](research-correspondence.md). C-04 convenience
wrappers, M-02/general M-03/M-04, A/P and generalized binders remain deferred.
D-03's external Rocq builds/assumption reports and publication corrections remain
unverified; none is silently claimed resolved by Lean validation.

D-04 readiness: no confirmed blocker remains for the supported local Lean
first deliverable. `lake build Nominal Instances Examples`, the explicit audit,
fresh project-artifact build, import/link checks and final diff review pass.
No clean dependency-bootstrap test was performed. The completed result is the
uncommitted snapshot identified above, not a published or committed release.

## 12. A — Generic algebraic nominal datatypes [DEFERRED]

The `fasapa/algebraic` branch is a useful sketch, not an implemented generic package.
Its two added modules have obsolete `NominalSets.*` imports, are not exported by
`Nominal/Set.lean`, and contain extensive placeholders. A default library build
must not be mistaken for verification of those modules.

### A-01 — Correct the signature and theorem statements

- [ ] Add atom arities distinct from recursive data positions. Lambda needs
  `A + X × X + [A]X`; the sketched `X + X × X + [A]X` has an empty initial algebra.
- [ ] Correct fixed-substitution equivariance to finite support or joint equivariance.
- [ ] Add actual recursive hypotheses through predicate lifting in generic induction.
- [ ] Thread avoidance contexts through binder induction; avoid unnecessarily requiring
  the user's fixed-parameter predicate to be equivariant.
- [ ] Tie the proposed algebra isomorphism to the actual constructor map.
- [ ] Audit structural isomorphism, adjunction, and uniqueness statements for unused
  parameters, reversed directions, and equations that do not express their names.
- [ ] Bind generalized support theorems to a canonical quotient action, rather than
  an arbitrary `Nominal` instance (`Structural.supp_genAbs`, review A-06).
- [ ] Replace nonexistence of any bare type equivalence by the intended failure of
  the canonical generalized-abstraction product comparison (review A-07).
- [ ] Correct the separated-product types and recheck the claimed distribution law
  on Unit/Unit before proof work (review A-08). The printed Pitts Exercise 4.6
  also fails this elementary check; this is an apparent source error, not an
  established published erratum or permission to import the claim uncritically.

Done when: a mathematical review finds the intended statements meaningful before
attempting to fill their proofs.

### A-02 — Choose and construct the generic carrier

Dependency: A-01; research decision Q-03.

- [ ] Compare generic raw syntax plus alpha quotient with an initial-chain construction.
- [ ] Resolve strict positivity and the circular nominal-instance dependency of a
  direct recursive constructor through `NameAbs α Syntax`.
- [ ] Stage interpreted carriers and their nominal instances coherently.
- [ ] Resolve the concrete interpretation errors after import repair: circular
  recursive instance synthesis, universe-zero Unit/Empty in Type u, and invalid
  instance/transport expressions. Import normalization does not make the sketch build.
- [ ] If using a chain, prove the required colimit-preservation facts; binary product/sum
  isomorphisms alone do not establish the necessary countable-chain result.
- [ ] Establish the constructor, action, support, and universal property for one small signature.

Done when: the carrier is kernel-accepted with proved structure and no axiomatized
initial object. Do not expand to every binding form before this example works.

### A-03 — Prove generic induction and supported recursion

Dependency: A-02.

- [ ] Implement functorial maps/laws and predicate lifting through arities.
- [ ] Prove initiality, computation, and uniqueness for the chosen map class.
- [ ] Distinguish equivariant maps from finitely supported/enriched maps and prove
  the support bounds required for fixed-parameter operations.
- [ ] Derive a genuine primitive recursor when original subterms are required,
  rather than documenting an iterator as the stronger principle.
- [ ] Derive fresh induction and instantiate the theory to the existing lambda interface.

Done when: generic results recover the concrete example with comparable hypotheses
and usability. Abstraction mapping on `NFun` is a key interface to investigate.

### A-04 — Extend only after a working generic example

- [ ] Add structural isomorphisms or adjunction infrastructure used by the selected construction.
- [ ] Consider multiple data sorts, mutual/nested recursion, and then multiple atom sorts.
- [ ] Treat simultaneous, list, set, pattern, and vacuous binders as explicit new specifications.
- [ ] Decide universe generalization against concrete semantic examples.

Done when: each extension has a motivating language and verified induction/recursion
behavior, with its own scope rather than an open-ended promise of generality.

## 13. P — Generated nominal package [DEFERRED]

Dependencies: usable N/M interfaces and a manually verified generic construction
or a deliberately restricted, verified generation scheme.

### P-01 — Specify a restricted datatype command

- [ ] Choose a supported signature grammar and reject unsupported recursion/binding forms clearly.
- [ ] Specify generated declarations, names, namespaces, universe parameters, and instances.
- [ ] Specify alpha equality, support equations, constructor properties, strong induction,
  and recursion as part of the generated contract.

### P-02 — Implement proof-producing generation

- [ ] Generate raw syntax/quotients or instantiate the generic carrier according to A-02.
- [ ] Produce action/support/equality proofs checked by Lean's kernel.
- [ ] Generate user-facing induction/recursion interfaces and function-tooling hooks.
- [ ] Diagnose unsupported inputs without leaving partially usable declarations behind.

### P-03 — Validate reuse beyond lambda calculus

- [ ] Reproduce the lambda interface through generation.
- [ ] Add a second language within the supported grammar to expose hard-coded assumptions.
- [ ] Compare generated proofs and ergonomics with the manual case study.
- [ ] Consider rule-induction generation only after concrete R-03 principles are understood.

Done when: users can declare a supported binder datatype and reason about it
without recreating the nominal infrastructure. This is a later release, not the
completion criterion for the current Church–Rosser deliverable.

## 14. Open decisions

| ID | Decision | Current recommendation | Resolve before |
| --- | --- | --- | --- |
| Q-01 | Direct parallel diamond or complete development? | RESOLVED 2026-10-05: direct diamond uses existing fresh induction, inversion, and simultaneous substitution; no additional API needed. Complete development is unnecessary for R-05. | Resolved in R-05 |
| Q-02 | Minimum metaprogramming for the first release? | RESOLVED 2026-10-02: reliable coercions/combinators, rewriting, focused support automation; general lambda elaboration follows later. Finish Church–Rosser to learn broader tooling needs. | Focused subset delivered; general elaboration deferred |
| Q-03 | Is generic initial-algebra theory itself a research goal? | RESOLVED 2026-10-02: mainly a means to usable datatype generation; recommend a restricted raw-quotient prototype after the case study | Apply at A-02 |
| Q-04 | Publication venue, deadline, maintenance expectations? | Deadline RESOLVED: none, prioritize correctness. Venue and maintenance expectations remain unspecified and need not block the proof | Release planning |
| Q-05 | Permanent layout for local examples/regressions? | RESOLVED: explicit `Examples.lean` import closure, including tutorial and axiom audit; `scripts/check-imports.py` checks coverage | B-05/N-01 |
| Q-06 | What warnings are deliberate design choices? | RESOLVED 2026-10-02 for supported sources: retain the public `Nominal.Set.Nominal` name with a scoped naming-linter exception; explicit discrete structures are instance-reducible but not global instances; all other build diagnostics resolved | Recheck on later changes |

## 15. Review and verification protocol

A complete review should independently check the code and the roadmap. Treat
this document as a set of recorded findings and proposals, not as authority that
a declaration exists or a theorem is correct.

Review dimensions:

- Mathematical definitions, theorem strength, assumptions, omitted cases, and proof dependencies.
- Build coverage, branch divergence, actual exports, and unsupported or unbuilt modules.
- Coherent permutation actions and the meaning of support/freshness across representations.
- Function usability, coercions, higher-order use, rewriting, currying, and elaborator behavior.
- BVC term/rule induction, recursion contracts, quotient boundaries, and substitution laws.
- Reduction/confluence dependencies and the validity of the proposed next steps.
- Tactic behavior, meaningful examples, inference performance, and failure diagnostics.
- Documentation and paper claims, constructive/classical distinctions, and research positioning.

Local verification commands should match the current layout:

```sh
# Default build covers both supported libraries:
lake build

# Explicit equivalent:
lake build Nominal Instances

# Complete libraries, tutorial and regression target:
lake build Nominal Instances Examples
lake env lean Examples/AxiomAudit.lean
python3 scripts/check-imports.py

# Fresh project artifacts with cached pinned dependencies:
python3 scripts/fresh-build.py

# Focused proof/example checks, after building their imports:
lake env lean path/to/Example.lean

# Whitespace/conflict hygiene:
git diff --check
```

Use `#print axioms` on selected public results. Scan for admissions, custom axioms,
unsafe declarations, disabled checks, and placeholder bodies, then inspect context:
commented experiments and module-signature requirements are not automatically
active logical assumptions. A complete build and meaningful usage proofs matter
more than a raw grep count.

For changes to tactics or elaboration, reproduce the failure first and retain a
small regression example whose conclusion needs the promised behavior. For proof
maintenance, compiling the changed theorem plus its dependent targets is the
primary verification. Avoid tests that merely repeat implementation details.

Use isolated scratch copies when comparing branches. Preserve dirty work. Record
external-source revisions and build limitations. Keep review suggestions distinct
from authorized implementation; a review should not silently merge branches or
refactor the entire library.

## 16. Work log

Append entries as work happens; keep historical evidence intact.

| Date | Task(s) | Result | Location/evidence | Remaining work |
| --- | --- | --- | --- | --- |
| 2026-10-02 | Initial assessment | Core, lambda, algebraic, Rocq, and articles reviewed | Revisions in section 4 | Findings tracked throughout this document |
| 2026-10-02 | B-01 | Core migration passed local build and independent review | `fasapa/next` working tree; 1003-job build | Record a commit when made; integrate lambda |
| 2026-10-02 | B-02 | Explicit atom freshness failure reproduced and repaired | `Freshness/Tactic.lean`; consuming regression examples | Automatic scan and nested splitting remain open |
| 2026-10-02 | B-03 | Migrated lambda build and representative axiom checks passed | Separate checkout; saved source patch | Not yet integrated into `fasapa/next` |
| 2026-10-02 | Roadmap update | Detailed task IDs, dependencies, completion criteria, and tracking added | This file | CI excluded at author's request; implementation tasks remain open |
| 2026-10-02 | Independent development review; B/C/N/M/L/R/A/D | Rebuilt current core and separate migrated lambda; broad axiom sweeps and consuming reproducers; verified source/statement and historical assumption distinctions | [Detailed review](reviews/2026-10-02-development-review.md); core `2c45db8`, lambda `9f04655`, algebraic `983adeb` | No fixes/integration performed; Rocq/TeX/Isabelle builds and clean dependency bootstrap unverified |
| 2026-10-02 | B-01/B-02 provenance correction | Migration and explicit-freshness repair already committed in `2c45db8`; initial work-log working-tree descriptions above remain historical | Git status/history and fresh project rebuild | Lambda integration and other tactic repairs remain TODO |
| 2026-10-02 | Q-02/Q-03/Q-04; sequencing | Author confirmed Church–Rosser-first cleanup/proof work, learning later infrastructure needs from it; focused NFun expectations; generic theory serves generation; no deadline | Review conversation and sections 1/3/14 | Sequencing and deadline resolved; venue/maintenance unspecified; implementation tasks unchanged |
| 2026-10-02 | B-04; B-05 build coverage | Integrated lambda modules, supporting lemmas, NFun split, and both default build targets; B-04 DONE, only two B-05 boxes completed | Uncommitted `fasapa/next` based on `2c45db8`, lambda `9f04655`; both build commands and fresh project-artifact builds passed (1,012 jobs); 32/32 modules; 1,636-declaration axiom sweep clean; consuming examples passed | Persistent validation target, clean-environment setup, comprehensive warning classification, and existing tactic/API/semantics tasks remain open; saved migration patch removed at author's request |
| 2026-10-02 | B-05 warning cleanup; raw Syntax scope | Resolved all supported build diagnostics; removed raw `Nominal.Syntax` at author's request, retaining lambda calculus | Both default/explicit working-tree and fresh project builds pass without warnings (1,009 jobs); 29/29 modules; 1,581-declaration axiom sweep clean; consumer/discrete-action checks passed; uncommitted working tree | Persistent validation target and clean-environment setup remain TODO; scoped naming exception documented |
| 2026-10-02 | C-01/C-02; B-05 persistent examples | Repaired expression identity, instance-based fresh selection, ambiguity/isolation/naming, and recursive product splitting; C-01/C-02 DONE | Uncommitted work on integrated `62b945a`; 39 persistent regression theorems; both supported libraries plus Examples build without warnings; 1,623-declaration axiom sweep and 16/64-input probes pass | Global instance priorities/unresolved-type filtering and standard product-action limits documented; clean-machine bootstrap and other roadmap tasks remain open |
| 2026-10-02 | L-01/R-01; two L-03 criteria | Consolidated Basic constructor/inversion APIs, relocated disjointness, and proved contraction-body independence with arbitrary replacements; preserved strong term induction and existing substitution laws; L-01/R-01 DONE | Uncommitted work based on `0277d3d`; declarations and evidence under L-01/R-01; two persistent public-API consumer files; explicit libraries/examples build warning-free (1,012 jobs); direct consumers and 1,606-declaration axiom sweep passed; tracked and untracked diff checks clean | R-02 reduction definitions are next; derivation induction and confluence remain absent; L-02/L-03/NFun polish and clean dependency bootstrap remain open; no commit/push |
| 2026-10-02 | N-01–N-05; M-01/focused M-03; lambda handler clients | Delivered coercion normalization, uncurry/inverses/action/support, equivariant/fixed-parameter adapters, focused capture-support automation and guarded macro subset; simplified existing substitution handlers without weakening statements or removing seals | Uncommitted work based on `0277d3d`, preserving L-01/R-01 edits; three new Examples targets; warning-free 1,015-job build; 1,683-declaration axiom audit; computation, independent review regressions, downstream examples, five-run timing/heartbeat comparison, and diff checks | M-02/general elaboration and broader M-03/M-04 remain deferred; global inference, arbitrary predicates and general support-set algebra require explicit evidence; no reduction/Church–Rosser/CI work, commit, or push |
| 2026-10-05 | R-02 | Defined unrestricted contextual beta and parallel reduction on quotient terms; proved nominal properties, reflexivity of parallel, constructor facts, and binder compatibility; reused Mathlib closures; R-02 DONE | Uncommitted `fasapa/next` based on `5434d4e`; three new modules plus 15 persistent examples; warning-free 1,021-job supported libraries/examples build; direct compilation, 20-result axiom inspection, persistent audit, import/diff/link checks, and independent mathematical review passed | R-03 fresh rule induction is next; parallel substitution, diamond, closure correspondence, and Church–Rosser remain open; no clean dependency bootstrap, commits, or pushes |
| 2026-10-05 | R-03 | Derived arbitrary-predicate/context fresh beta and parallel rule induction, finite-set forms, and chosen/common/context-fresh inversion; R-03 DONE | Uncommitted `fasapa/next` based on `026a54e`, preserving prior changes; 18 public principles and 12 persistent consumer proofs; warning-free 1,022-job libraries/examples build; direct module/consumer/downstream compilation; all principal axiom inspections and 1,790-declaration audit passed; independent theorem-strength/R-04-readiness review and diff/link checks passed | R-04 related-subject/related-replacement substitution is ready to start; diamond and Church–Rosser remain open; pinned dependencies reused, no clean bootstrap, commits, or pushes |
| 2026-10-05 | R-04 | Proved simultaneous parallel substitution compatibility on arbitrary open quotient terms, plus subject-only and replacement-only corollaries; R-04 DONE | Uncommitted `fasapa/next` based on `8a01417`, preserving prior changes; `ParallelSubstitution.lean` and seven persistent consumer proofs; warning-free 1,024-job libraries/examples build; direct module/consumer/downstream compilation; all three public axiom inspections and 1,793-declaration audit passed; independent contraction-hypothesis/example review and diff/link/import checks passed | R-05 confluence argument is ready to start; diamond, complete development, closure correspondence, and Church–Rosser remain open; pinned dependencies reused, no clean bootstrap, commits, or pushes |
| 2026-10-05 | R-05 | Proved direct parallel diamond on arbitrary open quotient terms using existing fresh rule induction, inversion, and simultaneous substitution; Q-01 resolved, R-05 DONE | Uncommitted `fasapa/next` based on `5732f32`, preserving prior changes; `Parallel.diamond`, six persistent consumer proofs, and explicit open/alpha-renamed joining terms; warning-free 1,026-job libraries/examples build; direct module/consumer/downstream compilation, principal axiom inspection and persistent audits, and independent theorem/overlap review passed | Ready for R-06 beta transfer; closure correspondence, beta confluence, Church–Rosser, and normal-form uniqueness remain open. Complete development unnecessary for this deliverable; pinned dependencies reused, no clean bootstrap, commits, or pushes |
| 2026-10-05 | R-06; mathematical R-07 | Proved beta/parallel inclusions and closure equality, beta confluence, Church–Rosser with full convertibility/joinability characterization, and both normal-form uniqueness formulations on arbitrary open quotient terms; R-06 DONE, R-07 IN PROGRESS | Uncommitted `fasapa/next` based on `ba0eacd`, preserving prior changes; exported `ChurchRosser.lean`, eleven theorems plus `BetaNormal`, and nine persistent client proofs; warning-free 1,028-job libraries/examples build, direct module/client/downstream checks, eleven principal axiom inspections and 1,806-declaration audit, independent statement/client reviews, and diff/link/import checks passed | Mathematical task 8 complete; task 9 retains broader R-07 interface review, compiling tutorial, API/assumption documentation, and reproducibility/release work. No normalization/termination or polished-release claim; pinned dependencies reused, no clean bootstrap, commits, or pushes |
| 2026-10-05 | Task 9: B-05, C-03/C-05–C-07, N revalidation, L-02/L-03, R-07, D-01/D-02/D-04 | Finished scoped client polish: shared fixed-NFun action lemma; public iterator uniqueness, support/NFun and bound independence; compiling end-to-end tutorial; accurate foundations/API/research documentation; complete example coverage and persistent validation tools | Uncommitted on `b74ad349fa1b0e77dbb59b8225abe84be8e5b617`, preserving preexisting work. Warning-free 1,033-job full and fresh-project builds; 37 library/15 example modules reached; 22 headline checks and module-origin sweep of 1,859 declarations use only standard foundations; independent reviews, link/name checks and final diff/whitespace checks passed. Fresh build reused pinned dependencies; source/config hash and 43.25s observation recorded above | Ready as scoped local first research deliverable, not published. D-03 external compiler/assumption checks and article corrections remain pending; clean dependency bootstrap untested; C-04/general M/A/P and generalized binders remain deferred. No speedup claimed, seal changes, CI, commits or pushes |

Suggested format for later detailed entries:

```text
Date / task ID / owner:
Status change:
Files and declarations:
Result and rationale:
Verification command and result:
Revision or explicit uncommitted/scratch location:
Remaining limitation or next dependency:
```
