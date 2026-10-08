# Nominal package roadmap

Last updated: 2026-10-08. Branch: `fasapa/nominal-package`.
Research baseline: `7fed53a2e5fc67379f86f085515e310e7c1fddb7`.
F01 assessment snapshot: `76966b1f2e44f594517442b6572e33abaa9038e0`.
Current inspected HEAD: `3c9d8dc527f7705b24c0308a2527e659ae933874`
(`some predicate + function support`). F04a/F04b are committed at `68956dd`,
F04c/general freshness at `9c1cb9a`, F04d at `32f3dba`, and F05 at this HEAD.
The working tree and index were clean when the PKG-01 investigation began.
F04c's specification and native plan were approved; its code, consumers, audit,
article and resolved independent reviews are delivered. F04c is DONE.
The author then approved general support-disjointness freshness as a bounded
F04c follow-up and requested three generalization investigations. The extension
and retained atom consumers pass. Its independent review found no Critical or
Important issues; one article proof-description correction was made and checked.
The new preference and checked proposals are recorded in
[the generalization report](research/2026-10-06-foundation-generalizations.md).
The author approved F04d's [written specification](superpowers/specs/2026-10-06-package-equivariant-quotients-design.md),
including the stronger supported-fiber characterization and quotient corollary.
Its [native implementation plan](superpowers/plans/2026-10-06-package-equivariant-quotients.md)
was subsequently approved. Native implementation, integrated Lean/article
checks and the fresh independent final review pass with no findings.
**F04d and the reconciled parent PKG-F04 are DONE**, with F04d committed at
`32f3dba`. F05 now has an author-approved
[written specification](superpowers/specs/2026-10-07-package-function-space-design.md)
and [source/probe investigation](research/2026-10-07-function-space-foundations.md).
Its [implementation plan](superpowers/plans/2026-10-07-package-function-space.md)
was approved for native execution. F05 code, public consumers, audit and article
pass integrated checks and the independent final review, with no findings.
**PKG-F05 is DONE**, committed at `3c9d8dc`.
**PKG-01 is DONE — complete, independently reviewed, uncommitted.**
The author selected the direct proof-field predicate record and scoped `И`,
then approved the [full specification](superpowers/specs/2026-10-07-package-predicate-foundations-design.md)
and [native implementation plan](superpowers/plans/2026-10-08-package-predicate-foundations.md).
Tasks 1–3 deliver ordinary logic, supported predicates, semantic views and a
single transferred Boolean algebra, quantifiers, sections and supported
collections. Tasks 4–5 deliver general pullback reflection and ordinary/supported
quotient descent with exact predicate support and individual-context freshness.
Tasks 6–7 deliver ordinary cofinite truth, supplied-bound Some/Any, context
adapters, bundled fresh projection and proved logical/quantifier boundaries.
Task 8 checks the complete accepted specification through nine public consumers,
compiled README examples, expanded axiom prints, import coverage, reconciled
exposition and a clean external article build. The independent technical review
passes with no correctness or acceptance defect; its one minor stale current
status paragraph is corrected. Final evidence and review disposition are below.
The run stops after Task 8; later PKG tasks were not started.
Earlier uncommitted-delivery descriptions retain their historical meaning.
F04a/F04b's specifications and native plans were approved, and their code,
consumers, audits, articles and independent final reviews passed.
F03b was committed at `34a8335`, following F02/F03a at `3d2196a`.
The original investigation started at
`4279ba92efacd77b3b96e507631502272b489999`; its verification remains historical
evidence, as recorded below.

This is the tracker for the new nominal-package research and development phase.
The [previous library roadmap](roadmap.md) retains the completed core and
Church–Rosser history. Stable PKG-00–PKG-11 identifiers are preserved; PKG-F01–F06
make the foundations required before or alongside them explicit.

The author's current decisions are recorded in the
[research brief](research/2026-10-05-nominal-package-brief.md). The
[research policy](research/README.md#architectural-freedom) makes existing code
optional reference material, and its
[implementation-location rule](research/README.md#implementation-location)
places all new implementation under top-level `Package/`, outside `Nominal/`.
The [architecture proposal](research/2026-10-05-package-architecture.md) compares
possible designs; it does not fix the implementation. This roadmap replaces the
earlier assumption that predicate work can start on a mandatory legacy core.
Revising the roadmap does not authorize later implementation increments. The
approved F02/F03a slice is delivered; subsequent specifications and scopes still
need their own agreement.

## Objective and architectural freedom

Researchers should be able to declare first-order syntax with binders,
operations and ordinary Lean `Prop` judgments, then prove results through
generated nominal interfaces. Every generated mathematical guarantee must be
justified by proofs checked by Lean's kernel.

- Use classical Lean/Mathlib, actual quotients and least supports. Noncomputable
  semantic operations are acceptable; executable fresh-name generation is not
  a requirement.
- Always investigate the pinned Mathlib APIs first and reuse suitable definitions,
  instances and theorems. Develop only the additional nominal interfaces and
  results that the existing infrastructure does not supply.
- Expose mathematical freshness and explicit induction avoidance. Hide support
  certificates and representation details where proved automation suffices,
  with ordinary Lean proof escape hatches when it does not.
- Initially target one atom sort, single/nested binders and multiple syntax
  categories. Specify universes, mutual recursion and container shapes rather
  than inheriting them accidentally from a prototype.
- Preserve arbitrary-predicate fresh term and rule induction. Supported
  predicates supply complementary tools; they do not restrict every motive.
- For each required layer, choose adoption, adaptation or reconstruction on
  mathematical and engineering evidence. The old nominal implementation may be
  replaced, while suitable Mathlib infrastructure should be reused. New code
  addresses demonstrated gaps rather than duplicating available foundations.
- Existing `Nominal/`, `Instances/` and examples provide optional theorems,
  counterexamples and client experience. Their public APIs, representations,
  module names, instance choices and universe restrictions do not bind the new
  package. Compatibility with `NFun`, `NameAbs`, FCB or old `Term` is not an
  acceptance condition.
- Preserve the completed development and unrelated work. Put new production
  code, generated examples and package-specific tests in `Package/`; specify
  the minimal Lake/root-file integration separately in PKG-F02. Do not grow the
  new package inside `Nominal/` or silently replace the manual case study.
- No deadline or CI. Do not merge the excluded syntax/unification branch or
  treat the old algebraic sketch as an established foundation. General algebra
  and automation must justify their cost through package clients.

Adoption still requires a reviewed contract: identify the exact imported
declarations, hypotheses, action and universe choices, proof dependencies,
public boundary and consuming examples. An import alone does not meet a task's
criterion. Conversely, an adopted and adequately checked dependency can meet
a foundation criterion without duplicating its proofs under a new name.

## Mathlib-first development

Prefer sound, mathematically natural general definitions and statements, with
specialized interfaces derived from them. The author explicitly values theory
reuse and stability as reasons for generalization, including before a specific
client requires it. Minimize hypotheses, preserve independently selected actions
and universes, and keep elementwise evidence where whole-carrier assumptions
would be unnecessary. This preference does not turn an unimplemented research
proposal into an established interface.

This policy applies to every research, design and implementation increment.
Before proposing a general-purpose definition, instance or proof, search the
pinned Mathlib source and inspect the relevant declarations. Use `rg` in
`.lake/packages/mathlib/Mathlib`; confirm exact statements, hypotheses, universes,
actions and imports with source inspection and small Lean checks when needed.
Do not infer absence from an unfamiliar name or from one unsuccessful search.

Prefer direct use, specialization, composition of existing lemmas, or a small
proved adapter over recreating infrastructure. This includes permutation/group
theory, actions, sets/finite sets, quotients, extensionality, relation closures
and existing proof automation. A domain-specific wrapper can still be justified
when it supplies a missing invariant, action boundary or usable public interface.

When custom code is needed, record the relevant Mathlib candidates and the
concrete gap or mismatch in the increment's design/research evidence. Check
mathematical meaning as well as types: an unsuitable action or weaker theorem
does not meet the required contract. Do not weaken a statement simply to use an
existing lemma. Keep this account proportionate; a full search transcript is
not required. Stay with the pinned dependencies rather than silently upgrading
to obtain another API.

Architectural freedom concerns independence from the old nominal implementation;
it is not a reason to rebuild Mathlib facilities. The article should distinguish
the Mathlib results used from the additional nominal results proved in Package.

## Agreed case studies

| Study | Proposed acceptance result | Distinct purpose |
| --- | --- | --- |
| Lambda calculus | Replay open-term Church–Rosser through generated syntax, functions and judgments | Complete workflow; fresh rule induction, inversion and simultaneous substitution |
| First-order logic | Substitution admissibility for natural deduction, including universal introduction and existential elimination | Multiple categories, finite contexts and eigenvariable transport |
| Lambda calculus with `let` | Expansion/substitution compatibility and contextual reduction simulation into base lambda calculus | Binder scopes over the body and excludes the defining term |
| π-calculus | Transition equivariance and fresh bound-residual inversion; then a selected behavioral congruence theorem | One name can bind jointly across a transition label and continuation |
| μ-calculus | Proposed modal variant: positive substitution, alpha-invariant semantics and fixed-point unfolding | Positivity and semantic environments need contracts separate from binding |

All five studies were selected by the author. Lambda with `let` replaces the
alternative imperative-local example. The first complete generated workflow
uses lambda and FOL; the other three remain subsequent milestones. Precise π
transition semantics and the μ-calculus variant remain open decisions. The
foundation redesign changes the route to these studies, not their inclusion.

## Status and evidence policy

**DONE** means the stated acceptance criterion is met with recorded evidence.
**TODO** means work has not been delivered. **IN PROGRESS** identifies active
research or implementation, without implying design approval. Use checked boxes
only for delivered results. F02 and F03a have committed implementation,
verification evidence and a clean independent final review. F01 remains open
for later per-layer choices.
F03b is delivered with matching LaTeX exposition and a clean independent review.
F04a is delivered with matching LaTeX exposition and a clean independent final review.
F04b is delivered with matching LaTeX exposition and a clean independent final
review. F04a/F04b are committed at `68956dd`. F04c is delivered with passing validation and resolved independent final review.
F04d is delivered with passing checks and a clean independent final review;
F05 is delivered with passing checks and independent final review, committed at
`3c9d8dc`. F06 remains unimplemented. PKG-01 Tasks 1–8 and all three phases
are complete, independently reviewed and uncommitted. The current authorization
ends after Task 8; later PKG tasks require a separate request.

Distinguish user decisions, integrated theorems, standalone probes, source
readings, mathematical analyses and proposed interfaces. Record revision and
working-tree state, commands actually run, cache conditions, limitations and
counterexamples. Scratch proofs do not complete an integration task. The old
library's build and axiom audit do not cover a new `Package` target.

**Every substantive implementation increment also delivers its article update.**
Write the relevant mathematics in LaTeX under `docs/article/` while developing
the Package code. The article is a selective research publication about the system
and mathematics: central definitions/theorems/proof ideas, architectural insights,
limitations, counterexamples and grounded comparisons with relevant theories and
systems. Select details for their explanatory value; no complete API inventory,
routine-proof catalogue or invented novelty is required.

Exclude development-stage/task IDs, work logs, status/delivery and approval
narratives, branch/commit bookkeeping, agent assignments, review verdicts, and
audit/build commands, results, counts, cache conditions and diagnostic histories
from the manuscript. Preserve these records here and in research notes.
Mathematical dependencies, logical assumptions and relevant Lean correspondence
remain appropriate. This [publication policy](research/2026-10-05-article-plan.md#publication-content-policy)
supersedes earlier directions to include operational evidence in the article.

Before marking an increment DONE, check the relevant statements, proofs,
hypotheses, declaration references and limitations against the Lean results,
and compile the article. Record verification and review evidence in this tracker.
PKG-11 coordinates this ongoing work; it is not a final writing phase. Routine
implementation changes may need no added manuscript text; record that editorial
decision internally. Do not present proposed results as established. Publication
polish is not required to complete an increment, but accurate exposition is.

## Dashboard and dependency order

| ID | Status | Dependencies | Deliverable |
| --- | --- | --- | --- |
| PKG-00 | DONE — historical research proposal; revised design pending | Completed core/Church–Rosser as research evidence | Architecture comparison, contracts, probes and article outline |
| PKG-F01 | IN PROGRESS — first foundation spec approved; later layer choices remain proposed | Current user decisions; PKG-00 evidence; pinned algebraic source | Algebraic-sketch investigation, foundation/API contract and per-layer adoption/adaptation/reconstruction decisions |
| PKG-F02 | DONE — verified, committed delivery | Approved F01 boundary for F02/F03a; approved native plan | `Package/` root, Lake/import boundary and production audit coverage |
| PKG-F03 | DONE — F03a and F03b verified and committed | Approved F01 boundary; F02; approved F03b native plan | Atoms, finite permutations, actions and equivariance |
| PKG-F04 | DONE — all four slices verified and committed | PKG-F03; F04a → F04b → F04c/F04d | Finite support calculus, nominality/least support, canonical instances/freshness, canonical equivariant quotients |
| PKG-F05 | DONE — verified delivery committed at `3c9d8dc` | PKG-F04; delivered F05a → F05b → F05c | Function objects, ordinary map/predicate certificates and supported values |
| PKG-F06 | TODO | PKG-F04/F05 | Abstraction, concretion or equivalent certified binder-descent facility |
| PKG-01 | DONE — Tasks 1–8 and independent whole-change review complete, uncommitted | Delivered PKG-F04/F05; 01a, independent ordinary 01b/01c, then bundled adapters | Supported predicates, logical/order calculus, pullback/descent and cofinite Some/Any |
| PKG-02 | TODO | PKG-F04; approved backend/grammar from PKG-F01 | Manual syntax-carrier certificate with constructor/action/support laws |
| PKG-03 | TODO | PKG-02 and PKG-F06 | Fresh term induction and supported iteration |
| PKG-04 | TODO | PKG-02/03 | Multiple/direct mutual categories and finite-context infrastructure |
| PKG-05 | TODO | PKG-01/03/04 | Datatype/function commands and a distinct primitive-recursion contract |
| PKG-06 | TODO | PKG-01/03/04; PKG-05 for command integration | Certified fresh judgment induction, inversion and generation |
| PKG-07 | TODO | PKG-05/06 | Complete generated lambda and FOL workflows |
| PKG-08 | TODO | PKG-07 and a scoped let specification | Lambda with let and expansion correctness |
| PKG-09 | TODO | PKG-07 and a residual-binding/transition specification | π-calculus case study |
| PKG-10 | TODO | PKG-07 and a positivity/semantic specification | μ-calculus case study |
| PKG-11 | IN PROGRESS — foundation/function exposition plus predicate and Some/Any mathematics | Alongside every task | Article, decision record and claim-to-Lean evidence ledger |

The implementation dependency spine is
`F01 → F02 → F03a → F03b → F04 → F05 → PKG-01`, with concurrent
LaTeX work tracked under PKG-11 at each step. F02/F03a/F03b are delivered.
F04 is split into `F04a → F04b → F04c/F04d`; F04a is delivered under its
approved specification and native plan, with a clean independent final review.
F04b is likewise delivered under its approved spec/native plan with a clean
independent final review and reconciled article.
F04c and F04d can be investigated independently after
F04b, while each retains a separate delivery/review boundary. These steps can
be small where reviewed
dependencies already discharge the contract; none prescribes a complete rewrite
or a full catalogue of nominal constructions.

After F04, carrier work (PKG-02) can progress independently of most predicate
lemmas. F06 follows the chosen supported-handler interface in F05 and can run
alongside PKG-01; PKG-03 requires both the carrier and binder-descent results.
PKG-04 extends that certified construction. PKG-06's mathematical criterion can
be proved alongside PKG-05; its generated commands must then use the certified
datatype/function boundary. PKG-07 integrates both. PKG-08–10 can proceed in
parallel once their individual semantics are specified. PKG-11 accompanies every
phase. Any change to this graph must record which acceptance obligation moved.

Each implementation increment gets a bounded specification and plan. The
F01 boundary needed for F02 + F03a and its native implementation plan are
approved; the implemented increment passed independent final review. Later
per-layer choices remain proposed and do not expand this slice.
PKG-01 is not the first implementation task.

## Foundation task contracts

### PKG-F01 — Algebraic-sketch investigation and foundation contract

- [ ] For each new foundation decision, inspect pinned Mathlib first. Record
  the declarations that can supply the required contract and the specific gaps
  requiring adaptation or new nominal theory.
- [x] Inspect the actual algebraic sketch at
  `983adeb9b80f75fb7c77c05acfd2fcef16db1d46`, the previously reviewed
  `origin/fasapa/algebraic` snapshot. Read both `Nominal/Set/Algebraic.lean` and
  `Nominal/Set/Structural.lean` from Git, without switching branches or merging.
- [x] Check the [existing assessment](research/2026-10-05-backend-comparison.md#reassessment-of-the-historical-branch)
  against those declarations. Distinguish false statements, statements weaker
  than their advertised contract, missing proofs, and elaboration/representation
  obstacles. Reuse verified evidence where applicable; reproduce decisive
  counterexamples or bounded probes when the new design relies on their claims.
- [x] Investigate useful ideas independently of their current implementations:
  binding signatures, functor maps, algebra morphisms, predicate lifting,
  initiality, supported recursion and abstraction descent. Identify which ideas
  help the lambda/FOL workflow and what corrected contracts or new proofs they need.
- [x] Inventory only the layers needed for the first lambda/FOL workflow:
  atoms/permutations/actions, support/freshness, products/quotients, function and
  predicate inputs, binder descent, syntax carriers, recursion and rule transport.
- [ ] For each layer, compare adoption, adaptation and reconstruction. Record
  the selected boundary, dependency costs, required proofs and why it serves
  the clients; retain unresolved choices explicitly. Include the algebraic
  sketch's usable ideas and rejected approaches in this comparison, without
  giving that sketch or the completed core architectural priority.
- [x] Specify proposed atom assumptions, universes, action-instance coherence, function
  conjugation, truth/predicate representation, equality/extensionality and the
  treatment of fixed nominal parameters.
- [x] Record a candidate syntax grammar and client assumptions to test the
  foundation choices. Settle only the scope/universe decisions that affect the
  next increment; later command details and π/μ semantics need not be fixed.
  Compare backends without requiring the former staged-hybrid recommendation
  or compatibility with legacy APIs.
- [x] Design ordinary application, useful equations, proof escape hatches and
  consuming validation examples before naming the internal wrappers.
- [x] Agree a bounded first implementation specification and its verification
  coverage, including which existing dependencies, if any, it will adopt and
  the LaTeX sections to develop with that increment.

Delivered research: [direct source investigation](research/2026-10-05-algebraic-source-investigation.md),
[readiness and proposed contracts](research/2026-10-05-pkg01-readiness.md), and
[new scratch evidence](research/2026-10-05-predicate-design-probes.md).
The author approved the [first written specification](superpowers/specs/2026-10-05-package-foundation-kernel-design.md)
for F02 + F03a. Its [implementation plan](superpowers/plans/2026-10-05-package-foundation-kernel.md)
is approved for native execution. This accepts the required F01
boundary for that increment; the broader predicate/support/backend choices
remain proposals. The recorded implementation approval covers the delivered
increment; it does not approve every later layer at once.

Required source-reading commands from the current checkout:

```sh
git show 983adeb9b80f75fb7c77c05acfd2fcef16db1d46:Nominal/Set/Algebraic.lean
git show 983adeb9b80f75fb7c77c05acfd2fcef16db1d46:Nominal/Set/Structural.lean
```

Record any additionally inspected revision separately; a moving branch name is
not a replacement for the pinned evidence. If source or a compatible build is
unavailable, state the limit explicitly. Inspect the required statements and
imports rather than assuming a default build reaches these historical modules.

Acceptance requires:

1. A source-referenced sketch assessment with revision, declaration/statement,
   evidence or counterexample, classification, correction or open obligation,
   and relevance to the new Package design. Record useful ideas as well as defects.
2. An explicit disposition for each investigated idea: adopt, adapt, rederive,
   defer or reject, with rationale, dependencies and unresolved issues. Validate
   any proposed initiality/isomorphism against its actual constructors and maps;
   distinguish supported from equivariant maps and iteration from recursion.
3. A reviewed foundation design/dependency matrix with concrete public signatures
   or mathematical contracts, positive/negative examples and a bounded next plan.

Reading only the assessment or inventorying old declarations is insufficient.
The investigation does not require repairing or filling every placeholder in
the sketch, merging it, adopting its architecture, or developing a categorical
initial-chain construction. All new implementation remains under `Package/`.
PKG-F01 is a research/design task and can finish without production Lean changes.

### PKG-F02 — Package boundary and validation setup

- [x] Establish top-level `Package/` as the location of new implementation,
  with a public import root and explicit internal/public module boundaries.
- [x] Add the minimal Lake/root-file configuration for a separately identifiable
  package target. Specify whether a conventional root umbrella such as
  `Package.lean` is required; do not scatter implementation outside `Package/`.
- [x] Put the axiom audit under `Package/` and make its import/build coverage
  explicit. The author removed standalone Package examples during execution;
  persistent usage examples are reserved for future case studies.
- [x] Define an import policy for any adopted legacy dependencies and a check
  that `Nominal/` and its manual clients remain preserved.
- [x] Document commands that actually reach the new target and audit; retain
  the pinned toolchain and dependencies. Temporary public-import checks supply
  this increment's usage evidence; persistent examples belong to case studies.

Accept a minimal compiling package boundary, temporary public-import checks and
verified production/audit coverage reports. An empty target is setup evidence
only, not proof of any foundation theorem. The working-tree implementation now supplies
this boundary and passed independent final review.

The approved first slice combines F02 with **F03a**, a bounded
permutation/action kernel. Its amended specification gives separate production
and audit roots under Package and retains the reference default targets.
The only Lake change is registration of the Package library. A full fresh-build
helper is deferred;
the existing reference helper must not be reported as Package validation.

### PKG-F03 — Atoms, permutations, actions and equivariance

- [x] Supply the finite-permutation group and swaps without unnecessary
  infinitude or countability assumptions; retain their stated equality requirements.
- [x] Prove the remaining permutation laws needed for the selected support
  construction. Introduce infinite-atom assumptions only where later results need them.
- [x] Prove or review adopted action laws, equivariance and canonical actions
  on atoms and the initial data shapes; document universe and instance choices.
- [x] Provide public application/composition/renaming equations sufficient for
  consuming proofs without unfolding representation internals.
- [x] Test action composition/inverses and instance coherence, including any
  permutation conjugation and discrete-data actions used by the design.

Accept proved foundations or an explicitly justified adopted dependency, with
package-boundary consumers and standard axioms only. Do not assume atom
countability or a particular concrete atom encoding unless the reviewed contract
requires it. No support or fresh-name theorem follows from group laws alone.

The approved **F03a** includes finite-moved permutations, swaps, canonical atom
action, standard product/Finset actions, discrete data and equivariance.
**F03b** supplies controlled swap factorization, arbitrary-set avoidance and the
selected-action criterion through `Perm.swap_factorization`,
`Perm.swap_factorization_avoiding`, `Perm.smul_eq_of_swap_smul_eq`, and
`Perm.forall_smul_eq_iff_swap_smul_eq`. Both slices use temporary public-import
checks; persistent usage examples remain deferred to case studies.

#### F03b — Controlled swaps preserving an avoidance set

The [bounded F03b specification](superpowers/specs/2026-10-05-package-controlled-swaps-design.md)
is approved by the author. It specifies four public results, arbitrary-set
avoidance, a restricted-generator Mathlib proof route and concurrent LaTeX work.
The [implementation plan](superpowers/plans/2026-10-05-package-controlled-swaps.md)
was approved for native execution. All four public results are implemented and
kernel-checked; the accompanying article is reconciled and compiled. Independent
final review found no Critical, Important or Minor issues. See the delivery log
for commands, counts and preservation evidence.

- [x] Investigate Mathlib's permutation factorization/induction and finite-set
  results before writing a new proof. Check whether they provide the required
  control over endpoints directly or through a small specialization/adapter.
- [x] Prove that each finite permutation is a finite product of swaps whose
  distinct endpoints lie in that permutation's moved set, or give an equivalent
  induction principle with the same control over endpoints.
- [x] Derive the avoidance consequence: if the permutation fixes a set S
  pointwise, the factorization uses swaps with both endpoints outside S.
- [x] Consume the result through `import Package`: for an arbitrary selected
  `MulAction (Perm A) X`, invariance of x under all swaps outside S implies
  invariance under every finite permutation fixing S pointwise.
- [x] Cover identity/empty factorization and finite atom carriers; no
  `Infinite A` hypothesis is needed for this factorization. Use temporary
  public-import checks, preserving the author's case-study-only examples policy.
- [x] Extend `docs/article/sections/foundations.tex` concurrently with the
  factorization statement, proof strategy and avoidance corollary. At delivery,
  connect them to relevant declarations and compile LaTeX; record the verification
  evidence in this roadmap.

Review the exact statement/proof route before implementation. An unrestricted
swap-generation theorem alone does not state the required avoidance guarantee.
F03a already supplies group/action and basic swap laws; F03b does not introduce
support predicates, least support, freshness or atom selection. Those belong to
F04. Completion requires the scoped permutation result, consuming verification,
production/audit coverage and the accompanying article update.

### PKG-F04 — Support, freshness and required constructions

**Delivered in four bounded phases.** F04a–F04d are slices of this existing stable
task ID, not replacements for PKG-F04. The author supplied the scope and ordering;
each slice had its concrete specification, implementation plan and execution
agreement. The full outline did not authorize a single combined implementation.
All four deliveries and the overall criteria are now verified. F02/F03a/F03b
remain delivered and are not reopened.

| Slice | Status | Dependencies | Article section assigned to its spec/plan |
| --- | --- | --- | --- |
| F04a — Finite support calculus | DONE — verified, committed at `68956dd`; clean final review | Delivered F03b and selected actions | `docs/article/sections/support.tex`, `sec:finite-support` |
| F04b — Nominality and least support | DONE — verified, committed at `68956dd`; clean final review | F04a, especially finite intersection | `docs/article/sections/support.tex`, `sec:least-support` |
| F04c — Canonical instances and freshness | DONE — committed at `9c1cb9a`, including general freshness; final reviews resolved | F04a/F04b; delivered canonical actions | `docs/article/sections/freshness.tex`, `sec:canonical-support` and `sec:freshness` |
| F04d — Canonical equivariant quotients | DONE — verified and committed at `32f3dba`; clean independent final review | F03 actions; F04a support bounds; F04b nominality/least support; delivered F04c for canonical/freshness consumers | `docs/article/sections/quotients.tex`, `sec:equivariant-quotients` |

All four assigned article sections are written. F04d's action construction and
support preservation need no infinitude;
its full delivery follows F04b for the nominality and least-support conclusions.
F04c is not a mathematical prerequisite for F04d: a quotient consumer may use
explicit local support evidence if canonical instances are not yet delivered.
No obligation has moved to F05; ordinary equivariant functions and explicit
support certificates suffice for these phases.

#### F04a — Finite support calculus

The [written F04a specification](superpowers/specs/2026-10-05-package-finite-support-design.md)
is approved by the author. It selects a finite-set abbreviation of pinned Mathlib
`MulAction.Supports`, an
elementwise `FinitelySupported A x` property, and one new module
`Package/Foundations/Support.lean`. It records exact signatures, assumptions,
Mathlib reuse, conjugation transport, the F03b specialization, intersection
proof and finite-atom boundary test. Its
[implementation plan](superpowers/plans/2026-10-05-package-finite-support.md)
was approved for native execution. All 18 agreed public declarations are
implemented and checked, with matching LaTeX mathematics and meaningful
temporary public-import consumers. Integrated validation passed; independent
final review found no Critical, Important or Minor issues. F04a is DONE.

- [x] Inspect the current F03b interface and pinned Mathlib support, finite-set,
  action and quotient candidates; record the four phase boundaries and exclusions.
- [x] Prepare the bounded written F04a specification and assign its concurrent
  LaTeX section, mathematical proofs, evidence reconciliation and acceptance checks.
- [x] Obtain agreement on the concrete written specification and prepare its
  implementation plan with concurrent article tasks.
- [x] Review the implementation plan and agree execution before production changes.
- [x] Adopt the pointwise-fixing support predicate through a thin finite-bound
  interface and define finite supportedness for individual action elements.
- [x] Supply monotonicity, empty-support invariance, conjugation transport,
  equivariant-image and product bounds, and existential closure.
- [x] Specialize the delivered F03b swap criterion without duplicating controlled
  factorization. Definitions, basic laws and this criterion need no `Infinite A`.
- [x] Prove binary intersection of finite supports under `Infinite A`; check
  the two-atom example where either singleton supports an atom but their empty
  intersection does not. Keep decidable-equality assumptions local to operations
  whose statements need them.
- [x] Deliver meaningful temporary public-import consumers, full new-module audit
  coverage and the reconciled/compiled `sec:finite-support` article section.

This slice supplies no least-support operator, nominality class, freshness API,
predicate bundle, quotient action or new function-space action.

#### F04b — Nominality and least support

The [approved written specification](superpowers/specs/2026-10-06-package-least-support-design.md)
reuses delivered F04a and selects Mathlib's well-founded Finset inclusion
order plus `supports_inter` for least-support existence. It specifies a
proof-only `Nominal A X`, elementwise `hx.support`, convenient `support A x`,
their agreement and exact assumption boundaries in one new
`Package/Foundations/Nominal.lean` module. The author approved it on 2026-10-06.
The [native implementation plan](superpowers/plans/2026-10-06-package-least-support.md)
was subsequently approved. All 19 public declarations and their consumers are
implemented and checked, with a passing whole-production audit and matching
compiled article. The requested fresh independent final review found no Critical,
Important or Minor issues. F04b is DONE; its delivery is committed at `68956dd`.

- [x] Verify branch/history/status and delivered F04a; inspect pinned Mathlib
  minimum, cardinality and order APIs and compare least-support constructions.
- [x] Prepare a bounded written specification with exact elementwise/carrier
  interfaces, witness independence, proof strategy, imports, article work and
  meaningful acceptance checks.
- [x] Obtain agreement on the concrete written F04b specification.
- [x] Prepare the native implementation plan with concurrent article tasks,
  meaningful consumers and one independent final review.
- [x] Obtain written-plan approval before production changes; preserve prior
  approvals and existing uncommitted work.
- [x] Review a proof-only `Nominal A X` certificate for the already selected
  `MulAction (Perm A) X`; it must not introduce or replace the action. Nominality
  itself does not require infinite atoms.
- [x] Under `Infinite A`, construct least finite support, prove that it supports
  its element and is contained in every finite supporting bound, and establish
  `Supports S x ↔ support x ⊆ S` and `support (π • x) = π • support x`.
- [x] Supply the empty-support characterization and required equivariant-image
  bounds. Keep finite-support evidence in proof fields and review an interface
  for individually supported elements without carrier-wide nominality.
- [x] Deliver consumers, audits and the concurrent `sec:least-support` section;
  distinguish least support from strong support throughout.
  Integrated checks and final independent review pass.

#### F04c — Canonical instances and freshness

The [approved written specification](superpowers/specs/2026-10-06-package-canonical-freshness-design.md)
uses the delivered interfaces and selected actions. It specifies four canonical
nominality certificates, exact support formulas with both inclusions,
elementwise `hx.Fresh a` and convenient `Fresh A a x`, transport, swaps and
finite combined avoidance. It specifies two foundation modules and assigns
concurrent article work and meaningful public-import acceptance checks.
The author approved it on 2026-10-06. Its
[native implementation plan](superpowers/plans/2026-10-06-package-canonical-freshness.md)
was approved for native execution. All 34 production interfaces and seven
temporary consumers now check, with the reconciled 20-page article. The production audit passes with 178 declarations in seven defining modules; source
coverage reaches eight production modules including the root and one audit.
The fresh independent final review found no Critical or Important issues. Its
two minor tracker/test findings were corrected and the affected checks passed.
F04c is DONE; this delivery and its follow-up are now committed at `9c1cb9a`.

**Approved follow-up:** general freshness now relates two nominal elements by
disjoint supports. `hx.FreshWith hy` retains the two-element evidence route and
`hx.Fresh a` is the atom specialization. Both product sides, disjoint sufficient
bounds, finite-set contexts and equivariant images have general laws. This
supersedes the initial atom-only scope. All 33 added declarations and eight
consumers pass; the direct audit now covers 226 declarations and the article has
21 pages. Follow-up independent review is resolved. The seven other checked
[generalization proposals](research/2026-10-06-foundation-generalizations.md)
remain research evidence for future design, not hidden implementation in F04c.

- [x] Verify branch/history/status and committed F04a/F04b; inspect delivered
  foundations, pinned Mathlib APIs, research constraints and current manuscript.
- [x] Prepare a bounded written specification with exact public statements,
  action/instance policy, assumption separation, evidence interfaces, imports,
  proof strategies, article work and acceptance checks.
- [x] Obtain agreement on the concrete written F04c specification.
- [x] Prepare the native implementation plan with concurrent article tasks,
  meaningful consumers and one fresh independent final review.
- [x] Obtain written-plan approval before production changes, preserving
  prior approvals and the selected execution method.
- [x] Supply nominality under the intended actions on atoms, `Discrete A X`,
  products and finite atom sets with the existing scoped image action.
- [x] Prove exact support formulas, with their required hypotheses:
  `support a = {a}`, `support (Discrete.mk x) = ∅`,
  `support (x,y) = support x ∪ support y`, and `support (S : Finset A) = S`.
- [x] Define atom freshness by nonmembership in least support; derive freshness
  from sufficient bounds, permutation transport and swaps fixing an element
  when both endpoints are fresh.
- [x] Use Mathlib's infinite/finite-set results for avoiding finite bounds and
  combined nominal contexts, including nested products. No executable or
  finitely supported fresh-selector function is required.
- [x] Retain the unordered-pair counterexample: swapping distinct a,b fixes
  `{a,b}` but moves both atoms of its least support. Do not infer nominality of
  arbitrary functions or bare permutations under their default actions.
- [x] Deliver consumers, audits and both assigned LaTeX subsections together.
- [x] Complete the fresh independent final review and resolve its findings
  before marking F04c DONE.

#### F04d — Canonical equivariant quotients

The [approved written specification](superpowers/specs/2026-10-06-package-equivariant-quotients-design.md)
selects explicit general scalar/monoid quotient constructors from an ordinary
invariance proof, with no blanket action or nominality instance. Projection
contracts refer to the constructed action. It includes the general equivariant
surjection nominality theorem, quotient support adapters, and existing general
freshness-map consumers. The approved stronger characterization generalizes
Pitts' representative-support characterization to a supported fiber of an
equivariant map, then specializes it to the quotient intersection formula.
The author approved the whole written specification on 2026-10-06.
Its [native plan](superpowers/plans/2026-10-06-package-equivariant-quotients.md)
assigns 15 declarations to three mathematical tasks and one integrated
validation/documentation/review task, with concurrent LaTeX and seven temporary
public-import consumers. The author approved that concrete plan before production
changes. All interfaces, consumers, integrated audit/coverage and matching article
now pass. The requested fresh independent final review found no Critical,
Important or Minor issues and independently rebuilt Package artifacts and the
article. F04d is DONE, committed at `32f3dba`; the overall F04 criteria are reconciled below.
The other checked generalizations are dispositioned individually, not silently
promoted to production APIs. Native execution and one fresh independent final
review remain selected; no other proposal has been silently implemented.

- [x] Verify actual branch/history/status and delivered foundations, including
  the general-freshness amendment; inspect the pinned quotient/action APIs.
- [x] Write a bounded specification with exact assumptions and universes,
  compatibility input, action-selection policy, elementwise/carrier contracts,
  mathematical boundaries, modules, article work and meaningful acceptance checks.
- [x] Obtain agreement on the written specification, including the stronger
  representative-support characterization and its quotient corollary.
- [x] Prepare the native implementation plan, preserving earlier approvals
  and the chosen method.
- [x] Obtain written-plan approval before production changes.
- [x] Construct the canonical quotient action for a setoid preserved by the
  selected action, through a natural general monoid construction and its
  permutation specialization, keeping atom/carrier universes independent.
  Inspect and reuse `Quotient.map`, `Quotient.map_mk` and
  `Function.Surjective.mulAction` where suitable.
- [x] Prove `π • q x = q (π • x)`, projection surjectivity and equivariance;
  preserve support bounds and inherit finite supportedness and nominality.
- [x] Prove `support (q x) ⊆ support x` with the least-support hypotheses and
  include a meaningful quotient with strict decrease. An unrelated quotient
  action does not satisfy this canonical-projection contract.
- [x] Prove the general supported-fiber characterization and the exact
  quotient-support intersection formula; retain nonattainment and failure of
  reverse supportedness as distinct mathematical boundaries.
- [x] Consume general freshness-map laws for nominal and individually supported
  contexts; test coherence with compatibility and canonical evidence active.
- [x] Deliver consumers, audit coverage and `sec:equivariant-quotients` together.
  Full predicate descent/support reflection remains PKG-01. The approved
  representative-support characterization does not assert equality with a
  chosen representative's support or supply a representative attaining it.
- [x] Complete the fresh independent final review, resolve findings, then
  reconcile every overall F04 criterion before marking PKG-F04 complete.

#### Overall F04 completion

- [x] Prove or adopt finite support, least support and their transport/minimality
  laws, with each required atom hypothesis explicit.
- [x] Establish fresh-atom existence, avoidance of finite combined contexts and
  the freshness/renaming laws consumed by the first workflow.
- [x] Supply required product and equivariant-quotient actions/support results.
  State upper bounds separately from exact support formulas and prove any exact
  formula that is advertised.
- [x] Validate fixed parameters, nested product avoidance and quotient descent;
  retain a counterexample separating least support from strong support.

Accept ordinary package clients that use the support and freshness conclusions,
plus reviewed quotient well-definedness. Fixing an element need not fix every
atom in its support pointwise. Add other containers only when a stated client
requires them; a complete core catalogue is not a prerequisite for PKG-01.
Mark PKG-F04 complete only when all four agreed slice contracts, their consumers,
audit obligations and concurrent LaTeX sections are delivered. Supported-function
objects, `SupportsMap`/`SupportsPred`, bundled predicates and Some/Any remain
F05/PKG-01; abstraction, FCB, recursion and generators remain later work.

**PKG-F04 is DONE.** The execution work log maps each overall criterion to
current passing consumers and preserved delivered theory. The independent final
review checked that reconciliation. F04d is committed at `32f3dba`;
F05 and PKG-01 are not marked delivered by this closure.

### PKG-F05 — Function-space and predicate-input foundation

**DONE — approved native implementation, integrated checks and independent final review;
committed at `3c9d8dc`.** The
[written specification](superpowers/specs/2026-10-07-package-function-space-design.md)
selects a hybrid: ordinary map/predicate certificates, a distinct full
conjugation function carrier, and a proof-field supported-function bundle.
The [investigation](research/2026-10-07-function-space-foundations.md) compares
all four requested approaches, pinned Mathlib, Pitts and bounded probes.
This supersedes the earlier immediate-client-only restriction: natural
mathematical generality is a foundation criterion, not a reason to build
unrelated category infrastructure or metaprogramming.

- [x] Inventory current foundations and pinned Mathlib; investigate Pitts' book.
- [x] Compare ordinary certificates, full function objects, supported bundles
  and a hybrid; investigate ordinary-first versus bundle-first consumers.
- [x] Prepare exact contracts, boundary probes, article exposition and a written
  specification with phase dependencies for review.
- [x] Author approves the written specification and three-phase hybrid scope.
- [x] Prepare the [implementation plan](superpowers/plans/2026-10-07-package-function-space.md),
  including exact interfaces, consumers, article work and verification.
- [x] Author reviewed the implementation plan and selected native execution.
- [x] F05a: full conjugation carrier, coherent FunLike, group evaluation,
  composition/pairing and curry/uncurry, general support correspondence.
- [x] F05b: ordinary map and predicate certificates, elementwise evaluation and
  fixed-parameter bounds, transport, discrete-truth bridge and negative boundaries.
- [x] F05c: supported proof-field values, nominality, exact embedding support,
  ordinary higher-order use, admissible curry and empty-domain behavior.
- [x] Integrate the selected interface under Package with module/import/axiom
  coverage, consuming checks and reconciled article evidence.

The plan specifies `ActionSupport.lean`, `FunctionAction.lean`, `FunctionSupport.lean`,
`PredicateSupport.lean` and `SupportedFunction.lean` under `Package/Foundations/`.
F05a uses general group/action machinery; F05b uses it with delivered F04;
F05c adds persistent supported values. A function-space action itself may use
DivisionMonoid; cancellation/evaluation use Group. No global alternate action
on bare arrows or Prop is proposed. Full curry works on arbitrary acted carriers;
bundled curry needs supported sections, supplied in particular by supported
parameters or nominality of the parameter carrier. Other carriers need not be
nominal. Ordinary inputs and generic function support must never be confused
with pointwise support of bare arrows.

Context-derived sufficient bounds, including user-provided values/bounds, are
an explicit intended consumer of the section/composition laws. No least-support
computation is required. An elaborator must still prove capture support and
operation compatibility; context inspection itself is later function tooling.
Full predicate logic, Some/Any and surjective-equivariant predicate pullback/
quotient descent remain PKG-01. Binder descent remains F06. No syntax, tactics,
macros, generators, category instances or case-study migration belongs to F05.
Accept the reusable interfaces and all stated phase criteria, not merely one
compiling wrapper probe. Public spellings and the seven-task execution sequence
are recorded in the plan for review.

### PKG-F06 — Binding, representatives and descent

- [ ] Specify and prove name abstraction with equality, support and fresh
  representatives, or an equivalent carrier-level binding facility with the
  same explicitly stated obligations.
- [ ] Provide concretion/reconstruction or the corresponding chosen-fresh
  representative interface; expose its freshness premises and computation laws.
- [ ] Establish the supported binder-descent principle needed by iteration:
  representative independence, scoped handler compatibility, existence,
  uniqueness and support/parameter bounds where claimed.
- [ ] Specify whether binder-output conditions quantify over all values,
  individually supported results, or certified reachable child/result pairs.
  Preserve the exact premise needed for the chosen representative-independence
  proof; the [Urban study](research/2026-10-07-urban-nominal-techniques.md)
  gives an elementwise-result precedent, not a preselected FCB implementation.
- [ ] Test nested binders, a binder over a product, fixed nominal parameters
  and let's scope over the body alone. Retain the constant-atom counterexample
  to unconditional supported abstraction mapping.

Accept a facility available through `Package/` and a consuming binder handler
that descends to the quotient with useful equations. Existing `NameAbs`,
concretion and FCB are optional implementations or references; their names and
proof organization are not required. A direct raw-alpha/descent construction is
also eligible, provided it proves the same needed obligations. This task must
precede PKG-03; syntax generation cannot simply assume a valid binder lift.

## Package task contracts

### PKG-00 — Architectural investigation

- [x] Inspect the research starting branch, history, working tree and completed
  lambda proofs.
- [x] Compare Pitts, Copello, Rocq, original Nominal, Nominal2 and then-current
  Lean predicate/induction principles, recording source and verification limits.
- [x] Compare generic syntax, per-declaration generation and a staged hybrid.
- [x] Propose grammar, generated guarantees, proof escape hatches and diagnostics.
- [x] Run bounded positive/negative Lean probes and inspect representative axioms.
- [x] Record the five studies, dependency order and article outline.

The [research artifacts](#research-artifacts) deliver this historical proposal.
Its completed status does not approve its architecture, make legacy dependencies
mandatory, or complete any of F01–F06. The later architectural-freedom decision
requires those explicit foundation contracts before implementation.

### PKG-01 — Predicate foundations

**DONE — complete specification, Tasks 1–8 and independent review; uncommitted.**
The [new specification](superpowers/specs/2026-10-07-package-predicate-foundations-design.md)
is grounded in delivered F05, pinned Mathlib and the
[current-source/probe record](research/2026-10-07-pkg01-predicate-foundations.md).
The author selected the direct proof-field predicate record on 2026-10-08,
with explicit supported-map and supported-subset views. The comparison with
the viable SupportedMap wrapper remains evidence for that decision; the old
direct-SPred proposal was not treated as prior approval.

- [x] Inspect current F02–F05 source/delivery and pinned Mathlib; compare all four
  storage candidates and their concrete ordinary-use behavior.
- [x] Check bounded representation/logical, pullback/descent and cofinite probes,
  including negative boundaries and representative axiom dependencies.
- [x] Write exact contracts, hypothesis/action/universe policy, phase acceptance,
  remaining obligations, research notes and matching mathematical LaTeX.
- [x] Author selects named fresh quantifier plus opt-in scoped `И` notation.
- [x] Author selects choice 1, the direct predicate record, on 2026-10-08.
- [x] Author approves the written specification and full phase scope on 2026-10-08.
- [x] Prepare the [implementation plan](superpowers/plans/2026-10-08-package-predicate-foundations.md), with eight tasks and a complete acceptance mapping.
- [x] Author approves the implementation plan and selects native execution on 2026-10-08, with one numbered task per fresh context.
- [x] **Task 1 / partial 01a:** ordinary logical support, joint/restricted quantification
  and uniformly supported action-free families, publicly exported and verified.
  Evidence: `/tmp/nominal-package-pkg01-execution.WReW3a/`; see the latest work log.
- [x] **Task 2 / partial 01a:** direct supported predicates, Iff extensionality,
  proof independence, canonical action/nominality, sufficient/least-support
  correspondence with map/object/subset views, and Mathlib-transferred Boolean
  algebra. Public consumer, signatures, audit and article checks pass; see the
  Task 2 work log and `/tmp/nominal-package-pkg01-execution.WReW3a/`.
- [x] **Task 3 / completes 01a:** bundled logical computation/support/action laws,
  F05 precomposition and individually certified sections, whole-carrier/restricted
  quantification and supported collection union/intersection. Public consumers,
  support loss, exact signatures, audit and article checks pass; see the Task 3
  work log and `/tmp/nominal-package-pkg01-execution.WReW3a/`.
- [x] **Phase 01a complete, uncommitted:** Tasks 1–3 acceptance criteria pass
  together. Ordinary uniform quantification is in Task 1; no unrestricted
  CompleteLattice on supported predicates. The whole-change review is recorded with Task 8.
- [x] **Task 4 / ordinary 01b:** scalar and DivisionMonoid pullback adapters;
  ordinary sufficient/least-support reflection and Mathlib-backed action-free
  predicate descent; canonical action laws and all positive/negative consumers.
- [x] **Task 5 / supported 01b:** supported pullback, explicit SubMulAction
  restriction and nominality, quotient equivalence, computation, both inverses
  and action directions, exact support, individual-context freshness and logic.
- [x] **Phase 01b complete, uncommitted:** both task criteria pass together,
  including unsupported descent/induction, unrelated-action rejection and the
  duplicate-label/enlarged-bound consumer. See the separate delivery records.
- [x] **Task 6 / ordinary 01c:** cofinite quantification and scoped notation,
  supplied/enlarged-bound Some/Any, finite/cofinite classification, decision
  laws, joint support and all three uniform-support interchanges.
- [x] **Task 7 / completes 01c:** individual contexts and avoidance, bundled fresh
  projection, predicate-object freshness and proved negative boundaries.
- [x] **Phase 01c complete, uncommitted:** both task criteria and combined
  acceptance checks pass. See the separate Task 6 and Task 7 delivery records.
  The independent whole-change review also passes in Task 8.
- [x] Integrate the complete positive/negative matrix: fixed atoms, nonminimal
  bounds, empty/non-nominal carriers, unsupported ordinary descent/motives,
  non-surjectivity, alpha incompatibility, infinite/coinfinite predicates,
  unsupported singleton unions, quantifier interchange and fresh-selector limits.
- [x] Verify all phases through the Package public boundary, import coverage and
  axiom audit; reconcile README/article and compile the manuscript.
- [x] **Task 8 complete:** exact public signatures, all nine consumers and eight
  README Lean blocks, complete specification mapping, expanded representative
  audit, preservation and one fresh independent whole-change review. No material
  findings; the minor current-status inconsistency is corrected. See the final record.

Dependencies: delivered 01a and 01b use F04/F05; supported 01b additionally
uses the phase 01a carrier and logic. Ordinary 01c uses PredicateLogic and
Mathlib's filter theory without depending on the supported carrier; its bundled
endpoints use 01a. All three phases, final integration, full specification
coverage and independent review satisfy the PKG-01 completion criterion. F06 is not a prerequisite for generic predicate descent
or Some/Any. Research probes alone never complete a production checkbox.

At this stage such consumers can use general quotient descent/equality or
ordinary induction. Generating fresh term/rule induction belongs to later tasks;
PKG-01 does not need to copy the reference lambda development to test this boundary.

Accept the reviewed API, consuming examples and intended negative examples under
the new package target/audit. Correspondence specifically with old `NFun` is
optional. The previous fixed-atom `letI` probe is evidence about the legacy
representation, not a mandatory new implementation. Do not introduce syntax
commands or migrate the manual case study in this task.

### PKG-02 — Carrier construction and mathematical contract

- [ ] Review the normalized atom/data/recursive/product/single-binder grammar
  against F01 and the selected foundation universe/action policy.
- [ ] Construct an actual carrier, with proved alpha equality or its certified
  equivalent, canonical action and quotient well-definedness where applicable.
- [ ] Prove constructor equations/inversion, exact support and fresh
  representatives; identify dependencies on F06 if the backend uses them here.
- [ ] Test lambda, let's mixed scope, a binder over a product and an empty
  datatype. Reject unproved scope, positivity and recursive-container cases.
- [ ] Compare concrete proof/transport costs before selecting a universal
  carrier or committing to per-declaration generation.

The [Urban study](research/2026-10-07-urban-nominal-techniques.md) adds a
restricted abstraction-function subset as comparison evidence. It does not
require that backend: compare the actual constructor/action/support/induction
contracts with a quotient construction. A bare bijection or an unrestricted
function-valued syntax field does not establish them. Preserve Lean's empty
datatype test independently of HOL's inhabited-type policy.

Accept a manual certificate for actual constructors, not merely an interpreted
arity or an arbitrary type equivalence. If initiality is claimed, specify and
prove the structure map, map class, commuting equations and uniqueness. The
old lambda carrier is reference evidence; its representation need not be reused.

### PKG-03 — Fresh induction and supported iteration

- [ ] Prove arbitrary-motive induction with context-generalized recursive
  hypotheses, including avoidance enlarged under nested binders.
- [ ] Assess the elementwise avoidance parent from Urban's Theorem 2:
  a context-selection function may return a supported value for each context
  without itself being supported or equivariant. Keep the motive arbitrary.
  See the [Urban investigation](research/2026-10-07-urban-nominal-techniques.md).
- [ ] Use the proved F06 facility to establish supported iteration, including
  scoped binder compatibility, totality and uniqueness.
- [ ] Assess individually supported outputs in an arbitrary acted-on result
  carrier before imposing a carrier-wide nominality hypothesis. Keep any
  stronger convenience interface as a derived specialization.
- [ ] Export guarded computation, support bounds, parameter/renaming laws and
  independence from a chosen support bound wherever the contract claims them.
- [ ] Demonstrate reconstruction and capture-avoiding substitution with the
  mathematical strength of the lambda reference, without stronger assumptions.

Accept proofs and public consumers for nested binders, shadowing and fixed
nominal parameters. Iteration supplies recursive results; original-child access
and dependent data-valued elimination are separate contracts. Binder descent
must apply to the actual scope, including only let's body. Compatibility with
old iterator names or implementation lemmas is not required.

### PKG-04 — Categories, mutual recursion and finite contexts

- [ ] Extend the certified construction to multiple categories and direct
  finite mutual recursion, with an explicit positivity/universe contract.
- [ ] Prove mutual alpha/action/support/induction laws on a genuinely cyclic
  example; retain every category's recursive hypotheses.
- [ ] Supply the focused finite-context representation needed by FOL, whether
  a proved List interface, another finite structure or a generated category.
- [ ] Reject unproved recursive-container extensions with precise diagnostics.

Accept mutual consumers and context substitution/support equations. An acyclic
Term/Formula pair does not verify mutual recursion. Finite products and nested
single binders are proposed initial shapes; recursive List/Option/Array/Finset
fields need separate proofs. Legacy container instances are optional evidence.

### PKG-05 — Datatype and function commands

- [ ] Generate the proved datatype contracts with predictable public
  declarations under the package's chosen representation.
- [ ] Generate supported definitions with ordinary application, useful
  computation equations and the selected proof-backed support interface.
- [ ] Check captures by elaborated expression/local identity; use registries
  of checked theorems while preserving action instances and binding scopes.
- [ ] Separate candidate-bound discovery from certification: combine relevant
  local captures with user-provided values/bounds, then prove the support
  equation. Prefer sufficient bounds; no least-support inference is required.
- [ ] Prove a distinct primitive recursor and a consumer using both original
  children and recursive results, with its advertised support/uniqueness laws.
- [ ] Expose unsolved support, binder-descent, coverage and termination
obligations. Failed commands must not leave a partial public package.

Use the [Urban investigation](research/2026-10-07-urban-nominal-techniques.md)
to distinguish support proof, binder-output/descent proof and discharge of the
user-facing freshness guard. Primitive recursion must establish support of
reachable outputs as well as totality/uniqueness. Reject bound-name and exposed
body selectors for alpha-compatibility reasons, separately from missing support
certificates. Graph transport permutes handlers jointly; fixed supported
handlers do not imply unconditional equivariance.

Accept generated substitution, higher-order use, `rw`/`simp`/`ext`, shadowing,
nested scopes and meaningful failure diagnostics. Arbitrary globals must not
silently acquire equivariance certificates. Split recursor and elaborator work
into separate increments as needed. Do not advertise iteration as primitive
recursion or promise unrestricted dependent elimination. The old `nfun` macro
and `NFun` packaging are not required parts of the command implementation.

### PKG-06 — Judgment contracts and generation

Urban's structural induction theorem is not a fresh-rule theorem. Retain the
separate criterion below; the [source study](research/2026-10-07-urban-nominal-techniques.md)
maps its historical warning without treating it as a proof of our later rules.

- [ ] Establish a sufficient fresh-rule criterion: per-rule transport or a
  proved semantic refreshability theorem preserving the intended relation.
- [ ] Specify positive rules, side-condition certificates, multiple categories
  and the scope of bound names/eigenvariables.
- [ ] Retain every recursive derivation and its context-generalized IH.
- [ ] Prove fresh inversion and then generate the certified interfaces through
  the package's datatype/function boundary.
- [ ] Validate unrestricted beta/parallel rules and FOL universal-introduction/
  existential-elimination rules. Reject a nominated binder free in the conclusion.

Accept substantive derivation-induction/inversion consumers with arbitrary
motives. Relation equivariance alone is insufficient: renaming must transport
all affected premises and preserve the whole conclusion, and IHs must cover
transformed premises. If fresh premises are added, prove equivalence with the
original judgment. Review the mathematical criterion separately from commands;
an existing manual rule-induction proof is useful evidence, not required code.

### PKG-07 — First complete workflow

- [ ] Generate lambda syntax, substitution and beta/parallel judgments.
- [ ] Replay simultaneous parallel substitution, diamond, closure
  correspondence, beta confluence, Church–Rosser and normal-form uniqueness
  for arbitrary open contextual terms.
- [ ] Generate FOL terms/formulas, substitution, finite contexts and natural
  deduction, using a specified treatment of eigenvariables.
- [ ] Prove `Γ ⊢ φ → substContext x s Γ ⊢ substFormula x s φ`, with genuine
  eigenvariable refreshing and no hidden closedness assumption.
- [ ] Demonstrate nested avoidance, capture-forcing substitution, arbitrary
  motives, primitive recursion, useful rewriting and meaningful diagnostics.
- [ ] Review statements independently, build/audit all new public modules and
  generated clients, and check preservation of the original development.

Acceptance requires proofs through the generated public interfaces. Transporting
the old Church–Rosser theorem alone is not a replay. An independently proved new
development suffices; a constructor-commuting equivariant equivalence with old
`Term`, and comparison of substitutions/relations, are optional validation.
Syntax-only generation or formula substitution composition alone is insufficient.
FOL consumers must exercise nonempty contexts, quantifier renaming, universal
introduction and existential elimination consuming both recursive premises.
No termination or existence-of-normal-forms theorem is required.

### PKG-08 — Lambda with let

- [ ] Specify contextual reduction for lambda with nonrecursive let.
- [ ] Prove expansion alpha-compatible and compatible with substitution.
- [ ] Prove each let-language step maps to beta-star reduction in the generated
  base lambda calculus.
- [ ] Include open terms, shadowing and a binder free in the defining term,
  confirming that its scope covers only the body.

Accept generated-interface proofs of the specified simulation theorem. The
small mixed-scope checks in F06/PKG-02 are prerequisites, not this full study.

### PKG-09 — π-calculus

- [ ] Select the transition convention, language fragment and representation
  of residual binding before implementing the semantics.
- [ ] Prove transition equivariance and fresh bound-residual inversion.
- [ ] Demonstrate substantive scope extrusion with the name binding jointly
  in a label and continuation where the selected semantics requires it.
- [ ] Specify and prove one behavioral congruence theorem.

Accept the agreed statements with any required relational or coinductive
infrastructure proved separately. Behavioral theory is not an automatic
consequence of nominal datatype generation. No transition convention is selected
by this roadmap revision.

### PKG-10 — μ-calculus

- [ ] Select the precise calculus, positivity criterion, interpretation and
  semantic environment contract before implementation.
- [ ] Prove the selected substitution and alpha-invariance results.
- [ ] Establish monotonicity and the chosen fixed-point/unfolding laws, with
  each semantic hypothesis explicit.
- [ ] Test valuation transport without assigning unsupported nominal
  certificates to arbitrary semantic valuations.

Accept the selected semantics and proved results. Positive modal μ-calculus is
a proposal; its selection and exact theorem remain open. Fixed-point semantics
requires additional mathematical work beyond binding and syntax generation.

### PKG-11 — Research writing

- [x] Propose a sustainable notes/manuscript organization and article outline.
- [x] Start the LaTeX manuscript alongside F02/F03a, with actual declarations
  and mathematical exposition; preserve that slice's verification in this tracker.
- [ ] Maintain a per-layer decision record, including discarded reuse/rebuild
  choices, counterexamples and their effect on dependencies.
- [ ] Create and maintain the statement-to-Lean claim ledger as increments land,
  distinguishing legacy evidence from new `Package` results.
- [ ] For every implementation increment, assign the relevant LaTeX sections
  in its spec/plan and develop their statements and mathematical explanations
  together with the Lean proofs; do not accumulate writing for a final phase.
- [ ] Before closing each increment, synchronize theorem hypotheses, source
  references and substantive limitations, review both artifacts and compile
  the article. Record commands/results and review evidence here, outside the manuscript.
- [x] Separate publication content from development records and adopt a selective
  research outline; explain insights and grounded comparisons without task IDs,
  delivery stories, review verdicts or build/audit logs in the manuscript.
- [ ] Preserve exact source versions, failed approaches and verification limits;
  review consistency among claims, contracts and implementation at each milestone.

Follow the [article plan](research/2026-10-05-article-plan.md). Neither the old
proposal nor this rewritten plan establishes novelty, publication readiness or
successful external builds.

The article remains entirely in LaTeX under `docs/article/`, written alongside
implementation. The [manuscript](article/main.tex) covers permutation/action and
finite- and least-support mathematics with selected declaration correspondence.
Predicate and binder results require their later proofs. The publication-content
clarification supersedes earlier evidence-section instructions as well as the
Markdown-first suggestion. Mathematical content and relevant implementation
correspondence advance together, without turning task boundaries into article
structure or requiring every implementation detail to appear in print.

## Validation of future implementation

Each delivered increment must identify its public declarations, their exact
theorem statements and the consumers that exercise them. Validate adopted
dependencies at the same boundary as newly proved foundations. Positive examples
must use generated facts in meaningful conclusions; negative tests must check
the intended unsupported case or diagnostic.

Review the Mathlib inventory and any reason for custom infrastructure before
closing the increment. Confirm that reused results meet the actual hypotheses
and action conventions, and that new general-purpose code does not duplicate
a suitable existing API without a documented need.

PKG-F02 must establish actual new-target commands before they are reported as
passing. The intended coverage includes the package library, future case-study
examples when delivered, generated declarations and a module-based axiom audit. Do not assume
that `lake build`, `lake build Nominal Instances Examples`, or the current audit
automatically discovers `Package/`. Run the configured package commands and
document their import closure, in addition to the preserved baseline checks
when integration changes affect those targets.

Compile affected modules while iterating, then their supported dependents.
Inspect representative public results with `#print axioms` and audit the new
module closure, allowing standard `propext`, `Classical.choice` and `Quot.sound`
but no admissions, custom axioms or disabled kernel checks. Report whether
builds were cached, rebuilt project artifacts with cached dependencies, or a
clean dependency bootstrap. Retain theorem-strength, coherence, scope and
negative-case review alongside compilation. Do not change pinned versions or
add CI as a routine part of validation.

When an increment changes the mathematics, interface or verification account,
update its LaTeX exposition in that same increment. Check the mathematical
statements and their correspondence to the Lean declarations, then compile from
`docs/article/` with the documented `latexmk` command, writing generated files
outside the source tree. A PDF build alone does not check mathematical accuracy;
Lean compilation alone does not establish that the prose describes the theorem.

Documentation-only updates require link/content and whitespace checks, not a
Lean rebuild. A successful document check is never package proof evidence.

## Open decisions and next step

1. F02 + F03a passed independent final review and is committed at `3d2196a`.
   The [native plan](superpowers/plans/2026-10-05-package-foundation-kernel.md)
   records completion and the author's removal of standalone Package examples.
2. F03b is delivered and committed at `34a8335`. F04a is implemented under its
   [approved specification](superpowers/specs/2026-10-05-package-finite-support-design.md)
   and [native plan](superpowers/plans/2026-10-05-package-finite-support.md),
   with a clean independent final review. The
   [F04b specification](superpowers/specs/2026-10-06-package-least-support-design.md)
   and [native implementation plan](superpowers/plans/2026-10-06-package-least-support.md)
   are approved. F04b is delivered with passing code, consumers, audit, article
   and independent final review. F04a/F04b are committed at `68956dd`.
   F04c's [written specification](superpowers/specs/2026-10-06-package-canonical-freshness-design.md)
   is approved; its [native implementation plan](superpowers/plans/2026-10-06-package-canonical-freshness.md)
   was also approved. F04c implementation, integrated checks and final review
   are complete and committed, including general freshness, at `9c1cb9a`.
   F04d's [specification](superpowers/specs/2026-10-06-package-equivariant-quotients-design.md)
   is approved, including its stronger characterization. Its
   [native plan](superpowers/plans/2026-10-06-package-equivariant-quotients.md)
   was approved before production changes. F04d code, consumers, audit and
   article and independent final review pass. F04d and the reconciled parent
   PKG-F04 are DONE, with F04d committed at `32f3dba`. F05's hybrid and three phases are now approved. Its
   [implementation plan](superpowers/plans/2026-10-07-package-function-space.md)
   was approved for native execution. Code, consumers, audit and article pass;
   the independent final review passed without findings. PKG-F05 is DONE and
   committed at `3c9d8dc`. PKG-01's written specification is approved and its
   implementation plan is approved for native execution in fresh contexts.
   Tasks 1–8, all phases, final integration, complete specification coverage and
   independent whole-change review pass. PKG-01 is DONE, uncommitted. The run
   stops here; later PKG tasks require a separate request.
   The [approved F03b specification](superpowers/specs/2026-10-05-package-controlled-swaps-design.md)
   and [native plan](superpowers/plans/2026-10-05-package-controlled-swaps.md)
   supply its bounded contract. The swap criterion supplies permutation input;
   it does not implement support or prove least support.
3. Settle syntax/backend, direct-mutual, finite-context and binder-descent choices
   at their own tasks. Later π/μ semantics remain separate decisions.

The actual F04a inspection began with a clean tree at `34a8335`. Earlier logs
retain the working-tree status at their own inspections. F04c's inspection
began with a clean tree at `68956dd`, containing committed F04a/F04b delivery.
Persistent usage examples belong to future case studies. The current
Package audit covers production declarations directly; the reference examples
remain unchanged. The author selected the direct SupportedPred representation
after its comparison with delivered SupportedMap.
The F05 hybrid is preserved. The author has approved the
[PKG-01 specification](superpowers/specs/2026-10-07-package-predicate-foundations-design.md),
including direct storage, scoped `И` notation and the full 01a/01b/01c scope.
The [implementation plan](superpowers/plans/2026-10-08-package-predicate-foundations.md)
is also approved. Task 8 and the independent final review are complete; this
run stops here. Earlier task checkpoints and handoffs are retained as history,
and all delivery remains uncommitted.

## Research artifacts

- [Approved PKG-01 predicate-foundations specification](superpowers/specs/2026-10-07-package-predicate-foundations-design.md).
- [Approved PKG-01 native implementation plan](superpowers/plans/2026-10-08-package-predicate-foundations.md).
- [PKG-01 current-source/Mathlib inventory, representation comparison and checked probes](research/2026-10-07-pkg01-predicate-foundations.md).
- [Approved F05 written specification](superpowers/specs/2026-10-07-package-function-space-design.md).
- [Approved F05 native implementation plan](superpowers/plans/2026-10-07-package-function-space.md).
- [F05 current-source, Mathlib, Pitts and interface investigation](research/2026-10-07-function-space-foundations.md).
- [Urban's nominal techniques: broader carrier, induction, recursion and automation investigation](research/2026-10-07-urban-nominal-techniques.md).

- [Discrete permutation sets, representation comparison and Mathlib reuse](research/2026-10-05-discrete-representation.md).
- [Current readiness and exact proposed predicate contracts](research/2026-10-05-pkg01-readiness.md).
- [Direct pinned algebraic-source investigation](research/2026-10-05-algebraic-source-investigation.md).
- [Independent and comparative predicate design probes](research/2026-10-05-predicate-design-probes.md).
- [First bounded foundation written specification](superpowers/specs/2026-10-05-package-foundation-kernel-design.md).
- [F02 + F03a implementation plan](superpowers/plans/2026-10-05-package-foundation-kernel.md).
- [Approved F03b controlled-swap specification](superpowers/specs/2026-10-05-package-controlled-swaps-design.md).
- [Completed F03b native implementation plan](superpowers/plans/2026-10-05-package-controlled-swaps.md).
- [Approved F04a finite-support specification](superpowers/specs/2026-10-05-package-finite-support-design.md).
- [Approved F04a native implementation plan](superpowers/plans/2026-10-05-package-finite-support.md).
- [Approved F04b nominality/least-support specification](superpowers/specs/2026-10-06-package-least-support-design.md).
- [Approved F04b native implementation plan](superpowers/plans/2026-10-06-package-least-support.md).
- [Approved F04c canonical-instances/freshness specification](superpowers/specs/2026-10-06-package-canonical-freshness-design.md).
- [Approved F04c native implementation plan](superpowers/plans/2026-10-06-package-canonical-freshness.md).
- [Approved F04d canonical-equivariant-quotient specification](superpowers/specs/2026-10-06-package-equivariant-quotients-design.md).
- [Approved F04d native implementation plan](superpowers/plans/2026-10-06-package-equivariant-quotients.md).
- [LaTeX manuscript](article/main.tex).
- [Current research policy and reading guide](research/README.md).
- [Requirements and author decisions](research/2026-10-05-nominal-package-brief.md).
- [Architecture and alternatives](research/2026-10-05-package-architecture.md).
- [Predicates, quotient descent and induction](research/2026-10-05-predicate-foundations.md).
- [Isabelle and rule-induction source comparison](research/2026-10-05-isabelle-comparison.md).
- [Backend grammar, feasibility and counterexamples](research/2026-10-05-backend-comparison.md).
- [Proposed user syntax and generated contracts](research/2026-10-05-package-contracts.md).
- [Article outline and evidence workflow](research/2026-10-05-article-plan.md).

## Work log and verification evidence

### 2026-10-05 — PKG-00 research proposal (historical)

The architectural investigation delivered the linked notes and five standalone
probes, initially as uncommitted research artifacts outside supported imports.
They were subsequently recorded in `7fed53a2e5fc67379f86f085515e310e7c1fddb7`.
The original investigation left library sources and dependencies unchanged.

Evidence from that investigation, not rerun for this roadmap revision:

- `lake build Nominal Instances Examples` passed, 1,033 jobs using existing caches.
- Direct tutorial compilation passed; direct axiom audit checked 1,859 project
  declarations with only `propext`, `Classical.choice` and `Quot.sound`.
- The five probes then present passed investigator/coordinator checks:
  `BackendCounterexamples.lean`, `BackendPositivity.lean`, `BackendStaging.lean`,
  `PredicateFoundations.lean` and `PredicateInstanceProbe.lean`, all under
  `docs/research/probes/`. They included guarded expected failures and standard
  positive-result axioms. This statement does not cover later probes by wildcard.
- Import coverage reached the then-existing 37 library and 15 example modules.
- Source versions and external verification limits are recorded in the notes.
  No external Isabelle/Rocq/Agda build or clean dependency bootstrap was performed.
- Cross-review clarified rule certificates, scoped let FCB, binder-renaming
  freshness premises, fixed-atom truth-action selection and Some/Any support.

These checks validate the historical baseline/probes. They establish neither a
new `Package` target nor its foundations, generated declarations or audit coverage.

### 2026-10-05 — Separate package roadmap (historical)

At the author's request, the preceding edit created this standalone roadmap,
retained PKG-00–PKG-11, and removed only the package-phase banner/appendix added
to the previous roadmap during the investigation. Navigation was updated in
the research brief, architecture proposal, article plan and README.

That documentation-only edit recorded passing checks of 12 Markdown files and
144 local links, clean whitespace/fences and `git diff --check`. It recorded
that the previous roadmap matched its preserved pre-investigation snapshot
byte-for-byte and that production/configuration hashes were unchanged. These
are the earlier edit's checks, not fresh verification counts for this rewrite.
No Lean build was rerun for that edit.

### 2026-10-05 — Foundation-first roadmap revision

The author clarified that the whole required foundation may be rebuilt and that
new implementation belongs under top-level `Package/`, outside `Nominal/`.
Rewrote the full roadmap around that policy, introducing stable PKG-F01–F06,
revising all later dependency/acceptance contracts and keeping PKG-00–PKG-11.
Existing function, abstraction, binder-lift and lambda APIs are optional reference
or adoption choices. Added explicit package import/example/audit coverage and
separated it from the historical baseline evidence.

This revision is documentation only and does not implement any proposed task.
The two later untracked probes `PredicateInterface.lean` and
`PredicateSomeAny.lean` are preserved; this entry makes no new validation claim
about them. This revision passed checks of its 15 local links/anchors, all 18
task sections and dashboard rows, whitespace/fence balance, and
`git diff --check -- docs/nominal-package-roadmap.md`. No Lean build or package
axiom audit was run for this documentation edit.

The coordinating review then checked all 12 revised/new research and roadmap
Markdown files: 141 local file links, 14 anchors, balanced fences and clean
whitespace, together with `git diff --check`. All 18 task IDs have matching
dashboard and contract entries. A 90-file baseline hash comparison found changes
only to the nine existing research Markdown notes and this roadmap; all other
80 hashes, including every Lean probe and the reference source/configuration,
were unchanged. The review also removed a premature requirement to settle later
π/μ semantics before initial command work.

### 2026-10-05 — Explicit algebraic investigation in PKG-F01

At the author's request, revised PKG-F01 to require direct inspection of both
pinned sketch modules, checking the earlier assessment, evaluating useful ideas
and recording declaration-level dispositions before foundation selection.
Updated the PKG-01 handoff and architecture summary to make this requirement
explicit in a fresh context. PKG-F01 remains TODO; this documentation edit does
not claim that its expanded investigation or design acceptance is complete.
Confirmed that both pinned files are available in local Git; no branch build,
new theorem check, code change, checkout or merge was performed.
Documentation validation passed: 143 local file links, 16 anchors, balanced
fences, whitespace and `git diff --check`. Only the roadmap, architecture summary
and PKG-01 handoff changed in this turn; the other 89 baseline file hashes,
including all code and probes, were preserved.

### 2026-10-05 — PKG-F01 source investigation and first written specification

Inspected the actual checkout before editing: `fasapa/nominal-package`, HEAD
`76966b1f2e44f594517442b6572e33abaa9038e0`, one documentation commit beyond the
handoff's last inspected HEAD. The tracked tree was clean. Preserved the three
existing untracked files: `pkg-01-start-prompt.md`, `PredicateInterface.lean`
and `PredicateSomeAny.lean` in their existing research locations.

Read both required algebraic modules directly at
`983adeb9b80f75fb7c77c05acfd2fcef16db1d46`, plus relevant pinned dependencies.
Delivered the declaration-level investigation with dispositions for signatures,
functor maps, morphisms, predicate lifting, induction, iteration, initiality and
abstraction descent. Confirmed the earlier distinction between false contracts,
weak statements, missing proofs and elaboration obstacles. A new proved negative
example shows why a fixed supported predicate cannot compute unchanged at every
abstraction representative. Useful arity/morphism and scoped-descent ideas are
retained without adopting the sketch. Untouched historical copies fail at their
obsolete imports under current Lean 4.34.1; the original Lean/Mathlib 4.28.0
development was not built or repaired.

The readiness assessment finds F02–F05 undischargeable by current Package
evidence: no target, action/support boundary or Package consumers exist.
Recommended direct `SPred A X` plus logical/map support certificates, ordinary
Prop application, and no required truth-action instance or general NFun library.
Recorded exact proposed logical, quotient, support and Some/Any contracts,
including independent universes and support for fixed parameters. A new
Mathlib-only probe verifies direct predicate action and support reflection along
an equivariant surjection; it does not establish least support or Some/Any for
arbitrary groups.

The proposed first written specification is F02 plus F03a: Package build/import/
consumer/audit coverage and a small finite-permutation/action kernel over Mathlib.
It explicitly defers support-facing permutation work to F03b and support,
freshness, quotient and predicate proofs to their own increments. F06 remains
later. The new documents were cross-reviewed for mathematical hypotheses,
action coherence, universe policy and bounded scope. Review clarified that
parameter support is a sufficient condition for the general section theorem,
made infinitude explicit beside least-support laws, and required the future
import checker to handle or explicitly reject supported import-header forms.

Verification actually performed:

- All seven existing probes passed direct `lake env lean` checks unchanged:
  BackendCounterexamples, BackendPositivity, BackendStaging,
  PredicateFoundations, PredicateInstanceProbe, PredicateInterface and
  PredicateSomeAny. Expected compiler failures remain guarded.
- Three new predicate scratch probes and the new abstraction-predicate
  counterexample passed, with standard-only representative printed axioms.
  Their exact Lean source is retained in the new notes. The coordinator
  extracted all four blocks into `/tmp/nominal-pkg01-note-validation/` and
  independently ran `lake env lean` on PackagePredicateGroup.lean,
  PackagePredicateDirect.lean, PackagePredicateQuantifierFailures.lean and
  AlgebraicSourceProbe.lean; all exited 0 without warnings. Source hashes of
  the three predicate blocks match their original compiled scratch files.
- `python3 scripts/check-imports.py` passed for 37 reference library modules
  and 15 example modules. It remains a reference-only check.
- Checked 16 Markdown files, 191 local file links, 16 anchors, balanced fences,
  whitespace and all 18 matching dashboard/task IDs. Removed a stale navigation
  link to the architecture prompt deleted in the current HEAD.
- `git diff --check` passed. Explicit new-file whitespace/content checks cover
  the four untracked research/spec documents as well.
- A SHA-256 comparison of all 91 original files found exactly the five intended
  research/tracker Markdown edits; the other 86 files are byte-identical,
  including reference code/configuration, all original probes, the untracked
  handoff and the historical roadmap. Four new Markdown artifacts were added.

These are direct scratch checks against built imports and pinned dependencies,
not a full library rebuild, fresh project-artifact build, clean dependency
bootstrap or Package audit. No production Package paths, Lake changes, external
proof-system builds, commits, merges, pushes or CI changes were made.

PKG-F01 remains IN PROGRESS pending author review of the written foundation
specification and layer choices. PKG-F02–F05 and PKG-01 remain TODO. Written-spec
approval is the next gate; only then prepare and review an implementation plan.
No implementation plan or production execution is approved by these artifacts.

### 2026-10-05 — F02 + F03a approval, implementation plan and LaTeX article

The author approved the F02 + F03a written specification. Recorded that approval
without extending it to production execution or the later support/predicate
interfaces. The required F01 boundary for this increment is accepted; F01's
broader per-layer choices remain proposed. Prepared the written implementation
plan as three sequential tasks: finite permutations with a public consumer,
canonical actions with counterexamples, and independent coverage/axiom auditing.
The plan awaits review and execution-method selection. No production Package
files or Lake changes were made.

During planning, the author requested an article under `docs/article/`, entirely
in LaTeX, written alongside implementation, and explicitly permitted delegation.
Created `main.tex`, `sections/introduction.tex` and `sections/foundations.tex`.
The draft gives finite-moved subgroup and swap proofs, action/equivariance
contracts and the three action distinctions. It labels these as manuscript
arguments and prospective implementation contracts, not checked Package results.
Each implementation task now owns the corresponding article update. The new
format supersedes the earlier Markdown-first manuscript recommendation.

Source-based planning checked pinned Mathlib action/coercion/swap interfaces and
Lean/Lake validation behavior. In particular, canonical atom action can reuse
subgroup restriction; equivariance names its atom carrier explicitly; named
consumer theorems survive into the audit whereas anonymous `example` proofs do
not. The proposed import checker uses Lean's actual dependency JSON parser and
checks per-file errors, rather than duplicating Lean syntax with a narrow regex.
The coordinator ran `lake env lean --deps-json` on `Nominal.lean`,
`Examples/AxiomAudit.lean` and Mathlib's `Algebra/Group/Action/Defs.lean` to confirm
the output shape. This was import-header inspection, not proof elaboration.

Verification for this planning/article turn:

- Self-reviewed the implementation plan against every approved spec section,
  public interface, consumer, negative case and verification boundary.
- Independently reviewed the manuscript mathematics; a separate source reviewer
  also found no actionable issue. No novelty or new Lean proof claim was made.
- From `docs/article`, ran
  `latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir=/tmp/nominal-package-article-build main.tex`.
  The article writer's compilation produced an eight-page PDF; the coordinator's
  repeat invocation confirmed it up to date. The final log has no warnings,
  unresolved references or over/underfull boxes. Checked 19 unique labels,
  five resolved references, all inputs, extracted text and rendered pages 3/8.
  Generated files remain outside the repository, under `/tmp`.
- Checked 17 Markdown files, 203 local links and 16 anchors, plus fences and
  whitespace. `git diff --check` passed; new-file checks include the plan and
  all three LaTeX sources.
- Against the 95-file planning-turn snapshot, 87 existing files are byte-identical
  and eight existing Markdown files contain only authorized status, format or
  navigation updates. Added the plan and three LaTeX sources. Preserved all
  reference code/configuration, original probes, untracked handoff and the
  historical roadmap. HEAD remains `76966b1f2e44f594517442b6572e33abaa9038e0`.

No Lean build or axiom audit was rerun for these documentation changes, and no
new Package verification is claimed. No commit, branch switch, merge, dependency
change, push, publication or CI change occurred. Next: review the implementation
plan and choose native execution with final independent review or subagent-driven
execution with task review gates. The approved specification and LaTeX format
do not need another approval.

### 2026-10-05 — Native F02 + F03a delivery and example-scope correction

The author approved the implementation plan and chose native execution. The
coordinator implemented the new Package sources and validation; a subagent
updated only the LaTeX manuscript, and a fresh independent reviewer inspected
the whole increment. Work stayed on `fasapa/nominal-package` at the same HEAD,
without commits, branch changes, dependency upgrades or CI changes.

Delivered the finite-moved subgroup, ordinary permutation application and
extensionality, group/moved-set/swaps equations, canonical atom/product/finite-set
actions, explicit `Discrete A X`, and `Equivariant A f` with identity,
composition, projections and pairing. The only new action instance is for the
discrete wrapper; canonical actions use Mathlib. No infinitude assumption is
introduced into the group/action interface. F03b's support-facing permutation
laws and all support/predicate/binder layers remain separate.

**Author correction during execution:** standalone Package examples are not
needed; persistent usage examples are reserved for future case studies. Removed
the newly created `Package/Examples.lean` and `Package/Examples/` source layer.
Preserved the reference `Examples/` byte-for-byte. Temporary public-import proofs
remain only under `/tmp/nominal-f02-f03a-execution/`, as scratch evidence. Updated
the approved spec/plan, import checker, audit and article to production/audit
coverage with no consumer root or consumer-count requirement. This changes the
validation layout, not the foundational theorem statements.

The public import is `Package.lean`; its two modules live in
`Package/Foundations/`. The only Lake configuration change adds the Package
library, retaining the existing defaults. `Package/Tests/AxiomAudit.lean` checks
production declarations by module origin and rejects zero coverage/unapproved
axioms. Its internal rejection checks use simulated names and `run_cmd`, with
no introduced axioms or linter suppression. `Package/Scripts/check-imports.py`
uses pinned Lean's dependency JSON parser and checks every file result, including
errors reported with process exit zero. Its disposable fixtures check missing,
orphan, out-of-scope and forbidden imports, production-to-audit edges, actual
header syntax, JSON failures and the boundary between header parsing and full
Lean compilation. Usage and actual commands are documented in Package/README.md.

Verification actually performed:

- Observed the initial public-import check fail with missing Package, then pass
  after the permutation implementation. The action check similarly failed at
  absent action/Discrete/equivariance interfaces before those were implemented.
  The external-data action rejection was observed and then guarded explicitly.
- `lake build Package +Package.Tests.AxiomAudit` passed, 821 jobs using cached
  dependencies and rebuilding changed Package modules. Direct
  `lake env lean Package/Tests/AxiomAudit.lean` checked **77 production
  declarations from two defining modules**, with only `propext`,
  `Classical.choice` and `Quot.sound`. The root adds imports, not declarations.
- `python3 Package/Scripts/check-imports.py --self-test` passed **13 tests**.
  The real checker reached **three production source modules and one audit
  module**, with the audit reaching the complete four-module source inventory.
- The two temporary files ActionContracts.lean and NegativeContracts.lean under
  `/tmp/nominal-f02-f03a-execution/` passed direct Lean checks against the final
  public root. They exercise finite/empty atoms, independent universes, ordinary
  rewriting/extensionality, six action-coherence cases, equivariant composition,
  finite-set transport, the three action distinctions and a missing-action
  diagnostic. These are not persistent case studies or public declarations.
- `lake build Nominal Instances Examples` passed, 1,033 jobs with cached
  artifacts. Direct reference axiom audit passed for **1,859 declarations**;
  its import checker still reaches **37 library and 15 example modules**.
- The LaTeX manuscript describes actual declarations and verification limits.
  Compilation produced a **ten-page PDF** with no final warnings, unresolved
  references or box diagnostics. The article worker compiled into
  `/tmp/nominal-package-article-build/`; the coordinator confirmed that build
  up to date, and the independent reviewer also performed a fresh manuscript
  compilation into `/tmp/nominal-foundation-final-review-article/`.
- The independent reviewer found **no Critical, Important or Minor issues**,
  and independently passed the Package build/audit, temporary contract checks,
  all checker tests, coverage and fresh article compilation. No fix pass or
  deferred minor finding remained.
- Documentation checks covered **18 Markdown files, 206 local links and 16
  anchors**, all 18 task IDs, fences and whitespace. `git diff --check` and
  explicit new-file checks passed. Admission scans were inspected in context:
  the audit's simulated `sorryAx`/unapproved names are not axiom declarations.
- A hash comparison against the 99-file execution-start snapshot found **87
  files unchanged**. The 12 changed existing files are the intended package
  documentation/status records, three article sources and Lake registration.
  All reference code, dependency pins, original probes, untracked handoff,
  existing scripts and the historical roadmap are preserved. Six new Package
  source/documentation/tool files were added, with no standalone examples layer.

This is verified, uncommitted working-tree delivery. There was no clean Lean
dependency bootstrap or fresh complete Lean project build; the independent fresh
build was of the LaTeX article. F02 is DONE. F03a is delivered, while PKG-F03
remains IN PROGRESS for F03b. PKG-F04/F05/F06 and PKG-01 remain TODO. The next
bounded design decision concerns the support-facing permutation contract; no
support, predicate or binder implementation is approved by completing this slice.

### 2026-10-05 — F03b next step and concurrent article completion rule

After the author confirmed F02/F03a delivery, inspected the current Package
source and recorded the next bounded F03b contract: swap generation with
endpoints controlled by the original moved set, its avoidance corollary, and
an action-level consumer. Split the F03 checklist to distinguish the delivered
group/swaps from the remaining support-facing laws. F03b remains proposed and
unimplemented; F04 support theory and F05/PKG-01 remain later work.

Reaffirmed the author's requirement that the LaTeX article be written together
with package development. Every substantive increment now explicitly owns its
article section and cannot be marked complete with that exposition left for a
later phase. Specifications/plans assign both artifacts; delivery checks their
mathematical correspondence and compiles the updated manuscript. Updated R13,
the article plan, research guide, architecture/readiness summaries and handoff.
Corrected the stale claim that the delivered article's implementation references
were still prospective; only later layers remain prospective.

A read-only independent review found no mathematical or scope issue in the
F03b contract or writing rule, including finite atom carriers, temporary usage
checks and the separation from F04. Documentation checks passed for seven
changed Markdown files, 119 local links and nine anchors, balanced fences,
whitespace and `git diff --check`. A 105-file baseline comparison preserved
all other 98 hashes, including all Lean, LaTeX, configuration and probe files.
No Lean or manuscript build was run for this documentation-only clarification;
the previous implementation/build reports above remain their original evidence.

### 2026-10-05 — Mathlib-first policy

The author requested that development always look for and use suitable Mathlib
infrastructure. Added this policy to every increment's design/completion criteria,
the research guide, R14 in the brief, the architecture decision register and the
fresh-context handoff. F01 now requires a Mathlib inventory for new foundation
choices; F03b explicitly checks available factorization/induction results before
developing its controlled-swap proof. Record concrete gaps when new code is needed.
The policy preserves freedom from old nominal APIs while preferring appropriate
existing Mathlib facilities. No existing theorem, implementation, dependency pin,
task completion status or manuscript source was changed by this documentation edit.

Validation: the five edited documents passed 83 local-link and ten anchor checks,
fence/whitespace checks and `git diff --check`. Lean/configuration/probe and
historical-roadmap hashes were preserved. Concurrent edits to two LaTeX sections
and the article plan were observed and left untouched. No Lean or LaTeX build
was needed or run for this policy-only change.


### 2026-10-05 — Discrete representation research and mathematical correspondence

The author requested comparison of `def Discrete` with the existing one-field
structure, explicit mathematical counterparts for definitions/structures in the
article, and reuse of suitable existing Mathlib concepts. Recorded the discrete
`Perm(A)`-set Δ_A(X), with identity action, as the mathematical object; the
wrapper is a representation of that construction, not additional mathematics.
Located Pitts 2013 Examples 1.5 (printed p.15) and 2.5 (p.30), and checked pinned
Lean/Mathlib sources and the official Lean reference.

The research record `research/2026-10-05-discrete-representation.md` compares
structure, ordinary def and abbrev, with complete reproducible scratch sources.
Regular def separates ordinary instance search and permits direct value/function/
container reuse. It does not automatically transfer all instances, and mere type
ascription does not reliably change the inferred action on an existing expression.
Named tagging functions or typed binders resolve the tested cases. The structure
keeps that passage explicit. Abbrev plus a global trivial-action instance changes
bare atom actions and still loses to the group self-action in a tested case.
Recommendation: retain the current structure for this interface, while keeping
regular def as a legitimate alternative rather than calling it mathematically
incorrect or intrinsically incoherent.

Mathlib already supplies the action construction through `MulAction.ofEndHom 1`.
A separate probe proves the resulting action record equal by `rfl` to the
current Package instance, retaining application/projection equations. This is
a concrete reuse recommendation, not a production edit in this research task.
The bundled `CategoryTheory.Action.trivial` and its concrete-action conversion
also exist, but are unnecessary here. `CategoryTheory.Discrete` represents a
discrete category, a different mathematical concept; its structure is relevant
encoding precedent, not a drop-in nominal carrier. No matching general-purpose
unbundled carrier tag was found in the searched pinned Mathlib source.

Updated the LaTeX introduction and discrete-data section with mathematical
meaning, the one-field rationale, alternatives, checked elaboration caveats,
Mathlib candidates and the recommendation. The article policy now explicitly
requires mathematical correspondence and a Mathlib search before new machinery.
A read-only cross-review found only an overstrong wording about a carrier being
necessary; corrected it to describe the chosen interface. Production code,
original probes, dependencies and F02/F03a theorem statements are unchanged.

Validation:

- Independently compiled DefAction.lean, StructureAction.lean and AbbrevAction.lean
  under `/tmp/nominal-discrete-actions-20261005/`, plus
  `/tmp/DiscreteUsabilityProbe.lean` and `/tmp/DiscreteMathlibReuse.lean`.
  All five exited 0 without warnings; printed theorem dependencies are only
  standard axioms or empty. Successful guarded failures retain their intended
  interpretation. These are scratch checks using built imports, not a new
  Package implementation or F04 support theory.
- Verified that the five complete Lean blocks in the research note and their
  SHA-256 hashes match the compiled scratch sources. No persistent Package
  examples were added.
- Recompiled `docs/article/main.tex` with the established latexmk command into
  `/tmp/nominal-package-article-build/`. The updated PDF is 13 pages; final log
  has no warnings, unresolved references or over/underfull boxes. Extracted
  text and rendered pages 8–9 were inspected.
- Checked the four edited/new research/tracker Markdown documents: 85 local
  links, nine anchors, balanced fences, whitespace and `git diff --check`;
  explicit new-file checking covers the research note. Verified all 69 existing
  Lean/configuration/script/historical-roadmap hashes against the start snapshot.
- Concurrent policy/handoff documentation updates were observed and preserved;
  the preservation report does not attribute those independent edits to this
  investigation. No production code, original probe or dependency pin changed,
  and no full Lean rebuild, commit, merge or publication occurred.

F03b remains a separate next increment. No representation replacement or
production action-constructor refactor was made by this investigation.


### 2026-10-05 — Retain the explicit discrete-action record

At the author's instruction to implement the representation investigation's
findings, briefly replaced the discrete action record with the checked
`MulAction.ofEndHom 1` alternative. The combined Package/reference build passed
(1,049 jobs with cached dependencies); direct Package auditing reported only
standard axioms. The author then preferred the original definition because it
states the action more clearly. Restored `Package/Foundations/Action.lean`
byte-for-byte to its pre-refactor contents:

```lean
instance : MulAction (Perm A) (Discrete A X) where
  smul _ d := d
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
```

The LaTeX article now explains this directly: the permutation is ignored, the
value stays unchanged, and both action laws compute to the same value. The
more abstract Mathlib constructor remains verified research evidence rather
than the selected production encoding. The structure, public API and theorem
strength are unchanged, and the choice adds no new general group-action theory.

Validation of the restored source: `lake build Package +Package.Tests.AxiomAudit`
and direct `lake env lean Package/Tests/AxiomAudit.lean` passed, with 77 production
declarations and only the three allowed standard axioms. The manuscript rebuilt
without warnings or layout/reference diagnostics; `git diff --check` passed.
The production action file exactly matches its saved pre-refactor bytes. No
commits, dependency changes, new persistent examples or other production edits
were made.

### 2026-10-05 — F03b specification prepared for review

Started the selected F03b increment by rechecking branch, status, relevant history,
current Package sources, prior approvals and article. Initial HEAD was
`76966b1f2e44f594517442b6572e33abaa9038e0` on `fasapa/nominal-package`. During
review it advanced externally to `3d2196a57b8964084dd58a65a0cb1c0be50b1592`,
committing the preceding implementation/research/article work. Source contents
were preserved; this design session made no commit, push or branch change.

The [new specification](superpowers/specs/2026-10-05-package-controlled-swaps-design.md)
proposes controlled endpoint-pair list factorization, arbitrary-set avoidance,
the selected-action consequence and its converse. Products apply the rightmost
swap first. It retains decidable equality for swaps and introduces no atom
infinitude, ambient finiteness, nominality or finite-avoidance-set hypothesis.
It assigns the corresponding LaTeX propositions, mathematical proof explanation,
source correspondence and manuscript compilation to the same implementation
increment. F03b remains unimplemented and awaits written-spec agreement, then
a reviewed implementation plan and execution agreement. F04/F05/PKG-01 remain
later work, and PKG-11 remains ongoing.

Two read-only investigations compared proof routes and article obligations.
Pinned Mathlib at `d13f23b723b8a846827a245b89c10fc7d3f11612` supplies
`mem_closure_isSwap` for a restricted set of swap generators. The recommended
adapter restricts endpoints to the original moved set and uses
`Subgroup.closure_induction_left` to extract an ordered list. Finite-subtype
induction is an alternative; a new moved-set cardinality induction would repeat
an argument already in Mathlib. Unrestricted generation alone is not accepted
as endpoint-control evidence.

Commands actually run during design:

- `lake build Package +Package.Tests.AxiomAudit` passed: 821 jobs with cached
  artifacts and replayed audit output.
- Direct `lake env lean Package/Tests/AxiomAudit.lean` passed: 77 production
  declarations from two defining modules; only `propext`, `Classical.choice`
  and `Quot.sound`.
- `python3 Package/Scripts/check-imports.py` passed: three production source
  modules and one audit module.
- `lake env lean /tmp/nominal-f03b-design-_hmdmsu4/MathlibBoundary.lean` passed
  without diagnostics after removing an unnecessary probe section variable.
  The original version, which passed with unused-variable warnings, is retained
  beside it. The probe checks the ambient fixed-point-complement bridge, exact
  Mathlib signatures and atom/group/function action coherence after the proposed
  imports. It does not prove F03b factorization or its action consequence.

This is baseline verification and design evidence, not a fresh project build,
dependency bootstrap or new mathematical delivery. No Package, article, reference
source, dependency, configuration, checker or persistent example was changed.
No article compilation was needed for this specification-only step; manuscript
development and compilation remain explicit F03b implementation obligations.

Specification self-review and an independent read-only review found no
mathematical or scope issue. The review's one documentation finding was the
externally advanced HEAD; the specification and current tracker now distinguish
the initial snapshot from the committed baseline. Documentation checks passed
for five changed/new Markdown files, 98 local links and their anchors, fences
and whitespace; `git diff --check` passed. A 106-file content snapshot confirmed
102 files unchanged, with only the four intended existing documentation files
modified and the new F03b specification added. The specification awaits author
agreement; no implementation plan has yet been prepared.

### 2026-10-05 — F03b specification approved; implementation plan prepared

The author approved the F03b written specification. Recorded that approval
without extending it to production edits. The
[implementation plan](superpowers/plans/2026-10-05-package-controlled-swaps.md)
is now prepared for review and execution-method agreement, at unchanged HEAD
`3d2196a57b8964084dd58a65a0cb1c0be50b1592` on `fasapa/nominal-package`.

Its three tasks deliver controlled/avoiding factorization, selected-action
consequences, and final audit/article/documentation evidence. Tasks 1 and 2
include concurrent LaTeX development and compilation; Task 3 reconciles exact
statements, proof explanations and measured verification evidence. The plan
retains all four approved signatures, arbitrary `Set A`, independent universes,
the original moved-set endpoint bound and the rightmost-first convention.

A read-only planning investigation identified reuse of the existing temporary
F03a action/coherence checks, plus concrete new checks for empty/singleton atom
carriers, empty controlled identity lists, noncommuting `Fin 3` factors and a
nonidentity swap avoiding the infinite set `({0,1} : Set ℕ)ᶜ`. These are planned
acceptance assertions, not newly implemented proofs. The coordinator self-reviewed
the plan against the approved spec, including its article obligations and all
five Review Focus cases.

Native execution is recommended with root-owned Lean/tests, exclusive article
ownership for a parallel worker and one fresh final reviewer. This recommendation
is not execution approval. No production, article, reference, dependency or
configuration content was changed during planning; no new Lean build, axiom
audit, checker self-test or LaTeX compilation was needed or claimed. F03b remains
unimplemented, and F04/F05/PKG-01 remain later work.

Planning validation passed for six changed/new Markdown files: 107 local links,
seven anchors, balanced fences and whitespace. All four plan signatures match
the approved specification exactly after whitespace normalization;
`git diff --check` passed. A 107-file planning snapshot confirmed 102 existing
files unchanged; only the five intended existing design/documentation files
were edited, with the new implementation plan added. The plan and approval
records remain uncommitted.

### 2026-10-05 — Native F03b delivery: controlled swaps and action criterion

The author approved the implementation plan by selecting native execution.
Root implemented the Lean proofs and temporary consumers; an article worker
owned the three LaTeX sources during development. Work remained on
`fasapa/nominal-package` at `3d2196a57b8964084dd58a65a0cb1c0be50b1592`.
The increment is verified, uncommitted working-tree work; no commit, push,
merge, branch switch, dependency upgrade or CI change was performed.

Delivered exact public declarations:

- `Perm.swap_factorization` in `Package/Foundations/SwapFactorization.lean`:
  an endpoint-pair list with product π and distinct endpoints in the original
  `π.moved`. The rightmost swap acts first.
- `Perm.swap_factorization_avoiding`: the same existential product guarantee
  with endpoints outside arbitrary `S : Set A` when π fixes S pointwise.
- `Perm.smul_eq_of_swap_smul_eq` and
  `Perm.forall_smul_eq_iff_swap_smul_eq` in `Package/Foundations/Action.lean`:
  the selected-action implication and converse, with independent atom/carrier
  universes and no nominality assumption.

The proof specializes pinned Mathlib's `mem_closure_isSwap` to generators whose
endpoints lie in the original moved set. Identity/swap orbit witnesses establish
closure membership; `Subgroup.closure_induction_left` extracts the list. The
local predicate tracks ambient product equality using `toEquiv_mul` at each
cons, then `Subtype.ext`; this implements the planned product transport without
a separate `map_list_prod` rewrite. No statement was weakened, no action instance
was added, and no countability, infinitude, ambient finiteness or finite-avoidance
hypothesis was introduced.

Verification actually performed:

- Observed the factorization consumers fail at the missing factorization names
  before implementation, then pass; likewise observed the action consumers fail
  at the two missing action names before implementing them. Temporary fixture
  corrections and failing versions are retained under
  `/tmp/nominal-f03b-execution/`, including the finite-pair lemma-name correction
  and explicit complement simplification. These were elaboration issues, not
  counterexamples or weakened mathematical contracts.
- Iterative `lake build Package` calls rebuilt the changed Package modules
  using cached dependencies. The final
  `lake build Package +Package.Tests.AxiomAudit` passed **967 jobs**, rebuilding
  the audit while reusing those modules. The independent review reran it cached.
- Direct `lake env lean Package/Tests/AxiomAudit.lean` passed: **81 production
  declarations from three defining modules**, with only `propext`,
  `Classical.choice`, and `Quot.sound`. All four new declarations are printed
  explicitly, and the module-origin traversal retains whole-production coverage.
- `python3 Package/Scripts/check-imports.py` passed: **four production source
  modules and one audit module**. The checker is unchanged; its historical
  self-test evidence is not reported as a new run.
- Direct Lean checks passed for the new `FactorizationContracts.lean` and
  `ActionContracts.lean` under `/tmp/nominal-f03b-execution/`, and the retained
  F03a `ActionContracts.lean` and `NegativeContracts.lean` under
  `/tmp/nominal-f02-f03a-execution/`. All import only Package. New consumers
  cover the original endpoint bound, identity/empty/singleton carriers,
  finite nonidentity swaps, noncommuting three-point composition order,
  the infinite avoidance set `({0,1} : Set ℕ)ᶜ`, arbitrary-set action invariance,
  both equivalence directions, independent-universe products, empty/universal
  sets, and a distinct-endpoint-only premise. The previous action-coherence
  and expected missing-action checks remain passing.
- `PublicSignatures.lean` directly checked all four signatures with universes
  printed. Only the approved decidable equality and selected action assumptions
  occur. No persistent examples or new harness entered Package.
- The article contains `sec:controlled-swaps`,
  `prop:controlled-factorization`, `prop:avoidance-factorization`, and
  `prop:swap-invariance`, with the actual proof route, exact hypotheses,
  original-set control, strict decrease explanation and declaration references.
  Its introduction, abstract and `sec:evidence` match the delivered scope.
- From `docs/article/`,
  `latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir=/tmp/nominal-package-article-build main.tex`
  passed, producing **17 pages**. Root checked correspondence, confirmed/rebuilt
  the final manuscript and inspected extracted text and the final log. The fresh
  reviewer independently compiled into `/tmp/nominal-f03b-final-review-article/`.
  Both final logs had no warnings, unresolved references or layout diagnostics.
- Independent final review found **no Critical, Important or Minor issues** and
  no declined-to-judge items. It independently reran the Package build, direct
  audit, new/retained consumers, signature check, import checker, whitespace/hash/
  linked-path checks and fresh manuscript compilation. No fix pass was needed.

These are checked source elaborations and builds with cached Lean dependencies,
plus a fresh manuscript build; no fresh full Lean project build or dependency
bootstrap is claimed. The reference source, historical roadmap, original probes,
base permutation module, checker, shared configuration and dependency pins are
unchanged. No shared integration change required a separate reference rebuild.

Final documentation checks passed for seven Markdown files, 109 local links and
seven anchors, balanced fences and tracked/untracked whitespace;
`git diff --check` passed. The 108-file execution snapshot confirms 95 original
files unchanged, with only the 13 intended implementation/article/documentation
files edited and one new Lean module added.

**F03b and PKG-F03 are DONE.** PKG-11 remains ongoing across later increments;
F04 support/freshness, F05 interfaces and PKG-01 remain TODO. Moved points are
not identified with support of an arbitrary action element, and no support,
least-support or freshness implementation is supplied by this delivery.

### 2026-10-05 — F04 phase split and F04a specification prepared

The author selected F04 with separate F04a–F04d review/delivery boundaries.
Inspection confirmed `fasapa/nominal-package` at
`34a83358739ab962e2b9d2035a21d67b2a896071`, initially clean. F03b and its
article/specification/plan are committed at that revision. The earlier logs'
uncommitted-state descriptions retain their historical meaning.

Recorded the four slices under the existing PKG-F04 ID, with dependency order
`F04a → F04b → F04c/F04d`, article destinations and per-slice acceptance
obligations. F04a's written specification proposes one Support module, a finite-set
abbreviation of Mathlib `MulAction.Supports`, `FinitelySupported A x`, basic and
equivariant-image/product bounds, conjugation transport, the delivered F03b
swap characterization and binary finite intersection under `Infinite A`.
The two-atom intersection counterexample is an explicit temporary-consumer
requirement. No new function/predicate interface, least support or freshness is
included in F04a. F04d remains independent of F04c once F04b is available.

Inspected pinned Mathlib support, fixing-subgroup/conjugation, finite-set,
product-action and swap infrastructure. `MulAction.Supports.smul` has commuting-
action assumptions, so the proposed proof transports support by conjugation.
The existing subgroup-conjugation theorem is also recorded; its broader import
cost is unnecessary for the small elementwise argument. `Finset.exists_notMem`
supplies the spare atom for intersection. `Quotient.map`, `Quotient.map_mk`
and `Function.Surjective.mulAction` were inspected for the later quotient
boundary, without bringing that implementation into F04a.

Baseline commands actually run:

- `lake build Package +Package.Tests.AxiomAudit`: passed, 967 jobs, cached
  project/dependency artifacts with replayed audit output.
- `lake env lean Package/Tests/AxiomAudit.lean`: passed directly, 81 production
  declarations from three defining modules; only standard `propext`,
  `Classical.choice`, `Quot.sound`.
- `python3 Package/Scripts/check-imports.py`: passed, four production source
  modules and one audit module. No checker change or self-test rerun.
- From `docs/article/`,
  `latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir=/tmp/nominal-package-article-build main.tex`:
  passed; manuscript outputs already up to date. The existing final log contains
  no warning, unresolved-reference or box diagnostics. No fresh PDF build claimed.
- `git diff --check` and temporary Markdown checks: passed for local links,
  anchors, balanced fences and tracked/untracked whitespace. A SHA-256 comparison
  against the initial 109-file snapshot confirms only the four intended existing
  documentation files changed; 105 original files, including all Lean/LaTeX
  sources, reference code, historical roadmap and dependency pins, are unchanged.
  One new written specification was added. Scratch evidence is under
  `/tmp/nominal-f04a-design-4xg5f700/`.

Self-review and two independent read-only design reviews found no actionable
issues. The proof routes and signatures are source-reviewed proposals; no new
Lean declaration or temporary implementation was written or compiler-checked.
These baseline checks are not F04a proof evidence. No reference rebuild, fresh
Lean project build or dependency bootstrap was needed or claimed.

**F04a awaits agreement on its written specification.** The next authorized
stage after that agreement is preparing its implementation plan, followed by
separate plan/execution agreement. Its assigned `sec:finite-support` article
section must be written alongside the eventual code, reconciled and compiled
before delivery; that obligation is not marked complete. PKG-F04 is IN PROGRESS
for design only, F04b–F04d remain TODO, and prior F02/F03 approvals stand.
All changes remain uncommitted; no branch switch, push, merge, publication,
dependency change or CI work was performed.

### 2026-10-05 — F04a specification approved; implementation plan prepared

The author approved the concrete written F04a specification. Its public
statements, assumptions, Mathlib specialization, proof strategies and concurrent
article contract are accepted; specification approval is not requested again.
The implementation plan is now prepared for review and execution agreement.

Planning rechecked `fasapa/nominal-package` at
`34a83358739ab962e2b9d2035a21d67b2a896071`. The preceding four modified
documentation files and untracked F04a specification were preserved. No
production change had intervened. The plan assigns four sequential tasks:
basic finite bounds and supported elements; transport and swaps; finite
intersection with its Bool boundary; and full public acceptance/audit/article
delivery. All 18 approved declarations have an owning task and meaningful
temporary consumers. Tasks 1–3 draft their own LaTeX mathematics; Task 4
reconciles the checked correspondence and verification evidence.

Native execution is recommended because the mathematical tasks extend one
module in dependency order, followed by a fresh independent whole-increment
review. Subagent-driven execution remains an alternative with a review after
each task. Neither method has been selected for F04a yet. No implementation
skill, production edit, new Lean probe, commit or branch operation was performed.

Planning verification consists of spec/plan self-review, a declaration-name
inventory restricted to Lean interface blocks, local Markdown-link/anchor and
fence/whitespace checks, `git diff --check`, and SHA-256 preservation comparison
against the 110 existing tracked/untracked files at planning start. The
preservation snapshot is under `/tmp/nominal-f04a-plan-q0pdiv6f/`. Only the five
intended existing design/tracker documents changed, and one implementation plan
was added. All Lean/LaTeX sources, reference files, historical roadmap, dependency
pins and existing implementation plans remain unchanged.

No Lean build, audit, import-checker invocation or LaTeX build was needed or
rerun for these documentation-only changes. The preceding design-session
baseline results retain their original cache conditions; they are not a new
planning verification run or proof of F04a. Implementation checkboxes remain open,
PKG-F04 remains IN PROGRESS, and F04b–F04d remain TODO. The next gate is approval
of the concrete implementation plan and execution method.

### 2026-10-05 — Native F04a implementation and integrated validation

The author approved the specification, then selected native execution of the
written plan. Work remained in the requested checkout on `fasapa/nominal-package`
at `34a83358739ab962e2b9d2035a21d67b2a896071`, preserving the earlier uncommitted
design documents. Root implemented the Lean module and temporary consumers; one
article worker owned the four LaTeX files while drafting, with root reconciling
the mathematics against each checked task.

`Package/Foundations/Support.lean` exports the two definitions and sixteen
theorems from the approved specification. `Supports` abbreviates Mathlib's
two-carrier predicate; `FinitelySupported A x` is an elementwise existential
property. Basic/image/product laws use the selected actions. Transport is proved
by conjugation, without commuting-action assumptions. The swap characterization
specializes F03b directly. Finite intersection uses `Infinite A` only for a spare
atom, with the triple-swap identity derived from the existing `Perm.conj_swap`.
There is no new action instance, support selector, least-support operator,
nominality class, freshness, quotient or supported-function/predicate interface.

Verification actually run:

- The execution baseline `lake build Package +Package.Tests.AxiomAudit` passed
  967 jobs using cached artifacts. Before each mathematical task, its temporary
  consumers failed at the intended missing Package declarations. Failing versions
  and logs are retained under `/tmp/nominal-f04a-execution/`.
- Iterative `lake build +Package.Foundations.Support Package` calls rebuilt
  Support and the public root with cached dependencies, passing 968 jobs.
  The final `lake build Package +Package.Tests.AxiomAudit` passed 969 jobs,
  first rebuilding the extended audit; the final combined run reused artifacts.
- Direct `lake env lean` checks passed for `BasicContracts.lean`,
  `TransportSwapContracts.lean`, `IntersectionContracts.lean`,
  `PublicSignatures.lean` and `ActionCoherence.lean` in the scratch directory.
  They use only `import Package` and consume the actual support conclusions.
  Cases include independent universes, empty/singleton atoms, nested products,
  equivariant images with strictly smaller sufficient bounds, noncommuting
  three-atom transport, Bool/equal-endpoint swap criteria, overlapping/disjoint
  supports and the proved two-atom failure of unconditional intersection.
- Public signatures check all 18 contracts with no extra assumptions. In
  particular, existential transport/product closure has no public equality
  instance, and infinitude occurs only on intersection.
- Direct `lake env lean Package/Tests/AxiomAudit.lean` passed: **104 production
  declarations in four defining modules**, including private/generated names,
  with only `propext`, `Classical.choice`, `Quot.sound`. Representative new
  declarations are printed explicitly; the intersection and Bool counterexample
  also have standard-axiom prints in their temporary consumer.
- `python3 Package/Scripts/check-imports.py` passed: **five production source
  modules including the root, one audit module**. The checker is unchanged;
  its self-tests were not rerun.
- The retained F03a `ActionContracts.lean` and `NegativeContracts.lean` under
  `/tmp/nominal-f02-f03a-execution/` both passed unchanged, preserving earlier
  action distinctions and the expected missing-action diagnostic.
- Root compiled the article from `docs/article/` with
  `latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir=/tmp/nominal-package-article-build main.tex`.
  The reconciled manuscript has **26 pages**; the final log has no warnings,
  unresolved references or layout diagnostics. Root checked the mathematical
  correspondence and extracted support-section text. The new section is
  `sec:finite-support`, with separate current evidence at `sec:support-evidence`;
  the F03b evidence remains explicitly historical.

No theorem was weakened or hypothesis added. Small elaboration corrections were
confined to explicit finite-product types, a constant-map consumer's intermediate
binding, and `Ne.symm` instead of field notation on negated equality. The article
initially failed on Unicode in a verbatim excerpt; equivalent ASCII `Exists`
and local paragraph reflow resolved that failure and the layout diagnostics.
These are recorded build iterations, not mathematical design changes.

The active validation uses rebuilt project modules with cached dependencies;
it is not a fresh project build or dependency bootstrap. No shared configuration
or reference source changed, so no separate reference rebuild was needed.
Final preservation/document checks passed: seven Markdown files, 125 local links,
ten anchors and all changed-file whitespace. The execution snapshot confirms
**99 of 111 original files unchanged**, with exactly twelve intended edits and
two new production/article files. Reference source, historical roadmap, checker,
shared configuration and dependency pins are preserved.

Independent final review found **no Critical, Important or Minor issues**. It
independently ran the cached 969-job Package build, direct Support source
elaboration, all five consumers, direct audit, import checker and documentation/
preservation checks. A fresh manuscript build in
`/tmp/nominal-f04a-final-review/article/` produced 26 pages with a clean log;
the reviewer also inspected extracted text and mathematical correspondence.
Review logs are under `/tmp/nominal-f04a-final-review/`. No fix pass was needed.
The review correctly leaves F04b–F04d and later APIs outside this contract;
it checks preservation of unchanged reference code without claiming a reference
rebuild. Those boundaries match the approved scope and integration policy.

**F04a is DONE. PKG-F04 remains IN PROGRESS**, with F04b–F04d still TODO.
All changes remain uncommitted. No later slice, function/predicate interface,
branch operation, dependency change or CI work is included in this delivery.

### 2026-10-05 — PKG-11 publication content and internal evidence separation

The author clarified that the article is intended as a selective research
publication about the system and its mathematics. It should explain central
definitions, theorems and proof ideas, meaningful architectural choices, limits
and counterexamples, and grounded comparisons with relevant theories and systems.
It should not contain every API detail or routine proof, or invent novelty.
Development-stage/task IDs, work logs, delivery/approval narratives, review
verdicts, commit bookkeeping and audit/build reports belong in this tracker and
research notes, not in the manuscript. Historical records above are retained
as evidence; their earlier manuscript-evidence directions are superseded.

Updated the active PKG-11/article directives, article plan, research brief R7/R13,
research README, architecture AD-08 and reusable handoff. The article outline now
offers selectable research themes with an internal evidence map. Concurrent
LaTeX drafting, mathematical/source correspondence review and compilation remain
required internal work; their outcomes are recorded outside the manuscript.
Routine implementation changes need not enlarge the article. The handoff now
recognizes delivered F04a and points to F04b rather than repeating F03b. Existing
F04a completion and remaining foundation dependencies are unchanged.

Policy-document verification: a temporary checker examined all six edited
Markdown files, 153 local links and 17 local anchors, balanced fences and
whitespace. Scoped `git diff --check` passed. A snapshot comparison confirms
that the pre-existing roadmap work log is preserved byte-for-byte. Check script,
baseline and output are under `/tmp/nominal-article-policy/`. This six-file policy
check ran no Lean build or LaTeX compilation and makes no new theorem-validation
claim; the coordinating manuscript edit owns its separate rendering checks.

The coordinating edit revised the actual LaTeX article: removed operational
evidence/status sections and task identifiers, condensed routine mathematics
and implementation inventories, and retained the central results, hypotheses,
proof ideas and explanatory counterexamples. Added a selective discussion of
supported predicates and induction motives, constructive support witnesses, and
the connection to Nominal2, with primary references in the bibliography. Updated
the six earlier specifications/plans whose article instructions had requested
process reports; their internal execution records remain available.

Ran `latexmk -pdf -interaction=nonstopmode -halt-on-error
-outdir=/tmp/nominal-article-editorial-build main.tex` from `docs/article/`.
The revised article compiles to 12 pages with no warnings, unresolved references
or box diagnostics in the final log. The LaTeX source and extracted PDF text
contain no task/stage identifiers or review/audit/build narrative. These checks
are recorded here and not in the manuscript.

Final checks covered 12 changed Markdown files, 169 local links, 17 anchors,
LaTeX labels/references, fences/whitespace and `git diff --check`. The 113-file
baseline comparison found only 16 existing documentation/article files changed;
all other 97 hashes, including every Lean/configuration/probe file and the
historical roadmap, are preserved. The new `perspectives.tex` is the only added
file. No Lean rebuild was run because no Lean source changed.

### 2026-10-06 — F04b specification prepared for review

Rechecked the actual branch `fasapa/nominal-package`, history and HEAD
`34a83358739ab962e2b9d2035a21d67b2a896071`. Preserved the existing F04a
working-tree implementation/specification/plan and subsequent article-policy
and editorial work, including all untracked files. The initial snapshot covers
114 tracked/untracked files under `/tmp/nominal-f04b-design-yo48zzie/`.
F02/F03a/F03b/F04a approvals and results were not reopened.

The new proposed specification stays within PKG-F04/F04b. It gives exact
proof-only nominality, elementwise least-support and carrier convenience
interfaces, with explicit atom selection and certificate agreement. Existence,
choice, minimality, empty support and image inclusion need infinite atoms but
no public decidable-equality parameter; nominality itself needs neither.
Finite-set transport retains decidable equality and the existing Pointwise
scope. Image bounds are inclusions, and elementwise results impose no global
nominality assumptions. Canonical instances, exact container support formulas,
freshness, quotients and function/predicate interfaces remain later slices.

Inspected the pinned Mathlib revision
`d13f23b723b8a846827a245b89c10fc7d3f11612`. Compared minimum-cardinality
support with finite intersections within a supplied finite bound. The smaller
recommended construction instead uses existing `Finset.wellFoundedLT` and
`exists_minimal_of_wellFoundedLT`: support intersection turns an inclusion-minimal
bound into a least one via `Minimal.le_of_le`. No general order theory or
arbitrary-intersection principle is added. A temporary imports/`#check`/`#synth`
inventory confirmed the exact APIs; it defines no proposed F04b result.

The specification assigns `sec:least-support` in the existing LaTeX support
file, developed alongside the approved Lean work and reconciled before delivery.
It follows the current publication policy: mathematics and useful declaration
correspondence in the article, operational evidence here. Acceptance includes
independent universes, arbitrary finite bounds, both support interfaces and
certificate independence, inverse transport, empty support, possibly strict
image inclusion, supported constants inside a non-nominal pointwise function
carrier, the proved Bool obstruction to least support, and action coherence.

Verification actually run during design, separately from F04a delivery history:

- `lake build Package +Package.Tests.AxiomAudit`: passed, 969 jobs using cached
  project/dependency artifacts; the compiled audit output was replayed.
- `lake env lean Package/Tests/AxiomAudit.lean`: fresh audit traversal passed,
  104 declarations from four defining modules, standard axioms only.
- `python3 Package/Scripts/check-imports.py`: passed, five production source
  modules including the root and one audit module. The checker is unchanged;
  its self-tests were not rerun.
- `lake env lean /tmp/nominal-f04a-execution/IntersectionContracts.lean` and
  `lake env lean /tmp/nominal-f02-f03a-execution/ActionContracts.lean`: passed
  unchanged, retaining the finite-atom boundary and selected-action evidence.
- `lake env lean /tmp/nominal-f04b-design-yo48zzie/MathlibInventory.lean`: passed
  declaration inspection and Finset instance synthesis, with no new proofs.
- From `docs/article/`, ran
  `latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir=/tmp/nominal-package-article-build main.tex`.
  This rebuilt the current edited manuscript in an existing output directory;
  the final PDF has 12 pages and the final log has no warnings, unresolved
  references or box diagnostics. The historical 26-page delivery predates the
  subsequent editorial changes. No article source was changed in this session.

These are baseline checks, not verification of the proposed F04b declarations.
No fresh whole-project build, dependency bootstrap or reference-library rebuild
was run. Specification self-review covers theorem strength, exact arguments,
assumptions, witness independence, scope and article/acceptance obligations.
Final document checks passed for the two edited/added Markdown files: 50 local
links, six anchors, balanced fences and whitespace including the untracked
specification. `git diff --check` passed. The snapshot comparison confirms that
113 of 114 baseline files are unchanged; only this tracker was edited, and the
new specification was added. The historical work-log text is preserved
byte-for-byte. Lean sources, reference sources, existing article/spec/plan files,
historical roadmap, dependency pins and validation tools are unchanged.

**F04b awaits agreement on its written specification.** The next step is its
native implementation plan, requiring separate approval before production
changes. One fresh independent final review is assigned after implementation;
no implementation review has been claimed. PKG-F04 remains IN PROGRESS and
F04c/F04d remain TODO. All work is uncommitted.

### 2026-10-06 — F04b specification approved; native plan prepared

The author approved the concrete written F04b specification. Its mathematical
contract is unchanged: proof-only nominality, individually certified least
support, carrier convenience and agreement, with the reviewed assumption
separation and F04a reuse. Specification approval authorizes planning; the
separate written-plan approval gate remains in force. Native execution with
one fresh independent final review was already selected and is preserved.

Planning rechecked `fasapa/nominal-package` and HEAD
`34a83358739ab962e2b9d2035a21d67b2a896071`, preserving all existing working-tree
and untracked files. The 115-file planning snapshot is under
`/tmp/nominal-f04b-plan-0zdaxrx4/`. Read the approved specification and current
support/root/audit interfaces; inspected pinned Mathlib's finite-set transport
containment laws to make the proof instructions concrete. No architectural
investigation was restarted, and no production or consumer Lean file was written.

The plan has four sequential native tasks: certificate and elementwise leastness;
elementwise transport/empty/image laws; carrier convenience and agreement;
integrated public acceptance, audit, documentation and final review. Each
mathematical task owns its corresponding LaTeX development and compilation.
Six temporary public-import files cover the actual conclusions, finite-atom
leastness failure, supported elements in a non-nominal pointwise function
carrier, proof independence, separate atom selection and action coherence.
All 19 approved declarations are assigned; no later-phase API is added.

Self-review maps every specification requirement and Review Focus item to its
owning task, checks signatures/arguments and step specificity, and preserves
the one final independent review after integrated validation. All implementation
steps remain unchecked. No new Lean build, audit, consumer check or article
compilation is claimed by this planning turn; the preceding design-session
baseline results remain historical evidence. Planning verification is limited
to document content/links/whitespace and preservation against the snapshot.

`python3 /tmp/nominal-f04b-plan-0zdaxrx4/check_plan.py` passed: three documents,
56 local links and six anchors, balanced fences, whitespace and
`git diff --check`. It confirms all 19 planned declaration signatures match
the approved spec, whose Lean blocks are unchanged, and that no execution
step is marked complete. Of 115 baseline files, 113 are unchanged; the F04b
specification's approval/status text and this tracker are the only existing
files edited, and the plan is the only addition. The historical work-log text,
all Lean/article sources, dependency pins, reference source, branch and HEAD
are preserved. These text checks are not Lean elaboration of the new contracts.

**The native implementation plan awaits author approval.** F04b remains
unimplemented and PKG-F04 remains IN PROGRESS; F04c/F04d are TODO. Keep all work
uncommitted and do not ask again for the already recorded specification approval
or native execution choice.

### 2026-10-06 — Native F04b implementation and integrated validation

After reviewing the written plan, the author selected Native and thereby
approved execution. Work remained on `fasapa/nominal-package` at
`34a83358739ab962e2b9d2035a21d67b2a896071`. The execution snapshot preserves
116 pre-existing tracked/untracked files, including all F04a and later editorial
work. Root implemented all tasks directly, followed by one fresh independent
final review with no actionable findings. No commit, branch operation, dependency
change, CI work or later-phase API is included.

The new `Package/Foundations/Nominal.lean` contains all 19 agreed public
declarations. Its proof-only class takes the existing action as a parameter.
The elementwise construction obtains an inclusion-minimal Finset support from
pinned Mathlib and uses delivered `supports_inter` to prove leastness and
uniqueness. Choice and all laws retain the approved assumption boundaries;
only the visible transport equations add decidable equality. Carrier operations
use the nominality projection, agree with any elementwise certificate and make
no new choice. Equivariant-image support is an inclusion. No canonical nominal
instance, freshness, quotient or supported-function/predicate interface is added.

The six temporary public-import files consume actual conclusions: arbitrary
least bounds and independent least candidates; witnesses/certificates; finite
Bool nominality with proved failure of least support; supported constant
functions alongside the unsupported pointwise identity; inverse transport;
empty support; strict image inclusion; multiple explicit atom parameters with
independent universes; all exact public signatures; and preserved actions.
Every mathematical task developed and compiled its LaTeX exposition alongside
the Lean work. The article's new subsection is `sec:least-support`.

Verification actually run:

- The execution baseline `lake build Package +Package.Tests.AxiomAudit`, direct
  audit and import checker passed using existing artifacts: 969 jobs, 104
  declarations from four defining modules, five production sources and one audit.
- Before each mathematical task, its new consumers failed on the intended
  missing declarations. Existing F04a-only boundary proofs already passed.
  Retained red sources/logs and all later checks are under
  `/tmp/nominal-f04b-execution/`.
- Iterative `lake build +Package.Foundations.Nominal Package` calls passed
  969 jobs, rebuilding the changed module/root with cached dependencies.
  ElementwiseContracts, BoundaryContracts, NaturalityContracts and
  CarrierContracts passed as their owning tasks completed.
- Final `lake build Package +Package.Tests.AxiomAudit` passed **970 jobs**.
  `lake env lean Package/Foundations/Nominal.lean` and all six current temporary
  files, including PublicSignatures and ActionCoherence, passed with no diagnostics.
- Direct `lake env lean Package/Tests/AxiomAudit.lean` passed: **132 production
  declarations from five defining modules**, including private/generated names,
  with only `propext`, `Classical.choice` and `Quot.sound`. Representative
  least-support declarations are also printed explicitly.
- `python3 Package/Scripts/check-imports.py` passed: **six production source
  modules including the root, one audit module**. The checker is unchanged;
  its self-tests were not rerun.
- Both retained F03a ActionContracts and NegativeContracts passed unchanged
  under `/tmp/nominal-f02-f03a-execution/`.
- From `docs/article/`, ran
  `latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir=/tmp/nominal-package-article-build main.tex`
  during each mathematical task and integrated validation. The reconciled
  manuscript has **16 pages** and a clean final log. The final invocation reused
  the current output. `pdftotext -layout` extracted the manuscript for a separate
  mathematical correspondence check; output stays outside the source tree.

The fully explicit signature check exposed an inferred binder order for carrier
`support_minimal` differing from the spec. A failing raw-type check was retained;
explicit theorem-local binders restored the approved order, and all consumers
then passed. A few consumer style warnings and one overlong LaTeX paragraph
were corrected locally without disabling diagnostics or changing mathematics.
No theorem was weakened and no assumption added.

The workflow uses a preserved `/tmp` ledger/snapshot instead of commit-based
review helpers, following the approved in-place/no-commit plan. F04b's review
diff is measured against the execution snapshot, so pre-existing F04a changes
are not attributed to this increment. No fresh whole-project Lean build,
dependency bootstrap or rebuild of unchanged reference targets is claimed.

Independent final review found **no actionable Critical, Important or Minor
issues**. It independently ran the cached 970-job build, direct Nominal source
and all six consumers, the direct production audit, import coverage and both
retained F03a checks. It also performed a fresh article compilation in
`/tmp/nominal-f04b-independent-review/`: 16 pages, clean final log, with extracted
least-support text inspected for mathematical correspondence. Review logs are
retained there. No fix pass was needed.

Final documentation and preservation checks passed: seven Markdown files,
146 local links, 13 anchors, 43 LaTeX labels, fences, whitespace including
untracked files, and `git diff --check`. Independent hash comparison confirmed
**103 of 116 baseline files unchanged**, exactly 13 intended existing-file
edits and one new production module. F04a source, reference libraries/examples,
historical roadmap, previous package work log, pins, validation infrastructure,
branch, HEAD and index were preserved. The final status-only edits retain the
validated Lean source hashes.

The review correctly excludes later-phase APIs, canonical instances, freshness,
quotients and function/predicate architecture. Those remain explicit later
contracts and require their own verification. Neither coordinator nor reviewer
claims a dependency bootstrap or rebuild of unchanged reference targets. The
review did not repeat external scholarly comparisons or conduct a page-by-page
visual typography review; LaTeX diagnostics, extracted text and mathematical
correspondence were checked.

**F04b is DONE. PKG-F04 remains IN PROGRESS**, with F04c/F04d still TODO.
All changes remain uncommitted in the requested checkout. No branch integration
or cleanup is requested or performed.

### 2026-10-06 — F04c specification prepared for review

Verified the requested checkout on `fasapa/nominal-package`, HEAD
`68956dd23066c7c5c647345e5598b859ff97a10c`, with a clean initial working tree.
History and the HEAD file inventory confirm that F04a/F04b are committed in
that revision. Corrected the current-state paragraphs above; preserved all
earlier work-log text and its historical uncommitted-delivery descriptions.
Earlier approvals and results are not reopened.

The [proposed F04c specification](superpowers/specs/2026-10-06-package-canonical-freshness-design.md)
defines the bounded interface for review: four certificates of existing
actions, exact canonical support formulas, an elementwise product formula,
`hx.Fresh a` and `Fresh A a x`, sufficient bounds, transport and inverse
transport, fresh swaps, canonical decomposition and finite combined avoidance.
No new notation is proposed. Finset nominality is registered in the existing
Pointwise scope; no action is introduced or replaced. Equality stays out of
atom/discrete nominality, product nominality, atom/discrete support formulas,
generic freshness transport/decomposition and existential avoidance interfaces.

The design gives both inclusions for every exact formula, keeps proof evidence
usable without carrier nominality, retains the Bool boundary and assigns an
unordered-pair consumer using actual least support. Canonical.lean and
Freshness.lean are proposed new modules over the delivered foundations; they
are not implemented. The plan will assign concurrent LaTeX development in
freshness.tex, final correspondence/build checks and one fresh independent
final review. F04d and all later phases remain outside this increment.

Read the current foundation, audits/import policy, requested design/research
inputs and all included manuscript sections. Inspected the pinned Mathlib
support, singleton/image/union, finite avoidance and action APIs at
`d13f23b723b8a846827a245b89c10fc7d3f11612`. An import/`#check`/`#synth` inventory
confirms their types and universe/assumption boundaries; it implements no
proposed F04c declaration. Initial fingerprints for all 117 tracked/untracked
files and design checks are under `/tmp/nominal-f04c-design-n_6qp3g8/`.

Fresh baseline commands actually run in this design session:

- `lake build Package +Package.Tests.AxiomAudit`: passed, 970 jobs using cached
  project/dependency artifacts; compiled audit output was replayed.
- `lake env lean Package/Tests/AxiomAudit.lean`: direct audit passed, 132
  production declarations in five defining modules, with only `propext`,
  `Classical.choice` and `Quot.sound`.
- `python3 Package/Scripts/check-imports.py`: passed, six production source
  modules including the root and one audit module reached. Checker unchanged.
- `lake env lean /tmp/nominal-f04c-design-n_6qp3g8/PinnedAPI.lean`: passed;
  declarations and action synthesis checked without proposed-result proofs.
- `lake env lean /tmp/nominal-f04c-design-n_6qp3g8/UnscopedFinset.lean`:
  expected exit 1, failing only to synthesize the Finset action without Pointwise;
  its scoped counterpart succeeds in the inventory check.
- `lake env lean /tmp/nominal-f04b-execution/BoundaryContracts.lean`: passed;
  retained finite-atom and unsupported-function conclusions remain checked.
- `lake env lean /tmp/nominal-f02-f03a-execution/ActionContracts.lean` and
  `lake env lean /tmp/nominal-f02-f03a-execution/NegativeContracts.lean`: passed.
- From docs/article/, `latexmk -pdf -interaction=nonstopmode -halt-on-error
  -outdir=/tmp/nominal-package-article-build main.tex`: passed with outputs
  already current. The existing 16-page log has no warning, unresolved reference
  or box diagnostic. This invocation did not rebuild the PDF.
- `git diff --check`: passed before documentation edits.

These are baseline checks, not F04c proof or implementation-review evidence.
No fresh whole-project build, dependency bootstrap or reference-library rebuild
is claimed. Production and manuscript sources are unchanged during design.

Document checks passed for both Markdown files: 57 local links, six anchors,
balanced fences, no unresolved specification placeholders and all whitespace,
including the untracked specification. `git diff --check` passed after edits.
Fingerprint comparison preserves 116 of 117 baseline files; only the active
roadmap changed, with this new specification added. The prior work log is
preserved verbatim, along with branch/HEAD, production sources, reference code,
historical roadmap, manuscript and dependency pins. No independent implementation
review has been performed during design.

**F04c awaits agreement on its concrete written specification.** After that,
prepare its native implementation plan and obtain plan approval before production
changes. The execution method and one fresh independent final review after
implementation are already selected; do not ask again. PKG-F04 remains
IN PROGRESS; F04d, F05 and PKG-01 remain later work. Leave the design and tracker
changes uncommitted.

### 2026-10-06 — F04c specification approved; native plan prepared

The author approved the concrete
[F04c specification](superpowers/specs/2026-10-06-package-canonical-freshness-design.md).
Its exact statements, action/instance policy, assumption separation and
freshness/evidence interfaces are unchanged. Native execution with one fresh
independent final review was already selected and is preserved. Specification
approval authorizes the written implementation plan; plan approval remains
required before production changes.

Reinspected `fasapa/nominal-package` at
`68956dd23066c7c5c647345e5598b859ff97a10c`. The only initial changes were the
uncommitted F04c specification and active roadmap. Snapshotted all 118 existing
tracked/untracked files under `/tmp/nominal-f04c-plan-d1f0h4eo/`, preserving
the prior design work and every historical log entry.

The [native implementation plan](superpowers/plans/2026-10-06-package-canonical-freshness.md)
assigns four mathematical tasks: canonical certificates, exact support,
freshness laws, and fresh existence/combined avoidance. A fifth task owns
integrated public-signature/action checks, audit, documentation, final article
reconciliation and the one fresh independent final review. Root owns the
native work; no per-task agent dispatch or additional review sequence is added.
Every mathematical task develops and compiles its LaTeX alongside Lean.

Seven temporary consumers cover all 34 production declarations and the
unordered-pair boundary theorem. The plan's seven Lean interface blocks match
the approved specification byte-for-byte; the specification's Lean blocks
are unchanged. The five review concerns have explicit test owners, including
arbitrary local actions, Pointwise scope, independent universes, supported
elements of non-nominal carriers, strict sufficient bounds, nested contexts,
inverse transport, equal-endpoint swaps and successive fresh choices.

Planning checks cover document consistency, links/anchors, fences, whitespace
including both untracked documents, exact interface-block comparison and file
preservation. `git diff --check` passed. No production or article source was
changed, and no execution step is marked complete. No Lean build, audit or
article compilation was rerun during planning; the prior design-session
verification remains recorded under that session, not as new planning evidence.

**The native implementation plan awaits author approval.** The specification
and native execution method are already approved; do not ask for either again.
F04c remains unimplemented and PKG-F04 remains IN PROGRESS, with F04d and later
phases unchanged. Keep the plan, specification and tracker work uncommitted.

### 2026-10-06 — Native F04c implementation and integrated validation

The author approved the written native plan. Both approval gates are satisfied;
the execution method and one fresh independent final review were preserved.
Execution began at `68956dd23066c7c5c647345e5598b859ff97a10c`, preserving all
119 existing tracked/untracked files, including the three design/tracker files.
Root performed the native Lean, consumer, article and integration work.

Canonical.lean supplies three sufficient bounds, four proof-only certificates
of existing actions, and five exact support formulas including the elementwise
product law. Freshness.lean supplies atom freshness, evidence/carrier agreement,
bound and transport laws, swaps, canonical/product decomposition and four fresh
existence laws. All 34 production interfaces check with the approved hypotheses
and independent universes. No action, parallel support theory, quotient or
function/predicate interface was introduced.

One mechanical encoding adjustment was recorded: `instNominalFinset` is a
theorem rather than the proposed proof-only def, and its scoped registration
uses the fully qualified name. Pinned Lean's warnings and scoped name resolution
required this local correction. Its public name, type, assumptions and scope
are unchanged; no linter, reducibility or instance-priority setting was changed.
For proof-indexed product freshness, consumers specialize
`hx.fresh_prod_iff hy a` before rewriting; generic simp cannot recover both
certificates from proof-irrelevant product evidence. Carrier decomposition
simplifies automatically. The README records this usage distinction.

The seven consumers in `/tmp/nominal-f04c-execution/` are
`InstanceContracts.lean`, `ActionCoherence.lean`, `CanonicalSupportContracts.lean`,
`BoundaryContracts.lean`, `FreshnessContracts.lean`, `AvoidanceContracts.lean`
and `PublicSignatures.lean`. They import only Package and consume actual
conclusions. New-interface tests failed before their declarations were added,
then passed. Fixture corrections preserved their mathematical assertions.
The unordered-pair theorem uses `support_finset` for actual least-support
membership of both moved endpoints. Bool and unsupported pointwise-identity
evidence remain proved. Nested avoidance chooses two distinct fresh atoms and
uses them to fix both the full context and its components.

Integrated commands actually run, all with exit 0:

- `lake build Package +Package.Tests.AxiomAudit`: 972 jobs; dependencies cached,
  changed project artifacts rebuilt during execution.
- `lake env lean Package/Foundations/Canonical.lean` and
  `lake env lean Package/Foundations/Freshness.lean`: direct source checks.
- `lake env lean` on each of the seven temporary files listed above: all
  public signatures, evidence, exactness, action/scope and avoidance checks pass.
- `lake env lean Package/Tests/AxiomAudit.lean`: direct traversal of 178
  production declarations from seven defining modules, including generated
  names; only `propext`, `Classical.choice` and `Quot.sound`.
- `python3 Package/Scripts/check-imports.py`: eight production source modules
  including the root and one audit module reached. Checker unchanged, so no
  checker self-test rerun was required.
- Direct retained checks of F03a `ActionContracts.lean`/`NegativeContracts.lean`
  and F04b `BoundaryContracts.lean`: passed unchanged.

The native runner `python3 /tmp/nominal-f04c-execution/integrated.py` records
these 15 commands, with full output and timing in the execution directory.
Baseline checks, per-task missing-interface failures and successful reruns
are separate logs there. No fresh whole-project build, dependency bootstrap
or rebuild of unchanged reference libraries is claimed. The five delivered
foundation sources, reference code, pins, Lake configuration, shared tools and
historical roadmap remain unchanged.

The article was developed and compiled in each mathematical task. The final
`latexmk -pdf -interaction=nonstopmode -halt-on-error
-outdir=/tmp/nominal-package-article-build main.tex` invocation from docs/article/
rebuilt the reconciled manuscript to 20 pages with a clean log. Both assigned
sections are included from main.tex; abstract/introduction and related exposition
are reconciled. Extracted canonical-support/freshness text was inspected against
the actual mathematics, separately from compilation. All generated artifacts
remain outside the source tree; operational records remain outside the article.

Document and preservation checks pass: seven Markdown files, local links and
anchors, 50 distinct LaTeX labels, and all changed/untracked whitespace.
`git diff --check` passes. The execution snapshot identifies 14 intended
existing-file edits and three new files, preserving the other 105 of 119
baseline files and the prior work log verbatim. The validated Lean sources
are unchanged after integrated verification. Branch and HEAD are preserved.

**Integrated validation passes; independent final review is pending.**
F04c remains IN PROGRESS until that review is resolved. PKG-F04 stays open
for F04d; no later phase, commit, push, merge, cleanup or publication is included.

The fresh independent final review is now complete. It found no Critical or
Important issues and two Minor findings: one stale sentence describing F04c's
article as future, and the arbitrary-Finset-action guard running without
Pointwise/equality, so its certificate was inactive. Both findings were verified
and corrected. The strengthened guard now first synthesizes canonical Finset
nominality in the same scoped/equality context, then rejects the unrelated
action; `lake env lean /tmp/nominal-f04c-execution/ActionCoherence.lean` passes.
Document/preservation/diff checks also pass after the corrections. No production
proof or API change and no second review were needed; no findings remain deferred.

The reviewer independently reran the cached 972-job build, both modules, seven
consumers, three retained consumers, its additional action/evidence contracts,
the direct 178-declaration standard-axiom audit, 8+1 import coverage and all
document/preservation checks. A fresh manuscript build in
`/tmp/nominal-f04c-review-V2nE2A/article/` produced 20 pages with clean diagnostics;
the extracted text was checked against the mathematics. The report and exact
commands are in `/tmp/nominal-f04c-review-V2nE2A/review.md`.

The review's exclusions match the approved boundary: later quotient and
function/predicate phases, prior-foundation/reference redesign, selectors,
general binary freshness, tactics, persistent Package examples and new external
research comparisons are not part of F04c. Existing scholarship was not
re-audited and no clean Lean/bootstrap/reference rebuild is inferred.

**F04c is DONE. PKG-F04 remains IN PROGRESS for F04d.** All code, meaningful
consumers, audits, article correspondence/compilation and the final review pass,
with the two minor corrections verified natively. All work remains uncommitted
on `fasapa/nominal-package`; the checkout, reference sources and retained evidence
are preserved.

### 2026-10-06 — General freshness and independent generalization investigations

After the original F04c delivery, the author requested Pitts' symmetric
freshness relation and approved the bounded extension before F04d. The later
instruction makes natural mathematical generality a standing preference:
use general definitions and minimally assumed statements, derive special cases,
and count theory reuse/stability as benefits. This is recorded in AGENTS.md,
research decision R15 and the current research policy; it supersedes F04c's
initial atom-only scope without reopening the delivered support construction.

`Fresh A x y` now means disjointness of the two least supports. The elementwise
form is `hx.FreshWith hy`; `hx.Fresh a` and the former named atom laws are
derived specializations. The fully explicit `@Fresh` signature intentionally
adds the second carrier/action/nominality parameters. Thirty-three added
declarations supply symmetry, self-freshness, products on both sides, transport,
disjoint sufficient bounds iff, equivariant-map preservation and finite-set
contexts. No new action, instance, notation, tactic, least-support construction
or later quotient/function infrastructure was added.

Three agents independently investigated permutations/actions, support/least
support, and canonical/freshness interfaces, without repository edits. Root
inspected their reports and proof routes, retained four standalone probes,
and reran every probe successfully. The
[generalization report](research/2026-10-06-foundation-generalizations.md)
records the adopted freshness results and seven other checked proposals.
The latter remain outside production imports. Important boundaries include
failure of unrestricted support reflection for surjections/equivariant maps,
and a checked arbitrary-set support that omits an atom of least finite support.
The investigation does not authorize silently implementing all proposals.

Execution evidence is under `/tmp/nominal-general-freshness-9a13sgo9/`.
The new general consumer first failed on the atom-only interface, then passed.
Eight temporary public-import consumers pass, including both associations of
the six-condition product example, general evidence without nominal carriers,
and two supported functions fresh in a provably non-nominal pointwise function
carrier. The copied old explicit-arity fixture was adapted; the original F04c
scratch evidence is preserved.

Actually run and passed: `lake build Package +Package.Tests.AxiomAudit`
(972 jobs, cached dependencies and incremental project artifacts), direct
Canonical/Freshness checks, all eight consumers, three retained F03a/F04b
consumers, `lake env lean Package/Tests/AxiomAudit.lean` (226 declarations in
seven defining modules, only the standard three axioms), and
`python3 Package/Scripts/check-imports.py` (8+1 source coverage).
Root separately ran `lake env lean` on all four `Generalization*.lean` research
probes. The unchanged checker did not require self-tests. No fresh full-project
Lean build, dependency bootstrap or unchanged reference-library rebuild is claimed.

The article now presents the general relation first, with atom freshness as a
specialization, both-sided product decomposition, disjoint bounds and image laws.
The documented latexmk command builds 21 pages with a clean final log. A fresh
independent reviewer reran all production/consumer/probe checks, inspected
the mathematics and preservation, and built a fresh 21-page article. It found
no Critical/Important issues and one Minor: a stale atom-transport proof
description. Root corrected it to cite general disjoint-support transport and
`Finset.disjoint_image`, rebuilt the article in the documented and a fresh
output directory, and reran document/preservation checks. No production fix,
second review or deferred finding was needed. The report is retained at
`/tmp/nominal-final-review-Xr59FA/review.md`.

The follow-up preserves 108 of its 122 baseline files, with 14 intentional
edits and five added research files. Previous work-log text, all other foundation
production modules, reference code, pins, branch and HEAD are preserved.
**F04c, including general freshness, is DONE; PKG-F04 remains open for F04d.**
All changes remain uncommitted. The next handoff is the requested F04d design
prompt, carrying the current interfaces and the generality preference.

### 2026-10-06 — F04d specification prepared for review

The author requested the next bounded slice of PKG-F04, preserving all earlier
deliveries and approvals. Actual inspection found a clean working tree on
`fasapa/nominal-package`, HEAD `9c1cb9aa2f9f69d8d801a9864a9f0220b92ea62a`
(`Freshness`), which commits F04c, general freshness and the accompanying
article/research/instruction work. The supplied `68956dd` remains the prior
F04a/F04b revision. Earlier work-log descriptions are preserved verbatim.

The [written specification](superpowers/specs/2026-10-06-package-equivariant-quotients-design.md)
proposes two focused new modules: general `QuotientAction.lean`, using ordinary
relation-invariance evidence, `Quotient.map` and
`Function.Surjective.mulAction`; and `Quotient.lean` for the nominal
specialization. Explicit local installation fixes the action in every canonical
projection/support/nominality contract. There is no blanket quotient action or
nominality instance. General equivariant-surjection nominality transfer is an
additive theorem for already selected actions in Nominal.lean. Existing map
support and general freshness laws supply the other mathematical contracts.

The specification separately proposes a natural stronger parent: under infinite
atoms, one supported preimage and equivariance, membership in image support is
equivalent to membership in every supported preimage's support. The quotient
intersection formula follows, with no exact-support representative promised.
Pitts, CUP 2013, Section 1.7 and Proposition 2.30 were inspected directly; the
fresh-swap proof route is recorded, not represented as already kernel checked.
The strict-decrease consumer forgets the second component of an atom pair while
retaining the first. The universal-atom quotient tests nonattainment of support;
the universal quotient of the pointwise function carrier tests failure of
reverse supportedness. All seven prior research proposals have explicit
dispositions, and the completed three-agent investigation was not repeated.

Read the delivered source, audit/checker and pins, current foundation/spec/plan
and research inputs, retained Generalization probes, and the whole current
manuscript. Lean/Mathlib remain `v4.34.1`, with Mathlib at
`d13f23b723b8a846827a245b89c10fc7d3f11612`. A temporary existing-API inventory
checked independent universes and exact signatures. Its initial lookup of the
nonexistent direct `MulAction.toSMul` projection was corrected using the pinned
inheritance through SemigroupAction, and the inventory then passed. No proposed
F04d theorem or construction was implemented in that inventory.

Fresh baseline checks actually run:

- `lake build Package +Package.Tests.AxiomAudit`: passed, 972 jobs, cached
  project/dependency artifacts; audit output replayed.
- `lake env lean Package/Tests/AxiomAudit.lean`: passed, direct traversal of
  226 declarations in seven defining modules, with only the standard three axioms.
- `python3 Package/Scripts/check-imports.py`: passed, eight production source
  modules including Package and one audit module. Checker unchanged.
- `lake env lean /tmp/nominal-f04d-design-xxzz3gbk/PinnedAPI.lean`: passed after
  the lookup correction; only imports, checks and representative axiom prints.
- From docs/article/, the documented `latexmk -pdf -interaction=nonstopmode
  -halt-on-error -outdir=/tmp/nominal-package-article-build main.tex` succeeded
  with existing outputs current. The log has 21 pages and no warning/box
  diagnostic; this invocation did not rebuild it.

These are checks of the delivered baseline. No fresh full-project build,
dependency bootstrap, reference-library rebuild, new generalization-probe run
or independent F04d implementation review is claimed. Evidence and fingerprints
of 127 original files are under `/tmp/nominal-f04d-design-xxzz3gbk/`.

Inline self-review covered the action-indexed signatures, weaker elementwise
assumptions, generality, support strictness/nonattainment, research dispositions,
article obligations and active-candidate coherence tests. Document checks pass
for 70 local links, six anchors, fences and changed/new whitespace;
`git diff --check` passes. The preservation comparison leaves 126 of 127
baseline files unchanged, with only this roadmap edited and the specification
added. The previous work log, all Lean/article sources, pins, reference code,
historical roadmap, branch and HEAD are preserved.

F04d remains **IN PROGRESS for design, unimplemented**. Written-specification
agreement, then preparation and approval of the native implementation plan,
remain the next gates. The execution method is already selected. Article
development, meaningful temporary public-import consumers, all-module audit,
action-coherence negatives with active evidence, and one fresh independent
final review are part of the proposed delivery. PKG-F04 remains open; F05 and
PKG-01 remain undelivered. Design/tracker changes are left uncommitted.

### 2026-10-06 — F04d specification approved; native plan prepared

The author approved the concrete written F04d specification, including the
general supported-fiber characterization and its quotient intersection
corollary. The scope is no longer conditional on that mathematical choice.
The selected native execution method and one fresh independent final review
remain unchanged. Written-specification approval authorizes this plan; the
concrete written plan still requires approval before production changes.

Reinspection found the same branch and HEAD `9c1cb9a`, with only the prior
F04d roadmap/specification work uncommitted. Planning fingerprinted 128
tracked/untracked files and saved all eight approved Lean interface blocks
under `/tmp/nominal-f04d-plan-87zxcq02/`. The design baseline, committed F04c
and general-freshness work, retained research and historical work log are
preserved. No implementation, article-source edit, dependency change, branch
operation, commit or new investigation is part of this planning session.

The [native implementation plan](superpowers/plans/2026-10-06-package-equivariant-quotients.md)
assigns the unchanged 15-declaration contract in four tasks:

1. General scalar/monoid quotient actions and the projection interface, with
   explicit action installation, compatibility rejection and inherited-SMul checks.
2. General surjective nominality transfer and canonical quotient support
   adapters, with finite/empty carriers, individual evidence, general freshness
   consumers and unrelated-action negatives with canonical evidence active.
3. General supported-fiber membership and quotient intersection, with exact
   first-component support decrease, nonattainment and reverse-support boundaries.
4. Exact public signatures, whole-production audit, public/research documentation,
   article reconciliation, all overall F04 criteria and one independent final review.

Every mathematical task develops and compiles its LaTeX alongside Lean. Seven
temporary consumers import only Package. Fixed-parameter object bounds,
nested supported contexts, actual quotient elimination and retained Bool/
unordered-pair evidence support explicit reconciliation of the parent task;
predicate support reflection remains F05/PKG-01. The plan preserves the partial
disposition of the seven research proposals and adds no unapproved interface.

Planning self-review checks spec coverage, exact type/argument consistency,
step specificity, all five review-focus cases and proportion. Document and
preservation checks, rather than Lean proof checks, are the validation for this
stage. The preceding 972-job build, 226-declaration direct audit, 8+1 coverage
and current 21-page manuscript outputs remain design-session evidence; those
checks were not rerun during planning.

Planning validation passes: all eight approved specification Lean blocks are
unchanged, and all six declaration blocks in the plan match them exactly,
covering the 15 interfaces. Checks cover 77 local links, six anchors, balanced
fences, changed/new-file whitespace and `git diff --check`. The preservation
comparison leaves 126 of 128 baseline files unchanged, with only specification
approval/status and current tracker edits plus the new plan. The entire previous
work log, all Lean/article sources, reference code, pins, branch and HEAD remain
unchanged. These document checks do not claim implementation verification.

F04d remains **IN PROGRESS, unimplemented**, and PKG-F04 remains open. The next
gate is approval of the concrete native plan; do not repeat specification approval
or ask the author to choose a task/execution method. Leave all changes uncommitted.

### 2026-10-06 — Native F04d implementation and integrated validation

The author approved the concrete native plan, after approving the specification
including its stronger characterization. Both gates are satisfied. Execution
stayed in the requested checkout at `9c1cb9a`, preserving the 129-file initial
snapshot including the existing design/tracker work. Root implemented the plan
natively; no per-task delegation or repeat generalization investigation occurred.

All **15 approved declarations** are implemented with their exact signatures.
QuotientAction.lean uses `Quotient.map` for the scalar operation and
`Function.Surjective.mulAction` for monoid laws, with an existing MulActionHom
projection. There is no global/scoped quotient action or nominality instance.
Quotient.lean fixes the constructed action in every canonical contract. Its
support and nominality theorems reuse existing map laws and the new explicit
general surjective nominality theorem. Nominal.lean additionally proves the
general supported-fiber membership characterization with one fresh swap;
quotient induction gives the exact Set intersection of representative supports.
No existing production theorem or hypothesis was changed.

The scalar construction needs only SMul; action laws need a monoid. Nominality
transfer needs no infinitude, equality or inhabitance. Individual least support
and the fiber characterization need Infinite A and explicit support evidence,
without carrier-wide nominality or surjectivity in the general fiber theorem.
Public signature assignments verify these boundaries and independent universes.
Only the surjective nominality part of the prior seven research proposals is
promoted; the new fiber theorem is separately approved F04d work.

The seven main temporary consumers are ActionContracts, ActionCoherence,
SupportContracts, FreshnessContracts, BoundaryContracts, ExactnessContracts and
PublicSignatures under `/tmp/nominal-f04d-execution/`. Every file imports only
Package and consumes actual conclusions. Red logs precede the corresponding
implementation. Two temporary fixture extracts separately proved strict
decrease/nonattainment before the stronger characterization was introduced.
The first-component quotient retains `{a}` while dropping b from `{a,b}`.
The universal-atom quotient has no representative attaining its empty support;
the universal function quotient supports the image of an unsupported identity.
General freshness, finite/empty carriers and both action-mismatch tests with
canonical evidence active pass. No standalone Package/Examples layer was added.

Execution corrections were local to consumers and article layout: explicit
local instance binding for ordinary hs, exposing kernel equality to `decide`
instead of using an unimported tactic, exact guard messages, visible Finset-pair
equality and unused proof-binder names. They did not change production signatures,
weaken conclusions or relax linter/reducibility policies.

Actually run and passed after the last production edit:

```sh
lake build Package +Package.Tests.AxiomAudit
lake env lean Package/Foundations/QuotientAction.lean
lake env lean Package/Foundations/Nominal.lean
lake env lean Package/Foundations/Quotient.lean
lake env lean Package/Tests/AxiomAudit.lean
python3 Package/Scripts/check-imports.py
```

All seven main consumer files were also checked individually with `lake env lean`.
The retained `/tmp/nominal-general-freshness-9a13sgo9/AvoidanceContracts.lean`
and `GeneralFreshnessContracts.lean` pass against the new public root. Exact
commands/results are in the execution directory's `validation-*.json` files.
The full build passes **974 jobs**; the direct audit traverses **245 production
declarations in nine defining modules**, allowing only `propext`,
`Classical.choice` and `Quot.sound`. Coverage reaches **ten production source
modules and one audit**. The checker is unchanged, so its self-tests were not
rerun. Dependencies are cached and project modules rebuilt incrementally;
no fresh whole-project build or dependency bootstrap is claimed.

The quotient article section was written and compiled with each mathematical
task. It states the invariant relation and action, projection laws, sufficient
support and nominality, least-support inclusion, strict decrease, supported
fibers, exact class intersection and nonattainment, general freshness and the
predicate-reflection distinction. Abstract/introduction are reconciled. The
documented latexmk command rebuilds a **26-page** manuscript with a clean final
log. Generated artifacts remain outside the source tree. The mathematical
correspondence is checked separately from compilation.

Overall PKG-F04 evidence, to be reconciled with the final review before closure:

| Overall criterion | Current evidence |
| --- | --- |
| Finite/least support and transport/minimality | F04a/F04b source preserved apart from the two additive general theorems; supported dependent build, exact old/new interface use and complete audit pass. |
| Fresh existence and combined finite avoidance | Delivered F04c/general freshness unchanged; retained AvoidanceContracts and GeneralFreshnessContracts pass, including nested contexts and fresh-swap consequences. |
| Required product and quotient actions/support | Delivered exact product support is consumed in firstComponentSupport/Strict; canonical construction, projection, every sufficient bound, nominality, elementwise inclusion and exact intersection pass. |
| Fixed parameters, nested avoidance, quotient descent, least versus strong support | fixedParameterQuotientBound and fixedAtomNotEquivariant; heterogeneous/nested freshness consumers; the relation-respecting first-projection lift; actual Bool leastness and unordered-pair support boundaries all pass. |

Here quotient descent means the induced action and ordinary relation-respecting
elimination. It does not count predicate descent/support reflection, SupportsMap/
SupportsPred or Some/Any as delivered. F05 and PKG-01 remain later work.

Final document/preservation checks and one fresh independent final review follow.
**F04d and PKG-F04 remain IN PROGRESS pending that review.** All changes are
uncommitted; no commit, push, publication, merge, branch switch, dependency or
CI change is performed. Reference targets share no changed integration files;
their source preservation is checked separately without claiming a rebuild.

**Final independent review and closure.** The requested fresh reviewer found
no Critical, Important or Minor issues. The report is retained at
`/tmp/nominal-f04d-final-review-3fVxOr/report.md`. It checks the exact interfaces,
mathematical proof routes, active-candidate negatives, meaningful boundaries,
all-module coverage and article correspondence, and confirms the overall F04
evidence map. No production fix or second review was needed.

Independent verification compiled all nine foundation modules and Package.lean
from current source into a fresh temporary olean tree, excluding the repository's
project oleans from LEAN_PATH and reusing pinned dependency artifacts. All seven
main consumers, both retained context consumers and the direct 245-declaration
audit pass against those fresh artifacts. Coverage and diff checks pass. A fresh
article build in the review directory has 26 pages and no warning/box diagnostic.
This is a fresh Package proof-artifact build using cached dependencies, distinct
from root's incremental Lake build; neither is a clean dependency bootstrap.

Root checked the report's command/exit records and confirmed reviewed source
hashes were unchanged before final status edits. All seven review exclusions
match the approved scope: later predicate and function/binder/generator work,
unadopted generalizations, unoffered selector/stronger support claims, new
external-source research, reference/dependency bootstraps, and full visual or
platform/performance review. Their omission changes no delivered guarantee;
the relevant mathematical boundary claims and reference-source preservation
were checked. There are no unresolved or deferred review findings.

Final document checks cover eight Markdown files, 182 local links, 13 anchors
and 59 LaTeX labels, plus preserved signature blocks, fences and whitespace.
The execution snapshot comparison preserves 116 of 129 baseline files, with
13 intended edits and three additions. Existing Nominal source is only extended,
and the historical work log, reference code, pins, checker, historical roadmap,
branch and HEAD are preserved. Final closure changes documentation only.

**F04d is DONE; all overall criteria are met and PKG-F04 is DONE.** F05 and
PKG-01 remain undelivered. All changes and retained evidence remain uncommitted,
with no branch, publication or integration action performed.

### 2026-10-07 — F05 architectural investigation and written specification

Started from a clean index/tree on `fasapa/nominal-package` at
`32f3dba551761881409bbc7453054e214e582269` (`Nominal quotient`). Reconciled
current-state summaries to record committed F04d; retained historical logs.
No completed foundation task was restarted.

The [F05 investigation](research/2026-10-07-function-space-foundations.md)
inventories current Package source, pinned Mathlib and Pitts, compares all four
requested representations, and records bounded positive/negative Lean evidence.
Three independent investigations recommend a contextual hybrid: ordinary
function/predicate inputs with explicit certificates, distinct full conjugation
objects, and proof-field supported bundles for persistent nominal values.
The [written specification](superpowers/specs/2026-10-07-package-function-space-design.md)
sets proposed phases F05a (general function actions), F05b (map/predicate inputs)
and F05c (supported values and admissible curry). It is for author review, not
an approved implementation plan. F05 is IN PROGRESS; production checkboxes,
PKG-01 and F06 remain open.

The author asked agents to investigate the ordinary-first/bundle-first choice,
then proposed local-context plus user-provided sufficient bounds. The spec now
requires explicit-bound constructors and a proof-backed context rule, without
least-support computation. A retained consumer combines two particular capture
bounds with an arbitrary enlargement. Context discovery remains later tooling;
a proposed bound does not certify unsupported functions, predicates or globals.
The supplied Urban manuscript was read for that heuristic and, at the author's
request, broader induction/recursion consequences; the
[separate note](research/2026-10-07-urban-nominal-techniques.md) records its
version, exact contracts, source cautions and future-task implications.

Root verification actually run:

- `lake env lean docs/research/probes/F05FunctionSpace.lean`: exit 0, including
  full curry/uncurry, action separation, ordinary and nominal higher-order
  consumers, context bounds, proof-field computation and predicate bridge.
- `lake env lean docs/research/probes/F05Boundaries.lean`: exit 0, including
  empty domains, sharp constant injectivity, unsupported sections/predicates,
  fixed-atom equality and impossibility of supported fresh selection.
- `lake env lean docs/research/probes/GeneralizationSupport.lean`: exit 0;
  existing arbitrary-set support/reflection and finite-minimality boundary rerun.
- Representative `#print axioms` outputs use only `propext`, `Classical.choice`
  and `Quot.sound`; the concrete `#eval` identity returns `true`.
- Integrated article compiled with `latexmk`, output under
  `/tmp/nominal-f05-final-article/`; final log has no LaTeX warnings or undefined
  references. Exposition adds functions, sufficient contexts, curry limits and
  grounded Pitts/Urban/constructive comparisons, without implementation claims.
- `git diff --check`, explicit changed/new-file whitespace and local Markdown
  target checks passed; production/configuration diff and staged diff are empty.

These are standalone elaborations with cached pinned imports, not a fresh
production build or dependency bootstrap. No new production audit is claimed.
No production Lean, dependencies, CI, branch, commits, pushes or publication
changed. Research/LaTeX/specification edits and new scratch sources remain
uncommitted. The next gate is author review of the written specification;
implementation planning and its review/execution-method selection follow only
then.

### 2026-10-07 — F05 specification approved; implementation plan prepared

The author approved the written F05 specification after its review delivery.
The hybrid, three phases, context-bound interface and PKG-01 predicate-storage
boundary are now approved design. Production implementation has not started.
The [implementation plan](superpowers/plans/2026-10-07-package-function-space.md)
contains seven tasks, exact shared interfaces, temporary public-import consumers,
negative boundaries, article reconciliation and integrated audit/checks.
It adds the small ActionSupport module explicitly permitted by the spec so that
arbitrary-scalar reflection and group transport are shared without refactoring
F04. The author has not yet reviewed this new plan or selected its execution
method. Native execution with a fresh independent final review is recommended
because the tasks share the same type/action/coercion interfaces.

Planning rechecked branch, HEAD, dirty state, current production signatures,
Mathlib adapters, module/import/audit coverage and the preceding plan conventions.
HEAD remains `32f3dba`; all earlier uncommitted research, probes and LaTeX are
preserved. A pre-plan hash snapshot is retained at
`/tmp/nominal-f05-planning-baseline.json`. The inline plan self-review checked
spec coverage, dependency/interface consistency, five review-focus cases and
proportion. It corrected the computation consumer to use infinite Nat atoms
with discrete Bool data when its proof mentions least support.

Documentation links, code fences, whitespace, `git diff --check` and preservation
against the initial hashes passed. Only approval/status documentation and the
new plan changed in this turn. No production Lean, scratch probe, article source,
configuration, index or Git history changed; no Lean or LaTeX rebuild was needed
or claimed for this planning-only update. No commits were made. The next gate
is written-plan review and execution-method selection, not another specification
approval or a restart of the investigation.

### 2026-10-07 — Native F05 implementation and integrated verification

The author approved the written plan for native execution. Work stays on
`fasapa/nominal-package` at HEAD `32f3dba`, with earlier uncommitted research,
probes, article and design records preserved. The five new production modules
are ActionSupport, FunctionAction, FunctionSupport, PredicateSupport and
SupportedFunction, exported by Package. The code implements the approved
three-phase hybrid: general full function actions, ordinary map/predicate
certificates and supported function values with admissible currying.

Evidence directory: `/tmp/nominal-package-f05-execution.dsh2fg3l/`.
It retains the initial hash snapshot, native ledger, per-task failing/passing
logs, eight public-import consumers, a checked README consumer and article PDF.
The standalone consumers establish action separation, independent universes,
ordinary higher-order rewriting, computation with noncomputable proof evidence,
context bounds, empty constants, exact supported curry and the stated negative
boundaries. Every consumer currently exits 0 without warnings.

A concrete ergonomics failure required a focused representation detail:
`FinitelySupportedMap` and `SupportedMap.SectionsSupported` are reducible aliases
of their exact specified propositions. Literal existential/lambda evidence made
constructor/curry simp fail under implicit transparency with semireducible defs.
The retained RED/GREEN consumers exercise those exact calls. No existing support
or action definition changed, and no broad transparency setting was introduced.
This is a proof-interface choice, not weaker mathematics or an inferred support.

Integrated checks actually run:

- `lake build Package +Package.Tests.AxiomAudit`: exit 0, 980 jobs, rebuilding
  new/affected project modules against cached pinned dependencies.
- `lake env lean Package/Tests/AxiomAudit.lean`: exit 0; 573 production
  declarations from 14 defining modules; only propext, Classical.choice and
  Quot.sound. The direct run is separate from Lake's cached replay behavior.
- All eight temporary public consumers and the extracted README consumer:
  exit 0 without warnings; proof-field computation returns true.
- `python3 Package/Scripts/check-imports.py`: all 15 production source modules
  and the separate audit reached, with the existing policy unchanged.
- Integrated article compiled with latexmk into the evidence directory:
  33 pages, final log without warnings or undefined references.
- Diff whitespace and baseline-hash preservation checks pass. Reference Lean,
  prior probes, toolchain/dependency/configuration files, index and HEAD are
  unchanged. No clean dependency bootstrap is claimed.

At this verification checkpoint F05 remained IN PROGRESS pending its fresh
independent final review and final status reconciliation. F06 and PKG-01 remain unimplemented. No commits, branch
operations, pushes, CI changes or publication occurred.

#### F05 final review and completion

The fresh independent read-only review found no Critical, Important or Minor
issues. It independently reran every supplied consumer, Package build, direct
audit and import/diff checks, and added a mixed-sort/same-carrier test covering
actual renamed bundles, predicate bridges, independent output evidence and
extensional reconstruction. The additional source is retained in the execution
evidence directory as IndependentReview.lean; final-review.md records the verdict.
The complete review-focus matrix and all F05a/b/c acceptance criteria are met.
PKG-F05 is DONE, delivered uncommitted. PKG-01 and F06 remain separate open tasks.

The review explicitly set aside a clean dependency bootstrap, larger-client
performance, external Isabelle/Rocq builds and complete inherited-bibliography
re-audit. These were not required by this plan; no corresponding success claims
are made. Central Pitts/Urban comparisons were checked, and root compiled the
article whose log the reviewer inspected. There are no deferred minor findings.

### 2026-10-07 — PredicateSupport module naming

At the author's request, the predicate foundation module is now
`Package/Foundations/PredicateSupport.lean`. The public import, specification
and implementation plan use that name. Its mathematical declarations are
unchanged. `lake build Package +Package.Tests.AxiomAudit`, the direct audit,
import coverage and `git diff --check` pass; no old module-name references
remain in Package or the documentation. The audit still covers 573 production
declarations with only the standard permitted axioms. Changes remain uncommitted.

### 2026-10-07 — PKG-01 architectural investigation and written specification

Inspected clean `fasapa/nominal-package` at
`3c9d8dc527f7705b24c0308a2527e659ae933874`, which commits F05 as
“some predicate + function support”. Current summaries now identify that
committed delivery; preceding work-log entries retain their historical states.
F02–F05 are complete and their implementation was preserved.

The author authorized investigation, bounded scratch probes, notes and a
reviewable specification, with no production implementation or commits. Three
independent investigations covered representation/logic, pullback/descent and
fresh quantification; root owned shared documentation and reconciliation.
The [current-source record](research/2026-10-07-pkg01-predicate-foundations.md)
contains the inventory, pinned Mathlib reuse, representation comparison,
counterexamples and evidence. The
[written specification](superpowers/specs/2026-10-07-package-predicate-foundations-design.md)
recommends:

* a direct ordinary-Prop predicate record with proof-only support and named
  supported-map/subset views, deriving action/support from F05;
* logical and quantified support with minimal hypotheses, Boolean structure
  transferred from Mathlib's supported Boolean subalgebra, and supported-family
  union/intersection without unrestricted external completeness;
* ordinary descent from `Setoid.liftEquiv`, plus exact sufficient-bound
  reflection along equivariant surjections and F04's canonical quotient action;
* cofinite `Freshly`, supplied-bound Some/Any, elementwise parameter contexts
  and precise logical/interchange boundaries.

The author selected scoped `И` notation alongside the named operation.
Direct storage versus the viable predicate-facing SupportedMap wrapper and
the proposed 01a/01b/01c review units remain written-spec review choices.
The full PKG-01 acceptance scope is retained; F06 is not made a prerequisite.

The probes check ordinary application/Iff/ext/higher-order behavior, the local
literal-existential simp remedy, independent universes and atom sorts, genuinely
non-nominal and empty quantified carriers, nonminimal logical bounds, and
supported collections. Descent checks include a nonempty-source counterexample
without surjectivity, a supported but incompatible binder observation and an
unsupported ordinary predicate used through quotient descent and induction.
Fresh checks include enlarged bounds, finite avoidance, no-global-selector,
unsupported singleton union and quantifier-interchange obstructions, plus the
valid common-bound repairs. They remain standalone research evidence.

Root verification actually run:

* `lake build Package +Package.Tests.AxiomAudit`: exit 0, cached 980-job baseline.
* `lake env lean Package/Tests/AxiomAudit.lean`: exit 0, 573 production
  declarations from 14 defining modules, standard axioms only.
* `python3 Package/Scripts/check-imports.py`: exit 0, all 15 production source
  modules and the separate audit reached.
* Direct elaboration of final
  `2026-10-07-pkg01-representation.lean`, `2026-10-07-pkg01-descent.lean` and
  `2026-10-07-pkg01-fresh.lean` under `docs/research/probes/`: all exit 0 without
  warnings/errors. Their 14/16/24 representative axiom reports use only standard
  foundations. These are fresh source checks using cached pinned imports.
* LaTeX compilation into `/tmp/pkg01-article-build`: exit 0, 37-page article,
  final log without warnings, unresolved references or box diagnostics.
  `sections/predicates.tex` states mathematical results and proof ideas;
  unsettled interfaces and operational records remain outside the manuscript.
* Changed/new-file whitespace, local Markdown targets, `git diff --check`,
  admission scan and preservation checks pass. HEAD, branch and index remain
  unchanged; no production, reference source, historical roadmap, dependency
  or CI file changed. No clean bootstrap or fresh full project rebuild claimed.

Independent read-only design checks found no blocking mathematical findings.
Root incorporated the Set-view elementwise-support clarification, precise
Pitts attribution and strengthened hypothesis separation, then self-reviewed
scope, placeholders and remaining proof obligations. PKG-01 remains **IN
PROGRESS**, with production criteria open. Review the written specification
before creating an implementation plan; review that plan and select an execution
method before production work. All documentation and new probes remain uncommitted.

### 2026-10-07 — PKG-01 storage-choice follow-up

At the author's request, two independent agents investigated the direct record
and predicate-facing SupportedMap wrapper. The
[research follow-up](research/2026-10-07-pkg01-predicate-foundations.md#follow-up-direct-record-versus-supported-map-wrapper)
records the symmetric adapter tradeoff and newly checked full wrapper action,
nominality, support and higher-order consumers. Both stores have `rfl` conversion
round trips and matching logical/map precomposition; no performance or
computation winner is established. The investigators have different mild
preferences, with no technical blocker in either candidate.

Root directly compiled both final temporary probes, with seven/seventeen
standard-only axiom reports and no diagnostics. Existing uncommitted work,
production source, branch, HEAD and index are preserved; no implementation plan
or production work began. The direct recommendation remains provisional and
the 01a/01b/01c scope is unchanged. No scientific article claim changed, so this
interface-comparison follow-up requires no new manuscript text.

### 2026-10-08 — PKG-01 direct predicate representation selected

The author chose **choice 1**, the direct `X → Prop` record with proof-only
`FinitelySupportedPred` evidence. The specification, current research summaries
and brief now record that decision as settled. Supported-map and subset views,
F05 reuse and the full logical/descent/Some/Any scope are retained. The wrapper
comparison remains historical design evidence.

This is representation selection, not approval of the full written specification
or an implementation plan. The next review remains the complete specification,
including the proposed 01a/01b/01c units. No production implementation, planning,
commit or branch change is authorized or performed by this update. Only
documentation changed. Content/whitespace checks, 213 local Markdown targets
and `git diff --check` pass. A hash comparison confirms exactly the six intended
decision-record documents changed in this turn and all other initial files were
preserved. HEAD, branch and index are unchanged. No new Lean or article
compilation was needed or claimed.

### 2026-10-08 — PKG-01 specification approved; implementation plan prepared

The author approved the full written specification after its storage decision
was incorporated. Direct proof-field SupportedPred, scoped И notation and the
complete 01a/01b/01c scope are approved. The
[implementation plan](superpowers/plans/2026-10-08-package-predicate-foundations.md)
now assigns eight tasks: ordinary logical support; carrier/views/Boolean
structure; bundled quantification; ordinary pullback/descent; supported descent;
cofinite Some/Any; contexts/bundled fresh projection/boundaries; and integration.

The plan fixes seven new module responsibilities, focused extensions to existing
pullback-related foundations, public names/types, nine temporary public-import
consumers, representative axiom checks, article reconciliation and preservation
checks. Mathlib and current source were consulted for the Boolean transfer,
setoid universal property, cofinite laws, import classification and audit policy.
No production code, temporary consumer or manuscript content was changed while
writing the plan. Existing scratch evidence is not reported as new implementation.

Inline plan self-review checked every approved requirement against its owner
task, type/name consistency, five additional review-focus cases and proportion.
It clarified elementwise least-support formulas, removed redundant Equiv inverse
aliases and fixed explicit ownership of compatibility connector lemmas. All
implementation task boxes remain unchecked.

Documentation verification passed: 226 local Markdown targets at the checkpoint,
changed/new-file whitespace and `git diff --check`; a hash comparison confirmed
exactly six existing documentation files changed plus the new plan, preserving
all other initial files. HEAD remains `3c9d8dc`, branch `fasapa/nominal-package`,
and the index is unchanged. No new Lean or article compilation is needed for
this approval/planning-only change, and none is claimed.

The plan awaits author review and an execution-method choice. Native execution
with one fresh independent final review is recommended because the eight tasks
share closely related interfaces; subagent-driven execution with per-task review
remains available. Specification approval is recorded once and is not requested
again. Production implementation, commits and branch operations have not begun.

### 2026-10-08 — Native execution approved; fresh-context Task 1 handoff

The author approved the implementation plan and explicitly selected native
execution, with a fresh context for each phase/step. The handoff unit is one
complete numbered task: execute all of that task's checklist, record its evidence
and the next prompt, then stop before the next task. Task 1 covers ordinary
logical support and quantification; it is the first part of phase 01a, whose
remaining work belongs to Tasks 2–3. The independent final review remains Task 8.

The plan/spec and current summaries record the approval and this execution
boundary, so future contexts do not request the same approvals or restart the
foundation/design investigations. Each handoff records actual source/status,
checks and scratch evidence paths; temporary state must be verified rather than
assumed to survive. No production implementation is performed while preparing
the first prompt, and all implementation checkboxes remain open.

Documentation checks passed: 227 local targets, changed-file whitespace and
`git diff --check`. A hash comparison confirmed only the seven intended approval/
handoff documents changed in this turn, preserving every other initial file.
HEAD, branch and index are unchanged. No Lean or article rebuild was needed
or claimed for this documentation-only handoff.


### 2026-10-08 — Task 1 complete: ordinary logical support and quantification

**Delivered uncommitted; phase 01a and PKG-01 remain open.** Tasks 2–3 are still
required for 01a; the independent whole-change review remains assigned to Task 8.
No Task 2 implementation was started. No mathematical contract changed.

Evidence directory: `/tmp/nominal-package-pkg01-execution.WReW3a/`.
`initial-snapshot.json` records all 151 baseline file hashes, branch, HEAD, index
hash and status; `initial.diff` preserves the starting tracked diff.
`task-1-brief.md` and `progress.md` retain the task and execution ledger.

Created `Package/Foundations/PredicateLogic.lean` and exported it from `Package`.
Its 23 public declarations are `supportsPred_const`, `SupportsPred.not`,
`supportsPred_not_iff`, `SupportsPred.and_same/or_same/imp_same/iff_same`,
`SupportsPred.and/or/imp/iff`, `FinitelySupportedPred.const/not/and/or/imp/iff`,
`SupportsPred.all/ex`, `FinitelySupportedPred.all/ex`, and `SupportsPred.iAll/iEx`.
The common-bound and existential statements need no decidable atom equality;
only displayed union bounds require it. Quantification preserves the joint bound
without nominality, nonemptiness or infinitude; external indices range over an
independent `Sort`. Restricted quantification accepts support of the combined
body itself. No new generic support hierarchy, bundled predicate, notation,
descent or fresh quantifier was introduced.

`Fixtures.lean` first passed with the proved nonnominal FunctionObject carrier.
`01Logic.lean` then failed on the planned missing public declarations (exit 1,
`01Logic-red.log`), with no fixture failure. After implementation it passed,
including joint ∀/∃, restricted implication/conjunction, separate guard bounds,
uniform action-free Sort indices, empty carriers/indices and genuinely nonnominal
quantified carriers. Independent universe parameters and all 23 exact signatures
are checked; representative prints for `.all`, `.ex`, `.iAll` and negation
reflection use only `propext`, `Classical.choice`, `Quot.sound`. The nonminimal
`{0,1,2}` certificate for `n = 0 ∨ n = 1` is consumed to prove the disjunction
at `π • 0`, rather than discarded.

Verification actually run, all final exits 0:

- `lake build Package.Foundations.PredicateLogic Package` — 980 jobs;
  newly elaborated PredicateLogic and public root, cached dependencies
  (`logic-build.log`). Baseline `lake build Package` passed with 979 cached jobs.
- `lake build Package.Foundations.PredicateLogic Package +Package.Tests.AxiomAudit`
  — 981 jobs; production artifacts cached from that build, audit freshly built
  (`final-build.log`).
- `lake env lean /tmp/nominal-package-pkg01-execution.WReW3a/01Logic.lean`
  — fresh source elaboration, all consumers and signature/axiom prints pass
  (`01Logic-final.log`).
- `lake env lean Package/Tests/AxiomAudit.lean` — fresh source elaboration;
  597 production declarations from 15 modules, no axioms beyond the three
  standard foundations (`axiom-audit.log`).
- `python3 Package/Scripts/check-imports.py` — all 16 production sources
  (including the root) and the one audit source reached (`import-coverage.log`).
- `lake build Nominal Instances Examples` — 1033 cached jobs; reference audit
  output replayed, not a fresh reference audit (`reference-build.log`).
- From `docs/article`, `latexmk -pdf -interaction=nonstopmode -halt-on-error
  -outdir=/tmp/nominal-package-pkg01-execution.WReW3a/article-build main.tex`
  — 37-page PDF; fresh external output directory. A new overfull line in the
  predicate API paragraph was shortened and recompiled; the final TeX log has
  no warnings or overfull/underfull boxes. Article changes clarify complement
  reflection, weakest quantifier premises, combined restricted bodies and
  independent uniform indices; task metadata stays outside the manuscript.
- `git diff --check` plus changed/new-file whitespace and local Markdown target
  checks pass. `validation-lean.json` and `validation-article.json` retain exact
  commands, working directories and exit codes.

Preservation check: `check-preservation.py` / `final-snapshot.json` confirm 142
of 151 initial files byte-identical, exactly nine intentionally reconciled
existing files, and only the new PredicateLogic source added. Those nine are
the public root, Package README, predicate article section, active roadmap,
plan, spec, current predicate research report, readiness summary and research
index. Existing article entry/quotient work, all probes, other research files,
reference source, historical roadmap, pinned dependencies, branch
`fasapa/nominal-package`, HEAD `3c9d8dc527f7705b24c0308a2527e659ae933874` and
index are unchanged. No commit, push, worktree, dependency or CI operation.
README/spec/current summaries now distinguish this partial delivery from the
remaining supported carrier, bundled logic, descent and cofinite work.

The copyable Task 2 prompt is in the [plan execution record](superpowers/plans/2026-10-08-package-predicate-foundations.md#copyable-fresh-context-prompt-for-task-2)
and `/tmp/nominal-package-pkg01-execution.WReW3a/Task2-handoff.txt`.

### 2026-10-08 — Task 2 complete: direct predicate values and semantic views

**Delivered uncommitted; phase 01a and PKG-01 remain open.** Task 3 is still
required for 01a. No Task 3 implementation was started, and the independent
whole-change review remains Task 8. No mathematical contract or hypothesis
changed; there were no mathematical rulings or deferred findings in this task.

Evidence remains `/tmp/nominal-package-pkg01-execution.WReW3a/`.
Earlier Task 1 evidence was present and preserved. Task 2's separate baseline is
`task-2-initial-snapshot.json`, `task-2-initial.diff` and `task-2-baseline/`, covering
152 existing files, branch, HEAD, status and index. `task-2-brief.md` and the
appended `progress.md` retain the task and ledger. Execution follows the explicit
user constraints: existing checkout, external evidence, no commits/worktree,
native implementation and stop at the numbered-task boundary.

Created `Package/Foundations/SupportedPredicate.lean` and exported it through
`Package`. The direct record has only `toFun : X → Prop` and proof-only
`supported : FinitelySupportedPred A toFun`. Delivered interfaces include:

- `instFunLike`, `ext`, the `@[ext]`-generated `ext_iff`, `congr_apply`,
  `ofFun/ofSupports/ofInvariant`, constructor application/coercion simp and
  `ofFun_proof_irrel`; both `coe_ofFun` and `coe_ofFun_exists` handle the two
  certificate forms without changing F05's reducibility.
- `toMap/ofMap/mapEquiv`, `toObject`, `toSet/ofSet`, their computation, inverse
  and action laws, including `toObject_eq` and `toSet_ofSet`.
- `instMulAction` via `renamePred` and injective transfer through `toObject`,
  `smul_apply/smul_apply_smul`, `supports_iff` and
  `supports_iff_toMap/toObject/toSet`, and `instNominal`.
- `toObject_finitelySupported`, `toSet_finitelySupported`,
  `support_toMap/toObject/toSet`, retaining elementwise full-view certificates
  and agreement with independently supplied evidence.
- `supportedSets` as Mathlib's `BooleanSubalgebra`, `subsetEquiv`,
  `mem_subsetEquiv`, the restricted image action with `val_smul_supportedSets`,
  `subsetEquiv_smul`, subtype nominality, `support_subsetEquiv`, and the single
  `instBooleanAlgebra` transferred using `Equiv.booleanAlgebra`.

Basic construction, action, nominality and Boolean structure retain independent
atom/carrier universes and require only the selected action on X. Least support
adds Infinite A. No Prop action, competing bare-arrow/Set action, full-powerset
nominality, chosen-support data, manual Boolean algebra or Task 3 operation
layer was added. The pinned Mathlib revision was checked as
`d13f23b723b8a846827a245b89c10fc7d3f11612` before using its transfer machinery.

`02Fixtures.lean` first passed using only delivered foundations.
`02Carrier.lean` then failed on missing SupportedPred names (exit 1;
`02Carrier-red.log`, reaching Lean's 100-error limit). The completed consumer
passes ordinary Prop application, Iff ext, rw/simp, higher-order application,
named/literal certificates, enlarged bounds, both equivalence round trips,
independent universes, two atom sorts (also on one carrier), view renaming,
nominality without Nominal X, Boolean computation and least-support witness
independence. A computable reconstruction keeps least-support choice inside
its certificate. A fixed-atom predicate is proved noninvariant, and the larger
`{0,1,2}` bound is consumed to prove its renamed proposition. Bare-arrow action
is tested on an actually acted codomain; Set-image membership is tested both by
inverse precomposition and by an explicit image witness.

The consumer also guards the observed failures to infer a Prop action or
Nominal Set Nat, and rejection by `ofSet` of a certificate for an independently
selected Set action. These guards pass, including the standalone
`02ActionBoundary.lean`. Additional higher-order map/Set constructor checks
already passed using existing simp rules (`02Carrier-views-red.log` is exit 0);
no extra coercion infrastructure was needed.

Resolved diagnostics: the first build attempted a redundant manual `ext_iff`,
which Mathlib's `@[ext]` had already generated, and omitted `(B := A)` from a
partially applied general support-reflection theorem. The duplicate was removed
and the atom carrier made explicit. A consumer's unnecessary `simpa` was changed
to `simp at he`. Final production/consumer checks have no warnings or errors;
guarded negative diagnostics are intentional and fully matched.

Checks actually run in this context, all final exits 0:

- `lake build Package.Foundations.SupportedPredicate Package` — 985 jobs;
  SupportedPredicate and Package freshly elaborated with cached dependencies
  (`task-2-build-2.log`). The earlier failed build is retained separately.
- `lake build Package.Foundations.SupportedPredicate Package +Package.Tests.AxiomAudit`
  — 986 jobs; production artifacts cached from the affected build, audit freshly
  elaborated (`task-2-final-build.log`).
- `lake env lean /tmp/nominal-package-pkg01-execution.WReW3a/02Carrier.lean`
  — fresh consumer elaboration and representative signature/axiom prints
  (`02Carrier-final.log`). `mapEquiv`, `subsetEquiv`, `supports_iff`,
  `instNominal`, `support_toSet` and `instBooleanAlgebra` depend only on
  `propext`, `Classical.choice`, `Quot.sound`.
- `lake env lean /tmp/nominal-package-pkg01-execution.WReW3a/01Logic.lean`
  — freshly rerun, source unchanged (`task-2-01Logic.log`). Earlier Task 1 logs
  remain prior-context evidence.
- `lake env lean Package/Tests/AxiomAudit.lean` — fresh direct audit of 703
  production declarations from 16 defining modules, with only the three
  standard foundations (`task-2-axiom-audit.log`).
- `python3 Package/Scripts/check-imports.py` — all 17 production source modules
  (including Package) and the one audit source reached (`task-2-import-coverage.log`).
- `lake build Nominal Instances Examples` — 1033 cached jobs; reference audit
  output replayed, not freshly elaborated (`task-2-reference-build.log`).
- From `docs/article`, `latexmk -pdf -interaction=nonstopmode -halt-on-error
  -outdir=/tmp/nominal-package-pkg01-execution.WReW3a/task-2-article-build main.tex`
  — fresh external output directory, 38-page PDF, no warnings or overfull/underfull
  boxes (`task-2-article.log`, `task-2-article-build/main.log`). The exposition now
  explains direct proof-field storage, semantic views, support agreement and
  the transferred Boolean structure; it contains no task/approval/evidence metadata.
- `git diff --check`, staged diff check, changed/new-file whitespace, local
  Markdown target checks, admission scan and task-boundary checks pass.
  `task-2-validation-lean.json` and `task-2-validation-article.json` record
  commands, working directories and exits.

Preservation: `task-2-check-preservation.py`, `task-2-preservation.log` and
`task-2-final-snapshot.json` confirm 143 of 152 baseline files byte-identical,
exactly nine intentionally reconciled existing files, and only the new
SupportedPredicate source added. The nine are the public root, Package README,
predicate article section, active roadmap, plan, spec, current predicate research
report, readiness summary and research index. `task-2-only.diff` isolates this
context's changes from earlier work. Task 1's PredicateLogic, all research probes,
existing article entry/quotient work, other research files, reference source,
historical roadmap, pinned dependencies, branch `fasapa/nominal-package`, HEAD
`3c9d8dc527f7705b24c0308a2527e659ae933874` and index are unchanged. No commit,
push, worktree, dependency or CI operation was performed.

Task 3 owns the additional bundled logical/quantified/collection operations and
all their named computation, bound and action laws. The Boolean instance is
already delivered and must be reused. Descent and fresh quantification remain
later tasks. The copyable handoff is retained as `Task3-handoff.txt` in the
external evidence directory and in the [plan execution record](superpowers/plans/2026-10-08-package-predicate-foundations.md#copyable-fresh-context-prompt-for-task-3).

### 2026-10-08 — Task 3 complete: bundled logic and quantification; phase 01a complete

**Delivered uncommitted. Tasks 1–3 and phase 01a are complete; PKG-01 remains
IN PROGRESS for Tasks 4–8.** Task 4 is the first task of phase 01b and was not
started. The independent whole-change review remains assigned to Task 8.
No mathematical contract or hypothesis changed, and no finding was deferred.

Evidence remains `/tmp/nominal-package-pkg01-execution.WReW3a/`.
All required earlier evidence was present and read, including `progress.md`,
`task-2-brief.md`, `task-2-final-snapshot.json`, both Task 2 validation JSON files,
and the `01Logic.lean` and `02Carrier.lean` consumers. Every file hash in the
Task 2 final snapshot matched the actual checkout. Task 3 took a new baseline:
`task-3-initial-snapshot.json`, `task-3-initial.diff`, `task-3-baseline/` (153
files), and `task-3-brief.md`. Earlier evidence is retained; only the shared
ledger is appended. Explicit user instructions continue to govern execution:
native work in the existing checkout, external evidence, no commits/worktree,
and stop at this numbered-task boundary.

Created `Package/Foundations/SupportedPredicateLogic.lean` and exported it from
`Package`. It reuses the single BooleanAlgebra delivered by Task 2 and F05's
ordinary precomposition/section laws. Delivered interfaces in `SupportedPred`:

- Boolean/order `*_apply` and `coe_*` simp laws for bot/top/inf/sup/complement,
  implication and difference; `le_def`; derived `biimp` with both computation laws.
- `precomp`, `precompMap`, individually certified `section`, jointly acted
  `all`/`ex`, and `collectionUnion`/`collectionInter`, each with application and
  coerced-function equations. `coe_section_exists` additionally handles literal
  parameter certificates without changing foundational reducibility.
- All planned Boolean/operator action laws, including order reflection,
  simultaneous predicate/map and relation/parameter renaming, quantifier
  reindexing and collection renaming.
- `supports_compl_iff`, binary/precomposition/section union bounds,
  `supports_all/ex/collectionUnion/collectionInter` retaining the very same
  input bound; empty support of bot/top, exact `support_compl`, and all planned
  `support_*_subset` laws. Difference and the supported-map adapter have the
  corresponding bounds too. Ordinary precomposition uses the exact supplied
  `hf.toObject.support`; a section uses `hy.support`.

Collection operations construct supported guarded relations from jointly
invariant evaluation, then use ordinary universal/existential quantification
over the ambient supported-predicate carrier. This is neither an external
arbitrary-family join nor an unrestricted CompleteLattice. No second Boolean
algebra, curry hierarchy, Prop action, bare-arrow/Set action, or new general
infrastructure was introduced. Basic operators preserve independent universes
and require only selected actions. Infinite atoms occur only in least-support
corollaries; decidable equality occurs only on displayed finite unions.
Pinned Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612` and the existing
Boolean transfer/computation sources were inspected before implementation.

`03Fixtures.lean` first compiled using only existing source (exit 0).
`03Quantifiers.lean` then failed on missing Task 3 names, before production
edits (`03Quantifiers-red.log`; initial 100-error cap). A consumer typo applying
`inf_bot_eq` without its argument was corrected, and the diagnostic run with
`-DmaxErrors=1000` records all missing-interface failures in
`03Quantifiers-red-2.log`. This diagnostic-only option changes error reporting,
not proof checking. Final consumers use the requested direct Lean command.

The passing consumer covers every planned name and printed signature, all
Boolean computations including implication/difference/order, named/literal
higher-order use, restricted quantification through separately bundled or only
combined certified bodies, generic empty quantified carriers, a concrete empty
carrier over finite Bool atoms, and genuinely non-nominal full function objects.
The latter carrier is proved non-nominal using an unsupported constant under
left multiplication, while its supported identity is fixed using only its
individual certificate. Supplied relation/parameter and collection bounds
prove actual renamed propositions. Both collection bounds are consumed in
renamed union/intersection conclusions. Operator action equations are checked,
including explicit Equivariant consumers. A singleton-supported zero predicate
has least support `{0}`, whereas its intersection with bottom has empty support,
so support loss is proved strict rather than merely asserted.

Resolved diagnostics: Lean reserves the token `section`, so the declaration
uses `«section»` while retaining the required public name. A higher-order
`xs.map (p \ q)` can elaborate at the Pi arrow type; the `pp.all` probe
`03SdiffInference.lean/.log` established this. Consumers now explicitly select
`(p \ q : SupportedPred A X)` to exercise the bundled coercion. A literal section
certificate then reproduced the semireducible-support simp issue already known
from Task 2 (`03Quantifiers-green-2.log`); `coe_section_exists` resolves it locally.
The concrete `Discrete Bool Empty` fixture supplies its own IsEmpty witness.
The final log scan caught the proof-local `letI` style warning; replacing it with
`let` and re-elaborating the consumer removed it (`03Quantifiers-final-warning.log`
retains the original diagnostic). All final production/consumer output is free of warnings and errors; Task 2's
intentional guarded diagnostics still match.

Commands actually run here, all final exits 0:

- `lake build Package.Foundations.SupportedPredicateLogic Package` — 986 jobs;
  new module and public root freshly elaborated using cached dependencies
  (`task-3-build-3.log`; earlier failed/successful iterations retained separately).
- `lake build Package.Foundations.SupportedPredicateLogic Package +Package.Tests.AxiomAudit`
  — 987 jobs; production artifacts cached from the affected build, audit freshly
  elaborated (`task-3-final-build.log`).
- `lake env lean /tmp/nominal-package-pkg01-execution.WReW3a/03Quantifiers.lean`
  — fresh elaboration; all consumers, exact signatures and representative axiom
  prints pass (`03Quantifiers-final.log`). `all_smul`, `section_smul`,
  `supports_collectionUnion`, `support_compl` use only `propext`,
  `Classical.choice`, `Quot.sound`.
- `lake env lean /tmp/nominal-package-pkg01-execution.WReW3a/01Logic.lean` and
  `lake env lean /tmp/nominal-package-pkg01-execution.WReW3a/02Carrier.lean`
  — both freshly elaborated, sources unchanged (`task-3-01Logic.log`,
  `task-3-02Carrier.log`). Earlier-context logs remain earlier evidence.
- `lake env lean Package/Tests/AxiomAudit.lean` — fresh direct audit: 818
  production declarations from 17 defining modules, with only the three standard
  foundations (`task-3-axiom-audit.log`). No admissions or additional axioms.
- `python3 Package/Scripts/check-imports.py` — all 18 production sources
  (including Package) and the one audit source reached (`task-3-import-coverage.log`).
- `lake build Nominal Instances Examples` — 1033 cached jobs; reference audit
  output replayed, not freshly elaborated (`task-3-reference-build.log`).
- From `docs/article`, `latexmk -pdf -interaction=nonstopmode -halt-on-error
  -outdir=/tmp/nominal-package-pkg01-execution.WReW3a/task-3-article-build main.tex`
  — fresh external output, 39-page PDF, no warnings or overfull/underfull boxes
  (`task-3-article.log`, `task-3-article-build/main.log`). The manuscript explains
  precomposition/sections, operator action and least bounds, empty quantification,
  and the guarded collection construction, with no task or verification metadata.
- `git diff --check`, staged diff check, changed/new-file whitespace and local
  Markdown target checks, admission scan, phase/task-boundary and preservation
  checks pass (`task-3-check-preservation.py`, `task-3-preservation.log`).

`task-3-validation-lean.json` and `task-3-validation-article.json` record commands,
working directories, durations and results. These are checks against cached
Lean/Mathlib dependencies, not a clean dependency bootstrap. There were no
unavailable required tools. No larger-client performance claim is made.

Phase 01a acceptance now passes as a whole:

| Criterion | Fresh evidence |
| --- | --- |
| Ordinary logical, joint/restricted/uniform support | Unchanged `01Logic.lean` rerun |
| Direct ordinary use, all views, coherent action/nominality and support agreement | Unchanged `02Carrier.lean` rerun, including action-separation guards |
| Single transferred Boolean structure and named logical/order laws | Both carrier and quantifier consumers; Task 2 source byte-identical |
| Sections, whole-carrier quantification, supported collections, empty/non-nominal clients and support loss | `03Quantifiers.lean`, including renamed conclusions and simultaneous action equations |
| Public root, imports, trusted proofs and reconciled exposition | Package build, fresh audit, coverage, signatures/axioms and external article build |

Preservation: `task-3-check-preservation.py` / `task-3-final-snapshot.json`
confirm 144 of 153 baseline files byte-identical, exactly nine intentional
reconciliations and only the new SupportedPredicateLogic source added. The nine
are Package.lean, Package README, predicate article, active roadmap, plan, spec,
current predicate research report, readiness summary and research index.
`task-3-only.diff` isolates these edits from existing uncommitted work. Earlier
PredicateLogic/SupportedPredicate source, consumers/evidence, all research probes,
existing article entry/quotient work, reference sources, historical roadmap,
dependency pins, branch `fasapa/nominal-package`, HEAD
`3c9d8dc527f7705b24c0308a2527e659ae933874`, and index are preserved. No commit,
push, merge, worktree, dependency upgrade or CI operation occurred.

Task 4 owns the general scalar/function/predicate pullback adapters and ordinary
quotient-predicate correspondence. It must preserve the explicit canonical-action
boundary and action-free ordinary descent. The complete fresh-context prompt is
`Task4-handoff.txt` in the evidence directory and in the [plan execution record](superpowers/plans/2026-10-08-package-predicate-foundations.md#copyable-fresh-context-prompt-for-task-4).

### 2026-10-08 — Task 4 delivered: ordinary pullback and quotient predicates

**Complete, uncommitted. Phase 01b continues with Task 5 in this run.** The author
explicitly changed this run to phase granularity; Task 6 is the stopping boundary.
Task4-handoff.txt was a START prompt, not a delivery. At entry all 154 files
matched the Task 3 final snapshot; no Task 4 production source or consumer existed.

Extended ActionSupport, FunctionAction and PredicateSupport; created/exported
PredicateDescent. The scalar parent requires only SMul. Full-object precomposition
is action-free, injective for surjections, and equivariant under DivisionMonoid;
ActionSupport.supports_map_iff reflects arbitrary sets. Ordinary predicate
pullback preserves bounds using F05 and reflects them through the scalar parent.
Elementwise least support agrees under surjectivity, with Infinite A only there.
Ordinary compatibility, kernel/fiber adapters, Mathlib liftEquiv correspondence,
computation, round trips, proof independence and obstruction require no action
or support. All canonical support/renaming theorem types select the quotient action.

External evidence: `/tmp/nominal-package-pkg01-execution.WReW3a/`.
`04Fixtures-green.log` passes existing foundations; `04Descent-red.log` records
missing interfaces before production edits. Final `04Descent.lean` proves both
support directions at arbitrary bounds, independent-universe SMul/DivisionMonoid
signatures, ordinary unsupported descent and quotient induction, diagonal
non-surjectivity failure, singleton-supported incompatible binder labels, and
rejection/non-equivariance of an unrelated trivial equality-quotient action.

Commands/results: `task-4-verified-validation.json` records exit 0 for
`lake build Package +Package.Tests.AxiomAudit`, each of `04Descent.lean`,
`01Logic.lean`, `02Carrier.lean`, `03Quantifiers.lean` via `lake env lean`,
`lake env lean Package/Tests/AxiomAudit.lean`, `python3 Package/Scripts/check-imports.py`,
`git diff --check`, and external latexmk. Affected-module build also passes
(`task-4-build-4.log`, 987 jobs). Audit build: 988 jobs, dependencies cached;
changed project modules were freshly built, and all consumers/direct audit freshly
elaborated. Audit: 858 declarations / 18 defining modules, only the standard three
axioms; scalar reflection is axiom-free. Coverage: 19 production sources plus audit.
No clean dependency bootstrap is claimed.

Resolved diagnostics: copied fixture lacked an explicit A binder under
`autoImplicit false`; equivariance rewriting needed its explicit scalar/input;
proof-local letI style and a class-valued fixture definition were corrected;
the unrelated-action fixture needed its kernel equality exposed. No mathematical
statement changed. Article line overflow was repaired by splitting a long Lean
name into namespace and declaration; final external
`latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir=/tmp/nominal-package-pkg01-execution.WReW3a/task-4-article-final main.tex`
from docs/article exits 0, 39 pages, no warnings or box diagnostics. Earlier logs
remain available. No mathematical rulings or deferred findings.

Article exposition now covers the nonempty diagonal counterexample, arbitrary-set
DivisionMonoid reflection, ordinary unsupported quotient induction, canonical action
selection and the distinction from object support. PKG-01 remains open; the
supported correspondence is Task 5, cofinite theory Tasks 6–7, final review Task 8.

### 2026-10-08 — Task 5 delivered: supported quotient correspondence; phase 01b complete

**Tasks 4 and 5 and their combined phase 01b acceptance criteria pass.** All
changes remain uncommitted. PKG-01 stays IN PROGRESS for Tasks 6–8. Task 6 has
not started; the independent whole-change review remains assigned to Task 8.
The author explicitly authorized Tasks 4–5 together in this run, superseding
only that part of the earlier per-task context boundary. No mathematical ruling
or deferred finding was needed.

Created and exported `Package/Foundations/SupportedPredicateDescent.lean`;
added the six action-free `Compatible.const/not/and/or/imp/iff` adapters to
PredicateDescent. Task 4's declarations remain unchanged. Delivered:

- `SupportedPred.pullback`, application/coercion computation, fixed-map action
  compatibility, same-bound preservation, every-bound reflection under
  surjectivity, and least-support equality with Infinite A.
- `CompatiblePred A s`, `compatibleAction A s hs` via Mathlib SubMulAction,
  `compatible_val_smul`, `supports_compatible_iff`, and explicit
  `compatibleNominal`. No instance guesses invariance or a quotient action.
- `descendSupported`, `supportedEquiv`, representative equations, both named
  inverse equations and action laws in both directions. Quotient-dependent
  types select the canonical action; action/support statements additionally
  select the compatible-subtype action.
- `supports_descendSupported_iff`, `supports_supportedEquiv_iff`,
  `support_supportedEquiv` and `freshWith_supportedEquiv_iff`. Basic laws
  require neither source nor quotient nominality. Infinite A occurs only in
  least support/freshness; the context uses its individual certificate with
  an independent universe, without Nominal on its carrier.
- Pullback and descent preserve top, bottom, complement, inf, sup, implication
  and biimplication through the existing Boolean structure. No second Boolean
  algebra, dependent data descent, binders or fresh quantifier was introduced.

Evidence remains `/tmp/nominal-package-pkg01-execution.WReW3a/`.
`05SupportedDescent-red.log` records the missing bundled/connector names before
implementation; `05Fixtures.log` independently passes the existing label and
non-nominal context fixtures. The final consumer proves computations, both
inverses, both action directions and exact sufficient/least support, including
freshness against a supported identity in a provably non-nominal function
carrier. It rejects implicit action guessing and passing a predicate certified
under an unrelated trivial quotient action to the canonical correspondence.
The quotient forgetting a discrete Bool label accepts equality with a fixed
atom at both labels, retains every supplied enlarged bound, computes after a
moving swap, and has exact singleton least support over infinite atoms.
The full public inventory has 79 new declarations across Tasks 4–5;
`Phase01bSignatures.lean` checks each, and the consumer additionally prints
explicit selected actions and representative axioms.

The combined acceptance checks preserve Task 4's unsupported ordinary descent
and quotient induction, scalar/DivisionMonoid generality and independent
universes, non-surjective diagonal obstruction, supported incompatible binder
observation and rejection of an unrelated quotient action. These tests are
external public-import consumers with autoImplicit false; no persistent Package
Examples layer was added.

Actual final commands/results are in `phase-01b-final-validation.json`, all exit 0:

- `lake build Package +Package.Tests.AxiomAudit` — 989 jobs, cached after
  iterative affected builds. `lake build Package.Foundations.SupportedPredicateDescent Package`
  freshly built the new module/root using cached dependencies (988 jobs,
  `task-5-build-3.log`). No clean dependency bootstrap is claimed.
- `lake env lean` on each of `04Descent.lean`, `05SupportedDescent.lean`,
  `01Logic.lean`, `02Carrier.lean`, `03Quantifiers.lean`, and
  `Phase01bSignatures.lean` in the evidence directory — fresh elaborations;
  final logs have no errors or warnings. Phase 01a's three consumer sources are unchanged.
- `lake env lean Package/Tests/AxiomAudit.lean` — fresh direct audit of 918
  declarations in 19 defining modules, allowing only propext, Classical.choice
  and Quot.sound. The cached build's audit output is distinguished from this run.
- `python3 Package/Scripts/check-imports.py` — all 20 production source modules
  (including the public root) and the separate audit are reached.
- `lake build Nominal Instances Examples` — 1033 cached jobs; reference audit
  output replayed, not a fresh reference audit.
- From `docs/article`, `latexmk -pdf -interaction=nonstopmode -halt-on-error
  -outdir=/tmp/nominal-package-pkg01-execution.WReW3a/phase-01b-final-article-build main.tex`
  — fresh external output, 40-page PDF, no warnings, unresolved references or
  overfull/underfull boxes.
- `git diff --check` — clean; final preservation validation also checks staged
  whitespace, changed-file whitespace and local Markdown targets.

Resolved diagnostics are retained: an omitted implicit element binder in
SubMulAction's closure field; a consumer biimplication needing explicit local
quotient action; a consumer rewrite requiring its local let exposed. The first
combined article build failed on an undefined support macro and line overflow;
ordinary operator notation and shorter sentences resolved both. The final full
validation is green; no diagnostics are suppressed and no hypotheses changed.

The article now develops the supported equivariant correspondence, exact bounds,
individual-context freshness, inherited logical operations and duplicate-label
example. Current README, specification, plan, research summaries and active
tracker describe the delivered interface. Historical records and prompts remain
historical; Task4-handoff.txt is preserved as a start prompt, not reclassified
as delivery. The manuscript contains no task or operational metadata.

Preservation evidence: `phase-01b-initial-snapshot.json`, `phase-01b-baseline/`,
`task-4-final-snapshot.json`, `phase-01b-final-snapshot.json`,
`phase-01b-only.diff` and `phase-01b-preservation.log`. Of 154 starting repository
files, 142 are byte-identical, twelve are intentional source/interface/status
reconciliations, and the two descent modules are new. All 417 earlier evidence
files are preserved (the shared ledger retains its exact original prefix).
Phase 01a sources and consumers, all research probes, unrelated article/research
work, the reference library, historical roadmap, dependency pins, branch, HEAD
and index are unchanged. Branch remains fasapa/nominal-package; HEAD remains
3c9d8dc527f7705b24c0308a2527e659ae933874; index SHA-256 remains
462fdfad827bcfebf9cf0239d1c5d0917226206646acc3270bd8892ffcd3a8ba.
No commits, branch/worktree changes, publication, dependency changes or CI edits.

Next: Task 6 begins phase 01c. `Task6-handoff.txt` contains the copyable prompt,
also retained in the plan below. Task 6 alone will not complete 01c; Task 7
and final integration/independent review in Task 8 remain required for PKG-01.

### 2026-10-08 — Task 6 delivered: ordinary cofinite truth and supplied-bound Some/Any

**Complete, uncommitted. Phase 01c continues with Task 7 in this run.**
The author authorized Tasks 6–7 together; Task 8 is the stopping boundary.
Created/exported `Package/Foundations/FreshQuantifier.lean`, importing only
PredicateLogic and Mathlib cofinite/finite filter theory. No SupportedPred dependency.

Delivered `Freshly` and opt-in typed/untyped `И`; definition/finite-exception/Finset
characterizations; pointwise/eventual congruence, monotonicity, conjunction, modus
ponens, constants and witnesses; independent-universe equivalence reindexing;
Sort-indexed one-way laws and finite universal interchange. Decision-based negation,
disjunction (either operand), implication and both distinct Iff interfaces retain
the plan's hypotheses. Some/Any uses supplied bounds, off-bound swap constancy,
evaluation and arbitrary extra finite avoidance, with no public DecidableEq.
Finite/cofinite classification, the infinite/coinfinite obstruction and supported
Boolean specializations need infinitude only for self-dual negation. Joint fresh
projection requires only the action on X. All three uniform-support interchange
laws retain their distinct infinitude/nonempty-index premises.

Evidence: `/tmp/nominal-package-pkg01-execution.WReW3a/`.
`06Fresh-red.log` records missing interfaces before production edits (the original
run reached Lean's 100-error limit). `06Fresh.lean` now checks the full interface,
finite Bool/Empty, Sort indices, no-Nominal projection, a supported antecedent
with arbitrary consequent, consuming enlarged/avoiding bounds, and scoped nested/
shadowed notation. A parser-based guarded unscoped check rejects the actual binder
syntax. `06Scope-red.log`/`06Scope-green.log` retain its focused investigation.

`task-6-final-validation.json` records all eleven commands at exit 0: Package plus
audit build, all six external consumers, direct axiom audit, import coverage,
diff check and external latexmk. Affected module/root freshly built with cached
dependencies (`task-6-build-2.log`, 1015 jobs); full build freshly compiled audit
(1016 jobs). Direct audit: 976 declarations / 20 defining modules, only the
standard propext/Classical.choice/Quot.sound axioms. Coverage: 21 production
sources plus audit. Consumers/direct audit freshly elaborated; no clean dependency
bootstrap claimed. The final LaTeX engine log has no warnings or box diagnostics;
initial cross-reference warnings in the multipass driver log resolved normally.

Resolved diagnostics: the reserved name exists is escaped in its declaration;
not_false no longer resolves recursively; reindexing exposes the Freshly definition
to simp; a deprecated Set lemma was replaced. The deliberate shadowing test now
uses both binders. Parser errors occur before #guard_msgs elaboration, so the
unscoped syntax is parsed within run_elab and its failure is tightly guarded.
No mathematical contract, public hypothesis or name changed. No rulings or
deferred findings. The article now states classification, precise Boolean premises,
finite/empty behavior, reindexing and all uniform-support alternatives.

### 2026-10-08 — Task 7 delivered: contexts and bundled fresh projection; phase 01c complete

**Tasks 6 and 7 and their combined phase 01c acceptance criteria pass.** All
PKG-01 changes remain uncommitted. Tasks 1–7 and phases 01a–01c are delivered;
PKG-01 remains IN PROGRESS pending Task 8: final integration, complete
specification coverage and the independent whole-change review. Task 8 was
not started and none of its checklist items was marked complete.

Extended FreshQuantifier with the eight ordinary context forms:
`freshly_section_iff_exists`, `_forall`, both `_avoiding` variants, and the
four `freshly_invariant_section_iff_*` variants. The explicit relation and
individual parameter bounds combine as S ∪ T. Displayed unions retain
DecidableEq; invariant forms use hx.Fresh a and need neither DecidableEq nor
Nominal X. All context Some/Any forms require Infinite A. They reuse F05
sections, Task 6 avoidance and the existing elementwise freshness interface.
`FinitelySupportedPred.freshly_iff_of_fresh` evaluates an ordinary predicate
using its individually certified predicateObject, without bundling it.

Created/exported SupportedPredicateFresh with `SupportedPred.fresh`,
`fresh_apply`, `coe_fresh`, `fresh_smul`, `supports_fresh`,
`support_fresh_subset` and `freshly_iff_of_fresh`. The operation stores only
its ordinary Prop-valued body and a support proof. Application/coercion simplify,
renaming commutes, and the same sufficient bound is retained without infinitude
or nominality of the parameter carrier. Least-support/freshness conveniences
add Infinite A. No new Fresh relation, support construction, global action,
filter hierarchy, or persistent Package Examples layer was introduced.

Evidence remains `/tmp/nominal-package-pkg01-execution.WReW3a/`.
`07Fixtures-red.log` is a successful fixture run (exit 0); the filename reflects
its use in the RED-stage batch. It separately proves the nonnominal full-function
carrier and supported identity using delivered foundations. The subsequent
`07FreshPredicates-red.log` fails on missing context/bundled interfaces before
production edits (maxErrors=1000 exposes all diagnostics). The green consumer
obtains a relation fact at a fresh atom using only an individual certificate,
and combines that fact with extra finite avoidance in the proved nonnominal
identity carrier. It checks arbitrary-action fresh projection, finite Bool
projection of bottom to top, higher-order coercions and generic signatures.

`08Boundaries.lean` proves every requested obstruction through the public root:
the infinite/coinfinite Bool-flag atom predicate; unsupported external union of
supported singletons; failed fresh existential/universal interchange despite
jointly invariant equality/disequality; finite nonempty Bool-index failure;
finite-atom/empty-index failure; failures of stronger Boolean laws without
decisions and of Iff with only one supported operand; an empty-supported,
witnessed but noncofinite predicate on Discrete Nat Bool × Nat; a finitely
supported global fresh-selector obstruction with no Infinite premise; and
fixed-atom support without invariance. Ordinary classical fresh choice remains
legal and is separately proved unsupported. All supplied/enlarged/avoiding
positive consumers retain actual predicate facts in their conclusions.

`phase-01c-public-names.json` inventories 58 public declarations (42 from Task 6,
16 from Task 7). `Phase01cSignatures.lean` checks all of them; the three new
consumers assign generic contracts and print representative axioms, including
the selector obstruction and joint fresh projection. No public statement or
hypothesis deviated from the approved plan. No mathematical rulings or deferred
findings were introduced. This is the phase acceptance check, not Task 8's
independent review of the whole PKG-01 change.

Actual final commands/results are in `phase-01c-final-validation.json`, all
fourteen commands exit 0:

- `lake build Package +Package.Tests.AxiomAudit` — 1017 jobs. The final run
  freshly compiled the audit with cached project/dependency artifacts.
  Iterative affected-module/root builds freshly compiled the new code using
  cached dependencies (`task-7-build-2.log`, 1016 jobs; FreshQuantifier context
  additions built in `task-7-build-1.log`). No clean dependency bootstrap claimed.
- `lake env lean` on each of `01Logic.lean`, `02Carrier.lean`,
  `03Quantifiers.lean`, `04Descent.lean`, `05SupportedDescent.lean`,
  `06Fresh.lean`, `07FreshPredicates.lean`, `08Boundaries.lean` and
  `Phase01cSignatures.lean` in that evidence directory — fresh elaborations,
  no errors/warnings/admission dependencies. The five earlier sources and logs
  remain byte-identical; their new run logs have the phase-01c-final prefix.
- `lake env lean Package/Tests/AxiomAudit.lean` — fresh direct audit of 995
  declarations in 21 defining modules; only propext, Classical.choice and
  Quot.sound. The representative prints and full traversal policy are unchanged;
  Task 8 still owns extending the representative production prints.
- `python3 Package/Scripts/check-imports.py` — all 22 production sources
  (including the public root) and the separate audit reached. The ordinary
  FreshQuantifier Package import closure separately contains no SupportedPred module.
- `git diff --check` — clean; final preservation additionally checks the index,
  whitespace in new untracked files and changed Markdown link targets.
- From docs/article, `latexmk -pdf -interaction=nonstopmode -halt-on-error
  -outdir=/tmp/nominal-package-pkg01-execution.WReW3a/phase-01c-final-article-build main.tex`
  — fresh external output, 42-page PDF. Final engine log has no warnings,
  unresolved references or overfull/underfull boxes. The 41-page Task 6 checkpoint
  also had a clean final engine log. Initial multipass reference warnings resolved.

Resolved Task 7 diagnostics remain in their original logs: the bundled action
proof needed an explicit reindexed predicate and parenthesized inverse;
Bool-flag consumers needed explicit atom-domain annotations (the atom argument
of FinitelySupportedPred deliberately does not select the predicate domain);
the fixed-atom contradiction needed Nat.one_ne_zero. Final proofs are complete
and have only standard axioms. No diagnostic is suppressed.

The article now states contextual Some/Any, individual predicate-object
freshness, bundled projection and its bound, all distinct Boolean hypotheses,
three uniform-support interchanges, finite/empty behavior, and the proved
carrier/selector boundaries. Only its cofinite subsection changed in this phase;
no operational metadata entered the manuscript. Current README, specification,
plan, research summaries and active roadmap describe the actual delivery.

Preservation is certified by `phase-01c-check-preservation.py`,
`phase-01c-preservation.log`, `phase-01c-initial-snapshot.json`,
`phase-01c-final-snapshot.json`, `phase-01c-baseline/` and `phase-01c-only.diff`.
147 of 156 starting repository files are byte-identical; nine intentional public
export/interface/article/status documents changed and two foundation modules
are new. Every Task 1–5 production file and all research probes are unchanged.
All 693 earlier evidence files are preserved, with the shared ledger's exact
original prefix; the Task 6 code checkpoint is unchanged apart from Task 7's
appended adapters. Reference library, historical roadmap, dependencies, staged
index, branch and HEAD are unchanged. Branch: fasapa/nominal-package; HEAD:
3c9d8dc527f7705b24c0308a2527e659ae933874; index SHA-256:
462fdfad827bcfebf9cf0239d1c5d0917226206646acc3270bd8892ffcd3a8ba.
No commits, worktrees, branch changes, pushes, merges, publication, dependency
upgrades or CI edits. No reference rebuild or checker self-test was needed;
the unchanged reference/checker sources and their prior evidence are preserved.

`phase-01c-acceptance.md` maps the combined criteria to actual consumers.
`Task8-handoff.txt` is the copyable fresh-context prompt, also retained below in
the plan. Reuse Tasks 1–7 and complete Task 8 before claiming PKG-01 complete.

### 2026-10-08 — Task 8 complete: public integration and independent final review

**Task 8 and PKG-01 are complete, uncommitted. All three phases, whole-specification
acceptance and the independent whole-change review pass.**
Only Task 8 is authorized in this run. Tasks 1–7 are reused without production
proof changes. Later PKG tasks remain outside this delivery.

Evidence remains `/tmp/nominal-package-pkg01-execution.WReW3a/`.
All earlier evidence was present. Every phase-01c final repository hash matched
the current checkout at entry. `task-8-initial-snapshot.json`,
`task-8-initial.diff` and `task-8-baseline/` preserve the 158 repository files,
branch, HEAD, index and 926 earlier evidence files. The retained `progress.md`
was appended; its original prefix is unchanged.

Delivered integration:

- `09PublicSignatures.lean` contains 65 public-import consuming examples with
  autoImplicit false. Exact contracts check independent universes, simultaneous
  atom sorts on one carrier, explicit selected/canonical quotient actions,
  scalar-only and DivisionMonoid parents, empty/proved nonnominal carriers,
  absent unnecessary Nominal/Infinite/Nonempty/DecidableEq premises, named and
  literal evidence, certificate independence, computability and higher-order use.
  Overloaded Boolean operations are explicitly typed as SupportedPred. Scoped
  typed/untyped И is consumed outside the defining namespace. It passed first
  elaboration against the existing implementation; no export or proof repair
  was needed.
- `Package/Tests/AxiomAudit.lean` adds 43 representative prints across every
  predicate area. Module-origin traversal, standard-axiom whitelist, zero-count
  rejection and simulated disallowed-name rejection tests remain byte-identical.
  The negative-test strings are not active axioms. The inspection-only heartbeat
  budget was preserved; no mathematical checking or diagnostic option was relaxed.
- Package README now has complete ordinary-certificate, supported-value,
  action-free/supported descent and supplied-bound Some/Any examples. All eight
  Lean blocks, including the earlier function examples and a formerly schematic
  quotient-action fragment, were extracted to `READMEExamples.lean` and compiled
  together through Package with autoImplicit false. Names and hypothesis limits
  agree with the public interfaces.
- `task-8-acceptance.md` maps 46 whole-specification obligations to actual source
  and consuming evidence across all phases. Both earlier signature inventories
  are retained and rerun. All specified negative boundaries remain proved;
  unsupported ordinary predicates, quotient induction motives and classical
  choice remain legal.
- The manuscript title/abstract, section guide and correspondence paragraphs
  now include functions, supported predicate logic, quotient descent and
  Some/Any. Its central predicate mathematics remains unchanged after checking
  hypotheses and proofs against source. `task-8-literature-check.md` records
  the pinned primary comparisons; no new external formalization build is claimed.
  Operational metadata remains outside the manuscript.

Commands actually run, all final exits 0, with exact argument arrays, working
directories, elapsed times and full logs in `task-8-integrated-validation.json`
(18 commands) and `task-8-initial-validation.json`:

- `lake build Package +Package.Tests.AxiomAudit` — 1017 jobs. The first Task 8
  run freshly compiled the changed audit using cached production/dependency
  artifacts. The integrated run was cached. No fresh production rebuild or
  clean dependency bootstrap is claimed.
- `lake env lean` on each of `01Logic.lean`, `02Carrier.lean`,
  `03Quantifiers.lean`, `04Descent.lean`, `05SupportedDescent.lean`,
  `06Fresh.lean`, `07FreshPredicates.lean`, `08Boundaries.lean`,
  `09PublicSignatures.lean`, `Phase01bSignatures.lean`,
  `Phase01cSignatures.lean` and `READMEExamples.lean` in the evidence directory
  — twelve fresh elaborations against cached imports. The original eight
  consumer sources and earlier logs are unchanged.
- `lake env lean Package/Tests/AxiomAudit.lean` — fresh traversal of 995
  production declarations in 21 defining modules; only `propext`,
  `Classical.choice`, `Quot.sound`.
- `python3 Package/Scripts/check-imports.py` — all 22 production sources,
  including the root, and the separate audit reached. Ordinary FreshQuantifier
  and PredicateDescent import closures separately checked to exclude the
  bundled predicate modules. No checker change or self-test was necessary.
- `git diff --check` and `git diff --cached --check` — clean. Additional
  checks include whitespace in untracked delivery files and local Markdown
  target/fragment validation.
- From `docs/article`, `latexmk -pdf -interaction=nonstopmode -halt-on-error
  -outdir=/tmp/nominal-package-pkg01-execution.WReW3a/task-8-article main.tex`
  — fresh external output directory, 42-page PDF. Final engine log has no
  warnings, unresolved references or overfull/underfull boxes. Transient
  first-pass cross-reference messages in the driver log resolved normally.

No Lean consumer/audit errors or warnings remain. The sole failed Task 8 check
was the new external preservation helper initially expecting the later snapshot
schema in the earliest snapshot (`files` versus `hashes`). The original failure
log is retained; inspecting the original keys identified the cause, and the
schema adapter passed the complete preservation check. No source theorem or
acceptance test was changed to conceal a failure.

The pre-review preservation check passes: 145 of 158 repository files are
byte-identical, with thirteen intentional integration/documentation/audit edits;
no new repository files in Task 8. All 77 protected reference/probe/pin files
match the earliest and latest snapshots, and all 926 earlier evidence files are
preserved (ledger prefix checked separately). 321 local targets and 20 Markdown
fragments pass. Earlier plan task contracts and all historical plan/roadmap
execution records are unchanged. No production theorem file changed in Task 8.

Independent whole-change review was performed once to `gpt-6-astra` with
explicit `ultra` reasoning and a fresh context (`fork_turns: none`), read-only.
`task-8-review-package.md` includes the approved authority, Review Focus verbatim,
actual source/documentation, complete 33-file uncommitted diff/inventory,
all consumers/logs, preservation scope and ledger rulings. This includes all
seven untracked production modules; HEAD..HEAD is not used as the change range.
The technical review gate passes with no Critical or Important findings and no
correctness, missing acceptance, or hypothesis defect. The reviewer independently
reran all nine consumers, README extracts, direct audit and import checker.
Its one Minor finding, M1, was an obsolete active roadmap policy paragraph saying
Tasks 6–8 remained and authorization stopped before Task 6. Source inspection
confirmed it; the required final current-status reconciliation now identifies
Tasks 1–8 as complete and the stopping point after Task 8. This is a documentation
correction within the existing task, with no production fix or new test needed.
Historical work-log entries remain unchanged. No minor finding is deferred.
The full report/disposition is `task-8-independent-review.md`; all reviewer
scope exclusions are explicitly ruled on in `task-8-rulings.md`.

Workflow ruling: explicit current instructions override generic worktree,
commit, evidence-deletion and branch-finishing helpers. The authorized checkout
and external evidence are retained. The cost is the requested uncommitted,
external evidence state; no mathematical scope or contract was changed.

Branch remains `fasapa/nominal-package`; HEAD remains
`3c9d8dc527f7705b24c0308a2527e659ae933874`; index SHA-256 remains
`462fdfad827bcfebf9cf0239d1c5d0917226206646acc3270bd8892ffcd3a8ba`.
Reference code, historical roadmap, research probes, pinned dependencies and
CI remain unchanged. No commit, push, merge, publication, worktree or branch
operation was performed. Larger-client elaboration performance and future
binder/generator/case-study work remain outside this acceptance claim.

Final status reconciliation covers the plan's seven Task 8 checklist steps, the
active roadmap dashboard/policy/task contract, approved specification, current
research index/investigation/readiness/brief and Package README. It preserves
all earlier execution records and handoffs. Completion concerns only PKG-01;
PKG-F06 and later PKG tasks retain their previous status.

**Final closeout:** the same reviewer confirmed M1 resolved and the final completion
status consistent, with no remaining discrepancy. Only status/evidence documentation
changed after technical review; production, audit, manuscript and compiled consumer
sources are unchanged. `python3 /tmp/nominal-package-pkg01-execution.WReW3a/task-8-check-preservation.py final`
passes after reconciliation: 144 of 158 starting repository files byte-identical,
fourteen intentional integration/docs/audit changes, no new repository files in
Task 8, all 77 protected files and 926 earlier evidence files preserved, 322 local
links and 20 fragments valid. The final snapshot and Task-8-only diff are
`task-8-final-snapshot.json` and `task-8-final-only.diff`; full final inventory/diff
also include every untracked PKG-01 source. Branch, HEAD and index remain unchanged.
Task 8 and PKG-01 are complete, uncommitted. No later PKG task was started.
