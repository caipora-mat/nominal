# Nominal package roadmap

Last updated: 2026-10-06. Branch: `fasapa/nominal-package`.
Research baseline: `7fed53a2e5fc67379f86f085515e310e7c1fddb7`.
F01 assessment snapshot: `76966b1f2e44f594517442b6572e33abaa9038e0`.
Current inspected HEAD: `34a83358739ab962e2b9d2035a21d67b2a896071`, containing
the committed F03b implementation/article/design updates. F04a design started
on a clean working tree at that revision; its subsequent approved native
implementation, article and design/tracker updates are uncommitted.
F04b's written specification and native implementation plan are approved.
Its code, consumers, audit and article pass; independent final review is clean.
F04b changes are also uncommitted.
F02/F03a were committed in the preceding `3d2196a`.
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
review. F04c/F04d, F05/F06 and PKG-01 remain unimplemented.

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
| PKG-F04 | IN PROGRESS — F04a/F04b DONE; F04c/F04d TODO | PKG-F03; F04a → F04b → F04c/F04d | Finite support calculus, nominality/least support, canonical instances/freshness, canonical equivariant quotients |
| PKG-F05 | TODO | PKG-F04 | Minimal function-space and predicate-input interface |
| PKG-F06 | TODO | PKG-F04/F05 | Abstraction, concretion or equivalent certified binder-descent facility |
| PKG-01 | TODO | PKG-F04/F05 | Supported predicates, logical support and quotient-predicate descent |
| PKG-02 | TODO | PKG-F04; approved backend/grammar from PKG-F01 | Manual syntax-carrier certificate with constructor/action/support laws |
| PKG-03 | TODO | PKG-02 and PKG-F06 | Fresh term induction and supported iteration |
| PKG-04 | TODO | PKG-02/03 | Multiple/direct mutual categories and finite-context infrastructure |
| PKG-05 | TODO | PKG-01/03/04 | Datatype/function commands and a distinct primitive-recursion contract |
| PKG-06 | TODO | PKG-01/03/04; PKG-05 for command integration | Certified fresh judgment induction, inversion and generation |
| PKG-07 | TODO | PKG-05/06 | Complete generated lambda and FOL workflows |
| PKG-08 | TODO | PKG-07 and a scoped let specification | Lambda with let and expansion correctness |
| PKG-09 | TODO | PKG-07 and a residual-binding/transition specification | π-calculus case study |
| PKG-10 | TODO | PKG-07 and a positivity/semantic specification | μ-calculus case study |
| PKG-11 | IN PROGRESS — F02/F03a/F03b/F04a/F04b LaTeX exposition and evidence delivered | Alongside every task | Article, decision record and claim-to-Lean evidence ledger |

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

**Selected task; bounded phases.** F04a–F04d are slices of this existing stable
task ID, not replacements for PKG-F04. The author supplied the scope and ordering;
each slice still needs its concrete specification, implementation plan and
execution agreement. The full outline does not authorize a single combined
implementation. F02/F03a/F03b remain delivered and are not reopened.

| Slice | Status | Dependencies | Article section assigned to its spec/plan |
| --- | --- | --- | --- |
| F04a — Finite support calculus | DONE — verified working-tree delivery; clean final review | Delivered F03b and selected actions | `docs/article/sections/support.tex`, `sec:finite-support` |
| F04b — Nominality and least support | DONE — verified working-tree delivery; clean final review | F04a, especially finite intersection | `docs/article/sections/support.tex`, `sec:least-support` |
| F04c — Canonical instances and freshness | TODO | F04a/F04b; delivered canonical actions | `docs/article/sections/freshness.tex`, `sec:canonical-support` and `sec:freshness` |
| F04d — Canonical equivariant quotients | TODO | F03 actions; F04a support bounds; F04b nominality/least support | `docs/article/sections/quotients.tex`, `sec:equivariant-quotients` |

F04a and F04b's assigned article sections are written; F04c/F04d paths/labels remain
assigned future sections. F04d's action construction and support preservation need no infinitude;
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
Important or Minor issues. F04b is DONE; the work remains uncommitted.

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

- [ ] Supply nominality under the intended actions on atoms, `Discrete A X`,
  products and finite atom sets with the existing scoped image action.
- [ ] Prove exact support formulas, with their required hypotheses:
  `support a = {a}`, `support (Discrete.mk x) = ∅`,
  `support (x,y) = support x ∪ support y`, and `support (S : Finset A) = S`.
- [ ] Define atom freshness by nonmembership in least support; derive freshness
  from sufficient bounds, permutation transport and swaps fixing an element
  when both endpoints are fresh.
- [ ] Use Mathlib's infinite/finite-set results for avoiding finite bounds and
  combined nominal contexts, including nested products. No executable or
  finitely supported fresh-selector function is required.
- [ ] Retain the unordered-pair counterexample: swapping distinct a,b fixes
  `{a,b}` but moves both atoms of its least support. Do not infer nominality of
  arbitrary functions or bare permutations under their default actions.
- [ ] Deliver consumers, audits and both assigned LaTeX subsections together.

#### F04d — Canonical equivariant quotients

- [ ] Construct the canonical quotient action for a setoid preserved by the
  selected permutation action, keeping atom/carrier universes independent.
  Inspect and reuse `Quotient.map`, `Quotient.map_mk` and
  `Function.Surjective.mulAction` where suitable.
- [ ] Prove `π • q x = q (π • x)`, projection surjectivity and equivariance;
  preserve support bounds and inherit finite supportedness and nominality.
- [ ] Prove `support (q x) ⊆ support x` with the least-support hypotheses and
  include a meaningful quotient with strict decrease. An unrelated quotient
  action does not satisfy this canonical-projection contract.
- [ ] Deliver consumers, audit coverage and `sec:equivariant-quotients` together.
  Full predicate descent/support reflection remains PKG-01; exact intersection
  formulas over every representative's support are not required without a
  concrete dependency.

#### Overall F04 completion

- [ ] Prove or adopt finite support, least support and their transport/minimality
  laws, with each required atom hypothesis explicit.
- [ ] Establish fresh-atom existence, avoidance of finite combined contexts and
  the freshness/renaming laws consumed by the first workflow.
- [ ] Supply required product and equivariant-quotient actions/support results.
  State upper bounds separately from exact support formulas and prove any exact
  formula that is advertised.
- [ ] Validate fixed parameters, nested product avoidance and quotient descent;
  retain a counterexample separating least support from strong support.

Accept ordinary package clients that use the support and freshness conclusions,
plus reviewed quotient well-definedness. Fixing an element need not fix every
atom in its support pointwise. Add other containers only when a stated client
requires them; a complete core catalogue is not a prerequisite for PKG-01.
Mark PKG-F04 complete only when all four agreed slice contracts, their consumers,
audit obligations and concurrent LaTeX sections are delivered. Supported-function
objects, `SupportsMap`/`SupportsPred`, bundled predicates and Some/Any remain
F05/PKG-01; abstraction, FCB, recursion and generators remain later work.

### PKG-F05 — Minimal function-space and predicate-input interface

- [ ] Choose the least interface needed to express finitely supported maps or
  predicates: bundles, explicit support proofs, supported subsets, or another
  justified representation.
- [ ] Prove function conjugation/evaluation laws where function objects are
  used. Distinguish this action from ordinary pointwise function actions and
  preserve instance coherence, including empty-domain cases.
- [ ] Provide ordinary application and extensionality, support of evaluation,
  and fixed-parameter support bounds from joint equivariance. Add only the
  composition/partial-application adapters required by immediate clients.
- [ ] Specify coherent truth action when `Prop` is itself an acted-on carrier,
  or give the corresponding logical interface if predicates are represented
  without such an instance. Check atom parameters and universe inference.
- [ ] Reject automatic finite-support/equivariance claims for arbitrary ordinary
  functions, arbitrary globals and unsupported predicates. Consume a supported
  but non-equivariant fixed-parameter example successfully.

Accept a small representation-specific foundation that makes PKG-01 precise
and usable. A legacy `NFun` wrapper, a global nominal `Prop` instance, the old
macro and a full higher-order function library are not prerequisites. Broader
function ergonomics and automation belong to PKG-05 when clients require them.

### PKG-F06 — Binding, representatives and descent

- [ ] Specify and prove name abstraction with equality, support and fresh
  representatives, or an equivalent carrier-level binding facility with the
  same explicitly stated obligations.
- [ ] Provide concretion/reconstruction or the corresponding chosen-fresh
  representative interface; expose its freshness premises and computation laws.
- [ ] Establish the supported binder-descent principle needed by iteration:
  representative independence, scoped handler compatibility, existence,
  uniqueness and support/parameter bounds where claimed.
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

- [ ] Build supported predicates on the selected F04/F05 interfaces, with
  extensional equality and proved correspondence to supported subsets or
  function objects where the chosen representation warrants it.
- [ ] Prove the raw/quotient `Prop` bridge under the exact descent hypothesis;
  distinguish alpha compatibility, finite support and equivariance.
- [ ] Supply logical support, parameter/evaluation and Some/Any interfaces,
  keeping finite-support premises explicit.
- [ ] Retain unsupported-predicate and fresh-selector counterexamples, and
  check any explicit truth-action/atom-instance choices at the public boundary.
- [ ] Demonstrate arbitrary-motive consumers that need no predicate support
  certificate; supported logical tools must not narrow future induction motives.

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

Accept a manual certificate for actual constructors, not merely an interpreted
arity or an arbitrary type equivalence. If initiality is claimed, specify and
prove the structure map, map class, commuting equations and uniqueness. The
old lambda carrier is reference evidence; its representation need not be reused.

### PKG-03 — Fresh induction and supported iteration

- [ ] Prove arbitrary-motive induction with context-generalized recursive
  hypotheses, including avoidance enlarged under nested binders.
- [ ] Use the proved F06 facility to establish supported iteration, including
  scoped binder compatibility, totality and uniqueness.
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
- [ ] Prove a distinct primitive recursor and a consumer using both original
  children and recursive results, with its advertised support/uniqueness laws.
- [ ] Expose unsolved support, binder-descent, coverage and termination
  obligations. Failed commands must not leave a partial public package.

Accept generated substitution, higher-order use, `rw`/`simp`/`ext`, shadowing,
nested scopes and meaningful failure diagnostics. Arbitrary globals must not
silently acquire equivariance certificates. Split recursor and elaborator work
into separate increments as needed. Do not advertise iteration as primitive
recursion or promise unrestricted dependent elimination. The old `nfun` macro
and `NFun` packaging are not required parts of the command implementation.

### PKG-06 — Judgment contracts and generation

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
   and independent final review. The remaining order is F04c/F04d, then F05
   before PKG-01; those slices retain their own design and approval boundaries.
   The [approved F03b specification](superpowers/specs/2026-10-05-package-controlled-swaps-design.md)
   and [native plan](superpowers/plans/2026-10-05-package-controlled-swaps.md)
   supply its bounded contract. The swap criterion supplies permutation input;
   it does not implement support or prove least support.
3. Settle syntax/backend, direct-mutual, finite-context and binder-descent choices
   at their own tasks. Later π/μ semantics remain separate decisions.

The actual F04a inspection began with a clean tree at `34a8335`. Earlier logs
retain the working-tree status at their own inspections. Current F04a implementation,
article and design/tracker changes are approved working-tree work, uncommitted.
Persistent usage examples belong to future case studies. The current
Package audit covers production declarations directly; the reference examples
remain unchanged. The candidate direct SPred interface is still a proposal and
requires no complete general supported-function library as a hidden prerequisite.

## Research artifacts

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
