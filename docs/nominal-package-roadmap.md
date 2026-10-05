# Nominal package roadmap

Last updated: 2026-10-05. Branch: `fasapa/nominal-package`.
Research baseline: `7fed53a2e5fc67379f86f085515e310e7c1fddb7`.
Current F01 assessment: `76966b1f2e44f594517442b6572e33abaa9038e0`, with
uncommitted research/design artifacts linked below.
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
only for delivered results. F02 and F03a now have working-tree implementation,
verification evidence and a clean independent final review. F01 remains open
for later per-layer choices.
F03b, F04–F06 and PKG-01 remain unimplemented.

Distinguish user decisions, integrated theorems, standalone probes, source
readings, mathematical analyses and proposed interfaces. Record revision and
working-tree state, commands actually run, cache conditions, limitations and
counterexamples. Scratch proofs do not complete an integration task. The old
library's build and axiom audit do not cover a new `Package` target.

**Every substantive implementation increment also delivers its article update.**
Write the corresponding mathematics in LaTeX under `docs/article/` while
developing the Package code. Before marking an increment DONE, check its Lean
results and the relevant manuscript statements/proofs, declaration references
and verification limits together, and compile the updated article. PKG-11
coordinates this ongoing work; it is not a final writing phase after the code.
Research proposals may appear in the article before implementation only with
their unverified status explicit. Publication polish is not required to complete
an increment, but an accurate, current exposition is.

## Dashboard and dependency order

| ID | Status | Dependencies | Deliverable |
| --- | --- | --- | --- |
| PKG-00 | DONE — historical research proposal; revised design pending | Completed core/Church–Rosser as research evidence | Architecture comparison, contracts, probes and article outline |
| PKG-F01 | IN PROGRESS — first foundation spec approved; later layer choices remain proposed | Current user decisions; PKG-00 evidence; pinned algebraic source | Algebraic-sketch investigation, foundation/API contract and per-layer adoption/adaptation/reconstruction decisions |
| PKG-F02 | DONE — verified working-tree delivery | Approved F01 boundary for F02/F03a; approved native plan | `Package/` root, Lake/import boundary and production audit coverage |
| PKG-F03 | IN PROGRESS — F03a implemented; F03b remains open | Approved F01 boundary; F02 | Atoms, finite permutations, actions and equivariance |
| PKG-F04 | TODO | PKG-F03 | Finite/least support, freshness and required products/quotients |
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
| PKG-11 | IN PROGRESS — F02/F03a LaTeX exposition and evidence delivered | Alongside every task | Article, decision record and claim-to-Lean evidence ledger |

The implementation dependency spine is
`F01 → F02 → F03a → F03b → F04 → F05 → PKG-01`, with concurrent
LaTeX work tracked under PKG-11 at each step. F02/F03a are delivered; F03b is
the next bounded design/implementation slice. These steps can be small where reviewed
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
- [ ] Prove the remaining permutation laws needed for the selected support
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
**F03b** retains the remaining support-facing permutation obligations, such as
swap generation/characterization prerequisites or a reviewed equivalent proof
route. These are slices of PKG-F03. The implemented F03a slice alone cannot mark
PKG-F03 DONE. Its public-import compatibility and action distinctions were
checked in temporary files; persistent usage examples are deferred to case studies.

#### F03b — Proposed next contract: swaps preserving an avoidance set

- [ ] Investigate Mathlib's permutation factorization/induction and finite-set
  results before writing a new proof. Check whether they provide the required
  control over endpoints directly or through a small specialization/adapter.
- [ ] Prove that each finite permutation is a finite product of swaps whose
  distinct endpoints lie in that permutation's moved set, or give an equivalent
  induction principle with the same control over endpoints.
- [ ] Derive the avoidance consequence: if the permutation fixes a set S
  pointwise, the factorization uses swaps with both endpoints outside S.
- [ ] Consume the result through `import Package`: for an arbitrary selected
  `MulAction (Perm A) X`, invariance of x under all swaps outside S implies
  invariance under every finite permutation fixing S pointwise.
- [ ] Cover identity/empty factorization and finite atom carriers; no
  `Infinite A` hypothesis is needed for this factorization. Use temporary
  public-import checks, preserving the author's case-study-only examples policy.
- [ ] Extend `docs/article/sections/foundations.tex` concurrently with the
  factorization statement, proof strategy and avoidance corollary. At delivery,
  connect them to the actual declarations and verification evidence and compile LaTeX.

Review the exact statement/proof route before implementation. An unrestricted
swap-generation theorem alone does not state the required avoidance guarantee.
F03a already supplies group/action and basic swap laws; F03b does not introduce
support predicates, least support, freshness or atom selection. Those belong to
F04. Completion requires the scoped permutation result, consuming verification,
production/audit coverage and the accompanying article update.

### PKG-F04 — Support, freshness and required constructions

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
  and recorded verification for that delivered slice.
- [ ] Maintain a per-layer decision record, including discarded reuse/rebuild
  choices, counterexamples and their effect on dependencies.
- [ ] Create and maintain the statement-to-Lean claim ledger as increments land,
  distinguishing legacy evidence from new `Package` results.
- [ ] For every implementation increment, assign the relevant LaTeX sections
  in its spec/plan and develop their statements and mathematical explanations
  together with the Lean proofs; do not accumulate writing for a final phase.
- [ ] Before closing each increment, synchronize theorem hypotheses, source
  references, proof status and limitations, review both artifacts and compile
  the article. Record the command/result with that increment's code verification.
- [ ] Preserve exact source versions, failed approaches and verification limits;
  review consistency among claims, contracts and implementation at each milestone.

Follow the [article plan](research/2026-10-05-article-plan.md). Neither the old
proposal nor this rewritten plan establishes novelty, publication readiness or
successful external builds.

The author now requires the article entirely in LaTeX under `docs/article/`,
written alongside implementation. The [initial manuscript](article/main.tex)
contains introduction and permutation/action sections with mathematical proofs,
actual F02/F03a declaration references and verification evidence. Later support,
predicate and binder results remain prospective. This supersedes the earlier
Markdown-first suggestion; the article's mathematical content and implementation
correspondence must advance with each new slice.

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

1. F02 + F03a passed independent final review and is delivered in the working
   tree. The [native plan](superpowers/plans/2026-10-05-package-foundation-kernel.md)
   records completion and the author's removal of standalone Package examples.
2. Review and implement the bounded F03b contract above: endpoint-controlled
   swap generation and the avoidance corollary, with its concurrent LaTeX
   section. Then proceed to F04/F05 before PKG-01. The present subgroup/action
   laws do not prove least support.
3. Settle syntax/backend, direct-mutual, finite-context and binder-descent choices
   at their own tasks. Later π/μ semantics remain separate decisions.

The implementation and accompanying LaTeX article are uncommitted working-tree
changes. Persistent usage examples belong to future case studies. The current
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
