# Nominal package roadmap

Last updated: 2026-10-05. Branch: `fasapa/nominal-package`.
Research baseline: `7fed53a2e5fc67379f86f085515e310e7c1fddb7`.
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
Revising the roadmap does not authorize package implementation. The concrete
foundation specifications and implementation increments below await agreement.

## Objective and architectural freedom

Researchers should be able to declare first-order syntax with binders,
operations and ordinary Lean `Prop` judgments, then prove results through
generated nominal interfaces. Every generated mathematical guarantee must be
justified by proofs checked by Lean's kernel.

- Use classical Lean/Mathlib, actual quotients and least supports. Noncomputable
  semantic operations are acceptable; executable fresh-name generation is not
  a requirement.
- Expose mathematical freshness and explicit induction avoidance. Hide support
  certificates and representation details where proved automation suffices,
  with ordinary Lean proof escape hatches when it does not.
- Initially target one atom sort, single/nested binders and multiple syntax
  categories. Specify universes, mutual recursion and container shapes rather
  than inheriting them accidentally from a prototype.
- Preserve arbitrary-predicate fresh term and rule induction. Supported
  predicates supply complementary tools; they do not restrict every motive.
- For each required layer, choose adoption, adaptation or reconstruction on
  mathematical and engineering evidence. Everything needed may be rebuilt from
  scratch. Rebuilding everything is permitted, not required.
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
only for delivered results. All implementation tasks below are TODO; the proposed
foundation contracts do not claim an existing `Package` implementation.

Distinguish user decisions, integrated theorems, standalone probes, source
readings, mathematical analyses and proposed interfaces. Record revision and
working-tree state, commands actually run, cache conditions, limitations and
counterexamples. Scratch proofs do not complete an integration task. The old
library's build and axiom audit do not cover a new `Package` target.

## Dashboard and dependency order

| ID | Status | Dependencies | Deliverable |
| --- | --- | --- | --- |
| PKG-00 | DONE — historical research proposal; revised design pending | Completed core/Church–Rosser as research evidence | Architecture comparison, contracts, probes and article outline |
| PKG-F01 | TODO — proposed next design increment | Current user decisions; PKG-00 evidence; pinned algebraic source | Algebraic-sketch investigation, foundation/API contract and per-layer adoption/adaptation/reconstruction decisions |
| PKG-F02 | TODO — proposed implementation prerequisite | PKG-F01 and bounded implementation agreement | `Package/` root, Lake/import boundary, example and audit coverage |
| PKG-F03 | TODO | PKG-F01/F02 | Atoms, finite permutations, actions and equivariance |
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
| PKG-11 | IN PROGRESS — outline delivered | Alongside every task | Article, decision record and claim-to-Lean evidence ledger |

The implementation dependency spine is
`F01 → F02 → F03 → F04 → F05 → PKG-01`. These steps can be small where reviewed
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

Each implementation increment gets a bounded specification and plan. The next
step is the F01 contract review, followed by the approved foundation increment;
PKG-01 is no longer assumed to be the first implementation task.

## Foundation task contracts

### PKG-F01 — Algebraic-sketch investigation and foundation contract

- [ ] Inspect the actual algebraic sketch at
  `983adeb9b80f75fb7c77c05acfd2fcef16db1d46`, the previously reviewed
  `origin/fasapa/algebraic` snapshot. Read both `Nominal/Set/Algebraic.lean` and
  `Nominal/Set/Structural.lean` from Git, without switching branches or merging.
- [ ] Check the [existing assessment](research/2026-10-05-backend-comparison.md#reassessment-of-the-historical-branch)
  against those declarations. Distinguish false statements, statements weaker
  than their advertised contract, missing proofs, and elaboration/representation
  obstacles. Reuse verified evidence where applicable; reproduce decisive
  counterexamples or bounded probes when the new design relies on their claims.
- [ ] Investigate useful ideas independently of their current implementations:
  binding signatures, functor maps, algebra morphisms, predicate lifting,
  initiality, supported recursion and abstraction descent. Identify which ideas
  help the lambda/FOL workflow and what corrected contracts or new proofs they need.
- [ ] Inventory only the layers needed for the first lambda/FOL workflow:
  atoms/permutations/actions, support/freshness, products/quotients, function and
  predicate inputs, binder descent, syntax carriers, recursion and rule transport.
- [ ] For each layer, compare adoption, adaptation and reconstruction. Record
  the selected boundary, dependency costs, required proofs and why it serves
  the clients; retain unresolved choices explicitly. Include the algebraic
  sketch's usable ideas and rejected approaches in this comparison, without
  giving that sketch or the completed core architectural priority.
- [ ] Specify atom assumptions, universes, action-instance coherence, function
  conjugation, truth/predicate representation, equality/extensionality and the
  treatment of fixed nominal parameters.
- [ ] Record a candidate syntax grammar and client assumptions to test the
  foundation choices. Settle only the scope/universe decisions that affect the
  next increment; later command details and π/μ semantics need not be fixed.
  Compare backends without requiring the former staged-hybrid recommendation
  or compatibility with legacy APIs.
- [ ] Design ordinary application, useful equations, proof escape hatches and
  consuming validation examples before naming the internal wrappers.
- [ ] Agree a bounded first implementation specification and its verification
  coverage, including which existing dependencies, if any, it will adopt.

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

- [ ] Establish top-level `Package/` as the location of new implementation,
  with a public import root and explicit internal/public module boundaries.
- [ ] Add the minimal Lake/root-file configuration for a separately identifiable
  package target. Specify whether a conventional root umbrella such as
  `Package.lean` is required; do not scatter implementation outside `Package/`.
- [ ] Put new package examples/regressions and axiom-audit code under `Package/`
  and make their import/build coverage explicit, including generated declarations.
- [ ] Define an import policy for any adopted legacy dependencies and a check
  that `Nominal/` and its manual clients remain preserved.
- [ ] Document commands that actually reach the new target, its examples and
  audit; retain the pinned toolchain and dependencies.

Accept a minimal compiling package boundary, a consuming import example and
verified coverage reports. An empty target is setup evidence only, not proof of
any foundation theorem. These are future implementation/configuration changes;
this roadmap revision creates no directory, target, root module or Lean example.

### PKG-F03 — Atoms, permutations, actions and equivariance

- [ ] Supply the selected infinite-atom interface and the finite-permutation
  group, including swaps and the laws required by subsequent support proofs.
- [ ] Prove or review adopted action laws, equivariance and canonical actions
  on atoms and the initial data shapes; document universe and instance choices.
- [ ] Provide public application/composition/renaming equations sufficient for
  consuming proofs without unfolding representation internals.
- [ ] Test action composition/inverses and instance coherence, including any
  permutation conjugation and discrete-data actions used by the design.

Accept proved foundations or an explicitly justified adopted dependency, with
package-boundary consumers and standard axioms only. Do not assume atom
countability or a particular concrete atom encoding unless the reviewed contract
requires it. No support or fresh-name theorem follows from group laws alone.

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
- [ ] Maintain a per-layer decision record, including discarded reuse/rebuild
  choices, counterexamples and their effect on dependencies.
- [ ] Create and maintain the statement-to-Lean claim ledger as increments land,
  distinguishing legacy evidence from new `Package` results.
- [ ] Develop article sections alongside proofs and user-level examples.
- [ ] Preserve exact source versions, failed approaches and verification limits;
  review consistency among claims, contracts and implementation at each milestone.

Follow the [article plan](research/2026-10-05-article-plan.md). Neither the old
proposal nor this rewritten plan establishes novelty, publication readiness or
successful external builds.

## Validation of future implementation

Each delivered increment must identify its public declarations, their exact
theorem statements and the consumers that exercise them. Validate adopted
dependencies at the same boundary as newly proved foundations. Positive examples
must use generated facts in meaningful conclusions; negative tests must check
the intended unsupported case or diagnostic.

PKG-F02 must establish actual new-target commands before they are reported as
passing. The intended coverage includes the package library, its persistent
examples, generated declarations and a module-based axiom audit. Do not assume
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

Documentation-only updates require link/content and whitespace checks, not a
Lean rebuild. A successful document check is never package proof evidence.

## Open decisions and next step

1. Review PKG-F01's source-based algebraic-sketch investigation, foundation/API
   contract, per-layer dependency choices and candidate backend. The permission
   to rebuild and the `Package/` location are
   settled; the particular implementation is not.
2. Agree the bounded first foundation increment and its Package build/audit
   setup. Complete or discharge F03–F05 against that contract before starting
   PKG-01; assess F06 separately for later binder/recursion work.
3. Settle the grammar, direct-mutual gate, universe policy and finite-context
   representation at the tasks that depend on them.
4. Select π transition semantics and the μ variant before those later studies;
   these decisions do not block the first lambda/FOL workflow.

The current work is a roadmap/research-policy revision. No implementation
increment is approved by this document, and no package production code or Lake
configuration is changed by it.

## Research artifacts

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
