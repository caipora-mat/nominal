# Nominal package research brief

These notes record the agreed research direction and unresolved questions for a
Lean package for reasoning about languages with binders. They are a requirements
and decision record, not an approved implementation architecture or a claim that
the package already exists. Update them as the discussion develops; preserve
superseded choices with their reasons rather than silently rewriting history.

Date: 2026-10-05.
Research branch: `fasapa/nominal-package`.
Starting commit: `4279ba92efacd77b3b96e507631502272b489999` on `fasapa/next`.

Current policy includes the author's later decisions **R11** (all infrastructure
may be reimplemented) and **R12** (new implementation lives in top-level
`Package/`). See the [research guide](README.md). These decisions supersede
earlier reuse-first wording; the source evidence retains its original baseline.

The branch was created at that commit with the existing working tree preserved.
It includes pre-existing modified README content and untracked instructions,
documentation, examples and validation scripts. Those files are not all part of
the starting commit. No implementation change or new build verification was made
while creating this brief.

## Research objective

Develop a nominal package for Lean inspired by Isabelle Nominal. A researcher
should be able to declare a language with binders, define operations and
judgments, and prove results using tools resembling ordinary mathematical
practice. The internal account must be grounded in nominal theory, with generated
proofs checked by Lean's kernel.

The completed lambda-calculus Church–Rosser development provides experience,
proved examples and a reference case study. Reusing its code is optional. The target is a specified general
class of first-order languages with binders, not a generator specialized to
lambda calculus. Here “first-order languages” describes the languages studied by
package users; it does not settle the package's internal term representation.

## Agreed decisions

### R1 Classical foundations

Use classical Lean and Mathlib fully, including choice, noncomputable definitions,
and quotients. Executable fresh-name generation, substitution, or extracted
programs are not requirements. Mathematical correctness and useful theorem-level
equations take priority over execution. Noncomputability does not remove the
need to justify totality or well-definedness of the operations being specified.

### R2 User visible mathematical concepts

Users may write familiar freshness/free-variable conditions and request
induction avoiding selected parameters. Hide permutations, support certificates,
quotient representatives, NFun packaging, and FCB obligations wherever automation
can justify them. The goal is a natural proof interface, with explicit control
over mathematical freshness rather than compulsory exposure to its implementation.

The behavior when automation cannot discharge an obligation still needs design:
the language-level diagnostic, manual proof interface, and expert escape hatch
must be specified rather than assuming every definition is admissible.

### R3 A complete first workflow

The first package milestone must include user-declared syntax, functions and
judgments, generated term and rule induction/recursion facilities, and meaningful
proofs using them. A syntax-only generator is insufficient as the milestone's
completion criterion, although smaller implementation increments are expected.

Lambda calculus and replaying Church–Rosser through the package are required
case-study targets. The selected second workflow is first-order logic with
substitution admissibility; R10 records the full five-study portfolio. The
earlier brief left this second example open; that choice has since been resolved.

### R4 Initial binding scope

One atom sort, single binders and nested binders. Allow multiple syntactic
categories, such as terms and formulas. Multiple syntactic categories do not
imply multiple atom sorts. Mutual recursion, recursive container shapes and the
precise signature grammar still need explicit specification.

Simultaneous/generalized/pattern binding and additional atom sorts are outside
the initial scope. Their eventual role should be considered when assessing
extension boundaries, without making them first-milestone requirements.

### R5 Dedicated commands or DSL

Prefer dedicated nominal language-definition commands implemented through Lean
metaprogramming, with sufficient control to hide the implementation and generate
the required theory. Conceptual examples include a nominal datatype/inductive
command and a nominal function-definition command. Exact spelling, grammar,
binding annotations, and how closely the syntax resembles ordinary Lean are
open. Generated public declarations should remain usable in ordinary Lean proofs.

This settles the user-facing direction; it does not decide whether the backend
interprets a generic signature, generates a separate construction for each
declaration, or combines these approaches.

### R6 Nominal justification without a prescribed implementation

Investigate the role of supported functions, name abstraction, concretion, FCB,
fresh quantification, nominal predicates/propositions, and fresh induction and
recursion in the generated package. Compare existing results with independently
designed alternatives. The original recommendation to reuse and extend the
existing implementation is superseded by R11: any necessary layer may be rebuilt,
and mathematical concepts do not mandate the current Lean encodings. The author
clarified that predicates and judgments should
primarily inhabit ordinary Lean `Prop`; a separately interpreted formula logic
is not the current objective. The underlying nominal-predicate theory still
requires detailed research, as recorded in R9 below.

The old `origin/fasapa/algebraic` sketch is research input, not an established
foundation to merge wholesale. Its statements and feasibility require reassessment
against the [historical review](../reviews/2026-10-02-development-review.md)
and the current core. Whether generic nominal terms are needed internally is an
open architectural question. The excluded syntax/unification branch has not been
added to the scope.

### R7 Research documentation is part of the work

Record consequential mathematical, architectural and user-interface decisions
as research notes, including alternatives, reasons, dependencies and evidence.
Record obstacles, counterexamples, unsuccessful approaches and remaining proof
obligations as well as successful results. Separate conjectures, source-reviewed
claims, scratch experiments and integrated verified results.

Plan for an evolving mathematical article describing the package, uses, theory,
difficulties and limitations. Publication venue and manuscript organization remain
open. Do not claim novelty, equivalence of architectures, or generality without
supporting evidence. The future brainstorming prompt must require both an
architectural roadmap and a sustainable research-writing workflow.

### R8 Preserve the completed development

Develop this research on the new branch and preserve the completed core and
Church–Rosser case study as a reference. Preserve existing dirty work. The earlier
preferences for no deadline, correctness first, and no CI remain in force unless
the author changes them. Keep the reference source available while developing
new representations independently under `Package/`; no backward compatibility
with old APIs is required. This does not authorize overwriting the reference
library or merging the old algebraic sketch.

### R9 Investigate propositions before selecting the architecture

Compare Pitts' finitely supported predicates and logical operations, the current
quotient-based arbitrary-predicate induction, Isabelle's treatment of predicates,
and Copello's alpha-compatible predicates. These may provide complementary
layers; do not force them into a mutually exclusive choice in advance.

The author's constructive Rocq experience with setoids and `Prop` is a research
motivation. Identify exactly which assumptions and representations produced each
limitation, and which transfer to classical Lean. Separate proof elimination,
extensional equality, quotient descent, finite support, equivariance and
metaprogram inspection. Preserve arbitrary-motive induction as a mathematical
goal without requiring the new package to retain current API names, signatures
or implementation. Do not require all user motives to be finitely supported.

The [initial propositions investigation](2026-10-05-propositions-and-induction.md)
records checked sources, scratch evidence and unresolved work. It does not choose
a public predicate representation. New proofs are required for a redesigned
theory even when the old implementation establishes an analogous statement.

## Primary reference observations

Isabelle Nominal2 exposes dedicated `nominal_datatype`, `nominal_function` and
`nominal_inductive` commands. Its implementation separates datatype metadata,
raw functions, alpha relations and quotient construction; this is a precedent
to investigate, not proof that Lean must use the same architecture.
[Nominal2 command and implementation entry point](https://isa-afp.org/browser_info/current/AFP/Incompleteness/Nominal2.Nominal2.html).

The AFP description identifies alpha-equated datatypes, structural function
definitions and induction principles incorporating the variable convention as
package capabilities. These motivate the comparison criteria for the Lean
project. [Nominal2 AFP entry](https://www.isa-afp.org/entries/Nominal2.html).

These pages were consulted on 2026-10-05. A full reference investigation should
pin source versions, distinguish original Isabelle Nominal from Nominal2, and
read the relevant implementation and mathematical papers before borrowing
architectural claims. The local [Pitts book](../../ref/nominalsets.pdf) and the
existing [research correspondence](../research-correspondence.md) remain relevant.

## Questions for the architecture investigation

- What is the precise accepted signature grammar, including multiple categories,
  mutual recursion, containers and external nominal parameters?
- Is a generic nominal-syntax carrier necessary, helpful, or avoidable? Compare
  a generic interpreted construction, proof-producing per-declaration generation,
  and a hybrid. Keep positivity and canonical action coherence explicit.
- Which facilities must the datatype, function and judgment commands generate,
  and which mathematical obligations can they soundly automate?
- How should supported fixed-parameter functions and higher-order use interact
  with ordinary Lean functions and rewriting?
- What does the nominal-proposition interface mean, and how does it preserve
  arbitrary-predicate induction without imposing unjustified support assumptions?
- What distinguishes supported iteration, primitive recursion and dependent
  elimination in the promised user contract?
- What generic conditions justify fresh induction for user-defined judgments?
- What happens when an attempted definition is not alpha-compatible, not finitely
  supported, outside the binding grammar, or beyond available automation?
- Which additional demands do the five selected studies place on the candidate
  foundation, beyond the completed reference lambda example?
- How should the research journal, mathematical exposition, implementation plan,
  experiments and current roadmap refer to one another without duplicating claims?

The representation, backend and command-grammar questions remain unresolved.
The architecture comparison and roadmap below record the research already
delivered; their recommendations must now be assessed under R11/R12 rather
than treated as commitments to the old core.

## 2026-10-05 architectural investigation: decisions and review artifact

The sections above express the current requirements, with superseded reuse and
case-study choices identified explicitly. The original source investigation was
performed before R11/R12; its evidence is retained below.
The requested investigation is now recorded in the
[architecture and roadmap proposal](2026-10-05-package-architecture.md), with
separate [predicate foundations](2026-10-05-predicate-foundations.md),
[Isabelle comparison](2026-10-05-isabelle-comparison.md),
[backend comparison](2026-10-05-backend-comparison.md),
[client contracts and proposed syntax](2026-10-05-package-contracts.md), and
[article/notes plan](2026-10-05-article-plan.md). These are research artifacts
for review; no backend selection or package implementation is approved by them.

At the author's subsequent request, the new phase is tracked in a dedicated
[nominal-package roadmap](../nominal-package-roadmap.md). The preceding library
roadmap retains its original first-deliverable history and is not reused as
the package tracker.

### R10 Agreed case-study portfolio

The author explicitly retained lambda calculus as a case study and selected
first-order logic with substitution admissibility as the second workflow. The
author then selected all five of the following studies, finally choosing lambda
with let over the alternative imperative-local language:

1. Lambda calculus, including the generated-interface Church–Rosser replay.
2. First-order logic, including substitution admissibility for a small
   natural-deduction judgment with eigenvariables.
3. Lambda calculus extended with nonrecursive `let`; its binder scopes only
   over the body. Let-expansion correctness is the proposed theorem target.
4. π-calculus; precise transition convention and theorem remain to be selected.
5. μ-calculus; positive modal μ-calculus is the proposed variant, not yet an
   author-selected semantic specification.

This supersedes R3's statement that the second example has not been chosen.
The proposed case-study delivery order is the complete lambda/FOL workflow first, then
let, π and μ as explicit later milestones. All five remain part of the research
program; no proof or implementation of the later studies is claimed.

### R11 Architectural freedom: existing infrastructure is optional

The author clarified that the entire new infrastructure may be developed from
scratch. Atoms, permutations, actions, support, freshness, supported functions,
predicates, abstraction, quotients, induction, recursion and metaprogramming are
all open to a new implementation. Existing APIs, typeclasses, module boundaries,
universe restrictions, seals and proof strategies are not requirements.

Use the existing development as learning material: proved mathematics, realistic
clients, negative results and engineering experience. Compare reuse, adaptation
and replacement on their merits; neither importing old code nor rewriting it
all is obligatory. Backward compatibility is not an acceptance criterion.

Preserve source/evidence and the intended mathematical theorem strengths. A new
implementation needs its own proofs and checks; old successful builds do not
certify it. Any foundational work needed before PKG-01 must be named and scoped
in the roadmap instead of being hidden inside the predicate task. This decision
supersedes the earlier reuse-first recommendation in R6 and any interpretation
of R8 as requiring the new package to retain the old representations.

### R12 New implementation under Package

The author selected top-level `Package/`, outside `Nominal/`, for the new
development. Put newly authored foundations and package facilities there.
Retain `Nominal/` and `Instances/` as the reference development. Optional imports
from them require an explicit design decision; an import-free rewrite is also
permitted. Decide internal subdirectories, namespace/entry-point conventions,
Lake targets, example coverage and axiom audits during foundation planning.

The [revised package roadmap](../nominal-package-roadmap.md) therefore includes
foundation-contract, build-boundary and mathematical prerequisites before
PKG-01. This location decision does not approve a backend or start implementation
during the documentation revision.

### Evidence from the initial investigation and current recommendations

- The initial investigation's supported baseline passed the 1,033-job library/example build, direct
  tutorial compilation, and direct 1,859-declaration axiom audit. That
  build reused existing project/dependency artifacts; the earlier fresh-build
  record is not restated as a new fresh build.
- New standalone probes establish Prop predicate descent and support reflection,
  supported-subset/NFun correspondence, logical support and finite/cofinite
  facts, as well as coherent dependent quotient elimination. A naive polymorphic
  Prop instance fails registration; explicit local truth action works.
- Direct recursive constructors through NameAbs fail the tested instance and
  kernel occurrence checks. Raw mutual staging compiles; this does not prove
  its alpha quotient, generic induction or generation contracts.
- Counterexamples reject unconditional supported abstraction mapping and fixed-
  substitution equivariance. The old algebraic sketch remains historical input;
  its false/misleading statements were audited, not merged or repaired.
- A candidate direction is a staged hybrid with generated raw syntax/alpha
  quotients, shared verified certificates and ordinary public functions/Prop
  judgments. Its shared core may be newly authored. A generic signature carrier
  and independently designed foundations remain alternatives; familiarity with
  the old core does not select this architecture.
- Supported predicate theory, alpha-compatible raw predicates and arbitrary-
  motive induction are complementary layers. Generic rule induction still needs
  a proved transport/refreshability criterion; relation equivariance alone does
  not supply it. The 2025 primary rule-induction theorem adds useful evidence.

Exact commands, named results, versions, assumptions, alternatives and remaining
obligations live in the linked notes. Scratch results remain outside supported
imports. The initial propositions note is retained as the earlier investigation;
its previously unavailable Copello 2016 source has now been retrieved and read.

### Next review decision

Begin with the foundation-contract and readiness tasks in the
[package roadmap](../nominal-package-roadmap.md), then develop PKG-01 against the
chosen Package interfaces once its prerequisites are met. Do not assume the old
core makes those prerequisites complete. The public representation and exact
implementation scope still need review; R11/R12 themselves are settled.

The initial research and this policy revision made no production-code changes.
Research material has since been committed in `7fed53a`; the current revision
is a documentation change on top of that commit. No new commit, push, merge,
dependency change, CI change or publication is part of this revision.
