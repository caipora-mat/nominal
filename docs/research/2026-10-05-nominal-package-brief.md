# Nominal package research brief

These notes record the agreed research direction and unresolved questions for a
Lean package for reasoning about languages with binders. They are a requirements
and decision record, not an approved implementation architecture or a claim that
the package already exists. Update them as the discussion develops; preserve
superseded choices with their reasons rather than silently rewriting history.

Date: 2026-10-05.
Research branch: `fasapa/nominal-package`.
Starting commit: `4279ba92efacd77b3b96e507631502272b489999` on `fasapa/next`.

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
reusable theory, and a reference case study. The target is a specified general
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

Lambda calculus and replaying Church–Rosser through the package are intended
case-study targets. Generality must be tested beyond lambda calculus. A second
example involving terms and quantified formulas has been proposed, but its exact
language and theorem have not yet been selected.

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

### R6 Reuse nominal theory throughout

Investigate the role of supported functions, name abstraction, concretion, FCB,
fresh quantification, nominal predicates/propositions, and fresh induction and
recursion in the generated package. Reuse and extend the existing proved theory
where appropriate. The author clarified that predicates and judgments should
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
the author changes them. There is no authorization here to merge the old
algebraic sketch or silently replace the established representations.

### R9 Investigate propositions before selecting the architecture

Compare Pitts' finitely supported predicates and logical operations, the current
quotient-based arbitrary-predicate induction, Isabelle's treatment of predicates,
and Copello's alpha-compatible predicates. These may provide complementary
layers; do not force them into a mutually exclusive choice in advance.

The author's constructive Rocq experience with setoids and `Prop` is a research
motivation. Identify exactly which assumptions and representations produced each
limitation, and which transfer to classical Lean. Separate proof elimination,
extensional equality, quotient descent, finite support, equivariance and
metaprogram inspection. In particular, do not weaken the current induction API
by requiring all user motives to be finitely supported.

The [initial propositions investigation](2026-10-05-propositions-and-induction.md)
records checked sources, scratch evidence and unresolved work. It does not choose
a public predicate representation or authorize replacing the working theory.

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
- Which second language and nontrivial theorem best test generality?
- How should the research journal, mathematical exposition, implementation plan,
  experiments and current roadmap refer to one another without duplicating claims?

These questions are deliberately unresolved. The next deliverable is a
brainstorming prompt grounded in this brief, followed by an evidence-based
architecture comparison and dependency-ordered roadmap. No particular backend
or command grammar has yet been selected.

## 2026-10-05 architectural investigation: decisions and review artifact

The sections above preserve the brief as it stood before the investigation.
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
The proposed delivery order is the complete lambda/FOL workflow first, then
let, π and μ as explicit later milestones. All five remain part of the research
program; no proof or implementation of the later studies is claimed.

### Investigated evidence and recommendations

- The supported baseline passes the 1,033-job library/example build, direct
  tutorial compilation, and direct 1,859-declaration axiom audit. This turn's
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
- The recommended direction is a staged hybrid with generated raw syntax/alpha
  quotients, shared verified certificates and ordinary public functions/Prop
  judgments. A generic signature carrier remains an evaluated alternative.
- Supported predicate theory, alpha-compatible raw predicates and arbitrary-
  motive induction are complementary layers. Generic rule induction still needs
  a proved transport/refreshability criterion; relation equivariance alone does
  not supply it. The 2025 primary rule-induction theorem adds useful evidence.

Exact commands, named results, versions, assumptions, alternatives and remaining
obligations live in the linked notes. Scratch results remain outside supported
imports. The initial propositions note is retained as the earlier investigation;
its previously unavailable Copello 2016 source has now been retrieved and read.

### Next review decision

Review AD-01–AD-08 in the proposal and PKG-00–PKG-11 in the
[package roadmap](../nominal-package-roadmap.md). The recommended first
implementation increment is **PKG-01**, the narrowly scoped predicate-foundations
API, followed by its written implementation plan and execution agreement.
PKG-02, the manual carrier-certificate experiment, is an alternative first
increment. The author has not yet approved either implementation increment.
No production code, existing theorem, dependency, branch, external repository,
CI configuration, commit, push or publication was changed by this research.
