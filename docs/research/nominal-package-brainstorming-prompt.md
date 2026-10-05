# Brainstorming prompt for the Lean nominal package

Use the following prompt to continue the architectural research. The linked
brief records settled user decisions; the propositions note contains initial
evidence, not a selected architecture. This prompt requests investigation and
planning, not implementation of the full package.

```text
Brainstorm an evidence-based architecture and research roadmap for a nominal
package for Lean, inspired by Isabelle Nominal and Nominal2.

Work on fasapa/nominal-package, created from the completed core/Church–Rosser
development at 4279ba92efacd77b3b96e507631502272b489999. Inspect the actual current
branch, history and working tree first; preserve every existing uncommitted file.
Do not restart from the old algebraic branch or merge it wholesale.

Read repository instructions and:
- docs/research/2026-10-05-nominal-package-brief.md
- docs/research/2026-10-05-propositions-and-induction.md
- docs/roadmap.md
- docs/release-assessment.md
- docs/tutorial.md and its compiling Lean examples
- docs/research-correspondence.md
- docs/reviews/2026-10-02-development-review.md, as historical evidence

Verify current code before repeating old findings. Tasks 1–9 delivered the core,
lambda interfaces, substitution, reduction, fresh rule induction, Church–Rosser,
NFun improvements and first-deliverable polish. Learn from those results.

Research purpose and agreed constraints

The objective is a package for researchers studying first-order languages with
binders. Users should declare syntax, operations and judgments and reason with
tools close to traditional pen-and-paper practice. All binding infrastructure
must have a justified nominal account checked by Lean's kernel.

- Use classical Lean/Mathlib fully: choice, quotients and noncomputable operations
  are acceptable. Executable programs are not a requirement.
- Expose familiar freshness/free-variable conditions and explicit avoidance in
  induction. Hide permutations, support certificates, quotient representatives,
  NFun packaging and FCB obligations wherever sound automation can justify them.
- Prefer dedicated Lean commands/DSL forms for nominal datatypes, function
  definitions and inductive judgments. Exact names and grammar remain open.
- Initially support one atom sort, single/nested binders, and multiple syntactic
  categories such as terms and formulas. Specify mutual recursion and container
  support rather than silently assuming them.
- The first package milestone is a complete workflow: user-defined syntax,
  functions, judgments and proofs. Syntax-only generation is an intermediate
  increment, not the full milestone.
- Lambda calculus and replaying Church–Rosser are case studies, not hard-coded
  architecture. Select a second language/theorem to test genuine generality.
- Nominal predicates/propositions should primarily support ordinary Lean Prop.
  A separately interpreted nominal formula logic is not a settled requirement.
- Whether generic nominal terms or an interpreted signature are needed internally
  is an open research question. Investigate the old fasapa/algebraic sketch, its
  mathematical defects and possible reusable ideas without treating it as authority.
- General algebraic theory should serve the package; no commitment has been made
  to a categorical initial-chain construction as an independent deliverable.
- Correctness first, no deadline, no CI. Preserve existing public theory and the
  completed case study. Murillo's syntax/unification branch remains excluded.

Research method

Ask focused questions when a real research or user-experience choice matters,
while continuing independent investigation. Do not ask again about settled
constraints above. Use parallel agents for independent investigations if useful;
coordinate scopes and critically verify their findings.

Every design decision must be recorded in research notes with its alternatives,
rationale, assumptions, dependencies, evidence and unresolved issues. Preserve
failed approaches and counterexamples. Distinguish hypotheses, source readings,
scratch experiments, integrated proofs and user decisions. Never turn a plausible
architecture into a claimed theorem or implementation result.

Plan an evolving mathematical article alongside the development: theory, package
interface, generated guarantees, examples, difficulties, negative results,
limitations and comparison with prior work. Propose a sustainable notes/manuscript
organization, with explicit links from mathematical statements to Lean declarations
and verification evidence. Do not invent novelty or publication claims.

Investigation 1: Extract requirements from actual proofs

Read the completed lambda development as a library client. Identify which manual
steps belong to datatype construction, supported definitions, predicate logic,
fresh term induction, fresh rule induction and proof automation.

Show prospective user-level declarations and proof fragments for:
- Syntax with single and nested binders.
- A function with fixed nominal parameters, such as substitution.
- A definition needing access to original subterms as well as recursive results.
- An inductive judgment and a proof using fresh rule induction.
- A second language with multiple syntactic categories.

Label these examples as proposed syntax. Specify what users supply, what the
package generates, and what obligations remain when automation cannot finish.
Do not force ordinary users to manipulate an internal generic syntax carrier.

Investigation 2: Propositions, predicates and induction foundations

Make this a substantial research workstream before selecting the architecture.
Consult the full local ref/nominalsets.pdf, especially nominal powersets, logical
operations, Some/Any, induction and inductive definitions. Compare primary sources
for original Isabelle Nominal, Nominal2, Copello's alpha-compatible predicates,
the Rocq precursor and the current Lean quotient principles. Pin versions and
state unavailable source/build evidence.

Distinguish:
- Truth values p : Prop and predicates P : X → Prop.
- Formula syntax, elaborated Lean expressions and proof terms.
- Finite support, equivariance and alpha-respectfulness.
- A supported predicate object and an arbitrary induction motive.
- Prop elimination restrictions, extensionality, quotient descent and dependent
  transport/coherence.

Investigate supported predicates via NFun-to-Prop, supported subsets and any
well-motivated alternative. Determine their action/equality laws, universes,
typeclass behavior, logical operations, parameter support and Some/Any interfaces.
Study a formal bridge between alpha-compatible raw predicates and predicates on
alpha quotients. Analyze genuinely dependent motives separately.

The initial note already contains checked scratch evidence that a local trivial
Nominal action on Prop supports an NFun predicate construction and a Some/Any
bridge. Do not repeat the claim that Prop makes this impossible. Likewise, do not
assume all ordinary predicates have finite support, or that all arbitrary uses of
Classical.choice define supported functions. A supported fresh-selector
counterexample is recorded in the note.

Preserve arbitrary-predicate/context-generalized term and rule induction where
justified. Compare Pitts' supported-predicate theory, Copello-style compatibility,
quotient boundaries and Isabelle automation as potentially complementary layers.
Explain precisely which constructive Rocq limitations transfer to classical Lean;
do not infer universal necessity of setoids from proof elimination alone.

Investigation 3: Compare backend architectures

Present at least two materially different approaches and a justified recommendation,
including a hybrid when appropriate:
- Generic first-order syntax/signatures, alpha relation, quotient and generic theory.
- Per-declaration proof-producing generation from binding annotations.
- A generic verified semantic core with generated user-facing declarations/lemmas.

Specify the accepted signature grammar, atom versus recursive positions, syntactic
categories, binding scopes, parameters, positivity and universe policy. Evaluate
whether a new raw nominal-term carrier is necessary and what role it serves.
Keep language atoms distinct from schematic metavariables and Lean metavariables.
Do not introduce unification merely because nominal terms can support it.

For each approach, explain the mathematical construction, required theorems,
Lean feasibility, public abstraction boundary, generation complexity, diagnostics,
maintenance costs and extension limits. Identify where the old algebraic sketch
has wrong statements, not merely missing proofs. If proposing initiality or an
isomorphism, tie it to the actual generated constructors and maps.

Investigate how NameAbs, concretion, FCB, supported functions, predicate lifting
and fresh representatives cooperate. Do not assume a recursive constructor through
NameAbs is accepted: address instance circularity and strict positivity explicitly.
Do not choose an architecture simply because it resembles an existing sketch.

Investigation 4: Define the generated mathematical contracts

For datatype commands, specify alpha equality, constructor equations/inversion,
canonical action, support/free-variable laws, fresh representatives, strong
induction and the exact recursion facilities supplied.

For function commands, distinguish iteration, primitive recursion and dependent
elimination. Specify supported fixed parameters, higher-order NFun use, computation,
uniqueness, support/equivariance, FCB and rewriting behavior. Decide how users see
ordinary functions while the package retains certified nominal information.

For judgment commands, specify the accepted rule grammar and sufficient conditions
for equivariance/support, alpha compatibility, fresh inversion and strong rule
induction. Explain how binders in premises and conclusions are transported
together. Do not infer fresh rule induction merely from term induction.

For automation, specify certified lemma registries, expression-aware handling of
binders/captures, unsupported-input diagnostics and explicit proof escape hatches.
Opaque operations, arbitrary functions and classical choice must not receive
unjustified support or equivariance certificates.

Investigation 5: Resolve risks with bounded experiments

Propose small decisive Lean probes for uncertain mathematical/elaboration points.
Run useful scratch experiments when feasible, clearly separated from supported
code. Inspect theorem statements and axioms, not just successful compilation.
Include positive examples and counterexamples delimiting the promised grammar
and automation. Preserve all existing production code during brainstorming.

Deliverables

1. A written research brief updated with decisions, hypotheses and open questions.
2. A precise literature/theorem comparison, especially for predicates and induction.
3. A comparison of architectures and a recommendation with explicit unresolved risks.
4. Proposed user-facing examples and generated mathematical contracts.
5. A dependency-ordered roadmap decomposed into manageable research/implementation
   increments, each with proof obligations, acceptance examples and verification.
6. A complete first-workflow criterion: generated lambda development replaying the
   relevant Church–Rosser proof, plus a second language/theorem testing generality.
7. A research-note workflow and detailed mathematical article outline.
8. A short list of focused questions genuinely requiring the author's choice.

Preserve existing roadmap IDs/history and distinguish the completed first deliverable
from this new phase. Do not mark a proposed or scratch-verified feature integrated.
Do not silently implement the package, merge experimental branches, commit, push,
publish, or alter external repositories as part of this brainstorming task.

Finish with a reviewable architecture/roadmap proposal. Keep unresolved decisions
explicit, and obtain agreement on the first concrete implementation increment
before beginning package implementation.
```
