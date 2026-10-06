# Research notes and evolving mathematical article

Date: 2026-10-05. Architectural-policy revision after
`7fed53a2e5fc67379f86f085515e310e7c1fddb7` on `fasapa/nominal-package`.
Writing policy for the
[package research](2026-10-05-package-architecture.md) and its intended research
publication; no publication, novelty or readiness claim is implied.
The article should develop alongside proofs and client experience; it should
not present proposed package contracts as already established results.

**Current author decision:** after approving the F02 + F03a specification, the
author requested an article under `docs/article/`, entirely in LaTeX, written
alongside implementation. The initial [main source](../article/main.tex) includes
[purpose/scope](../article/sections/introduction.tex) and
[permutation/action foundations](../article/sections/foundations.tex).
Its scientific scope includes permutations, selected actions and finite support,
with mathematical arguments and relevant Lean declaration correspondence.
The article now also covers the proved least-support construction and laws;
freshness/predicate contracts require their own results. The bounded
[implementation plan](../superpowers/plans/2026-10-05-package-foundation-kernel.md)
assigns article updates to each task. A subsequent author correction reserves
persistent usage examples for future case studies; the article does not claim
a separate Package examples or consumer-audit layer.

The author also requested that discussions clarifying mathematical concepts and
representation choices be incorporated into the corresponding LaTeX sections
when they add insight to the article. Explain the meaning of a consequential
interface, its rationale and viable alternatives with their tradeoffs; preserve
the full discussion in research notes when only part serves the manuscript.
Do not leave the reasoning only in chat or present an implementation choice as
a mathematical necessity.

For each definition or structure selected for exposition, state its mathematical
concept before discussing the Lean encoding, and identify the correspondence of
carriers, operations and laws. This does not require a manuscript entry for every
declaration. Check Mathlib before introducing package-specific machinery; record
the investigation in research notes and explain reuse or adaptation in the article
when it illuminates the mathematics or system design. Distinguish implementation
helpers from independent mathematical concepts.

## Publication content policy

The article is a selective research account of the system and its mathematics.
Choose a coherent argument around central definitions, theorems and proof ideas,
meaningful architectural choices, consequences, limitations and counterexamples.
Discuss relevant theories and related systems through grounded comparisons of
assumptions, guarantees and user reasoning. Explain what the results teach; do
not invent novelty, priority, generality or performance claims. This policy
supersedes earlier instructions that made the manuscript a development record.

Exclude development-stage and task IDs (including F03b, F04a and PKG identifiers),
work logs, delivery/status or approval narratives, branch and commit bookkeeping,
agent assignments, reviews and verdicts, and audit/build commands, results,
counts, cache conditions and diagnostic histories. In particular, review claims
such as "Independent final review found no issues" are not article content.
Keep this information in the roadmap, specifications/plans or research notes.
The internal claim ledger supports the article; it is not a manuscript section.

Retain scientifically relevant logical assumptions, mathematical dependencies,
limitations and Lean API correspondence. Lean's kernel and standard classical
axioms may be explained as the formalization's logical basis, without reporting
audit operations or outcomes. Cite relevant publications and source versions
for scholarly attribution; keep development revision tracking in research notes.

Select examples and proofs for their explanatory value. Summarize routine lemmas
or cite their source; do not mirror the module tree, enumerate the entire API,
or reproduce every implementation proof. An article section need not correspond
one-to-one with a task, module or declaration. Internal research notes retain
details and unsuccessful experiments that do not serve the publication's argument.

## Concurrent writing is part of delivery

The article is written together with the development of the package throughout
the project. Every substantive implementation increment includes the matching
LaTeX work in its scope and completion criteria. PKG-11 tracks this continuous
responsibility; it is not work postponed until the implementation is finished.

Each specification/plan must identify the relevant sections under `docs/article/`
and the selected mathematical statements, proof explanations or system insights
to add or revise. Draft the mathematics while designing/proving it, and update
the draft as hypotheses, relevant names, representations or proof strategies
change. Do not present proposed results as established; phrase open questions
in mathematical terms, without importing implementation-stage tracking.

Before closing an increment, require both its code validation and an accurate
article update: definitions and theorem assumptions match the chosen interface;
the mathematical argument and limitations are explained; relevant source and
declaration references are accurate; and the LaTeX entry point compiles. Review
the mathematical correspondence as well as PDF compilation. Record these checks
and their results in the roadmap, never in the manuscript. Routine implementation
or build-tooling changes may require no new article text; record that editorial
decision internally instead of adding an operational account. Publication polish
and publication are not per-increment requirements.

An article subagent may draft in parallel with implementation using agreed
statements. Reconcile its text against the final declarations and checks before
delivery; concurrent work does not justify leaving the manuscript behind.

F03b applies this rule to controlled swap factorization, arbitrary-set avoidance
and the selected-action criterion in [foundations.tex](../article/sections/foundations.tex).
The mathematics and LaTeX were developed together. The four public Lean results
are checked, the article is reconciled and compiled, and independent review
found no issues. F03b is delivered.
F04a finite support theory and F04b nominality/least support are implemented and
checked with their concurrent article sections; the remaining F04 layers remain
future work. F04b's independent final review found no issues and independently
checked its mathematical correspondence and a fresh manuscript compilation.

The [F04a written specification](../superpowers/specs/2026-10-05-package-finite-support-design.md)
now assigns `docs/article/sections/support.tex`, `sec:finite-support`, to its
concurrent implementation: Mathlib's support predicate and its finite-bound
specialization, finite supportedness, basic/image/product bounds, conjugation
transport, the F03b swap specialization, infinite-atom finite intersection and
the two-atom counterexample. The specification is approved; its
[implementation plan](../superpowers/plans/2026-10-05-package-finite-support.md)
assigns concurrent LaTeX drafting to Tasks 1–3 and final correspondence/build
verification to Task 4. The plan was approved for native execution; its code,
consumers and mathematical section now check, with a clean independent final review.
F04a is delivered in the working tree, uncommitted.
The approved [F04b specification](../superpowers/specs/2026-10-06-package-least-support-design.md)
and [native plan](../superpowers/plans/2026-10-06-package-least-support.md)
extend that file with `sec:least-support`, now reconciled and compiled alongside
the checked implementation. It explains the proof-only certificate, individual
leastness and uniqueness via the Finset minimum/intersection argument, witness
independence, carrier convenience, transport, empty support, image inclusion
and the finite-atom/strong-support boundaries. F04c owns `sections/freshness.tex` and F04d owns
`sections/quotients.tex`, as recorded in the active roadmap. Every later
specification and plan must retain its own article/reconciliation obligations.

The [F03b written specification](../superpowers/specs/2026-10-05-package-controlled-swaps-design.md)
assigns the controlled-factorization, avoidance and action-invariance propositions,
their Mathlib/Package proof correspondence and final manuscript verification to
this increment. The specification is approved. The
[implementation plan](../superpowers/plans/2026-10-05-package-controlled-swaps.md)
was approved for native execution. It assigns article drafting to its first two
mathematical tasks and final evidence reconciliation/compilation to its third task.

Follow the [architectural-freedom policy](README.md#architectural-freedom):
the package may develop its entire nominal foundation afresh, including actions,
support, functions, predicates, abstraction, quotients, and induction. Reuse,
adaptation, and replacement must each be evaluated on their merits. The article
should explain the resulting mathematics and design choices without treating
old APIs, classes, modules, seals, universe bounds, or backward compatibility as
requirements. Ordinary `Prop`, classical Lean, proof correctness, and the agreed
theorem strengths remain the mathematical commitments.

All new implementation belongs under top-level `Package/`, according to the
[implementation-location policy](README.md#implementation-location).
`Nominal/` and `Instances/` are preserved reference implementations. Links to
them are evidence for the earlier development; they do not designate the new
package's declaration paths or mandatory imports.

## Keep one owner for each kind of claim

| Artifact | Role | Update rule |
| --- | --- | --- |
| [Research policy](README.md) | Canonical architectural freedom and implementation location | Apply it throughout notes and plans; distinguish current decisions from historical evidence |
| [Research brief](2026-10-05-nominal-package-brief.md) | Settled user decisions, intent and unresolved choices | Append decisions with date, alternatives and reason; preserve superseded positions |
| Dated investigation notes | Mathematical arguments, literature readings, counterexamples and design alternatives | Record exact source version, statement assumptions, Lean evidence and limitations |
| `docs/research/probes/` | Small reproducible experiments, including guarded failures | Each probe states purpose, command and nonclaims; keep out of supported umbrellas until deliberately promoted |
| [Package roadmap](../nominal-package-roadmap.md) | PKG task IDs, dependency/status tracking, delivered verification | Link to notes instead of copying proofs; mark complete only against stated acceptance criteria; keep the prior library roadmap as historical evidence |
| `Package/` | New foundations, package machinery, and implementation clients | Choose internal paths in the relevant bounded plan; attach evidence to the actual new declarations |
| Future `docs/research/claims.md` | Statement-to-evidence ledger | Add a row whenever the manuscript makes or changes a substantive claim |
| `docs/article/`, entry point `main.tex` | Selective LaTeX research exposition | Develop alongside implementation; explain system and mathematics, attribute sources and delimit proved claims; exclude development records |
| Per-increment spec/plan | Implementation boundaries, replacement dependencies, article section and execution checks | Assign code and LaTeX work to the same bounded increment; link its PKG task and any historical evidence separately |

This table describes internal artifact ownership, not an article outline. The
separate claim-ledger path remains proposed, and `Package/` is the selected
implementation destination. The manuscript now uses a single LaTeX entry point
and included sections; its initial bibliography is in `main.tex`. This supersedes
the earlier recommendation to begin article sections in Markdown. All article
content must remain LaTeX, with no parallel Markdown manuscript. Research notes,
specifications and implementation plans retain their existing repository formats.
No external manuscript repository is modified, and creating the manuscript does
not create a Package implementation or certify its proposed declarations.

## Claim ledger format

The ledger is an internal research record, not manuscript content. Each claim
should record: stable claim ID; exact mathematical statement and
hypotheses; status; Lean declaration/module and source revision; proof dependency
policy; source/theorem/page when inherited; commands actually run; counterexample
or failure history; manuscript location; next unresolved obligation.
Label reference-library results separately from `Package/` results. An analogous
old theorem is evidence for feasibility, not proof of its newly implemented
counterpart. Reusing a result, adapting its proof, reproving it, and comparing
two implementations are distinct claims to record explicitly.

Possible initial entries (examples of the ledger format):

| ID | Statement/status | Precise evidence | Limitation |
| --- | --- | --- | --- |
| CL-001 | Least support is not necessarily strong support — reference counterexample | `Examples/CoreContracts.lean`, unordered atom-pair example; standard foundations | Does not refute least-support existence |
| CL-002 | Arbitrary-motive, context-generalized fresh term induction — proved in reference library | [`Term.strong_ind`](../../Instances/LambdaCalculus/Induction.lean); reference baseline and audit | Concrete lambda theorem; generic generation remains proposed |
| CL-003 | Supported iteration with guarded lambda equations and uniqueness — proved in reference library | [`Term.recNoContext_lam`, `recNoContext_unique`, `recNoContext_supports`](../../Instances/LambdaCalculus/Recursion.lean) | Iteration, not primitive or dependent recursion |
| CL-004 | Fresh rule induction for unrestricted beta/parallel — proved in reference library | [`Term.Beta.strong_ind`, `Term.Parallel.strong_ind`](../../Instances/LambdaCalculus/ReductionInduction.lean) | Relation-specific proofs; no arbitrary-judgment theorem inferred |
| CL-005 | Church–Rosser and normal-form uniqueness for open contextual terms — proved in reference library | [`Term.BetaEq.church_rosser`, `Term.BetaEq.normal_unique`](../../Instances/LambdaCalculus/ChurchRosser.lean) | No normalization/existence claim |
| CL-006 | Compatible raw Prop predicates correspond to quotient predicates — scratch | [Predicate probes](2026-10-05-predicate-foundations.md), named descent/pullback results | Not a generated dependent eliminator |
| CL-007 | Straight recursive NameAbs encoding is rejected — scratch negative | [BackendPositivity.lean](probes/BackendPositivity.lean), exact guarded diagnostics | Not a universal impossibility theorem |
| CL-008 | Unconditional abstraction mapping for supported functions fails — scratch theorem | [BackendCounterexamples.lean](probes/BackendCounterexamples.lean), `no_unconditional_const_abs_map` | Fresh-binder mapping remains possible research |
| CL-009 | Generic fresh rule criterion — primary-source theorem | [2025 comparison](2026-10-05-isabelle-comparison.md), Definition 6/Theorem 7 | No Lean port or Isabelle build in this research turn |
| CL-010 | Complete generated syntax/function/judgment workflow — proposed | PKG-07 acceptance criterion | No implementation/generation result yet |
| CL-011 | Package permutation/action, finite support and least support — F02/F03a/F03b/F04a/F04b delivered | `Package/Foundations/Permutation.lean`, `Package/Foundations/SwapFactorization.lean`, `Package/Foundations/Action.lean`, `Package/Foundations/Support.lean`, `Package/Foundations/Nominal.lean`, their recorded audit and article sections | Canonical nominal instances, freshness, quotients and predicate foundations require their later proofs and article updates |

Record actual declaration names when creating the ledger; a descriptive label is
not an adequate theorem reference. Re-run audits after a dependency-changing
proof refactor. A cached build, direct source elaboration, fresh project build
using cached dependencies, and clean dependency bootstrap are separate fields.

## Selective article outline

These are candidate research themes, not a requirement to document every layer.
Choose and combine them according to the proved results and the article's central
argument. Omit unsupported contributions and routine implementation details.
Case studies and future interfaces below are internal planning candidates;
listing them here does not establish them or require their appearance in a draft.

### 1. Research problem and explanatory example

Explain the problem of reasoning about syntax, operations and judgments with
binders. State the intended mathematical setting and the guarantees actually
provided. Use one small example to expose the difficulty and the reasoning the
system supports. Separate a demonstrated interface from a mathematical proposal
without a release/stage narrative. Introduce only contributions substantiated
by the formalization and the source comparisons.

### 2. The mathematical ideas behind the representation

Develop the definitions needed for the central results: finite permutations,
selected actions, support and equivariance, then the binding constructions when
available. Distinguish moved points from support and finite, least and strong
support. Choose proof ideas that explain why the representation works, such as
controlled transpositions or the fresh atom in finite-support intersection.
A short counterexample can explain an essential hypothesis better than an API
catalogue. Summarize routine closure laws unless a later argument needs detail.

Explain classical choice, actual quotients and noncomputable semantic operations
where they affect the theory. Relate meaningful Lean choices to the mathematics,
such as selected actions, universe independence and conjugation versus pointwise
function actions. Compare viable representations when the tradeoff yields an
insight; do not treat the old Lean or constructive Rocq representation as a
mathematical necessity. Describe mathematical dependencies without task IDs.

### 3. Reasoning with binders, predicates and judgments

Select the central theorems about alpha equivalence, predicate descent and fresh
reasoning once established. Distinguish supported predicate objects from the
arbitrary motives allowed by induction. Explain the hypotheses of Some/Any and
why quotient compatibility and dependent transport are different obligations.

Present fresh term induction, iteration and primitive recursion separately when
the distinction matters to the contribution. For judgments, explain how premises,
induction hypotheses and conclusions are transported together, and what justifies
the variable convention. A contraction or eigenvariable example should clarify
the theorem's reach. Include only the machinery needed to explain the result;
do not turn this theme into a full inventory of binder interfaces.

### 4. System architecture and user reasoning

Explain the selected syntax construction, accepted binding scopes and how the
system turns user declarations into certified guarantees. Give the central
correctness contracts and the reason for architectural choices. Show enough Lean
correspondence to connect the mathematical account with actual use, including a
manual proof when automation has a meaningful boundary.

Discuss generic versus generated proofs and Lean's kernel and standard axioms
as the logical basis. Routine module layout, declaration inventories, import
checks, development workflow and build/audit mechanisms do not belong here.
Do not call a type isomorphism an initiality theorem without the required map
class, existence and uniqueness results.

### 5. Case studies as mathematical evidence

Choose studies that add distinct insight to the argument. The agreed research
portfolio remains below for planning; completing it does not oblige the article
to give every study equal space or to report implementation stages.

| Candidate study | Distinct mathematical question |
| --- | --- |
| Lambda calculus | How syntax, substitution and fresh rule reasoning combine in Church–Rosser for open contextual terms |
| First-order logic | How finite contexts and eigenvariables enter substitution admissibility |
| Lambda with let | How binder scope and access to original subterms support expansion correctness |
| π-calculus | How joint label/continuation binding affects transitions and fresh inversion |
| Modal μ-calculus | How positivity, semantic environments and fixed-point unfolding interact with nominal binding |

Use actual theorem strengths and justified limits. For π and μ, state the chosen
semantics before discussing results. Arbitrary semantic environments need not be
finitely supported, and nominal syntax generation alone does not establish a
coinductive semantics. Reference-library examples must not be presented as new
package clients.

### 6. Related theories, systems and limitations

Integrate grounded comparisons with the mathematical and architectural discussion,
then draw together the consequences. Compare relevant results from Pitts,
Isabelle Nominal/Nominal2, Copello's predicate work, the Rocq precursor and other
binding frameworks by assumptions, theorem strength and forms of user reasoning.
Check primary sources before making each comparison or claim of novelty.

Select limitations and counterexamples that explain a boundary of the system:
for example, fixed-parameter support versus joint equivariance, unsupported fresh
selection, dependent coherence or inadmissible binder rules. A failed encoding
may motivate a representation choice, but it is not a universal impossibility
result. Discuss the substantive lesson rather than the sequence of attempts,
compiler diagnostics or review outcomes. End with grounded research questions.

### Internal evidence map

These links guide writing and checking; they are not a list of content to copy
into the manuscript. Operational commands, revisions, failed attempts and
validation results remain in the linked research records and roadmap.

| Theme | Internal sources and possible correspondence |
| --- | --- |
| User reasoning | [Tutorial](../tutorial.md), [reference client](../../Examples/Tutorial.lean), [proposed contracts](2026-10-05-package-contracts.md); PKG-07–PKG-10 |
| Permutations, actions and support | `Package/Foundations/Permutation.lean`, `SwapFactorization.lean`, `Action.lean`, `Support.lean`; [foundation investigation](2026-10-05-algebraic-source-investigation.md), [discrete representation](2026-10-05-discrete-representation.md); PKG-F03/F04 |
| Predicates and fresh reasoning | [Predicate foundations](2026-10-05-predicate-foundations.md), [propositions and induction](2026-10-05-propositions-and-induction.md), [Isabelle comparison](2026-10-05-isabelle-comparison.md); PKG-01/03/06 |
| Carrier and package design | [Backend comparison](2026-10-05-backend-comparison.md), [architecture](2026-10-05-package-architecture.md), [contracts](2026-10-05-package-contracts.md); PKG-02/04/05 |
| Reference theorem comparisons | [Term induction](../../Instances/LambdaCalculus/Induction.lean), [iteration](../../Instances/LambdaCalculus/Recursion.lean), [rule induction](../../Instances/LambdaCalculus/ReductionInduction.lean), [inversion](../../Instances/LambdaCalculus/ReductionInversion.lean), [pinned external correspondence](../research-correspondence.md) |
| Boundaries and counterexamples | [Backend probes](2026-10-05-backend-comparison.md), [predicate probes](2026-10-05-predicate-foundations.md), [reference contracts](../../Examples/CoreContracts.lean); record exact assumptions before generalizing |

## Sustainable update cycle

Follow the package roadmap's foundation stages before claiming that PKG-01 has
its inputs. A replacement action, support, or function theory is a substantive
dependency with its own statement and evidence, not merely a rename of a
reference theorem. Subsequent increments may develop additional foundations
when needed; the roadmap should record that work explicitly.

For every increment: record the question, discriminating test and relevant article
section internally; draft the selected mathematical explanation while developing
its Lean proof; preserve important failed approaches and counterexamples in
research notes; compile and audit the code; consume the claimed fact through the
public boundary; synchronize and compile the LaTeX exposition; then update the
roadmap's evidence and task status. None of these process records belongs in the
manuscript. For foundation slices, usage checks may remain temporary under the
author's policy;
persistent usage examples belong to case studies. A theorem rename updates any
article references in the same increment. A changed hypothesis reopens dependent
claims. A proposed command becomes a demonstrated command only when its example
compiles through the supported import boundary. Do not mark a mathematical
increment complete with relevant research exposition left for later. When a
routine change adds no research insight and changes no manuscript claim, record
that editorial decision in the roadmap instead of enlarging the article.
Use `Package/` paths for new declarations, imports, and implementation plans;
retain old source paths and revisions when citing historical evidence.

At each milestone, perform a short consistency review across grammar, generated
contracts, case-study acceptance, ledger and manuscript. Avoid a second enormous
hand-maintained declaration inventory. A small future script can check linked
declaration names and Markdown paths if maintaining them becomes burdensome;
it is not a prerequisite for the first mathematical increment. No CI or recurring
automation is proposed or installed by this research task.
