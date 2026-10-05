# PKG-01 fresh-context prompt

This handoff follows the revised foundation-first roadmap. The author has
settled architectural freedom and the top-level `Package/` location. Predicate
implementation still depends on establishing the chosen foundation contracts;
the prompt does not assume the existing core supplies them. **Current resume
point:** F02 and F03a are delivered in the working tree. F03b is next, followed
by F04/F05 before PKG-01. Write the corresponding LaTeX article sections with
each implementation increment.

```text
Begin the PKG-01 workstream for the Lean nominal package. First assess and plan
its prerequisites in the revised roadmap; do not assume it is ready to implement
on top of the existing library.

Repository and current state

Work in /home/fab/Documents/nominal/nominal on fasapa/nominal-package.
The last inspected HEAD was 76966b1f2e44f594517442b6572e33abaa9038e0, with
uncommitted F02/F03a implementation, article and design records. The
completed reference core/Church–Rosser baseline is
4279ba92efacd77b3b96e507631502272b489999. Inspect the actual branch, history and
working tree first. Preserve every existing tracked and untracked file.
In particular, PredicateInterface.lean and PredicateSomeAny.lean in the research
probes directory were existing untracked work at the last inspection.

Read AGENTS.md and README.md, then:
- docs/research/README.md
- docs/nominal-package-roadmap.md
- docs/research/2026-10-05-nominal-package-brief.md
- docs/research/2026-10-05-package-architecture.md
- docs/research/2026-10-05-backend-comparison.md
- docs/research/2026-10-05-predicate-foundations.md
- docs/research/2026-10-05-propositions-and-induction.md
- docs/research/2026-10-05-package-contracts.md
- docs/research/2026-10-05-isabelle-comparison.md
- docs/research/2026-10-05-article-plan.md
- docs/research/2026-10-05-pkg01-readiness.md
- docs/research/2026-10-05-algebraic-source-investigation.md
- Package/README.md and the delivered Package/Foundations modules

The F02 + F03a specification and native implementation plan were approved and
delivered. Preserve that work and its scope correction: persistent usage
examples belong to future case studies; foundation usage checks may be temporary.
Do not recreate the first kernel or ask for its approval again. Check the current
records rather than treating historical absence claims as current state.

The active tracker is docs/nominal-package-roadmap.md. Do not reuse or update
docs/roadmap.md as the package tracker; it preserves the earlier history.

Architectural freedom — settled

The entire existing infrastructure is optional reference material. We may
develop everything required from scratch: atoms, permutations, actions,
support, freshness, functions, predicates, abstraction, quotients, induction,
recursion and tooling. Compare reuse, adaptation and replacement on correctness,
clarity, usability, proof obligations and maintenance cost. Neither reuse nor
wholesale rewriting is mandatory.

Existing APIs, typeclasses, representations, module boundaries, universe limits,
seals and proof strategies do not constrain the new package. Backward
compatibility is not required. Study the existing development for mathematical
evidence, successful clients, counterexamples and engineering lessons. Preserve
its source and intended theorem strengths. A new representation needs its own
proofs; previous successful builds do not certify it.

Mathlib-first — settled

Always investigate the pinned Mathlib before introducing general-purpose
definitions, instances or proofs. Search .lake/packages/mathlib/Mathlib with rg,
inspect exact statements and imports, and use small Lean checks where needed.
Prefer direct reuse, specialization, combinations of existing lemmas or a small
proved adapter to recreating existing infrastructure. For F03b in particular,
look for permutation factorization/induction results and test whether they can
provide the required control over endpoints.

If new code is necessary, record the relevant candidates and the concrete
mathematical or interface gap. Check hypotheses, universes and action coherence;
do not weaken the requested theorem or silently upgrade dependencies. Freedom
to replace the old Nominal implementation does not mean rebuilding Mathlib.
Keep the evidence proportionate and distinguish inherited results in the article.

Implementation location — settled

All new implementation belongs under top-level Package/, outside Nominal/.
Keep Nominal/ and Instances/ as the reference development. Optional imports from
them must be explicit dependency decisions. Choose Package subdirectories,
namespaces, entry points, Lake targets, clients and audit coverage in the design.
The old library build is not evidence that Package modules are checked.

These current instructions supersede inherited reuse-first advice for work on
Package. Do not ask again whether a fresh implementation or Package location is
allowed. Preserve unrelated work; do not switch branches automatically, merge
experimental branches, commit, push, publish, upgrade dependencies or add CI.

Foundation readiness comes first

Use the revised PKG-F01–PKG-F05 tasks to determine which prerequisites are
established for the selected design:
- F01: direct algebraic-sketch investigation, mathematical/API contracts and
  reuse/adapt/rebuild decisions per layer.
- F02: Package build, import, example and axiom-audit boundary.
- F03: F03a group/actions are delivered; F03b's support-facing permutation
  lemmas remain, especially swap generation with controlled endpoints and its
  avoidance corollary.
- F04: required support, freshness and quotient interfaces.
- F05: minimal function/predicate-input foundation for the chosen representation.

Report the evidence for each prerequisite. If it is missing, propose the first
bounded foundation increment instead of hiding an entire core rewrite inside
PKG-01. Reuse may discharge a prerequisite only after its actual contracts and
Package consumers are checked. A matching old declaration name is insufficient.
The separate F06 binder-descent work is for later induction/recursion unless a
specific dependency justifies bringing part of it forward.

PKG-F01 algebraic investigation: required evidence, now recorded

The current F01 source-investigation note records this completed reading and
its dispositions. Use and verify that evidence when making new choices; do not
restart it or treat it as unfinished solely because the original instructions
below describe the required inspection. Revisit specific claims if the next
design relies on unverified evidence or changes the assumptions.

Inspect the previously reviewed origin/fasapa/algebraic snapshot at
983adeb9b80f75fb7c77c05acfd2fcef16db1d46. Read its actual source without
switching branches or merging:

git show 983adeb9b80f75fb7c77c05acfd2fcef16db1d46:Nominal/Set/Algebraic.lean
git show 983adeb9b80f75fb7c77c05acfd2fcef16db1d46:Nominal/Set/Structural.lean

Check the existing backend-comparison assessment against these declarations;
do not merely repeat its conclusions. Investigate signature design, atom versus
recursive positions, functor maps, algebra morphisms, predicate lifting,
induction/recursion, initiality and abstraction descent. Separate false
statements from weak contracts, missing proofs and elaboration obstacles.
Record useful ideas as well as defects, with declaration references, evidence,
necessary corrections, dependencies and relevance to the new Package design.
Retain verified counterexamples and run new bounded probes where a decision
needs further evidence. Record any additional revision and unavailable build
evidence explicitly; do not treat a moving branch tip as the pinned snapshot.

For each relevant idea, recommend adopting, adapting, rederiving, deferring or
rejecting it, with reasons. Reading the note alone does not complete F01. This
investigation does not require repairing every placeholder, merging the branch,
choosing its architecture or building initial-chain theory. Reuse remains
optional, and all new implementation belongs under Package/.

PKG-01 mathematical scope

1. Supported predicates over ordinary Lean Prop: action, extensional equality,
   ordinary application, useful rewriting, and supported-subset correspondence.
   Compare a direct predicate structure, new supported-function interface,
   supported subsets and optional adaptation of existing NFun-to-Prop.
2. The bridge between relation-invariant raw Prop predicates and predicates on
   quotients: descent, pullback, computation and inverse laws. Under the selected
   equivariant quotient action, prove preservation/reflection of support.
3. Logical operations and support bounds: Boolean operations, universal and
   existential quantification over jointly supported relations, evaluation,
   composition and fixed nominal parameters where justified.
4. Some/Any interfaces using certified support or equivariance/context evidence;
   retain the exact hypotheses of fresh-quantifier laws. Do not require users to
   supply an exact least support when a sufficient bound works.
5. Ordinary-use clients and mathematical counterexamples delimiting the API.

Retain classical Lean/Mathlib, choice, quotients and noncomputable operations.
Executable fresh-name generation is not required. Supported predicates must
coexist with arbitrary-motive fresh term/rule induction; not every user motive
needs a support certificate. Dependent quotient elimination exists with coherence
conditions, but a general dependent nominal eliminator is outside PKG-01.

Existing evidence to inspect, not a mandatory design

Read the Lean probes under docs/research/probes/ and their verification records.
Rerun relevant experiments when relying on them. Preserve their original files
and distinguish new experiments from old evidence.

Known reference results include Prop quotient descent, supported-subset/function
correspondence, logical support, finite/cofinite atom predicates and quotient
support reflection. A fixed atom predicate can be supported without equivariance.
Infinite/coinfinite atom predicates need not be supported; no supported function
chooses an atom outside every finite input set. Raw binder-name inspection does
not descend through alpha equivalence. Classical choice is not itself a support
certificate, and arbitrary external unions or quantifier interchanges can fail.

The tested old typeclasses reject a generic local Nominal instance on Prop
because of their atom outParam; explicit fixed-atom letI works. This is evidence
about that interface, not a restriction on newly designed classes or structures.
Likewise, PFun is one way to distinguish conjugation from ordinary pointwise
action. Its wrapper is optional; confusing those mathematical actions remains
incorrect. New universe/instance policies need their own positive and negative
examples. Do not select a representation just because a scratch version compiles.

The five case studies remain lambda calculus/Church–Rosser, first-order logic/
substitution admissibility, lambda with let, pi calculus and mu calculus. They
guide the contracts but are not implementations to undertake in PKG-01.

Concurrent article writing — settled

Write the article together with the implementation, entirely in LaTeX under
docs/article/. Every substantive increment's spec/plan includes its corresponding
article sections. Draft the mathematics while proving it; synchronize final
assumptions, declarations, proof status and verification evidence and compile
the article before marking that increment complete. PKG-11 coordinates ongoing
writing and is not deferred until the code is finished. For F03b, extend the
foundations section with the factorization argument and avoidance corollary.
Delegated article work may run in parallel but must match the final code.

Next-session deliverables and implementation boundary

This session authorizes inspection, bounded scratch experiments and concrete
design/planning. Do not begin production implementation before agreement on
the relevant spec and plan.

- Give a current-state and foundation-readiness assessment using the delivered
  F01/F02/F03a evidence; identify F03b's remaining contract without redoing the
  completed slice.
- Compare the proof routes and interfaces needed by the next unfinished slice,
  currently F03b. Resolve only choices that affect that increment; broader
  predicate representations remain later decisions when their dependencies exist.
- Specify exact proposed theorem statements, hypotheses, universes, action and
  equality laws, user interface, and required foundational dependencies.
- Propose concrete files under Package/, build/audit coverage, the matching
  LaTeX section, temporary consuming checks and counterexamples for the next
  manageable increment. Persistent examples remain reserved for case studies.
- Follow the design-review process to obtain agreement on that spec, then prepare
  the implementation plan. Do not request the settled freedom/location decisions
  again, or silently expand one increment into the full package.
- Update the new package roadmap and research notes with evidence and open issues.
  Keep historical, scratch-checked and integrated results distinct.

Use parallel agents for independent work when useful, with disjoint edit ownership.
Ask focused questions only for unresolved mathematical or user-interface choices
that materially change the result; continue independent work meanwhile.

Validation after implementation is approved

Check each new Package module and meaningful consumer, the registered Package
target and its actual import closure, representative #print axioms results and
an audit that includes the new declarations. Reject sorry/admit/custom axioms or
disabled kernel checking. Standard propext, Classical.choice and Quot.sound are
acceptable. Do not weaken theorem statements to make proofs compile.

Keep reference preservation checks separate: existing Nominal/Instances/Examples
builds and their audit can detect damage to the baseline, but cannot certify the
new Package implementation. Run git diff --check and documentation checks.
State commands actually run and distinguish cached builds, fresh project builds
and dependency bootstraps. Check the updated LaTeX mathematics against the actual
declarations and compile main.tex with generated files outside the source tree.
Documentation-only policy changes need no Lean or manuscript rebuild when those
sources are unchanged.

Finish with the concrete readiness/design artifacts and the exact next review
decision. Mark PKG-01 complete only when its reviewed interface, necessary
foundations, consumers, counterexamples and independent verification are delivered.
```
