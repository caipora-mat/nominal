# Nominal package roadmap

Last updated: 2026-10-05.
Branch: `fasapa/nominal-package`.
Baseline: `4279ba92efacd77b3b96e507631502272b489999`, with the existing working
tree preserved.

This is the standalone tracker for the new nominal-package research and
development phase. The [previous library roadmap](roadmap.md) retains the
completed core/Church–Rosser history; it is not the tracker for this phase.
The PKG IDs introduced during the architectural investigation remain stable.
Older A/P/M IDs may be used as historical cross-references, not as this document's
task structure.

The [architecture proposal](research/2026-10-05-package-architecture.md) explains
the alternatives and recommendation. The
[research brief](research/2026-10-05-nominal-package-brief.md) records user decisions.
This roadmap records sequence, dependencies, acceptance criteria and evidence.
The architecture and first implementation increment still await agreement.
Creating this document does not authorize package implementation.

## Objective and boundaries

Researchers should be able to declare first-order syntax with binders,
operations and ordinary Lean `Prop` judgments, then prove results through
generated nominal interfaces. Every mathematical guarantee must be justified
by proofs checked by Lean's kernel.

- Use classical Lean/Mathlib, actual quotients and noncomputable operations.
- Expose freshness and explicit induction avoidance; hide implementation
  packaging where proved automation can discharge its obligations.
- Initially target one atom sort, single/nested binders and multiple syntax
  categories. Specify mutual recursion, containers and universes explicitly.
- Preserve arbitrary-predicate fresh term and rule induction. Supported
  predicates are complementary infrastructure, not a restriction on all motives.
- Preserve the completed library, its public theory and the manual case study.
- No deadline or CI. Executable fresh-name generation is not required.
- Do not merge the old algebraic sketch or introduce the excluded
  syntax/unification branch. Generic algebraic theory must serve the package.

## Agreed case studies

| Study | Proposed acceptance result | Distinct purpose |
| --- | --- | --- |
| Lambda calculus | Replay open-term Church–Rosser through generated syntax, functions and judgments | Complete reference workflow; fresh rule induction, inversion and simultaneous substitution |
| First-order logic | Substitution admissibility for natural deduction, including universal introduction and existential elimination | Multiple categories, finite contexts and eigenvariable transport |
| Lambda calculus with `let` | Expansion/substitution compatibility and contextual reduction simulation into base lambda calculus | Binder scope covers the body but excludes the defining term |
| π-calculus | Transition equivariance and fresh bound-residual inversion; later a selected behavioral congruence theorem | A name can bind jointly across a transition label and continuation |
| μ-calculus | Proposed modal variant: positive substitution, alpha-invariant semantics and fixed-point unfolding | Positivity and semantic environments require contracts separate from binding |

All five studies were selected by the author. Lambda with `let` was selected
instead of an imperative-local language. The proposed first complete workflow
uses lambda and first-order logic; the other three are subsequent milestones.
Precise π transition semantics and the μ-calculus variant remain open.

## Status and evidence policy

**DONE** means the stated task's acceptance criterion is met, with evidence.
**TODO** means work has not been delivered. **IN PROGRESS** identifies an active
research or implementation task; it does not imply the architecture is approved.
Use checked boxes only for delivered results.

Distinguish existing integrated theorems, checked standalone probes, source
readings, mathematical analyses, proposed interfaces and user decisions.
Scratch proofs do not complete an integration task. Record the source revision,
commands actually run, build-cache conditions and remaining limitations.
Keep failed approaches and counterexamples linked to the relevant task.

## Dashboard and dependencies

| ID | Status | Dependencies | Deliverable |
| --- | --- | --- | --- |
| PKG-00 | DONE — research proposal; design review pending | Completed core/Church–Rosser baseline | Evidence-based architecture comparison, contracts, probes and article outline |
| PKG-01 | TODO — proposed first implementation increment | Architecture/increment agreement | Supported-predicate and quotient-predicate foundations |
| PKG-02 | TODO | Backend and grammar review | Manual syntax-carrier certificate with constructor/action/support laws |
| PKG-03 | TODO | PKG-02 | Fresh term induction and supported iteration |
| PKG-04 | TODO | PKG-02/03 | Multiple/direct mutual categories and finite-context infrastructure |
| PKG-05 | TODO | PKG-03/04 and required PKG-01 interface | Datatype/function commands and a distinct primitive-recursion contract |
| PKG-06 | TODO | PKG-03 and predicate/rule foundations | Certified fresh judgment induction and its generator |
| PKG-07 | TODO | PKG-05/06 | Complete generated lambda and FOL workflows |
| PKG-08 | TODO | PKG-07 | Lambda with let and expansion correctness |
| PKG-09 | TODO | PKG-07 and residual-binding contract | π-calculus case study |
| PKG-10 | TODO | PKG-07 and positivity/semantic contract | μ-calculus case study |
| PKG-11 | IN PROGRESS — outline delivered | Alongside every increment | Evolving article and claim-to-Lean evidence ledger |

PKG-02 can proceed independently of most predicate lemmas after its design is
approved. PKG-06 mathematical certification can start before command elaboration.
The three later case studies need not be executed serially when their foundations
are ready. Each implementation increment receives a bounded spec and plan;
this roadmap is not blanket implementation approval.

## Task contracts

### PKG-00 — Architectural investigation

- [x] Inspect current branch, history, working tree and completed lambda proofs.
- [x] Compare Pitts, Copello, Rocq, original Nominal, Nominal2 and current Lean
  predicate/induction principles, with source and verification limits.
- [x] Compare generic syntax, per-declaration generation and a staged hybrid.
- [x] Specify proposed grammar, generated guarantees, proof escape hatches and diagnostics.
- [x] Run bounded positive/negative Lean probes and inspect representative axioms.
- [x] Record the five studies, dependency order and article outline.

Delivered research is linked under [research artifacts](#research-artifacts).
Architecture approval is a subsequent decision, not a completed implementation.

### PKG-01 — Predicate foundations

- [ ] Select an explicit atom/action interface; test instance coherence and ordinary use.
- [ ] Prove/export the supported-subset/NFun correspondence and raw/quotient Prop bridge.
- [ ] Supply basic logical support, parameter/evaluation and Some/Any interfaces.
- [ ] Retain unsupported-predicate and fresh-selector counterexamples.
- [ ] Demonstrate that existing arbitrary-motive induction clients remain unchanged.

Accept when the reviewed API, ordinary consumers and negative examples compile,
with standard axioms only. A generic `local instance {α}` declaration is not a
solution to the checked registration failure; explicit fixed-atom `letI` works
in the probes. Do not add syntax commands or replace the case study in this task.

### PKG-02 — Carrier construction and mathematical contract

- [ ] Review the normalized atom/data/recursive/product/single-binder grammar.
- [ ] Construct one concrete carrier and prove its alpha equivalence and canonical action.
- [ ] Prove constructor equations/inversion, exact support and fresh representatives.
- [ ] Test lambda, let's mixed scope, a binder over a product and an empty datatype.
- [ ] Compare concrete proof/transport costs before committing to a universal carrier.

Accept a manual certificate for actual constructors, not merely an interpreted
arity or arbitrary type equivalence. If initiality is claimed, specify and prove
the actual structure map, map class, commuting equations and uniqueness.

### PKG-03 — Fresh induction and supported iteration

- [ ] Prove arbitrary-motive induction with context-generalized recursive hypotheses.
- [ ] Prove supported iteration, including binder compatibility, totality and uniqueness.
- [ ] Export guarded computation, support bounds and bound-independence laws.
- [ ] Recover current lambda reconstruction/substitution contracts without stronger assumptions.

Test nested binders, shadowing and fixed nominal parameters. Iteration supplies
recursive results; original-child access and dependent elimination are separate
contracts. FCB applies to the actual binding scope, not indiscriminately to all
fields of a constructor such as let.

### PKG-04 — Categories, mutual recursion and finite contexts

- [ ] Extend the construction to multiple categories and direct finite mutual recursion.
- [ ] Prove mutual alpha/action/support/induction contracts on a genuinely cyclic example.
- [ ] Provide the focused List action, support and nominal interface needed by FOL contexts,
  or explicitly choose a generated context category.
- [ ] Reject unproved recursive-container extensions with precise diagnostics.

An acyclic Term/Formula example alone does not verify mutual recursion.
Finite products and nested single binders are the proposed initial shapes;
arbitrary recursive List/Option/Array/Finset fields require additional contracts.

### PKG-05 — Datatype and function commands

- [ ] Generate the proved datatype contracts with predictable public declarations.
- [ ] Generate supported definitions with ordinary application and a certified NFun view.
- [ ] Check captures by elaborated expression/local identity and use theorem-backed registries.
- [ ] Prove a primitive recursor and test a function using original children and recursive results.
- [ ] Expose unsolved support/FCB/coverage/termination obligations; ensure failed commands
  leave no partial public package.

Accept generated substitution, higher-order consumers, `rw`/`simp`/`ext`, nested
scopes and consuming negative tests. Split the recursor and elaborator work into
separate implementation increments when needed. Do not advertise an iterator
as primitive recursion or promise unrestricted dependent elimination.

### PKG-06 — Judgment contracts and generation

- [ ] Establish a sufficient fresh-rule criterion: per-rule transport or a proved
  semantic refreshability theorem, with the intended relation preserved.
- [ ] Specify positive rules, side-condition certificates and bound/eigenvariable scopes.
- [ ] Retain every recursive derivation and its context-generalized IH.
- [ ] Prove fresh inversion and generate the certified interfaces.
- [ ] Validate unrestricted beta/parallel rules and FOL universal-introduction/
  existential-elimination rules; reject a nominated binder free in the conclusion.

Relation equivariance alone is insufficient. Renaming must transport all affected
premises and preserve the whole conclusion; transformed premises must be covered
by the IHs. If adding fresh-rule premises, prove equivalence with the original
judgment. Split the mathematical criterion and command implementation into
separate reviewable increments.

### PKG-07 — First complete workflow

- [ ] Generate lambda syntax, substitution and beta/parallel judgments.
- [ ] Replay simultaneous parallel substitution, diamond, closure correspondence,
  beta confluence, Church–Rosser and normal-form uniqueness for open contextual terms.
- [ ] Prove a constructor-commuting equivariant equivalence with existing `Term`,
  comparing substitution and relations while preserving the manual development.
- [ ] Generate FOL terms/formulas, substitution, finite contexts and natural deduction.
- [ ] Prove `Γ ⊢ φ → substContext x s Γ ⊢ substFormula x s φ`, with genuine
  eigenvariable refreshing and no hidden closedness assumption.
- [ ] Demonstrate nested avoidance, capture-forcing substitution, arbitrary motives,
  primitive recursion, useful rewriting and meaningful failure diagnostics.

Acceptance requires proofs through the generated public interfaces. Transporting
the existing Church–Rosser theorem alone does not constitute replaying its proof.
Syntax-only generation or formula substitution composition alone is insufficient.
Run complete supported builds and generated clients, inspect theorem statements,
audit axioms and imports, and keep the original clients passing.

### PKG-08–PKG-10 — Remaining case studies

- [ ] **PKG-08:** specify contextual lambda/let reduction; prove expansion is
  alpha-compatible, commutes with substitution, and sends each let-language step
  to beta-star reduction. Include a binder occurring freely in the defining term.
- [ ] **PKG-09:** select π transition semantics and residual representation; prove
  transition equivariance and fresh bound-residual inversion with a substantive
  scope-extrusion client, then specify and prove one behavioral congruence result.
- [ ] **PKG-10:** select the μ-calculus variant and positivity criterion; prove
  substitution, alpha-invariant interpretation and the chosen fixed-point laws.
  Arbitrary semantic valuations must not receive unsupported nominal certificates.

Each case gets its own language/theorem specification and proof obligations
before implementation. Bisimulation/coinduction and fixed-point semantics are
additional semantic work, not automatic consequences of datatype generation.

### PKG-11 — Research writing

- [x] Propose a sustainable notes/manuscript organization and detailed article outline.
- [ ] Create and maintain the statement-to-Lean claim ledger as increments are delivered.
- [ ] Develop article sections alongside proofs and user-level examples.
- [ ] Preserve failed approaches, counterexamples, exact versions and verification limits.
- [ ] Review consistency of claims, contracts and implementation at each milestone.

Follow the [article plan](research/2026-10-05-article-plan.md). Do not claim
novelty, publication readiness or completed external builds without evidence.

## Open decisions and next step

1. Review the staged-hybrid architecture and select the first implementation
   increment. PKG-01 is recommended; PKG-02 is the carrier-first alternative.
2. Approve the restricted grammar and its gated direct-mutual target.
3. Select π transition semantics and the precise μ variant before those studies.

No implementation increment has yet been approved. The current instruction is
to establish this separate roadmap before proceeding.

## Research artifacts

- [Architecture and alternatives](research/2026-10-05-package-architecture.md).
- [Predicates, quotient descent and induction](research/2026-10-05-predicate-foundations.md).
- [Isabelle and rule-induction source comparison](research/2026-10-05-isabelle-comparison.md).
- [Backend grammar, feasibility and counterexamples](research/2026-10-05-backend-comparison.md).
- [Proposed user syntax and generated contracts](research/2026-10-05-package-contracts.md).
- [Article outline and evidence workflow](research/2026-10-05-article-plan.md).

## Work log and verification evidence

### 2026-10-05 — PKG-00 research proposal

The architectural investigation delivered the linked notes and five standalone
probes. These remain uncommitted research artifacts outside supported imports.
The original library sources and dependencies were unchanged.

Evidence from that investigation, not newly rerun for this documentation edit:

- `lake build Nominal Instances Examples` passed, 1,033 jobs using existing caches.
- Direct tutorial compilation passed; direct axiom audit checked 1,859 project
  declarations with only `propext`, `Classical.choice` and `Quot.sound`.
- All five `docs/research/probes/*.lean` files passed investigator and coordinator
  checks, with guarded expected failures and standard positive-result axioms.
- Import coverage reached all 37 library and 15 example modules.
- Source versions and external verification limits are recorded in the notes.
  No external Isabelle/Rocq/Agda build or clean dependency bootstrap was performed.
- Cross-review clarified rule certificates, scoped let FCB, binder-renaming
  freshness premises, fixed-atom truth-action selection and Some/Any support.

### 2026-10-05 — Separate package roadmap

At the author's request, created this standalone roadmap, retained PKG-00–PKG-11,
and removed only the package-phase banner/appendix added to the previous roadmap
during the preceding investigation. Its original contents were checked against
the preserved pre-investigation snapshot. Updated navigation in the research
brief, architecture proposal, article plan and README.

This change is documentation only. Verification consists of local links,
Markdown structure, whitespace/diff checks and preservation checks. It does
not introduce or verify package implementation, and does not rerun Lean builds.

Those checks passed: 12 Markdown files and 144 local links, with clean
whitespace/fences and `git diff --check`. The previous roadmap matches its
pre-investigation snapshot byte-for-byte; production/configuration hashes are
unchanged.
