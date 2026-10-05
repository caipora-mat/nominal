# Nominal package research

This folder contains research for a new nominal package on
`fasapa/nominal-package`. The completed library at
`4279ba92efacd77b3b96e507631502272b489999` is the original evidence baseline.
The policy revision described here was made with HEAD
`7fed53a2e5fc67379f86f085515e310e7c1fddb7`; always inspect the actual checkout
before starting a new task.

## Architectural freedom

**Settled user decision:** the existing infrastructure is an optional source of
learning and reusable results. Any infrastructure required by the new package
may be developed from scratch: atoms, permutations, actions, support, freshness,
functions, predicates, abstraction, quotients, induction, recursion and tooling.

Compare reuse, adaptation and independent implementation by mathematical
correctness, clarity, usability, proof obligations and maintenance cost. Neither
reuse nor rewriting is mandatory. Existing representations, typeclasses, API
names, module structure, universe restrictions, seals and proof strategies do
not constrain a new design. Backward compatibility with the old implementation
is not an acceptance requirement.

This freedom is subject to the author's [Mathlib-first policy](#mathlib-first):
replace the old nominal implementation as useful, while building on appropriate
existing Mathlib infrastructure.

Preserve the existing source and completed Church–Rosser development as a
reference. Learn from its successful clients, failed approaches, counterexamples
and implementation costs. Preserve intended mathematical guarantees and useful
user-level reasoning, including arbitrary-motive fresh induction. A different
proof or interface is allowed; weakening a theorem merely to make it compile
still needs explicit mathematical justification.

A previous build or proof certifies the representation it actually checked.
It does not automatically certify a new representation. Optional comparison
maps to the old implementation need their own laws; a bare type equivalence
does not establish constructor or action compatibility. Such maps are one
verification technique, not mandatory compatibility infrastructure.

This decision supersedes earlier reuse-first wording and inherited API/layout
constraints in these notes and in general repository guidance for work on the
new package. It does not authorize deleting or refactoring the reference library.
Historical findings and source citations remain evidence with their original
assumptions, dates and verification limits.

## Mathlib-first

**Settled user decision:** always look for and use suitable infrastructure in
the pinned Mathlib before implementing general-purpose mathematics yourself.
Search local Mathlib source, inspect the exact declarations and test their
fit when needed. Prefer existing definitions, instances and lemmas, including
their specializations or small proof-backed adapters, over duplicate theory.

Custom nominal constructions remain appropriate when existing APIs do not meet
the mathematical or interface contract. Record the useful candidates and the
specific gap at the increment level; neither a superficially similar name nor
one failed search establishes the answer. Check hypotheses, universes and action
coherence, retain theorem strength, and do not silently change dependency pins.
Freedom to replace `Nominal/` does not imply rebuilding Mathlib's group/action,
set, quotient or other general infrastructure. The
[roadmap](../nominal-package-roadmap.md#mathlib-first-development) makes this a
design and completion criterion for every increment.

## Implementation location

**Settled user decision:** all new implementation belongs under top-level
`Package/`, alongside `Nominal/`. This includes any newly implemented foundations,
nominal interfaces, definitions/induction infrastructure and package tooling.
The reference library remains in `Nominal/` and its existing case study in
`Instances/`.

Select `Package/` subdirectories, namespaces and public entry points in the
foundation design. A conventional root `Package.lean` umbrella and the minimal
Lake registration may be added when the build-boundary task is approved. New
client examples and audits should have explicit Package coverage. Do not place
new foundations under `Nominal/` or accidentally rely on old library targets to
validate them. An import from the reference library is an optional, documented
dependency decision, not an implicit foundation.

No implementation directory, target or production Lean module is created by
this documentation revision. The agreed location does not decide the backend.

## Scope and order of work

The active tracker is [the package roadmap](../nominal-package-roadmap.md).
The earlier [library roadmap](../roadmap.md) preserves first-deliverable history
and is not reused for this phase.

Foundation decisions and build/action/support prerequisites come before PKG-01
when its selected design needs them. PKG-01 provides predicate foundations;
it does not implicitly include rebuilding the entire library. Record missing
prerequisites, their contracts and acceptance examples as explicit roadmap
tasks. The revised roadmap preserves existing PKG IDs and adds foundation tasks.

Classical Lean/Mathlib, ordinary `Prop`, kernel-checked guarantees, one atom sort,
single/nested binders, multiple syntax categories, correctness first and no CI
remain settled. The five selected case studies are lambda calculus, first-order
logic, lambda calculus with let, π-calculus and μ-calculus. Their mathematical
acceptance criteria guide architecture without prescribing the old implementation.

## Reading guide

| Document | Role |
| --- | --- |
| [Research brief](2026-10-05-nominal-package-brief.md) | User requirements and decisions; R11/R12 record architectural freedom and Package location |
| [Architecture proposal](2026-10-05-package-architecture.md) | Alternatives, candidate design and unresolved mathematical obligations |
| [Initial propositions note](2026-10-05-propositions-and-induction.md) | Earlier evidence and questions; historical limits are kept explicit |
| [Predicate foundations](2026-10-05-predicate-foundations.md) | Detailed source/theorem comparison, predicate representations and checked probes |
| [Isabelle comparison](2026-10-05-isabelle-comparison.md) | Pinned source readings and fresh-rule criteria |
| [Backend comparison](2026-10-05-backend-comparison.md) | Candidate grammar, construction alternatives and historical counterexamples |
| [Client contracts](2026-10-05-package-contracts.md) | Mathematical user contracts and proposed syntax; old declarations are examples |
| [Article plan](2026-10-05-article-plan.md) | Research-writing organization and statement-to-proof evidence workflow |
| [PKG-01 start prompt](pkg-01-start-prompt.md) | Fresh-context handoff that checks prerequisites before predicate implementation |
| [Current foundation readiness](2026-10-05-pkg01-readiness.md) | F01–F05 evidence, representation comparison and exact proposed predicate contracts at `76966b1` |
| [Pinned algebraic source investigation](2026-10-05-algebraic-source-investigation.md) | Direct declaration review, dispositions and reproduced counterexamples |
| [Predicate design probes](2026-10-05-predicate-design-probes.md) | Reproducible new scratch sources, including a Mathlib-only action experiment |
| [Discrete representation investigation](2026-10-05-discrete-representation.md) | Mathematical counterpart, structure/def/abbrev comparison, action inference and concrete Mathlib reuse |
| [First foundation specification](../superpowers/specs/2026-10-05-package-foundation-kernel-design.md) | Approved F02 + F03a boundary |
| [First implementation plan](../superpowers/plans/2026-10-05-package-foundation-kernel.md) | Approved native execution; incorporates removal of standalone Package examples |
| [F03b controlled-swap specification](../superpowers/specs/2026-10-05-package-controlled-swaps-design.md) | Approved public statements, Mathlib proof route, article obligations and acceptance checks |
| [F03b implementation plan](../superpowers/plans/2026-10-05-package-controlled-swaps.md) | Completed native execution with concurrent LaTeX work and clean independent review |
| [Package foundation interface](../../Package/README.md) | F02/F03a kernel plus working-tree F03b results, import policy and validation commands |
| [LaTeX article](../article/main.tex) | Foundation mathematics, actual public declarations and verification evidence |

The earlier architecture prompt was removed in `76966b1`; the table now points
to the existing handoff and current review artifacts. F01 is in progress, with
its required F02 + F03a boundary approved. Later layer proposals remain open.
The implementation plan was approved for native execution. F02 and F03a have
implementation and validation evidence, with a clean independent final review;
that preceding work was committed at `3d2196a` during F03b design review.
The author requires all article content in LaTeX under `docs/article/`
and reserves persistent usage examples for future case studies. The current
Package foundation has no standalone Examples layer.

## Article and implementation advance together

For every substantive Package increment, its spec/plan includes the corresponding
LaTeX sections under `docs/article/`. Develop the mathematical statements and
explanations alongside the Lean proofs, then reconcile hypotheses, declarations,
limitations and verification evidence and compile the article before closing the
increment. PKG-11 coordinates this requirement throughout development; manuscript
writing is not deferred until the package is finished. The
[article plan](2026-10-05-article-plan.md#concurrent-writing-is-part-of-delivery)
specifies the completion rule.

F02/F03a are delivered with their article sections. F03b now implements controlled
swap factorization, avoidance for arbitrary `Set A`, and the selected-action
implication/equivalence, with corresponding LaTeX exposition. The author approved
native execution; independent final review found no issues. The direct production audit covers
81 declarations in three defining modules with only standard axioms. Coverage
reaches four production source modules and one audit module. F04 support/freshness,
F05 interfaces and PKG-01 remain future work; the new results add no action instance.

## Scratch evidence

Files under `probes/` retain the definitions/imports used in their experiments.
They are preserved research evidence, not a required Package design. This policy
revision changes their interpretation in the research plan, not their proof text.

The five probes documented by the initial investigation were independently
checked then; see their notes for exact commands and axioms. At the start of
this revision, `PredicateInterface.lean` and `PredicateSomeAny.lean` were existing
untracked work. They were preserved; this documentation edit does not claim a
new compilation result for either. Inspect current contents and evidence before
using or promoting any probe. New implementation must receive its own build,
example and axiom validation under the selected Package structure.

The subsequent F01 session at `76966b1` reran all seven existing probes without
editing them, including both previously untracked predicate files. The
[current readiness note](2026-10-05-pkg01-readiness.md) and new probe record
separate that evidence from the earlier runs. New scratch sources remain
reproducible in the dated notes and are not Package production modules.
