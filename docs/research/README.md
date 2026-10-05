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
| [Architecture research prompt](nominal-package-brainstorming-prompt.md) | Reusable prompt updated for current decisions |
| [PKG-01 start prompt](pkg-01-start-prompt.md) | Fresh-context handoff that checks prerequisites before predicate implementation |

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
