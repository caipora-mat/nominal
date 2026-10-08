# Nominal package research

This folder contains research for a new nominal package on
`fasapa/nominal-package`. The completed library at
`4279ba92efacd77b3b96e507631502272b489999` is the original evidence baseline.
The policy revision described here was made with HEAD
`7fed53a2e5fc67379f86f085515e310e7c1fddb7`; always inspect the actual checkout
before starting a new task.

## Current Package state

F04a/F04b were committed at `68956dd23066c7c5c647345e5598b859ff97a10c`;
F04c and its general-freshness extension are committed at
`9c1cb9aa2f9f69d8d801a9864a9f0220b92ea62a`. They supply the delivered support,
nominality, canonical instances and freshness foundations. Earlier
uncommitted-delivery descriptions below record their original sessions.

Under the approved F04d specification and native plan, commit
`32f3dba551761881409bbc7453054e214e582269` delivers general explicit
quotient-action constructors, the canonical nominal
projection/support interface, general surjective nominality transfer and the
supported-fiber characterization. The exact quotient intersection formula
does not imply an exact-support representative. Current proof/consumer checks
pass with matching exposition in `docs/article/sections/quotients.tex`.
Integrated validation and the fresh independent final review pass with no
findings; F04d and the reconciled PKG-F04 are delivered and committed. Evidence
is tracked in the [active roadmap](../nominal-package-roadmap.md).
F05 production interfaces, native implementation checks and independent final
review are complete with no findings, committed at
`3c9d8dc527f7705b24c0308a2527e659ae933874`. The new
[PKG-01 investigation](2026-10-07-pkg01-predicate-foundations.md) starts from that
clean checkout. Its [written specification](../superpowers/specs/2026-10-07-package-predicate-foundations-design.md)
was approved on 2026-10-08; its [implementation plan](../superpowers/plans/2026-10-08-package-predicate-foundations.md)
is approved for native execution. Task 8 and the independent whole-change
review now pass; PKG-01 is complete, uncommitted. This run stops here. Tasks 1–3 deliver phase 01a in the working tree: ordinary predicate logic, direct
supported predicates and views, Boolean algebra, bundled logical/quantified
operations, individually certified sections and supported collections. The
investigation compares all four predicate representations and supplies three
review units covering logical calculus, pullback/descent and fresh quantification.
The author selected scoped `И` notation alongside the named cofinite operation.
On 2026-10-08 the author also selected choice 1, the direct predicate record
with proof-only support, then approved the full written specification.
Tasks 4–5 complete phase 01b: general pullback
reflection, ordinary/supported descent, explicit compatible actions, exact support
and individual-context freshness. Tasks 6–7 complete phase 01c: cofinite truth,
scoped notation, supplied-bound Some/Any, contexts and bundled fresh projection,
with precise logical/uniform-support laws and proved negative boundaries. Task 8
verifies all phases together through public consumers, README extracts, audit,
imports and the article. Independent review found no material issue; its one
minor current-status inconsistency was corrected. Separate delivery and
preservation evidence is recorded in the active roadmap and approved plan. Object-support
bounds and fiber intersections remain distinct from predicate support reflection.
The 2026-10-07 [F05 investigation](2026-10-07-function-space-foundations.md)
reassesses the older direct-SPred proposal against completed F04, pinned Mathlib
and Pitts. Its [written specification](../superpowers/specs/2026-10-07-package-function-space-design.md)
recommends ordinary certificates, full conjugation objects and supported bundles
with proved bridges. The author approved that specification on 2026-10-07.
The [implementation plan](../superpowers/plans/2026-10-07-package-function-space.md)
was approved for native execution. Code, public consumers, audit, article and
independent final review pass with no findings. It includes the author's context-bound idea as
an intended consumer of explicit-bound laws; context-scanning tooling is deferred.
At the author's request, the [broader Urban study](2026-10-07-urban-nominal-techniques.md)
also informs future carrier, selected-avoidance induction, binder descent,
primitive recursion and rule-induction criteria. It distinguishes the supplied
2008 author manuscript from current Isabelle and records two manuscript slips.
These are research/task refinements, not implemented or approved later APIs.

The author subsequently requested Pitts' general support-disjointness relation
and a preference for natural mathematical generalizations. The current extension
uses `Fresh A x y`, elementwise `hx.FreshWith hy`, and the retained atom helper
`hx.Fresh a`. Three independent investigations and their checked proposals are
recorded in [the generalization review](2026-10-06-foundation-generalizations.md).
The freshness extension, article, integrated checks and independent final review
are complete; a minor stale proof-description sentence was corrected.
The generality preference is also recorded in AGENTS.md and decision R15.
F04d adopts the surjective nominality part of that investigation and uses the
existing Mathlib hom bundle for its scalar projection. F05 subsequently adopts
scalar injective support reflection, same-group arbitrary-set support transport
and the Equivariant/MulActionHom bridge. Remaining generalizations retain their
research status; the supported-fiber theorem is separately approved F04d work.

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
Prefer the natural general statement and derive specialized APIs from it.
Theoretical reuse and stability are benefits in their own right; do not require
a particular client before considering a sound useful generalization.
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
| [Current PKG-01 investigation](2026-10-07-pkg01-predicate-foundations.md) | Delivered F05/Mathlib inventory, four representation candidates, exact contracts and new Package-based probes |
| [Approved PKG-01 written specification](../superpowers/specs/2026-10-07-package-predicate-foundations-design.md) | Full logical/descent/Some/Any scope and phase acceptance, approved 2026-10-08 |
| [Approved PKG-01 native plan](../superpowers/plans/2026-10-08-package-predicate-foundations.md) | Eight tasks, exact public contracts and consuming checks; Tasks 1–8 and all phases complete uncommitted, with independent whole-change review |
| [Architecture proposal](2026-10-05-package-architecture.md) | Alternatives, candidate design and unresolved mathematical obligations |
| [Initial propositions note](2026-10-05-propositions-and-induction.md) | Earlier evidence and questions; historical limits are kept explicit |
| [Predicate foundations](2026-10-05-predicate-foundations.md) | Detailed source/theorem comparison, predicate representations and checked probes |
| [Isabelle comparison](2026-10-05-isabelle-comparison.md) | Pinned source readings and fresh-rule criteria |
| [Backend comparison](2026-10-05-backend-comparison.md) | Candidate grammar, construction alternatives and historical counterexamples |
| [Client contracts](2026-10-05-package-contracts.md) | Mathematical user contracts and proposed syntax; old declarations are examples |
| [Article plan](2026-10-05-article-plan.md) | Selective publication policy, thematic outline and internal evidence workflow |
| [PKG-01 start prompt](pkg-01-start-prompt.md) | Fresh-context handoff that checks prerequisites before predicate implementation |
| [Current foundation readiness](2026-10-05-pkg01-readiness.md) | F01–F05 evidence, representation comparison and exact proposed predicate contracts at `76966b1` |
| [Pinned algebraic source investigation](2026-10-05-algebraic-source-investigation.md) | Direct declaration review, dispositions and reproduced counterexamples |
| [Predicate design probes](2026-10-05-predicate-design-probes.md) | Reproducible new scratch sources, including a Mathlib-only action experiment |
| [Discrete representation investigation](2026-10-05-discrete-representation.md) | Mathematical counterpart, structure/def/abbrev comparison, action inference and concrete Mathlib reuse |
| [First foundation specification](../superpowers/specs/2026-10-05-package-foundation-kernel-design.md) | Approved F02 + F03a boundary |
| [First implementation plan](../superpowers/plans/2026-10-05-package-foundation-kernel.md) | Approved native execution; incorporates removal of standalone Package examples |
| [F03b controlled-swap specification](../superpowers/specs/2026-10-05-package-controlled-swaps-design.md) | Approved public statements, Mathlib proof route, article obligations and acceptance checks |
| [F03b implementation plan](../superpowers/plans/2026-10-05-package-controlled-swaps.md) | Completed native execution with concurrent LaTeX work and clean independent review |
| [F04a finite-support specification](../superpowers/specs/2026-10-05-package-finite-support-design.md) | Approved Mathlib support specialization, exact assumptions, proof strategies and article/verification obligations |
| [F04a implementation plan](../superpowers/plans/2026-10-05-package-finite-support.md) | Completed native execution with concurrent article work and clean independent final review |
| [F04b least-support specification](../superpowers/specs/2026-10-06-package-least-support-design.md) | Approved proof-only nominality and elementwise/carrier least-support contracts |
| [F04b native implementation plan](../superpowers/plans/2026-10-06-package-least-support.md) | Completed native execution with concurrent article work and clean independent final review |
| [F04c specification](../superpowers/specs/2026-10-06-package-canonical-freshness-design.md) | Approved canonical-instance, exact-support, atom-freshness and avoidance interfaces |
| [F04c native implementation plan](../superpowers/plans/2026-10-06-package-canonical-freshness.md) | Approved execution with concurrent LaTeX, meaningful consumers and one independent final review |
| [Package foundation interface](../../Package/README.md) | Current canonical support/freshness interfaces, import policy and validation commands |
| [LaTeX article](../article/main.tex) | Research exposition of the system, mathematics and relevant Lean correspondence |

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

The article is intended as a selective research publication. Explain central
definitions, theorems and proof ideas, architectural meaning and choices, limits
and counterexamples, with grounded discussion of relevant systems and theories.
Select the details needed for that argument; avoid a complete API inventory or
routine-proof catalogue. Do not manufacture novelty or unsupported comparisons.

Keep development-stage/task IDs, work logs, status/delivery and approval stories,
branch/commit bookkeeping, agent assignments, review verdicts and audit/build
commands, outcomes, counts and cache conditions out of the manuscript. Preserve
them in this research folder and the roadmap. Logical assumptions, mathematical
dependencies, substantive limitations and relevant Lean APIs remain scientific
content. This distinction supersedes earlier manuscript-evidence instructions.

For every substantive Package increment, its spec/plan includes the corresponding
LaTeX work under `docs/article/`. Develop selected mathematical statements and
explanations alongside the Lean proofs, then reconcile hypotheses, relevant
declarations and limitations and compile the article before closing the increment.
Record the checks in the roadmap. Routine implementation changes may need no new
manuscript text. PKG-11 coordinates this requirement throughout development;
manuscript writing is not deferred until the package is finished. The
[article plan](2026-10-05-article-plan.md#concurrent-writing-is-part-of-delivery)
specifies the completion rule and [publication content policy](2026-10-05-article-plan.md#publication-content-policy).

The following earlier delivery records retain their original verification and
working-tree states; the current state is summarized above.

F02/F03a are delivered with their article sections. F03b now implements controlled
swap factorization, avoidance for arbitrary `Set A`, and the selected-action
implication/equivalence, with corresponding LaTeX exposition. The author approved
native execution; F03b's independent final review found no issues. The subsequent
F04a extension now passes a direct production audit of 104 declarations in four
defining modules with only standard axioms. Coverage reaches five production source
modules and one audit module. Its finite-support calculus adds no action instance.

The F04a design session inspected a clean tree at
`34a83358739ab962e2b9d2035a21d67b2a896071`, which commits F03b. The
[tracker](../nominal-package-roadmap.md#pkg-f04--support-freshness-and-required-constructions)
now splits F04 into finite support calculus (F04a), nominality/least support
(F04b), canonical instances/freshness (F04c), and canonical equivariant quotients
(F04d). The [F04a written specification](../superpowers/specs/2026-10-05-package-finite-support-design.md)
and its native implementation plan were approved. F04a's 18 public declarations
and meaningful temporary consumers now check, with corresponding mathematics in
`docs/article/sections/support.tex`, `sec:finite-support`. Independent final review
found no issues; F04a is delivered, uncommitted.

The author subsequently approved the F04b specification and native plan.
`Package/Foundations/Nominal.lean` now supplies proof-only `Nominal A X`,
elementwise `hx.support` and carrier `support A x`, with witness agreement,
leastness, transport, empty-support characterization and equivariant-image
inclusion. All 19 approved declarations and six temporary public-import files
check; the direct audit covers 132 declarations from five defining modules
with standard axioms only, and source coverage reaches six production modules
including the root plus one audit. The concurrent `sec:least-support` article
section is reconciled and compiled. Independent final review found no Critical,
Important or Minor issues and independently reran code/article/preservation
checks. F04b is delivered, uncommitted. F04c/F04d, F05 and PKG-01 remain future work.

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
