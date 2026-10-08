# Predicate foundations after F05

Date: 2026-10-07. **Historical architectural investigation and bounded scratch
evidence, followed by the separately authorized production delivery.** Task: PKG-01. The corresponding
[written specification](../superpowers/specs/2026-10-07-package-predicate-foundations-design.md)
was approved by the author on 2026-10-08. The initial investigation authorized
research/documentation only; the subsequent written-spec approval authorizes
the [implementation plan](../superpowers/plans/2026-10-08-package-predicate-foundations.md),
approved for native execution. Task 8 now completes whole-specification
integration and the independent final review, and the run stops here.
Production implementation is authorized by that subsequent plan approval;
commits remain unauthorized. Tasks 1–7 and phases 01a–01c are implemented and
verified in the working tree. Task 8, all specification criteria and the
independent whole-change review also pass. PKG-01 is complete, uncommitted.

**2026-10-08 decision:** the author selected choice 1, the direct predicate
record with proof-only support, then approved the full written specification
and three-phase scope, then approved the implementation plan for native execution
in fresh contexts. The comparisons below explain those decisions; current and
historical delivery evidence is recorded separately in the active roadmap.

Inspected branch: `fasapa/nominal-package`. HEAD:
`3c9d8dc527f7705b24c0308a2527e659ae933874` (`some predicate + function support`).
The index and working tree were clean at the first inspection. This commit
contains the F05 delivery; earlier descriptions of it as uncommitted refer to
the preceding session. F04d is committed at `32f3dba`, F04c at `9c1cb9a`,
F04a/F04b at `68956dd`. No completed foundation is reopened.

Lean is `v4.34.1`; pinned Mathlib is
`d13f23b723b8a846827a245b89c10fc7d3f11612` (`v4.34.1`). All Mathlib findings
below concern that source, not a moving upstream version. The
[package roadmap](../nominal-package-roadmap.md) is the active tracker;
the old roadmap and reference development remain untouched.

## Investigation checklist and intended outcome

- [x] Inspect branch/history/status, delivered source and latest delivery records.
- [x] Read the requested foundation, predicate, induction, generalization and
  article investigations, distinguishing historical proposals from current APIs.
- [x] Compare all four representation candidates against current F05 and Mathlib.
- [x] Investigate logical closure, pullback/descent and fresh quantification
  independently, with disjoint probe ownership.
- [x] Retain decisive bounded positive/negative probes and their axiom checks.
- [x] Prepare exact contracts, phase proposal and scientifically useful LaTeX.
- [x] Self-review the specification and reconcile the tracker with current source.
- [x] Author selects direct predicate storage on 2026-10-08.
- [x] Author approves the written specification on 2026-10-08.
- [x] Prepare the eight-task implementation plan with full acceptance coverage.
- [x] Author approves the plan and selects native execution, one task per fresh context.

Success means a coherent ordinary-Prop interface with selected actions,
independent universes, minimal hypotheses and elementwise support evidence.
Unsupported predicates stay legal. F05 remains the approved hybrid of ordinary
certificates, full conjugation objects and supported values. The final predicate
carrier is a distinct design choice; the historical argument that general
supported functions were unavailable no longer applies.

## Current-source inventory

| Source and declarations | Delivered now | Integration and boundaries |
| --- | --- | --- |
| [ActionSupport](../../Package/Foundations/ActionSupport.lean), `supports_map_iff`, `supports_smul_iff` | Arbitrary-set sufficient support through scalar-preserving injections; same-group conjugation transport | Scalar invariant_pullback_iff now requires only SMul; no parallel support definition |
| [FunctionAction](../../Package/Foundations/FunctionAction.lean), `FunctionObject`, `curryEquiv` | Full conjugation carrier, FunLike, application/composition/pairing/curry; action uses DivisionMonoid | precomp and arbitrary-set supports_precomp_iff now reuse the existing carrier and support injection theorem |
| [FunctionSupport](../../Package/Foundations/FunctionSupport.lean), `SupportsMap`, `FinitelySupportedMap`, section/evaluation laws | Ordinary map certificates and full-object support correspondence; elementwise parameter calculus | No new general map hierarchy is needed |
| [PredicateSupport](../../Package/Foundations/PredicateSupport.lean), `SupportsPred`, `FinitelySupportedPred`, `renamePred` | Ordinary logical certificates, inverse precomposition, monotonicity and finite renaming | Ordinary closure/quantifiers are in PredicateLogic; pullback reflection and Some/Any are delivered |
| Same module, `predicateObjectEquiv`, `supportsPred_iff`, `supportsPred_iff_supportsMap`, `supportsPred_iff_set` | Proved ordinary predicate/discrete-function/Set-image bridges | SupportedPredicate restricts these views; ordinary/supported descent is now delivered |
| Same module, `SupportsPred.precomp`, `.section`, `supportsPred_section_of_invariant`, `supportsPred_eq_iff` | Precomposition and fixed-parameter bounds; equality support, including exact least support of the equality object | Reuse for logical constructors and Some/Any contexts; fixed parameter support is not equivariance |
| [SupportedFunction](../../Package/Foundations/SupportedFunction.lean), `SupportedMap`, `supports_iff`, `curryWithSections` | Proof-field supported functions, FunLike, nominality without nominal source/target, parameter fixing and admissible currying | Its specialization retains discrete truth; SupportedPred supplies a separate Prop-facing record and named map view |
| [SupportedPredicate](../../Package/Foundations/SupportedPredicate.lean), `SupportedPred`, `mapEquiv`, `subsetEquiv` | Direct proof-field record, one Prop-valued FunLike, inverse-precomposition action, nominality, exact support views, supported-subset BooleanSubalgebra and transferred BooleanAlgebra | Reused by SupportedPredicateLogic for bundled operations; no second Boolean instance |
| [Support](../../Package/Foundations/Support.lean), [Nominal](../../Package/Foundations/Nominal.lean) | Finite bounds, individual supportedness, proof-only nominality, individual/carrier least support and witness agreement | No duplicate support selection is warranted for predicates |
| [SupportedPredicateLogic](../../Package/Foundations/SupportedPredicateLogic.lean) | Boolean/order computation, precomposition, individual sections, all/ex, supported collections, simultaneous actions and sufficient/least bounds | Phase 01a complete; reused by SupportedPredicateDescent and SupportedPredicateFresh |
| [Freshness](../../Package/Foundations/Freshness.lean) and [Canonical](../../Package/Foundations/Canonical.lean) | General support-disjointness freshness, atom specialization, canonical support and elementwise finite avoidance | Fresh quantification is a different operation; `Fresh` is already occupied |
| [QuotientAction](../../Package/Foundations/QuotientAction.lean) | Explicit scalar/monoid quotient constructors and projection laws | Use these exact selected actions for supported descent |
| [Quotient](../../Package/Foundations/Quotient.lean), `equivariant_mk`, `support_eq_iInter` | Canonical nominal projection, object-support bounds and supported-fiber characterization | PredicateDescent and SupportedPredicateDescent now provide the distinct predicate correspondence |
| [PredicateDescent](../../Package/Foundations/PredicateDescent.lean) | Action-free Compatible, Mathlib-backed ordinary equivalence, computation/inverses/obstruction, canonical quotient support and renaming, ordinary logical compatibility | Complete; ordinary unsupported predicates and quotient induction remain legal |
| [SupportedPredicateDescent](../../Package/Foundations/SupportedPredicateDescent.lean) | Supported pullback, explicit compatible action/nominality, equivalence/inverses/actions, exact support, individual-context freshness and logical preservation | Phase 01b complete; no dependent data/binder descent or second Boolean algebra |
| [FreshQuantifier](../../Package/Foundations/FreshQuantifier.lean) | Ordinary cofinite truth/scoped notation, supplied-bound Some/Any, classification/decision, joint support, uniform interchanges and individual contexts | No SupportedPred import; no global support assumption on ordinary predicates |
| [SupportedPredicateFresh](../../Package/Foundations/SupportedPredicateFresh.lean) | Bundled fresh projection with application/action/bound laws and atom-predicate freshness | Phase 01c complete; least-support conveniences add infinitude |
| [Public root](../../Package.lean) and [audit](../../Package/Tests/AxiomAudit.lean) | All delivered foundations exported, production-origin audit and separate import coverage | Future production additions need their own root/coverage/audit integration |

The F05 baseline `lake build Package +Package.Tests.AxiomAudit` succeeded using cached
project/dependency artifacts. Its separate direct audit checked 573 production
declarations from 14 defining modules, with only `propext`, `Classical.choice`,
`Quot.sound`. Import coverage reaches all 15 production source modules and the
separate audit. This records the F05 inputs; subsequent PKG-01 delivery checks
are in the execution records below and in the active roadmap.

## Pinned Mathlib inventory and actual gaps

| Pinned source | Reusable result | Nominal/interface use and delivery |
| --- | --- | --- |
| `Mathlib/Order/BooleanSubalgebra.lean:25,128` | Boolean subalgebra and inherited subtype Boolean algebra | Closure delivered by PredicateLogic and supportedSets |
| `Mathlib/Order/BooleanAlgebra/Basic.lean:631,662` | `Function.Injective.booleanAlgebra`, `Equiv.booleanAlgebra` | Transferred along subsetEquiv in SupportedPredicate; no manual Boolean axioms |
| `Mathlib/Data/FunLike/Basic.lean` | Coercion injectivity, congruence and extensionality | Delivered in SupportedPred with one ordinary projection and Iff ext |
| `Mathlib/Data/Setoid/Basic.lean:333,340` | `Setoid.liftEquiv`, `lift_unique` | Adapt equality-compatible functions to Iff-compatible predicates using propext |
| `Mathlib/Logic/Equiv/Basic.lean`, `Equiv.subtypeEquivRight` | Change a subtype's proof condition by an equivalence | Reuse for the compatibility formulation and restrict to support certificates |
| `Mathlib/Logic/Function/Basic.lean:840` | `Function.FactorsThrough` | Predicate compatibility adapter; quotient lift needs no choice-based extension |
| `Mathlib/Data/Quot.lean`, Lean `Init/Core.lean` | Lift computation, soundness/exactness, surjectivity and dependent recursors | No new quotient mechanism; data-valued dependent sections still need coherence |
| `Mathlib/Order/Filter/Cofinite.lean:49,57,89,96,254,264` | `eventually_cofinite`, `cofinite_neBot`, finite avoidance, injective tendsto/comap reindexing | Atom support implies constancy off the supplied bound; derive Some/Any from this |
| `Mathlib/Order/Filter/Basic.lean`, `Finite.lean` | Eventually conjunction, monotonicity, modus ponens, congruence, witness extraction and finite universal interchange | Only missing small decision/support adapters should be added |
| Existing Set direct-image action and `SubMulAction` | Appropriate image/restricted-action machinery | Restricted image action and supported-subset view delivered; no replacement bare Set action |

The elementary pullback reflection mechanism is even scalar-general: for a
surjective q and one scalar m with `q (m • x) = m • q x`, pointwise invariance
of `P ∘ q` is equivalent to invariance of P. This scratch proof has no axiom
dependencies. It needs no new logical-support definition. The corresponding
`FunctionObject` precomposition adapter works with `DivisionMonoid G` and an
arbitrary `Set B` bound, with only `[SMul G B]`; its proof uses F05's existing
injective support reflection. `Group G` would be unnecessarily strong here.

## Representation result and local elaboration evidence

The recommendation is a direct ordinary-predicate record with proof-only
`FinitelySupportedPred A` evidence, a single `FunLike` interface, and named
`toMap`, `toObject`, `toSet` views. The [specification](../superpowers/specs/2026-10-07-package-predicate-foundations-design.md#3-representation-comparison)
compares all candidates and specifies the equivalences and public laws.

The direct record and a distinct wrapper over
`SupportedMap A X (Discrete A Prop)` both pass ordinary Prop application,
Iff extensionality, `rw`, `simp`, higher-order list use and proof independence.
The wrapper is a close viable alternative. It was not rejected by a failed
action theorem or for lack of supported-function infrastructure. Its full
action/nominality interface was not separately built in the bounded comparison.
Direct storage is preferred because its primary data and certificate already
have the intended logical form; F05 supplies the small bridges needed to derive
its semantic theory. This is an interface/maintenance judgment, not a theorem
or a performance measurement.

The raw supported-map specialization fails the precise term check `p x : Prop`:
its output is `Discrete A Prop`. The plain supported-Set subtype fails ordinary
function application until an explicit FunLike adapter is supplied. With that
adapter its ordinary consumers also work. Neither diagnostic rules out the
underlying representation; the costs are explicit in the comparison.

A substantive simplification issue affects both direct and wrapper constructors.
With a constructor lemma quantified over the semireducible
`FinitelySupportedPred A P`, `simp` did not finish

```lean
xs.map (ofPred A P ⟨S,hS⟩) = xs.map P
```

Named evidence worked. A coercion simp lemma with the equivalent binder
`hP : ∃ S : Finset A, SupportsPred S P` makes the literal case work too.
This is a local lemma-shape remedy: neither F05's predicate definition nor its
approved hybrid needs to change. Different sufficient bounds give equal values
by proof irrelevance. Reverse conversion laws should remain named or simplify
only genuine round trips; avoid bidirectional simp loops.

The direct record's action and nominality were derived from F05, with exact
least-support agreement with the map view. The Boolean-algebra probe constructs
the supported subsets as a `BooleanSubalgebra (Set X)` and transfers its inherited
algebra using `Equiv.booleanAlgebra`. Conjunction, complement and implication
compute as ordinary logic. Task 2 subsequently delivered the action-certified
subset correspondence and transferred Boolean instance in production. Task 3
now supplies the named operator API, bundled quantifiers and supported collection
operations. Literal section evidence uses the same local explicit-existential
simp pattern as constructor evidence, without changing foundational reducibility.

## Mathematical refinements from the probes

### Joint quantification is not supported currying

The support of `R : X × Y → Prop` suffices for the **same bound** on
`∀ y, R (x,y)` and `∃ y, R (x,y)`. Quantification reindexes all y through
a bijection; it needs no finite support for individual y, no nominality and no
nonemptiness. Fixing y is different: use F05's individual parameter certificate
or its supported-section admission condition. This preserves F05's correct
currying boundary.

For restricted quantifiers the most general input is support of the combined
implication/conjunction body. Separate support of a domain guard and relation
is a convenient sufficient condition, not necessary. For an arbitrary external
index there may instead be one supplied bound supporting every section; the
index then needs no action. Individually supported sections with different
bounds do not establish this uniform condition or joint support.

A supported collection of supported predicates has supported union/intersection,
by joint evaluation and the whole-carrier quantifier theorem. These operations
retain every bound of the collection. This gives the nominal supported-family
construction without claiming closure under arbitrary external unions or an
unrestricted CompleteLattice. Mathlib's complete lattice of BooleanSubalgebras
is a lattice of different subalgebras, not completeness of each one's elements.

### Compatibility, support and equivariance stay separate

Ordinary predicate descent is the Mathlib quotient universal property adapted
with `propext`. No support or action is involved. Adding the canonical quotient
action gives exact preservation/reflection of every sufficient predicate bound
through the equivariant surjective projection. Infinite atoms enter only when
deriving equal least supports. No source or quotient carrier nominality is needed.

The non-surjectivity counterexample has a nonempty source: the equivariant
diagonal `Nat → Nat × Nat` makes
`P(x,y) := x = 0 ∧ x ≠ y` constantly false on its image. The pullback has
empty support while P does not. Surjectivity is therefore substantive, not
merely a condition to rule out empty-domain degeneracy.

A raw observation of a vacuous binder's atom label is singleton-supported yet
cannot descend through the relation that forgets that label. Conversely an
infinite/coinfinite predicate on atoms `Nat × Bool`, projected from a raw
carrier with an extra discrete label, descends through the nontrivial quotient
forgetting the extra label and remains unsupported. Its computations are proved.
The old actual lambda root-binder counterexample remains separate reference
evidence; no syntax backend is implemented by the tiny vacuous-binder model.

F04's object theorem `support (q x) ⊆ support x`, its supported-fiber theorem
and nonattainment example are unchanged. Predicate pullback embeds whole
predicates and is a different statement. Dependent data-valued quotient
elimination exists, but requires the transport coherence shown by the pinned
recursor types; it is not automatically solved by Prop descent.

### Cofinite truth and nominal laws have different hypotheses

Use `Freshly p := ∀ᶠ a in Filter.cofinite, p a` for any ordinary atom predicate.
The author chose scoped `И` notation as an additional interface; `Fresh` keeps
its existing support-disjointness meaning. Typed and untyped binders were probed.

For Infinite A and a supplied finite `SupportsPred S p`, swaps make p constant
outside S. This proves cofinite/Some/Any equivalence, evaluation at any atom
outside S, arbitrary enlargement and extra finite exclusions. Parameter forms
reuse F05 sections and individual support; no whole-carrier nominality is needed.
Fresh projection of a jointly supported relation retains its bound even without
Infinite A, because cofinite reindexing is valid on every carrier.

The exact atom classification

```text
FinitelySupportedPred A p ↔
  Set.Finite {a | p a} ∨ Set.Finite {a | ¬p a}
```

needs **no infinitude premise**. Finite carriers are a trivial case; infinite
ones use outside-swap constancy. It provides cofinite decision
`Freshly p ∨ Freshly (fun a => ¬p a)` without claiming that arbitrary predicates
are supported.

Filter conjunction, monotonicity and valid one-way ordinary quantifier laws
need no support. Self-dual negation requires a nontrivial filter and decision;
Infinite A supplies nontriviality. Full disjunction requires decision of only
one operand, and full implication requires it only for the antecedent. Both
laws work even on finite A. Two decisions suffice for the symmetric Iff law,
also without infinitude; alternatively an already cofinite operand suffices
with an arbitrary other operand. One merely supported operand does not suffice
for Iff, as the False-versus-infinite/coinfinite example proves.

Finite-index universal interchange is a general filter theorem. Finite nonempty
index alone does **not** repair existential interchange: use an unsupported
predicate and its complement at the two indices. With a common finite support
bound on every section, universal interchange holds for arbitrary indices
without Infinite A; existential interchange needs Infinite A, or alternatively
a nonempty index (to handle the finite-atom bottom-filter case). The equality/
disequality counterexamples show why joint invariance alone is insufficient.

## Retained bounded evidence and remaining obligations

All new probes import current Package and pinned Mathlib, remain outside
production imports, and contain complete proofs without admissions or custom
axioms. They are research alternatives and mechanism checks, not files to
promote wholesale into Package.

| Probe | Checked content | Deliberate limit |
| --- | --- | --- |
| [Representation and logic](probes/2026-10-07-pkg01-representation.lean) | Four candidates; ordinary use and local literal-proof fix; direct action/nominality/map bridge; BooleanSubalgebra transfer; joint/restricted/uniform quantifiers; supported collections; genuinely nonnominal parameter carrier | Production subset adapters and bundled operation/action laws are now delivered by Tasks 2–3; these alternative probe carriers remain research only |
| [Pullback and descent](probes/2026-10-07-pkg01-descent.lean) | Scalar reflection; DivisionMonoid function-object reflection; ordinary Mathlib-backed equivalence; canonical quotient support/renaming and support-subtype equivalence; exact least support; meaningful positive/negative consumers | The final direct-carrier interface is now delivered in SupportedPredicateDescent; this probe remains unchanged research evidence |
| [Fresh quantification](probes/2026-10-07-pkg01-fresh.lean) | Scoped notation; supplied/enlarged/avoiding Some/Any; elementwise context; joint fresh projection; finite/cofinite classification; weak logical premises; common-bound repairs and negative boundaries | Production interfaces and public consumers now delivered in Tasks 6–7; whole-change integration/review also passes in Task 8 |

The unsupported example is the true Bool flag among atoms `Nat × Bool` under
**all finite permutations of that atom type**, not componentwise permutation
of a discrete Bool. It and its complement are infinite. Supported singleton
predicates indexed by true-flag atoms have exactly that unsupported external
union. The selector proof rejects finite support of a global
`f : Finset A → A` with `f S ∉ S`; it needs no separate Infinite A premise,
because such a selector would itself supply the necessary spare atom.

The fresh probe also exhibits an empty-supported subset of the nominal carrier
`Discrete Nat Bool × Nat` with both a witness and infinitely many exceptions.
Thus atom Some/Any is not a cofinite theorem for arbitrary nominal carriers.
On finite Bool, `Freshly False` holds; this explains the nontriviality premise
where witness extraction or self-dual negation is used.

Root added two final substantive consumers after inspecting the independent
probes: `nonminimal_logic_consumer` uses a disjunction certificate with surplus
atom 2 to prove its renamed conclusion, and `flag_induction_consumer` uses
ordinary quotient induction to obtain a true-flag representative from the
unsupported descended predicate. Cofinite reindexing was also checked across
an equivalence of independently universe-polymorphic types.

Production obligations are listed phase by phase in the specification. Tasks
1–3 now discharge phase 01a: all views, the coherent Boolean instance, logical
and quantified computation/action laws, supported-family operations and their
public consumers and integration. Tasks 4–5 now discharge ordinary/supported
descent, exact support and context freshness. Tasks 6–7 discharge cofinite
theory, notation, context adapters, bundled fresh projection and negative boundaries;
final whole-change integration/review also passes. No large-client performance,
generated induction, binder descent or external formalization build is claimed.

## Verification and specification review record

Root directly elaborated the final retained sources, including the last
consumer/generalization edits:

```sh
lake env lean docs/research/probes/2026-10-07-pkg01-representation.lean
lake env lean docs/research/probes/2026-10-07-pkg01-descent.lean
lake env lean docs/research/probes/2026-10-07-pkg01-fresh.lean
```

All exited 0 without warnings or errors. Their 14, 16 and 24 representative
axiom reports contain only subsets of `propext`, `Classical.choice`, `Quot.sound`;
the scalar invariance theorem is axiom-free. The new sources contain no
admissions, custom axioms or disabled checking. These are fresh standalone
elaborations using cached pinned imports. Logs are
`/tmp/pkg01-root-representation.log`, `/tmp/pkg01-root-descent.log` and
`/tmp/pkg01-root-fresh.log`. The descent investigator additionally reran the
unchanged reference `PredicateFoundations.lean`, including its actual lambda
alpha-incompatibility theorem; root inspected that report rather than claiming
a second direct reference-probe run.

The Package baseline build was cached; the separate direct axiom audit and
import checker succeeded as recorded above. No clean dependency bootstrap,
fresh project rebuild or new reference-library build is claimed. Production
sources and supported imports did not change during this investigation.

From `docs/article`, root ran

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error \
  -outdir=/tmp/pkg01-article-build main.tex
```

It exited 0 and produced a 37-page PDF. The final LaTeX log has no warnings,
undefined references, or overfull/underfull boxes. Generated files stay outside
the repository. Mathematical claims and source attribution were reviewed,
including the distinction between arbitrary acted X and Pitts' nominal-X
formulation. The manuscript contains no task/review/build narrative.

Independent read-only checks of the written specification and article found
no blocking mathematical findings. Two clarifications were incorporated:
least support of bare `toSet` uses an induced elementwise certificate, and
Pitts' supported-family formulation is cited under his nominal-carrier
hypothesis. The root self-review corrected an overbroad finite-index existential
interchange statement before delivery, sharpened the implication/Iff and uniform
quantifier hypotheses, and checked phase scope and remaining obligations.
There are no unresolved placeholders; unchecked implementation criteria are
intentional future obligations, not completed results.

All changed/new files passed whitespace/final-newline checks and all 291 local
Markdown targets checked at the verification checkpoint existed. `git diff
--check` passed. The preservation check leaves HEAD, branch and index unchanged,
with no edits to Package, reference Lean, the historical roadmap,
toolchain/dependencies or CI. Only research documentation, the article and the
three new standalone probes changed. These changes are uncommitted.

## Literature used, without restarting the survey

Revisited the local complete Pitts PDF, *Nominal Sets*, CUP 2013, SHA-256
`546104434ce6388d2aed248428cc8bde653bf98780cee55265f686e7290f0794`:
§2.5 pp.38–40, Lemma 3.7/Definition 3.8/Theorem 3.9/Proposition 3.10 pp.52–53,
and Example 11.1 pp.220–221. These directly support nominal powersets,
supported-family operations and supplied-bound Some/Any. The sharpened
one-operand Boolean hypotheses are elementary filter deductions checked here,
not claims that Pitts states those exact Lean contracts. Infinitude replaces
the book's countable atom choice for these arguments; no countability is used.

Other comparisons use the already pinned primary-source investigations:

* [Isabelle comparison](2026-10-05-isabelle-comparison.md): original manual dated
  22 December 2008; Urban–Kaliszyk LMCS 8(2:14), 2012; Nominal2 source revision
  `0f498441e41026d1f5e677300353f5ba31a77f5a`. Logical equivariance and arbitrary
  strong-induction motives do not require a separate metatheory formula datatype.
* [Urban study](2026-10-07-urban-nominal-techniques.md): 27-page 2008 author
  manuscript, SHA-256 `b249192759a845fbe6d76b4734f52bce9809c9bb5af5c22e4dca265a6a5a7a63`.
  Support of individual avoidance values is distinct from support of a selector
  or motive. Its total swap-support representation is not adopted here.
* [Predicate-source comparison](2026-10-05-predicate-foundations.md): Copello
  et al., ENTCS 323 (2016), DOI `10.1016/j.entcs.2016.06.008`; Copello–Szasz–Tasistro,
  EPTCS 274 (2018), arXiv `1807.01870v1`; alpha compatibility is distinct from
  finite support, and data-valued transfer is distinct from Prop equivalence.
* The same source comparison pins Rocq main
  `78f41a6c7ca1b55814b7b7c7d734ad4decaac523` and article artifact
  `fc7b95a47539fa2dc39f41f293c7d943a0d8b22d`. Supplied computational supports and
  setoid equality are not copied into Lean proof-field records. Historical
  assumption limitations are not asserted of the current Lean Package.

No new external Isabelle, Agda or Rocq build or moving-version audit was needed.
The reference lambda non-descent probe was rerun unchanged; it remains reference
evidence. New mathematical exposition is in
[predicates.tex](../article/sections/predicates.tex), with the quotient section's
cross-reference reconciled. Unsettled storage choices, phase IDs and operational
evidence stay here and in the tracker, not in the manuscript.

## Follow-up: direct record versus supported-map wrapper

The author requested an in-chat comparison and independent investigation of
both viable stores. One investigator examined direct storage and another the
wrapper, preserving the existing dirty tree. Their temporary sources are
`/tmp/pkg01-direct-choice.lean` and `/tmp/pkg01-wrapper-choice.lean`, with
corresponding `-report.md` reports. These are further scratch experiments,
not production changes or a replacement of the retained earlier probes.

The second investigation closes the earlier imbalance in action evidence:
wrapper action, nominality, exact sufficient/least support, Boolean transfer,
precomposition, supported sections and higher-order uncurrying all compile.
The direct comparison proves that conversion round trips and agreement between
logical-certificate and SupportedMap precomposition are `rfl` for both stores.
Both can transfer action and nominality through the same F05 results. No
computational conversion penalty or performance advantage was established.

The concrete tradeoff is small and symmetric. Direct storage makes the ordinary
predicate constructor and logical certificate projections primitive, with map
views obtained through F05's proved conversions. Wrapper storage makes the map
view a projection and its inverse a constructor, deriving logical certificates
through those same conversions. Both still need Prop-facing FunLike/Iff-ext/simp
interfaces and the new logical, descent and fresh-quantifier theory. Distinct
predicate values inside higher-order SupportedMaps need a named map adapter
in either design. A wrapper need not expose `Discrete` to ordinary users.

The direct investigator retains a mild preference for native logical fields;
the wrapper investigator mildly prefers storing the map already required by
the specification. Neither identifies a technical blocker in the alternative.
The specification's direct recommendation remains an interface preference for
review, not an experimentally demonstrated winner. No storage approval is
inferred from the request for comparison.

Root independently compiled both final temporary sources: exit 0 without
warnings/errors; their seven and seventeen representative axiom lists are
confined to the standard three foundations. A root check caught an in-progress
failed direct-transfer consumer while the wrapper file was still being edited;
the final stable version fixes it and was rerun, with no `sorryAx`. Logs are
`/tmp/pkg01-direct-choice-root.log` and `/tmp/pkg01-wrapper-choice-root.log`.
No production build was required for these scratch-only changes. This follow-up
changes no mathematical article claim and adds no manuscript text.

## Author choices and handoff

The author explicitly selected scoped `И` notation alongside the named operator,
and selected the direct logical record on 2026-10-08 after reviewing the two
storage choices. The author then approved the full written specification and
three-phase scope. There is no unresolved mathematical choice blocking those
contracts, and no demonstrated F05 defect requiring its hybrid to be reopened.
The [implementation plan](../superpowers/plans/2026-10-08-package-predicate-foundations.md)
now fixes public spelling, module responsibilities, consuming checks and the
complete acceptance mapping; it does not promote scratch declarations to exports.

The author approved that plan for native execution and later grouped Tasks 4–5
into one phase 01b run, with an explicit stop before Task 6. Tasks 1–5 and phases
01a–01b are complete in the working tree. Package exports the direct predicate
carrier and its logical/quantified operations, plus general pullback reflection
and ordinary/supported quotient correspondence. The compatible subtype uses an
explicit SubMulAction restriction, with exact support and individual-context
freshness; neither source nor quotient needs carrier-wide nominality.

The plan and active roadmap record separate Task 4 and Task 5 deliveries and
combined fresh checks of all five consumers, the 918-declaration direct audit,
import coverage and the 40-page article in
`/tmp/nominal-package-pkg01-execution.WReW3a/`. Phase 01a source, research probes
and unrelated work are unchanged. Tasks 4–5 intentionally extend the scalar,
function and predicate support modules and add two descent modules. The starting
Task4-handoff.txt was a start prompt; actual source inspection established that
Task 4 was absent before this run. It was completed and verified before Task 5.

That phase 01b handoff was followed by the authorized whole-phase 01c run.
Tasks 6–7 now deliver the complete fresh-quantifier interface and boundary
consumers. Continue with Task 8 in a fresh context: final integration, complete
specification coverage and independent whole-change review. All PKG-01 production
and documentation changes remain uncommitted; earlier probes are unchanged.


### 2026-10-08 — Production phase 01c delivered

Tasks 6–7 complete ordinary/bundled fresh quantification without modifying the
retained probes or completed Tasks 1–5 source. The separate records and combined
acceptance map are in the active roadmap, plan and external evidence directory.
`phase-01c-final-validation.json` records fourteen successful commands, all eight
consumers and the 58-name phase signature inventory; direct audit checks 995
production declarations from 21 defining modules. Coverage reaches 22 production
sources plus audit. The fresh external 42-page article has a diagnostic-free final
engine log. `phase-01c-preservation.log` verifies the original branch/HEAD/index,
all earlier source/probe work and all 693 previous evidence files. All changes
remain uncommitted. PKG-01 is open pending Task 8; its fresh-context prompt is
`Task8-handoff.txt` in the same evidence directory and embedded in the plan.

## Final integration and review — 2026-10-08

Task 8 and PKG-01 are complete, uncommitted. All 46 specification coverage rows,
nine public consumers, both phase inventories and eight extracted README Lean
blocks pass. The expanded direct audit checks 995 production declarations in 21
defining modules, with only propext/Classical.choice/Quot.sound; import coverage
reaches 22 production sources and the separate audit. The fresh external article
build produces 42 pages with a clean final engine log. Production/dependency
artifacts were cached; consumers/audit were freshly elaborated. No dependency
bootstrap or unchanged reference rebuild is claimed.

One fresh independent gpt-6-astra reviewer at ultra reasoning reviewed the whole
uncommitted delivery, including all seven untracked production modules, and
independently reran the consuming checks. No correctness or acceptance issue was
found. Its one minor stale active roadmap paragraph was corrected during final
status reconciliation; no production theorem changed in Task 8 and no finding
is deferred. Evidence remains `/tmp/nominal-package-pkg01-execution.WReW3a/`:
`task-8-integrated-validation.json`, `task-8-acceptance.md`,
`task-8-independent-review.md`, `task-8-rulings.md` and final preservation records.
Branch, HEAD, index, reference code, probes, historical roadmap and dependencies
are preserved. The run stops after Task 8; later tasks require a separate request.
