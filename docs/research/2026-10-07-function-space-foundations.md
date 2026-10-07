# Function spaces and predicate inputs: F05 investigation

Date: 2026-10-07. Research and design, not production implementation.
Inspected branch: `fasapa/nominal-package`; HEAD:
`32f3dba551761881409bbc7453054e214e582269` (`Nominal quotient`).
The initial index and working tree were clean. F04d is committed at this HEAD;
earlier notes saying it was uncommitted describe their own historical sessions.
No F02–F04 work is reopened here.

The requested outcome is a reusable function/predicate-input foundation with
natural application, composition, fixed parameters, higher-order arguments,
extensionality and rewriting. Ordinary `Prop`, selected actions, independent
universes and elementwise support evidence are requirements. Production changes,
dependency changes, commits and implementation planning are outside this turn.
The author requested an evidence-based investigation of ordinary-first versus
bundle-first use, rather than selecting that preference in advance.

## Subsequent native implementation

After this investigation the author approved its written specification, then
approved the implementation plan for native execution. The five F05 modules now
exist under Package/Foundations, with passing public consumers, full production
axiom audit and matching article. Independent final review passed with no findings; delivery is uncommitted. See the
[implementation plan](../superpowers/plans/2026-10-07-package-function-space.md)
and [active roadmap](../nominal-package-roadmap.md) for actual delivery evidence.
The source inventory and scratch-status descriptions below retain the starting
revision's meaning; the old scratch files were preserved, not promoted as-is.
The production finite-map and section-admission predicates are reducible proof
aliases, justified by literal-evidence simp regressions during implementation.

## Sources and current inventory

Lean is pinned to `v4.34.1`. Mathlib's manifest revision is
`d13f23b723b8a846827a245b89c10fc7d3f11612` (`v4.34.1`). Paths in the
following table refer to this local checkout, not an unspecified current release.

| Source | Actual delivered contract | Consequence |
| --- | --- | --- |
| `Package/Foundations/Action.lean` | `Equivariant A f` is an ordinary-function property; id, composition, projections and pairing; explicit `Discrete A X`; selected `MulAction` | No existing conjugation function carrier or supported-function bundle; preserve ordinary pointwise function action |
| `Support.lean` | `Supports` abbreviates Mathlib support at a finite atom bound; `FinitelySupported A x`; map, product, transport, intersection | Function objects can reuse this theory; do not reimplement a parallel support calculus |
| `Nominal.lean` | Proof-only `Nominal`, elementwise `hx.support`, certificate independence, finite minimality, transport and image inclusion | A particular supported function/input needs no nominality assumption on its whole carrier |
| `Canonical.lean`, `Freshness.lean` | Exact canonical support; general disjointness freshness and elementwise `FreshWith` | Evaluation freshness should be derived from support bounds and equivariance |
| `QuotientAction.lean`, `Quotient.lean` | Explicit canonical action, equivariant surjective projection, nominality transfer, support inclusion and supported-fiber characterization | No predicate pullback/support-reflection interface is delivered by these object theorems |
| `Package.lean` | Imports these nine foundation modules | Scratch experiments remain outside this production boundary |
| `Nominal/Set/PFun.lean`, `Nominal/Set/NFun/Basic.lean`, `Examples/NFun.lean` | Reference conjugation wrapper and supported bundle; ordinary consumers, coercion simp, nested ext, curry laws and empty-domain guards | Useful evidence for ergonomics, but old carrier-wide nominality and universe/interface policy are not requirements |

Readiness, predicate-foundation and predicate-design notes from 2026-10-05
propose direct `SPred` with unbundled map certificates. They do not select its
representation for this task. Their Mathlib-only and legacy probes establish
only the implementations and assumptions they actually tested. The
[generalization investigation](2026-10-06-foundation-generalizations.md)
already separates arbitrary-set sufficient support from finite least support.
Its general support transport and injective reflection are research evidence;
F04d adopted surjective nominality transfer, not all of those proposals.

### Pinned Mathlib candidates

| Candidate | Fit and concrete mismatch |
| --- | --- |
| `Mathlib/GroupTheory/GroupAction/Support.lean`, `MulAction.Supports` | Suitable underlying support predicate on two acted carriers and arbitrary sets. Only `SMul` is needed for its definition and monotonicity. Its `.smul` theorem uses commuting scalar actions; it is not the same-group conjugation transport theorem needed here |
| `Mathlib/GroupTheory/GroupAction/Hom.lean`, `MulActionHom`, `map_smul`, `ext`, `comp` | Reuse for equivariant maps, with independent universes and `FunLike`. Its proof field requires equivariance for every scalar; a fixed-parameter supported function need not satisfy it |
| `Mathlib/Algebra/Group/Action/Basic.lean`, `arrowAction` | Named action by inverse precomposition, with a file-local instance. Fits predicates with discrete outputs. It omits the codomain action required for full conjugation; it must not replace the pointwise instance on ordinary arrows |
| `Mathlib/GroupTheory/GroupAction/DomAct/Basic.lean`, `DomMulAct` | Tags the scalar by an opposite action and precomposes functions. Its documentation explicitly explains the function-action diamond. It supplies domain-shift operations, not a full function carrier with the original scalar's simultaneous domain/codomain action |
| `Mathlib/GroupTheory/GroupAction/ConjAct.lean`, `ConjAct` | Tags scalars for group conjugation on a group. It is not the action on maps between arbitrary acted carriers |
| `Mathlib/Data/FunLike/Basic.lean`, `FunLike`, `DFunLike` | Reuse coercion, extensionality and congruence machinery. An injective ordinary-function projection is the obligation for the new records; do not invent a parallel extensional equality |
| `Mathlib/GroupTheory/GroupAction/SubMulAction.lean`, `SubMulAction`, `.mulAction`, `.subtype`; `Function.Injective.mulAction` in `Algebra/Group/Action/Defs.lean` | Reuse restriction or transfer of action laws. The supported part is an invariant subset; a dedicated function record is recommended for its public FunLike/constructor interface, not because generic invariant-subset actions are missing. Avoid adding a competing general subset-action framework |
| Ordinary `Function.curry`, `Function.uncurry`, their inverse laws and equivalences | Reuse underlying operations. Additional action compatibility and admissibility for supported sections need proofs |
| Mathlib pointwise actions on `Set` and functions | Preserve their instance policies. Set direct image agrees with inverse-precomposition membership for group actions, but importing a scope is not a license to change the selected action on a bare type |

The mathematical gap is the full function object plus its nominal restriction
and adapters. It is not a lack of general group theory, extensionality or
equivariant-map bundles. `Function.support`, `Finsupp` and finite range concern
different notions and cannot certify nominal dependence.

## Pitts: exact reference and mathematical use

The inspected source is Andrew M. Pitts, *Nominal Sets: Names and Symmetry in
Computer Science*, CUP 2013, Cambridge Tracts in Theoretical Computer Science
57, ISBN 978-1-107-01778-8, local [PDF](../../ref/nominalsets.pdf).
SHA-256: `546104434ce6388d2aed248428cc8bde653bf98780cee55265f686e7290f0794`.
The author's [publication list](https://www.cl.cam.ac.uk/~amp12/papers/index.html)
also identifies that edition; PDF-generation metadata does not change the
publication version. References below use printed pages.

| Location | Used here |
| --- | --- |
| §1.4, Theorem 1.7, pp. 18–19 | Full function-space conjugation, equivariant evaluation and currying for group actions |
| §2.4, Lemma 2.17, Definition 2.18, p. 35; Theorem 2.19, p. 36 | Finite-supported part of a permutation set; supported functions as nominal exponential when the input objects are nominal |
| §2.4, Example 2.20, p. 36 | Functions between nominal sets need not all be supported |
| Proposition 2.9, pp. 31–32 | Atom subsets are supported exactly when finite or cofinite; infinite/coinfinite predicates are genuine counterexamples |
| §2.5, Lemma 2.24 and Proposition 2.25, p. 39 | Logical support of a subset and the relation-section bound |
| Theorem 2.29, p. 43 | Failure of supported choice; distinguishes ordinary classical choice from a nominally supported selector |
| Proposition 3.4, p. 50; Example 3.5, pp. 50–51 | Freshness preserved by supported application with fresh function/input; pointwise fresh-output behavior does not characterize freshness of a function |

Pitts distinguishes equivariant morphisms from elements of a function object.
This is a reason to keep both ordinary equivariance certificates and supported
function values, not a reason to require a wrapper around every Lean function.
His nominal exponential theorem assumes nominal objects. Extending the full
function-space construction to arbitrary acted carriers is sound; extending
its restricted currying theorem without section evidence is not.

## Representation comparison

| Approach | Scope and strengths | Costs and boundaries |
| --- | --- | --- |
| A. Ordinary functions/predicates plus certificates | Broadest ordinary input; direct use of Lean application, `rw`, `funext`, `Iff`; unsupported motives remain legal; minimal construction cost | A certificate is a separate argument; bare `FinitelySupported A f` uses the pointwise action, not the intended map action; higher-order nominal parameters need explicit action selection or a function object |
| B. Full conjugation function carrier | Every function is representable, including unsupported ones; uniform action/evaluation/curry; direct reuse of elementwise least support/freshness | Wrapping is explicit; no carrier-wide nominality in general; reusable supported values still carry separate certificates |
| C. Proof-field supported bundle | Support travels with the function; ordinary application through `FunLike`; canonical nominal carrier even with arbitrary acted domain/codomain; proof irrelevance gives extensional equality | Cannot represent unsupported functions; construction needs evidence; currying requires supported sections; a bundle-only API can unnecessarily narrow ordinary inputs and motives |
| D. Proved hybrid A + B + C | Ordinary inputs and explicit theorem premises; B fixes action semantics; C handles persistent supported values; correspondence makes support/least support agree | More adapter laws and two function-like carriers; needs a deliberate coercion/simp policy and bounded module ownership |

None of these choices forces atom/domain/codomain universes to coincide. All
can keep classical support evidence in `Prop`; none needs to make a computable
function body noncomputable. Bundled equality must not compare chosen finite
bounds as data. A finite bound is sufficient evidence, not the identity of the
function or a computed exact support.

### Recommended division of use

Recommend D, with **ordinary inputs for operations and theorem entry points,
supported bundles for values whose support must travel through an interface**.
Full conjugation objects supply the mathematical action boundary. This is a
division by purpose rather than one mandatory representation for all clients.

The comparison must test both kinds of higher-order use. `List.map` accepts an
ordinary function and a bundle coerced to one; that alone does not choose a
winner. A nominal higher-order operator needs an acted function argument, which
ordinary coercion does not provide. Likewise returning a function together with
support is naturally bundled, whereas an arbitrary induction motive must stay
ordinary. Fixing one supported parameter should have both an ordinary section
theorem and a bundle constructor, each using the particular parameter's proof.

The exact proposed contracts, phase boundaries and acceptance matrix are in
the [written specification](../superpowers/specs/2026-10-07-package-function-space-design.md).
The author subsequently approved this recommendation and the written
specification on 2026-10-07. The
[implementation plan](../superpowers/plans/2026-10-07-package-function-space.md)
now awaits review; all evidence below remains brainstorming/scratch evidence.

## Context bounds and the author's follow-up

The author proposed combining an inspected local context with explicitly
provided values. This is a viable source of **sufficient** bounds. If a capture
tuple c has bound T and `E : C × X → Y` has map bound S, then
`x ↦ E (c,x)` has bound `S ∪ T`. For jointly equivariant E use T alone.
Nested products combine component bounds; monotonicity permits user enlargement
and unused supported captures. Neither least support, atom infinitude nor
nominality of C/X/Y enters this rule. The predicate version uses Iff.

Two issues must be distinguished. An explicit A or a surrounding expected
acted type chooses the atom/action semantics. A bound certificate proves
dependence of the actual value, which its function type alone cannot determine.
The earlier phantom-argument elaboration failure concerns the first issue;
automatic capture analysis concerns the second. They should have separate
diagnostics and inputs.

Pitts' Proposition 1.9 and Notes 1.10–1.11 (pp. 21–22) explain joint parameter
equivariance and the exception for unrestricted choice. The Finite Support
Principle (p. 40) concerns the internal nominal interpretation, where quantified
function/subset objects are restricted. It does not prohibit external Lean
quantification over full function spaces when a suitable equivariance theorem
is proved. Uniquely characterized choice can also have a proved action law.

Future tooling should inspect elaborated expressions/local-variable identities,
obtain support evidence for relevant captures, use registered operation laws,
and accept explicit bounds/proofs. Unsupported captured functions/predicates
cannot be certified by enumeration; irrelevant unsupported locals need not
prevent a proof. Extra user atoms give a larger bound only after a valid bound
is proved. There is no universal theorem certifying arbitrary Lean expressions
from their syntactic free variables. F05 supplies the mathematical constructors;
no scanner, capture macro, complete decision procedure or least-support inference
is proposed for this increment.

The constructive comparison needs precision. Swan,
[*Some Brouwerian Counterexamples Regarding Nominal Sets in Constructive Set Theory*](https://arxiv.org/html/1702.01556v1),
arXiv:1702.01556v1, 6 February 2017, Theorem 3.5, shows that general existence
of least finite supports is not constructively provable; Theorem 3.3 also
obstructs general support-function selection. This does not rule out specific
constructive least supports. The explicit-bound rule above avoids selecting
a least support, but the current Lean probes use the classical Package
foundation and do not certify a constructive port.

### Urban's supplied paper

Inspected the author's [*Nominal Techniques in Isabelle/HOL* PDF](https://urbanchr.github.io/Publications/nom-tech.pdf),
retrieved 2026-10-07, SHA-256
`b249192759a845fbe6d76b4734f52bce9809c9bb5af5c22e4dca265a6a5a7a63`.
It is a 27-page author manuscript with placeholder publication dates; page
numbers here refer to that file. The
[author's publication listing](https://urbanchr.github.io/publications.html)
identifies the journal article as JAR 40(4), 327–356 (2008),
DOI `10.1007/s10817-008-9097-2`. Do not substitute journal pagination for this
manuscript or call it a current Nominal2 implementation audit.

In §2, pp. 5–7, Urban separates permutation types from finite support and
explains why function types cannot certify it. In §5, Definition 5, Lemma 11
and Examples 1–2 (pp. 16–17), free-variable supports suggest a bound whose
validity is then proved. Section 6, pp. 20–21, illustrates `finite_guess`.
This directly supports investigating the author's context-bound proposal.

**Design inference:** offer a candidate-bound producer separately from its
kernel-checked support proof. Our `supports_iff_swap` already connects Urban's
swap criterion to all fixing permutations. The surrounding context is an
overapproximation; a proof must account for actual dependencies and operations.
The selected-action boundary remains necessary for coherent Lean use because
the existing bare-arrow action is pointwise. The paper's Isabelle encoding does
not select a Lean storage representation or justify dropping the bundle probe.

The author's subsequent request to study the paper beyond functions is recorded
in the [broader Urban investigation](2026-10-07-urban-nominal-techniques.md).
It sharpens future carrier, avoidance-context induction, FCB, primitive-recursion
and rule-induction obligations. Root checked its key source passages and
reference Lean signatures before updating the active roadmap. Those later
tasks remain unimplemented; F05's mathematical scope is unchanged.

## Bounded probes and independent review

Two new standalone sources are retained, outside production imports:

| Probe | Decisive checked content | Limits |
| --- | --- | --- |
| [F05FunctionSpace.lean](probes/F05FunctionSpace.lean) | Independent universes; full conjugation and curry; ordinary support correspondence; FunLike/ext/rw/higher-order consumers; proof-field bundle and nominality; particular-parameter support; discrete-Prop bridge; computable proof-field constructor | Small alternative implementation, not the selected production API or a full combinator library |
| [F05Boundaries.lean](probes/F05Boundaries.lean) | Empty-domain support, constant reflection and sharp injectivity criterion; projection and equality section obstructions; fixed-atom predicate; generic and concrete unsupported predicates; no supported fresh selector; Set/discrete-truth correspondence | Does not implement supported bundle curry, full predicate logic or quotient descent |

`F05Probe.contextBound` additionally consumes two particular capture bounds
and an arbitrary user enlargement to certify a fixed-parameter function.
It uses only the existing product/monotonicity rules and the proved parameter
adapter; no least-support selection, infinitude or nominal carrier is assumed.

Root also reran existing
[GeneralizationSupport.lean](probes/GeneralizationSupport.lean), including
arbitrary-set transport/reflection and the complement-of-singleton
counterexample. Those remain research results, not added production exports.

Important proof refinements: full curry action equations need only
`DivisionMonoid`; their inverse laws need no actions. Generic supported uncurry
is injective and exact on supports. Supported curry needs all sections supported,
with nominality of the fixed-parameter carrier only a sufficient adapter.
Constant injectivity is equivalent to `Nonempty X ∨ Subsingleton Y`.
The fresh-selector nonexistence probe needs no separate `Infinite A` premise:
the assumed selector provides the spare atom used to refute its own support.

Three independent investigations compared ordinary-first and bundle-first use.
All recommended the contextual hybrid. The executable comparison uses the same
ordinary list consumer and rewrites on both representations; bundles remove
repeated function-certificate arguments in support-sensitive application and
are natural for returned supported values. This is evidence of API feasibility,
not a user study or performance benchmark. Root inspected their proof statements,
read the sources, and reran the probes. Two specification corrections from review
were incorporated: curry's weaker hypotheses and the fact that projection to
pointwise arrows is not *generally* equivariant, with trivial actions as exceptions.

### Failed approaches retained as evidence

- `predicateObject P` left a phantom atom metavariable unresolved; explicit
  `(A := A)` worked. This is an adapter-inference limitation, not an absence of
  mathematical support. Public adapters should accept the atom choice.
- During construction of the action instance, `ext x; simp` alone did not expose
  its under-construction operation. An explicit `change` to the conjugation
  formula solved the elaboration problem; no action hypothesis was weakened.
- Treating `(P : Set X)` as a sufficient syntactic adapter left ordinary-arrow
  action goals in a probe. Explicit `{x | P x}` / `Set.ofPred P` and
  `Set.mem_ofPred_eq` made the selected scoped Set action unambiguous.
- Unconditional supported curry and automatic certification of arbitrary
  predicates are refuted by the retained proved counterexamples. They are
  mathematical failures, not elaborator defects.

The transient failed proof scripts are not retained as standalone broken files;
their failure patterns and remedies are recorded here. The surviving probes
contain complete proofs without admissions. Unchecked proposals include the
full supported-curry implementation, all general correspondence adapters,
automation, future client scale and final predicate storage ergonomics.

## Investigation status

- [x] Inspect current branch/history/tree, delivered foundations and prior proposals.
- [x] Inspect pinned Mathlib candidates and Pitts' relevant full-book sections.
- [x] Compare A/B/C/D and identify the currying, empty-domain and predicate boundaries.
- [x] Reconcile bounded probes, independent interface investigations and their limitations.
- [x] Self-review the written specification and reconcile article/tracker content.
- [x] Author approved the written specification after the brainstorming delivery.
- [x] A separate implementation plan was subsequently prepared for review.
- [x] Author approved that plan for native execution; implementation and final review are complete.

## Verification record

Root directly elaborated the final `F05FunctionSpace.lean` (including the later
context-bound consumer), `F05Boundaries.lean`, and unchanged
`GeneralizationSupport.lean` with `lake env lean`: all exited 0 without
warnings. The first two print 15 and 10 representative axiom lists respectively;
all are confined to `propext`, `Classical.choice`, and `Quot.sound` (some use
fewer). The `#eval` identity consumer returns `true`. The old generalization
probe also prints standard-only axioms. These are fresh standalone source
elaborations using cached pinned imports, not a full Package rebuild or a clean
dependency bootstrap. No production Lean changed, so no new production build
or audit result is claimed.

The integrated article was compiled with:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error \
  -outdir=/tmp/nominal-f05-final-article main.tex
```

from `docs/article`. Markdown local targets, changed/new file whitespace,
`git diff --check`, article references and scope/status wording were checked.
The article records mathematics, not task IDs, review states or these commands.
At the end of that investigation the specification awaited review. The author
subsequently approved it and the implementation plan for native execution.
Production implementation and independent final review are now complete; see
the subsequent-delivery section above and the active roadmap. All changes remain
uncommitted.
