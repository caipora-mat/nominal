# Urban's nominal techniques: implications beyond function spaces

Date: 2026-10-07. Research and proposed task refinements, **not an implemented Package
interface or an approval of later work**. Baseline: `fasapa/nominal-package`,
`32f3dba551761881409bbc7453054e214e582269`. The existing F05 design work and other
working-tree changes are preserved.

The useful result of this comparison is a sharper division of responsibilities: F05 supplies
support reasoning about ordinary functions and supported values; F06 must establish
representative independence; PKG-03 must keep arbitrary motives and individually supported
avoidance objects; PKG-05 must distinguish primitive recursion from iteration and prove
every inferred bound; PKG-06 needs its own rule-refreshing criterion. The paper supplies
evidence for these requirements, not a mandate to copy Isabelle's carrier or global
instances.

## Source and verification boundary

The source read in full is Christian Urban, [*Nominal Techniques in
Isabelle/HOL*](https://urbanchr.github.io/Publications/nom-tech.pdf), the supplied **27-page
author manuscript**. All page references below use its printed pages. Its PDF creation
metadata is 2008-02-08 and its SHA-256 is
`b249192759a845fbe6d76b4734f52bce9809c9bb5af5c22e4dca265a6a5a7a63`. The journal citation is
*Journal of Automated Reasoning* **40**(4), 327–356 (2008), DOI
[10.1007/s10817-008-9097-2](https://doi.org/10.1007/s10817-008-9097-2). That bibliographic
pagination is not the pagination used here; the two PDFs have not been established textually
identical.

Evidence is source inspection, including visual checks of manuscript pages 14, 20 and 21
where mathematical text extraction needed checking. The PDF renderer reported Type 3 glyph
bounding-box warnings; the rendered pages were legible. There is **no new Isabelle build or
external formalization audit**. The temporary PDF/text/renderings are review aids, not
repository dependencies. This note adds no Lean declarations and makes no new Lean-build
claim.

Current implementation claims below were checked against
[Package/README.md](../../Package/README.md), the foundation modules, and the specific
reference Lean files linked below. Earlier research proposals are not treated as current
Package declarations. The [F05 investigation](2026-10-07-function-space-foundations.md) and
[written design](../superpowers/specs/2026-10-07-package-function-space-design.md) contain
the separate function-space decision and bounded Lean experiments.

## Findings that affect the mathematical contracts

### Actions and finite support remain separate

**Source:** Sections 1–2, pp. 2–7; Definitions 2–4, Proposition 1; Definition 5 and Lemma
11, p. 16. Urban permits arbitrary acted-on values and requires finite support where needed.
His support is a total, swap-defined set; his sufficient-bound criterion uses outside swaps.
Lemma 11 explicitly requires the proposed bound to be finite.

**Package comparison and implication:** The delivered selected `MulAction`, elementwise
`FinitelySupported`, and proof-only `Nominal` already embody the important separation.
Package's least finite support is deliberately defined only with a support certificate. Do
not replace it by Urban's total support definition or silently assign support to unsupported
objects. Before using a paper statement literally, translate its finite-support/freshness
assumptions to this certificate-based interface. General sufficient-set support does not
give minimality against arbitrary infinite bounds. The retained [support
probe](probes/GeneralizationSupport.lean) already records that limit.

### Strong induction needs supported avoidance values, not a supported motive

**Source:** Theorem 2, p. 14; specialization to equation (21), pp. 14–15. For an arbitrary
property `P t c` and a chosen map `f`, the support premise is

```text
∀ c, finite (supp (f c)).
```

The lambda step assumes freshness for `f c`, and each recursive hypothesis quantifies over
**every** context. The proof strengthens induction over both permutations and contexts.
Neither finite support of `f` as a function nor finite support/equivariance of `P` is a
premise. The simpler nominal-context rule takes `f = id`. Lemma 14, p. 18, instead uses a
constant avoidance map whose value is the supported handler tuple, even though the ambient
function carriers are not nominal.

**Proposed PKG-03 contract:** preserve a general selected-avoidance interface, not only a
nominal-context specialization. In schematic future Lean notation:

```text
{C : Type v} {D : Type w} [MulAction (Perm A) D]
(avoid : C → D) (havoid : ∀ c, FinitelySupported A (avoid c))
{P : Term A → C → Prop}

hVar : ∀ a c, P (var a) c
hApp : ∀ t u c, (∀ d, P t d) → (∀ d, P u d) → P (app t u) c
hLam : ∀ a t c, (havoid c).Fresh a → (∀ d, P t d) → P (lam a t) c
---------------------------------------------------------------------
∀ t c, P t c
```

This is a proposed signature, not a checked new declaration. `C` needs no action; `avoid`
needs no support or equivariance certificate. In particular, an arbitrary `avoid : C →
Finset A` supplies finite avoidance without requiring the function itself supported. No
claim is made that the binder avoids every captured object: it avoids precisely the selected
value.

The reference [`Term.strong_ind`](../../Instances/LambdaCalculus/Induction.lean) already
preserves arbitrary motives and all-context IHs, but its public context carrier is nominal
and shares the atom universe. The proposed elementwise interface is a future Package
improvement, not a correction of a false reference theorem. A regression should capture an
unsupported predicate in the motive, choose a supported avoidance object independently, and
actually use the resulting IH at an enlarged context.

### The recursion theorem is genuinely stronger than an iterator

**Source:** Theorem 3, p. 17; footnote 6, p. 16; graph (23) and Lemmas 12–14, pp. 18–19. The
handlers have schematic types

```text
f₁ : Atom → Y
f₂ : Term → Term → Y → Y → Y
f₃ : Atom → Term → Y → Y.
```

Original subterms and recursive results are both available. The result carrier only needs a
permutation action. Lemma 12 proves that graph outputs are finitely supported; Lemma 13
transports the graph while permuting **all three handlers**; Lemma 14 proves existence and
uniqueness. The function is extracted only after that proof. Its lambda equation is guarded
by freshness for the handler tuple.

**Package implication:** retain PKG-03's iteration contract and PKG-05's distinct
primitive-recursion deliverable. The reference
[`recNoContext`](../../Instances/LambdaCalculus/Recursion.lean) is an iterator: its
application and lambda handlers receive recursive values, not original children, and its
result carrier is nominal. Referring to Urban's graph does not make that reference API
primitive recursion. A Package recursor should test original-child access and consider an
arbitrary acted-on result carrier with individually supported outputs. A proof through an
iterator returning `Term × Y` is eligible, but must prove reconstruction, binder
admissibility, equations and uniqueness for that construction.

Fixed supported handlers are not thereby equivariant. A graph-transport or recursor-renaming
theorem must permute handlers/parameters together, or state the fixer condition for their
sufficient bound. The paper's Lemma 13 does not justify unqualified equivariance with
arbitrary fixed handlers.

### FCB controls output freshness and representative independence

**Source:** Definition 6 and Theorem 3, p. 17; Lemma 14, pp. 18–19; Definition 7 and Lemma
15, p. 19. The paper's binder condition is

```text
∀ a t r, a # f₃ → finite (supp r) → a # f₃ a t r.
```

It quantifies over all terms and **finitely supported** recursive values, not every value of
an arbitrary result carrier. Its existential fresh-atom variant is equivalent under finite
support of the handler. The uniqueness proof aligns competing representatives at a common
fresh name, transports both original children and outputs, then uses binder-output freshness
to remove the swaps.

**Proposed F06/PKG-03/PKG-05 boundary:** state whether the chosen sufficient condition
ranges over all results, individually supported results, or certified reachable pairs
`(originalChild, recursiveResult)`. The latter is a possible generalization, not something
this paper proves. Support of a handler alone does not establish binder descent. Prove the
representative-independence lemma before defining a result by choice; derive guarded
computation, output support, joint transport and any claimed uniqueness from the proved
construction. An explicit common finite bound is appropriate, but enlarging that bound must
not silently change the resulting operation.

The existing reference [`NameAbs.FCB_guarded_val_indep`](../../Nominal/Set/FCB.lean) is
useful evidence, with its nominal carrier and stated universal freshness premise. Its
signature does not already deliver the stronger arbitrary-carrier/elementwise contract. For
an unimplemented Package design, require no stronger premise merely to reuse this reference
lemma unchanged.

### The carrier construction is one backend, not a full-function syntax

**Source:** Section 3, pp. 8–13; abstraction formula (9), Lemmas 6–10, Theorem 1. An ambient
datatype contains a function constructor, but the term carrier is the inductively generated
subset containing only special partial abstraction functions. Their equality, renaming and
support are proved; the subset is then shown bijective with alpha classes. Section 7, p. 24,
distinguishes quotient construction from the additional work needed for strong induction and
recursion.

**Package implication:** PKG-02 may retain a quotient backend or compare this
restricted-function backend. An arbitrary type bijection, a full function field, or mere
quotient formation is insufficient evidence for the promised constructor, action,
exact-support, fresh-representative and induction laws. Do not import the ambient function
space as syntax without the generated-subset invariant. Urban's HOL subset-to-type
construction needs nonemptiness; Lean's planned empty-datatype consumer should remain,
because HOL's inhabited-type restriction is not a Lean requirement.

## Automation and rejection examples

**Source:** Section 5, Examples 1–2, pp. 16–17; Section 6, pp. 20–22. `finite_guess`
proposes bounds from captures and proves them by permutation rewriting. `fresh_guess` uses
established bounds to discharge handler-freshness guards. The binder-output condition is a
separate obligation in the worked substitution definition.

**PKG-05 inference:** adopt the proof pattern, not a syntactic assumption that every
capture/global is supported. Accept user-supplied sufficient bounds and certificates;
support inference need not compute least supports. The existing [automation
contract](2026-10-05-package-contracts.md#8-sound-support-automation-and-expression-identity)
already requires elaborated variable identity, coherent action instances and registered
theorems. Add concrete tests that distinguish:

1. a proposed capture bound and its proof;
2. a binder-output/descent proof;
3. the implication from a user-facing freshness guard to the recursor's guard.

Failure to prove a proposed bound is not proof of unsupportedness. Arbitrary function
captures need certificates, and an unsupported motive must remain valid for induction.
Include nested scopes/shadowing, fixed supported but non-equivariant captures, conditional
branches with proved action laws, and positive consumers whose conclusions use the generated
certificates.

**Negative semantics:** Section 5, p. 15, equation (22), excludes functions returning
representative bound names or the unabstracted immediate lambda body: alpha-equal identity
abstractions would give unequal outputs. These are alpha-compatibility failures, distinct
from failure to infer finite support. Retain them as explicit PKG-05 rejection examples.
They do not forbid a well-defined function returning an abstraction object or an
appropriately quotiented body representation.

Classical choice and finite support remain separate (Section 1, p. 2, and Section 7, pp.
22–24). Choice may extract a unique graph result once existence and uniqueness are proved;
it does not supply equivariance or support for an arbitrary global selector. The
Package-only [F05 boundaries probe](probes/F05Boundaries.lean) already proves that a
selector fresh for every input finite set cannot have finite support. No new ban on ordinary
Lean choice, unsupported functions or arbitrary Prop motives follows.

## Proposed tracker refinements

These are actionable future acceptance criteria. They do not complete tasks, authorize
implementation, or change the F05 design-review gate.

| Task | Proposed refinement | Verification consumer |
| --- | --- | --- |
| PKG-F05 | Keep the action/individual-support/carrier-nominality separation and ordinary-input support certificates. Treat capture-derived bounds as sufficient bounds with proofs. | Supported fixed-parameter function; unsupported ordinary input; function-object and pointwise-action separation. |
| PKG-F06 | Explicitly state the domain of the FCB premise and prove representative independence under the chosen finite support bounds. | Two different fresh representatives produce equal results; nested binder and binder-over-product; constant-atom failure retained. |
| PKG-01 | Preserve arbitrary motives independently of supported logical tools. | The same unsupported predicate is accepted as a motive and rejected only where a support certificate is required. |
| PKG-02 | Compare the quotient and restricted-abstraction-function constructions through actual constructor/action/support/induction interfaces, not bare bijections. | Alpha-equal constructors, exact abstraction support, fresh representatives, mixed scope and empty datatype. |
| PKG-03 | Add selected avoidance `avoid : C → D` with `∀ c, FinitelySupported A (avoid c)`; no support premise on `avoid` or the motive and no action on C. Consider individually supported outputs for the iterator's result carrier. | Arbitrary context/motive; IH at a changed context; supported handler values in a non-nominal full function carrier. |
| PKG-05 | Keep primitive recursion separate; prove original-child access, supported graph outputs, totality/uniqueness and guarded equations. Expose the three automation obligations listed above. | Consumer uses both a child and its recursive result; bound-name/body selector rejection; successful support proof used downstream. |
| PKG-06 | Keep fresh derivation induction conditional on a proved rule-refreshing criterion. Term induction and relation equivariance alone do not establish it. | Transport all affected premises while preserving the conclusion; every recursive derivation and generalized IH retained; reject an escaping eigenvariable. |
| PKG-11 | Explain these distinctions alongside function spaces; cite the manuscript pagination/version explicitly. | Article claims distinguish existing Package results, reference Lean code, published mathematics and proposed interfaces. |

Section 7, p. 24, explicitly warns that structural fresh induction does not automatically
extend to every inductive relation. Section 8, p. 25, reports nested single binders and
different atom sorts, but leaves finite sets of binders and varying-parameter recursion as
future work. These are historical limits of this paper, not claims about current Isabelle.
They support the repository's staged scope; they do not settle the newer judgment or
generalized binding contracts. Fixed external parameters, context-generalized induction and
recursive calls with varying parameters must remain distinct requirements.

## Manuscript cautions

Two visible statements should not be transcribed literally: p. 20 displays the application
handler with reversed recursive results, contrary to equation (24) and the code on p. 21; p.
21's Lemma 16 prints the replacement as the result of freshness-based substitution, while
its preceding explanation, proof and Isabelle statement correctly retain the original term.
These are apparent manuscript slips, confirmed in page images, not an Isabelle kernel
finding. No correction to external sources is claimed.

The bound in Lemma 11 must remain finite; Lemma 15 must retain handler finite support;
Theorem 2's pointwise premise must not be strengthened to support of the avoidance map or
motive. These three easily missed details materially affect the proposed Package interfaces.
