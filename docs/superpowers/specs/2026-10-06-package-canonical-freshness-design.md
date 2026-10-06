# F04c: canonical instances and atom freshness

**Subsequent author-directed generalization (2026-10-06):** after this original
delivery, the author approved Pitts' general support-disjointness relation.
The initial atom-only scope and exact `Fresh` signature below are retained as
history and are superseded by the extension recorded at the end of this file.
Atom theorem calls remain supported as specializations. The author's approval
of the bounded follow-up authorizes its implementation; no earlier approval is
reopened.

Date: 2026-10-06. **Written specification approved by the author.**
Task: **PKG-F04, slice F04c**, with concurrent article work under **PKG-11**.
The [package roadmap](../../nominal-package-roadmap.md) owns status and phase
boundaries. Native execution with one fresh independent final review is already
selected. The author approved this specification on 2026-10-06. Its
[native implementation plan](../plans/2026-10-06-package-canonical-freshness.md)
was subsequently approved for native execution. Code, consumers, audit and article pass. Independent final review is resolved;
F04c is delivered, uncommitted.

## Intended outcome and preserved decisions

Make the delivered support theory usable for ordinary avoidance arguments.
Certify the canonical actions on atoms, discrete data, products and finite atom
sets; compute their exact least supports; define atom-versus-element freshness;
and choose atoms fresh for finite combined contexts. An individually supported
element must remain usable without nominality of its entire carrier.

Reuse `Supports`, `FinitelySupported`, proof-only `Nominal`, `hx.support` and
`support A x` as delivered. Neither least-support construction, binary
intersection nor conjugation transport is repeated. A nominality certificate
certifies an already selected action and never supplies another action.
Preserve `NominalPackage`, `Perm A`, independent universes, the pinned versions,
the consumer's `Pointwise` scope and all existing action choices.

New implementation belongs under `Package/`. Preserve the reference `Nominal/`,
`Instances/`, existing examples, historical `docs/roadmap.md`, tracked/untracked
and subsequent work. Do not commit, switch branches, push, publish, merge,
change dependencies or add CI. Earlier F02/F03a/F03b/F04a/F04b approvals stand.
The supplied first-session scope authorized this written design directly.
The author's subsequent approval authorizes its implementation plan; production
changes still require approval of that concrete written plan.

## Inspected baseline

The requested checkout is on `fasapa/nominal-package`, HEAD
`68956dd23066c7c5c647345e5598b859ff97a10c`, with a clean initial working tree.
`git log` and `git show --stat HEAD` confirm committed F04a/F04b source, article
and design/tracker changes, following F03b at `34a8335`. Earlier descriptions of
uncommitted delivery record the state at those sessions; they are not the
current checkout state.

Inspected inputs include AGENTS.md, both READMEs, Package.lean, all five
foundation modules, the production audit and import checker, the active F04
tracker, research guide, readiness and article-plan notes, F04b's specification
and native plan, and main.tex with all four included sections. The F04a
specification/plan, research brief, predicate-foundations note, historical
roadmap and development review were consulted for relevant constraints.
Historical proposed APIs do not supersede delivered interfaces or this scope.

Lean is pinned to `v4.34.1`. Both the manifest and installed Mathlib checkout
identify `d13f23b723b8a846827a245b89c10fc7d3f11612` (`v4.34.1`). A temporary
import/`#check`/`#synth` inventory confirms the APIs below without defining any
proposed F04c result. The initial 117 tracked/untracked files were fingerprinted
under `/tmp/nominal-f04c-design-n_6qp3g8/`.

Fresh design-session baseline checks, separate from historical delivery:

- `lake build Package +Package.Tests.AxiomAudit`: passed, 970 jobs, reusing
  cached project/dependency artifacts and replaying compiled audit output.
- `lake env lean Package/Tests/AxiomAudit.lean`: passed; direct traversal of
  132 production declarations from five defining modules, with only `propext`,
  `Classical.choice` and `Quot.sound`.
- `python3 Package/Scripts/check-imports.py`: passed; six production source
  modules including the root and one audit module reached. Checker unchanged.
- `lake env lean /tmp/nominal-f04c-design-n_6qp3g8/PinnedAPI.lean`: passed;
  checked existing APIs, independent universes and selected action synthesis.
- The separate `UnscopedFinset.lean` import/synthesis check exited 1 with the
  intended failure to synthesize `MulAction (Perm A) (Finset A)` without
  Pointwise. The scoped inventory check succeeds, confirming the current boundary.
- Direct checks of `/tmp/nominal-f04b-execution/BoundaryContracts.lean` and
  `/tmp/nominal-f02-f03a-execution/{ActionContracts,NegativeContracts}.lean`
  passed. These preserve actual Bool, unsupported-function and action evidence.
- The documented `latexmk` invocation from docs/article/ succeeded with all
  outputs already current. The existing 16-page log has no warning, unresolved
  reference or box diagnostic; no fresh PDF compilation is claimed.
- `git diff --check` passed before document edits.

These checks concern the delivered baseline. No F04c production proof, fresh
whole-project build, dependency bootstrap or reference-library rebuild has
been performed during design.

## Interface alternatives and recommendation

The alternatives concern only the new freshness interface; the foundations and
phase boundaries are settled.

| Approach | Consequence |
| --- | --- |
| **Approved: certificate-based predicate and carrier adapter** | `hx.Fresh a` means nonmembership in `hx.support`; `Fresh A a x` uses the nominality projection. This follows the existing support interfaces, keeps evidence explicit where needed and permits short nominal-carrier proofs. |
| Carrier predicate only, with clients writing raw support nonmembership for individual elements | Smaller named API, but individual-element clients lose the same transport, decomposition and existence vocabulary available to nominal carriers. |
| An existential predicate saying some finite supporting bound avoids the atom | Can be stated without carrier nominality and without a supplied certificate, but changes the requested primary meaning and obscures the infinite-atom least-support boundary. A second support-based predicate is unnecessary here. |

Use the first approach. Export **no new notation in this slice**: the exact
forms are `hx.Fresh a` and `Fresh A a x`. They make the atom sort and evidence
boundary visible without importing the legacy binary relation or its `#`
notation. A scoped notation can be justified by future concrete clients; none
is needed for the proposed consumers. `Fresh` here names atom freshness, not
the cofinite quantifier called `Fresh` in an older, unapproved predicate sketch.
The later quantifier's interface is outside this decision.

## Pinned Mathlib and delivered-theory reuse

Paths in this table are relative to `.lake/packages/mathlib/Mathlib/`.

| Existing declaration/source | Use and exact boundary |
| --- | --- |
| `MulAction.supports_of_mem`, `GroupTheory/GroupAction/Support.lean:42` | A member of a supporting set is supported by that set under the same action. Specialize to the canonical atom action and singleton membership. No infinitude or equality instance. |
| Singleton instance, `Finset.mem_singleton`, `singleton_subset_iff`, `Data/Finset/Insert.lean:61–74,145` | Singleton formation and these membership/subset laws do **not** require `DecidableEq`. Atom support statements need no equality parameter. |
| `Finset.image_congr`, `image_id'`, `mem_image_of_mem`, `Data/Finset/Image.lean` | Pointwise fixation gives equality of a finite set's image with itself; membership is transported to that image. The codomain equality instance is required. |
| `Finset.notMem_union`, `union_subset_iff`, `Data/Finset/Lattice/Basic.lean:115,300` | Exact product support and decomposition of finite avoidance. Visible union retains `DecidableEq`; proof-local unions do not force it into the statement. |
| `Finset.exists_notMem`, `Data/Set/Finite/Basic.lean:847` | `∀ [Infinite A] (S : Finset A), ∃ a, a ∉ S`, with no `DecidableEq`. Use this directly for explicit-set avoidance; do not add an alias or selector. |
| `Prod.mulAction`, `Algebra/Group/Action/Prod.lean:88` | Existing componentwise product action with independent universes; certify it, do not replace it. |
| `Finset.mulActionFinset` and its `Pointwise` registration, `Algebra/Group/Action/Pointwise/Finset.lean:94–101` | Existing image action, requiring decidable equality. Preserve the action synthesized by the delivered imports, including subgroup restriction; do not force a competing instance path. |
| `Finset.smul_mem_smul_finset_iff`, `inv_smul_mem_iff`, same file:163,171 | Membership under simultaneous image and inverse image. With proof-local classical equality, these discharge freshness transport without a public equality premise. |
| Package `Perm.smul_atom`, `.smul_finset`, `.mem_smul_finset`, swap equations | Stable selected-action equations and moving-atom arguments. No new group or image-action theory. |
| Package `FinitelySupported.prod`, `supports_prod`, `supports_prod_iff`, `supports_map`, `swap_smul_eq_of_supports` | Nominality of products, both directions of the exact product argument, and fresh-swap fixation. No factorization or swap-criterion proof is repeated. |
| Package elementwise support/minimality/uniqueness, `support_smul`, `support_eq` | All least-support reasoning, renaming and certificate agreement. No second choice or parallel support theory. |

The new nominal mathematics is the exact canonical support identification and
its freshness consequences. Mathlib already supplies the general finite-set,
infinite-type and action infrastructure. Existing imports expose the needed
APIs; no new Mathlib dependency is expected.

## Exact approved public interface

All declarations are in `NominalPackage`. Blocks specify independent contexts;
`u`, `v` and `w` are independent universes. Signatures below are the approved
contracts, not claims that these declarations already exist.

### Canonical certificates and sufficient bounds

```lean
universe u v w

theorem supports_atom (A : Type u) (a : A) : Supports ({a} : Finset A) a

theorem supports_discrete (A : Type u) {X : Type v} (d : Discrete A X) :
    Supports (∅ : Finset A) d

instance instNominalAtom (A : Type u) : Nominal A A

instance instNominalDiscrete (A : Type u) (X : Type v) :
    Nominal A (Discrete A X)

instance instNominalProd (A : Type u) {X : Type v} {Y : Type w}
    [MulAction (Perm A) X] [MulAction (Perm A) Y]
    [Nominal A X] [Nominal A Y] : Nominal A (X × Y)

open scoped Pointwise

theorem supports_finset (A : Type u) [DecidableEq A] (S : Finset A) :
    Supports S S

theorem instNominalFinset (A : Type u) [DecidableEq A] : Nominal A (Finset A)

scoped[Pointwise] attribute [instance] NominalPackage.instNominalFinset
```

The last theorem is a proof of nominality registered as a scoped instance,
following Mathlib's existing scoped-attribute pattern. The other three
certificates are ordinary instances at standard priority. **None introduces a
`MulAction`.** Declare atom, discrete and Finset results without an arbitrary
action parameter on those carriers. Products quantify only over the component
actions; their product action is Mathlib's componentwise one. Thus the resulting
types refer to the concrete canonical actions even if a client locally selects
an unrelated action on the same underlying type.

Execution made one mechanical adjustment to the proposed encoding:
`instNominalFinset` is a `theorem` rather than a proof-only `def`, and the
scoped attribute uses its fully qualified name. Pinned Lean warned about a
class-valued/propositional `def`, and the scoped command resolves names in
Pointwise. The public name, type, assumptions and scope are unchanged; no
linter or reducibility policy was relaxed.

None of these certificates requires `Infinite A`. Neither the discrete bound
nor its certificate assumes any action, equality, infinitude or nominality on
X. The product certificate uses `FinitelySupported.prod` on the two class
projections and needs no atom equality instance. Only Finset retains
`DecidableEq A`, required by its selected action. Neither importing Package nor
opening `NominalPackage` globally enables the `Pointwise` action or certificate.

### Exact canonical least supports

```lean
universe u v w

@[simp] theorem support_atom (A : Type u) [Infinite A] (a : A) :
    support A a = {a}

@[simp] theorem support_discrete (A : Type u) [Infinite A]
    {X : Type v} (d : Discrete A X) : support A d = ∅

theorem FinitelySupported.support_prod {A : Type u} {X : Type v} {Y : Type w}
    [MulAction (Perm A) X] [MulAction (Perm A) Y]
    [Infinite A] [DecidableEq A] {x : X} {y : Y}
    (hx : FinitelySupported A x) (hy : FinitelySupported A y) :
    (hx.prod hy).support = hx.support ∪ hy.support

@[simp] theorem support_prod (A : Type u) {X : Type v} {Y : Type w}
    [MulAction (Perm A) X] [MulAction (Perm A) Y]
    [Infinite A] [DecidableEq A] [Nominal A X] [Nominal A Y]
    (x : X) (y : Y) : support A (x, y) = support A x ∪ support A y

open scoped Pointwise

@[simp] theorem support_finset (A : Type u) [Infinite A] [DecidableEq A]
    (S : Finset A) : support A S = S
```

The discrete theorem accepts any wrapped value; taking `d := Discrete.mk x`
gives the requested constructor formula. All carrier theorems take A explicitly.
Atom and discrete formulas need no decidable equality. Product union and the
Finset image action retain it. Canonical certificates discharge nominality of
atoms, discrete values and Finsets; no extra abstract nominality premise is
added to their formulas.

The elementwise product equality is needed for freshness decomposition in
carriers without nominality. It assumes neither carrier nominal. For the other
three canonical types, the delivered `support_eq A x hx` gives the formula for
any supplied element certificate; additional elementwise copies would duplicate
that bridge. For example, `(support_eq A a hx).symm.trans (support_atom A a)`
identifies `hx.support` with `{a}`.

### Elementwise atom freshness

```lean
universe u v w
variable {A : Type u} {X : Type v}
variable [MulAction (Perm A) X] [Infinite A]
variable {x : X} {S : Finset A}

def FinitelySupported.Fresh (hx : FinitelySupported A x) (a : A) : Prop :=
  a ∉ hx.support

theorem FinitelySupported.fresh_iff_notMem_support
    (hx : FinitelySupported A x) (a : A) :
    hx.Fresh a ↔ a ∉ hx.support

theorem FinitelySupported.fresh_of_supports (hx : FinitelySupported A x)
    (hS : Supports S x) {a : A} (ha : a ∉ S) : hx.Fresh a

@[simp] theorem FinitelySupported.fresh_smul_iff
    (hx : FinitelySupported A x) (π : Perm A) (a : A) :
    (hx.smul π).Fresh (π a) ↔ hx.Fresh a

theorem FinitelySupported.fresh_smul_iff_inv
    (hx : FinitelySupported A x) (π : Perm A) (a : A) :
    (hx.smul π).Fresh a ↔ hx.Fresh (π⁻¹ a)

theorem FinitelySupported.swap_smul_eq_of_fresh [DecidableEq A]
    (hx : FinitelySupported A x) {a b : A}
    (ha : hx.Fresh a) (hb : hx.Fresh b) : Perm.swap a b • x = x

@[simp] theorem FinitelySupported.fresh_prod_iff
    {Y : Type w} [MulAction (Perm A) Y] {y : Y}
    (hx : FinitelySupported A x) (hy : FinitelySupported A y) (a : A) :
    (hx.prod hy).Fresh a ↔ hx.Fresh a ∧ hy.Fresh a
```

`hx` determines A, x and the selected action, so those parameters remain
implicit in these methods. `hx.Fresh a` has an explicit certificate and atom;
the entire carrier need not be nominal. `hS.finitelySupported` supplies the
certificate when a client starts with a bound alone.

Transport and product decomposition have no public `DecidableEq A` premise:
their statements contain no finite-set image or union. Local classical
equality permits use of the existing support transport and the product formula
inside their proofs. Both directions of simultaneous transport are provided by
the iff; the inverse-image form supports moving only one side of a freshness
goal. Swaps retain decidable equality and require **no** `a ≠ b` premise.

For any `hx hx' : FinitelySupported A x` under the same selected action,
`hx.Fresh a ↔ hx'.Fresh a` follows from `hx.support_eq hx'` (also proof
irrelevance). In particular, independently supplied certificates of a renamed
element or a pair agree with `hx.smul π` or `hx.prod hy`. Do not add a new
choice, supported-element subtype or parallel equality theory.

### Convenient freshness for nominal carriers

```lean
universe u v w
variable (A : Type u) {X : Type v}
variable [MulAction (Perm A) X] [Infinite A] [Nominal A X]

def Fresh (a : A) (x : X) : Prop :=
  (Nominal.finitelySupported (A := A) x).Fresh a

theorem fresh_iff_notMem_support (a : A) (x : X) :
    Fresh A a x ↔ a ∉ support A x

theorem fresh_iff (a : A) (x : X) (hx : FinitelySupported A x) :
    Fresh A a x ↔ hx.Fresh a

theorem fresh_of_supports {x : X} {S : Finset A}
    (hS : Supports S x) {a : A} (ha : a ∉ S) : Fresh A a x

@[simp] theorem fresh_smul_iff (π : Perm A) (a : A) (x : X) :
    Fresh A (π a) (π • x) ↔ Fresh A a x

theorem fresh_smul_iff_inv (π : Perm A) (a : A) (x : X) :
    Fresh A a (π • x) ↔ Fresh A (π⁻¹ a) x

theorem swap_smul_eq_of_fresh [DecidableEq A] {x : X} {a b : A}
    (ha : Fresh A a x) (hb : Fresh A b x) : Perm.swap a b • x = x

@[simp] theorem fresh_prod_iff {Y : Type w}
    [MulAction (Perm A) Y] [Nominal A Y] (a : A) (x : X) (y : Y) :
    Fresh A a (x, y) ↔ Fresh A a x ∧ Fresh A a y
```

Every declaration in this block takes A explicitly, in the same style as the
delivered carrier support interface. `Fresh` has binder order A, X, selected
action, infinitude, nominality, a, x. `fresh_iff A a x hx` bridges the two
interfaces for any evidence of that element under that action. Changing the
carrier's proof-only nominality certificate also changes nothing. These are
thin adapters, with no repeated mathematical proof or stronger hypothesis on
the elementwise side.

Canonical computation uses separate contexts, with their concrete actions:

```lean
universe u v

@[simp] theorem fresh_atom_iff (A : Type u) [Infinite A] (a b : A) :
    Fresh A a b ↔ a ≠ b

@[simp] theorem fresh_discrete (A : Type u) [Infinite A]
    {X : Type v} (a : A) (d : Discrete A X) : Fresh A a d

open scoped Pointwise

@[simp] theorem fresh_finset_iff (A : Type u) [Infinite A] [DecidableEq A]
    (a : A) (S : Finset A) : Fresh A a S ↔ a ∉ S
```

Repeated `fresh_prod_iff` handles either association of nested products; no
dedicated triple or arbitrary-container API is needed. Finset union/insert
avoidance uses `fresh_finset_iff` and ordinary Mathlib membership simplification.
For example, a context `(x, (y, (S, Discrete.mk d)))` decomposes to freshness
for x and y and nonmembership in S, with no action assumed on the type of d.

The declared simp rules reduce canonical support or freshness, remove a common
permutation, or split a product into smaller components. Do not make the raw
freshness definitions, certificate bridge, inverse-image transport, support
choice, quantified support criteria or existence laws global simp rules. No
new priorities, reducibility settings or linter suppression are needed.

### Fresh existence and explicit avoidance

For avoiding only a finite S, use the existing `Finset.exists_notMem S`
directly, with `[Infinite A]` and no equality assumption or support evidence.
Add only these context interfaces:

```lean
universe u v
variable {A : Type u} {X : Type v}
variable [MulAction (Perm A) X] [Infinite A] {x : X}

theorem FinitelySupported.exists_fresh (hx : FinitelySupported A x) :
    ∃ a : A, hx.Fresh a

theorem FinitelySupported.exists_fresh_notMem
    (hx : FinitelySupported A x) (S : Finset A) :
    ∃ a : A, a ∉ S ∧ hx.Fresh a

variable (A) [Nominal A X]

theorem exists_fresh (x : X) : ∃ a : A, Fresh A a x

theorem exists_fresh_notMem (S : Finset A) (x : X) :
    ∃ a : A, a ∉ S ∧ Fresh A a x
```

These four statements require no `DecidableEq A`. A witness outside
`S ∪ hx.support` is chosen inside the proof using local classical equality.
Nominality is needed only for the two carrier adapters. To avoid several
individually supported elements, use `.prod` certificates and
`.fresh_prod_iff`; for nominal contexts use ordinary nested products.
If a Finset is itself a context component, its image action still requires
the consumer's `Pointwise` scope and decidable equality. Merely supplying S
as an explicit exclusion bound imposes neither requirement.

All witness construction remains in existential proofs. Export no selected
atom function, equivariant selection claim, executable search or purported
finite support of a selector.

### Assumption summary

| Operation/law | Atom assumptions | Carrier/evidence requirement |
| --- | --- | --- |
| Atom/discrete nominality and sufficient bounds | None | Canonical actions; no assumption on underlying discrete data |
| Product nominality | None | Selected component actions and their nominality certificates |
| Finset nominality and sufficient bound | `DecidableEq A`, scoped `Pointwise` | Existing image action |
| Atom/discrete exact support | `Infinite A` | Canonical certificates |
| Exact product support | `Infinite A`, `DecidableEq A` | Two individual certificates, or nominal components for carrier notation |
| Exact Finset support | `Infinite A`, `DecidableEq A`, scoped `Pointwise` | Existing image action and its certificate |
| Freshness, sufficient-bound implication, transport, product decomposition and fresh existence | `Infinite A` | Individual certificate, or selected action and nominality for convenience |
| Atom/discrete freshness computation | `Infinite A` | Canonical action, no equality/underlying-data assumptions |
| Finset freshness computation | `Infinite A`, `DecidableEq A`, scoped `Pointwise` | Existing image action |
| Fresh-swap fixation | `Infinite A`, `DecidableEq A` | Individual or carrier certificate; no endpoint inequality |
| Explicit-set avoidance via Mathlib | `Infinite A` | Finite set only; no action or nominality |

No interface assumes countability or identifies atom/carrier universes. More
specific context actions can carry their own hypotheses, such as the Finset
action's equality instance; the generic freshness laws add none of those.

## Proof strategies and mathematical boundaries

**Canonical nominality.** A singleton supports its atom by Mathlib's
`supports_of_mem`; the empty set supports every discrete value by invariance.
For Finsets, a permutation fixing S pointwise has `S.image π = S` by
`Finset.image_congr` and `image_id'`, hence fixes S under the existing action.
Package's `.finitelySupported` converts these bounds to certificates. The
product instance applies the delivered `.prod` to the component certificates.

**Atoms: both inclusions.** The singleton bound gives
`support A a ⊆ {a}`. If a finite bound T supporting a omitted a, choose b
outside `insert a T`. The swap of a and b fixes T pointwise but moves a,
contradicting support. Thus every supporting T contains a; in particular the
least support does. Classical equality is internal to this argument.

**Discrete data: exact emptiness.** The empty set supports the value, hence
leastness gives containment in empty; the reverse containment is automatic.
The general F04b empty-support characterization is an equivalent short proof.

**Products: both inclusions.** The union of the two least supports supports
the pair, so bounds its least support from above. Conversely, the pair's least
support supports each projection by `supports_prod_iff` (equivalently the
equivariant projection laws). Component minimality gives both containments
into the pair's least support; union containment gives the reverse inclusion.
Prove this for `hx` and `hy`, then obtain the carrier formula by agreement.

**Finite atom sets: both inclusions.** S supports itself, giving
`support A S ⊆ S`. For the converse, suppose T supports S but omits some
`a ∈ S`. Choose `b ∉ S ∪ T`. Both swap endpoints lie outside T, so the
delivered swap consequence says that the swap fixes S. Its image nevertheless
contains b, the image of a, contradicting `b ∉ S`. Thus `S ⊆ T` for every
finite support T, in particular the least one. This uses actual image
membership, not the false converse that fixation of S fixes its atoms.

**Freshness laws.** Minimality sends nonmembership in a sufficient bound to
nonmembership in least support. For transport, apply the delivered elementwise
`support_smul`, then Mathlib's simultaneous-image membership equivalence; inverse
transport follows by the inverse action laws. This reuses conjugation transport
without re-proving it. Fresh-swap fixation applies `swap_smul_eq_of_supports`
to the least supporting bound. Canonical computation follows from exact
support, and product decomposition uses `Finset.notMem_union` with classical
equality confined to the proof. No distinctness case split is needed for the
fresh-swap statement.

**Fresh existence.** Apply `Finset.exists_notMem` to the least support, or to
its union with an explicit finite exclusion set. Decompose the resulting
nonmembership. Combining contexts is a use of the proved product laws, not a
new freshness relation or container construction.

**Least support is not strong support.** Retain this explicit temporary
public-import consumer (under `Pointwise`), and its mathematical account in
the article:

```lean
theorem unordered_pair_boundary (A : Type u) [Infinite A] [DecidableEq A]
    (a b : A) (hab : a ≠ b) :
    let S : Finset A := {a, b}
    Perm.swap a b • S = S ∧
      a ∈ support A S ∧ b ∈ support A S ∧
      Perm.swap a b a ≠ a ∧ Perm.swap a b b ≠ b
```

Use `support_finset A S` for both actual support memberships. Prove image
fixation and movement by the existing image/swap equations. The assertion
cannot be satisfied merely by supplying a larger supporting bound. Keep the
consumer source and command in the implementation evidence; do not introduce
a general strong-support predicate or a standalone Package/Examples layer.

Retain the checked Bool evidence: the canonical Bool action is nominal, but
false has two disjoint singleton supports and no least support. New instance
synthesis must work on finite atoms; the infinite-atom formulas and fresh
existence must not be generalized to them. Bare functions keep pointwise
action, including supported constants and an unsupported identity on Nat;
bare permutations keep left multiplication. Neither receives a blanket
nominality instance. Equivariant-image support remains inclusion, possibly
strict; this increment does not add a general equality theorem for images.

## Modules and bounded integration

Add two production modules:

```text
Package.Foundations.Canonical  imports Package.Foundations.Nominal
Package.Foundations.Freshness  imports Package.Foundations.Canonical
```

`Canonical.lean` owns the sufficient bounds, four certificates and exact support
formulas, including the elementwise product formula. `Freshness.lean` owns
freshness predicates, laws, computation and existence. Both reuse the delivered
dependency chain; no backwards import into Nominal.lean is required. Explicitly
export both from Package.lean after Nominal. Preserve all five existing
foundation modules.

| File | Responsibility after approval |
| --- | --- |
| `Package/Foundations/Canonical.lean` (new) | Canonical certificates and exact support |
| `Package/Foundations/Freshness.lean` (new) | Elementwise/carrier freshness and finite combined avoidance |
| `Package.lean` | Explicit public exports of both modules |
| `Package/Tests/AxiomAudit.lean` | Representative new prints, unchanged whole-production traversal |
| `Package/README.md` | Actual interfaces, scope/assumption policy, useful calls and remaining boundaries |
| `docs/article/sections/freshness.tex` (new) | Concurrent mathematical exposition, labels `sec:canonical-support` and `sec:freshness` |
| `docs/article/main.tex`, `sections/introduction.tex` | Include freshness.tex, reconcile abstract and exposition/cross-references |
| `docs/article/sections/foundations.tex`, `support.tex`, `perspectives.tex` | Focused cross-references and reconciliation where the new results clarify existing claims |
| Active roadmap, this specification and eventual plan | Approvals, verification, source preservation and delivered status |
| Research README, readiness and article-plan notes | Current-state reconciliation during delivery; preserve dated historical evidence |

The checker/audit already classify `Package.Foundations.*` as production.
Expected source coverage is eight production modules including the root and one
audit module; measure actual defining-module and declaration counts. No checker,
Lake, shared validation script or dependency edit is expected. Run checker
self-tests if a justified checker change becomes necessary.

F04d owns canonical quotient actions/support bounds. F05/PKG-01 own function
objects, SupportsMap/SupportsPred, predicate bundles and Some/Any. Abstraction,
FCB, recursion, generators and other container instances remain later work.
No general binary freshness relation, tactic, countability assumption, Name
class or selector is introduced. Native execution is in the requested checkout,
with one independent final review after integrated validation; do not repeat
the execution-method question or earlier approvals.

## Concurrent article obligation

Include freshness.tex after support.tex and before perspectives.tex. Present
canonical support and atom freshness as two labelled sections, explaining the
mathematical concepts before their Lean encoding. Develop the LaTeX alongside
the proofs and reconcile against the final declarations before completion.

The exposition must cover:

1. Why the four selected actions are nominal, and why these certificates do
   not require infinite atoms. Discrete data has no assumed underlying action.
2. The four exact support formulas under infinite atoms. Explain the upper
   bounds and the reverse arguments: a fresh swap for atoms and Finsets,
   projection support for products, and the least empty bound for discrete data.
3. Atom freshness as least-support nonmembership, use of sufficient bounds,
   the elementwise certificate and carrier convenience, and their agreement.
4. Simultaneous transport in both directions and the fresh-swap consequence,
   including equal endpoints. Attribute image-membership reasoning to Mathlib
   and refer back to the established support transport and swap criterion.
5. Canonical computation and finite combined avoidance. Give a nested context
   example and the finite-union proof of fresh existence. No algorithm or
   equivariant selector is asserted.
6. The unordered-pair counterexample using its exact least support. Connect it
   to the preceding setwise/pointwise distinction and retain the Bool boundary.

Update abstract/introduction and focused related exposition as needed. Explain
reuse of the prior finite/least-support results without copying their proofs
or using task IDs in the manuscript. Select useful Lean correspondence rather
than presenting a complete API catalogue. The
[publication policy](../../research/2026-10-05-article-plan.md#publication-content-policy)
keeps approvals, delivery narratives, commands, counts, cache conditions and
review verdicts in the roadmap/implementation notes. No new external research
comparison or novelty claim is required for this bounded increment.

## Acceptance and completion

Temporary consumers import **only `Package`**, use independent universes and
consume actual mathematical conclusions. Preserve their sources and logs under
a fresh `/tmp` execution directory; add no persistent Package/Examples layer.

| Consumer obligation | Required evidence |
| --- | --- |
| Exact public signatures and minimal assumptions | Assign every new public declaration its specified type. Check nominal synthesis for atoms/discrete/products without infinitude or equality, and Finsets with equality and Pointwise only. No surrounding classical context may mask an unintended public assumption. |
| Canonical action policy | Check atom application, product components, discrete fixation and Finset images, plus bare-function pointwise and bare-permutation left actions. An arbitrary local action on a canonical carrier must not acquire these certificates/formulas by pretending to be canonical. |
| Scope preservation | In a fresh public-import file without Pointwise, Finset image-action synthesis remains unavailable; opening the scope locally supplies it and its nominality certificate. Leaving that scope restores the boundary. |
| Exact support and both inclusions | Exercise all four formulas, including an atom/discrete formula without equality, generic product components in independent universes, elementwise product support, and membership in both sides of Finset equality. |
| Freshness and canonical decomposition | Derive inequality, Finset nonmembership, unconditional discrete freshness, both directions of product iff, and decomposition of nested contexts. Exercise finite-set unions/inserts via existing membership lemmas. |
| Sufficient bounds | From arbitrary `Supports S x` and nonmembership, derive freshness for arbitrary hx, and for a nominal carrier; then use it in swap fixation. Use a bound strictly larger than least support too. |
| Transport and inverse | Consume both directions of simultaneous transport and the inverse-image iff, at both evidence and carrier interfaces. Generic statements need no equality or Pointwise; test separately supplied evidence for the renamed element. |
| Evidence agreement | Compare two proofs of finite supportedness, elementwise/carrier freshness, and two nominality certificates for the same selected action. Use supported pointwise constants without making the function carrier nominal. |
| Equal swap endpoints | Apply the new fresh-swap law with a = b, retaining actual freshness evidence and concluding fixation. Also test distinct fresh endpoints. No unnecessary inequality premise. |
| Fresh existence and combined avoidance | Use `Finset.exists_notMem`, both elementwise existence laws and both carrier adapters. Decompose witnesses into actual nonmembership/freshness for nested products. Choose two fresh atoms in succession, excluding the first on the second choice, and conclude a swap fixes the context and its components. |
| Least versus strong support | Prove `unordered_pair_boundary` above using the proved exact Finset support formula. Both moved atoms belong to the actual least support. |
| Finite/non-nominal boundaries | Reuse the Bool least-support obstruction with new canonical nominality synthesis; retain unsupported pointwise identity evidence and no blanket function/permutation certificates. |

Compile affected modules while iterating and check supported dependents. The
audit's module-origin traversal must cover every new production declaration,
including private/generated names. Add representative `#print axioms` for
canonical certificates, all exact support formulas, certificate freshness,
transport, product decomposition, swap fixation, existence and agreement.
Allow only `propext`, `Classical.choice` and `Quot.sound`; no admissions, custom
axioms, disabled kernel checking or weakened statements.

Required integrated commands after the final production edits:

```sh
lake build Package +Package.Tests.AxiomAudit
lake env lean Package/Tests/AxiomAudit.lean
python3 Package/Scripts/check-imports.py
git diff --check
```

Also run each temporary consumer, direct affected-module checks and checker
self-tests if the checker changes. From docs/article/ run:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error \
  -outdir=/tmp/nominal-package-article-build main.tex
```

Keep generated files outside the source tree. Inspect final diagnostics,
references and mathematical correspondence separately from compilation. Check
local document links, untracked-file whitespace, preservation against the
execution baseline and any subsequent edits. If shared integration changes
affect reference targets, validate their preservation separately; otherwise
report source preservation without claiming a reference rebuild. Record actual
commands and distinguish cached builds, fresh project builds using cached
dependencies and clean dependency bootstraps.

After native implementation and integrated validation, one fresh independent
final reviewer checks statement strength, both inclusions, selected actions,
assumptions, evidence independence, meaningful consumers, manuscript
correspondence and preservation. Resolve findings and rerun affected checks.
Mark F04c complete only after code, consumers, audit, article and final review
pass. PKG-F04 stays open until F04d and all overall obligations are delivered.

## Design handoff

Self-review covers the exact public arguments, all four concrete actions, both
inclusions, the equality/infinitude separation, evidence and carrier agreement,
freshness simp direction, nested avoidance, phase boundaries and article work.
No mathematical choice is deferred inside this approved contract. This file
and the active tracker are design work; Lean and manuscript sources remain
unchanged. The author approved this concrete specification on 2026-10-06.
Its native implementation plan was subsequently approved; native execution
and the independent final review are complete.

Design-session document checks passed for the two changed/new Markdown files: 57 local links,
six anchors, balanced fences, no unresolved placeholders, and whitespace
including the untracked specification. `git diff --check` passed. Fingerprint
comparison preserves 116 of 117 baseline files; only the active roadmap changed,
alongside this new specification. Its historical work log is preserved verbatim.
Branch, HEAD, production code, pins, reference sources, historical roadmap and
manuscript are unchanged. No independent implementation review is claimed.

The [native plan](../plans/2026-10-06-package-canonical-freshness.md) assigns
the unchanged contract to four mathematical tasks and one integrated
validation/documentation/review task. Each mathematical task develops its
LaTeX alongside Lean. Seven temporary public-import consumers cover all
34 production declarations and the mathematical boundaries. The seven Lean
blocks above, including the unordered-pair consumer statement, are unchanged
by planning. Specification approval and the selected native execution method
remain satisfied; do not request them again. Production implementation and
the final independent review are now assigned to the approved execution.

## Native implementation evidence

All 34 public declarations now compile in Canonical.lean and Freshness.lean.
The three simple bounds and four certificates require no infinitude; the exact
formulas use delivered leastness and both inclusions. Freshness and combined
avoidance retain their elementwise/carrier interfaces and approved assumptions.
Generic certificate-product simplification needs explicit theorem specialization,
such as `hx.fresh_prod_iff hy a`, since proof irrelevance prevents recovering
both certificates from the product proof. Carrier decomposition simplifies
automatically. This usage detail is documented and exercised without changing
any public type or simp attribute.

Seven temporary public-import files under `/tmp/nominal-f04c-execution/` check
all signatures and actual conclusions, including scope/action isolation, Bool,
pointwise functions, unordered-pair support, and two fresh choices fixing a
nested context. New-interface consumers were run before implementation and
then passed after their corresponding code. The full 972-job Package build,
both direct module checks, direct audit, import coverage and retained F03a/F04b
consumers pass. The audit traverses 178 production declarations in seven
defining modules with standard axioms only; source coverage reaches eight
production modules including the root and one audit.

The matching LaTeX was written and compiled in each mathematical task. The
reconciled article is 20 pages. These checks use cached dependencies and
incrementally rebuilt project modules; no fresh whole-project build,
dependency bootstrap or unchanged reference-library rebuild is claimed.
Independent review found no Critical/Important issues. Two minor findings were
resolved: stale article status in the tracker and a Finset isolation guard that
needed Pointwise and equality enabled. The strengthened consumer and document
checks pass. F04c is DONE; PKG-F04 remains open for F04d. The reviewer independently
reran code, consumers, audit, coverage and a fresh 20-page article build. No
production proof change or second review was required.

## Author-approved general freshness extension

`Fresh A x y` now means `Disjoint (support A x) (support A y)`, for independent
carrier universes and the two selected nominal actions over A. The elementwise
relation is `hx.FreshWith hy := Disjoint hx.support hy.support`; it needs no
carrier-wide nominality. The existing `hx.Fresh a` is derived using the
canonical atom certificate, and `fresh_iff_notMem_support` recovers its former
nonmembership characterization. The fully explicit `@Fresh` type intentionally
adds the second carrier, action and nominality arguments; ordinary atom calls
and their named theorem interfaces remain available.

The extension adds 33 declarations for symmetry, self-freshness, product
decomposition on both sides, simultaneous/inverse transport, disjoint sufficient
bounds, equivariant maps and canonical finite-set/discrete reasoning. Generic
statements require `Infinite A` through least support but no decidable equality;
Finset carriers retain their existing equality/Pointwise requirements. No new
action, container, notation, tactic or parallel support construction is added.
The existing atom laws are derived from the general relation. Equivariant-map
freshness preservation is one-way, since maps can erase support.

Three independent investigators checked further natural generalizations.
Root inspected and reran their four retained research probes; the
[research report](../../research/2026-10-06-foundation-generalizations.md)
separates the adopted freshness results from seven checked proposals for later
foundation work. The author made natural generality a standing preference in
AGENTS.md and research decision R15. This does not authorize implementing every
research proposal or starting F04d in this increment.

The eight temporary public-import consumers pass, including the new
GeneralFreshnessContracts and retained atom/action/boundary/avoidance consumers.
The Package build passes 972 jobs with cached dependencies; the direct audit
checks 226 declarations in seven defining modules with only standard axioms,
and import coverage remains eight production source modules plus one audit.
The updated article compiles to 21 pages. Source snapshots, logs and the adapted
fully explicit Fresh fixture are under `/tmp/nominal-general-freshness-9a13sgo9/`.
The original F04c scratch evidence is preserved. Independent review found no
Critical/Important issues and one minor stale article proof description. That
paragraph now identifies the general disjoint-support transport theorem and
Finset.disjoint_image; the article and document checks pass after correction.
The reviewer independently repeated the production, consumer, probe and audit
checks and a fresh 21-page manuscript build. This follow-up is complete, with
all work uncommitted and F04d still unimplemented.
