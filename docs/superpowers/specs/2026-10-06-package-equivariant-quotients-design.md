# F04d: canonical equivariant quotients

Date: 2026-10-06. **Written specification approved by the author.**
Task: **PKG-F04, slice F04d**, with concurrent article work under **PKG-11**.
The [active roadmap](../../nominal-package-roadmap.md) owns status and phase
boundaries. Native implementation followed by one fresh independent final review
is already selected. The author approved this specification on 2026-10-06,
including the stronger supported-fiber characterization and quotient corollary.
The [native implementation plan](../plans/2026-10-06-package-equivariant-quotients.md)
was subsequently approved for native execution. All 15 declarations and their
consumers now check; the final independent review passes with no findings. F04d
and the reconciled parent PKG-F04 are delivered, uncommitted. Earlier approvals
remain satisfied. Nothing here authorizes a commit,
push, publication, merge, branch switch, dependency change or CI work.

## Intended outcome

Equip an ordinary `Quotient s` with the action induced by an invariant setoid
on a selected source action. Make its projection usable through computation,
equivariance, surjectivity, preservation of sufficient finite supports and
individual finite supportedness, nominality transfer, least-support inclusion
and the delivered general freshness laws. Quotients can strictly decrease
support; neither a chosen representative nor an unrelated quotient action
receives an exact-support or canonical-projection promise.

The requested increment is bounded mathematically but follows the architectural
review path because it adds public action constructors and interfaces. The
author's first-session request directly authorizes writing this specification.
The design does not reopen the preceding architectural investigation.

Preserve `NominalPackage`, `Perm A`, independently selected actions and
independent universes. `Nominal A X` remains a proof-only certificate of its
action parameter. Bare functions retain pointwise action; bare permutations
retain left multiplication, with no blanket nominality for either. Finset
actions and certificates remain consumer-scoped by `Pointwise`. Classical
reasoning is allowed, without admissions, new axioms or disabled kernel checks.

The stronger representative-support characterization below is **approved and
implemented**. Its general parent requires only one supported preimage.
Implementation followed the separately approved native plan and passed the
required final independent review.

## Inspected checkout and evidence

The requested directory is on `fasapa/nominal-package`, at
`9c1cb9aa2f9f69d8d801a9864a9f0220b92ea62a` (`Freshness`). The initial working
tree was clean at design start. History places it immediately after the supplied
`68956dd23066c7c5c647345e5598b859ff97a10c`. F04c, its general-freshness
extension, the article, generalization research and instruction updates are
committed in the newer revision. Earlier uncommitted-delivery accounts are
historical; preserve them as such rather than treating them as current status.

Inputs inspected include AGENTS.md, both READMEs, Package.lean, all seven
foundation modules, the audit and import checker, dependency pins, the active
tracker, research guide/readiness/article-plan/generalization notes, all four
retained Generalization probes, the F04b/F04c specifications and native plans
including their final delivery and freshness amendments, and main.tex with
all included sections. Relevant F04a, research-brief and predicate-foundations
passages were consulted. The old roadmap/review supply historical boundaries,
not implementation requirements. The three-agent investigation was not repeated.

Lean/Mathlib are pinned to `v4.34.1`; the manifest and installed Mathlib both
identify `d13f23b723b8a846827a245b89c10fc7d3f11612`. The local Pitts source is
*Nominal Sets*, CUP 2013: Section 1.7, equation (1.43), pp. 23–24; Section 2.9,
Proposition 2.30, pp. 45–46. No current-upstream API or countability assumption
is substituted for these inputs.

Fresh checks in this design session, distinct from supplied delivery history:

- `lake build Package +Package.Tests.AxiomAudit` passed, 972 jobs, with cached
  project/dependency artifacts and replayed audit output.
- `lake env lean Package/Tests/AxiomAudit.lean` directly checked 226 production
  declarations in seven defining modules, allowing only `propext`,
  `Classical.choice` and `Quot.sound`.
- `python3 Package/Scripts/check-imports.py` reached eight production source
  modules including the root, and one audit. The checker is unchanged.
- An import/`#check`/`#print axioms` inventory in
  `/tmp/nominal-f04d-design-xxzz3gbk/PinnedAPI.lean` passed. It defines no F04d
  operation or theorem. An initial lookup of `MulAction.toSMul` was corrected
  to the actual inheritance through `MulAction.toSemigroupAction` and
  `SemigroupAction.toSMul`; both logs are retained.
- The documented article `latexmk` command succeeded with all outputs current.
  The existing log reports 21 pages and no warning or box diagnostic; this
  invocation did not rebuild the PDF.

The scratch directory also records fingerprints of 127 baseline source/document
files and the original active roadmap. These checks are baseline evidence, not
F04d proof validation, a fresh full-project build, a dependency bootstrap or a
reference-library rebuild. The retained research probes were inspected, not
rerun as a new generalization investigation.

## Construction choices and Mathlib reuse

**Approved choice: explicit constructors from an ordinary compatibility proof.**
Clients install the resulting action with `letI` or a deliberately scoped local
instance. Canonical theorems elaborate with that constructed action in their
types. No quotient action or nominality theorem is registered globally or in a
new scope in this increment.

| Approach | Tradeoff and disposition |
| --- | --- |
| Explicit general constructors, then nominal specialization | Approved choice. Gives arbitrary monoid actions a reusable construction and makes the chosen quotient action visible. A short `letI` is the deliberate setup cost. |
| Compatibility typeclass plus scoped quotient-action instance | Can reduce setup, but adds instance-search/scoping policy and another route to an action on an existing quotient type. Unnecessary for the present contract; not selected. |
| A constructor specialized to `Perm A` | Would satisfy the immediate nominal client, but restricts a construction whose laws use only a monoid action. Derive the nominal interface from the general construction instead. |

Use `Quotient s` itself. No tagged replacement carrier, new equivalence-relation
representation, representative selector, generic quotient framework or
alternative equivariant-map bundle is needed.

Pinned source paths below are relative to `.lake/packages/mathlib/Mathlib/`.

| Declaration/source | Exact use or mismatch |
| --- | --- |
| `Quotient.map`, `Quotient.map_mk`, `Data/Quot.lean:230–236` | Descend each scalar operation using relation preservation; computation at a class constructor is definitional. Source/target quotient universes are independent in the general API. |
| `Quotient.map'`, same file:700 | Equivalent explicit-`Setoid.r` adapter. Available, but the approved construction can use `map` with explicit setoid arguments directly. |
| `Quotient.mk_surjective`, same file:342 | Projection surjectivity without action, inhabitance, nominality or atom assumptions. Reuse it directly; add no renamed surjectivity theorem. |
| `Function.Surjective.mulAction`, `Algebra/Group/Action/Defs.lean:454` | Transfers monoid action laws once the target `SMul` and the commuting surjection equation are supplied. It does not construct the scalar operation. Use its reducible non-instance pattern. |
| `MulActionHom`, `GroupTheory/GroupAction/Hom.lean:84`; `.map_smul` | Existing bundle works with only `SMul`, independent scalar/carrier universes and ordinary application. Use it for the general projection homomorphism, without changing Package's `Equivariant`. |
| `MulAction.QuotientAction`, `GroupTheory/GroupAction/Quotient.lean:52–98` | Concerns subgroup cosets of a group and a subgroup-specific compatibility class. It does not solve arbitrary invariant setoids on arbitrary acted-on carriers. |
| `Con.instSMul`, `Con.mulAction`, `GroupTheory/Congruence/Basic.lean:280–310` | Requires multiplication on the carrier, multiplicative congruence and scalar-tower hypotheses. Those assumptions are unnecessary here. |
| `Quotient.inductionOn`, `.lift`, `.lift_mk`, `.sound`, `.exact`, `.eq` | Existing elimination, representative computation and relation/equality bridges. Use for laws and consumers; no chosen representative is needed. |
| `Setoid.ker` | Supplies the equality-of-first-components setoid in the strict-decrease consumer, and simple equality/non-invariant fixtures. |
| Package `supports_map`, `FinitelySupported.map`, `.support_map_subset`, `support_map_subset`, `support_eq` | All existing image contracts are reused. The new quotient theorems are specializations, not a new support calculus. |
| Package `fresh_map_left/right`, `FinitelySupported.freshWith_map_left/right` | Quotient freshness consumers apply these directly. No parallel quotient freshness API. |

The missing construction is a small adapter from an invariant arbitrary setoid
to Mathlib's map and action-law transfer. Nominality transfer additionally needs
the proof-only Package certificate; the checked research proof already supplies
the mathematical route.

## Exact approved public interfaces

All names below are in `NominalPackage`. Blocks are separate variable contexts
and specify signatures, omitting proof bodies. The universes are independent.
The `letI` in a result type is part of the contract: it fixes the particular
constructed action, rather than quantifying over an ambient quotient action.

### Relation compatibility and the scalar operation

```lean
universe u v

def SMulInvariant (M : Type u) {X : Type v} [SMul M X]
    (s : Setoid X) : Prop :=
  ∀ (m : M) ⦃x y : X⦄, s.r x y → s.r (m • x) (m • y)

variable {M : Type u} {X : Type v} [SMul M X]

abbrev QuotientAction.smul (s : Setoid X) (hs : SMulInvariant M s) :
    SMul M (Quotient s)

@[simp] theorem QuotientAction.smul_mk
    (s : Setoid X) (hs : SMulInvariant M s) (m : M) (x : X) :
    letI := QuotientAction.smul s hs
    m • Quotient.mk s x = Quotient.mk s (m • x)

theorem QuotientAction.mk_smul
    (s : Setoid X) (hs : SMulInvariant M s) (m : M) (x : X) :
    letI := QuotientAction.smul s hs
    Quotient.mk s (m • x) = m • Quotient.mk s x

def QuotientAction.mkHom (s : Setoid X) (hs : SMulInvariant M s) :
    letI := QuotientAction.smul s hs
    X →[M] Quotient s

@[simp] theorem QuotientAction.mkHom_apply
    (s : Setoid X) (hs : SMulInvariant M s) (x : X) :
    QuotientAction.mkHom s hs x = Quotient.mk s x
```

`SMulInvariant` is an ordinary proposition, **not a typeclass** and not a bundle
carrying a second action. The setoid is an explicit argument; there is no
ambient `[Setoid X]` requirement. The compatibility proof refers to the selected
source scalar operation. It needs neither a monoid nor inverse preservation.
For a group action, preservation in the other direction follows by applying the
same hypothesis to the inverse; no stronger input is imposed.

The scalar operation is `Quotient.map (m • ·) (hs m)`, with both setoid
arguments fixed to s. `mkHom` is the existing Mathlib bundle with underlying
function `Quotient.mk s`. The operation and bundle remain computable; no
classical choice is needed for them. The finite-support witnesses added later
remain inside proofs.

### Monoid action, and selection of the canonical action

```lean
universe u v
variable {M : Type u} {X : Type v} [Monoid M] [MulAction M X]

abbrev QuotientAction.mulAction (s : Setoid X) (hs : SMulInvariant M s) :
    MulAction M (Quotient s)
```

Install `QuotientAction.smul s hs` inside this constructor and apply
`Function.Surjective.mulAction` to `Quotient.mk s`, `Quotient.mk_surjective`
and the commuting equation. The resulting inherited scalar operation must be
definitionally the same as `QuotientAction.smul s hs`. Consequently the scalar
computation and `mkHom` laws above also apply to the constructed `MulAction`.
This is the only monoid/group action construction needed; do not add an action
hierarchy catalogue.

The ordinary client setup is:

```lean
letI : MulAction M (Quotient s) := QuotientAction.mulAction s hs
```

No `[MulAction M (Quotient s)]` is an input to the constructor. Neither import
nor compatibility evidence alone installs it. Different proofs of compatibility
for the same source action/setoid give the same construction by proof
irrelevance. A different selected source action is different input data.

Only `smul_mk` and `mkHom_apply` receive new simp attributes. The reverse
`mk_smul`, equivariance, compatibility and support statements are named laws,
not reverse simp rules or global unfolding instructions. No instance-priority,
reducibility-policy or linter change is permitted. Local reducible constructors
follow Mathlib's established non-instance convention.

### General nominality transfer

Add the following general parent to Nominal.lean outside its infinite-atom
section, using the checked investigation's proof:

```lean
universe u v w
variable {A : Type u} {X : Type v} {Y : Type w}
variable [MulAction (Perm A) X] [MulAction (Perm A) Y]

theorem Equivariant.nominal_of_surjective [Nominal A X] {f : X → Y}
    (hf : Equivariant A f) (hsurj : Function.Surjective f) : Nominal A Y
```

This is an explicit theorem, not an instance-search rule. For y, eliminate
surjectivity inside the proof, obtain a representative x and apply
`(Nominal.finitelySupported (A := A) x).map hf`. No representative is chosen
as data, and no `Nonempty X`, `Infinite A` or `DecidableEq A` is required.
The codomain action is an already selected input; the theorem neither creates
nor replaces it. Individual image preservation still uses `.map` directly and
does not gain whole-source nominality.

### Canonical nominal quotient interface

```lean
universe u v
variable (A : Type u) {X : Type v} [MulAction (Perm A) X]

theorem QuotientAction.equivariant_mk
    (s : Setoid X) (hs : SMulInvariant (Perm A) s) :
    letI := QuotientAction.mulAction s hs
    Equivariant A (Quotient.mk s)

theorem QuotientAction.supports_mk
    (s : Setoid X) (hs : SMulInvariant (Perm A) s)
    {S : Finset A} {x : X} (hS : Supports S x) :
    letI := QuotientAction.mulAction s hs
    Supports S (Quotient.mk s x)

theorem QuotientAction.finitelySupported_mk
    (s : Setoid X) (hs : SMulInvariant (Perm A) s)
    {x : X} (hx : FinitelySupported A x) :
    letI := QuotientAction.mulAction s hs
    FinitelySupported A (Quotient.mk s x)

theorem QuotientAction.nominal [Nominal A X]
    (s : Setoid X) (hs : SMulInvariant (Perm A) s) :
    letI := QuotientAction.mulAction s hs
    Nominal A (Quotient s)

theorem QuotientAction.support_mk_subset [Infinite A] [Nominal A X]
    (s : Setoid X) (hs : SMulInvariant (Perm A) s) (x : X) :
    letI := QuotientAction.mulAction s hs
    letI := QuotientAction.nominal A s hs
    support A (Quotient.mk s x) ⊆ support A x
```

The first theorem is the specialization of the general projection equation
(or `mkHom.map_smul`) to `Perm A`, preserving the existing orientation of
`Equivariant`. The next two apply `supports_map` and `.map`. Nominality applies
the new general surjection theorem and the existing projection surjectivity.
The carrier inclusion is the delivered `support_map_subset` under those two
locally installed certificates. Nominality itself needs no infinite atoms.

The elementwise least-support interface deliberately reuses the existing
general law. With only `[Infinite A]` and `hx : FinitelySupported A x`, after
installing the canonical action, let `hq := QuotientAction.equivariant_mk A s hs`.
Then `hx.support_map_subset hq` proves exactly

```lean
(hx.map hq).support ⊆ hx.support
```

It requires neither carrier nominal. The separately supplied certificate
`QuotientAction.finitelySupported_mk A s hs hx` gives the same support by
`.support_eq`. A mixed client can compare the result with `support A` on
whichever carrier is nominal using the delivered `support_eq`. Add no duplicate
elementwise selector or image-inclusion theorem merely to rename this call.

Projection surjectivity is available as
`Quotient.mk_surjective (s := s) : Function.Surjective (Quotient.mk s)`,
independently of any action. The action-dependent projection/nominality laws
above explicitly fix the constructed action. Applying them with an unrelated
locally selected quotient action must fail unless the client separately proves
the required identification of actions or the appropriate equivariance law.

## Approved stronger representative-support characterization

Pitts' Proposition 2.30 identifies a quotient class's support with the
intersection of all its representatives' supports. This fits as a small
additional result: its proof uses existing image inclusion, support transport
and a single fresh swap. It needs no new support or predicate infrastructure.
The author approved its inclusion through the following more general parent.

```lean
universe u v w
variable {A : Type u} {X : Type v} {Y : Type w}
variable [MulAction (Perm A) X] [MulAction (Perm A) Y] [Infinite A]
variable {x : X} {f : X → Y}

theorem FinitelySupported.mem_support_map_iff
    (hx : FinitelySupported A x) (hf : Equivariant A f) (a : A) :
    a ∈ (hx.map hf).support ↔
      ∀ (z : X) (hz : FinitelySupported A z), f z = f x → a ∈ hz.support
```

There is no source/codomain nominality, surjectivity, inhabitance, countability
or public decidable-equality assumption. The chosen x supplies one supported
preimage, so the family on the right is nonempty. Unsupported representatives
are not assigned artificial least supports and need not become supported.

For the forward direction, every supported z with `f z = f x` maps its least
support to a sufficient bound for `f x`; apply image minimality. Conversely,
suppose a is outside the image support. Choose b outside `insert a hx.support`;
image inclusion also puts b outside the image support. The swap `(a b)` fixes
`f x`. Equivariance makes `z := (a b) • x` another preimage of `f x`, supported
by `hx.smul (Perm.swap a b)`. Support transport and b's nonmembership imply
that a is absent from z's least support, contradicting the universal condition.
Classical equality and the Finset image scope stay inside the proof. This uses
only existing outside-swap fixation and transport; it repeats neither proof.

Specialize the parent to q for the elementwise quotient characterization:

```text
a ∈ (hx.map hq).support ↔
  ∀ z (hz : FinitelySupported A z), s.r z x → a ∈ hz.support
```

This is a required public-import consumer of the parent using `Quotient.eq`,
not an additional differently named production theorem. For nominal source
carriers, provide the convenient class-level intersection formula, for an
arbitrary class c rather than a selected representative:

```lean
universe u v
variable (A : Type u) {X : Type v} [MulAction (Perm A) X]
variable [Infinite A] [Nominal A X]

theorem QuotientAction.support_eq_iInter
    (s : Setoid X) (hs : SMulInvariant (Perm A) s) (c : Quotient s) :
    letI := QuotientAction.mulAction s hs
    letI := QuotientAction.nominal A s hs
    (support A c : Set A) =
      ⋂ x : {x : X // Quotient.mk s x = c}, (support A x.val : Set A)
```

Use quotient induction on c, the general membership theorem, `support_eq`,
class nominality and set extensionality. The intersection is a `Set A`, not
an unavailable infinitary Finset operation. This proves the advertised exact
formula; it is not an assumption of closure under arbitrary intersections of
supporting bounds. The right side consists of supports of different elements.

Do **not** claim existence of a representative whose support equals the class
support. In the universal quotient of canonical atoms, the class has empty
support but every representative has singleton support. Also do not infer
finite supportedness or nominality backwards through a surjection. A universal
quotient of the non-nominal pointwise function carrier supplies a separate
boundary consumer: its image is invariant even for the unsupported identity.

This characterization is about supports of objects in a fiber. Predicate
pullback/support reflection quantifies over predicates and uses a different
surjective-map theorem. That interface, its descent hypotheses and exact
predicate-support equations remain F05/PKG-01.

## Freshness consumers and exactness example

After installing the canonical action, use `hq` with
`fresh_map_left/right` to preserve `Fresh A c x` and `Fresh A x c` when the
quotiented value is x. Use `hx.freshWith_map_left hc hq` and
`hc.freshWith_map_right hx hq` for the corresponding individual certificates.
Only the carrier notation needs nominality of its two values' carriers;
the elementwise route needs no nominality instance on any entire carrier.
Both use `[Infinite A]` through the delivered freshness definition, with no
additional equality assumption. Do not add quotient-specific freshness laws.

The main strictness consumer uses `X := A × A` and
`s := Setoid.ker (Prod.fst : A × A → A)`. It relates pairs exactly when their
first components agree, so it is invariant under the selected product action.
For distinct a,b over infinite A, prove actual equalities and strict inclusion:

```text
support A (q (a,b)) = {a}
support A (a,b) = {a,b}
support A (q (a,b)) ⊂ support A (a,b)
```

For the upper equality bound, `q (a,b) = q (a,a)` and the delivered
atom/product formulas give support at most `{a}`. For the reverse bound,
`Quotient.lift Prod.fst` is well defined and equivariant by quotient induction;
apply the delivered image inclusion to recover `{a}` from the class. Thus the
quotient retains a nonempty dependency and loses b. This proof does not depend
on the intersection formula, an injectivity generalization or a
chosen representative function. The same example proves b fresh for the
class but not for `(a,b)`, illustrating failure of freshness reflection.

## Assumptions, modules and research dispositions

| Contract | Sufficient assumptions beyond independent carriers |
| --- | --- |
| Compatibility predicate, quotient scalar operation, computation and `mkHom` | Selected `SMul M X` and explicit relation preservation |
| Quotient `MulAction` | `Monoid M`, selected `MulAction M X`, same relation preservation |
| Projection surjectivity | `Setoid X` only |
| Projection equivariance and preservation of finite bounds/evidence | Selected `MulAction (Perm A) X`, invariant setoid; bound/evidence for the individual source value where used |
| General surjective nominality transfer | Two selected actions, source nominality, ordinary equivariance and surjectivity |
| Canonical quotient nominality | Source nominality and invariant setoid; no infinitude or equality |
| Elementwise least-support inclusion and fiber characterization | `Infinite A`, one supported source element, equivariance |
| Carrier inclusion and quotient intersection | `Infinite A`, source nominality, invariant setoid; quotient nominality is derived |
| General quotient freshness consumers | `Infinite A` and the relevant individual certificates, or nominality for carrier notation |

None of these contracts requires `Nonempty X`, a decidable relation,
`DecidableEq A`, countability or equality of atom/carrier universes. Particular
consumer operations, such as an explicit swap or acted-on Finset, retain their
existing local equality/scope requirements.

Add two focused production modules:

```text
Package.Foundations.QuotientAction
  imports Mathlib.Algebra.Group.Action.Defs
          Mathlib.Data.Quot
          Mathlib.GroupTheory.GroupAction.Hom

Package.Foundations.Quotient
  imports Package.Foundations.QuotientAction
          Package.Foundations.Nominal
```

The first owns compatibility, scalar/monoid constructors and general projection
laws. It has no dependency on `Perm`, nominality or freshness. The second owns
the nominal projection/support/nominality specializations and exact
intersection formula. Add the general surjection theorem and general
membership theorem to Nominal.lean at their respective assumption levels.
Those are additive changes; preserve existing declarations and proofs. There
is no backward import from Nominal into quotients or from quotients into
freshness. Freshness and canonical exact-formula consumers use the public root.

Explicitly export both new modules from Package.lean, extend representative
axiom prints, and update Package/README.md with construction calls and action
selection. The existing checker/audit policies cover both new foundation
modules unchanged. Expected source coverage is ten production modules including
the root and one audit, with nine defining modules; measure declaration counts.
No Lake, dependency, shared validation script or reference-source edit is
expected. Preserve historical docs/roadmap.md.

Disposition of the seven checked research proposals:

| Proposal | F04d disposition |
| --- | --- |
| Injective reflection and injection/surjection nominality transfer | Adopt only the surjection nominality theorem required here; injection/reflection APIs remain research. Strictness uses an ordinary equivariant lift, not new injection theory. |
| General group/set support transport and equality-free Finset transport | Reuse delivered transport with proof-local classical equality; broader transport APIs remain research. |
| `SMul`-only equivariance and Mathlib hom bridge | Use existing `MulActionHom` for the scalar-level projection. Preserve Package's existing Equivariant definition/combinators; their general rewrite remains research. |
| Algebraic generation of pointwise fixers | Remains research; no new factorization theorem is needed. |
| Spare-atom generalization of support intersection | Remains research; no intersection proof is reconstructed. |
| Atom-equivalence transport | Remains research; no representation or atom-sort change. |
| Directedness-based least-support extraction | Remains research; preserve the delivered Infinite-based least-support API. |

The approved fiber characterization is a separately stated F04d addition,
supported by Pitts' proof route; it is not falsely counted among the already
kernel-checked generalization probes. Full predicate descent/reflection,
SupportsMap/SupportsPred, predicate bundles, Some/Any, supported-function objects,
abstraction, FCB, recursion, generators and other container catalogues remain
outside this increment.

## Concurrent article work

Create `docs/article/sections/quotients.tex`, with
`sec:equivariant-quotients`, and include it after freshness.tex and before
perspectives.tex. Draft the mathematics alongside Lean, then reconcile the
actual hypotheses, declarations, action arguments and proof routes. Cover:

1. An invariant equivalence relation on a monoid action, its induced scalar
   operation and why representative independence gives a well-defined action.
   Attribute quotient mapping and law transfer to the existing Lean/Mathlib
   infrastructure; relate the group case to Pitts Section 1.7.
2. Projection computation, surjectivity and equivariance, with the selected
   canonical action explicit. Explain the explicit-constructor choice and why
   a different action on the same carrier need not make the projection equivariant.
3. Preservation of every sufficient finite support and of individual supportedness;
   the general surjective nominality argument and its quotient specialization.
   Separate these assumption-free atom results from infinite-atom least support.
4. Least-support inclusion, the first-component quotient's exact singleton
   support and strict decrease, with both inclusions explained.
5. The general supported-fiber characterization, its fresh-swap proof
   and the quotient intersection formula, citing Pitts Proposition 2.30.
   Explain the lack of an exact-support representative and the universal-atom
   quotient counterexample. No countability requirement enters the proof.
6. General freshness preservation by existing image laws, including supported
   contexts in non-nominal carriers, and the distinction from predicate
   pullback/support reflection. Refer to the existing Bool and unordered-pair
   boundaries without reproving or weakening them.

Update abstract/introduction and focused cross-references in support.tex,
freshness.tex and perspectives.tex where useful. Mathematical concepts precede
their Lean encoding; avoid a complete API catalogue. Follow the
[publication-content policy](../../research/2026-10-05-article-plan.md#publication-content-policy):
task IDs, approval/delivery histories, commands, audit counts, cache conditions
and review verdicts belong to the tracker/notes, not the manuscript.

## Acceptance and completion

Temporary consumers import **only `Package`**, use independent universes and
consume actual conclusions. Store their source/logs outside the repository;
add no standalone Package/Examples layer. The implementation plan assigns
these obligations to native tasks, with consumer failures observed before new
interfaces and meaningful passing proofs afterwards.

| Obligation | Required conclusion or discriminating check |
| --- | --- |
| Exact signatures | Assign every new public declaration its approved type without surrounding classical instances hiding extra hypotheses; inspect action arguments and independent universes. |
| Generality of construction | Use arbitrary `SMul M X` for scalar computation, arbitrary monoid actions for laws, and a concrete non-group monoid. No Group, nominality, relation decidability, equality or inhabitance may leak into construction. |
| Well-definedness and laws | From `s.r x y`, derive equality of acted-on classes. Consume `one_smul`, `mul_smul`, `smul_mk`, `mk_smul` and `mkHom.map_smul` under the actual constructor, not a manually defined test action. Check inherited SMul coherence. |
| Finite atoms and empty carriers | Instantiate canonical Bool quotients and a quotient of `Discrete A PEmpty` with independent universes. Prove nominality and eliminate projection preimages without any infinitude or `Nonempty X`. |
| Projection | Derive a representative existential using `Quotient.mk_surjective` and use it in a quotient conclusion; consume ordinary equivariance and representative computation. No `Quotient.out`. |
| Sufficient bounds and evidence | For arbitrary S supporting x, prove fixation of `q x` by a permutation fixing S. Preserve individual supportedness and consume its least support without assuming either whole carrier nominal. Test independent image certificates via support agreement. |
| General surjective transfer | Install the returned nominality certificate on an already selected Y action, then consume its projection. Include finite atoms, empty carriers and independent A/X/Y universes. |
| Least-support inclusion | Consume both the general elementwise route and quotient carrier theorem as membership implications. Retain a source that has supported elements but is not nominal, using pointwise constant functions and the existing unsupported identity boundary. |
| Strict decrease | Prove the three exact first-component quotient conclusions above, retaining a in the image support and dropping b. Derive failure of representative support equality and freshness reflection. |
| Supported-fiber characterization | Consume both directions of the general theorem, specialize it to a supported quotient representative with no whole-carrier nominality, and consume the exact intersection equality at an arbitrary quotient class. Check the universal-atom quotient where no representative attains class support. |
| No reverse supportedness | For the universal quotient of `Nat → Nat` under pointwise action, prove its class invariant/finitely supported while the identity representative has no finite support. This is an actual mathematical counterexample, not a failed instance search. |
| General freshness | Use map laws on either side with a nested supported context, deriving component freshness or a fresh-swap consequence. Include individual certificates for values in non-nominal carriers and a Finset context under its existing scope. |
| Incompatible relation | Use the kernel of `fun n : Nat => if n = 1 then 0 else n`. Prove 0 related to 1 but their images under swapping 1 and 2 unrelated; refute `SMulInvariant`. A missing compatibility instance is not sufficient evidence. |
| Unrelated quotient action | With source nominality and the valid hs in scope, keep the canonical construction and its nominality evidence available, then select an abstract different quotient action. Guard failed applications of the canonical equivariance/certificate theorems to that explicit action. Also take the equality setoid on infinite atoms and the trivial quotient action; prove the projection computation/equivariance contract actually fails on a moving swap. |
| Active candidate in coherence negatives | Install the canonical nominality proof explicitly as a local instance for its precise action before guarding synthesis for the unrelated action. Positive neighboring checks use the same s, hs and source evidence with the canonical action. Do not claim the unrelated action itself non-nominal merely because a canonical certificate cannot apply. |
| Existing policies | Retain atom/product/discrete/Finset action equations, bare-function pointwise and bare-permutation left multiplication, no blanket function/permutation nominality, and Pointwise availability before/inside/after a local scope. Reuse the checked Bool and unordered-pair conclusions. |

Compile affected modules while iterating, then supported dependents. Extend
representative `#print axioms` for the constructors, general surjection transfer,
projection, sufficient bounds, nominality, carrier inclusion and the
characterization. Preserve the complete module-origin audit including private
and generated declarations, zero-coverage rejection and standard-axiom allowlist.
Every new production module must be reached from both the public root and audit.

Run after the final production changes, besides direct module/consumer checks:

```sh
lake build Package +Package.Tests.AxiomAudit
lake env lean Package/Tests/AxiomAudit.lean
python3 Package/Scripts/check-imports.py
git diff --check
```

Rerun checker self-tests if the checker changes. From docs/article/, run:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error \
  -outdir=/tmp/nominal-package-article-build main.tex
```

Keep generated artifacts outside the source tree. Check manuscript mathematics
separately from successful compilation and resolve new diagnostics. Record
commands actually run and whether project/dependency artifacts were cached,
rebuilt or bootstrapped. Check preservation against the initial and subsequent
working-tree state, including untracked files, and check document links/fences/
whitespace. If shared integration affects reference targets, validate them
separately; otherwise report source preservation without claiming a rebuild.

After native implementation and integrated validation, obtain the requested
**one fresh independent final review** of statements, proof assumptions, action
coherence, consumers, exactness, article correspondence and preservation.
Resolve findings and rerun affected checks. F04d is complete only after code,
consumers, audit, article and final review pass. Then reconcile every overall
PKG-F04 criterion, checking the actual recorded evidence for fixed parameters,
nested contexts and least versus strong support against the current interfaces.
Here the quotient-descent criterion concerns the induced action and ordinary
relation-respecting quotient elimination, as exercised by the first-component
lift; full predicate descent/support reflection remains later work. Do not
assume a completed slice automatically discharges an unchecked parent criterion.
Mark the parent complete only if all criteria are met; neither F05 nor PKG-01
becomes delivered by this work.

## Design-stage handoff

- [x] Verify checkout and delivered interfaces; inspect exact pinned APIs.
- [x] Compare construction policies and delimit the general parents needed.
- [x] Write exact contracts, proof routes, module/article work and acceptance checks.
- [x] Complete specification self-review and document/preservation checks.
- [x] Obtain agreement on this written specification, including the stronger
  characterization and its quotient corollary.
- [x] Prepare the native implementation plan after specification approval.
- [x] Obtain written-plan approval before production changes.

At the design handoff, only the delivered baseline and existing API inventory
had been checked. The subsequently approved native execution now checks all
15 declarations and their consumers. The selected execution method and all
earlier approvals stand.

Self-review checked action-indexed result types, hypothesis separation,
computability of the constructors, proof-only evidence, strictness and
nonattainment, the general fiber proof, independent universes, research
dispositions and acceptance/article coverage. No unspecified mathematical
contract is left inside the approved specification. The stronger characterization
was included in the author's written-specification approval.

Document checks passed for 70 local links and six anchors, balanced fences and
changed/new-file whitespace. `git diff --check` passed. Fingerprint comparison
preserves 126 of 127 baseline files, with only the intended active-roadmap edit
and this added specification. Its previous work log is preserved verbatim.
Production/article sources, dependency pins, historical roadmap, branch and
HEAD are unchanged. No independent implementation review is claimed.

The native plan assigns the unchanged 15-declaration contract to three
mathematical tasks and one integrated validation/documentation/review task.
Each mathematical task develops Lean and LaTeX together. Seven temporary
public-import consumers cover generic and nominal actions, elementwise bounds,
supported fibers, strictness/nonattainment, general freshness and active-candidate
coherence. Overall F04 reconciliation and the single independent final review
are explicit final obligations. Specification approval and the selected native
method remain satisfied, and the author subsequently approved the written plan.

Planning validation confirms all eight Lean blocks above are unchanged from
the approved artifact, and the plan copies the six declaration blocks exactly.
Document checks pass for 77 local links, six anchors, fences and whitespace.
The planning snapshot comparison preserves 126 of 128 existing files, changing
only specification status and the active tracker, alongside the added plan.
The previous work log and all Lean/article sources are unchanged. No Lean build,
audit or article compilation was rerun during this documentation-only stage.

## Native execution evidence

QuotientAction.lean and Quotient.lean implement the canonical construction and
nominal specialization; Nominal.lean adds only the two approved general parent
theorems. The 15 signatures match the specification under fully explicit
assignments with independent universes and no hidden equality/nominality
assumptions. No production contract changed during execution.

Consumer-first checks recorded missing-interface failures, then passing proofs.
All seven main temporary consumers pass, covering raw/monoid actions, finite
atoms, empty carriers, support bounds and individual evidence, general freshness,
active-candidate action isolation, strict decrease, supported fibers and the
two distinct representative boundaries. The strictness/nonattainment fixtures
were independently checked before adding the stronger characterization.
Minor consumer corrections concerned local instance binding, exact guard
diagnostics, visible Finset-pair equality and available tactics; they changed
no mathematical conclusion or production hypothesis.

The integrated build passes 974 jobs with cached dependencies and incrementally
rebuilt project artifacts. Direct checks of the three affected modules and
all consumers pass. The direct audit checks 245 declarations in nine defining
modules with only the permitted axioms; coverage reaches ten production sources
including Package and one audit. The two retained general-freshness/avoidance
consumers pass against the new public root. The article was developed and
compiled with each task; its reconciled output is 26 pages with a clean log.
These checks are not a fresh full-project build, dependency bootstrap or
reference-library rebuild. Evidence is under `/tmp/nominal-f04d-execution/`.

The active roadmap contains the reconciled overall F04 evidence map. The fresh
independent review found no Critical, Important or Minor issues; no production
fix or further review was needed. Its fresh temporary Package olean build
excluded cached project oleans while reusing pinned dependencies, then checked
all seven consumers, both retained context consumers and the full audit. A fresh
article build also passes with 26 pages and a clean log. The report is retained
at `/tmp/nominal-f04d-final-review-3fVxOr/report.md`.

Document checks cover eight Markdown files, 182 links, 13 anchors, 59 LaTeX
labels and all changed/new whitespace. Preservation leaves 116 of 129 original
files unchanged, with 13 intended edits and three additions; old Nominal source
is only extended. The historical work log, reference code, pins, historical
roadmap, branch and HEAD are preserved. F04d and the fully reconciled PKG-F04
are DONE; F05 and PKG-01 remain undelivered. All work remains uncommitted.
