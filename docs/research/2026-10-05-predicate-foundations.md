# Predicate foundations for the nominal package

**2026-10-07 continuation:** the [post-F05 investigation](2026-10-07-pkg01-predicate-foundations.md)
and [written PKG-01 specification](../superpowers/specs/2026-10-07-package-predicate-foundations-design.md)
reassess storage against committed supported maps and pinned Mathlib. Their
new probes use delivered Package foundations. The evidence and representation
recommendations below retain their original historical scope; they do not
override the new comparison or approve production implementation.

Date: 2026-10-05. Historical research baseline: `fasapa/nominal-package`, commit
`4279ba92efacd77b3b96e507631502272b489999`, with the pre-existing working tree
preserved. This note develops R6/R9 of the [research brief](2026-10-05-nominal-package-brief.md)
and extends the [initial investigation](2026-10-05-propositions-and-induction.md).
It is research evidence and an architectural recommendation, not an implemented
package. The original investigation changed no library source, dependency or
branch. This documentation revision starts from
`7fed53a2e5fc67379f86f085515e310e7c1fddb7` and applies the current
[architectural freedom policy](README.md#architectural-freedom); it does not
rerun or rebaseline the experiments below.

**Subsequent F01 session at `76966b1`:** see the
[readiness and proposed contracts](2026-10-05-pkg01-readiness.md) and
[new design-probe record](2026-10-05-predicate-design-probes.md). All four existing
predicate probes were rerun unchanged, including the two previously untracked
files. A new Mathlib-only direct-predicate experiment checks action/support
transport and surjective-equivariant pullback with independent universes.
The direct SPred API remains proposed. The author approved the first F02 + F03a
specification and its native implementation plan. F02/F03a were subsequently
implemented and checked; this note's predicate probes still do not certify the
proposed new support/predicate interface or complete PKG-01.

All new implementation, including any replacement foundations, belongs under
top-level `Package/`. The existing `Nominal/`, `Instances/` and probes remain
reference material and evidence. Actions, support, supported functions,
predicates, abstraction, quotients and induction may each be reused, adapted or
implemented afresh on their merits. No inherited API, typeclass, module layout,
universe restriction, seal boundary, representation or compatibility interface
is required. This freedom does not weaken the mathematical contracts or require
a rewrite: PKG-01 stays bounded, with its selected foundational dependencies
named explicitly and broader work tracked separately.
The [package roadmap](../nominal-package-roadmap.md) places PKG-F01–PKG-F05
before it: contract selection, `Package/` build/audit coverage, atom/action
foundations, support/freshness, and the minimal function/predicate-input
foundations required by the chosen representation. These are explicit
prerequisites, not a mandate to reproduce every reference-core feature.

The evidence supports three complementary layers: ordinary `Prop` judgments and
arbitrary-predicate fresh induction for users; a supported-predicate calculus for
logical operations, parameters and Some/Any; alpha-compatible raw predicates at
the quotient construction boundary. None requires a separate formula language
for the package's metatheory. An object language of first-order formulas is a
different, appropriate case study.

## Evidence and versions

“Checked” below means a successful local Lean invocation. “Source-verified” means
the cited statement or implementation was inspected, without rebuilding its
external development. “Analysis” identifies deductions or proposals that are not
new integrated theorems.

| Source | Exact evidence |
| --- | --- |
| Reference Lean library | Historical baseline above; Lean `v4.34.1`, Mathlib `v4.34.1`; affected sources inspected directly |
| Lean foundations | Installed `leanprover--lean4---v4.34.1/src/lean/Init/Core.lean`, especially `Quotient.rec`, `recOn`, `recOnSubsingleton`, `hrecOn`, lines 2031–2106; corroborated by the [official quotient reference](https://lean-lang.org/doc/reference/latest/The-Type-System/Quotients/) |
| Pitts | Andrew M. Pitts, *Nominal Sets: Names and Symmetry in Computer Science*, Cambridge University Press, 2013; complete local [PDF](../../ref/nominalsets.pdf), SHA-256 `546104434ce6388d2aed248428cc8bde653bf98780cee55265f686e7290f0794` |
| Copello et al. 2016 | Published version, ENTCS **323**, 109–124, DOI `10.1016/j.entcs.2016.06.008`; [author-institution repository PDF](https://publications.lib.chalmers.se/records/fulltext/247760/local_247760.pdf), retrieved successfully |
| Copello, Szasz, Tasistro 2018 | *Formalisation in Constructive Type Theory of Barendregt's Variable Convention for Generic Structures with Binders*, EPTCS **274**, 11–26, DOI `10.4204/EPTCS.274.2`; [arXiv:1807.01870v1](https://arxiv.org/pdf/1807.01870v1), 5 July 2018 |
| Rocq | Local read-only repository `/tmp/nominal-rocq-audit`, HEAD `78f41a6c7ca1b55814b7b7c7d734ad4decaac523`; compared with article artifact `fc7b95a47539fa2dc39f41f293c7d943a0d8b22d` (`lsfa2025`) |

All web access was on 2026-10-05. The first KCL-hosted 2016 PDF URL returned
403, but the Chalmers copy supplied the full published text. Thus the initial
note's inability to inspect the 2016 paper is now resolved. The complete local
Pitts PDF was text-extracted, with contents/index and the relevant full sections
consulted; this is not a claim that every theorem in the book was audited.
Page numbers below are printed book/article pages, not PDF viewer offsets.

## The objects that must remain distinct

| Object | Role | Relevant contract |
| --- | --- | --- |
| `p : Prop` | A truth value in Lean's metatheory | A discrete action fixes `p`; this says nothing about the support of a function returning `p` |
| `P : X → Prop` | A semantic predicate | Conjugation acts on its argument: `(π • P)(x) = P(π⁻¹ • x)` under discrete truth values |
| A subset `S : Set X` | Extension of a semantic predicate | Lean represents it by `X → Prop`; the intended set action is direct image, equivalent to inverse precomposition |
| `φ : Formula` | Syntax of an object-language formula | Its atoms, binders, alpha equivalence and support belong to the declared language |
| `e : Lean.Expr` | A metaprogram's representation of elaborated Lean code | Inspection can guide proof generation; it is not a support certificate |
| `h : P x` | A proof term | Lean proof irrelevance and elimination rules apply; the proof need not be represented as nominal formula syntax |
| `C : Term → Type v` | A data-valued dependent family | Quotient-indexed transport and compatibility of outputs must be addressed separately |

For example `fun x => x = a` is a supported predicate with a fixed parameter
`a`; joint permutation of `a` and `x` preserves equality, but fixing `a` does not
give equivariance in `x`. Its evaluated proposition has trivial action under the
chosen truth-value instance. Confusing these two actions loses the parameter.

Alpha compatibility is yet another condition: a raw predicate assigns equivalent
propositions to alpha-equivalent representatives. It does not say how the
predicate behaves when free atoms are permuted. Finite support restricts that
latter behavior outside a finite set; equivariance requires invariance under all
permutations. An arbitrary induction motive need satisfy neither.

## What Pitts provides

The book supplies both a semantic predicate theory and ordinary strong-induction
reasoning. It does not force them into a single public representation.

| Location | Precise content | Consequence for this package |
| --- | --- | --- |
| §1.5, Proposition 1.9, p.21; Notes 1.10–1.11, p.22 | Logical operations are equivariant; parameters must all be permuted; Hilbert choice is excluded from the unrestricted equivariance principle | Registered logical constructors and captured parameters can drive proof-producing automation; arbitrary choice cannot be accepted automatically |
| Proposition 2.9, pp.31–32 | Supported subsets of atoms are exactly finite or cofinite subsets | Provides the missing bridge from a supported atom predicate to the current Boolean laws for `И` |
| §2.5, Theorem 2.23, p.38 | `Nom` is a Boolean topos; discrete two-valued truth classifies equivariant subobjects | A supported predicate is richer than a global equivariant subobject: parameters can give nonempty support |
| Lemma 2.24 and Proposition 2.25, p.39 | Set support is permutation stability; taking a section of a relation is supported by the relation and fixed argument | The relevant fixed-parameter support bound is a union, not automatic empty support |
| Definition 2.26, pp.39–40 | The nominal powerset `Pfs X` contains the supported elements of the full powerset | All subsets form a permutation set; only supported subsets form this nominal carrier |
| §2.5, p.40 | Intersection, complement, supported-family intersection, equivariant pullback and comprehension; the Finite Support Principle | Quantification over functions/subsets in the internal nominal interpretation ranges over supported ones |
| §3.2, Lemma 3.7, Definition 3.8, Theorem 3.9, p.52 | Cofinite quantification is defined for any property; Some/Any applies to supported properties via an equivariant relation and nominal context | Separate the general cofinite operator from its nominal elimination rules |
| Proposition 3.10, p.53 | Fresh quantification respects Boolean operations under the supported-predicate assumptions | Self-duality and full disjunction laws cannot be extended to arbitrary predicates |
| §7.3, Theorem 7.3, p.116 | Support of a set of rules transfers to its inductively generated subset | Relation equivariance has its own generation proof; it is not a consequence of term induction |
| Examples 7.8–7.9, pp.119–122; Remark 7.10, p.122 | Renaming derivations supports BVC reasoning; ordinary higher-order logic can express strong rule induction | A separate nominal formula logic is optional, not a prerequisite |
| §7.5, Proposition 7.14, Lemma 7.15, p.125 | Supported monotone maps on an equivariant complete lattice have supported least fixed points; rule operators supply examples | External powerset constructions can be used before proving nominal closure |
| Remark 7.16, pp.125–126 | Internal `Pfs` fixed points require supported rule/hypothesis families; the external theorem is more general and identifies the two closures when applicable | Do not install an ordinary unrestricted `CompleteLattice` interface on `Pfs X` |
| §8.6, Theorem 8.21, pp.148–149; Corollary 8.22, p.150 | Alpha-structural induction for supported predicate families on nominal algebraic datatypes | This is a useful generic theorem, not evidence that arbitrary-motive induction is invalid |
| Example 11.1, pp.220–221 | `Pfs X` has meets and joins of supported families | Closure under each finite operation does not imply closure under arbitrary external indexed families |
| §12.3, pp.253–255 | A separate nominal logic-programming formulation uses formula syntax and freshness environments | This is a different layer from the present goal of Lean `Prop` judgments |

In Theorem 8.21, predicate lifting follows the signature's name, data, unit,
product and abstraction sorts. The abstraction clause in equation (8.50) uses
representatives `[a]d` with `a # P` and the body predicate. Its proof strengthens
over all permutations. The current Lean strong-induction proof also strengthens
over permutations, but avoids a support premise on the user's motive by making
the selected context and recursive hypotheses explicit. These interfaces share
a proof idea without having identical hypotheses.

An external-completeness counterexample is already visible at the atom powerset:
take an infinite, coinfinite set `A` of atoms, and the external family of
supported singletons `{ {a} | a ∈ A }`. Its union is `A`, which is unsupported.
The family itself is not asserted to be supported. This does not contradict
Example 11.1. The probe below checks the general obstruction for infinite,
coinfinite atom predicates, without assuming atom countability.

There is also no automatic commutation of `И` with arbitrary quantifiers.
For `R(a,x) := a = x`, `И a, ∃ x, R(a,x)` holds, while
`∃ x, И a, R(a,x)` fails. The relation is equivariant. With inequality, the
corresponding reversed universal-quantifier interchange fails. These simple
semantic counterexamples explain the directional current APIs; support is not
a license to reorder every quantifier.

## Copello and the Rocq precursor

**Source-verified, 2016.** Section 3, p.114 defines alpha compatibility of
`P : Λ → Set ℓ` by transport of inhabitants along alpha equivalence. The same
page gives `TermαPrimInd`, with variable/application cases and a lambda case
avoiding a finite list. It requires no predicate support premise. Its proof
strengthens induction over permutations. Pages 115–116 distinguish iteration
and recursion, using canonical fresh representatives. Because Agda `Set ℓ`
is data-valued, compatibility here is transfer maps between fibers, rather than
Lean propositional equivalence. This is a meaningful additional distinction
when comparing elimination interfaces.
[Copello et al., §3](https://publications.lib.chalmers.se/records/fulltext/247760/local_247760.pdf).

**Source-verified, 2018.** Section 4.2, Figure 16, p.22 gives `alphaPrimInd` for
`P : μ F → Set`, an avoidance list, and alpha compatibility. Its recursive
predicate lifting also records that avoided names do not occur bound in the
chosen subterm. Section 5, Figure 17, p.23 states a separate BVC proof principle
using representatives whose bound names avoid both the context and their own
free names. These are complementary constructions; neither states finite
support of every motive. Section 2.1, p.15 explicitly limits that universe to
one top-level recursive fixed point, excluding mutual recursive datatypes.
Thus it is useful evidence for a generic design, but not a ready-made theorem
covering every proposed multicategory signature.
[Copello, Szasz, Tasistro, v1](https://arxiv.org/pdf/1807.01870v1).

**Source-verified, Rocq.** At the pinned main revision,
[`theories/Example/Lambda.v:344–400`](https://github.com/fasapa/nominal/blob/78f41a6c7ca1b55814b7b7c7d734ad4decaac523/theories/Example/Lambda.v#L344)
labels its induction section “COPELLO's”. `αCompat` is
`∀ m n, m ≡ n → P m → P n`, with `P : Λ → Prop`.
`alpha_ind` takes an arbitrary finite `NameSet L`, alpha compatibility, and a
lambda step requiring `a ∉ L`. It never identifies `L` with the support of `P`.
`perm_ind` and `lam_rename` supply the strengthened-renaming proof.

The supported-function record stores a computational support set and a `Proper`
certificate, and its equality is pointwise setoid equality. These choices are
visible in
[`Instances/SupportedFunctions.v:20–51`](https://github.com/fasapa/nominal/blob/78f41a6c7ca1b55814b7b7c7d734ad4decaac523/theories/Instances/SupportedFunctions.v#L20).
They are separate from restricted proof elimination. Equating such records by
ordinary equality would also equate their possibly different stored supports.
Lean's `NFun` stores support existence in a proof field and has a proved
`FunLike` extensionality interface, so that particular obstruction does not
transfer unchanged.

The inspected
[`FreshnessTheorem.v`](https://github.com/fasapa/nominal/blob/78f41a6c7ca1b55814b7b7c7d734ad4decaac523/theories/FreshnessTheorem.v)
proves a Some/Any statement about supported-function output freshness;
`Lambda.v` separately proves `fcb_some_any`. These are positive evidence against
describing the precursor as unable to reason about Some/Any at all. A general
relational wrapper and these specialized statements are different API claims.

A local `git diff` between main and `lsfa2025` was empty for these three files.
Their imported dependency closures still differ: the tag has the active
permutation-instance admissions documented in
[research correspondence](../research-correspondence.md). No Rocq build or
`Print Assumptions` was run here; byte-identical theorem source is not proof of
identical trusted dependencies.

## Quotient descent and genuinely dependent motives

**Checked.** For any `Setoid X`, the probe constructs an equivalence

```lean
(Quotient s → Prop) ≃
  {P : X → Prop // ∀ x y, s.r x y → (P x ↔ P y)}
```

Pullback is precomposition with `Quotient.mk s`; descent uses
`Quotient.lift` and `propext`; both inverse laws are proved. The result needs
no nominal structure and therefore applies to any eventual generic alpha
quotient once its equivalence relation is established. It does not prove that a
proposed signature's alpha relation is itself an equivalence relation.

For an equivariant setoid equipped with the existing quotient action, the probe
also proves, for every finite `S`,

```lean
supports S (PFun.mk P) ↔
  supports S (PFun.mk (fun x => P (Quotient.mk s x)))
```

Thus pullback preserves and reflects support in the tested representation;
quotienting does not manufacture finite support for arbitrary predicates. This
action-level theorem uses the reference library's same-universe quotient
instances. That restriction is not a requirement for `Package/`; the predicate
descent equivalence itself has no such atom/carrier restriction. The reference
lambda `Term` defines its action manually, so automatic instance elaboration for
that concrete quotient is a separate interface issue; this probe does not
register a new lambda instance. A different quotient/action implementation must
establish its own corresponding laws.

**Checked negative result.** On current raw lambda terms, the predicate “the
root binder is named `a`” cannot descend. The probe uses distinct `a,b` and
alpha-equivalent `λa.a`, `λb.b` to contradict the purported quotient predicate.
This is a proved nonexistence result, rather than a deliberately broken proof.

**Source-verified and checked.** Lean does support dependent quotient
elimination. Given `C : Quotient s → Sort v`, `Quotient.rec` takes
`f : ∀ x, C (Quotient.mk s x)` and the condition that transporting `f x`
along `Quotient.sound hxy` equals `f y`. `Quotient.hrecOn` states the condition
using heterogeneous equality. For subsingleton fibers, `recOnSubsingleton`
discharges coherence. The probe constructs both the general recursor wrapper
and the genuinely quotient-indexed family `{r : Quotient s // r = q}`.

This does not solve an arbitrary raw `Type`-valued family. Two distinctions
remain:

1. To **construct the family on the quotient**, equality of raw fiber types is
   sufficient for `Quotient.lift`; mere equivalence of types does not imply their
   equality in Lean's standard foundations. In particular, alpha-compatibility
   transfer maps in both directions are weaker still: the probe gives maps
   `Unit → Bool` and `Bool → Unit` and proves `Unit ≠ Bool`.
2. Once a quotient-indexed family exists, constructing a **section with prescribed
   representative equations** requires coherence of its values. Proof-valued
   fibers are subsingletons; general data-valued fibers need a genuine argument.

Classical representative selection can define some quotient-indexed data or
families, and can select data from proved existence. It does not automatically
give representative-independent computation equations or nominal support.
Accordingly, a first package milestone can promise arbitrary `Prop` induction
and separately specified supported recursion without promising unrestricted
dependent alpha recursion. “Dependent quotient elimination is impossible” would
be an incorrect explanation for that scope decision.

Restricted elimination from a proof of `∃ x, P x` into data remains a real Lean
rule; classical `Classical.choose` is an available different construction.
Inspection of `Lean.Expr` happens in the metaprogram, not by eliminating a proof
at runtime. `propext` is sufficient for the `Prop` quotient bridge and requires
no syntax inspection. These foundational mechanisms must not be conflated.
[Official propositions reference](https://lean-lang.org/doc/reference/latest/The-Type-System/Propositions/).

## Supported predicates: representations and laws

There is no observed mathematical obstruction to the reference `NFun α X Prop`
under an explicit discrete truth-value instance. The initial note checked this;
the later probes tested its relationship to subsets and operations. Those
results make it a candidate, not the required foundation for the new package.

| Choice | Advantages | Unresolved or costly part |
| --- | --- | --- |
| Reference `NFun α X Prop` with an explicit instance | Can reuse support, application, composition, curry/uncurry and evaluation | In that interface, `Prop` alone cannot determine the atom `outParam`; public elaboration needs a policy |
| A supported-subset representation | Natural membership, Boolean/order vocabulary; avoids promising every subset nominal | Needs a coherent action and support API; conversions are required only for interfaces actually chosen |
| A dedicated atom-indexed truth wrapper | Atom type appears in the carrier and helps instance inference | Coercion/`Iff` rewriting becomes additional user-facing work unless hidden well |
| Bare predicates with explicit logical-support proofs | Keeps ordinary `Prop` statements and supports automation certificates | Must specify how support evidence and higher-order nominal arguments are carried; existing `NFun` bundling is one option |
| A newly designed action/support and predicate interface | Can make atom/action parameters explicit, redesign typeclass inference, or use structures instead of inherited classes | Must prove its action, support and logical laws and test its own universes and elaboration; old probes do not certify it |

These alternatives are illustrative, not an exhaustive list or a restriction to
wrappers around the current API. They may include replacing the underlying
function, support or quotient machinery. Compare ordinary-use clients and proof
costs; neither reuse nor replacement is the default obligation.

**Checked representation bridge.** The probe defines logical support by
invariance `P (π • x) ↔ P x` for permutations fixing `S`. It proves this
equivalent to existing `supports S (PFun.mk P)` and constructs an actual type
equivalence between `NFun α X Prop` and supported subsets using this condition.
Both round trips are extensional equality. It also proves that transporting the
NFun action through this equivalence gives direct-image membership:

```text
x ∈ π • S  iff  ∃ y, y ∈ S and π • y = x.
```

This establishes semantic compatibility without installing a global action on
bare `Set X`, or claiming that a complete production subset API has been built.
The logical-operation probes quantify independently over atom universe `u`,
domain universe `v` and quantified-domain universe `w`. `Prop` is a legitimate
carrier for this use; there is no requirement to replace it by a data-valued
formula type to satisfy the universe checker.

**Checked instance warning.** A naive parameterized
`local instance {α} [Name α] : Nominal α Prop` is rejected at instance
registration: Lean cannot determine a synthesis order because `Name ?α` remains
unknown and `α` is an output parameter. The persistent diagnostic probe checks
that failure with `#guard_msgs`. The working probes use an explicit `letI`
selection. A scoped instance declaration does not, by itself, establish that
this registration problem has been solved. This is an elaboration limitation
of that declaration under the tested `Nominal`/`Name`/`outParam` interface, not a
failure of the discrete mathematical action or a universal restriction on
possible `Prop` interfaces. A redesigned parameter or class discipline is open
for investigation in `Package/`.

**Checked action warning.** Under the discrete truth action, Mathlib's ordinary
pointwise action on `X → Prop` fixes every function pointwise. The NFun/PFun
action uses inverse precomposition. The probes exhibit both equations. Reusing
the bare function action for predicate support would certify the wrong property.
`Set X` is also function-represented, and Mathlib has scoped pointwise set-image
instances: any future design must make its action choice explicit and test
coherence. Preserve the mathematical distinction between conjugation and
pointwise action. The existing `PFun` wrapper is optional; a new action interface,
an alternative wrapper or explicit action parameters may enforce the distinction.

The following is a candidate semantic law contract independent of inherited
declaration names. “Checked” identifies historical probe evidence; other rows
follow directly from reference interfaces or are proposed derived API rather
than claims of new exported declarations. Any selected `Package/` representation
needs its own verified versions of the promised laws.

| Operation | Support contract | Status |
| --- | --- | --- |
| `¬ P` | Any support of `P` supports its complement | Checked |
| `P ∧ Q` | Union of support bounds | Checked |
| `P ∨ Q`, `P → Q`, `P ↔ Q` | Union of support bounds | Mathematical derivation by Boolean operations; current equivariant relation versions already exist |
| `∀ y, R(x,y)`; `∃ y, R(x,y)` | Any support of the jointly acted relation remains a support after quantification over the whole carrier | Checked |
| `P ∘ f` | `supp P ∪ supp f` is a support bound | Existing `NFun.comp` / `supports_pfun_comp` |
| `R(p,·)` | `supp R ∪ supp p`; if `R` is jointly equivariant, `supp p` suffices | Existing `NFun.fromParam`, application and curry APIs; initial equality-predicate probe |
| `И a, R(a,x)` | Intended support bound from joint relation and captured parameters | Current cofinite permutation law provides the key ingredient; general packaged binder operation not added here |
| Higher-order quantification | Quantify supported functions/subsets when working internally in the nominal predicate calculus | Pitts' Finite Support Principle; no claim that an arbitrary external family is supported |

Bounds are not asserted to be exact least supports. For instance, conjunction
with `False` can discard all dependence on a parameter.

**Checked Some/Any bridge.** The historical probe proves that every bundled supported
atom predicate has a finite or cofinite truth set, then derives its fresh-negation
law through current `freshQuantifier_neg`. It also proves both the lack of finite
support and the failure of fresh-negation self-duality for any predicate with
infinite truth and falsehood sets. Together with the initial note's checked
Some/Any evaluation wrapper, these provide evidence and possible proof material
for the desired predicate API. They do not validate a different representation.
No fresh selector is introduced; the earlier nonexistence result for supported
fresh selectors remains applicable under that finite-support contract.

## What the reference induction already guarantees

[`Term.strong_ind`](../../Instances/LambdaCalculus/Induction.lean) has an
arbitrary motive `P : Term α → Z → Prop` and a nominal avoidance context `Z`.
Each recursive hypothesis is generalized over **all** contexts. The lambda
step receives `a # z`; the motive itself has no support/equivariance hypothesis.
`strong_ind_finset` takes any finite avoidance set. Therefore that set need not
be, or contain, the motive's support. An unsupported motive can still be supplied
to the theorem; of course the caller must prove its constructor steps.

[`Beta.strong_ind` and `Parallel.strong_ind`](../../Instances/LambdaCalculus/ReductionInduction.lean)
likewise accept arbitrary endpoint/context predicates. They are induction on
**derivations**, retain recursive derivations and context-generalized induction
hypotheses, and use relation equivariance to transport premises. Their binder
renaming also uses quotient constructor equality, freshness preservation and
`subst_rename`; relation equivariance alone is not all their proof requires.
The contraction cases expose freshness for argument terms as well as the
context, and never require the binder fresh for its own body.

There is a small reference-interface universe distinction: term strong induction
uses its context in the atom/term universe, whereas reduction strong induction
allows a separate context universe. This is an observed difference to consider
when selecting and testing the new theorem contracts, not a proposition-level
impossibility or an inherited restriction on generation.

For a user-defined judgment, the package must establish its own rule
transport/renaming criterion. A rule's side condition may inspect a distinguished
atom, use an unsupported predicate or call a non-equivariant selector. It cannot
be certified merely because its endpoints are nominal types. Even an equivariant
relation need not allow arbitrary freshness assumptions on all names appearing
in its rules: which names are bound in a conclusion, and what remains fixed
during renaming, must be justified. Generated fresh induction must preserve the
meaning of the original judgment or prove any proposed fresh-rule presentation
equivalent to it.

## Recommendations and open obligations

**Recommended semantic boundary, with implementation open.** Preserve the
strength of arbitrary-motive fresh induction for alpha-equated syntax and
ordinary `Prop` judgments. Investigate supported-predicate theory for logical
operations and Some/Any without forcing every client proof through a supported
predicate wrapper. Raw alpha-compatible predicates and quotient descent are one
construction route; the existing `NameAbs`, quotient and induction machinery are
optional implementations of relevant contracts. Reuse, adapt or reprove the
needed bridges for the chosen representation in `Package/`, with explicit
foundational dependencies and no implicit full-core rewrite in PKG-01.

For the proposed first lambda-plus-FOL workflow, object-language formulas should
be generated syntax, while satisfaction, substitution lemmas, typing and
derivability remain ordinary Lean predicates. Parameterize the action of semantic
environments and interpretations deliberately: a fixed environment may carry
support, and arbitrary atom-indexed assignments need not be nominal. A syntactic
substitution theorem is a useful first test without making an unrestricted
semantic model automatically nominal. The larger selected portfolio—lambda
calculus with `let`, π-calculus and μ-binders—should stress the eventual rule and
recursion contracts; these probes do not certify them in advance.

Resolve the following in the corresponding roadmap stages; later induction and
generation obligations are not all prerequisites for predicate task PKG-01:

1. **Public representation and elaboration.** Compare explicit actions, redesigned
   classes, wrappers, subsets and supported-function representations by small
   ordinary-use clients, including two different atom carriers in separate scopes.
   Require directed `simp`, `Iff` rewriting and useful higher-order application,
   without requiring compatibility with `NFun`. Do not choose a representation
   only because one raw instance declaration is convenient.
2. **Theory sufficient for the first workflow.** Export support certificates for
   logical operations, fixed parameters, evaluation and Some/Any before building
   a general reflection engine. Most zero-support relation operations already
   exist in the reference `Equivariant.lean`; evaluate reuse, adaptation or
   replacement against the selected foundations. Declare which laws PKG-01
   actually needs; a complete predicate calculus is not an implicit prerequisite.
3. **Generated arbitrary induction.** Prove a theorem for the actual selected
   signature grammar, including the promised multiple categories. Pitts' supported
   theorem and Copello's restricted universe are evidence, not substitutes for
   this proof.
4. **Rule induction.** Specify bound positions, premise dependencies, rule
   equivariance and representative-renaming obligations. Require generated
   certificates or expose unsolved obligations honestly. Distinguish this from
   ordinary induction, term induction and fresh inversion.
5. **Dependent scope.** State explicitly whether the command generates only
   `Prop` induction, supported iteration, primitive recursion, or a dependent
   recursor with coherence premises. Do not advertise these as interchangeable.
6. **Automation.** Inspect elaborated expressions and local identities, recognize
   proved primitives, and account for captures. Unsupported globals and arbitrary
   choice require proofs or a useful failure message, not inferred equivariance.
7. **Research writing.** Record the exact theorem contract and source version
   alongside each implemented certificate; retain counterexamples and failed
   designs as tests of scope. This note is evidence for the architecture decision,
   not a completion mark for a package roadmap task.
8. **New implementation validation.** Plan `Package/` targets, client tests and
   an axiom audit that reaches its declarations, including replacement foundations.
   Reference-library builds and probes provide comparison evidence only; they
   do not validate new code. This documentation revision adds no such code or
   build configuration.

## Reproduction and limits

Persistent research probes recorded by the original investigation:

- [PredicateFoundations.lean](probes/PredicateFoundations.lean): descent,
  dependent elimination, subset bridge, logical support, support reflection,
  Some/Any Boolean bridge and proved negative cases.
- [PredicateInstanceProbe.lean](probes/PredicateInstanceProbe.lean): an expected
  instance-registration rejection checked with `#guard_msgs`.

Commands run from the repository root during that investigation:

```sh
pdftotext -layout ref/nominalsets.pdf /tmp/predicate-nominalsets.txt
sha256sum ref/nominalsets.pdf
lake env lean docs/research/probes/PredicateFoundations.lean
lake env lean docs/research/probes/PredicateInstanceProbe.lean
git diff --check
git diff --no-index --check /dev/null docs/research/2026-10-05-predicate-foundations.md
git diff --no-index --check /dev/null docs/research/probes/PredicateFoundations.lean
git diff --no-index --check /dev/null docs/research/probes/PredicateInstanceProbe.lean
```

At that investigation's baseline the new files were untracked research artifacts.
Their explicit `--no-index` checks emitted no whitespace diagnostics (exit 1
denotes the new-file diff). Local Markdown link targets were also checked for
existence. This is historical provenance, not a statement of their present Git
status or a new verification run.

Those Lean checks used the then-built imports and pinned dependencies, not a new
full build, fresh project-artifact rebuild or dependency bootstrap. Representative
`#print axioms` commands are retained in the probe. The descent equivalence reports
`propext` and `Quot.sound`; the dependent recursor witnesses report `Quot.sound`;
`unit_ne_bool` has no axioms. The other printed results report only the standard
`propext`, `Classical.choice` and `Quot.sound`. These are research declarations,
not integrated public interfaces. External Rocq, Agda and Isabelle developments
were not built. No claim of unrestricted dependent nominal recursion, generic
fresh rule induction, semantic FOL interpretation support, or complete external
lattice structure was established by these probes.
