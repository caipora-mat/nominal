# PKG-01 readiness and proposed predicate contracts

Date: 2026-10-05. **Research/design proposal for review, not an approved
implementation plan.** Inspected checkout: `fasapa/nominal-package`, HEAD
`76966b1f2e44f594517442b6572e33abaa9038e0`. The preceding research revision was
`7fed53a2e5fc67379f86f085515e310e7c1fddb7`; the completed reference baseline is
`4279ba92efacd77b3b96e507631502272b489999`.

**Subsequent approval:** the author approved the bounded F02 + F03a specification
and requested a LaTeX article under `docs/article/` maintained alongside its
implementation. The [implementation plan](../superpowers/plans/2026-10-05-package-foundation-kernel.md)
was approved for native execution. The broader predicate/support contracts below
remain proposals. The initial assessment is retained below. F02/F03a originally
delivered three production source modules and 77 audited declarations; the
historical F03b extension had four production source modules, one audit
module and 81 audited production declarations. The subsequent checked F04a extension
has five production source modules, one audit and 104 audited declarations.
The author removed the standalone Package
examples layer during execution; persistent usage examples are reserved for
future case studies. Temporary public-import checks are scratch evidence only.

The intended outcome is a reusable nominal package for ordinary Lean proofs
about languages with binders. This increment selects its prerequisites and
predicate contracts; it does not implement the five case studies. Classical
Lean/Mathlib, ordinary `Prop`, actual quotients, least support, arbitrary-motive
fresh induction, one atom sort and single/nested binders remain the brief.
Architectural freedom and top-level `Package/` are settled. No backward
compatibility requirement or reference-library dependency is inferred.

The initial tracked tree was clean. Existing untracked files were
`docs/research/pkg-01-start-prompt.md`,
`docs/research/probes/PredicateInterface.lean`, and
`docs/research/probes/PredicateSomeAny.lean`. They are preserved unchanged.
No branch switch, merge, commit, dependency change, production implementation,
or CI change belongs to this session. The active tracker is the
[package roadmap](../nominal-package-roadmap.md), not the historical roadmap.

## Current status after F04d implementation

**2026-10-07 reconciliation:** F04d is committed at
`32f3dba551761881409bbc7453054e214e582269`, with a clean initial checkout for
F05. The [new investigation](2026-10-07-function-space-foundations.md) and
[written F05 specification](../superpowers/specs/2026-10-07-package-function-space-design.md)
reassess the direct-SPred recommendation below. They recommend a hybrid
function foundation; the final supported-predicate storage remains a PKG-01
review decision. The author subsequently approved the F05 specification;
its [implementation plan](../superpowers/plans/2026-10-07-package-function-space.md)
was approved for native execution. F05 now supplies the function/predicate-input
foundation with passing integrated checks and a clean independent final review.
This does not approve direct-SPred storage or start PKG-01.

The approved canonical-instance/freshness slice now supplies four nominality
certificates for existing actions, exact atom/discrete/product/Finset supports,
and `hx.Fresh a` / `Fresh A a x`. Transport, sufficient bounds, fresh swaps,
nested-product decomposition and combined finite avoidance retain the approved
assumption separation. Individual supported elements need no nominal carrier;
canonical nominality itself needs no infinitude. Finset's action and certificate
remain Pointwise-scoped. See the
[F04c plan](../superpowers/plans/2026-10-06-package-canonical-freshness.md) and
[active tracker](../nominal-package-roadmap.md) for checks and final-review status.
F04c is delivered with passing integrated checks and resolved independent review;
the two minor tracker/test findings were corrected and rechecked.
The author's later approved extension makes `Fresh A x y` the general
support-disjointness relation, with `hx.FreshWith hy` for individual evidence.
Atom freshness is a derived interface. Product decomposition now works on both
sides; disjoint sufficient bounds, finite-set contexts and equivariant images
have general laws. See the [generalization review](2026-10-06-foundation-generalizations.md)
for the accompanying independent investigations and remaining proposals.
Canonical equivariant quotients are now implemented under the approved F04d
specification and native plan. General scalar/monoid action constructors require
only invariant-setoid evidence; explicit local installation fixes the canonical
projection contract. General surjective nominality transfer and the existing
map laws give quotient finite/least-support bounds. The supported-fiber theorem
needs only one supported preimage, and specializes to the exact intersection
of representative supports on a nominal source. General freshness-map laws
supply the context consumers. See the
[F04d plan](../superpowers/plans/2026-10-06-package-equivariant-quotients.md) and
active tracker for passing integrated validation and a clean independent final
review. F04d and the reconciled PKG-F04 are delivered and committed. Function/predicate input interfaces (F05) are now implemented with passing
integrated checks and a clean independent final review. Full predicate descent/support reflection
and predicate foundations (PKG-01) remain undelivered.

F04a/F04b were committed at `68956dd`, and F04c/general freshness at `9c1cb9a`;
the records below preserve their
historical uncommitted delivery states. The old predicate proposals do not
override the delivered support/freshness signatures. In particular `Fresh`
now names support-disjointness freshness, with atom freshness as a specialization,
not the cofinite predicate quantifier sketched below.

## F04b implementation record (historical)

The current Package source supplies the permutation/action kernel and its
production audit. **F03b** now proves swap generation with endpoints in the
original moved set, arbitrary-set avoidance, and the selected-action criterion.
All four results are kernel-checked without an infinite-atom assumption. F03b's
independent final review is clean. F04a supplies the finite support calculus,
and F04b now supplies nominality and least support; F04c/F04d and F05 still
precede PKG-01.

**F04b implementation update (2026-10-06):** the author approved the
[least-support specification](../superpowers/specs/2026-10-06-package-least-support-design.md)
and [native plan](../superpowers/plans/2026-10-06-package-least-support.md).
All 19 declarations and six temporary consumers/signature files pass.
Nominality is a proof-only certificate for the selected action, without atom
assumptions. Under `Infinite A`, least support is available for an individual
`hx : FinitelySupported A x`, with a convenient carrier interface and proof
independence. Decidable equality is confined to the finite-set transport
equation. Images give inclusions, without carrier-wide assumptions in the
elementwise result. Coverage reaches six production source modules and one
audit; the direct audit checks 132 declarations in five defining modules with
standard axioms only. The matching LaTeX section compiles. Independent final
review found no Critical, Important or Minor issues, with independent code,
article and preservation checks. F04b is delivered; changes remain uncommitted. Canonical nominal instances,
freshness, quotients and function/predicate interfaces remain later work.

**F04a design update:** the current inspection is at committed F03b revision
`34a83358739ab962e2b9d2035a21d67b2a896071`, initially with a clean tree. The
[F04a specification](../superpowers/specs/2026-10-05-package-finite-support-design.md)
is approved and selects finite-bound support as an abbreviation of pinned Mathlib's
`MulAction.Supports`, elementary support laws and infinite-atom finite
intersection. Its [implementation plan](../superpowers/plans/2026-10-05-package-finite-support.md)
was approved for native execution. All 18 public declarations, temporary consumers
and whole-production audit now pass; the matching LaTeX mathematics is written and
compiled, with a clean independent final review. F04a is delivered in the working
tree, uncommitted. The active
tracker records `F04a → F04b → F04c/F04d`. The F04b update above discharges
the nominality/least-support interface; freshness and canonical quotients
remain F04c/F04d, and map/predicate bundles remain F05/PKG-01. This refines the older combined proposals below without
reopening F02/F03 or treating historical probe checks as new-package proofs.

The [F03b specification](../superpowers/specs/2026-10-05-package-controlled-swaps-design.md)
and [implementation plan](../superpowers/plans/2026-10-05-package-controlled-swaps.md)
were approved for native execution. `Perm.swap_factorization` specializes pinned
Mathlib's restricted-swap closure theorem and extracts a controlled list.
`Perm.swap_factorization_avoiding` derives avoidance for arbitrary `Set A`;
`Perm.smul_eq_of_swap_smul_eq` and `Perm.forall_smul_eq_iff_swap_smul_eq` consume
it for any selected action. Production coverage and the direct standard-axiom
audit pass, and the independent final review found no issues.

Every next increment includes its LaTeX work in the same scope and completion
criteria. F03b extends `docs/article/sections/foundations.tex` with the controlled
factorization, avoidance and action-invariance propositions and proof explanations.
Its references/evidence are synchronized and the article compiles; the independent
review also performed a fresh manuscript build. F03b is complete.
See the [current roadmap](../nominal-package-roadmap.md) for acceptance details.

## Initial readiness against the proposed design (historical)

This table records the original F01 inspection before Package implementation.
Its missing-F02/F03a statements do not describe the current working tree.

| Task | Evidence at the original F01 inspection | Missing evidence / next action at that time |
| --- | --- | --- |
| F01 | Both algebraic modules read directly at `983adeb9b80f75fb7c77c05acfd2fcef16db1d46`; declaration-level assessment, dispositions and bounded probes in the [source investigation](2026-10-05-algebraic-source-investigation.md); F02 + F03a boundary approved | First implementation plan awaits review; later layer choices remain proposed. Remains IN PROGRESS. |
| F02 | `lakefile.toml` registers only Nominal, Instances and Examples. `Package/` and `Package.lean` are absent. Existing import checker reaches 37 library and 15 example modules | Establish independent Package target, consumers, import policy and module-origin audit. No existing command certifies Package. |
| F03 | Reference `FinitePerm` supplies the subgroup, swaps and factorization; `PermType` supplies actions but has an atom `outParam`. Pinned Mathlib supplies group/action/product interfaces | Approved new subgroup boundary and standard `MulAction` consumers are not integrated. F03a plan review is pending; remaining swap/support prerequisites need F03b. |
| F04 | Reference Support/Nominal/Freshness/EquivalenceClass prove finite/least support and quotient results for their own actions; quotient instances share atom/carrier universes | No proofs at the new action boundary. Reprove/adapt support intersection/minimality, freshness and the canonical quotient projection contract in separate increments. |
| F05 | Existing predicate probes establish several possible input interfaces. A new Mathlib-only scratch probe checks direct predicate action and support transport, independently of old nominal classes | Select and integrate logical-support/map certificates with consuming examples. A full supported-function bundle is unnecessary for the recommended PKG-01 representation. |
| PKG-01 | Reference and scratch predicate evidence is substantial | Not ready for production implementation: F02–F05 are not discharged. No PKG-01 checkbox is completed by this design. |

F06 binder descent remains later work for induction/recursion. Neither generic
predicate descent through an already specified setoid nor its support theorem
requires name abstraction, concretion, FCB, initial chains or a syntax generator.

The coverage gap is concrete: `scripts/check-imports.py` enumerates only
Nominal/Instances/Examples; `scripts/fresh-build.py` copies those directories;
`Examples/AxiomAudit.lean` filters module origins to Nominal/Instances. Its
namespace-independent filtering is a useful technique to adapt, but it currently
excludes future Package declarations. Reference builds remain preservation
checks, not new-foundation evidence.

## Representation comparison and recommendation (historical proposal)

| Candidate | Benefit | Cost / mathematical boundary | Disposition |
| --- | --- | --- | --- |
| Direct `SPred A X` with `toFun : X → Prop` and support existence in a proof field | Ordinary application, proof-irrelevant extensional equality, explicit atom parameter, no truth action; only an action on X is needed | Must prove its own action/nominality/logical API; a later general supported-function interface needs a proved adapter if wanted | **Recommend** with an unbundled support-certificate API |
| Newly designed supported functions specialized to Prop | Shares composition, evaluation and higher-order theory with later function definitions | Requires selecting a larger function-space boundary before predicate delivery; conjugation still needs a distinct representation or explicit action | Defer the general bundle to demonstrated function clients; supply minimal map certificates now |
| Supported subsets as the primary carrier | Membership and Boolean algebra vocabulary are natural; same mathematics as predicates | Ordinary function application needs an adapter; arbitrary external completeness is false; bare Set has competing action interpretations | Provide an extensional, action-compatible subset view of SPred |
| Adapt existing NFun-to-Prop | Most function operations and proofs already exist | Imports its nominal classes, requires nominal domain/codomain, and must manage truth-instance inference; generic Prop registration fails in that interface | Viable alternative, not selected; retain probes as comparative evidence |

The direct recommendation follows the smaller mathematical prerequisites and
desired application interface, not merely one successful elaboration. The old
`PredicateInterface.lean` tests an NFun-backed structure and abbreviation; it
does **not** certify this direct representation. The abbreviation's guarded
examples also show that ordinary `NFun.ext`/`.comp` elaboration can still require
a locally selected truth action. Those are specific interface costs, not a
theorem that generic truth actions are impossible in Lean.

No global action is installed on bare `Prop`, `X → Prop`, or `Set X` for the
predicate representation. A truth value and a whole predicate are different
objects. The proposed SPred action is inverse precomposition. Mathlib's ordinary
function action remains pointwise; nominal map certificates below express
conjugation mathematically without changing that instance.

## Proposed foundation boundary and per-layer decisions

The proposed namespace is `NominalPackage`. Use `A : Type u`, `X : Type v`,
`Y : Type w`, and further independent universes where needed. The public first
foundation uses `MulAction (Perm A) X` directly, with A present in the group
input, rather than an atom-outParam action class. A proof-only later class
`Nominal A X : Prop` certifies finite support for every element of the **already
selected** action; it does not carry another action. No theorem is polymorphic
over an unrelated replacement action while claiming a canonical support formula.

Atoms require `[Infinite A]` for nominal support/freshness theory, not
countability. The finite-permutation group and ordinary action laws need no
infinitude. `DecidableEq A` is explicit on executable swaps/finite-set operations
where required; classical instances can discharge it locally. Support witnesses
stay in proof fields, and chosen least supports may be noncomputable.

| Layer | Proposed dependency decision | Cost and obligations |
| --- | --- | --- |
| Atom assumptions | Adopt Mathlib `Infinite`; no replacement `Name` class | More explicit parameters where A is not inferable; avoids duplicating an assumption class |
| Finite permutations | Adapt the finite-moved-point subgroup mathematics into Package over Mathlib `Equiv.Perm`/`Subgroup` | New application/group/swap proofs and audits; no import of old `Nominal.Wheels` or root-level declarations |
| Actions/equivariance | Adopt Mathlib `MulAction`, products and scoped Finset image action; expose narrow Package equations | Check action coherence, two atom carriers, empty domains and independent universes; no blanket discrete action on arbitrary types |
| Discrete data | A distinct `Discrete A X` structure with trivial action | Prevents collisions when A itself is Nat or another ordinary data type |
| Finite/least support | Adapt/rederive the support mathematics against the new group and selected actions | Swap characterization or an equivalent proof, finite intersections, least-support existence/transport/minimality; new proofs, not theorem-name reuse |
| Freshness | Derive from least supports plus certified upper bounds | Fresh existence, combined finite avoidance, swaps; never identify least support with strong support |
| Products/finite atom sets | Adopt standard action constructions, rederive required support formulas | Product support union is exact; other operation bounds are not automatically exact |
| Quotients | Adopt Lean Quotient; construct its canonical action from an equivariant setoid | Separate atom/carrier universes, projection equation/surjectivity, action laws and support upper bound; no arbitrary-action support promise |
| Function/predicate inputs | Rebuild minimal logical `SupportsPred` and `SupportsMap` certificate layer | Transport, composition/evaluation and fixed-parameter bounds; no arbitrary-function support instance |
| Supported predicates | Direct proof-field bundle and supported-subset equivalence | New FunLike/ext/action/nominality and logical/descent proofs |
| Binder descent | Defer implementation to F06; rederive or adapt fresh-representative descent when its handler contract is chosen | Guarded computation and scoped representative independence; equivariance alone does not prevent binder leakage |
| Syntax carriers | Retain staged raw syntax/quotients with shared certificates as a candidate; compare generic carrier and bespoke generation at PKG-02 | No backend is established by F03a. Constructor/action/scope and arbitrary-motive induction must be tested on actual syntax |
| Recursion/rule transport | Defer; learn from reference iteration and derivation induction without importing them | Primitive recursion needs original subterms; rule transport must preserve all premises, IH applicability and whole conclusions |

No production import from `Nominal` or `Instances` is proposed for this route.
That increases the proof work in F03b/F04 but avoids importing their class and
instance policy as an accidental constraint. Reconsider a layer if actual proof
costs outweigh the interface benefit; record a changed decision before importing
it. This is selective adaptation over Mathlib, not an obligation to rewrite
Mathlib or the entire reference library.

For later carrier comparison retain the candidate grammar
`unit | atom | data D | rec i | product S T | bind S`. Atom positions are fixed
by recursive maps but acted on by permutations; recursive positions are mapped.
`bind S` covers exactly S. In particular, let has an unscoped RHS and scoped
body. Finite mutual categories are a later tested goal, not implemented by the
first increment. Generic initiality and structural adjunctions are deferred.
The algebraic investigation explains why their stubs cannot discharge F01–F05.

## Exact semantic contracts proposed for F04/F05 and PKG-01

The following are mathematical signatures for review, not already exported Lean
declarations. Unless a row adds nominality, carriers need only the selected
`MulAction (Perm A)`; X and Y need not have finite support at every element.
All equality below is Lean equality, and predicate extensionality uses `propext`
and function extensionality. Finite sets S and T contain atoms of A.

### Support and map inputs

```text
Fixes S π             := ∀ a ∈ S, π a = a
Supports S x          := ∀ π, Fixes S π → π • x = x
FinitelySupported x   := ∃ S : Finset A, Supports S x
Nominal A X           := ∀ x : X, FinitelySupported x       -- proof-only class
SupportsPred S p      := ∀ π, Fixes S π → ∀ x, p (π • x) ↔ p x
SupportsMap S f       := ∀ π, Fixes S π → ∀ x, f (π • x) = π • f x
Equivariant f         := ∀ π x, f (π • x) = π • f x
```

These map certificates are the fixed-point condition for conjugation
`(π ⋅ f) x = π • f (π⁻¹ • x)`, not for pointwise function action. For predicates
the codomain action is represented by logical equivalence, so it needs no Prop
instance. Required F05 laws include monotonicity of bounds, support transport
under permutation, `SupportsMap ∅ f ↔ Equivariant f`, composition with union
bounds, and
`SupportsMap S f → Supports T x → Supports (S ∪ T) (f x)`.

With `[Infinite A]` and a nominal X, F04 supplies `support x : Finset A` with:

```text
Supports (support x) x
Supports S x ↔ support x ⊆ S
support (π • x) = π '' support x
support (x,y) = support x ∪ support y
support (a : A) = {a}                     -- canonical atom action
support (s : Finset A) = s                -- canonical image action
a # x ↔ a ∉ support x
∀ S : Finset A, ∃ a, a ∉ S                -- requires Infinite A
Supports S x → a ∉ S → b ∉ S → swap a b • x = x
```

Here `π '' S` means finite image, not an assertion of pointwise fixation.
Support intersection and its hypotheses must be proved before least support is
claimed. The unordered pair `{a,b}` fixed by swapping distinct a,b is the
required counterexample to the converse strong-support assertion.

### Predicate carrier, action and ordinary use

```text
SPred (A : Type u) (X : Type v) [MulAction (Perm A) X] : Type v
  toFun       : X → Prop
  isSupported : ∃ S : Finset A, SupportsPred S toFun

ofSupported (p : X → Prop) (h : ∃ S, SupportsPred S p) : SPred A X
ofSupported p h x ↔ p x
p = q ↔ ∀ x, p x ↔ q x
(π • p) x ↔ p (π⁻¹ • x)
1 • p = p
(π * σ) • p = π • (σ • p)
(π • p) (π • x) ↔ p x
Supports S p ↔ SupportsPred S (fun x => p x)
```

Provide `FunLike`, an Iff-based `@[ext]` lemma, directed application `simp`
lemmas, and ordinary coercion to `X → Prop`. Proof irrelevance makes the chosen
support witness invisible to equality; no support finset is stored as data.
Provide a nominal instance for SPred even if X has only an action.

The subset interface is
`SPred A X ≃ {U : Set X // ∃ S, SupportsPred S U}` with both inverse laws and
`x ∈ (π • p).toSet ↔ ∃ y, y ∈ p.toSet ∧ π • y = x`.
The action on the supported subset carrier is transported/proved explicitly;
this does not install an action on bare Set or a CompleteLattice instance.

Ordinary-use tests must exercise `p x`, passing p to an ordinary higher-order
function, rewriting a hypothesis using pointwise Iff, `ext x`, proof-witness
independence, and simultaneous `SPred A X` / `SPred B Y` in separate atom scopes.
Avoid a coercion from *every* ordinary predicate into SPred: a certificate is
required exactly at that construction boundary.

### Logical operations, quantification and fixed parameters

For `SupportsPred S p` and `SupportsPred T q`, negation retains S; conjunction,
disjunction, implication and Iff have bound `S ∪ T`. Constant True/False have
bound ∅. Bundle these operations with the expected application Iffs and derived
least-support inclusions; do not assert all inclusions are equalities.

For `R : X × Y → Prop` with `SupportsPred S R` under the **joint product action**:

```text
SupportsPred S (fun x => ∀ y, R (x,y))
SupportsPred S (fun x => ∃ y, R (x,y))
Supports T y → SupportsPred (S ∪ T) (fun x => R (x,y))
Supports T x → SupportsPred (S ∪ T) (fun y => R (x,y))
```

Whole-carrier quantification needs only an action on Y: permutations are
bijections. It does not need `[Nonempty Y]`, even for empty Y. Quantification
over a domain predicate D uses the bound for the jointly supported expression
`D y → R (x,y)` or `D y ∧ R (x,y)`. A family of separately supported sections
does not imply joint support or one common finite bound.

The general section theorem uses finite support of the actual fixed parameter.
A general
`curry : SPred A (X × Y) → (X → SPred A Y)` therefore requires `[Nominal A X]`
or an explicit support certificate for each selected x. There is no such
unconditional curry for arbitrary acted-on X. In the joint-equivariant case
S = ∅, the support of the fixed parameter suffices; a fixed atom equality
predicate is supported without being equivariant.

For `SupportsPred S p` and `SupportsMap T f` require
`SupportsPred (S ∪ T) (fun x => p (f x))`. Bundle precomposition using an
existential map certificate; its equation is `precomp p f hf x ↔ p (f x)`.
No general SFun library is needed for this contract. Evaluation is jointly
equivariant by `(π • p) (π • x) ↔ p x`. A section of a supported higher-order
relation at a supported predicate value uses the same union-bound theorem.

### Raw and quotient predicates

For any `s : Setoid X`, with **no nominal assumptions**, let
`Compatible s p := ∀ x y, s.r x y → (p x ↔ p y)` and `q := Quotient.mk s`.
Require:

```text
descend (p : X → Prop) (hp : Compatible s p) : Quotient s → Prop
pullback (P : Quotient s → Prop) : X → Prop := P ∘ q
descend p hp (q x) ↔ p x
pullback (descend p hp) = p
descend (pullback P) (compatibility_of_pullback P) = P
(Quotient s → Prop) ≃ {p : X → Prop // Compatible s p}
```

For the support bridge add the action on X and
`∀ π x y, s.r x y → s.r (π • x) (π • y)`. F04 constructs the action on
`Quotient s` with `π • q x = q (π • x)`; it must not accept an arbitrary
quotient action in place of that law. Then for every S and arbitrary P:

```text
SupportsPred S P ↔ SupportsPred S (pullback P)
SupportsPred S (descend p hp) ↔ SupportsPred S p
```

Thus support existence is preserved and reflected. Once bundled, exact least
support is equal across pullback and descent. The stronger reusable lemma needs
only an equivariant **surjection** `q : X → Y`, not quotient internals or
nominality of X/Y. Omitting surjectivity permits arbitrary behavior off the
image and loses reflection. The supported equivalence is
`SPred A (Quotient s) ≃ {p : SPred A X // Compatible s (fun x => p x)}`,
with action compatibility and both inverse laws. Compatibility is stable under
predicate action because s is equivariant.

F04's object theorem `support (q x) ⊆ support x` is a different result; it is
not generally equality. Predicate pullback reflection does not assert exact
support of representatives. No support hypothesis is added to the ordinary
quotient-predicate equivalence or user induction motives.

### Some/Any with sufficient bounds

Define the cofinite operator for **any** ordinary atom predicate:
`Fresh p := ∃ S : Finset A, ∀ a, a ∉ S → p a`.
Under `[Infinite A]` and a certificate `hp : SupportsPred S p` for the canonical
atom action, require all three equivalences:

```text
Fresh p ↔ ∃ a, a ∉ S ∧ p a
Fresh p ↔ ∀ a, a ∉ S → p a
a ∉ S → (Fresh p ↔ p a)
```

S is any proved bound. Users need not compute the exact least support. The
context variant takes `R : A × C → Prop`, joint bound S, and `Supports T c`;
its exclusion set is `S ∪ T`. For jointly equivariant R only T is needed. A
nominal context supplies such a certificate via its support, but an explicit
bound is also accepted.

For jointly supported `R : A × X → Prop`, fresh quantification over its first
component preserves its bound on X. Boolean laws for Fresh at ¬, ∨, → and ↔
are exported with finite-support certificates on their operand predicates.
Constants and finite conjunction also have unconditional cofinite laws; do not
generalize the stronger Boolean laws to arbitrary predicates.

Retain these failures even for equivariant relations:
`Fresh (fun a => ∃ x, a = x)` holds while `∃ x, Fresh (fun a => a = x)` fails;
`∀ x, Fresh (fun a => a ≠ x)` holds while `Fresh (fun a => ∀ x, a ≠ x)` fails.
Supportedness does not authorize either quantifier interchange.

## Acceptance clients and counterexamples for the later predicate increment

These belong to later F04/F05/PKG-01 delivery, not the first kernel increment:

1. A fixed atom equality predicate, its singleton support bound, permutation
   equation, and a proof that it is not invariant under every permutation.
2. Boolean support with a larger-than-necessary bound; quantification over an
   empty acted carrier; a supported relation section using an explicit bound
   for its parameter; ordinary higher-order use and nested `ext`/`simp`/`rw`.
3. Generic raw/quotient round trips, canonical quotient action, and both support
   directions with atom/carrier universes independent. Include an arbitrary
   unsupported ordinary motive in quotient reasoning, without packaging it.
4. Some/Any at a user-supplied finite bound and after extending that bound with
   another context; use the resulting fact in a nontrivial conclusion.
5. If both `{a | p a}` and `{a | ¬ p a}` are infinite, prove
   `¬ ∃ S, SupportsPred S p`; derive a concrete infinite/coinfinite example.
   Finite/cofinite supported-atom-predicate classification delimits the API.
6. Prove no `f : Finset A → A` with `∀ S, f S ∉ S` has any `SupportsMap T f`.
   Classical fresh choice is allowed as an ordinary function, not certified.
7. Preserve the arbitrary-union counterexample using supported singletons
   indexed by an infinite/coinfinite atom subset, and the quantifier failures.
8. Prove the generic non-descent test: `s.r x y`, `p x`, and `¬ p y` rule out a
   quotient predicate computing p. Use a simple vacuous-binder quotient
   forgetting an atom label.
   The existing lambda alpha counterexample remains separate reference evidence;
   PKG-01 does not need to implement lambda syntax or F06 to illustrate it.

The exact non-descent obstruction is:
`s.r x y → p x → ¬ p y → ¬ ∃ P, ∀ z, P (q z) ↔ p z`.
Keep unsupported predicates legal in ordinary Lean. Negative tests reject a
false certificate or computation law, not ordinary application or arbitrary
Prop-valued induction.

## First bounded increment and review sequence

The concrete first increment is **F02 plus F03a: Package boundary and finite
permutation/action kernel**, specified in the
[written design](../superpowers/specs/2026-10-05-package-foundation-kernel-design.md).
It supplies no support, quotient, SPred, fresh quantifier, binder, recursor or
generator implementation. It explicitly leaves F03b, F04 and F05 acceptance
outstanding. The predicate contracts above constrain later designs without
turning their proofs into hidden work in the first increment.

The first specification and its dependency choices were approved, followed by
the written implementation plan and native execution. The implemented F02/F03a
slice and concurrent LaTeX exposition are recorded in the roadmap. Later F03b,
F04/F05 and PKG-01 contracts remain separate. Changes remain uncommitted at the
user's request.

## Evidence recorded in this session

The algebraic investigation records its pinned reads, original import failures,
three existing backend-probe reruns and one new non-descent probe. The predicate
investigation reran, without editing, each of:

```sh
lake env lean docs/research/probes/PredicateFoundations.lean
lake env lean docs/research/probes/PredicateInstanceProbe.lean
lake env lean docs/research/probes/PredicateInterface.lean
lake env lean docs/research/probes/PredicateSomeAny.lean
```

All exited successfully. Guarded failures are intended negative evidence;
representative printed axiom lists contain only standard axioms. These are
direct checks using built imports, not a fresh project build or dependency
bootstrap. They certify their own reference-based representations only.

New scratch proofs separately test the direct representation over ordinary
Mathlib group actions and finite support. Their reproducible sources and exact
limits are recorded in the companion
[probe record](2026-10-05-predicate-design-probes.md). In particular, this tests
predicate action/support transport but does not prove least supports or Some/Any
for an arbitrary group. Those require the selected finite-permutation theory.

`python3 scripts/check-imports.py` passed for the unchanged reference roots.
Documentation links, diff checks and a hash comparison against the 91 initial
files are recorded in the package roadmap work log. No new Package target or
Package axiom audit was run: neither exists yet. No full reference-library
rebuild or external Isabelle/Rocq/Agda build was needed or claimed here.
