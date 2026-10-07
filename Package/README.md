# Package foundation kernel

This contains F02, both F03 slices, F04a–F04d, and F05 of the new nominal package. It uses the pinned
Lean/Mathlib 4.34.1 and imports Mathlib directly. The reference `Nominal/` and
`Instances/` development remains separate.

```lean
import Package
open NominalPackage
open scoped Pointwise -- for the finite-set image action
```

`Perm A` is the subgroup of `Equiv.Perm A` with a finite moved-point set.
It supports ordinary application, group operations, coercion to `Equiv.Perm`,
`ext`, and directed computation lemmas. The group needs neither infinite atoms
nor decidable equality; `Perm.swap` takes `[DecidableEq A]`.

| Interface | Public declarations |
| --- | --- |
| Group/application | `Perm.ext`, `one_apply`, `mul_apply`, `inv_apply_apply`, `apply_inv_apply`, `toEquiv_*` |
| Moved points | `Perm.moved`, `moved_finite`, `moved_mul_subset`, `moved_inv`, `moved_conj` |
| Swaps | `Perm.swap`, `swap_apply_left/right`, `swap_apply_of_ne_of_ne`, `swap_self`, `swap_inv`, `swap_mul_self`, `conj_swap`, `moved_swap` |
| Controlled factorization | `Perm.swap_factorization`, `Perm.swap_factorization_avoiding` |
| Swap invariance criterion | `Perm.smul_eq_of_swap_smul_eq`, `Perm.forall_smul_eq_iff_swap_smul_eq` |
| Canonical atom action | `Perm.smul_atom`; inherited from Mathlib, with no competing atom instance |
| Products | Standard componentwise Mathlib action and projection equations |
| Finite atom sets | `Perm.smul_finset`, `Perm.mem_smul_finset`; requires the consumer's `Pointwise` scope and decidable equality |
| Explicit discrete data | `Discrete A X`, `Discrete.equiv`, `smul_mk`, `smul_val` |
| Ordinary equivariant maps | `Equivariant A f`, `Equivariant.id`, `.comp`, `.fst`, `.snd`, `.pair` |
| Finite support bounds | `Supports S x`, `supports_iff`, `supports_mono`, `supports_empty_iff` |
| Images and products | `supports_map`, `supports_prod_iff`, `supports_prod` |
| Support transport and swaps | `supports_smul`, `supports_smul_iff`, `supports_iff_swap`, `swap_smul_eq_of_supports` |
| Finite intersection | `supports_inter`, requiring infinite atoms |
| Individual finite supportedness | `FinitelySupported A x`, `Supports.finitelySupported`, `FinitelySupported.smul`, `.map`, `.prod`, `finitelySupported_smul_iff` |
| Proof-only nominality | `Nominal A X`, `Nominal.finitelySupported` for the selected action |
| Elementwise least support | `FinitelySupported.exists_least_support`, `.support`, `.supports_support`, `.support_minimal`, `.supports_iff_support_subset`, `.support_unique`, `.support_eq` |
| Elementwise support laws | `FinitelySupported.support_smul`, `.support_eq_empty_iff`, `.support_map_subset` |
| Nominal-carrier convenience | `support A x`, `support_eq`, `supports_support`, `support_minimal`, `supports_iff_support_subset`, `support_smul`, `support_eq_empty_iff`, `support_map_subset`; A explicit throughout |
| Canonical nominality | `instNominalAtom`, `instNominalDiscrete`, `instNominalProd`, scoped `instNominalFinset`; no infinitude premise |
| Canonical sufficient bounds | `supports_atom`, `supports_discrete`, `supports_finset` |
| Exact canonical support | `support_atom`, `support_discrete`, `support_prod`, `support_finset`, `FinitelySupported.support_prod` |
| General freshness | `Fresh A x y`, `hx.FreshWith hy`, `fresh_iff_disjoint_support`, `fresh_iff_freshWith` |
| Symmetry and products | `fresh_comm`, `fresh_self_iff`, `fresh_prod_left_iff`, `fresh_prod_right_iff`; elementwise `freshWith_*` counterparts |
| General bounds, transport and maps | `fresh_iff_exists_disjoint_supports`, `fresh_of_disjoint_supports`, `fresh_smul_both_iff`, `fresh_smul_right_iff`, `fresh_map_left/right`; elementwise counterparts |
| Atom specialization | `hx.Fresh a`, `Fresh A a x`, `fresh_iff_notMem_support`, `fresh_iff`, `fresh_atom_right_iff` |
| Freshness laws | Elementwise and carrier `fresh_of_supports`, `fresh_smul_iff`, `fresh_smul_iff_inv`, `swap_smul_eq_of_fresh`, `fresh_prod_iff` |
| Canonical freshness | `fresh_atom_iff`, `fresh_discrete`, `fresh_finset_iff` |
| Fresh existence | Elementwise and carrier `exists_fresh`, `exists_fresh_notMem`; explicit-set avoidance uses Mathlib's `Finset.exists_notMem` |
| Invariant quotient actions | `SMulInvariant`, explicit `QuotientAction.smul` / `.mulAction`, `.smul_mk`, `.mk_smul` |
| Canonical projection | `QuotientAction.mkHom`, `.mkHom_apply`, `.equivariant_mk`; Mathlib's `Quotient.mk_surjective` |
| Surjective nominality transfer | `Equivariant.nominal_of_surjective` for already selected actions |
| Quotient support | `QuotientAction.supports_mk`, `.finitelySupported_mk`, `.nominal`, `.support_mk_subset` |
| Exact supported-fiber support | `FinitelySupported.mem_support_map_iff`, `QuotientAction.support_eq_iInter` |

Atom and carrier universes are independent. `Discrete A X : Type v` retains the
universe of `X : Type v`. Its ordinary type equivalence to X does not identify
an independently chosen action on X. Bare permutation groups keep their usual
left-multiplication action; bare functions keep the pointwise codomain action.
Neither is silently changed to conjugation.

`Perm.swap_factorization π` provides a list `l : List (A × A)` with
`(l.map (fun p => Perm.swap p.1 p.2)).prod = π`. Every pair has distinct endpoints
in the **original** `π.moved`. The rightmost swap acts first; the empty list
represents identity. The witness is nonunique, with no chosen factorization algorithm.

For arbitrary `S : Set A`, `Perm.swap_factorization_avoiding π S hfix` gives
factors whose endpoints lie outside S when `hfix : ∀ a ∈ S, π a = a`.
For any selected `MulAction (Perm A) X`, `Perm.smul_eq_of_swap_smul_eq S x hswap π hfix`
then proves `π • x = x`, where `hswap` says every swap outside S fixes x.
`Perm.forall_smul_eq_iff_swap_smul_eq S x` gives the equivalence with invariance
under all permutations fixing S pointwise. Equal-endpoint swaps are harmless.
These four results require decidable equality for swaps but no infinitude,
countability, finite avoidance set, or nominality of X. Pointwise fixation of S
is essential; setwise preservation is a different condition.

`Supports S x`, for `S : Finset A`, abbreviates
`MulAction.Supports (Perm A) (S : Set A) x`. The pointwise-fixing condition is
available through `supports_iff`. `FinitelySupported A x` means that such a
finite bound exists for this element of the selected action; it stores no chosen
support as data and does not introduce a nominality class or another action.

| Support calculus | Atom assumptions |
| --- | --- |
| Definitions, monotonicity, empty-support invariance, equivariant images, common-bound product equivalence | None |
| All `FinitelySupported` closure laws | None; classical finite witnesses remain inside proofs |
| Union bounds, finite-set image transport, swap characterization and consequence | `DecidableEq A` |
| Binary intersection of finite bounds | `DecidableEq A`, `Infinite A` |

`supports_smul hS π` transports `Supports S x` to
`Supports (π • S) (π • x)` using conjugation, without a commuting-action
assumption. Open `Pointwise` to use the finite-set image notation. Use the named
Package theorem rather than Mathlib's similarly named `Supports.smul`, which
has a different commutation contract. `supports_iff_swap` specializes the
delivered F03b equivalence; no swap-generation proof is repeated.

`supports_prod_iff` characterizes a common supporting bound for a pair;
`supports_prod` combines separate bounds by union. Equivariant images preserve
sufficient bounds, which can be larger than necessary. There is no least-support
claim in these results. The infinitude requirement for general intersection
matters: under the canonical Bool action, both `{false}` and `{true}` support
`false`, whereas their empty intersection does not.

`Nominal A X : Prop` certifies `∀ x : X, FinitelySupported A x` for the
already selected action. It stores neither an action nor a chosen finite set,
uses no atom `outParam`, and needs neither infinitude nor decidable equality.

Under `[Infinite A]`, a certificate `hx : FinitelySupported A x` supplies the
noncomputable `hx.support : Finset A`. This supports x and is contained in every
finite supporting bound: `hx.support_minimal hS` proves containment in S, and
`hx.supports_iff_support_subset S` gives both directions. An independently proved
least candidate agrees by `hx.support_unique hS hmin`; different existence proofs
agree by `hx.support_eq hx'`. No nominality instance for the whole carrier is
required. The construction uses Mathlib's well-founded Finset order and F04a's
intersection theorem; it gives unsupported elements no default value.

With `[Nominal A X]`, use `support A x` and its carrier laws, for example
`supports_support A x`, `support_minimal A hS` and
`supports_iff_support_subset A x S`. This operation uses the class projection's
elementwise certificate and makes no second choice. `support_eq A x hx` proves
agreement with any supplied hx, so changing the nominality certificate for the
same action also leaves the result unchanged. Atom and carrier universes remain
independent, and explicit A selects the intended atom action.

The elementwise and carrier support/leastness/empty/image laws need `Infinite A`
but no `DecidableEq A`. The transport equations
`hx.support_smul π` and `support_smul A π x` additionally need decidable equality
and the consumer's `Pointwise` scope for the finite-set image action. Empty
least support is equivalent to universal permutation invariance. For an
equivariant f, `hx.support_map_subset hf` bounds the support of the certificate
`hx.map hf` without assuming either carrier nominal. The convenient
`support_map_subset A hf x` uses nominality of both carriers. These image bounds
are inclusions and can be strict.

Finite-atom nominality alone does not imply least support: a least bound for
false in the Bool example would lie in both singletons, hence be empty, which
is impossible. Least support is not strong support either: fixing an element
implies setwise preservation of its least support, not pointwise fixation of
the atoms in it.

The canonical actions on atoms, `Discrete A X`, products of nominal carriers,
and `Finset A` now have nominality certificates. None requires infinite atoms.
Discrete data needs no action or nominality on its underlying X. Products reuse
`FinitelySupported.prod` and need no decidable atom equality. The Finset
certificate is scoped with `Pointwise`, like its image action, and requires
`DecidableEq A`. These instances certify exactly the existing canonical actions;
they do not assert nominality for an arbitrary locally selected action on the
same type.

Under `[Infinite A]`, the exact formulas are:

```text
support A a = {a}
support A (Discrete.mk d : Discrete A X) = ∅
support A (x, y) = support A x ∪ support A y
support A (S : Finset A) = S
```

The atom/discrete equations need no decidable equality; the visible union and
Finset action retain it. `hx.support_prod hy` gives the product equation without
carrier-wide nominality. Both inclusions are proved. In particular swapping
distinct a,b fixes `{a,b}` but moves both members of its actual least support,
as identified by `support_finset`.

Following Pitts, `Fresh A x y` means
`Disjoint (support A x) (support A y)`. The two carriers and their universes
may differ; both use the same atom type and their selected actions. Use
`hx.FreshWith hy` for individually supported values without requiring either
carrier nominal. `fresh_iff_freshWith A x y hx hy` gives agreement for any
certificates of those values/actions. The definition and generic laws need
`Infinite A` but no `DecidableEq A`. No new notation or action is installed.

Freshness is symmetric (`fresh_comm`), and `fresh_self_iff` characterizes empty
support. `fresh_prod_left_iff` and `fresh_prod_right_iff` decompose products on
both sides, so a condition such as `Fresh A ((a,b),c) (d,e)` gives all six
pairwise conditions. `fresh_smul_both_iff A π x y` provides simultaneous
transport; `fresh_smul_right_iff` moves an action across the relation by its
inverse. Symmetry is not a global simp rule.

`fresh_iff_exists_disjoint_supports A x y` characterizes freshness by the
existence of disjoint sufficient finite bounds. Use `fresh_of_disjoint_supports`
to introduce it from two such bounds. The `fresh_map_left/right` laws preserve
freshness under ordinary equivariant maps, with no function-space action.
They are implications: an equivariant map can erase support. All these results
also have elementwise `FinitelySupported.freshWith_*` forms.

Atom freshness is a specialization using singleton atom support. Use
`hx.Fresh a` with explicit evidence or `Fresh A a x` on a nominal carrier;
`fresh_iff A a x hx` retains their agreement. Ordinary atom calls and theorem
names are retained; the fully explicit `@Fresh` signature now has both carrier,
action and nominality parameters.
`hx.fresh_of_supports hS ha` and `fresh_of_supports A hS ha` derive freshness
from `Supports S x` and `ha : a ∉ S`.

`hx.fresh_smul_iff π a` and `fresh_smul_iff A π a x` preserve and reflect
simultaneous renaming. The `_iff_inv` variants rewrite freshness for `π • x`
as freshness of `π⁻¹ a` for x. These statements need only infinitude; their
proofs keep classical equality local. With decidable equality,
`hx.swap_smul_eq_of_fresh ha hb` or `swap_smul_eq_of_fresh A ha hb` proves
swap fixation, including equal endpoints.

Canonical freshness reduces to inequality for atoms and nonmembership for
atom-versus-finite-set comparisons. `fresh_discrete_left/right` gives freshness
for arbitrary discrete data on either side. `fresh_finset_left_iff` and
`fresh_finset_right_iff` characterize `Fresh A S x` and `Fresh A x S` by
`∀ a ∈ S, Fresh A a x`; `fresh_finsets_iff` gives disjointness for two finite
atom sets. These Finset carrier laws keep decidable equality and Pointwise.
Carrier product freshness simplifies on either side; `fresh_prod_iff` remains
the atom-left adapter. For explicit certificates, specialize
`hx.freshWith_prod_left_iff hy hz`, `hx.freshWith_prod_right_iff hy hz`, or
the atom adapter `hx.fresh_prod_iff hy a` before rewriting:
generic simp cannot recover both certificates from proof-irrelevant product
evidence. This route requires neither carrier nominality nor decidable equality.

`hx.exists_fresh_notMem S` gives `∃ a, a ∉ S ∧ hx.Fresh a`;
`exists_fresh_notMem A S x` is the carrier adapter. Without an extra exclusion
set, use `hx.exists_fresh` or `exists_fresh A x`. None requires decidable equality.
Combine certificates using `.prod`, or supply a nested nominal context to the
carrier operation and decompose its freshness. A Finset used as a context
component still needs equality and Pointwise; an explicit finite exclusion bound
alone does not. These theorems construct witnesses in proofs and export no
executable, equivariant or finitely supported fresh-selector function.

An invariant setoid on an acted-on X gives an ordinary quotient with a canonical
action. `SMulInvariant M s` means
`∀ m ⦃x y⦄, s.r x y → s.r (m • x) (m • y)`. It is an ordinary proof argument,
not a class; s need not be an ambient setoid instance. `QuotientAction.smul s hs`
descends the selected scalar operation using Mathlib's `Quotient.map` and needs
only `[SMul M X]`. For `[Monoid M] [MulAction M X]`,
`QuotientAction.mulAction s hs` transfers the action laws along the surjective
projection. Neither constructor needs nominality, relation decidability,
inhabitance or any atom assumption. Both are computable and keep scalar/carrier
universes independent.

Install the action explicitly. For `s : Setoid X` and
`hs : SMulInvariant (Perm A) s`:

```lean
letI : MulAction (Perm A) (Quotient s) := QuotientAction.mulAction s hs
-- When the selected source action has [Nominal A X]:
letI : Nominal A (Quotient s) := QuotientAction.nominal A s hs
```

Neither import nor compatibility evidence alone installs an action or quotient
nominality instance. The projection computation laws are
`QuotientAction.smul_mk s hs π x` and its reverse `.mk_smul`; only the first
is a simp rule. `mkHom` packages the same ordinary projection in Mathlib's
`MulActionHom`, with a computation lemma for application. For permutation
actions, `.equivariant_mk A s hs` gives `Equivariant A (Quotient.mk s)`.
Surjectivity is the existing `Quotient.mk_surjective (s := s)`. All action-dependent
contracts fix the constructed action; they do not certify an unrelated action
on the same quotient carrier.

The two sufficient-support adapters preserve any supplied bound or individual
certificate by the existing map laws. The general theorem
`hf.nominal_of_surjective hsurj` transfers nominality to an already selected
codomain action, with no infinitude, equality or nonempty-carrier hypothesis.
Quotient nominality specializes it to the projection.
Under `[Infinite A]`, `QuotientAction.support_mk_subset A s hs x` gives the
carrier inclusion. Without source nominality, install only the canonical action
and use `hx.support_map_subset (QuotientAction.equivariant_mk A s hs)`; the image
certificate is `hx.map` of that equivariance proof. Support agreement permits
independently supplied image evidence. The general freshness-map laws likewise
apply directly in either argument, including `.freshWith_map_left/right` on
individual certificates; no quotient-specific freshness theory is needed.

For an ordinary equivariant f and one supported x, the stronger theorem says:

```text
a ∈ (hx.map hf).support ↔
  ∀ z (hz : FinitelySupported A z), f z = f x → a ∈ hz.support
```

`hx.mem_support_map_iff hf a` needs Infinite A but neither whole carrier nominal,
surjectivity nor decidable equality. It considers only supported preimages.
For a nominal X, `QuotientAction.support_eq_iInter A s hs c` identifies
`(support A c : Set A)` with the intersection of `support A x` over the subtype
`{x : X // Quotient.mk s x = c}`. This is a Set intersection, not a new Finset
operation. The result does not provide a representative attaining class support:
over infinite atoms, the universal quotient has empty support while every representative
has singleton support. The quotient of atom pairs that forgets the second
component has support `{a}` at the class of `(a,b)`, strictly smaller than
`{a,b}` when the atoms differ. Surjective equivariant maps can lose support and
increase freshness; they do not reflect supportedness of arbitrary representatives.
Predicate pullback/support reflection is a separate later interface.

Persistent usage examples are reserved for future case studies. This increment
contains the foundation modules and their audit, without a `Package/Examples`
layer. F04a supplies the finite support calculus and F04b supplies nominality
and least support. F04c supplies canonical instances and freshness; F04d supplies
canonical equivariant quotients and their support characterization.
Full predicate logic, Some/Any, predicate quotient descent, binders
and recursion are later work. Function objects, supported maps and predicate
inputs are described below. Bare permutations retain left multiplication and
ordinary functions retain their pointwise action; neither receives an automatic
finite-supportedness or nominality claim.

## Functions and predicate inputs

Ordinary mathematical definitions use `X → Y` and `X → Prop`. `SupportsMap S f`
means that f commutes with permutations fixing S; `FinitelySupportedMap A f`
asserts existence of such a finite bound. This is conjugation support, not
`FinitelySupported A f` under the ordinary pointwise arrow action. Identity
has empty map support, although pointwise action can move the ordinary identity.
The finite-map certificate is a reducible existential alias, so `simp` also
accepts literal witnesses passed to `SupportedMap.ofFun`.

`FunctionObject G X Y` contains every ordinary map and has full conjugation
`(g • F) x = g • F (g⁻¹ • x)`. It retains `Type (max uX uY)` independently
of G. Its action uses DivisionMonoid, and cancellation/evaluation use Group.
Full curry/uncurry and their inverse laws have no finite-support or nonempty
premises. General sufficient bounds use Mathlib's `MulAction.Supports`;
`ActionSupport.supports_map_iff` reflects them through equivariant injections,
and `.supports_smul_iff` transports them by the same group without requiring
commuting actions. These arbitrary-set laws do not extend finite least-support
minimality to infinite supporting sets.

`supportsMap_iff` connects ordinary certificates to `FunctionObject.ofFun (Perm A)`.
`hf.toObject` converts finite map evidence to the delivered elementwise evidence,
so `hf.toObject.support` and `.FreshWith` reuse the existing theory. Evaluation,
composition, pairing and parameter fixing have sufficient/least-support bounds.
Pairing and full curry/uncurry preserve the stated exact support; composition
and evaluation only give inclusions. `Equivariant.toMulActionHom` and
`equivariant_coe_mulActionHom` bridge the existing Mathlib bundle.

`SupportedMap A X Y` stores a full object and finite support in a proof field.
It is nominal without requiring X or Y nominal. Use `ofFun`, `ofSupports`,
`ofEquivariant`, or `fromParam` with explicit evidence. FunLike provides ordinary
application, higher-order arguments, `rw` and `ext`; `toObject` is a named
projection, not a competing coercion. Different support proofs give the same
function value. Constants, identity, composition, pairing and evaluation have
application/coercion simp lemmas. Computable bodies remain computable when
classical support witnesses stay in proofs.

```lean
section FunctionInputs
variable {A P X Y : Type*}
variable [MulAction (Perm A) P] [MulAction (Perm A) X] [MulAction (Perm A) Y]

example (E : P × X → Y) (hE : Equivariant A E)
    (p : P) (hp : FinitelySupported A p) :
    FinitelySupportedMap A (fun x => E (p,x)) :=
  hE.finitelySupportedMap_section hp

example (E : P × X → Y) (hE : Equivariant A E)
    (p : P) (hp : FinitelySupported A p) (x : X) :
    SupportedMap.fromParam E hE p hp x = E (p,x) := by simp

example (f : X → Y) (hf : FinitelySupportedMap A f) (xs : List X) :
    xs.map (SupportedMap.ofFun A f hf) = xs.map f := by simp
end FunctionInputs
```

A nested tuple of captures with individually certified bounds gives a context
bound by products and `SupportsMap.section`; a jointly equivariant operation
needs only the context's bound. Extra supplied values/atoms can enlarge that
bound by monotonicity. This proves sufficient support without selecting a least
support. The package supplies these proof constructors, not a context scanner
or automatic support for arbitrary globals. Atom/action selection and support
inference are separate: use explicit A/G when the surrounding type cannot
select them.

For `F : SupportedMap A (X × Y) Z`, `F.curryAt x hx` needs support of this x.
`F.curryWithSections hs` instead accepts `hs : F.SectionsSupported`, the exact
condition that every section is supported. `F.curry` is the convenience form
under `Nominal A X`; Y and Z need only actions. `H.uncurry` is unconditional.
The admissible-subset equivalence works without nominality of X, and all these
curry/uncurry correspondences preserve exact least support. A supported binary
projection can have an unsupported section at an unsupported parameter, so
unconditional bundled curry is not available.

An empty-domain function is always supported: `SupportedMap.ofIsEmpty A f`
requires no support for codomain values. `supportsMap_const_iff`,
`finitelySupportedMap_const_iff`, `SupportedMap.support_const` and `.const_inj`
use Nonempty for reflection/exactness. `FunctionObject.const_injective_iff`
also records the subsingleton-codomain exception.

`SupportsPred S P` uses ordinary logical equivalence; no global Prop action is
needed. `predicateObject A P` maps into `Discrete A Prop`, with both support
and ordinary-type correspondences. `supportsPred_iff_set` uses the existing
Pointwise-scoped Set image action. Renaming, precomposition and fixed-parameter
bounds have explicit and existential forms. Equality with a supported value
has exactly its support. An unsupported predicate is still an ordinary Lean
predicate and a legal motive; only support-sensitive uses require evidence.
No supported-predicate logic bundle, Some/Any or predicate pullback/descent API
is supplied by this input layer.

## Verification

```sh
lake build Package +Package.Tests.AxiomAudit
lake env lean Package/Tests/AxiomAudit.lean
python3 Package/Scripts/check-imports.py
# Also run --self-test when changing the checker.
git diff --check
```

The public root imports all delivered foundation modules. The coverage script inventories
all Package Lean sources and checks the separate production and audit closures.
It rejects unclassified sources, missing local imports, production-to-audit
imports and reference-library dependencies. Its header parser is pinned Lean's
`--deps-json`; per-file errors are checked even when the process exits zero.
Header discovery does not replace full Lean compilation or validate body syntax.
The checker self-tests use temporary source trees outside the repository.

The audit traverses production declarations by their originating module, including
private names, and checks transitive axiom dependencies. It fails on zero
production declarations or any axiom beyond `propext`, `Classical.choice` and
`Quot.sound`. Its rejection tests use simulated names, never new axiom declarations.
Run the direct audit command when Lake reports its compiled module is cached.

The default Lake targets and old validation scripts still cover the reference
library only. `lake build Nominal Instances Examples`, its direct axiom audit,
and `python3 scripts/check-imports.py` check reference preservation separately.
The old fresh-build helper does not copy Package and cannot certify a fresh
Package build. Report cache/rebuild conditions for commands actually run.

The accompanying [LaTeX article](../docs/article/main.tex) describes the mathematics
and its implementation. Compile it from `docs/article` with:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir=/tmp/nominal-package-article-build main.tex
```

Create that output directory if necessary. Keep generated manuscript files out
of the source tree. Task status and evidence live in the
[package roadmap](../docs/nominal-package-roadmap.md).
