# Package foundation kernel

This contains F02, both F03 slices, and F04a/F04b of the new nominal package. It uses the pinned
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

Persistent usage examples are reserved for future case studies. This increment
contains the foundation modules and their audit, without a `Package/Examples`
layer. F04a supplies the finite support calculus and F04b supplies nominality
and least support. Canonical nominal instances/freshness and equivariant quotients
remain F04c/F04d. Supported-function and predicate interfaces, Some/Any, binders
and recursion are later work. Bare permutations retain left multiplication and
ordinary functions retain their pointwise action; neither receives an automatic
finite-supportedness or nominality claim.

## Verification

```sh
lake build Package +Package.Tests.AxiomAudit
lake env lean Package/Tests/AxiomAudit.lean
python3 Package/Scripts/check-imports.py
# Also run --self-test when changing the checker.
git diff --check
```

The public root imports all five foundation modules. The coverage script inventories
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
