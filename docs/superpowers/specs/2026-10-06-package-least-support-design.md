# F04b: nominality and least support

Date: 2026-10-06. **Written specification approved by the author.**
Task: **PKG-F04, slice F04b**, with concurrent article work under **PKG-11**.
The [package roadmap](../../nominal-package-roadmap.md) owns status and the
F04a–F04d boundaries. The author approved this specification on 2026-10-06.
Its [native implementation plan](../plans/2026-10-06-package-least-support.md)
was approved for native execution. All 19 public declarations and their temporary
consumers now check, with matching compiled LaTeX. Independent final review found
no Critical, Important or Minor issues. F04b is delivered, uncommitted.

## Intended outcome and constraints

Give clients canonical least finite support for an individually finitely
supported element of an already selected `MulAction (Perm A) X`. Add a proof-only
certificate that every element of a carrier is finitely supported, and a
convenient least-support operation using that certificate. The elementwise
interface remains primary: neither its construction nor its laws require
carrier-wide nominality.

Reuse the delivered F04a interface exactly: `Supports S x` abbreviates Mathlib's
`MulAction.Supports (Perm A) (S : Set A) x`, and `FinitelySupported A x` asserts
existence of a finite supporting bound. Reuse `supports_inter`, support transport,
equivariant-image bounds and existential closure. No swap characterization,
factorization, conjugation transport or intersection proof is repeated.

Preserve namespace `NominalPackage`, `Perm A`, independent atom/carrier universes,
all selected actions and scoped finite-set images. New implementation belongs
under `Package/`, with direct pinned Mathlib dependencies. The reference
`Nominal/` and `Instances/` are preserved and are not implementation dependencies.
The historical `docs/roadmap.md` is unchanged. No branch switch, commit, push,
publication, merge, dependency upgrade or CI change is authorized.

This is one bounded interface increment, using the architectural review path.
The supplied scope authorizes writing this specification; agreement on it
authorizes preparation of the implementation plan, not production changes.
Earlier F02/F03a/F03b/F04a approvals and deliveries stand.

## Inspected state and verification limits

The actual checkout is `/home/fab/Documents/nominal/nominal`, branch
`fasapa/nominal-package`, HEAD
`34a83358739ab962e2b9d2035a21d67b2a896071`. History confirms that HEAD contains
F03b, following the F02/F03a commit `3d2196a`. F04a is existing uncommitted work,
including untracked `Package/Foundations/Support.lean`, its specification and
plan, and the article's `support.tex`. The later editorial work, including
untracked `perspectives.tex`, is also preserved. Untracked files are part of
the baseline, not disposable experiments.

Read inputs include AGENTS.md, both READMEs, the public root, all four foundation
modules, the axiom audit and import checker, the active roadmap, research guide,
readiness and article-plan notes, the delivered F04a spec/plan, and the article
entry point and all four included sections. The research brief and predicate
note were consulted for downstream constraints, without reopening their earlier
architectural proposals or overriding F04a's actual definitions.

Lean is pinned to `v4.34.1`; both the manifest and installed Mathlib checkout
identify `d13f23b723b8a846827a245b89c10fc7d3f11612` (`v4.34.1`). The minimum,
cardinality, finite-intersection and order APIs below were inspected at that
revision. A temporary file containing only imports, `#check` and `#synth`
commands also confirmed their exact types and the assumption-free Finset order
instances. It defines no new F04b operation or theorem.

Fresh design-session baseline commands, distinct from the supplied delivery
history:

- `lake build Package +Package.Tests.AxiomAudit`: passed, 969 jobs, using cached
  project/dependency artifacts and replaying the compiled audit output.
- `lake env lean Package/Tests/AxiomAudit.lean`: direct audit passed,
  104 production declarations from four defining modules; only `propext`,
  `Classical.choice` and `Quot.sound`.
- `python3 Package/Scripts/check-imports.py`: five production source modules
  including the root, and one audit module, all reached. The checker is unchanged.
- Direct checks of the retained F04a `IntersectionContracts.lean` and F03a
  `ActionContracts.lean` passed. These certify their existing conclusions.
- The documented `latexmk` command rebuilt the current manuscript in the
  existing `/tmp/nominal-package-article-build` directory. It has **12 pages**;
  the final log has no warning, unresolved reference or box diagnostic. This is
  the later edited article, not the historical 26-page F04a delivery version.
- `git diff --check` passed before this specification/tracker edit.

The baseline hashes for 114 tracked/untracked files and the API inventory are
under `/tmp/nominal-f04b-design-yo48zzie/`. No fresh whole-project build,
dependency bootstrap, reference-library rebuild or F04b proof validation is
claimed by those baseline checks. The approved contracts below have subsequently
been implemented and checked; execution evidence is recorded at the end of this
specification and in the active roadmap.

## Construction alternatives and recommendation

**Approved choice: an inclusion-minimal supporting set using Mathlib's existing
well-founded Finset order.** Binary support intersection turns that minimal
element into a least element. This avoids choosing an initial bound as data,
introducing a cardinality argument into the Package proof, or building a family
of intersections. It uses the same finite-descent idea as cardinality minimization.

| Construction | Proof and tradeoff |
| --- | --- |
| Inclusion-minimal supporting bound — approved | `Finset.wellFoundedLT` and `exists_minimal_of_wellFoundedLT` select a minimal support from `hx`. For every support T, `supports_inter` supplies a support inside the selected S; `Minimal.le_of_le` gives `S ⊆ S ∩ T ⊆ T`. The needed order infrastructure already exists. |
| Minimum-cardinality supporting bound | Apply `exists_minimalFor_of_wellFoundedLT` to `Finset.card`. The selected S satisfies `S.card ≤ (S ∩ T).card`; `Finset.eq_of_subset_of_card_le` yields `S ∩ T = S`, hence `S ⊆ T`. Sound and short, but includes an unnecessary cardinality comparison once the Finset order API is available. |
| Finite intersections within a supplied bound B | Form the nonempty family of supporting subsets in `B.powerset` and take its `Finset.inf'` intersection, or fold intersections starting at B. Prove support by finite induction using `supports_inter`. For arbitrary support T, `B ∩ T` is a member of the family, giving containment in T. This also works, but needs filtering, nonemptiness/fold bookkeeping and removal of apparent dependence on B. |

The third construction uses only a finite family. None of these arguments
assumes closure under arbitrary intersections. Inclusion-minimality alone is
not leastness: the intersection step is indispensable, and is precisely where
`Infinite A` enters the chosen proof.

Pinned source inventory (paths relative to `.lake/packages/mathlib/Mathlib/`):

| Declaration and source | Fit for this increment |
| --- | --- |
| `Finset.wellFoundedLT`, `Data/Finset/Defs.lean:292` | Well-founded strict inclusion for finite sets, with no `DecidableEq A` or `Infinite A`; the ordinary partial order is already available. |
| `exists_minimal_of_wellFoundedLT`, `Order/Minimal.lean:226` | For a nonempty predicate on a preorder with well-founded `<`, produces a `Minimal` witness. Use the predicate `fun S : Finset A => Supports S x`. |
| `Minimal.prop`, `Minimal.le_of_le`, `Order/Defs/Unbundled.lean:231–239` | Extract support and show the selected bound lies below a supporting intersection. These do not assume a linear order. |
| `exists_minimalFor_of_wellFoundedLT`, `Order/Minimal.lean:221`; `MinimalFor.le`, same file:291 | Available alternative for minimization of a Nat-valued cardinality. `MinimalFor.le` needs the linear order on Nat, not a linear order on Finset. |
| `Finset.card`, `card_le_card`, `eq_of_subset_of_card_le`, `Data/Finset/Card.lean:46,65,285` | The cardinality alternative needs no new general minimum theorem. |
| `Finset.inter_subset_left/right`, `inter_eq_left`, `Data/Finset/Lattice/Basic.lean:209–210,306` | Standard finite-intersection containments and equality/subset conversion. Public intersection syntax needs decidable equality. |
| `Finset.powerset`, `mem_powerset`, `Data/Finset/Powerset.lean:33–40`; `Finset.inf'`, `Data/Finset/Lattice/Fold.lean:529–565` | Supply the finite-family alternative; no powerset/fold import is needed for the recommended construction. |
| `DirectedOn.minimal_iff_isLeast`, `Order/Bounds/Basic.lean:740`; `IsLeast.unique`, same file:817 | Express the general order argument. A direct specialization using `Minimal.le_of_le` and intersection is smaller than packaging directedness; uniqueness is ordinary subset antisymmetry. No new generic order theorem or least-support predicate is needed. |

The Package-specific step is supplying support closure under intersection from
F04a. Mathlib supplies the minimum/order machinery. The selected approach needs
no new classical search procedure or enumeration of atoms or supports.

## Exact approved public interface

All declarations are in `NominalPackage`. Each block specifies its own variable
context; `u`, `v` and `w` are independent. Actions are always parameters already
selected by `MulAction`, never fields of the nominality certificate.

### Proof-only nominality, without atom assumptions

```lean
universe u v

class Nominal (A : Type u) (X : Type v) [MulAction (Perm A) X] : Prop where
  finitelySupported : ∀ x : X, FinitelySupported A x
```

Neither parameter is an `outParam`. The certificate introduces no action,
operation, chosen bound, equality decision or infinitude premise. Its projection
is used as `Nominal.finitelySupported (A := A) x`. Ordinary construction from a
proof of `∀ x, FinitelySupported A x` suffices; no additional constructor layer
or automatic canonical nominal instance belongs here.

### Elementwise least support

```lean
universe u v w
variable {A : Type u} {X : Type v}
variable [MulAction (Perm A) X] [Infinite A]
variable {x : X} {S : Finset A}

theorem FinitelySupported.exists_least_support (hx : FinitelySupported A x) :
    ∃! S : Finset A, Supports S x ∧
      ∀ T : Finset A, Supports T x → S ⊆ T

noncomputable def FinitelySupported.support (hx : FinitelySupported A x) :
    Finset A

theorem FinitelySupported.supports_support (hx : FinitelySupported A x) :
    Supports hx.support x

theorem FinitelySupported.support_minimal (hx : FinitelySupported A x)
    (hS : Supports S x) : hx.support ⊆ S

theorem FinitelySupported.supports_iff_support_subset
    (hx : FinitelySupported A x) (S : Finset A) :
    Supports S x ↔ hx.support ⊆ S

theorem FinitelySupported.support_unique (hx : FinitelySupported A x)
    (hS : Supports S x)
    (hmin : ∀ T : Finset A, Supports T x → S ⊆ T) :
    hx.support = S

theorem FinitelySupported.support_eq
    (hx hx' : FinitelySupported A x) : hx.support = hx'.support

theorem FinitelySupported.support_eq_empty_iff (hx : FinitelySupported A x) :
    hx.support = ∅ ↔ ∀ π : Perm A, π • x = x

variable {Y : Type w} [MulAction (Perm A) Y] {f : X → Y}

theorem FinitelySupported.support_map_subset (hx : FinitelySupported A x)
    (hf : Equivariant A f) : (hx.map hf).support ⊆ hx.support
```

The atom type and element are implicit in these methods because `hx` determines
them; clients may still write `(A := A)` explicitly. The operation is used as
`hx.support`, without constructing a nominal carrier or a subtype of supported
elements. Existential choice selects the least bound proved by the existence
theorem. Unsupported elements do not have an application of this operation;
there is no default empty branch and no unrestricted support law.

For finite-set image syntax, add decidable equality and explicitly open the
existing scope:

```lean
universe u v
variable {A : Type u} {X : Type v}
variable [MulAction (Perm A) X] [Infinite A] [DecidableEq A]
variable {x : X}
open scoped Pointwise

theorem FinitelySupported.support_smul (hx : FinitelySupported A x)
    (π : Perm A) : (hx.smul π).support = π • hx.support
```

The certificates `hx.map hf` and `hx.smul π` are delivered F04a proofs.
The image theorem assumes neither `[Nominal A X]` nor `[Nominal A Y]`.
Transport has no commuting-action hypothesis. A separately supplied certificate
for the image or renamed element gives the same result by `support_eq`.

### Convenient interface for nominal carriers

Here **A is explicit in every declaration**, including theorems. This makes
atom selection predictable for `support A x` even when X carries actions from
different atom types in the same context.

```lean
universe u v w
variable (A : Type u) {X : Type v}
variable [MulAction (Perm A) X] [Infinite A] [Nominal A X]

noncomputable def support (x : X) : Finset A

theorem support_eq (x : X) (hx : FinitelySupported A x) :
    support A x = hx.support

theorem supports_support (x : X) : Supports (support A x) x

theorem support_minimal {x : X} {S : Finset A} (hS : Supports S x) :
    support A x ⊆ S

theorem supports_iff_support_subset (x : X) (S : Finset A) :
    Supports S x ↔ support A x ⊆ S

theorem support_eq_empty_iff (x : X) :
    support A x = ∅ ↔ ∀ π : Perm A, π • x = x

variable {Y : Type w} [MulAction (Perm A) Y] [Nominal A Y] {f : X → Y}

theorem support_map_subset (hf : Equivariant A f) (x : X) :
    support A (f x) ⊆ support A x

variable [DecidableEq A]
open scoped Pointwise

theorem support_smul (π : Perm A) (x : X) :
    support A (π • x) = π • support A x
```

The defining expression for `support A x` is
`(Nominal.finitelySupported (A := A) x).support`. It makes no second choice.
The image wrapper needs nominality of both carriers because both sides use the
carrier operation. Its elementwise counterpart above retains the weaker,
mathematically sufficient assumptions. A mixed client with only X nominal can
apply the elementwise theorem to its nominality projection and use `support_eq`.

No carrier theorem re-proves the least-support construction: these are thin
applications of the elementwise laws and agreement theorem. No additional
global simp attributes are required. In particular, do not globally unfold
the choice, nominality or quantified support predicates during simplification.

### Witness and certificate independence

`FinitelySupported.support_eq` covers any two proofs of support existence for
the same x and selected action, including `⟨S,hS⟩` and `⟨T,hT⟩` with different
finite bounds. Proof irrelevance makes this equality immediate; uniqueness
also characterizes the chosen result independently of the construction.
`support_unique` equates the chosen set with any independently established
least supporting set, not merely another invocation of the same selector.

`support_eq A x hx` holds for any carrier certificate and any `hx`. Thus two
certificates `n₁ n₂ : @Nominal A X act` give equal values of the explicitly
instantiated carrier operation:

```lean
@support A X act inf n₁ x = @support A X act inf n₂ x
```

Here `act : MulAction (Perm A) X` and `inf : Infinite A` are fixed, and the
implicit/instance binder order of `support` is A, X, act, inf, nominality, x,
as specified above. Check this equality in a temporary consumer. A separate
public certificate-comparison theorem would duplicate the agreement theorem
and proof irrelevance. No equality between supports for different actions is
asserted.

### Assumption separation

| Interface | Atom assumptions | Support evidence |
| --- | --- | --- |
| `Nominal A X` and its projection | None | A proof for every x; no data field |
| Elementwise least-support existence, choice, support/minimality/uniqueness, empty characterization and image inclusion | `Infinite A` | Explicit `hx`; image evidence derived by `.map` |
| Elementwise transport equation | `Infinite A`, `DecidableEq A`; scoped `Pointwise` | Explicit `hx`; renamed evidence derived by `.smul` |
| Carrier choice, agreement, support/minimality and empty characterization | `Infinite A` | `[Nominal A X]`; agreement additionally takes `hx` |
| Carrier image inclusion | `Infinite A` | `[Nominal A X]`, `[Nominal A Y]`, equivariance |
| Carrier transport equation | `Infinite A`, `DecidableEq A`; scoped `Pointwise` | `[Nominal A X]` |

Use local classical equality in the existence proof's intersection step.
It must not become a parameter of existence, choice or nominality. The public
transport equation retains it because the finite-set image action requires it.
There is no countability, nonemptiness or carrier-universe identification.

## Proof strategy and mathematical boundaries

From `hx`, obtain S with `Minimal (fun S : Finset A => Supports S x) S`
using the pinned well-founded-order theorem. Its first component says that S
supports x. For any support T, the delivered `supports_inter` gives support by
`S ∩ T`. Since `S ∩ T ⊆ S`, `Minimal.le_of_le` yields `S ⊆ S ∩ T`, and hence
`S ⊆ T`. Two bounds with this property contain each other, so antisymmetry
proves uniqueness. Classical choice on this existence theorem defines
`hx.support`; `choose_spec` supplies its support and minimality properties.
The public iff combines minimality with F04a's `supports_mono`.

Transport is a uniqueness/minimality consequence of the existing
`supports_smul`: `π • hx.support` supports `π • x`. Conversely, transport any
support of `π • x` back by `π⁻¹`, use leastness for x, and take its image by π.
The inverse-action laws cancel the two images. This gives equality, including
the reverse containment, without repeating the conjugation argument.

The empty characterization combines leastness with `supports_empty_iff`:
an invariant element has the empty supporting bound, and the least bound can
equal empty only if it supports that invariant element. Equivariant images
inherit `hx.support` by `supports_map`; leastness of the image gives inclusion.
The inclusion can be strict, for example for a constant map to discrete data.

Nominality itself is meaningful for finite atom types. Under the canonical
Bool action every atom has a singleton supporting bound, so a local
`Nominal Bool Bool` certificate exists. Nevertheless false has two disjoint
singleton supports and no empty support. Any least bound would lie in both
singletons and hence be empty, a contradiction. Thus individual finite
supportedness and even carrier-wide nominality do not imply general least
support without an atom hypothesis. This extends the existing F04a boundary
evidence, without promising that every finite atom carrier fails.

Least support is not strong support. The support law says that pointwise
fixation of the support fixes x; its converse is not asserted. If π fixes x,
transport implies only setwise preservation of its least support. A permutation
may permute those atoms. The canonical unordered-pair counterexample and exact
Finset support formula remain F04c's responsibility.

## Modules, imports and exclusions

Add **one** production module, `Package/Foundations/Nominal.lean`, importing:

```lean
import Package.Foundations.Support
import Mathlib.Order.Minimal
```

The existing dependency chain becomes
`Permutation → SwapFactorization → Action → Support → Nominal`.
The class appears before the least-support section; place `[Infinite A]` only
on the latter declarations, and `[DecidableEq A]` only on transport statements.
The elementwise results and carrier wrappers share this small module. There
is no cycle through future nominal instances or freshness.

| File | Work during approved implementation |
| --- | --- |
| `Package/Foundations/Nominal.lean` | Proof-only class, unique least-support existence, elementwise operation/laws and carrier adapters |
| `Package.lean` | Explicitly export the new module |
| `Package/Tests/AxiomAudit.lean` | Representative prints for existence, leastness, transport, empty support, image inclusion and agreement; retain whole-production traversal |
| `Package/README.md` | Public calls, atom assumptions, certificate independence and remaining boundaries |
| `docs/article/sections/support.tex` | Add `sec:least-support` alongside the Lean work |
| `docs/article/main.tex`, `sections/introduction.tex` | Reconcile abstract and mathematical scope/cross-references |
| `docs/article/sections/perspectives.tex` | Reconcile the existing support-witness comparison where the new section changes its explanation |
| Active roadmap, this spec, eventual plan and relevant research guides | Record approved scope, actual declarations, commands, limits and final delivery evidence |

The audit and checker already classify `Package.Foundations.*` as production.
Expected source coverage becomes six production modules including the root
and one audit module; the new module must be reached by both closures. Record
the actual declaration count. No checker, Lake, dependency, reference-source or
shared validation-script change is expected. F04a's source remains intact.

F04c owns canonical nominal instances and exact atom/discrete/product/Finset
formulas, freshness and fresh-atom existence. F04d owns canonical quotient
actions and quotient bounds. F05/PKG-01 own supported functions, map/predicate
certificates, bundles and Some/Any. Abstraction, FCB, recursion and generators
remain later work. Temporary local nominal certificates and explicit bounds
are permitted in acceptance consumers, without exporting these later APIs.

## Concurrent article obligation

Extend `docs/article/sections/support.tex` with a subsection labelled
`sec:least-support`, retaining the existing finite-support exposition. Develop
its mathematics alongside the Lean proofs, then reconcile the final names,
assumptions and proof routes. It should explain:

1. Nominality as the assertion that all elements of a selected action have
   finite support; its proof-only Lean certificate does not select an action.
2. Unique least finite support for one supported element over infinite atoms,
   with the inclusion-minimum/intersection proof and a brief explanation of
   the cardinality alternative. Attribute the order infrastructure to Mathlib
   and reuse the existing intersection proposition by reference.
3. The noncomputable choice and the supporting/minimality characterization.
   Explain elementwise use, the carrier convenience and independence from
   supplied witnesses/certificates; classical choice is not a support algorithm.
4. Transport, empty support and equivariant-image inclusion, with their proof
   ideas. Explain why the last result can be strict.
5. The distinct roles of finite supportedness and infinitude, the Bool
   obstruction to leastness, and the distinction from strong support.

Select declaration references that clarify this account rather than listing
every wrapper. Update introduction/abstract and the existing witness discussion
as needed. The current [publication policy](../../research/2026-10-05-article-plan.md#publication-content-policy)
keeps task IDs, status/approval narratives, audit counts, build commands,
cache conditions and review verdicts outside the article. Reconcile proof
status and verification limits in the roadmap/spec/plan, and keep manuscript
claims within checked mathematics. No new scholarly comparison or external
source investigation is needed for this increment.

## Meaningful acceptance and completion

Temporary consumers import **only `Package`**, under a fresh directory outside
the source tree. No standalone `Package/Examples` layer is added. They must use
the new conclusions, not merely elaborate names or prove `True` after a call.
In addition to exact public-signature checks, require:

| Consumer | Required conclusion or boundary |
| --- | --- |
| Universe and action selection | Generic A/X/Y in independent universes; explicit `support A x` and `support B x` in a context with separately selected atom actions/certificates. No `outParam` or universe collapse. |
| Nominality without infinitude | Construct a local canonical `Nominal Bool Bool` using singleton bounds and consume its projection. Certificate construction needs no `Infinite Bool`. |
| Individually supported elements | Obtain and use `hx.support` in an arbitrary selected action without any nominality instance. Include a constant function `A → A` under the existing pointwise action with explicit singleton support. |
| A non-nominal carrier | On `A = Nat`, prove the pointwise identity function has no finite supporting bound: for each finite S, swap two distinct atoms outside S and evaluate at one of them. Together with the supported constant function this witnesses supported elements inside a carrier that is not nominal. No production instance or function-space API is added. |
| Leastness against arbitrary finite bounds | From arbitrary `hS : Supports S x`, obtain `hx.support ⊆ S`. Conversely, from that inclusion derive `Supports S x` and use it to show a permutation fixing S fixes x. Also use `support_unique` on an independently supplied least candidate. |
| Certificate independence and agreement | Compare two existential proofs built from different bounds; compare `hx.support` with `support A x`; compare explicitly supplied `n₁,n₂` for the same action. No unfolding of classical choice in client proofs. |
| Transport and inverse | Consume the forward equality and derive `π⁻¹ • (hx.smul π).support = hx.support`. Repeat with an independently supplied certificate of the renamed element and with the carrier wrapper. Keep Pointwise scoped. |
| Empty support | Use both directions of the elementwise and carrier equivalences, deriving actual invariance or equality to empty. The finite-supportedness premise remains explicit where no nominality instance is present. |
| Image bounds and strictness | For arbitrary equivariant f, derive membership of an atom in the source support from membership in the image support, without nominality of Y. Also consume `support_map_subset A hf x` with local certificates for both carriers. A constant map from Nat atoms to `Discrete Nat Bool` has empty image support while the chosen source atom has nonempty support, proved using a moving swap rather than a deferred exact atom formula. |
| Finite-atom leastness failure | Retain both supporting Bool singletons and failure of empty support, then refute existence of any least finite support of false. A failed search for `Infinite Bool` alone is insufficient. |
| Action coherence | Recheck atom application, componentwise products, scoped finite-set image, discrete fixation, left multiplication on bare Perm and pointwise action on bare functions. Use the retained F03a consumers when equivalent. |

Compile the affected module while iterating, then all supported Package
dependents. Assign every new public declaration its exact proposed type in a
temporary signature consumer; definitions and certificate/existence/choice laws
must not silently acquire equality or carrier-wide assumptions. Inspect
representative `#print axioms` and retain the audit's module-origin traversal
including private/generated declarations. Only `propext`, `Classical.choice`
and `Quot.sound` are allowed; no admissions, custom axioms or disabled kernel
checking. Do not weaken a mathematical contract to repair elaboration.

Required final commands, in addition to affected-module and consumer checks:

```sh
lake build Package +Package.Tests.AxiomAudit
lake env lean Package/Tests/AxiomAudit.lean
python3 Package/Scripts/check-imports.py
git diff --check
```

Run checker self-tests if the checker changes. From `docs/article/`, run:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error \
  -outdir=/tmp/nominal-package-article-build main.tex
```

Keep generated files outside the source tree; inspect final diagnostics and
mathematical correspondence as well as PDF compilation. Check links/content,
untracked-file whitespace and preservation against the initial snapshot.
Reinspect status before edits to preserve subsequent work too. Shared integration
changes affecting reference targets require separate reference verification;
otherwise report their source preservation without claiming a rebuild.
Record commands actually run and distinguish cached builds, fresh project
builds with cached dependencies and clean dependency bootstraps.

After native implementation and integrated validation, obtain **one fresh
independent final review** covering mathematical statements, proof assumptions,
interfaces, consumers, action coherence, article correspondence and preservation.
Resolve findings and rerun affected checks. Mark F04b complete only after code,
consumers, audit, article and final review pass. Keep PKG-F04 open for F04c/F04d.

## Review handoff

Self-review checked the exact atom/evidence arguments, theorem strength,
assumption separation, witness independence, finite-atom obstruction, imports,
phase exclusions and article/consumer obligations. The design stage checked the
existing minimum APIs without implementing the proposed declarations; the
subsequent approved execution now checks all 19 contracts. There were no
deferred mathematical choices. At the design handoff, document checks passed
for this specification and the active roadmap: 50 local
links, six local anchors, balanced fences and whitespace, including this untracked
file. The preservation comparison found only the intended roadmap edit among
the 114 baseline files, plus this new specification; the pre-existing roadmap
work log was preserved byte-for-byte. No Lean or article source changed during
that design stage.

The author approved this concrete written specification on 2026-10-06. Its
[implementation plan](../plans/2026-10-06-package-least-support.md) now assigns
the approved contracts to four native tasks, with concurrent Lean/LaTeX work
and one fresh independent final review. No mathematical signature or scope
changed during planning. The verification above belongs to the design session;
planning adds document/preservation checks, not new Lean proof evidence.

The author then approved native execution of the written plan. Both approval
gates are satisfied; do not repeat them. All mathematical tasks and integrated
validation have passed, and the independent final review found no issues.
Leave all work uncommitted.

## Native execution evidence

All 19 approved declarations are implemented in
`Package/Foundations/Nominal.lean`. The proof uses the inspected Finset minimum
API and delivered `supports_inter`; transport, empty support and image inclusion
reuse F04a. Six temporary files under `/tmp/nominal-f04b-execution/` check actual
conclusions, boundary counterexamples, certificate independence, all exact public
signatures and action coherence. The carrier `support_minimal` binders were made
explicit after a raw-type check exposed an inferred order differing from the
specification. No theorem or mathematical hypothesis changed.

The integrated Package build passes 970 jobs using cached dependencies, with
project modules rebuilt after changes. Direct source and consumer checks pass;
the direct audit traverses 132 production declarations from five defining
modules, with only standard axioms. The unchanged checker reaches six production
source modules including the root and one audit module. Retained F03a action
and negative checks pass. This is not a fresh whole-project build or dependency
bootstrap; unchanged reference targets were not rebuilt.

The new `sec:least-support` exposition was developed and compiled with each
mathematical task. The reconciled manuscript is 16 pages with a clean final log;
the integrated final invocation reused the current output. The native plan and
active roadmap record commands, diagnostic corrections and preservation limits.
Independent final review found no actionable Critical, Important or Minor
issues. It independently reran the cached 970-job build, direct source/consumer
and audit checks, import coverage, retained F03a consumers, document/preservation
checks and a fresh manuscript build in `/tmp/nominal-f04b-independent-review/`.
That manuscript is also 16 pages with a clean final log, and its extracted text
was checked against the mathematics. No fix pass was needed.

Final document checks cover seven Markdown files, 146 local links, 13 anchors,
43 LaTeX labels and all changed/untracked whitespace. The execution snapshot
confirms 103 of 116 original files unchanged, exactly 13 intended existing-file
edits and one new module. F04a source, reference sources, pins, validation tools,
the historical roadmap and previous work log are preserved. F04b is complete;
PKG-F04 remains open for F04c/F04d. All work remains uncommitted.
