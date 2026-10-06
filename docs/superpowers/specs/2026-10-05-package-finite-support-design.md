# F04a: finite support calculus

**Article editorial correction:** manuscript passages follow the current
[research-article policy](../../research/2026-10-05-article-plan.md): selected
system/mathematical exposition and substantive comparisons, with no task IDs
or development/review/build diary. Article instructions below are amended
accordingly; the recorded execution history remains an internal record.

Date: 2026-10-05. **Written specification approved by the author.**
Task: **PKG-F04, slice F04a**, with concurrent article work
under **PKG-11**. The [package roadmap](../../nominal-package-roadmap.md) owns
status and the F04a–F04d split. The
[implementation plan](../plans/2026-10-05-package-finite-support.md) was approved
for native execution. All 18 public declarations and their temporary consumers
now check; independent final review found no issues. F04a is delivered in the
working tree, uncommitted.

## Intended outcome and agreed constraints

Give ordinary Lean clients a finite-support calculus for an already selected
`MulAction (Perm A) X`. This supplies F04b's least-support construction and later
equivariant clients without introducing nominality, least support, freshness,
quotients, predicate bundles or another function-space action in this increment.

Preserve `NominalPackage`, `Perm A`, independent atom/carrier universes, the
delivered F02/F03a/F03b interfaces and all existing action choices. New production
code belongs under `Package/` and uses pinned Mathlib directly. Existing
`Nominal/` and `Instances/` are optional references, not imports or API constraints.
The historical `docs/roadmap.md` remains unchanged.

The user selected F04 and requested a written F04a specification followed by
separate specification and execution agreements. The later slices define the
overall scope; they do not authorize implementation together. No branch switch,
commit, push, merge, publication, dependency upgrade or CI change is authorized.
Persistent usage examples remain reserved for case studies; acceptance consumers
will be temporary public-import files.

## Inspected starting point

The actual branch is `fasapa/nominal-package`, with HEAD
`34a83358739ab962e2b9d2035a21d67b2a896071`; the working tree was clean at design
start. That commit contains the F03b implementation, article and review artifacts.
Statements in earlier delivery logs that those changes were uncommitted describe
their historical inspections, not this checkout. F02/F03a were committed in the
preceding `3d2196a57b8964084dd58a65a0cb1c0be50b1592`.

Inspected inputs include the repository and Package READMEs, production modules,
public root, audit and coverage checker; the research brief, readiness,
predicate-foundations and article-plan notes; the approved
[F03b specification](2026-10-05-package-controlled-swaps-design.md); and the
manuscript entry point and both included sections. The historical development
review and library roadmap were consulted as earlier evidence only.

Lean is pinned to `v4.34.1`. Mathlib's installed checkout and manifest agree at
`d13f23b723b8a846827a245b89c10fc7d3f11612` (`v4.34.1`). Source inspection confirms
all four F03b results: `Perm.swap_factorization`,
`Perm.swap_factorization_avoiding`, `Perm.smul_eq_of_swap_smul_eq`, and
`Perm.forall_smul_eq_iff_swap_smul_eq`. F04a specializes the last equivalence;
it does not reimplement factorization or its action induction.

Historical baseline verification run during design, before implementation:

- `lake build Package +Package.Tests.AxiomAudit`: passed, 967 jobs, using cached
  project/dependency artifacts and replaying the compiled audit's output.
- `lake env lean Package/Tests/AxiomAudit.lean`: direct traversal passed,
  81 production declarations from three defining modules, with only `propext`,
  `Classical.choice` and `Quot.sound`.
- `python3 Package/Scripts/check-imports.py`: passed, four production source
  modules including the root, and one audit module. The checker is unchanged.
- The documented `latexmk` command from `docs/article/`: passed with existing
  outputs already up to date; the existing final log has no warning, unresolved
  reference or overfull/underfull-box diagnostics.
- `git diff --check`: passed before documentation edits.

These checks certify the delivered baseline, not the approved F04a signatures
below. At that design stage no new Lean declaration or scratch implementation
had been written or checked.
No fresh project build, dependency bootstrap or fresh manuscript rebuild is claimed.

## Representation decision and alternatives

**Approved choice: a finite-set abbreviation of Mathlib's predicate.**
`MulAction.Supports G s b` already means that every scalar fixing every member
of `s` fixes `b`. Its support and result carriers have independent universes.
Specializing `G` to `Perm A` and `s` to the coercion of a `Finset A` preserves
that definition exactly and gives finite-bound clients a short interface.

The alternatives are direct use of `MulAction.Supports (Perm A) (S : Set A) x`
everywhere, which repeats group/coercion arguments in the intended finite-bound
API, or a new predicate repeating its quantifier, which duplicates the meaning
and requires needless bridges. A general Set-valued Package support layer is
also unnecessary: clients needing arbitrary sets already have Mathlib's
predicate and F03b's arbitrary-set criterion.

Do not introduce a second pointwise-fixing predicate or a fixing-subgroup API.
The public `supports_iff` equation exposes the pointwise condition in the same
explicit-binder form as F03b. No global action or atom inference class is added.
The atom sort is determined by `S : Finset A` for `Supports S x` and is explicit
in `FinitelySupported A x`, just as it is in `Equivariant A f`.

Use qualified Package theorem names such as `supports_mono` and `supports_smul`.
The abbreviation unfolds to Mathlib's `Supports`; the public contract does not
depend on dot-notation resolution choosing between two namespaces' `Supports.smul`
methods with different hypotheses. No unproved elaboration convenience is promised.

## Exact approved public contract

The following approved declaration signatures are now implemented and checked
in namespace `NominalPackage`. Let `A : Type u`, `X : Type v`, and
`Y : Type w`, with all three universes independent. Every action is the selected
`MulAction (Perm A)` on its stated carrier. No carrier-wide supportedness is assumed.

### Definitions and laws without atom assumptions

```lean
abbrev Supports {A : Type u} {X : Type v}
    [MulAction (Perm A) X] (S : Finset A) (x : X) : Prop :=
  MulAction.Supports (Perm A) (S : Set A) x

def FinitelySupported (A : Type u) {X : Type v}
    [MulAction (Perm A) X] (x : X) : Prop :=
  ∃ S : Finset A, Supports S x

variable {A : Type u} {X : Type v} {Y : Type w}
variable [MulAction (Perm A) X] [MulAction (Perm A) Y]
variable {S T : Finset A} {x : X} {y : Y} {f : X → Y}

theorem supports_iff (S : Finset A) (x : X) :
    Supports S x ↔
      ∀ π : Perm A, (∀ a ∈ S, π a = a) → π • x = x

theorem supports_mono (hST : S ⊆ T) (hS : Supports S x) :
    Supports T x

theorem supports_empty_iff (x : X) :
    Supports (∅ : Finset A) x ↔ ∀ π : Perm A, π • x = x

theorem supports_map (hf : Equivariant A f) (hS : Supports S x) :
    Supports S (f x)

theorem supports_prod_iff (S : Finset A) (x : X) (y : Y) :
    Supports S (x, y) ↔ Supports S x ∧ Supports S y

theorem Supports.finitelySupported (hS : Supports S x) :
    FinitelySupported A x

theorem FinitelySupported.smul (hx : FinitelySupported A x) (π : Perm A) :
    FinitelySupported A (π • x)

theorem finitelySupported_smul_iff (π : Perm A) (x : X) :
    FinitelySupported A (π • x) ↔ FinitelySupported A x

theorem FinitelySupported.map (hx : FinitelySupported A x)
    (hf : Equivariant A f) : FinitelySupported A (f x)

theorem FinitelySupported.prod (hx : FinitelySupported A x)
    (hy : FinitelySupported A y) : FinitelySupported A (x, y)
```

These declarations require neither `DecidableEq A` nor `Infinite A`.
The existential transport/product proofs may use local classical equality to
form witness images/unions inside `Prop`. They do not store chosen support sets
as data or add an action on ordinary functions. Equivariant-image bounds can
shrink; no converse or exact least-support assertion is made.

### Finite-set operations and swaps

With the variables above, add only `[DecidableEq A]` and
`open scoped Pointwise` for the existing finite-set image action:

```lean
theorem supports_smul (hS : Supports S x) (π : Perm A) :
    Supports (π • S) (π • x)

theorem supports_smul_iff (π : Perm A) (S : Finset A) (x : X) :
    Supports (π • S) (π • x) ↔ Supports S x

theorem supports_prod (hS : Supports S x) (hT : Supports T y) :
    Supports (S ∪ T) (x, y)

theorem supports_iff_swap (S : Finset A) (x : X) :
    Supports S x ↔
      ∀ a b : A, a ∉ S → b ∉ S → Perm.swap a b • x = x

theorem swap_smul_eq_of_supports (hS : Supports S x)
    {a b : A} (ha : a ∉ S) (hb : b ∉ S) :
    Perm.swap a b • x = x
```

No infinitude, countability, nonemptiness, nominality or commuting-action
assumption belongs to these results. Equal-endpoint swaps are allowed, as in F03b.
Finite-set action expressions use the scoped Mathlib image action, never a new
global instance. Consumers explicitly open `Pointwise` where that notation occurs.

### Binary intersection

Add `[Infinite A]` only for:

```lean
theorem supports_inter (hS : Supports S x) (hT : Supports T x) :
    Supports (S ∩ T) x
```

The bounds here are **finite sets**. Decidable equality is retained for the
visible finite-set intersection; infinitude supplies a spare atom in the proof.
This theorem needs no `Nominal A X`, and no general intersection-closure claim
on finite atom carriers is part of the interface. A weaker spare-atom premise
could suffice in particular cases, but exporting another intersection theorem
or a separate atom-selection API is unnecessary for F04b.

## Pinned Mathlib reuse and concrete gaps

Paths in this table are relative to `.lake/packages/mathlib/Mathlib/` at the
pinned revision above; the declarations were inspected directly.

| Source and declaration | Use or boundary |
| --- | --- |
| `GroupTheory/GroupAction/Support.lean:36`, `MulAction.Supports` | Adopt the predicate by finite-set specialization; it separates support/result carriers |
| Same file, `supports_of_mem` (42), `Supports.mono` (47) | Reuse atom membership support in consumers and monotonicity in the adapter |
| Same file, `Supports.smul` (57) | Requires `SMulCommClass` on both carriers; does not establish the required permutation transport |
| `GroupTheory/GroupAction/FixingSubgroup.lean`, `fixingSubgroup`, `mem_fixingSubgroup_iff` | Correct pointwise-fixer infrastructure; no subgroup-valued API is needed in this slice |
| `GroupTheory/GroupAction/SubMulAction/OfFixingSubgroup.lean`, `Set.conj_mem_fixingSubgroup`, `fixingSubgroup_smul_eq_fixingSubgroup_map_conj` | Existing conjugation transport for fixing subgroups; useful alternative, but imports subactions, transitivity and primitivity for a short elementwise support proof |
| `Algebra/Group/Pointwise/Finset/Scalar.lean`, `smul_mem_smul_finset`, `coe_smul_finset`; `Algebra/Group/Action/Pointwise/Finset.lean`, `inv_smul_mem_iff` | Existing image-membership/coercion laws; Package already supplies `Perm.smul_finset` and `Perm.mem_smul_finset` |
| `Algebra/Group/Action/Prod.lean` | Retain the standard componentwise product action |
| `Data/Set/Finite/Basic.lean:847`, `Finset.exists_notMem` | Obtain an atom outside a finite union under `Infinite A`; no fresh-selector definition |
| `Algebra/Group/End.lean`, `Equiv.Perm.swap_mul_swap_mul_swap` | Available triple-swap identity; the delivered `Perm.conj_swap` already yields the needed identity at the Package boundary |

Searches of the pinned group-action support/fixing-subgroup modules found no
finite-permutation support-intersection theorem. The new nominal argument is
the spare-atom proof below, using the already delivered swap criterion. The
transport gap is removed by conjugation, not by adding a commutation hypothesis.
Monotonicity, finite avoidance, general action laws and swap generation are reused.

For the later F04d boundary, exact source inspection also confirms:
`Function.Surjective.mulAction` in `Algebra/Group/Action/Defs.lean:454` supplies
action laws for an **already defined** scalar operation and a commuting
surjective map; it does not construct the quotient scalar operation by itself.
`Quotient.map` and `Quotient.map_mk` in `Data/Quot.lean:230–236` supply the
relation-respecting lift and its representative equation. These are candidates
for F04d's canonical construction, not imports or implementation tasks in F04a.

## Proof strategy

The `supports_iff` adapter changes only the implicit atom binder in Mathlib's
pointwise premise and uses `Perm.smul_atom`. Monotonicity specializes Mathlib's
lemma. Empty support is universal invariance because the pointwise premise is
vacuous. For an equivariant `f`, rewrite `π • f x` as `f (π • x)` and apply the
support hypothesis. Product support with a common bound is componentwise;
the union theorem follows by monotonicity. Existing equivariant projections can
also supply the two component implications. Existential closure uses these bounds.

For transport, suppose σ fixes `π • S` pointwise. For every `a ∈ S`, σ fixes
`π a`, so `π⁻¹ * σ * π` fixes a. Support of x therefore gives

```text
(π⁻¹ * σ * π) • x = x,
σ • (π • x) = π • ((π⁻¹ * σ * π) • x) = π • x.
```

Use the existing group/action/application equations and finite-image membership
laws. The reverse implication applies this transport with `π⁻¹` and cancels both
actions. The argument works for arbitrary sets too; a private Set-level helper
is permitted if useful, without adding another public support predicate. The
small elementwise proof avoids the larger fixing-subgroup import above.

The swap characterization is exactly the F03b equivalence at `(S : Set A)`,
combined with `supports_iff`. The outside-swap consequence projects its forward
direction. Do not repeat controlled factorization or list-action induction.

For intersection, use the swap characterization and take a,b outside `S ∩ T`.
If a = b, the swap is identity. Otherwise choose c outside the finite set
`S ∪ T ∪ {a,b}` using `Finset.exists_notMem`. Each of a,b lies outside at least
one of S,T. Since c lies outside both, `(a c)` fixes x using whichever support
a avoids, and `(c b)` fixes x using whichever support b avoids. The identity

```text
swap a c * swap c b * swap a c = swap a b
```

follows from `Perm.conj_swap (Perm.swap a c) c b`, `Perm.swap_inv` and the
endpoint/third-point equations. All three factors fix x, so `mul_smul` shows
that `swap a b` fixes x. F03b then establishes the full pointwise-fixer condition.
This is a support proof, not new swap-generation machinery.

The necessary boundary example uses `A = Bool`, its canonical atom action, and
`x = false`. The singleton `{false}` supports false by membership. If a bijection
fixes true, injectivity on the two-point carrier forces it to fix false, so
`{true}` also supports false. Their intersection is empty, whereas
`Perm.swap false true` moves false. Thus unconditional binary intersection is
false. The temporary `IntersectionContracts.lean` consumer now checks both
singleton supports and failure of their empty intersection; it is not an
additional exported Package declaration.

## Modules, imports and scope

Add one production module, `Package/Foundations/Support.lean`, importing:

```lean
import Package.Foundations.Action
import Mathlib.GroupTheory.GroupAction.Support
import Mathlib.Data.Set.Finite.Basic
```

The final import makes the finite-avoidance dependency explicit even though the
permutation module already imports it. The dependency direction stays
`Permutation → SwapFactorization → Action → Support`. Definitions and basic laws
occupy sections without atom assumptions; separate sections introduce decidable
equality and finally infinitude. Proof ordering can differ from the signature
grouping above so that existential closure follows the bound theorems.

| File | Change during approved F04a execution |
| --- | --- |
| `Package/Foundations/Support.lean` | Proposed definitions and calculus above; no new action instance |
| `Package.lean` | Explicit public import of Support |
| `Package/Tests/AxiomAudit.lean` | Representative prints for `supports_smul`, `supports_iff_swap`, `supports_inter`, image/product and finite-support closure; retain module-origin traversal |
| `Package/README.md` | Delivered support API, assumptions, scoped finite-set action and boundaries |
| `docs/article/sections/support.tex` | New `sec:finite-support` section developed together with the Lean proofs |
| `docs/article/main.tex`, `sections/introduction.tex`, `sections/foundations.tex` | Include the new mathematical section and reconcile scientific scope and relevant declaration references |
| `docs/nominal-package-roadmap.md` and relevant research guides | Record F04a verification/status without closing F04b–F04d |

The existing checker and audit already classify all `Package.Foundations.*`
modules as production. No checker, Lake, dependency or reference-source change
is expected. After the public import is added, coverage must reach five
production source modules including the root and the existing audit module.
Measure the actual declaration count rather than prescribing one.

Use ordinary theorem application, `simp`, and product extensionality. Do not
mark the quantified `supports_iff` or `supports_iff_swap` expansions as global
simp rules. Any additional simp attributes must have a directed use and be
checked for termination; no broad reducibility, instance-priority or linter
change belongs to this design.

## Concurrent article obligation

The corresponding article section is **Finite support calculus**,
`docs/article/sections/support.tex`, label `sec:finite-support`. This section is
now written alongside the checked Lean results. The implementation plan assigns its
drafting to the same tasks as the definitions, transport and intersection proofs,
and its reconciliation/compilation to final validation.

State the mathematical notion before its encoding: a finite atom bound supports
x when its pointwise fixer fixes x. Explain finite supportedness as an existential
property of a single element with a selected action, and explain why Mathlib's
two-carrier `Supports` matches it. Compare direct use, the selected abbreviation
and the unnecessary duplicate predicate; the finite-bound adapter is an interface
choice, not a new mathematical notion.

Select the central results and proof ideas: finite support, conjugation
transport, the swap criterion and finite intersection. Summarize routine
monotonicity/image/product bounds where they clarify the theory; do not enumerate
every auxiliary lemma. Give the Bool counterexample and explain where infinitude
enters. Pointwise fixation differs
from setwise preservation; support bounds do not identify moved points of bare
permutations, and finite support is not least or strong support.

Keep the manuscript claims within the established mathematical results. Reconcile
universes, equality/infinitude hypotheses, action choices, relevant Mathlib
attribution and selected declaration references. Explain conceptual connections
and limits in mathematical terms. Do not include task labels, implementation
stages, review reports, audit counts, commands, cache limits or delivery status.
Record those details in the roadmap and implementation notes. Later concepts
may be discussed as mathematical context without claiming unproved results.

The design session originally assigned this article work without claiming it
delivered. Native execution has now written and checked the mathematics; final
evidence reconciliation and independent review are recorded with delivery below.
All manuscript writing remains LaTeX under `docs/article/`; this Markdown file
is a specification only.

## Acceptance checks for approved execution

1. Kernel-check the exact public statements above. Audit only standard `propext`,
   `Classical.choice`, `Quot.sound`; no admissions, custom axioms, disabled kernel
   checking, weakened statements or extra commutation/nominality assumptions.
2. Temporary named theorems using only `import Package` must consume the actual
   conclusions: both directions of `supports_iff`, empty support and the swap
   criterion; enlarged bounds; transport and its inverse; image and product
   bounds; finite-supportedness closure and intersection.
3. Quantify independently over A/X/Y with arbitrary selected actions. Check the
   assumption-free signatures without a decidable-equality or infinite instance;
   use local classical equality only where witness proofs require it. Exercise
   empty/singleton atom carriers for basic laws and a noncommuting permutation
   example on three atoms for transport, so no commuting-action premise is hidden.
4. Use canonical atom singleton support through Mathlib `supports_of_mem`,
   discrete empty support through `Discrete.smul_mk`, and nested product union
   bounds in temporary consumers. F04a exports no nominal instances or exact
   least-support formulas for these clients; those remain F04c.
5. On an infinite atom carrier, combine independent support hypotheses and use
   the intersection conclusion to prove a permutation fixes the element.
   Include a concrete consumer with overlapping bounds `{a,b}` and `{a,c}`
   supporting a, with a,b,c distinct; the proof reduces to singleton `{a}`.
   Also prove all three parts of the Bool counterexample, including failure of
   empty support. A rejected application lacking `Infinite` alone is insufficient.
6. For equivariant images, include a constant map into explicit discrete data
   to show that an inherited bound need not be least. Recheck existing public
   action equations on atoms, products, scoped Finsets, Discrete, bare Perm and
   pointwise functions; do not infer nominality of the last two.
7. Compile the affected module, then the supported Package target and audit.
   Run direct temporary consumers and representative `#print axioms`, confirming
   every new module lies in both production and audit closures. If the import
   checker changes, run its self-tests; otherwise preserve it.
8. Deliver the concurrent LaTeX section with matching mathematics, hypotheses,
   actual declarations and verification status; compile the manuscript and check
   its log and mathematical correspondence before closing F04a.

Required final commands, in addition to affected-module and temporary consumer
checks:

```sh
lake build Package +Package.Tests.AxiomAudit
lake env lean Package/Tests/AxiomAudit.lean
python3 Package/Scripts/check-imports.py
git diff --check
```

From `docs/article/`:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error \
  -outdir=/tmp/nominal-package-article-build main.tex
```

Keep generated files outside the source tree. Check local links, untracked-file
whitespace and reference/source preservation separately. Shared integration
changes affecting reference targets require their separate build/audit/import
checks; no such change is expected. Record commands actually run and distinguish
cached builds, rebuilt project artifacts with cached dependencies, and fresh
dependency bootstraps. F04a is complete only after code, meaningful consumers,
audit and article pass; PKG-F04 remains open until all four agreed slices pass.

## Review gates

The author approved this written specification on 2026-10-05, including its
public API, assumption boundaries, Mathlib reuse, proof strategies, module design
and article/acceptance obligations. The subsequent plan approval selected native
execution and authorized its bounded production/article changes. Self-review checks
theorem strength, finite-atom boundaries, action coherence, assumption separation,
imports, scope and article coverage. Source investigations support the proof
strategies; all new public declarations have now passed Lean verification.

Self-review and two independent read-only reviews found no actionable
mathematical, assumption, API or phase-boundary issue. These were source/design
reviews, not compiler checks of the proposed declarations.

The implementation plan was prepared using the writing-plans workflow, reviewed
by the author and approved for native execution. Both approval gates are satisfied;
do not request them again. Preserve all prior F02/F03 approvals
and completed work; do not restart the earlier architecture investigation or
infer approval for F04b–F04d from the phase outline.

## Execution evidence

All 18 approved declarations are implemented in `Package/Foundations/Support.lean`
without added hypotheses or weakened conclusions. The final 969-job Package build,
five temporary public-import consumer/signature files, direct axiom audit and
import checker pass. The audit covers 104 production declarations from four
defining modules with only standard axioms; the checker reaches five production
source modules and one audit. Retained F03a action and negative consumers also pass.

The corresponding LaTeX section is written and reconciled with the checked
mathematics. Root rebuilt the manuscript to 26 pages with a clean final log and
inspected the extracted section text. Independent final review found no Critical,
Important or Minor issues and reran the Package checks and a fresh manuscript build.
Commands, cache conditions, scratch paths and preservation limits are recorded
in the active roadmap's native F04a validation log. These checks use cached
dependencies, not a fresh full project build or dependency bootstrap. Work
remains uncommitted; no F04b–F04d result is claimed.
