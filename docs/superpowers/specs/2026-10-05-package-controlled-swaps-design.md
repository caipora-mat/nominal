# F03b: controlled swap factorization

**Article editorial correction:** manuscript passages follow the current
[research-article policy](../../research/2026-10-05-article-plan.md): selected
system/mathematical exposition and substantive comparisons, with no task IDs
or development/review/build diary. Article instructions below are amended
accordingly; the recorded execution history remains an internal record.

Date: 2026-10-05. **Written specification approved by the author.**
The [implementation plan](../plans/2026-10-05-package-controlled-swaps.md) is
approved for native execution. All four results and the matching article are
implemented and checked; independent final review found no issues. F03b is
delivered in the working tree, uncommitted.

Task: **PKG-F03, slice F03b**, with concurrent article work under **PKG-11**.
The [package roadmap](../../nominal-package-roadmap.md) owns status. F02/F03a
are delivered; their [approved specification](2026-10-05-package-foundation-kernel-design.md)
is retained. The next sequence remains F03b → F04 → F05 → PKG-01.

## Intended outcome and fixed boundary

Supply the permutation input needed by later support proofs: a finite
permutation factors into swaps with distinct endpoints in its original
moved-point set. Consequently, a permutation fixing any set pointwise has a
factorization avoiding that set. Consume this at the existing selected action
boundary, without defining support.

Preserve namespace `NominalPackage`, the finite-moved subgroup representation of
`Perm A`, and `MulAction (Perm A) X`. New implementation belongs under `Package/`
and imports Mathlib directly. No new atom/action class, action instance, support
predicate, least support, freshness, fresh selection, nominality, predicate
bundle, abstraction, recursion or generator belongs to this increment.

Work remains on `fasapa/nominal-package`. Preserve all existing tracked and
untracked work, including the reference library, research probes and historical
`docs/roadmap.md`. Do not switch branches, commit, push, merge, publish, upgrade
dependencies or add CI. Persistent usage examples remain reserved for case
studies; foundation consumers stay in temporary files.

## Inspected starting point

At design start, HEAD was `76966b1f2e44f594517442b6572e33abaa9038e0`; the Package
implementation, article and preceding design/research work were uncommitted.
During review, HEAD advanced externally to
`3d2196a57b8964084dd58a65a0cb1c0be50b1592`, committing that preceding work on the
same branch. Snapshot comparison confirmed unchanged source/article contents.
No commit, push or branch change was performed by this design session; the F03b
specification and its tracker/research updates remain uncommitted. Direct inspection
confirmed F03a's group/application/coercion/extensionality, finite moved sets,
multiplication/inverse/conjugation laws, swaps and their equations, canonical
atom/product/Finset actions, `Discrete`, and `Equivariant` declarations.
`Package.lean` currently imports `Permutation` and `Action`. The audit counts
production declarations by originating module; the checker already classifies
every `Package.Foundations.*` module as production.

Pinned versions: Lean 4.34.1 and Mathlib 4.34.1, Mathlib revision
`d13f23b723b8a846827a245b89c10fc7d3f11612` (manifest and installed checkout agree).
Baseline commands actually run during design:

- `lake build Package +Package.Tests.AxiomAudit`: passed, 821 jobs; cached
  project/dependency artifacts and replayed audit output.
- `lake env lean Package/Tests/AxiomAudit.lean`: direct audit passed, 77
  production declarations from two defining modules; only `propext`,
  `Classical.choice`, and `Quot.sound`.
- `python3 Package/Scripts/check-imports.py`: passed, three production source
  modules including the root, and one audit module.
- `git diff --check`: passed before specification edits.

These design-baseline commands checked F02/F03a, not the F03b theorems below. No fresh project build,
dependency bootstrap, checker modification or new article compilation is claimed.

## Assumptions and exact approved public contract

Let `A : Type u`, `X : Type v`, with independent universes. Statements mentioning
`Perm.swap` retain `[DecidableEq A]`; callers may select classical equality
locally. There is no `Infinite A`, countability, `Finite A`, `Fintype A`,
`Nonempty A`, or nominality assumption. The avoidance parameter is **an arbitrary
`Set A`**: neither it nor its complement needs to be finite. Only each
permutation's moved set is finite, already certified by `Perm A`.

The following approved signatures are now implemented and kernel-checked.
They are in namespace `NominalPackage.Perm`:

```lean
variable {A : Type u} [DecidableEq A]

theorem swap_factorization (π : Perm A) :
    ∃ l : List (A × A),
      (l.map (fun p => swap p.1 p.2)).prod = π ∧
      ∀ p ∈ l, p.1 ≠ p.2 ∧ p.1 ∈ π.moved ∧ p.2 ∈ π.moved

theorem swap_factorization_avoiding (π : Perm A) (S : Set A)
    (hfix : ∀ a ∈ S, π a = a) :
    ∃ l : List (A × A),
      (l.map (fun p => swap p.1 p.2)).prod = π ∧
      ∀ p ∈ l, p.1 ≠ p.2 ∧ p.1 ∉ S ∧ p.2 ∉ S

variable {X : Type v} [MulAction (Perm A) X]

theorem smul_eq_of_swap_smul_eq (S : Set A) (x : X)
    (hswap : ∀ a b : A, a ∉ S → b ∉ S → swap a b • x = x)
    (π : Perm A) (hfix : ∀ a ∈ S, π a = a) :
    π • x = x

theorem forall_smul_eq_iff_swap_smul_eq (S : Set A) (x : X) :
    (∀ π : Perm A, (∀ a ∈ S, π a = a) → π • x = x) ↔
      (∀ a b : A, a ∉ S → b ∉ S → swap a b • x = x)
```

The equivalence is the natural converse as well as the requested implication.
Its swap premise includes equal endpoints for ease of use; restricting that
premise to distinct endpoints is equivalent by `swap_self` and `one_smul`.
The factorization itself contains only distinct-endpoint swaps. No assumption
that every element of X has finite support is justified or required.

**Order:** list `[p₁, …, pₙ]` denotes
`swap p₁.1 p₁.2 * (… * (swap pₙ.1 pₙ.2 * 1))`. The rightmost swap acts first,
by `Perm.mul_apply` and `mul_smul`. Prepending a pair left-multiplies the existing
product. The empty list has product 1. No canonical list, executable factoring
algorithm, minimal length or uniqueness is promised.

Use `List.map`, `List.prod_nil`, `List.prod_cons`, the existing application and
swap equations, and ordinary group/action rewriting. A separate swap-word
datatype, evaluator and duplicate list-product API are unnecessary. Public
proofs should not require consumers to unfold the subgroup representation.

## Mathlib investigation and alternatives

All references in this section are to the pinned revision above.

1. **Recommended: specialize restricted-swap closure, then extract a list.**
   `Mathlib/GroupTheory/Perm/ClosureSwap.lean`, `mem_closure_isSwap`, characterizes
   membership in the subgroup generated by an arbitrary set of transpositions
   using finite moved points and an orbit condition. Restrict the generating
   set to swaps whose distinct endpoints lie in the original moved set. Then
   `Subgroup.closure_induction_left` in
   `Mathlib/Algebra/Group/Subgroup/Pointwise.lean` constructs the pair list.
   This reuses the existing finite-set induction and keeps endpoint control
   explicitly in the generator predicate. The Package work is the restriction,
   list certificate, and transfer to its subgroup carrier.
2. **Finite moved subtype.** `Equiv.Perm.subtypePerm` and `ofSubtype` in
   `Mathlib/Algebra/Group/End.lean`, `ofSubtype_subtypePerm`,
   `Equiv.Perm.ofSubtype_swap_eq` in `Perm/Support.lean`, and
   `Equiv.Perm.swap_induction_on` in `Perm/Sign.lean` give another sound adapter.
   Restrict to `π.moved`, apply finite-carrier induction, extend by identity.
   Endpoint membership follows from subtype values. This adds restriction and
   extension transport and the Sign dependency, with no stronger public result.
3. **Direct moved-set induction.** Use the existing raw shrink lemma
   `Equiv.Perm.ne_and_ne_of_swap_mul_apply_ne_self` in `Perm/Support.lean` and
   finite-set induction. This gives a short mathematical proof but duplicates
   the general reduction already used inside `mem_closure_isSwap`. Prefer the
   first route unless an actual elaboration or dependency issue changes that
   assessment; record such evidence without weakening the public contract.

`mem_closure_isSwap'` alone is unrestricted and does not discharge avoidance.
Similarly, `swapFactorsAux` exposes an `IsSwap` certificate but no endpoint
bound in its result type. Neither is treated as the desired theorem merely
because it mentions swap generation.

A bounded dependency/interface probe at
`/tmp/nominal-f03b-design-_hmdmsu4/MathlibBoundary.lean` checks the raw fixed-point
complement bridge, the exact closure/shrink signatures, and existing atom,
permutation-group and pointwise-function action equations after importing the
proposed Mathlib dependencies. It is not a proof of controlled factorization.
The first version had unused `DecidableEq` section-variable warnings; that
version is preserved as `MathlibBoundary.initial.lean`, and the unnecessary
probe variable was removed rather than disabling the linter. Direct
`lake env lean /tmp/nominal-f03b-design-_hmdmsu4/MathlibBoundary.lean` then passed
without diagnostics; its printed bridge axioms are the three permitted ones.

## Proof route and mathematical invariants

Fix π and write M = π.moved. In the ambient group `Equiv.Perm A`, let G consist
of `Equiv.swap a b` for `a ≠ b` and `a,b ∈ M`. This is a local/private generator
predicate, not a new public group representation.

Apply `mem_closure_isSwap` to G. Its finiteness condition is exactly
`π.moved_finite`: the complement of `MulAction.fixedBy A π.toEquiv` is
definitionally M. For its orbit condition at a, use the identity if π a = a.
Otherwise `a ∈ M` and `π a ∈ M`; the latter follows from injectivity, since
`π (π a) = π a` would imply `π a = a`. The generator `swap a (π a)` sends a to
π a. This proves π.toEquiv belongs to the closure of **this restricted G**.

Use left closure induction with a proposition asserting an endpoint-pair list
and equality of its product to the current ambient permutation. The identity
case uses `[]`; a generator step prepends its endpoint pair. The inverse-
generator step uses the same pair, since a swap is self-inverse. All endpoints
remain in fixed M, which is outside the induction motive's changing permutation.
The implementation maintains equality of the underlying product directly, using
`toEquiv_mul` at each cons and then subtype extensionality. This specializes the
planned product transport through `(permSubgroup A).subtype` without a separate
`map_list_prod` rewrite.
No new general homomorphism abstraction or competing action is necessary.

The mathematical reduction behind the adopted closure theorem is precise.
For a moved a, put τ = swap a (π a), ρ = τ * π. Then

```text
a ≠ π a,   a ∈ moved π,   π a ∈ moved π,
ρ a = a,
moved ρ ⊆ moved π \ {a},
|moved ρ| < |moved π|,
π = τ * ρ.
```

The inclusion follows directly from the inspected Mathlib shrink lemma: any
point moved by ρ is moved by π and differs from a. Since a is moved by π, the
inclusion is strict and finite cardinality decreases. It is not in general
equality with `moved π \ {a}`: a two-cycle loses both endpoints. These facts
explain the terminating reduction already proved in Mathlib; the recommended
implementation does not duplicate that induction in Package. If the direct
route is needed, prove the inclusion and strict decrease before applying it.

Avoidance follows because `hfix` implies every member of M lies outside S.
Use the controlled factorization unchanged. For the action consequence, induct
over its list and use `one_smul` and `mul_smul` to show its product fixes x.
For the converse, a swap of a,b outside S fixes each c in S, by the existing
third-point swap equation. Apply the universal permutation hypothesis.

This proves invariance under the pointwise stabilizer of S. Setwise preservation
of S is insufficient. The moved-point set of π is not the support of an element
of an arbitrary action, and no least- or strong-support assertion follows here.

## Target files and import boundary

| Path | Change during approved implementation |
| --- | --- |
| `Package/Foundations/SwapFactorization.lean` | New controlled and avoiding list-factorization theorems; import existing Permutation and required Mathlib closure/list infrastructure |
| `Package/Foundations/Action.lean` | Import SwapFactorization and add the two action results at the existing selected action boundary |
| `Package.lean` | Explicitly export SwapFactorization alongside existing foundation imports |
| `Package/Tests/AxiomAudit.lean` | Add representative `#print axioms` for all four new public results; retain whole-production traversal |
| `Package/README.md` | Document the four declarations, list order, arbitrary-set contract and delivered boundary |
| `docs/article/sections/foundations.tex` | Selected mathematical exposition and relevant declaration correspondence |
| `docs/article/sections/introduction.tex`, `docs/article/main.tex` | Reconcile the scientific scope and abstract with the formalized results |
| `docs/nominal-package-roadmap.md` | F03b/F03 and PKG-11 evidence and completion status |
| `docs/research/README.md`, `2026-10-05-pkg01-readiness.md`, `2026-10-05-article-plan.md` (under `docs/research/`) | Link review artifacts, then reconcile current delivery and remaining F04/F05 work |

The new dependency direction is `Permutation → SwapFactorization → Action`.
Keep the existing base representation and action instances. The import checker
already accepts the proposed module; no checker, Lake, dependency, reference
source or old validation-script change is expected. Its report should reach
four production source modules and one audit module; actual declaration counts
must be measured, not predicted.

## Concurrent LaTeX development

All manuscript content stays under `docs/article/` in LaTeX. This section is the
article obligation of the increment and must have owning tasks in its subsequent
implementation plan.

Replace the factorization deferral after transpositions with a subsection
`sec:controlled-swaps`, including `prop:controlled-factorization` and
`prop:avoidance-factorization`. State the arbitrary atom carrier, decidable-
equality encoding requirement, distinct endpoints in the original moved set,
rightmost-first composition convention and empty identity product. Explain
restricted generators, the orbit witnesses and closure/list proof, together
with the finite moved-set reduction underlying the adopted Mathlib result.
Identify the reused Mathlib mathematics and the additional Package certificate.

After introducing selected actions, add `prop:swap-invariance` for the exact
equivalence above, with the essential list-action argument and converse. Explain
its mathematical role in the support criterion, without roadmap labels. State
only the results justified by the corresponding formalization.

Draft the exposition while the Lean proofs are developed. Reconcile the
mathematical hypotheses, product order, selected proof explanation and relevant
declaration references against the source. Retain the reasoning that explains
endpoint control and its significance, rather than duplicate routine calculations.
The article has no operational evidence section: module/declaration counts,
axiom-audit output, commands, cache conditions, reviews and phase identifiers
belong in the roadmap or implementation notes. Update the introduction/abstract
around mathematical scope. Compile and review the manuscript internally.

## Acceptance and verification

1. Kernel-check the four exact public statements with standard axioms only.
   No `sorry`, `admit`, custom axiom, disabled kernel checking or extra atom/
   action/avoidance-set assumption is permitted.
2. Use temporary named theorems with only `import Package` to consume endpoint
   membership and the product equality, derive avoidance for arbitrary S, and
   prove the action conclusion for independently quantified A/X and a selected
   `MulAction`. Conclusions must use the facts, not prove `True`.
3. Check the identity using the empty list and prove that a controlled list
   for identity is empty; check empty and singleton atom carriers, a two-point
   swap and a noncommuting finite three-point composition. Confirm the latter's
   application order. Do not require a particular factor list for a nonidentity
   permutation, since factorization is nonunique.
4. Check `S = ∅`, `S = Set.univ`, and a temporary infinite avoidance-set
   specialization, plus a generic arbitrary-set consumer. No finite-set coercion
   or unused finiteness premise may conceal a narrower theorem.
5. Recheck public-import action coherence for atoms, products, scoped Finsets,
   Discrete, bare permutation groups and pointwise functions. Reuse existing
   F03a temporary checks when available instead of rebuilding their interface.
6. Compile affected modules and dependents, run the production coverage and
   direct audit, and inspect representative `#print axioms`. Keep the new module
   in both production and audit closures. If the checker changes, rerun its
   self-tests; otherwise no checker rewrite or new persistent harness is needed.
7. Deliver the reconciled LaTeX sections, mathematical correspondence review and
   successful manuscript compilation before marking F03b complete. Record
   commands actually run and limitations; F04/F05/PKG-01 remain later work.

Required implementation verification commands:

```sh
lake build Package +Package.Tests.AxiomAudit
lake env lean Package/Tests/AxiomAudit.lean
python3 Package/Scripts/check-imports.py
git diff --check
```

Also directly check the temporary public-import Lean files. From `docs/article/`:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error \
  -outdir=/tmp/nominal-package-article-build main.tex
```

Keep generated files outside the source tree. Check document links, untracked
file whitespace, and preservation against the starting snapshot. If shared
integration changes become necessary, run the appropriate separate reference
checks (`lake build Nominal Instances Examples`, its direct audit and import
checker); do not report reference validation as Package evidence. Distinguish
cached builds, rebuilt project modules with cached dependencies, fresh project
builds and dependency bootstraps. No clean dependency bootstrap is required.

## Review and execution gates

The author approved this concrete bounded specification, including the four
signatures, arbitrary-set hypotheses, restricted-closure proof route, target
files and article obligations. A separate implementation plan now includes
concurrent LaTeX tasks. The author approved that plan and selected native execution; this agreement
authorizes the bounded production and article work specified here.

Self-review checked statement strength, original-set endpoint control, composition
order, scope, file coverage and article obligations. An independent read-only
review found no mathematical or scope issue; its baseline-status finding was
resolved by recording the externally advanced HEAD above.

## Delivery evidence

All four approved declarations are implemented with unchanged signatures. The
new module and action consumer pass the Package build and temporary public-import
checks. The direct audit checks 81 production declarations from three defining
modules with only standard axioms; coverage reaches four production source
modules and one audit. The reconciled article compiles to 17 pages without final
reference or layout diagnostics. Independent review found no Critical, Important
or Minor issues and independently reran the Lean checks and a fresh manuscript
build. Exact commands and cache/preservation limits are in the package roadmap
delivery log. No fresh Lean project/dependency bootstrap is claimed, and no
commit, push, branch change or F04 implementation was performed.
