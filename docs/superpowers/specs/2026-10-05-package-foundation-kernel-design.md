# Package foundation kernel: F02 and F03a

**Article editorial correction:** manuscript passages follow the current
[research-article policy](../../research/2026-10-05-article-plan.md): selected
system/mathematical exposition and substantive comparisons, with no task IDs
or development/review/build diary. Article instructions below are amended
accordingly; the recorded execution history remains an internal record.

Date: 2026-10-05. **Written specification approved by the author.**
The author approved F02 + F03a, then requested a LaTeX article developed alongside
implementation under `docs/article/`. The
[implementation plan](../plans/2026-10-05-package-foundation-kernel.md) was reviewed;
the author approved it and selected native execution. The implementation is now
present in the working tree. A later user correction removes the standalone
Package examples layer: persistent usage examples belong to future case studies.
Research checkout:
`fasapa/nominal-package`, `76966b1f2e44f594517442b6572e33abaa9038e0`.

This is the first bounded foundation increment identified by the
[PKG-01 readiness assessment](../../research/2026-10-05-pkg01-readiness.md).
The [package roadmap](../../nominal-package-roadmap.md) owns task status.
“F03a” and “F03b” name slices of stable task PKG-F03, not replacements for its ID.

## Outcome and boundary

Provide a small independently checked Package import through which a user can
apply finite permutations to atoms, products, finite atom sets and explicit
discrete data, prove renaming equations, and inspect the assumptions of those
proofs. Establish the target/import/audit boundary before any predicate
claim is implemented. The result serves later support and predicate proofs,
while keeping the completed Nominal/Instances development available intact.

The deliverable is **F02 plus part of F03**, not PKG-01 and not all of F03.
Finite support, least support, freshness, quotient actions, supported predicates,
Some/Any, name abstraction, recursion, generated syntax and automation remain
subsequent increments. No such implementation is hidden in this specification.
The only nominal convention established here is the permutation/action boundary.

## Approved dependencies and conventions

- Retain pinned Lean and Mathlib 4.34.1 and the current Lake manifest.
- Use namespace `NominalPackage` and top-level implementation directory
  `Package/`. The conventional `Package.lean` root and minimal Lake registration
  are the only required implementation integration outside that directory.
- Depend directly on Mathlib. Import no `Nominal`, `Instances`, `Examples`,
  research probe or historical `NominalSets` module from Package production.
- Represent `Perm A` by the subgroup of `Equiv.Perm A` whose moved-point set is
  finite. Adapt the elementary subgroup proofs, with attribution to the
  reference construction where used; do not import its tactic/support closure.
- Use standard `MulAction (Perm A) X`, not a new outParam action class.
  Atom A and carrier X may inhabit independent universes.
- Reuse Mathlib's product action and its `Pointwise`-scoped Finset image action.
  A consumer using finite-set scalar notation explicitly writes
  `open scoped Pointwise`; importing an implementation file with that scope
  opened is not assumed to activate it downstream.
- Use a distinct `Discrete A X` structure for arbitrary data with trivial
  action. Do not infer that arbitrary external data or ordinary functions are
  discrete. Do not install conjugation on the bare permutation group, whose
  inherited self-action is left multiplication.

These choices are justified against the alternatives in the readiness note.
In particular, all-new action classes would add another class/instance layer
without an immediate client need; importing the old core would couple this
boundary to its namespace/instance policy and `Nominal.Wheels`. Either remains
a possible explicitly reviewed revision if actual implementation evidence
changes the cost comparison.

## Public mathematical contract

The statements below are the approved contract, now implemented in the working
tree and checked. No theorem here requires
atom countability. Generic group/action results need no `Infinite A`; later
freshness/support proofs will add it where needed.

Let `A : Type u`, `X : Type v`, `Y : Type w`.

### Finite permutations

```text
Perm A = {π : Equiv.Perm A // Set.Finite {a | π a ≠ a}}
```

The implementation obtains the group structure from a proved subgroup,
provides ordinary function application and `toEquiv`, and proves:

```text
Perm.ext : (∀ a, π a = σ a) → π = σ
Perm.one_apply : (1 : Perm A) a = a
Perm.mul_apply : (π * σ) a = π (σ a)
Perm.inv_apply_apply : π⁻¹ (π a) = a
Perm.apply_inv_apply : π (π⁻¹ a) = a
Perm.toEquiv_one / mul / inv : coercion preserves group operations

Perm.moved π = {a | π a ≠ a}                 -- Set A, not a chosen Finset
Perm.moved_finite : (Perm.moved π).Finite
Perm.moved_one : Perm.moved 1 = ∅
Perm.moved_mul_subset : Perm.moved (π * σ) ⊆ Perm.moved π ∪ Perm.moved σ
Perm.moved_inv : Perm.moved (π⁻¹) = Perm.moved π
Perm.moved_conj : Perm.moved (π * σ * π⁻¹) = π '' Perm.moved σ
```

For `[DecidableEq A]`, provide `Perm.swap (a b : A) : Perm A` with:

```text
swap a b a = b
swap a b b = a
c ≠ a → c ≠ b → swap a b c = c
swap a a = 1
(swap a b)⁻¹ = swap a b
swap a b * swap a b = 1
π * swap a b * π⁻¹ = swap (π a) (π b)
a ≠ b → Perm.moved (swap a b) = {a,b}
```

Use qualified names to avoid confusion with `Equiv.swap`. Exact carrier/group
coercions must be checked by consumers, including ordinary rewriting and ext.
Keep mathematical finite-support witnesses in proof fields; the application
function itself must not require selecting a least support.

This slice does **not** prove finite-swap generation/factorization or the
outside-a-support factorization used by a swap characterization. Those laws or
an equivalent support-proof route are F03b obligations; F03 remains incomplete
until its support-facing contract is established and consumed.

### Actions and equivariance

The canonical atom action must compute as `π • a = π a`. It is a single
`MulAction` path; a separately competing `SMul` is not installed. For arbitrary
selected actions, expose/use the standard laws:

```text
1 • x = x
(π * σ) • x = π • (σ • x)
π⁻¹ • (π • x) = x
π • (π⁻¹ • x) = x
π • x = π • y ↔ x = y
```

For products, `π • (x,y) = (π • x, π • y)` with both projection equations.
For finite atom sets under the explicitly selected `Pointwise` scope:

```text
π • S = S.image π
a ∈ π • S ↔ π⁻¹ a ∈ S
π • ∅ = ∅
π • {a} = {π a}
π • (S ∪ T) = (π • S) ∪ (π • T)
```

Finite-set equations may use local classical decidable equality. Do not supply
a new globally overlapping Finset action merely to avoid a scope declaration.
The namespace/scoped interface should be documented at its point of use.

`Discrete A X` has `val : X`, constructor/application equations, and
`(π • d).val = d.val`. Its ordinary type equivalence to X does not make that
equivalence an equivariant map to an independently acted-on X. In particular,
`Discrete A A` and A represent different actions when permutations move atoms.

Define the unbundled property for ordinary maps:

```text
Equivariant (f : X → Y) := ∀ (π : Perm A) x, f (π • x) = π • f x
```

Require identity and composition closure and equivariance of product projections
and pairing of equivariant maps. These give meaningful ordinary-function clients
without introducing a supported-function wrapper or a conjugation instance on
bare function types.

Universe coverage includes independently quantified u/v/w, products of unequal
universes, and universe-correct `PUnit`/`PEmpty` data. The implementation may use
ordinary Type-valued carriers; no general `Sort`-valued action/recursor interface
is promised. `Prop` can later occur as the codomain of an ordinary predicate
without requiring any global truth-action instance.

## Files and import/build coverage

The following paths form the implemented boundary. Temporary compatibility
checks are outside the library; persistent usage examples are deferred to case
studies at the author’s request.

| Path | Responsibility |
| --- | --- |
| `Package.lean` | Public production import root, importing the two foundation modules |
| `Package/Foundations/Permutation.lean` | Subgroup, application/group/moved-set/swap contract |
| `Package/Foundations/Action.lean` | Canonical atom action, documented standard products/Finset actions, discrete wrapper, equivariance |
| `Package/Tests/AxiomAudit.lean` | Module-origin audit importing Package production declarations |
| `Package/Scripts/check-imports.py` | Separate production/audit closure accounting and forbidden dependency/orphan checks |
| `Package/README.md` | Actual commands, scope requirements and validation limits |
| `lakefile.toml` | One new `[[lean_lib]] name = "Package"`; retain existing default targets |

Pinned Lake's default library globs select its named root and dependency
closure. Registering a library does not justify assuming every file below
Package is compiled. Build the audit explicitly and fail if a Lean source
is absent from the intended closure. Production must not import the audit root.
The checker inventories every `Package/**/*.lean` and `Package.lean`,
distinguishes production and audit modules, and verifies each category
against its own root. Unsupported/unclassified files fail coverage rather than
being silently excluded. Package-to-reference imports fail the chosen policy;
Mathlib/Lean dependencies remain allowed.

The checker must parse the import-header forms the Package source policy
accepts (including repeated import directives and `public import` if used), or reject
unsupported forms explicitly. Do not silently skip a header that fails a narrow
regular expression. Include import-syntax variants in the temporary fixtures.

Use a module-origin audit, not a declaration-name prefix filter: future private
or generated names may not start with `NominalPackage`. Audit all declarations
from the Package production closure and inspect their transitive axiom
dependencies. Only `propext`, `Classical.choice` and `Quot.sound` are allowed.
Fail if no production declarations are found. Do not add custom axioms,
admissions or disabled kernel checking.

The existing baseline scripts and audit remain unchanged. A fresh-snapshot
Package build script is not necessary for this first scope; if a fresh project
build is reported, its snapshot must actually include Package and be described
separately. This specification requires no dependency bootstrap or CI.

### Concurrent LaTeX article

The author's subsequent instruction requires the implementation's mathematical
exposition to be written alongside this increment, entirely in LaTeX under
`docs/article/`. The entry point is `docs/article/main.tex`, with included
introduction and foundations sections. Select the central mathematical concepts,
proof ideas and representation choices; relate them to appropriate theories or
systems where this explains the design. Keep the scientific claims and relevant
Lean references accurate. Do not include task IDs, implementation chronology,
review verdicts, audit counts, commands or build outcomes in the manuscript.
Record operational evidence in the roadmap and implementation notes. Compile
the manuscript internally without placing generated files in the source tree.
This adds an accompanying article deliverable without broadening the Lean mathematics.

## Acceptance and verification

Temporary public-import checks must use conclusions of the public equations;
persistent use belongs to future case studies:

1. Normalize a composition/inverse acting on an atom; prove two permutations
   equal with `ext`; swap two distinct atoms and preserve a third.
2. Rename a pair across independent universes, use its projections, and prove
   an ordinary composed map equivariant using the public composition theorem.
3. Transport finite-set membership through a swap/image, explicitly using the
   documented scope at the consumer site.
4. Use `Discrete A X` at nonzero universe, plus empty and singleton data. Show
   its contents are unchanged. Check two distinct atom carriers in the same
   Lean section without ambiguous truth/action inference.
5. Check that inferred scalar operations agree with the `MulAction` used by
   the public theorem, including downstream imports and inherited products.

Temporary negative checks and manuscript arguments establish these boundaries:

1. For distinct a,b, prove the canonical swap moves a while it fixes the
   wrapped value in `Discrete A A`. Do not equate those actions via the bare
   type equivalence.
2. Prove the bare permutation group's left action sends 1 to π, whereas
   conjugating 1 yields 1; exhibit a nonidentity swap to distinguish them.
3. For a plain function with nontrivial codomain action, expose Mathlib's
   pointwise equation and distinguish it from conjugation (identity A→A under
   a nonidentity swap suffices). No nominal function instance is inferred.
4. Check that an opaque arbitrary external carrier has no automatically
   supplied discrete action. A guarded diagnostic should be narrow enough
   to detect the intended missing certificate, not an unrelated type error.

Check the coverage tool against temporary orphan/forbidden-import fixtures and
the audit's zero-coverage and disallowed-axiom detection using isolated tooling
fixtures; no such declarations may enter supported source or import closure.
The audit's selected axiom set can be unit-tested with simulated collected names
without adding actual axioms to Lean files. This tests the check's rejection
logic; the real module audit independently traverses compiled declarations.

Commands to establish during implementation:

```sh
lake build Package +Package.Tests.AxiomAudit
lake env lean Package/Tests/AxiomAudit.lean
python3 Package/Scripts/check-imports.py
lake build Nominal Instances Examples
lake env lean Examples/AxiomAudit.lean
python3 scripts/check-imports.py
git diff --check
```

Compile affected modules while iterating. The final direct audit invocation
must execute even if Lake can reuse its compiled artifact. Print representative
axioms for group closure/swaps, atom action, discrete action and equivariance
composition. Record actual output and declaration/module counts. Report cached
builds separately from direct elaboration and fresh project builds using cached
dependencies. Reference commands check preservation after Lake integration;
they do not certify Package.

Completion requires all public statements above, successful temporary interface
checks, correct
import coverage, successful audit and preserved reference source. An empty
registered target discharges only a fragment of F02. Any unresolved group/action
law remains an open obligation; do not weaken it or expand into support theory
to conceal the gap.

## Subsequent increments and exact review gate

After this slice, review F03b's support-facing permutation laws, then F04 finite/
least support and freshness, F04 canonical quotients, and F05 minimal map/
predicate certificates. Their consumers must establish the new contracts before
PKG-01 implementation. A full NFun catalogue and F06 binder descent are not
prerequisites for this recommended predicate representation.

The author has approved **this F02 + F03a written specification**. Its
implementation plan is approved for native execution. The subsequent correction
reserves persistent usage examples for future case studies; it changes the
validation layout without weakening the mathematical statements. Later support
and predicate increments remain outside this approval. No commit is requested or authorized.
