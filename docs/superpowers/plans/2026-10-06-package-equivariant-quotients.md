# F04d Canonical Equivariant Quotients Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking. Native execution with one fresh independent final review is already selected.

**Goal:** Deliver PKG-F04/F04d: canonical equivariant quotients, support and nominality transfer, the approved supported-fiber characterization, meaningful public-import consumers, audited proofs and matching LaTeX exposition.

**Architecture:** Construct the quotient scalar operation and monoid action explicitly over Mathlib, then derive the nominal projection/support interface from general equivariant-map laws. Add the general surjective nominality and supported-fiber theorems to Nominal.lean without changing its existing interface; specialize the latter to an exact quotient-support intersection formula. All canonical contracts fix the constructed quotient action.

**Tech Stack:** Lean/Mathlib `v4.34.1`; Mathlib revision `d13f23b723b8a846827a245b89c10fc7d3f11612`; Lake, the existing Python import checker and module-origin axiom audit, LaTeX/latexmk.

**Spec:** [Approved F04d specification](../specs/2026-10-06-package-equivariant-quotients-design.md). The author approved the written specification, including the stronger characterization, on 2026-10-06. The author subsequently approved this written plan for native execution. Both approval gates, all four tasks and the independent final review are complete. F04d and the reconciled PKG-F04 are delivered, uncommitted.

## Global Constraints

- Work in `/home/fab/Documents/nominal/nominal` on `fasapa/nominal-package`. Planning inspected HEAD `9c1cb9aa2f9f69d8d801a9864a9f0220b92ea62a` (`Freshness`), with only the existing F04d specification/tracker work uncommitted. Preserve all tracked/untracked and subsequent work.
- Do not commit, push, publish, merge, switch branches, create a worktree, change dependency pins or add CI. Native implementation uses the requested checkout; no branch-integration workflow is part of delivery.
- New implementation belongs under `Package/`. Preserve `Nominal/`, `Instances/`, existing examples and historical `docs/roadmap.md`. Do not repeat earlier implementations or the completed three-agent generalization investigation.
- Preserve `NominalPackage`, `Perm A`, independently selected actions and independent universes. `Nominal A X` remains a proof-only certificate of its action parameter.
- Bare functions retain pointwise action; bare permutations retain left multiplication, with no blanket nominality for either. Finset actions and certificates remain consumer-scoped by `Pointwise`.
- `SMulInvariant` is an ordinary proposition with an explicit setoid and selected source scalar operation. It is not a typeclass or a bundle of actions. Add no global or scoped quotient action/nominality instance.
- Preserve all approved signatures below, including the `letI` action arguments in result types. Use explicit local action installation. The inherited scalar operation of `QuotientAction.mulAction` must be definitionally the supplied `QuotientAction.smul`.
- Raw quotient mapping and `mkHom` require only `SMul`; the action constructor requires a monoid action. No construction needs nominality, infinite atoms, decidable equality, relation decidability, countability or carrier inhabitance.
- Sufficient support and individual finite supportedness reuse `supports_map` and `.map`. General surjective nominality transfer has no infinitude/equality/inhabitance premise. Least-support and freshness results retain `Infinite A`; equality used only inside proofs stays local.
- The stronger characterization is approved and required: `FinitelySupported.mem_support_map_iff` uses one supported preimage and equivariance, without whole-carrier nominality or surjectivity. The quotient intersection is a `Set A`, not an infinitary Finset operation or an exact-support representative selector.
- Keep the constructors and `mkHom` computable; keep existential support/preimage evidence inside proofs. Reuse `Quotient.map`, `Quotient.mk_surjective`, `Function.Surjective.mulAction`, `MulActionHom` and quotient induction/lifting. No `Quotient.out` or parallel quotient representation.
- Only `QuotientAction.smul_mk` and `.mkHom_apply` gain new simp attributes. No reverse simp rule, broad reducibility/instance-priority change or linter suppression.
- Allow only `propext`, `Classical.choice` and `Quot.sound` in audited dependencies. No `sorry`, `admit`, custom axioms, disabled kernel checking or weakened statements.
- Temporary consumers import only `Package`, with `set_option autoImplicit false`, independent universe variables and namespace `F04dChecks`. Keep Pointwise/classical equality local to assertions needing them. Add no standalone Package/Examples layer.
- No quotient-specific freshness theory: use `fresh_map_left/right` and `.freshWith_map_left/right`. Full predicate descent/reflection, SupportsMap/SupportsPred, predicates, Some/Any, supported functions, abstraction, FCB, recursion, generators and other containers remain later work.
- Develop `docs/article/sections/quotients.tex`, labelled `sec:equivariant-quotients`, alongside Lean. Keep task IDs, approval/delivery stories, commands, counts, cache conditions and review verdicts outside the manuscript.
- Root performs all implementation, tests, LaTeX and integration. Obtain one fresh independent read-only final review after integrated validation, with no per-task agent dispatch or additional review gates. Reconcile every overall PKG-F04 criterion before marking that parent complete; do not mark F05 or PKG-01 delivered.

## Review Focus

- **A second action on the quotient:** valid invariance and source nominality must not let canonical projection/certificate laws apply to another selected action. Tasks 1–2 check explicit construction, inherited SMul coherence and negatives with the canonical certificate actually active.
- **Hidden assumptions and universes:** scalar-only actions, non-group monoids, finite atoms and empty carriers must remain accepted at their stated levels. Tasks 1–2 exercise them; Task 4 assigns all exact signatures without ambient classical instances.
- **Supported values in non-nominal carriers:** image support and the fiber theorem must accept individual certificates while refusing reverse supportedness claims. Tasks 2–3 use pointwise constants and the unsupported identity, with no function-space nominality premise.
- **Intersection versus an attaining representative:** support can shrink strictly and the intersection need not be the support of any representative. Task 3 proves the first-component quotient's exact support and the universal-atom quotient's nonattainment, consuming both characterization directions.
- **Freshness for heterogeneous contexts:** both argument positions and nested contexts must work with certificates alone; preservation must not imply reflection. Task 2 exercises both map directions and Finset scoping; Task 3 proves a concrete failure of reflection.

## Files, ownership and order

| File | Responsibility |
| --- | --- |
| `Package/Foundations/QuotientAction.lean` (new) | Task 1: invariant setoid predicate, scalar/monoid constructors and general projection interface |
| `Package/Foundations/Nominal.lean` | Task 2: general surjective nominality theorem; Task 3: general supported-fiber membership theorem; existing declarations/proofs preserved |
| `Package/Foundations/Quotient.lean` (new) | Task 2: nominal projection/support/certificate specializations; Task 3: exact intersection formula |
| `Package.lean` | Tasks 1–2: explicitly export both new modules |
| `Package/Tests/AxiomAudit.lean` | Task 4: representative prints; unchanged complete traversal and axiom policy |
| `Package/README.md` | Task 4: construction calls, exact assumptions, action-selection boundary and stronger characterization |
| `docs/article/sections/quotients.tex` (new) | Tasks 1–3: concurrent mathematical exposition; Task 4: final correspondence |
| `docs/article/main.tex`, `sections/introduction.tex` | Task 1: include quotients after freshness and before perspectives; Tasks 1–3: reconcile abstract/scope |
| `docs/article/sections/support.tex`, `freshness.tex`, `perspectives.tex` | Focused cross-references and reconciliation; retain existing mathematics |
| Active roadmap, approved specification and this plan | Approval/status, executed steps, evidence and overall F04 reconciliation |
| `docs/research/README.md`, `2026-10-05-pkg01-readiness.md`, `2026-10-05-article-plan.md`, `2026-10-06-foundation-generalizations.md` | Task 4: current-state and proposal-disposition reconciliation, preserving dated evidence |

Run **1 → 2 → 3 → 4**. The approved imports are:

```text
QuotientAction.lean:
  Mathlib.Algebra.Group.Action.Defs
  Mathlib.Data.Quot
  Mathlib.GroupTheory.GroupAction.Hom

Quotient.lean:
  Package.Foundations.QuotientAction
  Package.Foundations.Nominal
```

No nominal/freshness dependency enters QuotientAction. No quotient import enters
Nominal or Freshness. Expected source coverage is ten production modules
including Package and one audit, with nine defining modules. Measure the actual
declaration/job counts. No checker, Lake or shared validation-script edit is expected.

Use `/tmp/nominal-f04d-execution/` for snapshots, temporary consumers and logs;
if it already exists, preserve it and choose a fresh suffixed directory, then
substitute that path in the commands below. The seven consumer files are
ActionContracts, ActionCoherence, SupportContracts, FreshnessContracts,
BoundaryContracts, ExactnessContracts and PublicSignatures. Each is standalone
with only `import Package`; copy the minimal needed fixture/proof from retained
evidence instead of importing a scratch module. Preserve original scratch files.

The design inventory and current source are the API evidence; reread if they
change. A failing pre-implementation consumer must identify a missing F04d name,
not a mistaken fixture, unrelated instance failure or admission. Existing-theory
fixtures should already check. The assertion tables give names, exact conclusions
and required consumption; write ordinary Lean proof bodies during execution.

## Task 1: General canonical quotient action and projection

**Files:** Create QuotientAction.lean and quotients.tex; modify Package.lean,
main.tex and introduction.tex. Tests: ActionContracts.lean and the initial
ActionCoherence.lean.

**Interfaces:** Consume Mathlib `Quotient.map`, `.map_mk`, `.mk_surjective`,
`.sound`, `.exact`, `.eq`, `.inductionOn`, `MulActionHom`/`.map_smul` and
`Function.Surjective.mulAction`. Produce these seven approved declarations:

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

```lean
universe u v
variable {M : Type u} {X : Type v} [Monoid M] [MulAction M X]

abbrev QuotientAction.mulAction (s : Setoid X) (hs : SMulInvariant M s) :
    MulAction M (Quotient s)
```

- [x] **Step 1: Record the execution snapshot.** Recheck branch, HEAD, status
  and the approved spec/plan. Fingerprint and preserve all tracked/untracked
  files before editing, including design documents. Record any subsequent work;
  distinguish this increment from the existing diff against HEAD.

- [x] **Step 2: Verify the execution baseline.** Run the Package build, direct
  audit and coverage commands from Task 4, recording actual results and cache
  conditions. Design-session results are historical and are not the execution
  baseline. Do not rerun the completed generalization investigation.

- [x] **Step 3: Write ActionContracts.lean.** Use `q := Quotient.mk s` and
  explicit local installation of the new scalar/action constructors. The
  following are consumer assertions, not new production declarations:

  | Name | Assertion and required use |
  | --- | --- |
  | `scalarProjection`, `projectionScalar` | With only `[SMul M X]`, prove `m • q x = q (m • x)` and its reverse using the two named computation laws. No Monoid or Group premise. |
  | `relatedImages` | From `hxy : s.r x y`, prove `m • q x = m • q y`, consuming compatibility and quotient computation/soundness. |
  | `projectionHom`, `projectionHomHigherOrder` | Use `mkHom.map_smul` and `mkHom_apply` to prove `q (m • x) = m • q x`. For arbitrary `g : Quotient s → Z`, also prove `(g ∘ QuotientAction.mkHom s hs) x = g (q x)`, consuming ordinary function coercion and application. |
  | `projectionPreimage` | For arbitrary c, use `Quotient.mk_surjective` to prove `∃ x, q (m • x) = m • c`. No representative selector or inhabitance premise. |
  | `quotientOne`, `quotientMul` | Under the constructed monoid action, prove `(1 : M) • c = c` and `(m * n) • c = m • (n • c)` for arbitrary c. Consume the inherited action laws. |
  | `inheritedScalar` | For arbitrary c, compare the scalar operation inherited through `MulAction.toSemigroupAction`/`SemigroupAction.toSMul` with `@SMul.smul M (Quotient s) (QuotientAction.smul s hs) m c`; require a definitional equality proof. |
  | `nonGroupMonoid` | For multiplication of Nat on Nat and `s := Setoid.ker (id : Nat → Nat)`, consume the constructor to prove `(2 : Nat) • q 3 = q 6`. This fixture cannot rely on Group Nat. |
  | `compatibilityProofIndependent` | For `hs₁ hs₂ : SMulInvariant M s`, prove equality of the two scalar constructions, and separately of the monoid constructions, using proof irrelevance. |
  | `emptyQuotient` | For `s : Setoid (Discrete A PEmpty.{v+1})` and its vacuous invariance proof, eliminate an arbitrary `c : Quotient s` by projection surjectivity. Keep A and v independent, with no Infinite/Nonempty premise. |
  | `nonInvariantKernel` | Put `s := Setoid.ker (fun n : Nat => if n = 1 then 0 else n)`. Prove `s.r 0 1` and `¬ s.r (Perm.swap 1 2 • 0) (Perm.swap 1 2 • 1)`, then conclude `¬ SMulInvariant (Perm Nat) s`. |

- [x] **Step 4: Write initial ActionCoherence.lean.** Reuse the six action
  equations from `/tmp/nominal-general-freshness-9a13sgo9/ActionCoherence.lean`:
  atom application, componentwise product, discrete fixation, scoped Finset
  image, bare permutation left multiplication and bare function pointwise action.
  Retain Pointwise synthesis checks before/inside/after its local scope and the
  absence of blanket function/permutation nominality. Add `#guard_msgs` checks
  that, with generic M/X, s and valid hs present, neither `SMul M (Quotient s)`
  nor `MulAction M (Quotient s)` is installed by import/evidence alone. Neighboring
  positive checks explicitly install the constructor and consume computation.

- [x] **Step 5: Observe intended missing-interface failures.** Run
  `lake env lean /tmp/nominal-f04d-execution/ActionContracts.lean` and the
  corresponding ActionCoherence command before adding the production module.
  Retain failing sources/logs, separating absent F04d names from fixture or
  already-existing action-policy failures. Do not make negative tests pass merely
  because hs is absent: it must be present in the post-implementation guards.

- [x] **Step 6: Draft the action mathematics.** Create quotients.tex with
  `sec:equivariant-quotients`: invariant equivalence relation, representative
  independence of scalar mapping, identity/composition laws, projection
  computation/equivariance/surjectivity and the explicit-action boundary.
  Explain the monoid generality and Mathlib reuse; cite Pitts Section 1.7 for
  the group case. Include it after freshness and before perspectives and update
  the abstract/introduction to the mathematics being developed.

- [x] **Step 7: Implement the seven interfaces and public export.** Use the
  three approved imports and existing header/namespace style. Define the scalar
  operation by `Quotient.map (m • ·) (hs m)` with s fixed explicitly. Computation
  is definitional; `mkHom` uses Mathlib's existing bundle with underlying q.
  Install the scalar operation inside `mulAction`, then use
  `Function.Surjective.mulAction q Quotient.mk_surjective` with the commuting
  equation. Add only the two approved simp attributes and export the module
  from Package.lean. No global/scoped instance registration.

- [x] **Step 8: Verify the general construction.** Run
  `lake build +Package.Foundations.QuotientAction Package`, then both consumers
  from Steps 3–4. Require exit 0, meaningful positive conclusions, intended
  guarded diagnostics and the definitional inherited-scalar equality. Resolve
  issues locally without strengthening hypotheses or changing action conventions.

- [x] **Step 9: Reconcile and compile the action exposition.** Check the actual
  computation/action proof route, scalar-only versus monoid assumptions, absence
  of choice/inhabitance and selected-action explanation, then run Task 4's article
  command and inspect diagnostics. Do not describe later support results as proved
  until their tasks pass.

## Task 2: General nominality transfer and canonical quotient bounds

**Files:** Add to Nominal.lean; create Quotient.lean; export it from Package.lean;
extend quotients.tex and related abstract/cross-references. Tests: SupportContracts,
FreshnessContracts and BoundaryContracts; extend ActionCoherence.

**Interfaces:** Consume Task 1's constructors/computation and existing
`Equivariant`, `supports_map`, `FinitelySupported.map`, `.support_map_subset`,
`support_map_subset`, `support_eq`, `supports_prod`, general freshness-map laws
and `Quotient.mk_surjective`. Produce these six approved declarations:

```lean
universe u v w
variable {A : Type u} {X : Type v} {Y : Type w}
variable [MulAction (Perm A) X] [MulAction (Perm A) Y]

theorem Equivariant.nominal_of_surjective [Nominal A X] {f : X → Y}
    (hf : Equivariant A f) (hsurj : Function.Surjective f) : Nominal A Y
```

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

- [x] **Step 1: Write SupportContracts.lean.** Install the actual constructed
  quotient action, with `q := Quotient.mk s` and
  `hq := QuotientAction.equivariant_mk A s hs`. Install quotient nominality only
  for tests using carrier notation. Generic elementwise tests have no nominality
  premise on X or the quotient.

  | Name | Assertion and required use |
  | --- | --- |
  | `surjectiveCertificateUse` | Given selected X/Y actions, `[Nominal A X]`, hf and surjectivity, locally install `hf.nominal_of_surjective hsurj`; derive `FinitelySupported A y` from its class projection for arbitrary y. A/X/Y universes are independent. |
  | `projectionEquivariant` | Consume `hq π x` to prove `q (π • x) = π • q x`. |
  | `boundFixesClass` | From `hS : Supports S x` and `hfix : ∀ a ∈ S, π a = a`, conclude `π • q x = q x` through `QuotientAction.supports_mk` and `supports_iff`. S is an arbitrary sufficient bound. |
  | `individualClassSupported` | Obtain `FinitelySupported A (q x)` through `finitelySupported_mk`, without source nominality. Under Infinite A, consume that certificate's supporting least bound in a fixation conclusion. |
  | `individualSupportMember` | From `a ∈ (hx.map hq).support`, infer `a ∈ hx.support` using `hx.support_map_subset hq`. |
  | `independentImageCertificate` | For separately supplied `hy : FinitelySupported A (q x)`, prove `hy.support ⊆ hx.support` using evidence agreement; also compare the `finitelySupported_mk` certificate with `.map`. |
  | `carrierSupportMember` | After installing `QuotientAction.nominal`, use `support_mk_subset A s hs x` to infer source membership from class-support membership. |
  | `mixedSupport` | With only source nominality and individual image evidence, compare the image least support with `support A x` using `support_eq`. |
  | `finiteAtomQuotient` | On `Bool × Bool`, use the kernel of fst and construct quotient nominality, then consume its finite-supportedness projection. No Infinite Bool or least-support expression. |
  | `emptyCarrierNominality` | For arbitrary `s : Setoid (Discrete A PEmpty.{v+1})`, use its vacuous invariance and source certificate to install quotient nominality and consume it at an arbitrary class. Also exercise general surjective nominality transfer through the empty quotient projection. No Nonempty or atom assumptions. |
  | `fixedParameterQuotientBound` | For independently acted-on C/X/Z, equivariant `f : C × X → Z`, `Supports S c`, `Supports T x` and an invariant setoid on Z, prove `Supports (S ∪ T) (q (f (c,x)))` using `supports_prod`, `supports_map` and the quotient bound. Equality is needed only for the displayed union. This certifies the resulting object, not equivariance of the fixed-parameter function. |

- [x] **Step 2: Write FreshnessContracts.lean.** Use the new hq and existing
  general freshness laws; introduce no quotient-specific production lemma.

  | Name | Assertion and required use |
  | --- | --- |
  | `individualFreshLeft` | `hx.FreshWith hc → (hx.map hq).FreshWith hc`, through `.freshWith_map_left`; no carrier nominality or equality. |
  | `individualFreshRight` | `hc.FreshWith hx → hc.FreshWith (hx.map hq)`, through `.freshWith_map_right`, under the same weak assumptions. |
  | `carrierFreshLeft`, `carrierFreshRight` | `Fresh A x c → Fresh A (q x) c` and `Fresh A c x → Fresh A c (q x)`, using `fresh_map_left/right` after explicit quotient nominality installation. |
  | `nestedContextFreshness` | From `(hc.prod (hd.prod he)).FreshWith hx`, preserve freshness after quotienting x and derive `hc.FreshWith (hx.map hq) ∧ hd.FreshWith (hx.map hq) ∧ he.FreshWith (hx.map hq)` using delivered product decomposition. Keep carrier universes independent. |
  | `finsetContextFreshness` | Under local equality/Pointwise, from `Fresh A S x`, derive `∀ a ∈ S, Fresh A a (q x)` via map preservation and the existing Finset context law. Outside this context, generic tests gain neither hypothesis. |
  | `supportedFunctionContext` | Use singleton support certificates for two pointwise constant functions with distinct Nat values to establish general freshness from disjoint bounds; quotient one function using the equality setoid, preserve freshness and consume the result. Do not install Nominal on the function carrier. |

- [x] **Step 3: Write BoundaryContracts.lean.** Adapt the checked Bool,
  unsupported-function and unordered-pair evidence from
  `/tmp/nominal-general-freshness-9a13sgo9/BoundaryContracts.lean` without editing
  that file. Retain the actual `falseHasNoLeastSupport`, `identityNotSupported`,
  `¬ Nominal Nat (Nat → Nat)` and fixed-unordered-pair/actual-support conclusions.
  Add the following consumers:

  | Name | Assertion and required use |
  | --- | --- |
  | `constantFunctionClass` | For pointwise `fun _ : Nat => a`, use its explicit singleton support and `finitelySupported_mk` for the equality setoid. Under Infinite Nat, consume the image support inclusion without nominality of the source carrier. |
  | `unsupportedRepresentativeSupportedClass` | Use `s := Setoid.ker (fun _ : Nat → Nat => ())`. Under its canonical quotient action prove every class invariant, hence empty-supported, and exhibit the class of id as finitely supported while `¬ FinitelySupported Nat (id : Nat → Nat)`. Do not obtain source nominality from the quotient. |
  | `fixedAtomNotEquivariant` | Prove `¬ Equivariant Nat (fun _ : Nat => 0)` using the swap of 0 and 1. This complements the jointly equivariant fixed-parameter object-bound consumer without adding a supported-function API. |

- [x] **Step 4: Extend ActionCoherence.lean with active-candidate negatives.**
  For generic A/X, source nominality, s and valid hs, define the canonical
  action value and install `QuotientAction.nominal A s hs` explicitly as a local
  instance indexed by that precise action. Keep it active while selecting an
  abstract `other : MulAction (Perm A) (Quotient s)`. Guard failure of synthesis
  for `@Nominal A (Quotient s) other` and failed applications of the canonical
  nominality/equivariance theorems to goals with other explicitly supplied.
  Positive neighbors with identical s, hs and source evidence must consume the
  canonical certificate and projection equation. Also use the equality setoid
  on infinite atoms and the trivial action on its quotient: with `a ≠ b`, prove
  `Perm.swap a b • q a ≠ q (Perm.swap a b • a)` and `¬ Equivariant A q` for that
  trivial action. This is a mathematical failure of the contract, not merely
  an instance-search failure or a claim that the other action is non-nominal.

- [x] **Step 5: Observe the intended missing-interface failures.** Run the
  four new/extended files from Steps 1–4 before adding the six declarations.
  Retain logs; baseline Bool/function/action fixtures should pass. Missing
  quotient support/nominality/equivariance names are expected. After production
  exists, verify guarded failures concern mismatched action arguments while the
  valid compatibility and canonical nominality evidence remain active.

- [x] **Step 6: Draft support, nominality and freshness exposition.** Extend
  quotients.tex with sufficient bounds, individual support existence, the general
  surjective nominality argument, quotient specialization and least-support
  inclusion. Explain the separation of infinite-atom leastness from nominality,
  proof-only preimages, general freshness consumers and selected-action policy.
  Distinguish object bounds from later predicate support reflection.

- [x] **Step 7: Add general surjective nominality transfer.** In Nominal.lean,
  place `Equivariant.nominal_of_surjective` immediately after the class in a
  separate context before the existing `[Infinite A]` variables. Eliminate a
  preimage inside the proof for each y and map its nominality projection.
  Preserve all existing declarations, proofs and implicit parameters.

- [x] **Step 8: Implement the five quotient adapters and export.** Create
  Quotient.lean with exactly the two approved imports. Derive equivariance from
  Task 1, finite bounds/evidence from the delivered map laws, nominality from
  Step 7 plus `Quotient.mk_surjective`, and carrier inclusion from
  `support_map_subset`. Each action-dependent result fixes the canonical action
  in its type; only the last uses Infinite A. Export the module from Package.lean.

- [x] **Step 9: Verify support and coherence consumers.** Run
  `lake build +Package.Foundations.Nominal +Package.Foundations.Quotient Package`,
  then SupportContracts, FreshnessContracts, BoundaryContracts and ActionCoherence
  with `lake env lean`. Rerun ActionContracts to check inherited computation
  after both public exports. Require exit 0, intended guard diagnostics and no
  additional equality, nominality, infinitude or inhabitance assumptions.

- [x] **Step 10: Reconcile and compile the exposition.** Compare all new
  support/nominality hypotheses and the selected-action explanation to source;
  verify that general freshness is consumed, not redefined. Compile with
  Task 4's article command and resolve new diagnostics.

## Task 3: Exact supported-fiber characterization and quotient boundaries

**Files:** Add to Nominal.lean and Quotient.lean; extend quotients.tex and focused
related exposition. Tests: ExactnessContracts.lean; extend BoundaryContracts.

**Interfaces:** Consume Task 2's projection/certificates, existing
`.support_map_subset`, `.supports_support`, `.support_minimal`, `.smul`,
`.support_smul`, `support_eq`, `swap_smul_eq_of_supports`, finite avoidance/image
membership, atom/product exact supports and ordinary quotient lifting/induction.
Produce the two approved declarations below; no new freshness or injection API.

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

- [x] **Step 1: Write ExactnessContracts.lean.** Generic fiber assertions
  assume only the first block's hypotheses; quotient assertions install the
  canonical action, with nominality only where the second block requires it.

  | Name | Assertion and required use |
  | --- | --- |
  | `memberInEverySupportedPreimage` | From `a ∈ (hx.map hf).support`, `hz : FinitelySupported A z` and `f z = f x`, conclude `a ∈ hz.support` using the forward direction of `.mem_support_map_iff`. |
  | `memberFromAllSupportedPreimages` | From `∀ z (hz : FinitelySupported A z), f z = f x → a ∈ hz.support`, conclude image-support membership using the reverse direction; no surjectivity or whole-carrier nominality. |
  | `freshSupportedPreimage` | From `a ∉ (hx.map hf).support`, use the characterization to derive `∃ z, ∃ hz : FinitelySupported A z, f z = f x ∧ a ∉ hz.support`. Witness choice remains in Prop. |
  | `sameFiberSameCharacterization` | For another supported z with `f z = f x`, prove `a ∈ (hx.map hf).support ↔ a ∈ (hz.map hf).support` by comparing the two characterizations and support/evidence agreement. No chosen representative is canonicalized. |
  | `quotientIndividualMembership` | Specialize the general theorem and `Quotient.eq` to prove `a ∈ (hx.map hq).support ↔ ∀ z (hz : FinitelySupported A z), s.r z x → a ∈ hz.support`, without nominality of X. Consume each implication. |
  | `arbitraryClassIntersection` | For arbitrary c, use `support_eq_iInter A s hs c` to prove `a ∈ support A c ↔ ∀ x, q x = c → a ∈ support A x`. Consume both implications and the exact set equality. |
  | `partialCarrierFiber` | Apply the general theorem and its quotient specialization to a supported pointwise constant function under the equality-setoid quotient. No Nominal premise on `Nat → Nat`; BoundaryContracts retains proof that this carrier is not nominal. |

- [x] **Step 2: Add the meaningful strictness fixture to ExactnessContracts.lean.**
  Let `s := Setoid.ker (Prod.fst : A × A → A)`, prove invariance, and install
  the canonical action and quotient nominality. Define the temporary lift of fst
  by `Quotient.lift`, prove its computation and equivariance by quotient induction.
  For `[Infinite A]`, `a b : A` and `hab : a ≠ b`, prove:

  ```text
  firstComponentSupport : support A (q (a,b)) = {a}
  originalPairSupport  : support A (a,b) = {a,b}
  firstComponentStrict : support A (q (a,b)) ⊂ support A (a,b)
  retainedAndLost      : a ∈ support A (q (a,b)) ∧
                        b ∉ support A (q (a,b)) ∧ b ∈ support A (a,b)
  freshnessNotReflected : Fresh A b (q (a,b)) ∧ ¬ Fresh A b (a,b)
  ```

  These are consumer names/assertions, not production declarations. Use
  `q (a,b) = q (a,a)` and the delivered product/atom formulas for the upper bound;
  use equivariance of the lifted fst for the lower bound. Do not rely on the
  new intersection theorem, an injectivity generalization, or merely a supplied
  bound. Keep classical equality inside proofs where the public assertion permits.

- [x] **Step 3: Extend BoundaryContracts with nonattainment.** On canonical
  atoms use `s := Setoid.ker (fun _ : A => ())`, its valid invariance proof and
  the actual canonical quotient action. Under Infinite A prove:

  ```text
  universalClassEmpty : ∀ c : Quotient s, support A c = ∅
  noRepresentativeAttains : ∀ c : Quotient s,
    ¬ ∃ x : A, Quotient.mk s x = c ∧ support A x = support A c
  ```

  Every class is invariant; every atom has singleton support by `support_atom`.
  Consume the intersection theorem in a further assertion that an arbitrary atom
  is omitted by some representative's support, using projection surjectivity to
  avoid a vacuous fiber argument. Keep the unsupported-function quotient from
  Task 2 separate: one boundary refutes attainment, the other reverse supportedness.

- [x] **Step 4: Observe the characterization failures.** Run ExactnessContracts
  and BoundaryContracts before adding the two declarations. The strict-decrease,
  invariant-class and nonattainment facts use already delivered interfaces and
  should be independently checked at this point; isolate the expected missing
  characterization names. Retain both failing and passing fixture evidence.

- [x] **Step 5: Draft exactness mathematics.** Extend quotients.tex with the
  two inclusions for the first-component quotient, the general supported-fiber
  theorem, its one-fresh-swap reverse proof and the quotient intersection formula.
  Attribute the quotient result to Pitts, CUP 2013, Proposition 2.30, and state
  the weaker elementwise general parent explicitly. Explain nonattainment,
  failure of reverse supportedness/freshness, independent universes and absence
  of countability. Keep predicate support reflection distinct and deferred.

- [x] **Step 6: Prove the general supported-fiber theorem.** Add
  `.mem_support_map_iff` to Nominal.lean in an Infinite context without a Nominal
  assumption. For the forward direction, map each representative's least bound
  and use minimality at the common image. For the converse, if a is fresh for the
  image, choose b outside `insert a hx.support`; image inclusion makes b fresh
  there too. The existing outside-swap law fixes the image. Set z to the swapped
  source; equivariance keeps it in the fiber, `.smul` certifies it, and delivered
  support transport/inverse-image membership omit a. Equality and Pointwise are
  proof-local. Do not reconstruct transport or a new freshness theory.

- [x] **Step 7: Prove the quotient intersection formula.** In Quotient.lean,
  use quotient induction on arbitrary c, the general theorem, support agreement,
  source nominality and Set extensionality. Relate representatives using
  `Quotient.eq`/`.sound`/`.exact`. Keep the precise canonical action/nominality
  `letI` binders and the dependent subtype index in the approved statement.
  No representative selection or arbitrary-intersection support axiom is involved.

- [x] **Step 8: Verify exactness and dependent consumers.** Run
  `lake build +Package.Foundations.Nominal +Package.Foundations.Quotient Package`,
  then ExactnessContracts, BoundaryContracts, SupportContracts, FreshnessContracts
  and ActionCoherence with `lake env lean`. Require exit 0 and consumption of
  both directions, actual strict least-support inclusion and both distinct
  representative boundaries. Retain all theorem hypotheses unchanged.

- [x] **Step 9: Reconcile and compile the full quotient exposition.** Compare
  the formal general theorem and indexed-intersection statement with the article,
  including the supported-preimage qualification, nonempty fiber argument and
  inability to choose an exact-support representative. Reconcile the abstract,
  introduction and focused support/freshness/perspectives cross-references, then
  compile with Task 4's command and inspect diagnostics.

## Task 4: Integrated validation, documentation and final review

**Files:** Modify audit, Package README, current research-note paragraphs,
active roadmap and this plan/spec; reconcile affected LaTeX. Test:
PublicSignatures.lean plus the six consumers from Tasks 1–3.

**Interfaces:** Consume all **15** approved production declarations and their
existing Mathlib/Package parents. Produce complete coverage of ten production
source modules and one audit, the reconciled article, explicit overall F04
evidence and one resolved independent final review. Counterexample/usage fixtures
remain temporary consumers, not new production APIs.

- [x] **Step 1: Write and check PublicSignatures.lean.** Assign all 15 public
  constants their exact approved types and inspect fully explicit universe/action
  arguments. Include the generic SMul operation, proof-only compatibility,
  inherited monoid action, all canonical `letI` results, absence of Infinite on
  nominality transfer, weak fiber assumptions and the exact Set intersection.
  Do not install ambient classical instances to hide leakage. Run the file with
  `lake env lean`; require exit 0. Recheck evidence independence and action
  negatives with all public imports in place.

- [x] **Step 2: Extend representative audit output.** Add `#print axioms` for
  `SMulInvariant`, `QuotientAction.smul`, `.mulAction`, `.smul_mk`, `.mkHom`,
  `Equivariant.nominal_of_surjective`, `QuotientAction.equivariant_mk`,
  `.supports_mk`, `.finitelySupported_mk`, `.nominal`, `.support_mk_subset`,
  `FinitelySupported.mem_support_map_iff` and `QuotientAction.support_eq_iInter`.
  Preserve whole-production traversal, private/generated coverage, zero-coverage
  rejection and the standard allowlist. Do not replace complete coverage with
  only these representative declarations.

- [x] **Step 3: Run integrated Lean validation after the final production edit.**
  Execute and inspect every result:

  ```sh
  lake build Package +Package.Tests.AxiomAudit
  lake env lean Package/Foundations/QuotientAction.lean
  lake env lean Package/Foundations/Nominal.lean
  lake env lean Package/Foundations/Quotient.lean
  lake env lean /tmp/nominal-f04d-execution/ActionContracts.lean
  lake env lean /tmp/nominal-f04d-execution/ActionCoherence.lean
  lake env lean /tmp/nominal-f04d-execution/SupportContracts.lean
  lake env lean /tmp/nominal-f04d-execution/FreshnessContracts.lean
  lake env lean /tmp/nominal-f04d-execution/BoundaryContracts.lean
  lake env lean /tmp/nominal-f04d-execution/ExactnessContracts.lean
  lake env lean /tmp/nominal-f04d-execution/PublicSignatures.lean
  lake env lean Package/Tests/AxiomAudit.lean
  python3 Package/Scripts/check-imports.py
  ```

  Require exit 0, both new modules reached and only permitted axioms; resolve
  new diagnostics. The direct audit must run even if Lake replays cached output.
  If the checker changes, also run `python3 Package/Scripts/check-imports.py
  --self-test`. Record actual cache conditions and measured counts.

- [x] **Step 4: Reconcile public docs and research dispositions.** Update
  Package/README.md with the explicit constructor/nominality setup, generic map
  reuse, elementwise inclusion, exact intersection and action boundaries.
  Reconcile current guide/readiness/article-plan and generalization-report text:
  only surjective nominality transfer from the seven checked proposals was
  promoted; the scalar projection uses existing MulActionHom without rewriting
  Package Equivariant. The new fiber theorem is separately proved F04d work.
  Preserve dated earlier evidence, the unadopted injection/reflection parts of
  that proposal, and the other six proposal boundaries.

- [x] **Step 5: Review final mathematical correspondence and compile.** Check
  actual definitions, all hypotheses/action arguments, selected declaration names,
  strictness proofs and intersection/nonattainment explanation against the full
  manuscript. From docs/article/, run:

  ```sh
  latexmk -pdf -interaction=nonstopmode -halt-on-error \
    -outdir=/tmp/nominal-package-article-build main.tex
  ```

  Create the output directory if necessary. Keep artifacts outside the source
  tree; require successful compilation, resolved references and no unexplained
  new layout diagnostics. Inspect the resulting quotient exposition separately
  from the successful PDF build. Record whether this invocation rebuilt.

- [x] **Step 6: Check preservation and record execution evidence.** Compare
  tracked/untracked files against the execution snapshot and inspect subsequent
  edits. Verify unchanged reference sources, historical roadmap, pins, action
  conventions and prior work-log text. Check Markdown links/anchors, fences,
  LaTeX references and all changed/new-file whitespace; run `git diff --check`.
  If shared integration affects reference targets, separately run
  `lake build Nominal Instances Examples`, `lake env lean Examples/AxiomAudit.lean`
  and `python3 scripts/check-imports.py`; otherwise record source preservation
  without claiming a reference rebuild. Keep source/logs and exact commands in
  the execution directory and tracker. Leave delivery pending final review.

- [x] **Step 7: Reconcile the overall PKG-F04 obligations.** Prepare an evidence
  row for each overall criterion, without marking the parent complete yet:
  delivered finite/least-support laws; delivered fresh existence/combined
  avoidance; canonical product and the new quotient results; and fixed parameters,
  nested-context avoidance, quotient elimination and least-versus-strong support.
  Use `fixedParameterQuotientBound`/`fixedAtomNotEquivariant`, the new freshness
  consumers, the first-component lift and retained Bool/unordered-pair facts.
  Rerun the retained `AvoidanceContracts.lean` and `GeneralFreshnessContracts.lean`
  under `/tmp/nominal-general-freshness-9a13sgo9/` for the fresh-existence/context
  evidence; if unavailable, reproduce their needed assertions in temporary
  public-import files. F04 quotient descent here is action/projection and
  ordinary relation-respecting elimination; predicate support reflection is
  neither assumed nor counted as delivered. Identify any remaining criterion
  rather than automatically closing the parent because F04d's tests pass.

  ```sh
  lake env lean /tmp/nominal-general-freshness-9a13sgo9/AvoidanceContracts.lean
  lake env lean /tmp/nominal-general-freshness-9a13sgo9/GeneralFreshnessContracts.lean
  ```

- [x] **Step 8: Obtain one fresh independent final review.** Give one read-only
  reviewer on the most capable available model the approved spec/plan,
  execution snapshot and scoped diff, final
  sources including new files, seven consumers and retained-context checks,
  exact validation logs, full manuscript and the overall F04 evidence map.
  Request independent checks of all five Review Focus items, theorem strength,
  Mathlib reuse, actual-action negatives, supported fibers, exactness and
  nonattainment, meaningful consumers, audit coverage, article correspondence
  and preservation. Use the preserved native method with one final reviewer;
  no per-task reviews or new architectural investigation.

- [x] **Step 9: Resolve findings and finish tracking.** Resolve actionable
  review findings natively and rerun affected checks, including dependent
  consumers/article where relevant. Mark F04d DONE only once code, consumers,
  audit, article and this review pass. Mark PKG-F04 complete only if every
  overall criterion has its evidence. Keep F05 and PKG-01 undelivered, record
  cache/verification limits and leave all work uncommitted.

## Planning self-review and handoff

Coverage: Task 1 owns the seven generic interfaces, quotient well-definedness,
action laws and computation; Task 2 owns six support/nominality interfaces,
general freshness consumers and active-candidate coherence; Task 3 owns the two
stronger interfaces, strict decrease and representative boundaries; Task 4 owns
all-signature checks, complete audit, documentation, final article correspondence,
parent-task reconciliation and one independent final review. Every mathematical
task includes concurrent LaTeX development and a compilation checkpoint.

The six declaration blocks above reproduce all 15 approved signatures. Tests
cover the five Review Focus items, finite/empty carriers, independent universes,
fixed parameters and the selected-action distinction. The plan adds no production
API or stronger hypothesis beyond the approved specification. At planning these
tests were execution obligations; the execution record below now supplies their
compilation evidence.

**The specification, including the stronger characterization, is approved.**
The author also approved this concrete native plan before production changes.
Both approval gates are satisfied. Do not ask the author to select a task or
execution method again. Planning validation concerned
document consistency and preservation; the design-session Lean/audit/article
checks are historical to this planning turn.

Planning self-review is complete. A mechanical comparison confirms all eight
specification Lean blocks remain byte-for-byte unchanged and this plan copies
the six declaration blocks covering all 15 interfaces exactly. Document checks
pass for 77 local links, six anchors, balanced fences, changed/new whitespace
and `git diff --check`. The snapshot comparison preserves 126 of 128 existing
files; only specification approval/status and the active tracker changed, with
this plan added. Previous work-log text, branch/HEAD, Lean/article sources,
reference code and pins are preserved. Evidence is under
`/tmp/nominal-f04d-plan-87zxcq02/`. No Lean build, audit or manuscript compilation
was rerun during planning.

## Native execution evidence

Tasks 1–3 and integrated code checks pass. Consumers failed on absent interfaces
before each production addition, then passed with actual conclusions. The
construction, six support/nominality declarations and two characterization
theorems compiled without changing any approved signature. Fully explicit type
assignments cover all 15 declarations and confirm the independent universes,
selected action arguments and absence of extra assumptions.

Scratch corrections preserve the planned mathematics: use explicit local let
bindings instead of a parametrized instance with uninferable hs; expose a Nat
kernel equality to `decide` instead of using an unimported tactic; match Lean's
actual guarded diagnostic; and retain equality on the visible `{a,b}` consumer
formula while keeping it proof-local in strict inclusion. Unused proof-binder
names and local article line breaks were corrected without linter/layout policy
changes. No production fix or mathematical deviation was needed.

The final Package build passes 974 jobs. Direct affected-module checks, all
seven main consumers and two retained freshness/avoidance consumers pass. The
direct audit covers 245 production declarations in nine defining modules with
the standard three axioms only; the unchanged import checker reaches ten
production sources and one audit. The article has 26 pages and a clean final
log, after compilation during each mathematical task. These results use cached
dependencies and incremental project builds, not a fresh whole-project build,
dependency bootstrap or rebuild of unchanged reference targets.

The execution snapshot, task briefs, progress ledger, red/green sources/logs,
exact command/result JSON files and consumers are under
`/tmp/nominal-f04d-execution/`. Preserve them: all changes remain uncommitted.
Task 4's final document/preservation checks, overall F04 evidence map and the
fresh independent review now pass. The review found no Critical, Important or
Minor issues; no fix pass or further review was needed. It independently
compiled fresh Package oleans under /tmp with the repository's project oleans
excluded, then checked the seven consumers, two retained context consumers,
245-declaration audit and import coverage. Its fresh article build has 26 pages
and a clean log. Pinned dependencies were cached; no dependency bootstrap or
reference-library rebuild is claimed. The report is retained at
`/tmp/nominal-f04d-final-review-3fVxOr/report.md`.

Final document checks cover eight Markdown files, 182 links, 13 anchors,
59 LaTeX labels, signature-block preservation and changed/new whitespace.
The snapshot preserves 116 of 129 original files, with 13 intended edits and
three additions. The prior work log, reference sources, pins, historical
roadmap, branch and HEAD are unchanged; original Nominal source is extended
without alteration. All four tasks are complete. F04d and the reconciled
PKG-F04 are DONE; F05 and PKG-01 remain undelivered, and all changes remain
uncommitted as requested.
