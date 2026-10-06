# F04b Nominality and Least Support Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking. The author approved this plan for native execution on 2026-10-06.

**Goal:** Deliver PKG-F04/F04b: proof-only nominality and canonical least finite support, with elementwise and carrier interfaces, meaningful public-import consumers, audited proofs and matching LaTeX exposition.

**Architecture:** Add one foundation module over delivered F04a. Use Mathlib's well-founded Finset inclusion order to obtain an inclusion-minimal support, then `supports_inter` to prove leastness. Derive the elementwise laws first and expose carrier operations as thin adapters, preserving every selected action.

**Tech Stack:** Lean/Mathlib `v4.34.1`; Mathlib revision `d13f23b723b8a846827a245b89c10fc7d3f11612`; Lake, existing Python import checker and module-origin axiom audit, LaTeX/latexmk.

**Spec:** [Approved F04b specification](../specs/2026-10-06-package-least-support-design.md). The author approved it on 2026-10-06. Work remains in `/home/fab/Documents/nominal/nominal`, branch `fasapa/nominal-package`, at inspected HEAD `34a83358739ab962e2b9d2035a21d67b2a896071`. No production implementation is authorized by specification approval alone.

**Execution status:** The author subsequently approved this plan for native
execution. All four tasks, integrated Lean/LaTeX validation and the independent
final review pass. F04b is complete; all changes are uncommitted.

## Global Constraints

- Preserve namespace `NominalPackage`, `Perm A`, independent atom/carrier universes, all selected actions and scoped finite-set images.
- New implementation belongs under `Package/`, with direct pinned Mathlib dependencies. Preserve `Nominal/`, `Instances/`, their examples and the historical `docs/roadmap.md`.
- Work in the existing requested checkout. Preserve all tracked/untracked and subsequent work, including delivered F04a and the later article edits. No branch switch, commit, push, publication, merge, dependency upgrade or CI change is authorized.
- Retain Lean/Mathlib `v4.34.1`, the manifest revision above, Lake targets, audit/checker policies and shared validation scripts. Do not reopen F02/F03a/F03b/F04a or repeat their proofs.
- `Nominal A X : Prop` has only the field `finitelySupported : ∀ x, FinitelySupported A x`. It takes the selected action as a parameter, has no `outParam`, and requires neither `Infinite A` nor `DecidableEq A`.
- Elementwise least-support declarations require `Infinite A` and explicit `hx`, never carrier-wide nominality. Existence and noncomputable choice must not acquire `DecidableEq A`.
- Retain `DecidableEq A` only on the visible finite-set transport equations; consumers explicitly open `Pointwise`. No commuting-action or countability assumption is permitted.
- `support A x` and every carrier-level theorem take A explicitly. `support` has binder order A, X, selected action, infinitude, nominality, x. Its value is `(Nominal.finitelySupported (A := A) x).support`.
- Only `propext`, `Classical.choice` and `Quot.sound` may occur in audited dependencies. No `sorry`, `admit`, custom axioms, disabled kernel checking or weakened statements.
- Do not globally unfold choice, nominality or quantified support predicates via simp. No broad instance, reducibility or linter changes.
- Temporary consumers import only `Package`; no standalone `Package/Examples` layer. Local certificates and concrete bounds are allowed in those consumers.
- F04c retains canonical nominal instances, exact atom/discrete/product/Finset support formulas and freshness. F04d retains quotients. F05/PKG-01 retains supported functions/predicates and Some/Any; binders, FCB, recursion and generators remain later work.
- Develop `sec:least-support` in `docs/article/sections/support.tex` alongside Lean. Keep task/status/build/review narratives outside the manuscript, under the current publication policy.
- Implement natively, then obtain one fresh independent final review of F04b. No per-task agent delegation or repeated design review is planned. Keep PKG-F04 open for F04c/F04d.

## Review Focus

- **Assumption leakage:** finite-atom nominality and generic elementwise support must not inherit hidden equality, infinitude or nominal-carrier premises. Task 1 tests Bool and arbitrary actions; Task 4 assigns exact public signatures.
- **Leastness versus a chosen bound:** support must lie inside an arbitrary supporting T, even when T is unrelated to the witness used for `hx`. Task 1 checks arbitrary bounds, independent candidates and the Bool obstruction.
- **Evidence and atom inference:** changing proofs for the same selected action must not change support, and explicit A must select the intended atom action. Tasks 1/3 test distinct witnesses, explicit class certificates and two atom parameters with independent universes.
- **Supported elements in non-nominal carriers:** the elementwise operation and image bound must work without nominality of either carrier. Tasks 1/2 test pointwise constants alongside an unsupported identity and generic image membership.
- **Transport and action coherence:** least-support transport needs both containments and inverse transport; bare functions and permutations must retain their existing actions. Tasks 2/4 check those conclusions and the six action equations.

## Files, ownership and order

| File | Responsibility |
| --- | --- |
| `Package/Foundations/Nominal.lean` (new) | Tasks 1–3: certificate, elementwise construction/laws, carrier adapters |
| `Package.lean` | Task 1: export Nominal after Support |
| `Package/Tests/AxiomAudit.lean` | Task 4: representative prints, unchanged whole-production traversal |
| `Package/README.md` | Task 4: actual API, assumptions, usage and deferred scope |
| `docs/article/sections/support.tex` | Tasks 1–3: concurrent `sec:least-support`; Task 4: mathematical reconciliation |
| `docs/article/main.tex`, `docs/article/sections/introduction.tex` | Tasks 1–3: abstract/scope/cross-references; Task 4: final correspondence |
| `docs/article/sections/perspectives.tex` | Task 3: reconcile the support-witness comparison |
| `docs/nominal-package-roadmap.md`, this plan, approved spec | Approval/status, executed steps, verification evidence and limits |
| `docs/research/README.md`, `docs/research/2026-10-05-pkg01-readiness.md`, `docs/research/2026-10-05-article-plan.md` | Task 4: update current readiness and article correspondence; preserve historical evidence |

Run **1 → 2 → 3 → 4**. Root owns all edits. The mathematical tasks share one
module and build on one another; the only independent reviewer is the final
read-only reviewer after integrated validation. Use the execution snapshot
to distinguish F04b changes from existing F04a work in the diff against HEAD.

Temporary consumers use `/tmp/nominal-f04b-execution/` and namespace `F04bChecks`.
If that directory exists, preserve it and use a fresh suffixed path, recording
the substitution in all commands. The test rows below specify named assertions
to prove, not production declarations or permission to insert placeholders.
Use independently quantified universes and `set_option autoImplicit false`.

## Task 1: Nominality and elementwise least-support construction

**Files:** Create Nominal.lean; modify Package.lean, support.tex, article
introduction/abstract. Temporary tests: `ElementwiseContracts.lean` and
`BoundaryContracts.lean`.

**Interfaces:** Consume `FinitelySupported A x := ∃ S : Finset A, Supports S x`,
`supports_iff`, `supports_mono`, `supports_inter`, `supports_empty_iff`,
`Supports.finitelySupported`, and the existing action/swap equations. Mathlib
supplies `Finset.wellFoundedLT`, `exists_minimal_of_wellFoundedLT`,
`Minimal.prop`, `Minimal.le_of_le` and intersection containments. Produce:

```lean
class Nominal (A : Type u) (X : Type v) [MulAction (Perm A) X] : Prop where
  finitelySupported : ∀ x : X, FinitelySupported A x

-- All following declarations: independent A/X, selected action, [Infinite A].
-- No [DecidableEq A] or [Nominal A X]; {x : X} and {S : Finset A}.
theorem FinitelySupported.exists_least_support (hx : FinitelySupported A x) :
    ∃! S : Finset A, Supports S x ∧
      ∀ T : Finset A, Supports T x → S ⊆ T
noncomputable def FinitelySupported.support (hx : FinitelySupported A x) : Finset A
theorem FinitelySupported.supports_support (hx : FinitelySupported A x) :
    Supports hx.support x
theorem FinitelySupported.support_minimal (hx : FinitelySupported A x)
    (hS : Supports S x) : hx.support ⊆ S
theorem FinitelySupported.supports_iff_support_subset
    (hx : FinitelySupported A x) (S : Finset A) :
    Supports S x ↔ hx.support ⊆ S
theorem FinitelySupported.support_unique (hx : FinitelySupported A x)
    (hS : Supports S x) (hmin : ∀ T : Finset A, Supports T x → S ⊆ T) :
    hx.support = S
theorem FinitelySupported.support_eq (hx hx' : FinitelySupported A x) :
    hx.support = hx'.support
```

- [x] **Step 1: Record the execution baseline.** Read the approved spec/plan;
  recheck branch, HEAD and status, fingerprint all existing tracked/untracked
  files, and retain their pre-edit contents for scoped review. Reuse the design
  API inventory; reread source if it changed. Run the Package build/audit/import
  commands from Task 4 and record actual cache conditions before editing.

- [x] **Step 2: Write the elementwise consumers.** In ElementwiseContracts,
  use only `import Package` and the generic assumptions above. Prove these
  named assertions using the indicated results:

  | Name | Assertion and consumption |
  | --- | --- |
  | `leastBoundFixes` | For hx, π and `hfix : ∀ a ∈ hx.support, π a = a`, conclude `π • x = x` using `hx.supports_support` and `supports_iff`. |
  | `memberOfEveryBound` | From `hS : Supports S x` and `ha : a ∈ hx.support`, conclude `a ∈ S` using `hx.support_minimal hS`; T/S is arbitrary, not extracted from hx. |
  | `fixesFromLeastInclusion` | From `hsub : hx.support ⊆ S` and π fixing S pointwise, conclude `π • x = x` using the reverse `hx.supports_iff_support_subset S`. |
  | `leastCandidatesEqual` | If S and T each support x and are contained in every finite support of x, conclude `S = T` using uniqueness from `hx.exists_least_support`. |
  | `candidateAgreement` | For the same least-candidate premises on S, conclude `hx.support = S` via `hx.support_unique`. |
  | `differentWitnesses` | Given `hS : Supports S x` and `hT : Supports T x`, prove `hS.finitelySupported.support = hT.finitelySupported.support` using `.support_eq`, without unfolding choice. |

- [x] **Step 3: Write the boundary consumers.** In BoundaryContracts, prove:

  | Name | Assertion and consumption |
  | --- | --- |
  | `boolNominality`, `boolCertificateUse` | Construct `Nominal Bool Bool` from singleton bounds; locally install it and conclude `FinitelySupported Bool b` from `Nominal.finitelySupported (A := Bool) b`, with no infinitude premise. |
  | `falseSupportedByFalse`, `falseSupportedByTrue`, `falseNotEmptySupported` | Retain the three F04a Bool conclusions, adapting the already checked proofs in `/tmp/nominal-f04a-execution/IntersectionContracts.lean` into this standalone public-import consumer. |
  | `falseHasNoLeastSupport` | Prove `¬ ∃ S : Finset Bool, Supports S false ∧ ∀ T : Finset Bool, Supports T false → S ⊆ T`; both singleton bounds force S empty, contradicting the preceding result. |
  | `constantFunctionSupported` | For generic A and `a : A`, prove `FinitelySupported A (fun _ : A => a)` under the ordinary pointwise action, using the explicit singleton bound; no nominality instance. |
  | `constantLeastBoundFixes` | Under `[Infinite A]`, use that certificate's least support and a pointwise fixer to conclude `π • (fun _ : A => a) = (fun _ : A => a)`. |
  | `identityNotSupported` | Prove `¬ FinitelySupported Nat (id : Nat → Nat)`. For an alleged finite bound S, obtain two distinct atoms outside S using `Finset.exists_notMem`, apply the outside swap, and evaluate the resulting function equality at one endpoint. |
  | `functionCarrierNotNominal` | Prove `¬ Nominal Nat (Nat → Nat)` by applying its projection to id and using `identityNotSupported`; the constant consumer still succeeds on that carrier. |

- [x] **Step 4: Observe the intended missing-interface failures.** Run
  `lake env lean /tmp/nominal-f04b-execution/ElementwiseContracts.lean` and
  the corresponding BoundaryContracts command before adding Nominal.lean.
  Retain failing sources/logs; isolate missing F04b names from fixture mistakes.
  Existing-support-only Bool and identity-obstruction proofs should already
  check. Do not add admissions or alter production assumptions to make fixtures run.

- [x] **Step 5: Draft the construction mathematics.** Add the subsection
  `sec:least-support` to support.tex: the mathematical nominality certificate,
  unique least support for an individual supported element over infinite atoms,
  the minimal-bound/intersection argument, noncomputable choice and witness
  independence. Reference the existing intersection proposition and extend the
  Bool explanation to failure of leastness. Attribute the reused Mathlib order
  infrastructure and briefly compare cardinality minimization. Update the
  abstract/introduction consistently; main.tex already includes support.tex.

- [x] **Step 6: Implement the certificate and construction.** Create
  `Package/Foundations/Nominal.lean` with the existing header/namespace conventions
  and only `Package.Foundations.Support` and `Mathlib.Order.Minimal` imports.
  Keep the class outside the Infinite section. Obtain a minimal supporting S
  from hx; locally use classical equality, intersect S with any support T,
  and apply `Minimal.le_of_le` to obtain `S ⊆ S ∩ T ⊆ T`. Prove uniqueness by
  antisymmetry. Choose from the existence theorem, derive the supporting and
  minimality laws, use monotonicity for the iff, and prove both equality laws.
  Export the module through Package.lean. Leave Support.lean unchanged.

- [x] **Step 7: Verify the construction.** Run
  `lake build +Package.Foundations.Nominal Package`, then both temporary
  consumers directly. Require exit 0 and resolve new diagnostics. Confirm the
  existential theorem and choice require no public equality instance. Inspect
  the task diff against the execution baseline; leave changes uncommitted.

- [x] **Step 8: Reconcile and compile the article.** Match this subsection to
  the checked declarations, hypotheses and actual proof route. Run Task 4's
  manuscript command and inspect the final log. No future transport/image
  theorem is claimed as a checked Package result yet.

## Task 2: Elementwise transport, empty support and images

**Files:** Modify Nominal.lean, support.tex and article scope text where needed.
Temporary test: `NaturalityContracts.lean`.

**Interfaces:** Consume Task 1's support/minimality/independence laws and F04a's
`supports_smul`, `supports_empty_iff`, `supports_map`, `hx.smul π`, `hx.map hf`.
Produce, with independent A/X/Y and selected actions:

```lean
-- [Infinite A], no nominality or decidable-equality premise:
theorem FinitelySupported.support_eq_empty_iff (hx : FinitelySupported A x) :
    hx.support = ∅ ↔ ∀ π : Perm A, π • x = x
theorem FinitelySupported.support_map_subset (hx : FinitelySupported A x)
    (hf : Equivariant A f) : (hx.map hf).support ⊆ hx.support

-- Add only [DecidableEq A] and open scoped Pointwise:
theorem FinitelySupported.support_smul (hx : FinitelySupported A x)
    (π : Perm A) : (hx.smul π).support = π • hx.support
```

- [x] **Step 1: Write the consuming assertions.** NaturalityContracts imports
  only Package. Keep equality/Pointwise assumptions confined to transport.

  | Name | Assertion and consumption |
  | --- | --- |
  | `transportMembership` | From `ha : a ∈ (hx.smul π).support`, conclude `π⁻¹ a ∈ hx.support` using `.support_smul` and `Perm.mem_smul_finset`. |
  | `inverseTransport` | Prove `π⁻¹ • (hx.smul π).support = hx.support` by the transport equation and inverse cancellation. |
  | `otherTransportCertificate` | For `hπx : FinitelySupported A (π • x)`, prove `hπx.support = π • hx.support` using `.support_eq` and `.support_smul`. |
  | `emptyImpliesFixation`, `invarianceImpliesEmpty` | From `hx.support = ∅`, conclude `π • x = x` for arbitrary π; from universal invariance, conclude `hx.support = ∅`. Consume both directions of `.support_eq_empty_iff`. |
  | `imageMember`, `otherImageCertificate` | From `ha : a ∈ (hx.map hf).support`, derive `a ∈ hx.support`; for an independent `hy : FinitelySupported A (f x)`, prove `hy.support ⊆ hx.support`. Neither carrier has a nominality instance. |
  | `constantImageStrict` | Put `f := fun _ : Nat => (Discrete.mk true : Discrete Nat Bool)`; supply equivariance and `h0 : FinitelySupported Nat (0 : Nat)`. Prove `(h0.map hf).support = ∅` and `h0.support ≠ ∅`, hence `(h0.map hf).support ⊂ h0.support`. Use swap 0 1 for noninvariance of 0, without an exact atom-support formula. |

- [x] **Step 2: Observe the intended failures.** Run
  `lake env lean /tmp/nominal-f04b-execution/NaturalityContracts.lean` before
  implementing these three results; retain the missing-interface log and
  separately fix any fixture errors.

- [x] **Step 3: Draft the law statements and explanations.** Extend
  `sec:least-support` with transport, empty-support equivalence and image
  inclusion. Explain inverse transport and potentially strict inclusion,
  referring to the existing conjugation argument rather than repeating it.
  Explain that element fixation yields setwise preservation of support, not
  pointwise fixation of its atoms; retain F04c's counterexample/formula boundary.

- [x] **Step 4: Prove the three laws.** Empty support uses Task 1 minimality
  and `supports_empty_iff`; images use `supports_map hf hx.supports_support`
  and leastness of `hx.map hf`. For transport, one containment follows from
  `supports_smul hx.supports_support π`; the other transports the renamed
  least bound back by π⁻¹ and applies leastness for x. Pinned Mathlib's
  `Finset.smul_finset_subset_iff` states `π • S ⊆ T ↔ S ⊆ π⁻¹ • T`
  (`Algebra/Group/Action/Pointwise/Finset.lean:183`) and can discharge the final
  image containment. Use inverse action laws; add no commuting-action premise.

- [x] **Step 5: Check the Lean deliverable.** Run
  `lake build +Package.Foundations.Nominal Package`, then NaturalityContracts,
  ElementwiseContracts and BoundaryContracts. Require exit 0 with their
  original assumptions and the strict-inclusion conclusion intact.

- [x] **Step 6: Reconcile and compile the exposition.** Match statements,
  certificate arguments and atom assumptions to Lean; compile with the Task 4
  command and resolve new manuscript diagnostics.

## Task 3: Nominal-carrier convenience and agreement

**Files:** Modify Nominal.lean, support.tex, perspectives.tex and article
scope/cross-references. Temporary test: `CarrierContracts.lean`.

**Interfaces:** Consume `Nominal.finitelySupported` and all Task 1/2 elementwise
laws. Produce these declarations; A is explicit in each, with independent X/Y:

```lean
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

- [x] **Step 1: Write the carrier consumers.** Use only Package, temporary
  local certificates and ordinary selected actions in CarrierContracts:

  | Name | Assertion and consumption |
  | --- | --- |
  | `carrierElementAgreement` | With `[Nominal A X]` and any hx, prove `support A x = hx.support` via `support_eq A x hx`. |
  | `nominalCertificateIndependence` | For fixed `act : MulAction (Perm A) X`, `inf : Infinite A` and `n₁ n₂ : @Nominal A X act`, prove `@support A X act inf n₁ x = @support A X act inf n₂ x`. Check the prescribed binder order. |
  | `carrierBoundFixes`, `carrierMemberOfBound` | From `support A x ⊆ S` and a pointwise fixer of S, conclude fixation of x via the carrier iff. From `Supports S x` and membership in `support A x`, conclude membership in S using `support_minimal A`; also consume `supports_support A x` directly. |
  | `twoAtomParameters` | For unrelated A/B with `[Infinite A]` and `[Infinite B]`, and one X carrying both selected actions/certificates, prove `Supports (support A x) x ∧ Supports (support B x) x`, with each conjunct using its intended atom type. Keep all universes independent. |
  | `carrierTransportBack` | With Pointwise/equality, prove `π⁻¹ • support A (π • x) = support A x` via `support_smul A π x`; also consume its forward equation. |
  | `carrierEmptyFixes`, `carrierInvariantEmpty` | Consume each direction of `support_eq_empty_iff A x` to prove fixation by an arbitrary π or equality to empty. |
  | `carrierImageMember` | With local nominality certificates for both carriers, `a ∈ support A (f x)` implies `a ∈ support A x` using `support_map_subset A hf x`. |
  | `mixedImageBound` | With only X nominal, prove `((Nominal.finitelySupported (A := A) x).map hf).support ⊆ support A x` using the elementwise image law and agreement; no nominality of Y. |

- [x] **Step 2: Observe the expected failures.** Run
  `lake env lean /tmp/nominal-f04b-execution/CarrierContracts.lean` before
  adding the wrappers; record missing F04b carrier names independently of
  fixture errors or pre-existing library names with similar spelling.

- [x] **Step 3: Draft the certificate-interface explanation.** Explain the
  primary elementwise operation, convenient carrier operation and their
  agreement in `sec:least-support`. Reconcile perspectives.tex's comparison
  between supplied witnesses and canonical support. Keep every action fixed
  when comparing certificates, and include no claim about later canonical
  instances or strong support. Update abstract/introduction as needed.

- [x] **Step 4: Implement the thin adapters.** Define support using the exact
  nominality-projection expression in Global Constraints, with the prescribed
  binder order. Derive agreement and all wrappers from the corresponding
  elementwise laws. Introduce no new choice, action instance or global nominal
  instance. Use ordinary proofs/rewrite lemmas, leaving clients independent
  of the selector's implementation.

- [x] **Step 5: Verify all current consumers.** Run
  `lake build +Package.Foundations.Nominal Package`, then CarrierContracts and
  the three earlier files. Require exit 0; confirm the mixed-image and explicit
  certificate tests succeed without changing any approved signature.

- [x] **Step 6: Reconcile and compile the article.** Check mathematical
  correspondence, relevant names, atom assumptions and witness/action
  distinctions, then run the manuscript command and inspect its final log.

## Task 4: Public acceptance, audit, documentation and final review

**Files:** Modify audit, Package README, active roadmap, this plan/spec and the
three research guides in the file table. Reconcile all affected article files.
Temporary tests: `PublicSignatures.lean`, `ActionCoherence.lean`, and Tasks 1–3 files.

**Interfaces:** Consume all **19** approved public declarations from Tasks 1–3,
plus the generated Nominal constructor/projection. Produce verified coverage
of six production source modules including the root, one audit module and all
new production declarations; declaration/job counts are measured, not prescribed.

- [x] **Step 1: Check exact signatures and action preservation.** Assign
  every public constant to its exact approved type in PublicSignatures, including
  independent universe variables, explicit A on wrappers and absence of extra
  instances. Use fully explicit `@` assignments and inspect universe/binder
  output; do not mask missing assumptions with a surrounding `classical` block.
  In ActionCoherence prove the six equations
  `π • a = π a`, `π • (x,y) = (π • x,π • y)`, `π • S = S.image π`,
  `π • (Discrete.mk x : Discrete A X) = Discrete.mk x`,
  `(π • σ : Perm A) = π * σ`, and `(π • f) x = π • f x` for bare functions.
  Keep Pointwise/equality scoped; reuse the equivalent retained F04a file if
  present. Run both files directly and require exit 0.

- [x] **Step 2: Extend representative audit output.** Add qualified
  `#print axioms` for `FinitelySupported.exists_least_support`, `.support`,
  `.supports_support`, `.supports_iff_support_subset`, `.support_smul`,
  `.support_eq_empty_iff`, `.support_map_subset`, and the carrier `support_eq`.
  Preserve the module-origin traversal, zero-coverage rejection and standard
  allowlist. Confirm Nominal.lean is reached from the public root and audit;
  do not restrict the traversal to these representatives.

- [x] **Step 3: Run integrated Lean validation after the last production edit.**
  Execute and inspect every result:
  ```sh
  lake build Package +Package.Tests.AxiomAudit
  lake env lean Package/Foundations/Nominal.lean
  lake env lean /tmp/nominal-f04b-execution/ElementwiseContracts.lean
  lake env lean /tmp/nominal-f04b-execution/BoundaryContracts.lean
  lake env lean /tmp/nominal-f04b-execution/NaturalityContracts.lean
  lake env lean /tmp/nominal-f04b-execution/CarrierContracts.lean
  lake env lean /tmp/nominal-f04b-execution/PublicSignatures.lean
  lake env lean /tmp/nominal-f04b-execution/ActionCoherence.lean
  lake env lean Package/Tests/AxiomAudit.lean
  python3 Package/Scripts/check-imports.py
  ```
  Require exit 0, all new-module coverage, permitted axioms only and no
  unexplained diagnostics. Retain the existing F03a ActionContracts and
  NegativeContracts checks when available; otherwise reproduce their intended
  action distinctions locally. If the checker changes, also run
  `python3 Package/Scripts/check-imports.py --self-test`. Record cache conditions.

- [x] **Step 4: Reconcile public documentation and manuscript claims.** Update
  Package/README.md and the current paragraphs of the three research guides to
  reflect checked F04b, while preserving historical records and F04c/F04d/F05
  boundaries. Compare every manuscript hypothesis, selected declaration and
  proof explanation with actual Lean results. Keep operational evidence in
  trackers and notes, not in the article. No unimplemented canonical formulas
  or unconditional support operation is described as delivered.

- [x] **Step 5: Compile and inspect the final manuscript.** From docs/article/:
  ```sh
  latexmk -pdf -interaction=nonstopmode -halt-on-error \
    -outdir=/tmp/nominal-package-article-build main.tex
  ```
  Require successful compilation, resolved references and no new unexplained
  layout diagnostics. Inspect the resulting least-support text and the
  mathematical correspondence separately from compilation. Keep generated
  artifacts outside the source tree and report whether the invocation rebuilt.

- [x] **Step 6: Check preservation and document evidence.** Compare against
  the execution snapshot, including untracked files. Verify F04a source, reference
  code, old roadmap, existing unrelated work and pins are preserved; inspect
  current status for subsequent user edits. Check local links/anchors, fences
  and untracked-file whitespace; run `git diff --check`. If shared integration
  changes affect reference targets, separately run `lake build Nominal Instances
  Examples`, `lake env lean Examples/AxiomAudit.lean` and
  `python3 scripts/check-imports.py`. Otherwise record source preservation
  without claiming a reference rebuild. Record actual commands, measured counts
  and cache limits in the active roadmap/plan; leave completion pending review.

- [x] **Step 7: Obtain the fresh independent final review.** Give one read-only
  reviewer the approved spec/plan, F04b diff against the execution snapshot,
  final source including untracked additions, six consumers, validation evidence
  and article. Request independent checks of theorem strength, all five Review
  Focus items, code/article correspondence and preservation, not only compilation.
  Resolve findings natively and rerun affected checks. Mark F04b DONE only when
  code, consumers, audit, article and this review pass. Keep PKG-F04 IN PROGRESS
  for F04c/F04d, update evidence and leave all changes uncommitted.

## Planning self-review and handoff

Coverage maps certificate/construction/leastness/uniqueness/witness independence
and finite/non-nominal boundaries to Task 1; elementwise transport, empty support
and image inclusion to Task 2; carrier operations, agreement, atom selection and
mixed clients to Task 3; exact signatures, action preservation, complete audit,
documentation, article correspondence and independent review to Task 4.
All five Review Focus items have owning consumers. LaTeX drafting is assigned
to every mathematical task, with final reconciliation after the proofs.

Self-review checked specification coverage, exact types and arguments, step
specificity, missing edge cases and proportion. This plan preserves the approved
mathematical contract and adds no production API beyond its 19 declarations.
The assertions are implementation-time obligations, not already checked Lean
consumers. No production or article source has been changed by planning.

Planning checks passed for the three documents: 56 local links, six anchors,
balanced fences, whitespace and `git diff --check`. A text comparison confirms
that all 19 planned declaration signatures match the approved specification,
whose Lean blocks are unchanged. The planning snapshot comparison preserves
113 of 115 existing files; only the F04b spec status and active tracker changed,
alongside this new plan. The historical work log, branch and HEAD are preserved.
Checks and snapshots are under `/tmp/nominal-f04b-plan-0zdaxrx4/`.

**Native execution and this written plan are approved.**
Use executing-plans in this checkout and proceed in task order;
do not ask which task or execution method to use. Earlier specification/design
baseline builds and audit/LaTeX results remain historical to this planning turn.
Planning validation is limited to document checks and preservation comparison.

## Native execution evidence

Tasks 1–3 followed the consumer-first sequence: the new assertions failed on
the missing interfaces, then passed after their corresponding implementations.
Article statements and explanations were developed and compiled in each task.
The production proofs compiled without additional hypotheses. Consumer style
warnings and one overlong LaTeX paragraph were corrected locally; linter and
layout policies were not relaxed. A fully explicit signature check caught the
carrier `support_minimal` binder order; explicit theorem-local binders restored
the exact approved order, and all signature/consumer checks then passed.

The integrated 970-job Package build, direct Nominal source check, all six
temporary consumers, direct audit, import checker and retained F03a action and
negative consumers pass. The direct audit covers 132 declarations in five
defining modules with standard axioms only; coverage reaches six production
source modules and one audit. The reconciled article has 16 pages and a clean
final log. The final manuscript invocation reused the outputs built during
the mathematical tasks. These checks use cached dependencies and rebuild
changed project modules; no fresh whole-project build, dependency bootstrap
or rebuild of unchanged reference targets is claimed.

Scratch proofs, red/green logs, execution snapshot and ledger remain under
`/tmp/nominal-f04b-execution/`. Preserve them: no commits provide an alternative
record. Task 4's document/preservation checks and independent final review now
pass. The review found no actionable Critical, Important or Minor issues and
independently reran the cached Package build, direct Lean/audit/consumer checks,
import coverage, document/preservation checks and a fresh 16-page article build.
No fix pass was required. Review evidence is under
`/tmp/nominal-f04b-independent-review/`.

Final document checks cover seven Markdown files, 146 links, 13 anchors and
43 LaTeX labels. Preservation checks identify exactly 13 intended changes to
the 116 baseline files and one new module, preserving the other 103 files and
the previous work log. F04b is DONE; PKG-F04 remains IN PROGRESS for F04c/F04d.
No later-phase implementation, commit, push, merge or cleanup is performed.
