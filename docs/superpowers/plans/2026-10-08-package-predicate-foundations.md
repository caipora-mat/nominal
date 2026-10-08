# PKG-01 Predicate Foundations Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:executing-plans. The author approved native execution on 2026-10-08. Task 8 and the whole-change review are complete, uncommitted, reusing Tasks 1–7 and phases 01a–01c. The authorized run stops here. Complete each task's checklist and record separate delivery evidence. Steps use checkbox (`- [ ]`) syntax for tracking. The independent whole-change review is recorded in Task 8.

**Goal:** Deliver the complete PKG-01 predicate foundation: ordinary logical support, direct supported predicates, general pullback and quotient descent, and cofinite Some/Any, with public consumers and reconciled mathematical exposition.

**Architecture:** Ordinary predicates and certificates remain the general theorem boundary. A direct proof-field `SupportedPred` reuses F05 through named map/object views and inherits Boolean structure through Mathlib's supported-subset subalgebra. Descent and cofinite theory have ordinary modules independent of that carrier, followed by thin bundled adapters.

**Tech Stack:** Lean/Mathlib `v4.34.1`; Mathlib revision `d13f23b723b8a846827a245b89c10fc7d3f11612`; Lake, existing Python import checker and module-origin axiom audit; LaTeX/latexmk.

**Spec:** [Approved PKG-01 specification](../specs/2026-10-07-package-predicate-foundations-design.md). The author selected direct storage, approved the full specification, then approved this implementation plan for **native execution in fresh contexts** on 2026-10-08. All eight tasks are authorized within their stated scope; no repeated design/plan approval is needed. Tasks 1–7 and phases 01a–01c are complete in the working tree, uncommitted. Task 8 is complete: final integration, all specification criteria and the independent whole-change review pass. PKG-01 is complete, uncommitted; no later task was started.

## Global Constraints

- Work in `/home/fab/Documents/nominal/nominal` on `fasapa/nominal-package`; planning inspected HEAD `3c9d8dc527f7705b24c0308a2527e659ae933874`. Preserve all existing staged, tracked and untracked work, including the uncommitted specification, article and research probes.
- Earlier runs used one fresh context per task, then grouped Tasks 4–5 and Tasks 6–7. The current run is authorized to complete only Task 8, then stop. Read actual source/delivery evidence before trusting a handoff or status claim; retain each complete task checklist and separate record. No repeated approval is needed.
- No branch switching, commits, pushes, merges, publication, dependency upgrades or CI changes. Use the requested checkout. Checkpoints below are evidence records, not commits; no worktree or branch-finishing operation is planned.
- F02–F05 are delivered. Reuse their support, nominality, freshness, function and explicit quotient interfaces. Add only the focused general pullback adapters specified below; do not reopen the F05 hybrid.
- All production additions belong under `Package/`. Preserve reference `Nominal/`, `Instances/`, existing examples and historical `docs/roadmap.md`. Use `docs/nominal-package-roadmap.md` as the tracker.
- Ordinary unsupported predicates remain legal. No automatic ordinary-to-supported coercion, global Prop action, competing bare-arrow/Set action, atom `outParam`, or blanket nominality of full predicate/function carriers.
- Keep atom/carrier/parameter/index universes independent. `SupportedPred A X : Type v` for `X : Type v`, independently of the atom universe. Use one FunLike coercion to `X → Prop`; semantic views are named projections.
- Basic logic, carriers and descent require selected actions, not carrier-wide nominality, infinitude or inhabitance. `Infinite A` is reserved for least support/freshness and the fresh-quantifier laws that actually need it. Visible finite unions/images retain `DecidableEq A`; existential/common-bound laws use local classical reasoning without that public premise.
- Store finite-support existence in proof fields, never a chosen Finset as predicate data. Keep computational bodies computable where possible. Use existing elementwise least support; never assign unsupported objects a default support.
- Reuse `BooleanSubalgebra`, `Equiv.booleanAlgebra`, `Setoid.liftEquiv`, `Function.FactorsThrough`, `Filter.cofinite` and existing action transfer. No manual duplicate Boolean algebra and no unrestricted CompleteLattice instance on supported predicates.
- Quotient-dependent statements explicitly select `QuotientAction.mulAction s hs`. Compatibility, finite support and equivariance remain different hypotheses. Data-valued dependent motives, binder descent and exact-support representatives are not supplied by Prop descent.
- The fresh operator accepts every ordinary predicate. Its notation is opt-in `NominalPackage.FreshQuantifier`; keep the existing `Fresh` relation. Atom Some/Any must not be generalized to arbitrary nominal carriers.
- No sorry, admit, custom axioms, disabled kernel checking, broad reducibility/instance-priority changes or diagnostic suppression. The audit permits only `propext`, `Classical.choice`, `Quot.sound`.
- All three approved phases remain required. F06, syntax/judgment commands, support automation, binder recursion and case studies are outside this plan.
- Reconcile `docs/article/sections/predicates.tex` alongside the proofs. Keep alternatives, task IDs, approvals, commands, diagnostics and verification records outside the manuscript.
- Temporary consumers import `Package`, use `set_option autoImplicit false`, and live in a fresh external evidence directory. Do not introduce a persistent `Package/Examples` layer or import research probes into production.

## Review Focus

- **Literal versus named certificates and proof changes:** both constructor forms must simplify inside ordinary higher-order consumers; enlarging support cannot change a predicate. Task 2 owns the tests.
- **Action selection on definitionally related carriers:** bare functions retain pointwise action; Set views use the existing image action; quotient theorems cannot certify a caller's unrelated quotient action. Tasks 2, 4 and 5 own the tests.
- **Empty and non-nominal quantified/parameter carriers:** whole-carrier quantification needs no element support; fixing a parameter uses only its certificate. Tasks 1, 3 and 7 own the tests.
- **Scope and inference with multiple atom choices:** independently quantified universes and two simultaneous atom sorts must work, and scoped И must respect nested/shadowed binders. Tasks 2, 6 and 8 own the tests.
- **Fresh quantification at finite/empty boundaries:** finite atoms make cofinite the bottom filter; finite indices alone do not repair existential interchange. Tasks 6 and 7 own the tests, including uniform-bound repairs and empty indices.

## Files, order and evidence conventions

All names below are in `NominalPackage` unless a namespace is written explicitly.
Use independent universes for A, X, Y, Z, B and I. In the signature tables,
`S,T : Finset A`, `p,q : X → Prop`, `R : X × Y → Prop`, and X/Y have the
selected `MulAction (Perm A)` unless the row explicitly concerns action-free
descent or cofinite truth. No unstated nominality/infinitude premise is allowed.
Tables specify public contracts; the implementation supplies ordinary proof bodies.

| File | Responsibility / owner task |
| --- | --- |
| `Package/Foundations/PredicateLogic.lean` — new | Task 1: ordinary logical, joint and uniformly indexed support |
| `Package/Foundations/SupportedPredicate.lean` — new | Task 2: direct carrier, action/support/views, supported-subset algebra and transferred Boolean instance |
| `Package/Foundations/SupportedPredicateLogic.lean` — new | Task 3: logical computation/bounds, quantifiers, sections and supported collection operations |
| `Package/Foundations/ActionSupport.lean` — extend | Task 4: scalar invariance reflection through a surjection |
| `Package/Foundations/FunctionAction.lean` — extend | Task 4: full-object precomposition and arbitrary-set support reflection |
| `Package/Foundations/PredicateSupport.lean` — extend | Task 4: ordinary logical pullback reflection and rename law |
| `Package/Foundations/PredicateDescent.lean` — new | Task 4: ordinary compatible-predicate correspondence and canonical-action support specialization |
| `Package/Foundations/SupportedPredicateDescent.lean` — new | Task 5: supported pullback, compatible subtype and quotient equivalence |
| `Package/Foundations/FreshQuantifier.lean` — new | Task 6: cofinite operator/notation, filter laws, supplied-bound Some/Any, classification and joint-support projection |
| `Package/Foundations/SupportedPredicateFresh.lean` — new | Task 7: bundled fresh projection and predicate-object freshness conveniences |
| `Package.lean` | Export each new module as introduced |
| `Package/Tests/AxiomAudit.lean`, `Package/README.md` | Task 8: representative prints and actual public documentation |
| `docs/article/sections/predicates.tex` | Tasks 1–7: reconcile central mathematics and selected Lean correspondence |
| Article entry point, quotient/functions/perspectives sections | Task 8: reconcile affected scope statements and cross-references only |
| Active roadmap, spec, this plan and current research summaries | Phase checkpoints / Task 8: preserve historical evidence and record actual delivery |

Import direction is fixed:

```text
PredicateLogic              → PredicateSupport
SupportedPredicate          → PredicateLogic, SupportedFunction, Mathlib.BooleanSubalgebra
SupportedPredicateLogic     → SupportedPredicate
PredicateDescent            → PredicateSupport, Quotient, Mathlib.Data.Setoid.Basic
SupportedPredicateDescent   → PredicateDescent, SupportedPredicateLogic
FreshQuantifier             → PredicateLogic, Mathlib.Order.Filter.Cofinite/Finite
SupportedPredicateFresh     → FreshQuantifier, SupportedPredicateLogic
```

The scalar/function pullback adapters extend their existing modules without new
reverse imports. The current checker already classifies `Package.Foundations.*`
and the audit traverses all their declarations. No checker, Lake or audit-policy
change is needed.

Tasks **1 → 2 → 3 → 4 → 5 → 6 → 7** are delivered natively. Complete only
Task **8** in the current run, then stop. Do not dispatch implementation agents.
The one independent whole-change reviewer belongs to final integration.
Task 4's ordinary work and Task 6 are
mathematically independent of Tasks 2–3, but the selected execution order is sequential.
Tasks 1–3 close phase 01a, Tasks 4–5 close 01b, Tasks 6–7 close 01c. Task 8
verifies the complete accepted scope. One plan keeps their shared interfaces
consistent; these are independently testable review units within that plan.

At execution start, create a fresh directory with
`mktemp -d /tmp/nominal-package-pkg01-execution.XXXXXX`, record its path in this
plan's execution record, and substitute it for `$PKG01_CHECKS` in every command.
Record initial status and hashes before edits. The exact consumer basenames are
`01Logic.lean`, `02Carrier.lean`, `03Quantifiers.lean`, `04Descent.lean`,
`05SupportedDescent.lean`, `06Fresh.lean`, `07FreshPredicates.lean`,
`08Boundaries.lean`, `09PublicSignatures.lean`.

Task 1 records the evidence directory here and in the roadmap. Later contexts
recover that path from the handoff and verify its files exist; do not assume
shell variables, chat history or temporary logs survive automatically. If evidence
is missing, report that and recreate the required checks from source without
repeating completed implementation. At each task boundary record changed files,
public declarations, exact verification/results, diagnostics, evidence paths,
remaining obligations and a copyable prompt for the next numbered task.

For each task, first compile consumers using the planned public names and record
their missing-name failure; existing fixtures must already compile. Do not add
unproved production declarations to reach a test. End with complete proofs of
negative statements or tightly guarded expected diagnostics, never broken files.
Commands below are future execution checks, not verification performed in planning.

## Task 1: Ordinary logical support and quantification (01a)

**Files:** Create `Package/Foundations/PredicateLogic.lean`; export it in
`Package.lean`; reconcile the first article subsection. Test: `01Logic.lean`.

**Consumes:** F05 `SupportsPred`, `FinitelySupportedPred`, monotonicity,
precomposition and section laws; ordinary Iff congruence and action bijections.

**Produces:**

| Name | Exact contract |
| --- | --- |
| `supportsPred_const (A) (X) (b : Prop)` | `SupportsPred (∅ : Finset A) (fun _ : X => b)` |
| `SupportsPred.not (hp : SupportsPred S p)` | `SupportsPred S (fun x => ¬p x)` |
| `supportsPred_not_iff S p` | `SupportsPred S (fun x => ¬p x) ↔ SupportsPred S p` |
| `SupportsPred.and_same/or_same/imp_same/iff_same hp hq` | From `SupportsPred S p` and `SupportsPred S q`, support S for the corresponding pointwise connective |
| `SupportsPred.and/or/imp/iff hp hq` | From bounds S and T, support `S ∪ T` for the corresponding connective; `[DecidableEq A]` |
| `FinitelySupportedPred.const/not/and/or/imp/iff` | Existential versions of the preceding contracts, without `[DecidableEq A]` |
| `SupportsPred.all (hR : SupportsPred S R)` | `SupportsPred S (fun x => ∀ y, R (x,y))` |
| `SupportsPred.ex (hR : SupportsPred S R)` | `SupportsPred S (fun x => ∃ y, R (x,y))` |
| `FinitelySupportedPred.all/ex` | Corresponding existential support results |
| `SupportsPred.iAll/iEx {I : Sort i} {P : I → X → Prop} (h : ∀ i, SupportsPred S (P i))` | Support S for `fun x => ∀ i, P i x` / `fun x => ∃ i, P i x`; no action on I |

Restricted quantification uses `.all`/`.ex` on the combined implication/
conjunction body; do not add a narrower admission rule requiring independent
support of its guard. Joint quantified carriers need neither Nominal nor Nonempty.

- [x] **1. Create `01Logic.lean`** with `universe u v w i`, the exact hypotheses
  above, and this consuming assertion:

  ```lean
  example {A : Type u} {X : Type v} {Y : Type w}
      [MulAction (Perm A) X] [MulAction (Perm A) Y]
      {S : Finset A} {R : X × Y → Prop} (hR : SupportsPred S R)
      (π : Perm A) (hπ : ∀ a ∈ S, π a = a) (x : X)
      (h : ∀ y, R (x,y)) : ∀ y, R (π • x,y) :=
    (hR.all π hπ x).2 h
  ```

  Also consume `.ex`, exact combined-body restricted quantification, and
  `.iAll/.iEx` with an action-free index. Test `IsEmpty Y`: quantified universal
  and existential predicates have empty support. Use the proved nonnominal
  FunctionObject fixture from the retained representation probe as another Y.
- [x] **2. Run `lake env lean "$PKG01_CHECKS/01Logic.lean"`**, recording missing
  logical declaration failures rather than a failure in the fixtures.
- [x] **3. Implement the constants and connector contracts** using Iff congruence,
  monotonicity and local classical witness unions; prove complement reflection.
- [x] **4. Implement joint and uniform quantification** by reindexing y through
  π/π⁻¹ or applying pointwise Iff congruence at each external index.
- [x] **5. Add a nonminimal-bound consumer**: `{0,1,2}` supports
  `fun n : Nat => n = 0 ∨ n = 1`, and its certificate proves that predicate at
  `π • 0` whenever π fixes that bound. Do not conclude only `True`.
- [x] **6. Run `lake build Package.Foundations.PredicateLogic Package` and the
  consumer.** Require exit 0 with no new diagnostics; print axioms/signatures of
  `SupportsPred.all`, `.ex`, `.iAll`, `supportsPred_not_iff`.
- [x] **7. Reconcile article joint-quantification hypotheses and record checkpoint.**

## Task 2: Direct predicate values and semantic views (01a)

**Files:** Create `Package/Foundations/SupportedPredicate.lean`; update
`Package.lean` and relevant article representation discussion. Test: `02Carrier.lean`.

**Consumes:** Task 1; F05 predicate/object/map correspondences, `SupportedMap`,
`Function.Injective.mulAction`, `ActionSupport.supports_map_iff`; Mathlib BooleanSubalgebra.

**Produces:** The approved direct representation, without additional data fields:

```text
structure SupportedPred (A : Type u) (X : Type v)
    [MulAction (Perm A) X] : Type v where
  toFun : X → Prop
  supported : FinitelySupportedPred A toFun

SupportedPred.ofFun (A) (p : X → Prop) (hp : FinitelySupportedPred A p) : SupportedPred A X
SupportedPred.ofSupports (A) (p : X → Prop) (S : Finset A) (hp : SupportsPred S p) : SupportedPred A X
SupportedPred.ofInvariant (A) (p : X → Prop)
  (hp : ∀ π : Perm A, ∀ x, p (π • x) ↔ p x) : SupportedPred A X
SupportedPred.toMap (p : SupportedPred A X) : SupportedMap A X (Discrete A Prop)
SupportedPred.ofMap (F : SupportedMap A X (Discrete A Prop)) : SupportedPred A X
SupportedPred.toObject (p : SupportedPred A X) : FunctionObject (Perm A) X (Discrete A Prop)
SupportedPred.toSet (p : SupportedPred A X) : Set X
```

Export `ext : (∀ x, p x ↔ q x) → p = q`, `ext_iff`,
`congr_apply : p = q → p x ↔ q x`, `ofFun_proof_irrel`, constructor application
and coerced-function equations. Use **both** named-certificate and explicit
existential-certificate coercion simp lemmas (`coe_ofFun`, `coe_ofFun_exists`)
so named and literal witnesses work without changing F05's semireducibility.
Supply corresponding `ofSupports` computation and `ofInvariant_apply`.

The selected action has `(π • p) x ↔ p (π⁻¹ • x)` and
`(π • p) (π • x) ↔ p x`, named `smul_apply`, `smul_apply_smul`.
Use `renamePred` for the body and derive laws through `toObject` or `toMap`;
neither route repeats permutation/support proofs.

Name the direct-carrier instances `SupportedPred.instFunLike`,
`SupportedPred.instMulAction`, `SupportedPred.instNominal` and
`SupportedPred.instBooleanAlgebra`; intermediate SMul construction is internal.

Required named contracts:

| Names | Contract |
| --- | --- |
| `mapEquiv A X`, `toMap_ofMap`, `ofMap_toMap` | Equivalence with `SupportedMap A X (Discrete A Prop)` and both inverse laws |
| `toMap_apply`, `toObject_apply`, `toObject_eq`, `mem_toSet` | Discrete-map application, predicateObject agreement and ordinary membership/application |
| `toMap_smul`, `toObject_smul`, `toSet_smul` | Each semantic view preserves the selected action; Set uses Pointwise |
| `supports_iff S p`, `supports_iff_toMap S p`, `supports_iff_toObject S p`, `supports_iff_toSet S p` | `Supports S p` iff logical support / support of the corresponding view |
| `instNominal` | `Nominal A (SupportedPred A X)` with only the selected action on X |
| `toObject_finitelySupported`, `toSet_finitelySupported` | Elementwise evidence for each full view |
| `support_toMap`, `support_toObject`, `support_toSet` | With Infinite A, `support A p` equals map support or the appropriate elementwise certificate's `.support`; no Nominal Set X |

Define `SupportedPred.supportedSets A X : BooleanSubalgebra (Set X)` with
carrier `{U | FinitelySupportedPred A (fun x => x ∈ U)}`. Its subtype is the
supported-subset view; `subsetEquiv A X` maps a predicate to its satisfying set
with evidence. Use the inherited `Equiv.symm_apply_apply` and
`Equiv.apply_symm_apply` inverse laws; membership is `mem_subsetEquiv`.
Restrict the existing Set image action to this subtype, using stability and
injective action transfer, and export `subsetEquiv_smul`. Its nominality follows
from the equivariant equivalence. `support_subsetEquiv` adds Infinite A.

`ofSet (A) (U : Set X) (hU : FinitelySupported A U)` uses the **Pointwise image
action fixed in its type**. Give `ofSet_apply` and `toSet_ofSet`. Do not accept
pointwise-arrow support as this Set certificate. Transfer the single Boolean
instance along `subsetEquiv` using `Equiv.booleanAlgebra`; no manual lattice laws.

- [x] **1. Create `02Carrier.lean`** with ordinary application, Iff `ext`, `rw`,
  both view round trips, simultaneous renaming at two atom sorts and these consumers:

  ```lean
  example (P : X → Prop) (hP : FinitelySupportedPred A P) (xs : List X) :
      xs.map (SupportedPred.ofFun A P hP) = xs.map P := by simp
  example (P : X → Prop) (S : Finset A) (hS : SupportsPred S P) (xs : List X) :
      xs.map (SupportedPred.ofFun A P ⟨S,hS⟩) = xs.map P := by simp
  example (P : X → Prop) (h₁ h₂ : FinitelySupportedPred A P) :
      SupportedPred.ofFun A P h₁ = SupportedPred.ofFun A P h₂ := rfl
  ```

  The file supplies the independent-universe/action variables explicitly.
  Include reconstruction from a larger bound, nominality without Nominal X,
  and support agreement with independently supplied object/Set evidence.
- [x] **2. Run its direct Lean command**, expecting missing SupportedPred declarations.
- [x] **3. Implement the record, constructors, one FunLike and Iff ext interface.**
  Keep semantic projections named; prove the F05 map equivalence and computation.
- [x] **4. Implement action, support correspondence and nominality** by existing
  transfer/reflection results. Prove view transport and certificate-independent
  least-support agreements, rather than defining another support choice.
- [x] **5. Implement the supported-subset subalgebra, equivalence and restricted
  action**, then transfer BooleanAlgebra through that equivalence.
- [x] **6. Verify action separation in the consumer**: Set-image membership is
  inverse precomposition, ordinary arrow action remains its existing action,
  and no Prop action is needed to state or use a predicate. Check the actual
  pointwise function action on an existing acted codomain, not a fabricated Prop instance.
- [x] **7. Run `lake build Package.Foundations.SupportedPredicate Package` and
  `02Carrier.lean`.** Inspect signatures/axioms of `mapEquiv`, `subsetEquiv`,
  `supports_iff`, `instNominal`, `support_toSet` and the Boolean instance.
- [x] **8. Reconcile article representation correspondence and record checkpoint.**

## Task 3: Bundled logical and quantified operations (01a)

**Files:** Create `Package/Foundations/SupportedPredicateLogic.lean`; export it;
reconcile article Boolean/quantified-family discussion. Test: `03Quantifiers.lean`.

**Consumes:** Tasks 1–2 and the unchanged F05 parameter/precomposition laws.

**Produces:** In `SupportedPred`, the following operations and equations:

```text
biimp (p q : SupportedPred A X) : SupportedPred A X
precomp (p : SupportedPred A Y) (f : X → Y) (hf : FinitelySupportedMap A f) : SupportedPred A X
precompMap (p : SupportedPred A Y) (f : SupportedMap A X Y) : SupportedPred A X
section (R : SupportedPred A (Y × X)) (y : Y) (hy : FinitelySupported A y) : SupportedPred A X
all (R : SupportedPred A (X × Y)) : SupportedPred A X
ex (R : SupportedPred A (X × Y)) : SupportedPred A X
collectionUnion (C : SupportedPred A (SupportedPred A X)) : SupportedPred A X
collectionInter (C : SupportedPred A (SupportedPred A X)) : SupportedPred A X
```

Application/coercion simp names are `bot_apply`, `top_apply`, `inf_apply`,
`sup_apply`, `compl_apply`, `himp_apply`, `sdiff_apply`, `biimp_apply`,
`precomp_apply`, `precompMap_apply`, `section_apply`, `all_apply`, `ex_apply`,
`collectionUnion_apply`, `collectionInter_apply`, and matching `coe_*` equations.
The bodies are exactly ordinary False/True, ∧/∨/¬/→, `p x ∧ ¬q x`, ↔,
`p (f x)`, `R (y,x)`, `∀ y, R (x,y)`, `∃ y, R (x,y)`,
`∃ p, C p ∧ p x`, and `∀ p, C p → p x` respectively.
`le_def` states `p ≤ q ↔ ∀ x, p x → q x`.

Export `smul_bot/top/inf/sup/compl/himp/sdiff/biimp`, `smul_le_smul_iff`,
`precompMap_smul`, `section_smul`, `all_smul`, `ex_smul`,
`collectionUnion_smul`, `collectionInter_smul` with simultaneous renaming of
all inputs. `section_smul` permutes y and transports hy; `precompMap_smul`
permutes both p and f. These are operator action laws, not merely closure facts.

`supports_compl_iff` preserves/reflects the same S. `supports_inf/sup/himp/biimp`
combine separate bounds by union; `supports_precomp` combines predicate/map
bounds and `supports_section` combines relation/parameter bounds. Theorems
`supports_all/ex/collectionUnion/collectionInter` retain **the input's same bound**.
Derive `support_compl` as equality, and `support_*_subset` for the other operations
under Infinite A, keeping DecidableEq only for displayed unions. Define
`support_bot`, `support_top` as empty-support equations. No exact binary bounds
or unrestricted external joins are asserted. In particular the exact least-bound
interfaces include, for the certificates supplied to the constructors:

```text
support_precomp_subset [Infinite A] [DecidableEq A] p f hf :
  support A (p.precomp f hf) ⊆ support A p ∪ hf.toObject.support
support_section_subset [Infinite A] [DecidableEq A] R y hy :
  support A (R.section y hy) ⊆ support A R ∪ hy.support
support_all_subset [Infinite A] R : support A R.all ⊆ support A R
support_ex_subset [Infinite A] R : support A R.ex ⊆ support A R
support_collectionUnion_subset [Infinite A] C : support A C.collectionUnion ⊆ support A C
support_collectionInter_subset [Infinite A] C : support A C.collectionInter ⊆ support A C
```

- [x] **1. Create `03Quantifiers.lean`** with pointwise Boolean laws (including
  implication/difference), `le_def`, and the all/ex equations on empty Y.
  Test restricted quantification as `(D ⇨ R).all` and `(D ⊓ R).ex`; the combined
  ordinary body may also be certified without separately certifying D.
- [x] **2. Run the consumer**, recording missing operation/computation laws.
- [x] **3. Implement the listed computation and sufficient-bound laws**, deriving
  biimp from the transferred algebra and all/ex from Task 1. Reuse F05 for
  precomposition and sections. Do not introduce another curry hierarchy.
- [x] **4. Implement supported collection operations** by jointly invariant
  evaluation and all/ex over the ambient predicate carrier with the C guard.
- [x] **5. Prove all operator action laws and least-support consequences.** Use
  ordinary extensionality and bounds; keep the sufficient-versus-exact distinction.
- [x] **6. Add substantive consumers** fixing the supported identity inside the
  proved nonnominal full function carrier, quantifying over that same carrier,
  and using a collection's supplied bound to obtain the union's renaming law.
  Test `p ⊓ ⊥ = ⊥` to expose support loss; no input-support equality may follow.
- [x] **7. Run `lake build Package.Foundations.SupportedPredicateLogic Package`
  and the consumer.** Print axioms of `all_smul`, `section_smul`,
  `supports_collectionUnion`, `support_compl`; record phase 01a and article checks.

## Task 4: General pullback and ordinary quotient predicates (01b)

**Files:** Extend ActionSupport.lean, FunctionAction.lean and PredicateSupport.lean;
create PredicateDescent.lean; update Package.lean and article descent subsection.
Test: `04Descent.lean`. All these paths are under `Package/Foundations/`.

**Consumes:** Existing F05 scalar injection reflection/function objects and F04
explicit canonical quotient action; pinned `Setoid.liftEquiv` and subtype equivalence.
This task has no dependency on SupportedPred.

**Produces:**

```text
ActionSupport.invariant_pullback_iff
  [SMul M X] [SMul M Y] (q : X → Y) (hsurj : Surjective q)
  (m : M) (hq : ∀ x, q (m • x) = m • q x) (P : Y → Prop) :
  (∀ x, P (q (m • x)) ↔ P (q x)) ↔ ∀ y, P (m • y) ↔ P y

FunctionObject.precomp (F : FunctionObject G Y Z) (q : X → Y) : FunctionObject G X Z
FunctionObject.supports_precomp_iff
  [DivisionMonoid G] [SMul G B] [MulAction G X] [MulAction G Y] [MulAction G Z]
  (q : X → Y) (hq : ∀ g x, q (g • x) = g • q x) (hsurj : Surjective q)
  (S : Set B) (F : FunctionObject G Y Z) :
  MulAction.Supports G S (F.precomp q) ↔ MulAction.Supports G S F

supportsPred_pullback_iff (q : X → Y) (hq : Equivariant A q)
  (hsurj : Surjective q) (S : Finset A) (P : Y → Prop) :
  SupportsPred S (P ∘ q) ↔ SupportsPred S P
finitelySupportedPred_pullback_iff q hq hsurj P :
  FinitelySupportedPred A (P ∘ q) ↔ FinitelySupportedPred A P
renamePred_pullback q hq π P : renamePred π P ∘ q = renamePred π (P ∘ q)
```

Give `FunctionObject.precomp_apply`, `coe_precomp`, `precomp_injective` (action-free,
using surjectivity), and `precomp_smul` using hq under DivisionMonoid. Preservation
without surjectivity uses F05; provide `SupportsPred.pullback hp hq` with the same S
and `FinitelySupportedPred.pullback hp hq` for existence.
`FinitelySupportedPred.support_pullback hp q hq hsurj` adds Infinite A and states:

```text
((finitelySupportedPred_iff A (P ∘ q)).1 (hp.pullback hq)).support =
  ((finitelySupportedPred_iff A P).1 hp).support
```

These are **elementwise predicateObject** supports, not ordinary arrow supports.

In namespace `PredicateDescent`, ordinary declarations need only `s : Setoid X`:

```text
abbrev Compatible (s : Setoid X) (p : X → Prop) : Prop :=
  ∀ x y, s.r x y → (p x ↔ p y)
pullback (s : Setoid X) (P : Quotient s → Prop) : X → Prop := P ∘ Quotient.mk s
descend (s : Setoid X) (p : X → Prop) (hp : Compatible s p) : Quotient s → Prop
ordinaryEquiv (s : Setoid X) : (Quotient s → Prop) ≃ {p : X → Prop // Compatible s p}
```

Prove `compatible_iff_le_ker`, `compatible_iff_factorsThrough`,
`compatible_pullback`, `pullback_apply`, `descend_mk`, `pullback_descend`,
`descend_pullback`, `descend_proof_irrel`, and both equivalence computation laws
`ordinaryEquiv_apply`/`ordinaryEquiv_symm_apply`.
`compatible_iff_exists_descend` characterizes existence of P computing p on
all representatives; `cannot_descend` derives its negation from related x,y
with p x and ¬p y. Reuse `(Setoid.liftEquiv s).symm` with propext; do not rebuild
the general function universal property or use a choice-selected representative.

Add selected source action and `hs : SMulInvariant (Perm A) s` only for
`supports_pullback_iff`, `supports_descend_iff`, `finitelySupported_descend_iff`,
`compatible_rename`, `descend_rename`. Each quotient support/action type installs
`letI := QuotientAction.mulAction s hs`. The first iff has pullback on the left;
the second has descended predicate on the left. Descended renaming equals
renaming of descent, with the transported compatibility proof. No Nominal premise.

- [x] **1. Create `04Descent.lean`** with the exact scalar/DivisionMonoid signatures,
  independent universes and the ordinary round-trip consumer:

  ```lean
  example {X : Type u} (s : Setoid X) (P : Quotient s → Prop) :
      PredicateDescent.descend s (PredicateDescent.pullback s P)
        (PredicateDescent.compatible_pullback s P) = P :=
    PredicateDescent.descend_pullback s P
  ```

  Include exact-bound reflection for arbitrary P and an arbitrary supplied S,
  followed by its explicit canonical quotient specialization.
- [x] **2. Run the consumer**, expecting missing adapters/descent names.
- [x] **3. Add the scalar and full-function precomposition adapters**, deriving
  arbitrary-set reflection from `ActionSupport.supports_map_iff` and surjectivity.
- [x] **4. Add ordinary predicate pullback reflection and elementwise least-support
  equality**, then construct the Mathlib-backed ordinary descent correspondence.
- [x] **5. Add canonical quotient support and renaming laws**, with the action
  constructor in their types. Preserve ordinary descent's action-free signature.
- [x] **6. Prove negative/ordinary consumers** by adapting the retained descent
  probe: diagonal `Nat → Nat × Nat` and `P(x,y) := x = 0 ∧ x ≠ y` refute
  reflection without surjectivity; a singleton-supported vacuous-binder label
  observation cannot descend; the unsupported true-flag atom predicate descends
  through the quotient forgetting an extra discrete label. Use it in quotient
  induction to obtain a true-flag representative. Include the equality quotient
  with a separately chosen trivial action to show its projection is not
  equivariant: no canonical-action theorem may certify that unrelated action.
- [x] **7. Build the three extended modules, PredicateDescent and Package; run
  `04Descent.lean`.** Inspect axioms/signatures of both parent reflection theorems,
  `ordinaryEquiv`, `supports_descend_iff` and `descend_rename`.
- [x] **8. Reconcile the article's ordinary/supported and object/predicate distinctions;
  record the checkpoint.** No dependent data recursor or binder backend is added.

## Task 5: Supported pullback and quotient correspondence (01b)

**Files:** Create `Package/Foundations/SupportedPredicateDescent.lean`, export it;
extend `Package/Foundations/PredicateDescent.lean` with the ordinary compatibility
connector lemmas below; reconcile article descent correspondence.
Test: `05SupportedDescent.lean`.

**Consumes:** Tasks 2–4; Mathlib SubMulAction and the existing selected quotient action.

**Produces:**

```text
SupportedPred.pullback (P : SupportedPred A Y) (q : X → Y)
  (hq : Equivariant A q) : SupportedPred A X
PredicateDescent.CompatiblePred (A) (s : Setoid X) :=
  {p : SupportedPred A X // PredicateDescent.Compatible s (fun x => p x)}
PredicateDescent.compatibleAction (A) (s) (hs : SMulInvariant (Perm A) s) :
  MulAction (Perm A) (PredicateDescent.CompatiblePred A s)
PredicateDescent.compatibleNominal (A) (s) (hs) :
  letI := PredicateDescent.compatibleAction A s hs
  Nominal A (PredicateDescent.CompatiblePred A s)
PredicateDescent.descendSupported (A) (s) (hs) (p : SupportedPred A X)
  (hp : PredicateDescent.Compatible s (fun x => p x)) :
  letI := QuotientAction.mulAction s hs
  SupportedPred A (Quotient s)
PredicateDescent.supportedEquiv (A) (s) (hs) :
  letI := QuotientAction.mulAction s hs
  SupportedPred A (Quotient s) ≃ PredicateDescent.CompatiblePred A s
```

Restrict the source predicate action using `Compatible` stability and
`SubMulAction`; `compatibleAction` and `compatibleNominal` are explicit
constructors with the supplied hs, not automatic proof-search instances.
`SupportedPred.pullback_apply` computes P(q x); `pullback_smul` fixes q/hq and
permutes P. `supports_pullback_iff` adds surjectivity and reflects every S;
`support_pullback` adds Infinite A and gives least-support equality.

The quotient API includes `descendSupported_mk`, `supportedEquiv_apply`,
`supportedEquiv_symm_apply`, both inverse equations, `supportedEquiv_smul`
and `supportedEquiv_symm_smul`. Action statements select **both** explicit
actions. `supports_supportedEquiv_iff` reflects every bound through the
equivalence; `support_supportedEquiv` additionally selects compatibleNominal
and assumes Infinite A. `freshWith_supportedEquiv_iff` compares disjointness
with any individually supported context using that exact support equality;
the context need not have a nominal carrier.

Precisely, after selecting the quotient action, compatibleAction and
compatibleNominal, for `hc : FinitelySupported A c` the freshness contract is

```text
(Nominal.finitelySupported (A := A) P).FreshWith hc ↔
  (Nominal.finitelySupported (A := A) (supportedEquiv A s hs P)).FreshWith hc
```

Logical preservation uses ordinary subtype values: export
`descendSupported_top/bot/compl/inf/sup/himp/biimp` and the analogous
`SupportedPred.pullback_*` laws, with compatibility premises for the operands
and their derived combinations. Prove `Compatible.const/not/and/or/imp/iff`
as the needed ordinary adapters. Do not add a second Boolean instance to the
compatible subtype solely to state these laws.

- [x] **1. Create `05SupportedDescent.lean`** checking both equivalence inverses,
  representative computation, action preservation and every-bound reflection.
  Include an independent universe for an individually supported freshness context.
- [x] **2. Run the consumer**, expecting missing bundled names.
- [x] **3. Implement supported pullback and its computation/action/support laws**
  from ordinary Task 4 reflection and certified constructors.
- [x] **4. Implement the compatible subtype/action and supported equivalence**
  by restricting ordinary descent, without source/quotient Nominal assumptions.
- [x] **5. Prove exact support, context freshness and logical preservation** from
  the established equivalence and representative equations.
- [x] **6. Add the representative-label consumer**: quotient `A × Discrete A Bool`
  by first-coordinate equality, descend equality with a fixed atom a, retain any
  supplied bound containing `{a}`, and prove the result on both Bool-labelled
  representatives. Its finite bound may be strictly larger than needed.
- [x] **7. Run `lake build Package.Foundations.SupportedPredicateDescent Package`
  and the consumer.** Inspect signatures/axioms of `supportedEquiv`,
  `compatibleAction`, `supports_supportedEquiv_iff`, `support_supportedEquiv`.
- [x] **8. Reconcile article/phase 01b and record the checkpoint.**

## Task 6: Ordinary cofinite quantification and supplied-bound Some/Any (01c)

**Files:** Create `Package/Foundations/FreshQuantifier.lean`, export it;
reconcile article Some/Any and logical hypotheses. Test: `06Fresh.lean`.

**Consumes:** Mathlib cofinite/eventually/reindexing/finite-index laws, Task 1
ordinary support, and delivered atom swaps/elementwise context support.
This module does not import SupportedPred.

**Produces:** `Freshly {A : Type u} (p : A → Prop) : Prop :=
∀ᶠ a in Filter.cofinite, p a`, plus typed/untyped `И` in the opt-in scope
`NominalPackage.FreshQuantifier`. Lemma namespace `Freshly` provides:

| Names | Exact contract / additional hypotheses |
| --- | --- |
| `iff_eventually`, `iff_finite`, `iff_exists_finset` | Definition, finite falsehood set, and `Freshly p ↔ ∃ S : Finset A, ∀ a, a ∉ S → p a` |
| `of_forall`, `mono`, `congr`, `congr_eventually` | Pointwise truth/implication/Iff and eventual Iff transfer cofinite truth; no support or infinitude |
| `true`, `and_iff`, `mp` | Cofinite True, exact conjunction, and cofinite modus ponens; arbitrary predicates |
| `const_iff`, `not_false`, `exists` | Constant iff, exclusion of False, witness extraction; `[Infinite A]` |
| `reindex (e : A ≃ B) (p : B → Prop)` | `Freshly (p ∘ e) ↔ Freshly p`; independent universes, no actions |
| `forall_of`, `of_exists` | Valid one-way universal/existential interchange for arbitrary `I : Sort i` |
| `forall_finite [Finite I]` | `Freshly (fun a => ∀ i, p i a) ↔ ∀ i, Freshly (p i)` |
| `not_iff_of_decision (hd : Freshly p ∨ Freshly (fun a => ¬p a))` | `Freshly (fun a => ¬p a) ↔ ¬Freshly p`; `[Infinite A]` |
| `or_iff_of_decision hd` | `Freshly (fun a => p a ∨ q a) ↔ Freshly p ∨ Freshly q`; decision of p, arbitrary q, no infinitude; give the symmetric right-operand adapter |
| `imp_iff_of_decision hd` | `Freshly (fun a => p a → q a) ↔ (Freshly p → Freshly q)`; no infinitude |
| `iff_iff_of_decisions hp hq` | `Freshly (fun a => p a ↔ q a) ↔ (Freshly p ↔ Freshly q)`; both decisions, no infinitude |
| `iff_iff_of_freshly_left hp` | Same Iff law from `hp : Freshly p`, arbitrary q; no support or infinitude |

Use existing general filter lemmas for these proofs; no new filter construction
or general filter hierarchy. `forall_of` takes cofinite ∀ and returns each
cofinite section; `of_exists` takes an index with a cofinite section.

Nominal results have canonical atom input. For `hp : SupportsPred S p`:

```text
SupportsPred.iff_of_notMem hp ha hb : p a ↔ p b       -- ha : a ∉ S, hb : b ∉ S
SupportsPred.freshly_iff_exists hp : Freshly p ↔ ∃ a, a ∉ S ∧ p a
SupportsPred.freshly_iff_forall hp : Freshly p ↔ ∀ a, a ∉ S → p a
SupportsPred.freshly_iff hp ha : Freshly p ↔ p a
SupportsPred.freshly_iff_exists_avoiding hp T : Freshly p ↔ ∃ a, a ∉ S ∧ a ∉ T ∧ p a
SupportsPred.freshly_iff_forall_avoiding hp T : Freshly p ↔ ∀ a, a ∉ S → a ∉ T → p a
```

Only `iff_of_notMem` omits Infinite A. None needs a public DecidableEq premise.
Enlarged bounds use existing `.mono`, not a new support representation.
`finitelySupportedPred_atom_iff` states finite-or-cofinite classification with
no atom hypotheses. `FinitelySupportedPred.freshly_or_not` derives cofinite
decision; `.freshly_not_iff`, `.freshly_or_iff`, `.freshly_imp_iff`,
`.freshly_iff_iff` specialize the preceding decision laws with exactly their
needed support and infinitude premises. `not_finitelySupportedPred_of_infinite_coinfinite`
rejects a certificate when both truth and falsehood sets are infinite.

For `R : X × A → Prop`, export `SupportsPred.fresh` and
`FinitelySupportedPred.fresh` retaining the relation's support bound/existence
under fresh projection, with only the action on X. This does **not** need
Infinite A or support of any particular x. Reindex cofinite through π.

Uniform-section laws for `hp : ∀ i : I, SupportsPred S (p i)` are
`Freshly.forall_iff_of_uniform_support` (full universal iff, no infinitude),
`Freshly.exists_iff_of_uniform_support` (full existential iff, Infinite A), and
`Freshly.exists_iff_of_uniform_support_nonempty` (the same iff with Nonempty I
instead of Infinite A). I needs no action. Do not assert finite-index
existential interchange without these stronger hypotheses.

- [x] **1. Create `06Fresh.lean`** with raw filter laws on unrestricted predicates,
  reindexing across different universes, finite Bool with `Freshly False`, and
  this supplied-bound consuming assertion:

  ```lean
  example {A : Type u} [Infinite A] {S : Finset A} {p : A → Prop}
      (hp : SupportsPred S p) (h : Freshly p) (T : Finset A) :
      ∃ a, a ∉ S ∧ a ∉ T ∧ p a :=
    (hp.freshly_iff_exists_avoiding T).1 h
  ```

  Test finite-index universal interchange, all three uniform-support variants,
  and implication with a supported antecedent and arbitrary consequent.
- [x] **2. Run the consumer**, expecting missing Freshly/Some/Any declarations.
- [x] **3. Define Freshly and scoped notation; add ordinary filter adapters.**
  Test typed/untyped binders, nested `И a, ∀ b, ...`, deliberate binder shadowing,
  surrounding locals, and a guarded unscoped-use failure before opening the scope.
- [x] **4. Prove constancy off a supplied bound and Some/Any**, using swaps,
  `Finset.eventually_cofinite_notMem` and cofinite nontriviality. Derive finite
  avoidance/evaluation without selecting least support.
- [x] **5. Prove finite/cofinite classification and the weak Boolean interfaces.**
  Keep finite atoms legal; only self-dual negation/witness laws need nontriviality.
- [x] **6. Prove joint fresh projection and uniform-section interchange.** In
  the finite-atom case cofinite is bottom; existential equivalence needs the
  stated infinite-atom or nonempty-index premise.
- [x] **7. Run `lake build Package.Foundations.FreshQuantifier Package` and the
  consumer.** Inspect signatures/axioms of `Freshly.reindex`,
  `SupportsPred.freshly_iff_exists`, `SupportsPred.fresh`, classification and
  the three uniform-support laws. Reconcile the article and record checkpoint.

## Task 7: Parameter contexts, bundled fresh projection and boundaries (01c)

**Files:** Extend FreshQuantifier.lean for ordinary context adapters; create
`Package/Foundations/SupportedPredicateFresh.lean`; export it; reconcile the
article's context and limitation statements. Tests: `07FreshPredicates.lean`,
`08Boundaries.lean`.

**Consumes:** Tasks 2–3 and 6; F05 ordinary sections and F04 individual freshness.

**Produces:** Ordinary `freshly_section_iff_exists` and `freshly_section_iff_forall`
for joint `R : X × A → Prop` bound S and `Supports T x`, with avoidance of
`S ∪ T` (Infinite A and DecidableEq for the displayed union). The invariant
forms `freshly_invariant_section_iff_exists` and `_forall` take
`hR : ∀ π z, R (π • z) ↔ R z` and `hx : FinitelySupported A x`; their fresh
conditions are `hx.Fresh a`, with Infinite A but no Nominal X or DecidableEq.
Use Task 6's avoidance forms to add an arbitrary finite exclusion.

```text
SupportedPred.fresh (R : SupportedPred A (X × A)) : SupportedPred A X
SupportedPred.fresh_apply R x : R.fresh x ↔ Freshly (fun a => R (x,a))
SupportedPred.fresh_smul π R : (π • R).fresh = π • R.fresh
SupportedPred.supports_fresh (hR : Supports S R) : Supports S R.fresh
SupportedPred.support_fresh_subset [Infinite A] R : support A R.fresh ⊆ support A R
```

Give `coe_fresh` and the atom-predicate convenience
`SupportedPred.freshly_iff_of_fresh [Infinite A] (p : SupportedPred A A)
(ha : Fresh A a p) : Freshly (fun b => p b) ↔ p a`.
Ordinary `FinitelySupportedPred.freshly_iff_of_fresh hp` uses freshness for
the elementwise certificate of `predicateObject A p`, without bundling p.

- [x] **1. Create `07FreshPredicates.lean`** with fresh projection's computation,
  same-bound/action laws without Infinite A, and a context consumer that obtains
  `R (x,a)` at a fresh atom from cofinite truth and only hx. Use the supported
  identity in the proved nonnominal full function carrier, with an extra finite
  exclusion; the resulting relation fact must appear in the conclusion.
- [x] **2. Run that consumer**, expecting missing bundled/context adapter names.
- [x] **3. Implement the context and predicate-object adapters** using existing
  section bounds and Task 6; implement bundled fresh projection and its laws.
- [x] **4. Write `08Boundaries.lean` with these proved assertions**, adapting the
  retained fresh/descent probes through public names, not importing them:

  ```text
  A := Nat × Bool; p a := a.2 = true
  ¬FinitelySupportedPred A p; ¬Freshly p; ¬Freshly (fun a => ¬p a)
  ∀ n, FinitelySupportedPred A (fun a => a = (n,true))
  ¬FinitelySupportedPred A (fun a => ∃ n, a = (n,true))
  Freshly (fun a : Nat, ∃ x : Nat, a = x) ∧ ¬∃ x, Freshly (fun a => a = x)
  (∀ x : Nat, Freshly (fun a => a ≠ x)) ∧ ¬Freshly (fun a : Nat => ∀ x, a ≠ x)
  Freshly (fun a : A => ∃ i : Bool, a.2 = i) ∧ ¬∃ i : Bool, Freshly (fun a : A => a.2 = i)
  Freshly (fun _ : Bool => ∃ _ : Empty, False) ∧ ¬∃ _ : Empty, Freshly (fun _ : Bool => False)
  ```

  Prove equality/disequality are jointly invariant. Refute self-dual negation,
  full disjunction/implication on arbitrary p, and Iff with just one supported
  operand (take False and p). On `Discrete Nat Bool × Nat`, exhibit an
  empty-supported, witnessed predicate with infinitely many exceptions.
  Prove no `f : Finset A → A` with `∀ S, f S ∉ S` has FinitelySupportedMap;
  the statement needs the chosen Finset action's DecidableEq but no extra Infinite.
  Ordinary choice and unsupported predicates remain legal.
- [x] **5. Include fixed-atom support/non-equivariance and a larger-bound Some/Any
  consumer**; connect the negative examples to the exact missing hypothesis,
  not an expected rejection of ordinary Lean predicates or motives.
- [x] **6. Run `lake build Package.Foundations.SupportedPredicateFresh Package`
  and both consumers.** Inspect representative axioms, including the selector
  obstruction and joint fresh projection; require complete proofs and no diagnostics.
- [x] **7. Reconcile article hypotheses and limitations; record phase 01c checkpoint.**

## Task 8: Public integration, specification coverage and final review

**Files:** Package.lean, Package/Tests/AxiomAudit.lean, Package/README.md,
affected article sections/entry point, active tracker and current spec/plan/research
summaries. Tests: all nine consumers and extracted README examples.

**Consumes:** Tasks 1–7. **Produces:** The complete reviewed PKG-01 interface through
the public root, with all accepted positive/negative boundaries and accurate exposition.

- [x] **1. Create `09PublicSignatures.lean`** assigning the headline declarations
  to their exact types in this plan, with independent universes and explicit
  selected actions. Check no-Nominal/no-Infinite/empty consumers, scalar-only
  and DivisionMonoid parent statements, explicit quotient actions, two atom
  sorts and fresh notation outside its defining namespace. Missing exports fail.
- [x] **2. Extend the audit's representative prints** for logical quantification,
  carrier action/nominality, both semantic equivalences, Boolean transfer,
  generic/quotient support reflection, supported descent, Some/Any, classification
  and fresh projection. Preserve the complete traversal, standard-axiom whitelist
  and rejection tests unchanged.
- [x] **3. Update Package/README.md** with actual constructors/names and small
  ordinary-input, supported-value, quotient-descent and supplied-bound `И`
  consumers. State the empty/non-nominal/uniform-bound limits precisely; compile
  extracted Lean examples through `import Package`.
- [x] **4. Reconcile the manuscript against final statements and declarations.**
  Keep the selected central results, proof ideas and pinned literature attributions.
  Add implementation correspondence only when proved; no task/build/approval
  narratives. Avoid duplicating routine API inventories in the article.
- [x] **5. Run integrated checks**, all requiring exit 0:

  ```sh
  lake build Package +Package.Tests.AxiomAudit
  lake env lean Package/Tests/AxiomAudit.lean
  python3 Package/Scripts/check-imports.py
  git diff --check
  ```

  Directly elaborate all nine consumers and README extracts. Run latexmk from
  `docs/article` with output under `$PKG01_CHECKS/article`; inspect the final log
  for unresolved references and diagnostics. Check changed/new Markdown links
  and whitespace, and compare initial hashes/status to preserve unrelated work.
  No dependency bootstrap or unchanged reference-library rebuild is required;
  report cached/rebuilt artifacts accurately. Checker self-tests apply only if
  a separately justified checker change occurred.
- [x] **6. Self-check the acceptance mapping below and obtain the review required
  by the chosen execution method.** For native execution, use one fresh independent
  final reviewer on the most capable available model, with spec, plan, diff,
  exact commands/logs and preserved-work inventory. Resolve findings and rerun
  affected checks; do not repeat unrelated passing checks without a reason.
- [x] **7. Record actual evidence and delivered status** in the roadmap, this plan
  and current research summaries. Mark PKG-01 complete only after every phase
  and integration criterion is satisfied. Distinguish uncommitted delivery from
  a commit; the user's no-commit instruction remains in force.

## Coverage self-review and handoff

| Approved specification obligation | Owning tasks |
| --- | --- |
| Ordinary support, connectors, whole/restricted/uniform quantification | 1, 3 |
| Direct storage, proof irrelevance, FunLike/Iff ext and literal-proof simp | 2 |
| Function/object/subset views, action, nominality and exact support agreement | 2 |
| Mathlib Boolean/order reuse, computation, no external completeness | 2, 3, 7 |
| Elementwise parameters, admissible function reuse, supported collections | 3, 7 |
| Scalar/DivisionMonoid parents and equivariant-surjective support reflection | 4, 5 |
| Ordinary descent without support; supported canonical quotient equivalence | 4, 5 |
| Unsupported ordinary quotient induction and alpha-incompatible raw predicate | 4 |
| Cofinite definition/scoped notation, Some/Any and weakest logical premises | 6, 7 |
| Extra avoidance, individual context, joint fresh support, common-bound repairs | 6, 7 |
| Infinite/coinfinite, arbitrary unions, quantifier/selector/carrier boundaries | 7 |
| Independent universes/actions, public exports, trust, article and preservation | All; final integration 8 |

Planning self-review completed on 2026-10-08: this mapping, consistent names and
types, all five Review Focus tests, and the unchanged full three-phase scope
were checked against the approved specification and current source. This plan specifies
contracts, consumers and proof routes; it does not copy entire implementation
proofs. Research probes establish feasibility only. No production or consumer
test is claimed run merely because its command appears here.

The planning-only content/link, whitespace and preservation checks passed.
No production source or research probe was modified in this planning turn;
future consumer declarations and proofs still require their execution checks.

**Approved execution:** Native, with one fresh context per numbered task and one
independent whole-change review in Task 8. This method was explicitly selected
after plan approval; it is not inferred from specification approval.

**Stopping point reached:** Task 8 and PKG-01 are complete, uncommitted.
All three phases, public integration, full specification coverage and the
independent review pass. The final execution record below contains commands,
cache conditions, preservation and review disposition. Earlier prompts remain
historical; later PKG tasks require a separate request.

## Execution record

### 2026-10-08 — Task 1 complete: ordinary logical support and quantification

**Delivered uncommitted; phase 01a and PKG-01 remain open.** Tasks 2–3 are still
required for 01a; the independent whole-change review remains assigned to Task 8.
No Task 2 implementation was started. No mathematical contract changed.

Evidence directory: `/tmp/nominal-package-pkg01-execution.WReW3a/`.
`initial-snapshot.json` records all 151 baseline file hashes, branch, HEAD, index
hash and status; `initial.diff` preserves the starting tracked diff.
`task-1-brief.md` and `progress.md` retain the task and execution ledger.

Created `Package/Foundations/PredicateLogic.lean` and exported it from `Package`.
Its 23 public declarations are `supportsPred_const`, `SupportsPred.not`,
`supportsPred_not_iff`, `SupportsPred.and_same/or_same/imp_same/iff_same`,
`SupportsPred.and/or/imp/iff`, `FinitelySupportedPred.const/not/and/or/imp/iff`,
`SupportsPred.all/ex`, `FinitelySupportedPred.all/ex`, and `SupportsPred.iAll/iEx`.
The common-bound and existential statements need no decidable atom equality;
only displayed union bounds require it. Quantification preserves the joint bound
without nominality, nonemptiness or infinitude; external indices range over an
independent `Sort`. Restricted quantification accepts support of the combined
body itself. No new generic support hierarchy, bundled predicate, notation,
descent or fresh quantifier was introduced.

`Fixtures.lean` first passed with the proved nonnominal FunctionObject carrier.
`01Logic.lean` then failed on the planned missing public declarations (exit 1,
`01Logic-red.log`), with no fixture failure. After implementation it passed,
including joint ∀/∃, restricted implication/conjunction, separate guard bounds,
uniform action-free Sort indices, empty carriers/indices and genuinely nonnominal
quantified carriers. Independent universe parameters and all 23 exact signatures
are checked; representative prints for `.all`, `.ex`, `.iAll` and negation
reflection use only `propext`, `Classical.choice`, `Quot.sound`. The nonminimal
`{0,1,2}` certificate for `n = 0 ∨ n = 1` is consumed to prove the disjunction
at `π • 0`, rather than discarded.

Verification actually run, all final exits 0:

- `lake build Package.Foundations.PredicateLogic Package` — 980 jobs;
  newly elaborated PredicateLogic and public root, cached dependencies
  (`logic-build.log`). Baseline `lake build Package` passed with 979 cached jobs.
- `lake build Package.Foundations.PredicateLogic Package +Package.Tests.AxiomAudit`
  — 981 jobs; production artifacts cached from that build, audit freshly built
  (`final-build.log`).
- `lake env lean /tmp/nominal-package-pkg01-execution.WReW3a/01Logic.lean`
  — fresh source elaboration, all consumers and signature/axiom prints pass
  (`01Logic-final.log`).
- `lake env lean Package/Tests/AxiomAudit.lean` — fresh source elaboration;
  597 production declarations from 15 modules, no axioms beyond the three
  standard foundations (`axiom-audit.log`).
- `python3 Package/Scripts/check-imports.py` — all 16 production sources
  (including the root) and the one audit source reached (`import-coverage.log`).
- `lake build Nominal Instances Examples` — 1033 cached jobs; reference audit
  output replayed, not a fresh reference audit (`reference-build.log`).
- From `docs/article`, `latexmk -pdf -interaction=nonstopmode -halt-on-error
  -outdir=/tmp/nominal-package-pkg01-execution.WReW3a/article-build main.tex`
  — 37-page PDF; fresh external output directory. A new overfull line in the
  predicate API paragraph was shortened and recompiled; the final TeX log has
  no warnings or overfull/underfull boxes. Article changes clarify complement
  reflection, weakest quantifier premises, combined restricted bodies and
  independent uniform indices; task metadata stays outside the manuscript.
- `git diff --check` plus changed/new-file whitespace and local Markdown target
  checks pass. `validation-lean.json` and `validation-article.json` retain exact
  commands, working directories and exit codes.

Preservation check: `check-preservation.py` / `final-snapshot.json` confirm 142
of 151 initial files byte-identical, exactly nine intentionally reconciled
existing files, and only the new PredicateLogic source added. Those nine are
the public root, Package README, predicate article section, active roadmap,
plan, spec, current predicate research report, readiness summary and research
index. Existing article entry/quotient work, all probes, other research files,
reference source, historical roadmap, pinned dependencies, branch
`fasapa/nominal-package`, HEAD `3c9d8dc527f7705b24c0308a2527e659ae933874` and
index are unchanged. No commit, push, worktree, dependency or CI operation.
README/spec/current summaries now distinguish this partial delivery from the
remaining supported carrier, bundled logic, descent and cofinite work.

### Copyable fresh-context prompt for Task 2

```text
$superpowers:executing-plans

Implement ONLY Task 2, “Direct predicate values and semantic views (01a),” from
`docs/superpowers/plans/2026-10-08-package-predicate-foundations.md`.
The full specification and plan are approved; direct predicate storage and scoped
И notation are settled. Execute natively yourself, one complete numbered task
per fresh context. Do not restart brainstorming or request the same approvals.
Stop before Task 3. Phase 01a requires Tasks 1–3; PKG-01 and its independent
whole-change review (Task 8) remain open.

Work in `/home/fab/Documents/nominal/nominal`. Expected branch:
`fasapa/nominal-package`; last verified HEAD:
`3c9d8dc527f7705b24c0308a2527e659ae933874`. Inspect actual status/history/source.
Preserve all existing modified/untracked work, including Task 1 and research/
article documents. Do not switch branches, create a worktree, commit, push,
merge, publish, upgrade dependencies or add CI. Reuse completed F02–F05.

Read AGENTS.md, README.md, Package/README.md, the approved specification
`docs/superpowers/specs/2026-10-07-package-predicate-foundations-design.md`,
the plan's constraints/review focus/evidence conventions and all of Task 2,
and the active `docs/nominal-package-roadmap.md` with its latest Task 1 record.
Inspect actual PredicateLogic/PredicateSupport/SupportedFunction/FunctionAction
source and pinned Mathlib. Preserve historical `docs/roadmap.md`.

Task 1 is complete, uncommitted: PredicateLogic exports all 23 planned ordinary
logical/quantifier theorems through Package. Its public consumer, build, direct
axiom audit, import coverage, article and preservation checks passed. Evidence:
`/tmp/nominal-package-pkg01-execution.WReW3a/`. Verify this directory exists;
read progress.md, initial-snapshot.json, final-snapshot.json, validation-*.json
and 01Logic.lean. Recreate missing evidence if necessary without reimplementing
Task 1. Take a new Task 2 preservation snapshot and retain earlier evidence.

Create 02Carrier.lean there using import Package and autoImplicit false. Follow
Task 2's exact names/contracts and red-to-green steps: direct proof-field record,
one Prop-valued FunLike coercion, Iff ext, literal/named certificates, semantic
views, action/support/nominality, supported-subset BooleanSubalgebra and transferred
Boolean structure. Verify independent universes, action separation, proof changes,
higher-order use, two atom sorts and least-support agreement. No placeholders.
Reconcile the article, run Task 2's checks plus Package audit/import coverage,
compile LaTeX externally, update task/roadmap evidence and status, confirm
preservation, and provide a copyable Task 3 prompt. Then stop.
```

### 2026-10-08 — Task 2 complete: direct predicate values and semantic views

**Delivered uncommitted; phase 01a and PKG-01 remain open.** Task 3 is still
required for 01a. No Task 3 implementation was started, and the independent
whole-change review remains Task 8. No mathematical contract or hypothesis
changed; there were no mathematical rulings or deferred findings in this task.

Evidence remains `/tmp/nominal-package-pkg01-execution.WReW3a/`.
Earlier Task 1 evidence was present and preserved. Task 2's separate baseline is
`task-2-initial-snapshot.json`, `task-2-initial.diff` and `task-2-baseline/`, covering
152 existing files, branch, HEAD, status and index. `task-2-brief.md` and the
appended `progress.md` retain the task and ledger. Execution follows the explicit
user constraints: existing checkout, external evidence, no commits/worktree,
native implementation and stop at the numbered-task boundary.

Created `Package/Foundations/SupportedPredicate.lean` and exported it through
`Package`. The direct record has only `toFun : X → Prop` and proof-only
`supported : FinitelySupportedPred A toFun`. Delivered interfaces include:

- `instFunLike`, `ext`, the `@[ext]`-generated `ext_iff`, `congr_apply`,
  `ofFun/ofSupports/ofInvariant`, constructor application/coercion simp and
  `ofFun_proof_irrel`; both `coe_ofFun` and `coe_ofFun_exists` handle the two
  certificate forms without changing F05's reducibility.
- `toMap/ofMap/mapEquiv`, `toObject`, `toSet/ofSet`, their computation, inverse
  and action laws, including `toObject_eq` and `toSet_ofSet`.
- `instMulAction` via `renamePred` and injective transfer through `toObject`,
  `smul_apply/smul_apply_smul`, `supports_iff` and
  `supports_iff_toMap/toObject/toSet`, and `instNominal`.
- `toObject_finitelySupported`, `toSet_finitelySupported`,
  `support_toMap/toObject/toSet`, retaining elementwise full-view certificates
  and agreement with independently supplied evidence.
- `supportedSets` as Mathlib's `BooleanSubalgebra`, `subsetEquiv`,
  `mem_subsetEquiv`, the restricted image action with `val_smul_supportedSets`,
  `subsetEquiv_smul`, subtype nominality, `support_subsetEquiv`, and the single
  `instBooleanAlgebra` transferred using `Equiv.booleanAlgebra`.

Basic construction, action, nominality and Boolean structure retain independent
atom/carrier universes and require only the selected action on X. Least support
adds Infinite A. No Prop action, competing bare-arrow/Set action, full-powerset
nominality, chosen-support data, manual Boolean algebra or Task 3 operation
layer was added. The pinned Mathlib revision was checked as
`d13f23b723b8a846827a245b89c10fc7d3f11612` before using its transfer machinery.

`02Fixtures.lean` first passed using only delivered foundations.
`02Carrier.lean` then failed on missing SupportedPred names (exit 1;
`02Carrier-red.log`, reaching Lean's 100-error limit). The completed consumer
passes ordinary Prop application, Iff ext, rw/simp, higher-order application,
named/literal certificates, enlarged bounds, both equivalence round trips,
independent universes, two atom sorts (also on one carrier), view renaming,
nominality without Nominal X, Boolean computation and least-support witness
independence. A computable reconstruction keeps least-support choice inside
its certificate. A fixed-atom predicate is proved noninvariant, and the larger
`{0,1,2}` bound is consumed to prove its renamed proposition. Bare-arrow action
is tested on an actually acted codomain; Set-image membership is tested both by
inverse precomposition and by an explicit image witness.

The consumer also guards the observed failures to infer a Prop action or
Nominal Set Nat, and rejection by `ofSet` of a certificate for an independently
selected Set action. These guards pass, including the standalone
`02ActionBoundary.lean`. Additional higher-order map/Set constructor checks
already passed using existing simp rules (`02Carrier-views-red.log` is exit 0);
no extra coercion infrastructure was needed.

Resolved diagnostics: the first build attempted a redundant manual `ext_iff`,
which Mathlib's `@[ext]` had already generated, and omitted `(B := A)` from a
partially applied general support-reflection theorem. The duplicate was removed
and the atom carrier made explicit. A consumer's unnecessary `simpa` was changed
to `simp at he`. Final production/consumer checks have no warnings or errors;
guarded negative diagnostics are intentional and fully matched.

Checks actually run in this context, all final exits 0:

- `lake build Package.Foundations.SupportedPredicate Package` — 985 jobs;
  SupportedPredicate and Package freshly elaborated with cached dependencies
  (`task-2-build-2.log`). The earlier failed build is retained separately.
- `lake build Package.Foundations.SupportedPredicate Package +Package.Tests.AxiomAudit`
  — 986 jobs; production artifacts cached from the affected build, audit freshly
  elaborated (`task-2-final-build.log`).
- `lake env lean /tmp/nominal-package-pkg01-execution.WReW3a/02Carrier.lean`
  — fresh consumer elaboration and representative signature/axiom prints
  (`02Carrier-final.log`). `mapEquiv`, `subsetEquiv`, `supports_iff`,
  `instNominal`, `support_toSet` and `instBooleanAlgebra` depend only on
  `propext`, `Classical.choice`, `Quot.sound`.
- `lake env lean /tmp/nominal-package-pkg01-execution.WReW3a/01Logic.lean`
  — freshly rerun, source unchanged (`task-2-01Logic.log`). Earlier Task 1 logs
  remain prior-context evidence.
- `lake env lean Package/Tests/AxiomAudit.lean` — fresh direct audit of 703
  production declarations from 16 defining modules, with only the three
  standard foundations (`task-2-axiom-audit.log`).
- `python3 Package/Scripts/check-imports.py` — all 17 production source modules
  (including Package) and the one audit source reached (`task-2-import-coverage.log`).
- `lake build Nominal Instances Examples` — 1033 cached jobs; reference audit
  output replayed, not freshly elaborated (`task-2-reference-build.log`).
- From `docs/article`, `latexmk -pdf -interaction=nonstopmode -halt-on-error
  -outdir=/tmp/nominal-package-pkg01-execution.WReW3a/task-2-article-build main.tex`
  — fresh external output directory, 38-page PDF, no warnings or overfull/underfull
  boxes (`task-2-article.log`, `task-2-article-build/main.log`). The exposition now
  explains direct proof-field storage, semantic views, support agreement and
  the transferred Boolean structure; it contains no task/approval/evidence metadata.
- `git diff --check`, staged diff check, changed/new-file whitespace, local
  Markdown target checks, admission scan and task-boundary checks pass.
  `task-2-validation-lean.json` and `task-2-validation-article.json` record
  commands, working directories and exits.

Preservation: `task-2-check-preservation.py`, `task-2-preservation.log` and
`task-2-final-snapshot.json` confirm 143 of 152 baseline files byte-identical,
exactly nine intentionally reconciled existing files, and only the new
SupportedPredicate source added. The nine are the public root, Package README,
predicate article section, active roadmap, plan, spec, current predicate research
report, readiness summary and research index. `task-2-only.diff` isolates this
context's changes from earlier work. Task 1's PredicateLogic, all research probes,
existing article entry/quotient work, other research files, reference source,
historical roadmap, pinned dependencies, branch `fasapa/nominal-package`, HEAD
`3c9d8dc527f7705b24c0308a2527e659ae933874` and index are unchanged. No commit,
push, worktree, dependency or CI operation was performed.

Task 3 owns the additional bundled logical/quantified/collection operations and
all their named computation, bound and action laws. The Boolean instance is
already delivered and must be reused. Descent and fresh quantification remain
later tasks. The copyable handoff is retained as `Task3-handoff.txt` in the
external evidence directory and immediately below in the plan execution record.

### Copyable fresh-context prompt for Task 3

```text
$superpowers:executing-plans

Implement ONLY Task 3, “Bundled logical and quantified operations (01a),” from
`docs/superpowers/plans/2026-10-08-package-predicate-foundations.md`.
The full specification and plan are approved. Direct predicate storage and
scoped И notation are settled. Execute natively yourself, one complete numbered
task per fresh context. Do not restart brainstorming or repeat approvals.
Complete Task 3's implementation, verification and documentation, then stop
before Task 4. Tasks 1–3 close phase 01a; PKG-01 remains open for Tasks 4–8.
The independent whole-change review remains assigned to Task 8.

Work in `/home/fab/Documents/nominal/nominal`. Expected branch:
`fasapa/nominal-package`; last verified HEAD:
`3c9d8dc527f7705b24c0308a2527e659ae933874`. Inspect actual status/history/source.
Preserve all existing tracked, staged and untracked work, including uncommitted
Tasks 1–2, research probes and article changes. Do not switch branches, create
a worktree, commit, push, merge, publish, upgrade dependencies or add CI.
F02–F05 and Tasks 1–2 are complete; reuse them without reimplementation.

Read AGENTS.md, README.md, Package/README.md, the approved specification
`docs/superpowers/specs/2026-10-07-package-predicate-foundations-design.md`,
the plan's constraints/review focus/evidence conventions and all of Task 3,
and the latest Task 2 delivery in `docs/nominal-package-roadmap.md`.
Inspect actual PredicateLogic, SupportedPredicate, PredicateSupport,
SupportedFunction and relevant support/freshness source and pinned Mathlib.

Evidence: `/tmp/nominal-package-pkg01-execution.WReW3a/`. Verify files exist;
read progress.md, task-2-brief.md, task-2-initial-snapshot.json,
task-2-final-snapshot.json, task-2-validation-lean.json,
task-2-validation-article.json, 01Logic.lean and 02Carrier.lean.
Preserve earlier evidence and take a new Task 3 preservation snapshot. Recreate
missing checks from source without repeating completed implementation.

Task 2 created/exported SupportedPredicate.lean: the direct proof-field
SupportedPred, one Prop-valued FunLike, Iff ext (including generated ext_iff),
named/literal constructor simp, map/object/set/subset views, inverse-precomposition
action, support correspondence, nominality, elementwise least-support agreement,
supportedSets BooleanSubalgebra with restricted image action, and the single
instBooleanAlgebra transferred through subsetEquiv. Basic interfaces have
independent universes and need no Nominal X, Infinite A or DecidableEq A.
There is no global Prop action, competing bare-arrow/Set action, or Nominal Set X.
The Boolean instance is already delivered; its named operation laws are Task 3.

Create/export `Package/Foundations/SupportedPredicateLogic.lean`. Implement
Task 3's exact names/contracts: Boolean/order computation and coe laws, biimp,
precomp/precompMap, section, all/ex, collectionUnion/collectionInter, simultaneous
action laws, sufficient bounds and least-support results. Derive the collection
operations from jointly invariant evaluation and ordinary quantification;
reuse F05 for map composition and individual supported parameters. Do not add a
second algebra, curry hierarchy or unrestricted CompleteLattice. Keep ordinary
predicates legal and retain the specified weak hypotheses and independent universes.

Create `03Quantifiers.lean` in the evidence directory, importing Package with
`set_option autoImplicit false`. Watch planned missing names fail before
implementation, then pass. Cover empty and proved nonnominal quantified carriers,
restricted combined bodies, an individually supported parameter in a nonnominal
carrier, supported collections using their bound, and genuine support loss.
Inspect the specified signatures and #print axioms. No admissions or disabled checking.

Run the Task 3 build/consumer and Package's direct axiom audit/import coverage,
rerun 01Logic.lean and 02Carrier.lean for the shared interfaces, and run
`git diff --check`. Reconcile the article and current interface/status summaries;
compile LaTeX with output outside the repository. Keep operational metadata out
of the manuscript and add no persistent Package Examples layer. Record actual
commands, results, diagnostics and cache conditions; distinguish this context's
checks from earlier evidence. Confirm preservation of unrelated work, pinned
dependencies, branch, HEAD and index. Update Task 3's checkboxes and phase 01a
only when its full criterion passes, keep PKG-01 open, give a copyable Task 4
fresh-context prompt, then stop.
```

### 2026-10-08 — Task 3 complete: bundled logic and quantification; phase 01a complete

**Delivered uncommitted. Tasks 1–3 and phase 01a are complete; PKG-01 remains
IN PROGRESS for Tasks 4–8.** Task 4 is the first task of phase 01b and was not
started. The independent whole-change review remains assigned to Task 8.
No mathematical contract or hypothesis changed, and no finding was deferred.

Evidence remains `/tmp/nominal-package-pkg01-execution.WReW3a/`.
All required earlier evidence was present and read, including `progress.md`,
`task-2-brief.md`, `task-2-final-snapshot.json`, both Task 2 validation JSON files,
and the `01Logic.lean` and `02Carrier.lean` consumers. Every file hash in the
Task 2 final snapshot matched the actual checkout. Task 3 took a new baseline:
`task-3-initial-snapshot.json`, `task-3-initial.diff`, `task-3-baseline/` (153
files), and `task-3-brief.md`. Earlier evidence is retained; only the shared
ledger is appended. Explicit user instructions continue to govern execution:
native work in the existing checkout, external evidence, no commits/worktree,
and stop at this numbered-task boundary.

Created `Package/Foundations/SupportedPredicateLogic.lean` and exported it from
`Package`. It reuses the single BooleanAlgebra delivered by Task 2 and F05's
ordinary precomposition/section laws. Delivered interfaces in `SupportedPred`:

- Boolean/order `*_apply` and `coe_*` simp laws for bot/top/inf/sup/complement,
  implication and difference; `le_def`; derived `biimp` with both computation laws.
- `precomp`, `precompMap`, individually certified `section`, jointly acted
  `all`/`ex`, and `collectionUnion`/`collectionInter`, each with application and
  coerced-function equations. `coe_section_exists` additionally handles literal
  parameter certificates without changing foundational reducibility.
- All planned Boolean/operator action laws, including order reflection,
  simultaneous predicate/map and relation/parameter renaming, quantifier
  reindexing and collection renaming.
- `supports_compl_iff`, binary/precomposition/section union bounds,
  `supports_all/ex/collectionUnion/collectionInter` retaining the very same
  input bound; empty support of bot/top, exact `support_compl`, and all planned
  `support_*_subset` laws. Difference and the supported-map adapter have the
  corresponding bounds too. Ordinary precomposition uses the exact supplied
  `hf.toObject.support`; a section uses `hy.support`.

Collection operations construct supported guarded relations from jointly
invariant evaluation, then use ordinary universal/existential quantification
over the ambient supported-predicate carrier. This is neither an external
arbitrary-family join nor an unrestricted CompleteLattice. No second Boolean
algebra, curry hierarchy, Prop action, bare-arrow/Set action, or new general
infrastructure was introduced. Basic operators preserve independent universes
and require only selected actions. Infinite atoms occur only in least-support
corollaries; decidable equality occurs only on displayed finite unions.
Pinned Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612` and the existing
Boolean transfer/computation sources were inspected before implementation.

`03Fixtures.lean` first compiled using only existing source (exit 0).
`03Quantifiers.lean` then failed on missing Task 3 names, before production
edits (`03Quantifiers-red.log`; initial 100-error cap). A consumer typo applying
`inf_bot_eq` without its argument was corrected, and the diagnostic run with
`-DmaxErrors=1000` records all missing-interface failures in
`03Quantifiers-red-2.log`. This diagnostic-only option changes error reporting,
not proof checking. Final consumers use the requested direct Lean command.

The passing consumer covers every planned name and printed signature, all
Boolean computations including implication/difference/order, named/literal
higher-order use, restricted quantification through separately bundled or only
combined certified bodies, generic empty quantified carriers, a concrete empty
carrier over finite Bool atoms, and genuinely non-nominal full function objects.
The latter carrier is proved non-nominal using an unsupported constant under
left multiplication, while its supported identity is fixed using only its
individual certificate. Supplied relation/parameter and collection bounds
prove actual renamed propositions. Both collection bounds are consumed in
renamed union/intersection conclusions. Operator action equations are checked,
including explicit Equivariant consumers. A singleton-supported zero predicate
has least support `{0}`, whereas its intersection with bottom has empty support,
so support loss is proved strict rather than merely asserted.

Resolved diagnostics: Lean reserves the token `section`, so the declaration
uses `«section»` while retaining the required public name. A higher-order
`xs.map (p \ q)` can elaborate at the Pi arrow type; the `pp.all` probe
`03SdiffInference.lean/.log` established this. Consumers now explicitly select
`(p \ q : SupportedPred A X)` to exercise the bundled coercion. A literal section
certificate then reproduced the semireducible-support simp issue already known
from Task 2 (`03Quantifiers-green-2.log`); `coe_section_exists` resolves it locally.
The concrete `Discrete Bool Empty` fixture supplies its own IsEmpty witness.
The final log scan caught the proof-local `letI` style warning; replacing it with
`let` and re-elaborating the consumer removed it (`03Quantifiers-final-warning.log`
retains the original diagnostic). All final production/consumer output is free of warnings and errors; Task 2's
intentional guarded diagnostics still match.

Commands actually run here, all final exits 0:

- `lake build Package.Foundations.SupportedPredicateLogic Package` — 986 jobs;
  new module and public root freshly elaborated using cached dependencies
  (`task-3-build-3.log`; earlier failed/successful iterations retained separately).
- `lake build Package.Foundations.SupportedPredicateLogic Package +Package.Tests.AxiomAudit`
  — 987 jobs; production artifacts cached from the affected build, audit freshly
  elaborated (`task-3-final-build.log`).
- `lake env lean /tmp/nominal-package-pkg01-execution.WReW3a/03Quantifiers.lean`
  — fresh elaboration; all consumers, exact signatures and representative axiom
  prints pass (`03Quantifiers-final.log`). `all_smul`, `section_smul`,
  `supports_collectionUnion`, `support_compl` use only `propext`,
  `Classical.choice`, `Quot.sound`.
- `lake env lean /tmp/nominal-package-pkg01-execution.WReW3a/01Logic.lean` and
  `lake env lean /tmp/nominal-package-pkg01-execution.WReW3a/02Carrier.lean`
  — both freshly elaborated, sources unchanged (`task-3-01Logic.log`,
  `task-3-02Carrier.log`). Earlier-context logs remain earlier evidence.
- `lake env lean Package/Tests/AxiomAudit.lean` — fresh direct audit: 818
  production declarations from 17 defining modules, with only the three standard
  foundations (`task-3-axiom-audit.log`). No admissions or additional axioms.
- `python3 Package/Scripts/check-imports.py` — all 18 production sources
  (including Package) and the one audit source reached (`task-3-import-coverage.log`).
- `lake build Nominal Instances Examples` — 1033 cached jobs; reference audit
  output replayed, not freshly elaborated (`task-3-reference-build.log`).
- From `docs/article`, `latexmk -pdf -interaction=nonstopmode -halt-on-error
  -outdir=/tmp/nominal-package-pkg01-execution.WReW3a/task-3-article-build main.tex`
  — fresh external output, 39-page PDF, no warnings or overfull/underfull boxes
  (`task-3-article.log`, `task-3-article-build/main.log`). The manuscript explains
  precomposition/sections, operator action and least bounds, empty quantification,
  and the guarded collection construction, with no task or verification metadata.
- `git diff --check`, staged diff check, changed/new-file whitespace and local
  Markdown target checks, admission scan, phase/task-boundary and preservation
  checks pass (`task-3-check-preservation.py`, `task-3-preservation.log`).

`task-3-validation-lean.json` and `task-3-validation-article.json` record commands,
working directories, durations and results. These are checks against cached
Lean/Mathlib dependencies, not a clean dependency bootstrap. There were no
unavailable required tools. No larger-client performance claim is made.

Phase 01a acceptance now passes as a whole:

| Criterion | Fresh evidence |
| --- | --- |
| Ordinary logical, joint/restricted/uniform support | Unchanged `01Logic.lean` rerun |
| Direct ordinary use, all views, coherent action/nominality and support agreement | Unchanged `02Carrier.lean` rerun, including action-separation guards |
| Single transferred Boolean structure and named logical/order laws | Both carrier and quantifier consumers; Task 2 source byte-identical |
| Sections, whole-carrier quantification, supported collections, empty/non-nominal clients and support loss | `03Quantifiers.lean`, including renamed conclusions and simultaneous action equations |
| Public root, imports, trusted proofs and reconciled exposition | Package build, fresh audit, coverage, signatures/axioms and external article build |

Preservation: `task-3-check-preservation.py` / `task-3-final-snapshot.json`
confirm 144 of 153 baseline files byte-identical, exactly nine intentional
reconciliations and only the new SupportedPredicateLogic source added. The nine
are Package.lean, Package README, predicate article, active roadmap, plan, spec,
current predicate research report, readiness summary and research index.
`task-3-only.diff` isolates these edits from existing uncommitted work. Earlier
PredicateLogic/SupportedPredicate source, consumers/evidence, all research probes,
existing article entry/quotient work, reference sources, historical roadmap,
dependency pins, branch `fasapa/nominal-package`, HEAD
`3c9d8dc527f7705b24c0308a2527e659ae933874`, and index are preserved. No commit,
push, merge, worktree, dependency upgrade or CI operation occurred.

Task 4 owns the general scalar/function/predicate pullback adapters and ordinary
quotient-predicate correspondence. It must preserve the explicit canonical-action
boundary and action-free ordinary descent. The complete fresh-context prompt is
`Task4-handoff.txt` in the evidence directory and in the plan's next section.

### Copyable fresh-context prompt for Task 4

```text
$superpowers:executing-plans

Implement ONLY Task 4, “General pullback and ordinary quotient predicates (01b),”
from docs/superpowers/plans/2026-10-08-package-predicate-foundations.md.

The full specification and implementation plan are approved. Direct predicate
storage and scoped И notation are settled. Execute natively yourself, one complete
numbered task per fresh context. Do not restart brainstorming or request the same
approvals. Complete Task 4's implementation, verification and documentation, then
stop before Task 5. Tasks 1–3 and phase 01a are complete, uncommitted. PKG-01 remains
open for Tasks 4–8; the independent whole-change review remains assigned to Task 8.
Phase 01b requires both Tasks 4–5; Task 4 alone does not close it.

Work in /home/fab/Documents/nominal/nominal. Expected branch: fasapa/nominal-package.
Last verified HEAD: 3c9d8dc527f7705b24c0308a2527e659ae933874. Inspect actual status,
history and source before editing. Preserve all existing tracked, staged and
untracked work, including Tasks 1–3, research probes and article changes. Do not
switch branches, create a worktree, commit, push, merge, publish, upgrade dependencies
or add CI. Reuse F02–F05 and Tasks 1–3 without reimplementation. Preserve the reference
library and historical docs/roadmap.md; use docs/nominal-package-roadmap.md.

Read first: AGENTS.md, README.md, Package/README.md; the approved specification
at docs/superpowers/specs/2026-10-07-package-predicate-foundations-design.md; the
plan's constraints, Review Focus, evidence conventions and all of Task 4; the active
roadmap's latest Task 3 delivery. Read relevant research and the retained descent
probe at docs/research/probes/2026-10-07-pkg01-descent.lean, the predicate article,
and actual ActionSupport, FunctionAction, PredicateSupport and quotient sources.
Inspect pinned Mathlib, particularly Setoid.liftEquiv, Function.FactorsThrough and
existing support reflection. Task 4 has no dependency on SupportedPred.

Evidence directory: /tmp/nominal-package-pkg01-execution.WReW3a/
Verify its files exist. Read progress.md, task-3-brief.md, task-3-delivery-record.md,
task-3-final-snapshot.json, task-3-validation-lean.json,
task-3-validation-article.json, 01Logic.lean, 02Carrier.lean and 03Quantifiers.lean.
Preserve earlier evidence and take a new Task 4 preservation snapshot. Recreate
missing checks from source without repeating completed implementation.

Task 3 supplies SupportedPredicateLogic.lean through Package: Boolean/order
computation, biimp, ordinary certified precomp and SupportedMap precompMap,
individually certified section, jointly acted all/ex, supported collection
union/intersection, simultaneous action laws, sufficient bounds and least-support
consequences. It reuses Task 2's single Boolean instance. coe_section_exists handles
literal support evidence without changing reducibility. In higher-order consumers,
annotate overloaded Boolean operations as SupportedPred to select that carrier.
All three consumers were freshly rerun; direct audit checks 818 declarations in
17 defining modules, import coverage reaches 18 production sources plus one audit.
The article compiles to 39 pages without diagnostics. Dependencies were cached;
no clean dependency bootstrap is claimed. Branch, HEAD, index, earlier sources,
research probes, unrelated article changes and earlier evidence were preserved.

Implement Task 4's exact names/contracts: scalar invariant_pullback_iff with only
SMul; FunctionObject precomp/application/coercion/injectivity/action and arbitrary-
set supports_precomp_iff under DivisionMonoid; ordinary predicate pullback support
preservation/reflection, renaming and elementwise exact least support; PredicateDescent
Compatible, ordinary adapters, pullback/descend/ordinaryEquiv, computation, round
trips, proof independence and existence/obstruction results; explicit canonical-
quotient support and renaming laws. Use Mathlib's correspondence, not a selected
representative. Keep atom/carrier universes independent and hypotheses minimal.
All quotient-action-dependent theorem types select QuotientAction.mulAction s hs;
none may certify an unrelated chosen quotient action. No bundled descent or fresh
quantification in this task. No admissions, custom axioms or disabled checking.

Create 04Descent.lean externally, importing Package with autoImplicit false, and
follow the missing-name-to-passing cycle. Cover exact scalar/DivisionMonoid
signatures, ordinary unsupported descent and round trips, arbitrary supplied-bound
reflection, canonical quotient specialization, the non-surjective diagonal
counterexample, alpha-incompatible binder-label predicate, true-flag unsupported
quotient induction, and the equality quotient with an unrelated trivial action.
Inspect exact signatures and representative #print axioms.

Run Task 4's affected-module/public builds, 04Descent.lean, all three earlier
consumers, lake build Package +Package.Tests.AxiomAudit, direct
lake env lean Package/Tests/AxiomAudit.lean, python3 Package/Scripts/check-imports.py,
and git diff --check. Reconcile the article and current interface/status docs;
compile LaTeX with output outside the repository. Keep task IDs, approvals and
verification records out of the manuscript. Add no persistent Package Examples.

Record actual commands/results/diagnostics/cache conditions/evidence paths,
distinguish fresh checks from earlier evidence, confirm preservation including
branch/HEAD/index/pins, update Task 4's checkboxes and the active roadmap, and
provide a copyable fresh-context Task 5 prompt carrying the approved state forward.
Keep phase 01b and PKG-01 open, and stop before implementing Task 5.
```

### 2026-10-08 — Task 4 delivered: ordinary pullback and quotient predicates

**Complete, uncommitted. Phase 01b continues with Task 5 in this run.** The author
explicitly changed this run to phase granularity; Task 6 is the stopping boundary.
Task4-handoff.txt was a START prompt, not a delivery. At entry all 154 files
matched the Task 3 final snapshot; no Task 4 production source or consumer existed.

Extended ActionSupport, FunctionAction and PredicateSupport; created/exported
PredicateDescent. The scalar parent requires only SMul. Full-object precomposition
is action-free, injective for surjections, and equivariant under DivisionMonoid;
ActionSupport.supports_map_iff reflects arbitrary sets. Ordinary predicate
pullback preserves bounds using F05 and reflects them through the scalar parent.
Elementwise least support agrees under surjectivity, with Infinite A only there.
Ordinary compatibility, kernel/fiber adapters, Mathlib liftEquiv correspondence,
computation, round trips, proof independence and obstruction require no action
or support. All canonical support/renaming theorem types select the quotient action.

External evidence: `/tmp/nominal-package-pkg01-execution.WReW3a/`.
`04Fixtures-green.log` passes existing foundations; `04Descent-red.log` records
missing interfaces before production edits. Final `04Descent.lean` proves both
support directions at arbitrary bounds, independent-universe SMul/DivisionMonoid
signatures, ordinary unsupported descent and quotient induction, diagonal
non-surjectivity failure, singleton-supported incompatible binder labels, and
rejection/non-equivariance of an unrelated trivial equality-quotient action.

Commands/results: `task-4-verified-validation.json` records exit 0 for
`lake build Package +Package.Tests.AxiomAudit`, each of `04Descent.lean`,
`01Logic.lean`, `02Carrier.lean`, `03Quantifiers.lean` via `lake env lean`,
`lake env lean Package/Tests/AxiomAudit.lean`, `python3 Package/Scripts/check-imports.py`,
`git diff --check`, and external latexmk. Affected-module build also passes
(`task-4-build-4.log`, 987 jobs). Audit build: 988 jobs, dependencies cached;
changed project modules were freshly built, and all consumers/direct audit freshly
elaborated. Audit: 858 declarations / 18 defining modules, only the standard three
axioms; scalar reflection is axiom-free. Coverage: 19 production sources plus audit.
No clean dependency bootstrap is claimed.

Resolved diagnostics: copied fixture lacked an explicit A binder under
`autoImplicit false`; equivariance rewriting needed its explicit scalar/input;
proof-local letI style and a class-valued fixture definition were corrected;
the unrelated-action fixture needed its kernel equality exposed. No mathematical
statement changed. Article line overflow was repaired by splitting a long Lean
name into namespace and declaration; final external
`latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir=/tmp/nominal-package-pkg01-execution.WReW3a/task-4-article-final main.tex`
from docs/article exits 0, 39 pages, no warnings or box diagnostics. Earlier logs
remain available. No mathematical rulings or deferred findings.

Article exposition now covers the nonempty diagonal counterexample, arbitrary-set
DivisionMonoid reflection, ordinary unsupported quotient induction, canonical action
selection and the distinction from object support. PKG-01 remains open; the
supported correspondence is Task 5, cofinite theory Tasks 6–7, final review Task 8.

### 2026-10-08 — Task 5 delivered: supported quotient correspondence; phase 01b complete

**Tasks 4 and 5 and their combined phase 01b acceptance criteria pass.** All
changes remain uncommitted. PKG-01 stays IN PROGRESS for Tasks 6–8. Task 6 has
not started; the independent whole-change review remains assigned to Task 8.
The author explicitly authorized Tasks 4–5 together in this run, superseding
only that part of the earlier per-task context boundary. No mathematical ruling
or deferred finding was needed.

Created and exported `Package/Foundations/SupportedPredicateDescent.lean`;
added the six action-free `Compatible.const/not/and/or/imp/iff` adapters to
PredicateDescent. Task 4's declarations remain unchanged. Delivered:

- `SupportedPred.pullback`, application/coercion computation, fixed-map action
  compatibility, same-bound preservation, every-bound reflection under
  surjectivity, and least-support equality with Infinite A.
- `CompatiblePred A s`, `compatibleAction A s hs` via Mathlib SubMulAction,
  `compatible_val_smul`, `supports_compatible_iff`, and explicit
  `compatibleNominal`. No instance guesses invariance or a quotient action.
- `descendSupported`, `supportedEquiv`, representative equations, both named
  inverse equations and action laws in both directions. Quotient-dependent
  types select the canonical action; action/support statements additionally
  select the compatible-subtype action.
- `supports_descendSupported_iff`, `supports_supportedEquiv_iff`,
  `support_supportedEquiv` and `freshWith_supportedEquiv_iff`. Basic laws
  require neither source nor quotient nominality. Infinite A occurs only in
  least support/freshness; the context uses its individual certificate with
  an independent universe, without Nominal on its carrier.
- Pullback and descent preserve top, bottom, complement, inf, sup, implication
  and biimplication through the existing Boolean structure. No second Boolean
  algebra, dependent data descent, binders or fresh quantifier was introduced.

Evidence remains `/tmp/nominal-package-pkg01-execution.WReW3a/`.
`05SupportedDescent-red.log` records the missing bundled/connector names before
implementation; `05Fixtures.log` independently passes the existing label and
non-nominal context fixtures. The final consumer proves computations, both
inverses, both action directions and exact sufficient/least support, including
freshness against a supported identity in a provably non-nominal function
carrier. It rejects implicit action guessing and passing a predicate certified
under an unrelated trivial quotient action to the canonical correspondence.
The quotient forgetting a discrete Bool label accepts equality with a fixed
atom at both labels, retains every supplied enlarged bound, computes after a
moving swap, and has exact singleton least support over infinite atoms.
The full public inventory has 79 new declarations across Tasks 4–5;
`Phase01bSignatures.lean` checks each, and the consumer additionally prints
explicit selected actions and representative axioms.

The combined acceptance checks preserve Task 4's unsupported ordinary descent
and quotient induction, scalar/DivisionMonoid generality and independent
universes, non-surjective diagonal obstruction, supported incompatible binder
observation and rejection of an unrelated quotient action. These tests are
external public-import consumers with autoImplicit false; no persistent Package
Examples layer was added.

Actual final commands/results are in `phase-01b-final-validation.json`, all exit 0:

- `lake build Package +Package.Tests.AxiomAudit` — 989 jobs, cached after
  iterative affected builds. `lake build Package.Foundations.SupportedPredicateDescent Package`
  freshly built the new module/root using cached dependencies (988 jobs,
  `task-5-build-3.log`). No clean dependency bootstrap is claimed.
- `lake env lean` on each of `04Descent.lean`, `05SupportedDescent.lean`,
  `01Logic.lean`, `02Carrier.lean`, `03Quantifiers.lean`, and
  `Phase01bSignatures.lean` in the evidence directory — fresh elaborations;
  final logs have no errors or warnings. Phase 01a's three consumer sources are unchanged.
- `lake env lean Package/Tests/AxiomAudit.lean` — fresh direct audit of 918
  declarations in 19 defining modules, allowing only propext, Classical.choice
  and Quot.sound. The cached build's audit output is distinguished from this run.
- `python3 Package/Scripts/check-imports.py` — all 20 production source modules
  (including the public root) and the separate audit are reached.
- `lake build Nominal Instances Examples` — 1033 cached jobs; reference audit
  output replayed, not a fresh reference audit.
- From `docs/article`, `latexmk -pdf -interaction=nonstopmode -halt-on-error
  -outdir=/tmp/nominal-package-pkg01-execution.WReW3a/phase-01b-final-article-build main.tex`
  — fresh external output, 40-page PDF, no warnings, unresolved references or
  overfull/underfull boxes.
- `git diff --check` — clean; final preservation validation also checks staged
  whitespace, changed-file whitespace and local Markdown targets.

Resolved diagnostics are retained: an omitted implicit element binder in
SubMulAction's closure field; a consumer biimplication needing explicit local
quotient action; a consumer rewrite requiring its local let exposed. The first
combined article build failed on an undefined support macro and line overflow;
ordinary operator notation and shorter sentences resolved both. The final full
validation is green; no diagnostics are suppressed and no hypotheses changed.

The article now develops the supported equivariant correspondence, exact bounds,
individual-context freshness, inherited logical operations and duplicate-label
example. Current README, specification, plan, research summaries and active
tracker describe the delivered interface. Historical records and prompts remain
historical; Task4-handoff.txt is preserved as a start prompt, not reclassified
as delivery. The manuscript contains no task or operational metadata.

Preservation evidence: `phase-01b-initial-snapshot.json`, `phase-01b-baseline/`,
`task-4-final-snapshot.json`, `phase-01b-final-snapshot.json`,
`phase-01b-only.diff` and `phase-01b-preservation.log`. Of 154 starting repository
files, 142 are byte-identical, twelve are intentional source/interface/status
reconciliations, and the two descent modules are new. All 417 earlier evidence
files are preserved (the shared ledger retains its exact original prefix).
Phase 01a sources and consumers, all research probes, unrelated article/research
work, the reference library, historical roadmap, dependency pins, branch, HEAD
and index are unchanged. Branch remains fasapa/nominal-package; HEAD remains
3c9d8dc527f7705b24c0308a2527e659ae933874; index SHA-256 remains
462fdfad827bcfebf9cf0239d1c5d0917226206646acc3270bd8892ffcd3a8ba.
No commits, branch/worktree changes, publication, dependency changes or CI edits.

Next: Task 6 begins phase 01c. `Task6-handoff.txt` contains the copyable prompt,
also retained in the plan below. Task 6 alone will not complete 01c; Task 7
and final integration/independent review in Task 8 remain required for PKG-01.

### Copyable fresh-context prompt for Task 6

```text
$superpowers:executing-plans

Implement ONLY Task 6, “Ordinary cofinite quantification and supplied-bound
Some/Any (01c),” from
  docs/superpowers/plans/2026-10-08-package-predicate-foundations.md.

The specification and implementation plan are approved. Execute natively yourself;
do not restart brainstorming or request the same approvals. Complete Task 6's
implementation, verification and documentation, then stop before Task 7. This
begins phase 01c; Task 6 alone does not close it. Tasks 1–5 and phases 01a–01b
are complete, uncommitted. PKG-01 remains open for Tasks 6–8; the independent
whole-change review remains Task 8.

Work in /home/fab/Documents/nominal/nominal.
Expected branch: fasapa/nominal-package.
Last verified HEAD: 3c9d8dc527f7705b24c0308a2527e659ae933874.
Inspect actual status, branch, history and source before editing. Preserve all
tracked, staged and untracked work, including foundations, Tasks 1–5, research
probes and article changes. Do not switch branches, create a worktree, commit,
push, merge, publish, upgrade dependencies or add CI. Use the current checkout,
Package/ and docs/nominal-package-roadmap.md; preserve the reference library and
historical docs/roadmap.md. Reuse the F05 hybrid and phases 01a–01b.

Read first: AGENTS.md, README.md and Package/README.md; the approved specification
at docs/superpowers/specs/2026-10-07-package-predicate-foundations-design.md;
the plan's global constraints, Review Focus, evidence conventions, all of Task 6
and latest execution records; the active roadmap's separate Task 4 and Task 5
records. Read docs/research/2026-10-07-pkg01-predicate-foundations.md, the retained
fresh probe docs/research/probes/2026-10-07-pkg01-fresh.lean and
docs/article/sections/predicates.tex. Inspect actual PredicateSupport,
PredicateLogic, support/freshness and atom-swap sources and pinned Mathlib's
cofinite, eventual-decision, finite-index and reindexing APIs before implementation.
Task 6's ordinary module must not import SupportedPred.

Evidence directory: /tmp/nominal-package-pkg01-execution.WReW3a/
Verify it still exists. Read progress.md, task-4-delivery-record.md,
task-5-delivery-record.md, phase-01b-final-snapshot.json,
phase-01b-final-validation.json, phase-01b-preservation.log and the five consumers
01Logic.lean, 02Carrier.lean, 03Quantifiers.lean, 04Descent.lean,
05SupportedDescent.lean. Preserve earlier logs and take a new snapshot. If temporary
evidence is unavailable, record a replacement directory and recreate checks from
source without repeating completed implementation.

Starting-state reconciliation for the previous run: Task4-handoff.txt was a START
prompt, not evidence of delivery. Task 4 was absent at that run's entry and was
implemented and verified before Task 5. Both now have separate delivery records.
Task 4 exports general SMul invariance reflection; DivisionMonoid full-function
precomposition and arbitrary-set support reflection; ordinary predicate pullback
with exact sufficient/elementwise least support; Mathlib-backed action-free
descent, obstruction, and explicit canonical quotient support/renaming.
Task 5 exports SupportedPredicateDescent, six ordinary Compatible connectors,
supported pullback, explicit SubMulAction-based compatibleAction/compatibleNominal,
supportedEquiv and descendSupported with representative/inverse/action laws,
exact support, individual-context freshness and Boolean preservation. Both quotient
and compatible-subtype actions are explicitly selected. No source or quotient
Nominal premise is needed. There is one existing Boolean structure. Generic context
freshness accepts individual support even in a provably non-nominal carrier.

Implement Task 6's exact public names/signatures: ordinary Freshly and scoped typed/
untyped И notation; raw cofinite/filter laws, universe-independent reindexing,
one-way and finite-index universal interchange, weak eventual-decision Boolean
laws, constancy outside supplied bounds, all Some/Any and additional-avoidance
forms, finite-or-cofinite atom classification and its negative criterion,
FinitelySupportedPred decision/logical specializations, joint fresh projection,
and all three uniform-support interchange laws. Preserve arbitrary ordinary
predicates, Sort-valued external indices, empty indices, finite atoms and minimal
hypotheses. Infinite atoms are needed only where the plan says so; no public
DecidableEq is needed for Some/Any. Do not generalize atom Some/Any to arbitrary
nominal carriers, assert unrestricted existential interchange, or implement Task 7.
No admissions, custom axioms or disabled checking.

Create 06Fresh.lean externally with import Package and autoImplicit false.
Record missing-name failures before implementation, then prove all positive and
negative Task 6 cases. Test notation scope/hygiene, finite Bool with Freshly False,
extra avoidance and enlarged bounds, supported antecedent with arbitrary consequent,
all uniform-support variants, independent universes, exact signatures and axioms.
Compile affected modules while iterating, then run lake build Package
+Package.Tests.AxiomAudit, all six external consumers, direct
lake env lean Package/Tests/AxiomAudit.lean, python3 Package/Scripts/check-imports.py,
and git diff --check. Reconcile current interface/status docs and the article;
compile LaTeX externally. No operational metadata in the manuscript or persistent
Package Examples layer. Record actual commands/results/diagnostics/cache conditions,
confirm branch/HEAD/index/pins/unrelated work and previous evidence preservation,
update Task 6 separately, keep phase 01c and PKG-01 open, and provide Task 7's
copyable fresh-context prompt. Stop before Task 7.
```

### 2026-10-08 — Task 6 delivered: ordinary cofinite truth and supplied-bound Some/Any

**Complete, uncommitted. Phase 01c continues with Task 7 in this run.**
The author authorized Tasks 6–7 together; Task 8 is the stopping boundary.
Created/exported `Package/Foundations/FreshQuantifier.lean`, importing only
PredicateLogic and Mathlib cofinite/finite filter theory. No SupportedPred dependency.

Delivered `Freshly` and opt-in typed/untyped `И`; definition/finite-exception/Finset
characterizations; pointwise/eventual congruence, monotonicity, conjunction, modus
ponens, constants and witnesses; independent-universe equivalence reindexing;
Sort-indexed one-way laws and finite universal interchange. Decision-based negation,
disjunction (either operand), implication and both distinct Iff interfaces retain
the plan's hypotheses. Some/Any uses supplied bounds, off-bound swap constancy,
evaluation and arbitrary extra finite avoidance, with no public DecidableEq.
Finite/cofinite classification, the infinite/coinfinite obstruction and supported
Boolean specializations need infinitude only for self-dual negation. Joint fresh
projection requires only the action on X. All three uniform-support interchange
laws retain their distinct infinitude/nonempty-index premises.

Evidence: `/tmp/nominal-package-pkg01-execution.WReW3a/`.
`06Fresh-red.log` records missing interfaces before production edits (the original
run reached Lean's 100-error limit). `06Fresh.lean` now checks the full interface,
finite Bool/Empty, Sort indices, no-Nominal projection, a supported antecedent
with arbitrary consequent, consuming enlarged/avoiding bounds, and scoped nested/
shadowed notation. A parser-based guarded unscoped check rejects the actual binder
syntax. `06Scope-red.log`/`06Scope-green.log` retain its focused investigation.

`task-6-final-validation.json` records all eleven commands at exit 0: Package plus
audit build, all six external consumers, direct axiom audit, import coverage,
diff check and external latexmk. Affected module/root freshly built with cached
dependencies (`task-6-build-2.log`, 1015 jobs); full build freshly compiled audit
(1016 jobs). Direct audit: 976 declarations / 20 defining modules, only the
standard propext/Classical.choice/Quot.sound axioms. Coverage: 21 production
sources plus audit. Consumers/direct audit freshly elaborated; no clean dependency
bootstrap claimed. The final LaTeX engine log has no warnings or box diagnostics;
initial cross-reference warnings in the multipass driver log resolved normally.

Resolved diagnostics: the reserved name exists is escaped in its declaration;
not_false no longer resolves recursively; reindexing exposes the Freshly definition
to simp; a deprecated Set lemma was replaced. The deliberate shadowing test now
uses both binders. Parser errors occur before #guard_msgs elaboration, so the
unscoped syntax is parsed within run_elab and its failure is tightly guarded.
No mathematical contract, public hypothesis or name changed. No rulings or
deferred findings. The article now states classification, precise Boolean premises,
finite/empty behavior, reindexing and all uniform-support alternatives.

### 2026-10-08 — Task 7 delivered: contexts and bundled fresh projection; phase 01c complete

**Tasks 6 and 7 and their combined phase 01c acceptance criteria pass.** All
PKG-01 changes remain uncommitted. Tasks 1–7 and phases 01a–01c are delivered;
PKG-01 remains IN PROGRESS pending Task 8: final integration, complete
specification coverage and the independent whole-change review. Task 8 was
not started and none of its checklist items was marked complete.

Extended FreshQuantifier with the eight ordinary context forms:
`freshly_section_iff_exists`, `_forall`, both `_avoiding` variants, and the
four `freshly_invariant_section_iff_*` variants. The explicit relation and
individual parameter bounds combine as S ∪ T. Displayed unions retain
DecidableEq; invariant forms use hx.Fresh a and need neither DecidableEq nor
Nominal X. All context Some/Any forms require Infinite A. They reuse F05
sections, Task 6 avoidance and the existing elementwise freshness interface.
`FinitelySupportedPred.freshly_iff_of_fresh` evaluates an ordinary predicate
using its individually certified predicateObject, without bundling it.

Created/exported SupportedPredicateFresh with `SupportedPred.fresh`,
`fresh_apply`, `coe_fresh`, `fresh_smul`, `supports_fresh`,
`support_fresh_subset` and `freshly_iff_of_fresh`. The operation stores only
its ordinary Prop-valued body and a support proof. Application/coercion simplify,
renaming commutes, and the same sufficient bound is retained without infinitude
or nominality of the parameter carrier. Least-support/freshness conveniences
add Infinite A. No new Fresh relation, support construction, global action,
filter hierarchy, or persistent Package Examples layer was introduced.

Evidence remains `/tmp/nominal-package-pkg01-execution.WReW3a/`.
`07Fixtures-red.log` is a successful fixture run (exit 0); the filename reflects
its use in the RED-stage batch. It separately proves the nonnominal full-function
carrier and supported identity using delivered foundations. The subsequent
`07FreshPredicates-red.log` fails on missing context/bundled interfaces before
production edits (maxErrors=1000 exposes all diagnostics). The green consumer
obtains a relation fact at a fresh atom using only an individual certificate,
and combines that fact with extra finite avoidance in the proved nonnominal
identity carrier. It checks arbitrary-action fresh projection, finite Bool
projection of bottom to top, higher-order coercions and generic signatures.

`08Boundaries.lean` proves every requested obstruction through the public root:
the infinite/coinfinite Bool-flag atom predicate; unsupported external union of
supported singletons; failed fresh existential/universal interchange despite
jointly invariant equality/disequality; finite nonempty Bool-index failure;
finite-atom/empty-index failure; failures of stronger Boolean laws without
decisions and of Iff with only one supported operand; an empty-supported,
witnessed but noncofinite predicate on Discrete Nat Bool × Nat; a finitely
supported global fresh-selector obstruction with no Infinite premise; and
fixed-atom support without invariance. Ordinary classical fresh choice remains
legal and is separately proved unsupported. All supplied/enlarged/avoiding
positive consumers retain actual predicate facts in their conclusions.

`phase-01c-public-names.json` inventories 58 public declarations (42 from Task 6,
16 from Task 7). `Phase01cSignatures.lean` checks all of them; the three new
consumers assign generic contracts and print representative axioms, including
the selector obstruction and joint fresh projection. No public statement or
hypothesis deviated from the approved plan. No mathematical rulings or deferred
findings were introduced. This is the phase acceptance check, not Task 8's
independent review of the whole PKG-01 change.

Actual final commands/results are in `phase-01c-final-validation.json`, all
fourteen commands exit 0:

- `lake build Package +Package.Tests.AxiomAudit` — 1017 jobs. The final run
  freshly compiled the audit with cached project/dependency artifacts.
  Iterative affected-module/root builds freshly compiled the new code using
  cached dependencies (`task-7-build-2.log`, 1016 jobs; FreshQuantifier context
  additions built in `task-7-build-1.log`). No clean dependency bootstrap claimed.
- `lake env lean` on each of `01Logic.lean`, `02Carrier.lean`,
  `03Quantifiers.lean`, `04Descent.lean`, `05SupportedDescent.lean`,
  `06Fresh.lean`, `07FreshPredicates.lean`, `08Boundaries.lean` and
  `Phase01cSignatures.lean` in that evidence directory — fresh elaborations,
  no errors/warnings/admission dependencies. The five earlier sources and logs
  remain byte-identical; their new run logs have the phase-01c-final prefix.
- `lake env lean Package/Tests/AxiomAudit.lean` — fresh direct audit of 995
  declarations in 21 defining modules; only propext, Classical.choice and
  Quot.sound. The representative prints and full traversal policy are unchanged;
  Task 8 still owns extending the representative production prints.
- `python3 Package/Scripts/check-imports.py` — all 22 production sources
  (including the public root) and the separate audit reached. The ordinary
  FreshQuantifier Package import closure separately contains no SupportedPred module.
- `git diff --check` — clean; final preservation additionally checks the index,
  whitespace in new untracked files and changed Markdown link targets.
- From docs/article, `latexmk -pdf -interaction=nonstopmode -halt-on-error
  -outdir=/tmp/nominal-package-pkg01-execution.WReW3a/phase-01c-final-article-build main.tex`
  — fresh external output, 42-page PDF. Final engine log has no warnings,
  unresolved references or overfull/underfull boxes. The 41-page Task 6 checkpoint
  also had a clean final engine log. Initial multipass reference warnings resolved.

Resolved Task 7 diagnostics remain in their original logs: the bundled action
proof needed an explicit reindexed predicate and parenthesized inverse;
Bool-flag consumers needed explicit atom-domain annotations (the atom argument
of FinitelySupportedPred deliberately does not select the predicate domain);
the fixed-atom contradiction needed Nat.one_ne_zero. Final proofs are complete
and have only standard axioms. No diagnostic is suppressed.

The article now states contextual Some/Any, individual predicate-object
freshness, bundled projection and its bound, all distinct Boolean hypotheses,
three uniform-support interchanges, finite/empty behavior, and the proved
carrier/selector boundaries. Only its cofinite subsection changed in this phase;
no operational metadata entered the manuscript. Current README, specification,
plan, research summaries and active roadmap describe the actual delivery.

Preservation is certified by `phase-01c-check-preservation.py`,
`phase-01c-preservation.log`, `phase-01c-initial-snapshot.json`,
`phase-01c-final-snapshot.json`, `phase-01c-baseline/` and `phase-01c-only.diff`.
147 of 156 starting repository files are byte-identical; nine intentional public
export/interface/article/status documents changed and two foundation modules
are new. Every Task 1–5 production file and all research probes are unchanged.
All 693 earlier evidence files are preserved, with the shared ledger's exact
original prefix; the Task 6 code checkpoint is unchanged apart from Task 7's
appended adapters. Reference library, historical roadmap, dependencies, staged
index, branch and HEAD are unchanged. Branch: fasapa/nominal-package; HEAD:
3c9d8dc527f7705b24c0308a2527e659ae933874; index SHA-256:
462fdfad827bcfebf9cf0239d1c5d0917226206646acc3270bd8892ffcd3a8ba.
No commits, worktrees, branch changes, pushes, merges, publication, dependency
upgrades or CI edits. No reference rebuild or checker self-test was needed;
the unchanged reference/checker sources and their prior evidence are preserved.

`phase-01c-acceptance.md` maps the combined criteria to actual consumers.
`Task8-handoff.txt` is the copyable fresh-context prompt, also retained below in
the plan. Reuse Tasks 1–7 and complete Task 8 before claiming PKG-01 complete.

### Copyable fresh-context prompt for Task 8

```text
$superpowers:executing-plans

Complete ONLY Task 8, “Public integration, specification coverage and final review,”
from docs/superpowers/plans/2026-10-08-package-predicate-foundations.md.

The specification and implementation plan are approved. Execute natively yourself;
do not restart brainstorming or request the same approvals. Tasks 1–7 and phases
01a–01c are complete, uncommitted. Reuse them; do not repeat implementation.
PKG-01 remains open until Task 8's final integration, complete accepted-specification
coverage and independent whole-change review pass. Stop after Task 8, before any
later PKG task. Do not commit, push, merge, publish, switch branches, create a
worktree, upgrade dependencies or add CI. Preserve the evidence rather than
running a branch-finishing/deletion workflow.

Work in /home/fab/Documents/nominal/nominal.
Expected branch: fasapa/nominal-package.
Last verified HEAD: 3c9d8dc527f7705b24c0308a2527e659ae933874.
Inspect actual branch, status, history and source before editing. Preserve all
tracked, staged and untracked work, including F05, Tasks 1–7, research probes and
article changes. Use Package/ and docs/nominal-package-roadmap.md; preserve the
reference library and historical docs/roadmap.md. Reuse the F05 hybrid.

Read AGENTS.md, README.md and Package/README.md; the approved specification at
docs/superpowers/specs/2026-10-07-package-predicate-foundations-design.md; the
plan's global constraints, Review Focus, complete Task 8 and coverage mapping;
and the active roadmap's separate Task 6 and Task 7 delivery records. Read actual
production modules and docs/article/sections/predicates.tex. Do not mistake an
older handoff prompt for a delivery or current stopping instruction.

Evidence directory: /tmp/nominal-package-pkg01-execution.WReW3a/
Verify it exists and read progress.md, task-6-delivery-record.md,
task-7-delivery-record.md, phase-01c-acceptance.md,
phase-01c-final-validation.json, phase-01c-final-snapshot.json,
phase-01c-preservation.log, phase-01c-only.diff and phase-01c-public-names.json.
Read all eight consumers: 01Logic.lean, 02Carrier.lean, 03Quantifiers.lean,
04Descent.lean, 05SupportedDescent.lean, 06Fresh.lean, 07FreshPredicates.lean,
08Boundaries.lean; Phase01bSignatures.lean and Phase01cSignatures.lean supplement
them. Preserve their sources/logs and take a new snapshot. If temporary evidence
is missing, record a replacement directory and recreate necessary checks from
source without repeating completed implementation.

Phase 01c delivery: FreshQuantifier imports PredicateLogic and pinned Mathlib's
cofinite/finite filter APIs, without SupportedPred even transitively. It provides
ordinary Freshly/scoped typed-untyped И, filter/decision laws, supplied-bound
Some/Any/avoidance, finite-cofinite classification, uniform-support interchanges,
joint fresh support, eight ordinary context adapters and ordinary predicate-object
freshness. SupportedPredicateFresh is the thin bundled fresh projection with
computation/coercion, action, same-bound, least-support and freshness laws.
58 public declarations were signature-checked. Keep the exact distinctions:
Some/Any Infinite A with no public DecidableEq; classification no infinitude;
joint projection no infinitude or Nominal X; Boolean decision premises differ;
uniform universal no infinitude, existential Infinite A or Nonempty I; Sort-valued
external indices; context freshness needs only individual support. Keep Fresh
as support disjointness. All specified negative boundaries are proved externally,
including finite nonempty-index failure, Iff with one supported operand, arbitrary
nominal-carrier Some/Any failure and the global selector obstruction without an
Infinite premise. Unsupported predicates and ordinary classical choice remain legal.

Task 8 work:
- Create 09PublicSignatures.lean through import Package with autoImplicit false,
  assigning headline declarations to the exact plan contracts, independent
  universes, explicit selected actions, two atom sorts, no unnecessary
  Nominal/Infinite/Nonempty premises and fresh notation outside its namespace.
- Extend Package/Tests/AxiomAudit.lean representative prints for all PKG-01
  areas; preserve full module-origin traversal, standard-axiom whitelist and
  rejection tests. No custom axioms, admissions or disabled checking.
- Reconcile Package/README.md with ordinary, supported, quotient and Some/Any
  examples and compile extracted Lean examples. Check the full specification
  acceptance mapping, not just the latest phase.
- Reconcile the complete manuscript and current status/interface documents;
  keep operational metadata out of the manuscript. Compile LaTeX externally.
- Run lake build Package +Package.Tests.AxiomAudit, all nine external consumers
  and README extracts, direct lake env lean Package/Tests/AxiomAudit.lean,
  python3 Package/Scripts/check-imports.py and git diff --check. Check links,
  final LaTeX diagnostics and preservation. No unchanged reference rebuild or
  dependency bootstrap is required; distinguish caches from fresh elaboration.
- Obtain ONE fresh independent whole-change review as required by executing-plans,
  on the most capable available reviewer model with explicit reasoning effort.
  This is the final reviewer, not a per-task implementer/reviewer chain. Pass the
  spec, plan, Review Focus verbatim, all actual sources/diffs, consumer/evidence
  paths and ledger rulings. Review the complete UNCOMMITTED PKG-01 change from
  HEAD, including untracked modules; a HEAD..HEAD commit range alone is empty
  and cannot represent this delivery. Preserve unrelated working-tree work.
  Resolve material findings and run affected regression/integrated checks.
- Record actual commands, results, diagnostics, cache conditions, preservation,
  review findings/rulings and remaining limitations. Mark PKG-01 complete only
  when all Task 8 and whole-specification criteria pass. Leave all work uncommitted.

Phase 01c baseline verification: fourteen commands passed; all eight consumers
and signature inventory freshly elaborated; direct audit 995 declarations in
21 defining modules, only propext/Classical.choice/Quot.sound; import coverage
22 production sources plus one audit; final 42-page external article has no
diagnostics. Affected modules/root were freshly built using cached dependencies;
final Package build was cached except for the audit. No mathematical deviations
or deferred findings were introduced in Tasks 6–7. No independent review has yet
been performed for the whole PKG-01 change; it remains mandatory here.
```

### 2026-10-08 — Task 8 complete: public integration and independent final review

**Task 8 and PKG-01 are complete, uncommitted. All three phases, whole-specification
acceptance and the independent whole-change review pass.**
Only Task 8 is authorized in this run. Tasks 1–7 are reused without production
proof changes. Later PKG tasks remain outside this delivery.

Evidence remains `/tmp/nominal-package-pkg01-execution.WReW3a/`.
All earlier evidence was present. Every phase-01c final repository hash matched
the current checkout at entry. `task-8-initial-snapshot.json`,
`task-8-initial.diff` and `task-8-baseline/` preserve the 158 repository files,
branch, HEAD, index and 926 earlier evidence files. The retained `progress.md`
was appended; its original prefix is unchanged.

Delivered integration:

- `09PublicSignatures.lean` contains 65 public-import consuming examples with
  autoImplicit false. Exact contracts check independent universes, simultaneous
  atom sorts on one carrier, explicit selected/canonical quotient actions,
  scalar-only and DivisionMonoid parents, empty/proved nonnominal carriers,
  absent unnecessary Nominal/Infinite/Nonempty/DecidableEq premises, named and
  literal evidence, certificate independence, computability and higher-order use.
  Overloaded Boolean operations are explicitly typed as SupportedPred. Scoped
  typed/untyped И is consumed outside the defining namespace. It passed first
  elaboration against the existing implementation; no export or proof repair
  was needed.
- `Package/Tests/AxiomAudit.lean` adds 43 representative prints across every
  predicate area. Module-origin traversal, standard-axiom whitelist, zero-count
  rejection and simulated disallowed-name rejection tests remain byte-identical.
  The negative-test strings are not active axioms. The inspection-only heartbeat
  budget was preserved; no mathematical checking or diagnostic option was relaxed.
- Package README now has complete ordinary-certificate, supported-value,
  action-free/supported descent and supplied-bound Some/Any examples. All eight
  Lean blocks, including the earlier function examples and a formerly schematic
  quotient-action fragment, were extracted to `READMEExamples.lean` and compiled
  together through Package with autoImplicit false. Names and hypothesis limits
  agree with the public interfaces.
- `task-8-acceptance.md` maps 46 whole-specification obligations to actual source
  and consuming evidence across all phases. Both earlier signature inventories
  are retained and rerun. All specified negative boundaries remain proved;
  unsupported ordinary predicates, quotient induction motives and classical
  choice remain legal.
- The manuscript title/abstract, section guide and correspondence paragraphs
  now include functions, supported predicate logic, quotient descent and
  Some/Any. Its central predicate mathematics remains unchanged after checking
  hypotheses and proofs against source. `task-8-literature-check.md` records
  the pinned primary comparisons; no new external formalization build is claimed.
  Operational metadata remains outside the manuscript.

Commands actually run, all final exits 0, with exact argument arrays, working
directories, elapsed times and full logs in `task-8-integrated-validation.json`
(18 commands) and `task-8-initial-validation.json`:

- `lake build Package +Package.Tests.AxiomAudit` — 1017 jobs. The first Task 8
  run freshly compiled the changed audit using cached production/dependency
  artifacts. The integrated run was cached. No fresh production rebuild or
  clean dependency bootstrap is claimed.
- `lake env lean` on each of `01Logic.lean`, `02Carrier.lean`,
  `03Quantifiers.lean`, `04Descent.lean`, `05SupportedDescent.lean`,
  `06Fresh.lean`, `07FreshPredicates.lean`, `08Boundaries.lean`,
  `09PublicSignatures.lean`, `Phase01bSignatures.lean`,
  `Phase01cSignatures.lean` and `READMEExamples.lean` in the evidence directory
  — twelve fresh elaborations against cached imports. The original eight
  consumer sources and earlier logs are unchanged.
- `lake env lean Package/Tests/AxiomAudit.lean` — fresh traversal of 995
  production declarations in 21 defining modules; only `propext`,
  `Classical.choice`, `Quot.sound`.
- `python3 Package/Scripts/check-imports.py` — all 22 production sources,
  including the root, and the separate audit reached. Ordinary FreshQuantifier
  and PredicateDescent import closures separately checked to exclude the
  bundled predicate modules. No checker change or self-test was necessary.
- `git diff --check` and `git diff --cached --check` — clean. Additional
  checks include whitespace in untracked delivery files and local Markdown
  target/fragment validation.
- From `docs/article`, `latexmk -pdf -interaction=nonstopmode -halt-on-error
  -outdir=/tmp/nominal-package-pkg01-execution.WReW3a/task-8-article main.tex`
  — fresh external output directory, 42-page PDF. Final engine log has no
  warnings, unresolved references or overfull/underfull boxes. Transient
  first-pass cross-reference messages in the driver log resolved normally.

No Lean consumer/audit errors or warnings remain. The sole failed Task 8 check
was the new external preservation helper initially expecting the later snapshot
schema in the earliest snapshot (`files` versus `hashes`). The original failure
log is retained; inspecting the original keys identified the cause, and the
schema adapter passed the complete preservation check. No source theorem or
acceptance test was changed to conceal a failure.

The pre-review preservation check passes: 145 of 158 repository files are
byte-identical, with thirteen intentional integration/documentation/audit edits;
no new repository files in Task 8. All 77 protected reference/probe/pin files
match the earliest and latest snapshots, and all 926 earlier evidence files are
preserved (ledger prefix checked separately). 321 local targets and 20 Markdown
fragments pass. Earlier plan task contracts and all historical plan/roadmap
execution records are unchanged. No production theorem file changed in Task 8.

Independent whole-change review was performed once to `gpt-6-astra` with
explicit `ultra` reasoning and a fresh context (`fork_turns: none`), read-only.
`task-8-review-package.md` includes the approved authority, Review Focus verbatim,
actual source/documentation, complete 33-file uncommitted diff/inventory,
all consumers/logs, preservation scope and ledger rulings. This includes all
seven untracked production modules; HEAD..HEAD is not used as the change range.
The technical review gate passes with no Critical or Important findings and no
correctness, missing acceptance, or hypothesis defect. The reviewer independently
reran all nine consumers, README extracts, direct audit and import checker.
Its one Minor finding, M1, was an obsolete active roadmap policy paragraph saying
Tasks 6–8 remained and authorization stopped before Task 6. Source inspection
confirmed it; the required final current-status reconciliation now identifies
Tasks 1–8 as complete and the stopping point after Task 8. This is a documentation
correction within the existing task, with no production fix or new test needed.
Historical work-log entries remain unchanged. No minor finding is deferred.
The full report/disposition is `task-8-independent-review.md`; all reviewer
scope exclusions are explicitly ruled on in `task-8-rulings.md`.

Workflow ruling: explicit current instructions override generic worktree,
commit, evidence-deletion and branch-finishing helpers. The authorized checkout
and external evidence are retained. The cost is the requested uncommitted,
external evidence state; no mathematical scope or contract was changed.

Branch remains `fasapa/nominal-package`; HEAD remains
`3c9d8dc527f7705b24c0308a2527e659ae933874`; index SHA-256 remains
`462fdfad827bcfebf9cf0239d1c5d0917226206646acc3270bd8892ffcd3a8ba`.
Reference code, historical roadmap, research probes, pinned dependencies and
CI remain unchanged. No commit, push, merge, publication, worktree or branch
operation was performed. Larger-client elaboration performance and future
binder/generator/case-study work remain outside this acceptance claim.

Final status reconciliation covers the plan's seven Task 8 checklist steps, the
active roadmap dashboard/policy/task contract, approved specification, current
research index/investigation/readiness/brief and Package README. It preserves
all earlier execution records and handoffs. Completion concerns only PKG-01;
PKG-F06 and later PKG tasks retain their previous status.

**Final closeout:** the same reviewer confirmed M1 resolved and the final completion
status consistent, with no remaining discrepancy. Only status/evidence documentation
changed after technical review; production, audit, manuscript and compiled consumer
sources are unchanged. `python3 /tmp/nominal-package-pkg01-execution.WReW3a/task-8-check-preservation.py final`
passes after reconciliation: 144 of 158 starting repository files byte-identical,
fourteen intentional integration/docs/audit changes, no new repository files in
Task 8, all 77 protected files and 926 earlier evidence files preserved, 322 local
links and 20 fragments valid. The final snapshot and Task-8-only diff are
`task-8-final-snapshot.json` and `task-8-final-only.diff`; full final inventory/diff
also include every untracked PKG-01 source. Branch, HEAD and index remain unchanged.
Task 8 and PKG-01 are complete, uncommitted. No later PKG task was started.
