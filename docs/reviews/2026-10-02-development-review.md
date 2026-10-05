# Nominal development review — 2026-10-02

## Assessment and scope

The integrated Lean core is a substantial, working classical nominal library. A fresh project-artifact rebuild passed, and an automated dependency inspection of 1,165 project-namespace declarations found no axioms beyond `propext`, `Classical.choice`, and `Quot.sound`. No false mathematical theorem was found in the integrated core. This is evidence about the inspected revision and tests, not a proof that every possible client interaction is correct.

The lambda development is also substantial: alpha-quotiented terms, exact support/free-variable correspondence, strong term induction, supported-handler iteration, and capture-avoiding substitution with composition are proved. Its saved migration patch reproduces a successful separate build. It is **not integrated into `fasapa/next`**, and it does not yet contain reduction or Church–Rosser.

The most immediate integrated defects are in freshness tactics, including a newly reproduced loss of shadowed local variables. NFun application, composition, currying, extensionality, and several ordinary higher-order uses already work. Its construction and adaptation interfaces need improvement; the lambda branch's syntax-only `nfun` macro fails on ordinary globals, local bindings, and nested functions.

The algebraic branch is an unbuilt, admitted sketch with several mathematically wrong statements. It must not be treated as an implementation waiting only for proofs. Some findings go beyond the existing roadmap: arbitrary quotient actions in a support theorem, confusion between a canonical comparison and any set equivalence, and an incorrectly typed separated-product claim.

Historical distinctions matter. Current Rocq main has no active admissions found in its supported source, but the article-linked `lsfa2025` tag has two active admitted permutation-instance proofs. An additional extensional-function experiment with an unsound axiom is excluded from that tag's build and deleted from main. Neither historical issue contaminates the checked Lean core.

This review preserved the existing working tree. No implementation fixes, branch switches, merges, or library redesigns were performed. Experiments were confined to `/tmp`. The requested review and a reconciliation of `docs/roadmap.md` are the only intended repository edits. Murillo's syntax/unification branch was excluded; the two small `Nominal/Syntax` files already exported on `fasapa/next` were included.

Decisions supplied by the author during this review:

- Immediate priority is cleanup/review of what needs attention to finish Church–Rosser, then completing that proof and learning from it. General metaprogramming and algebraic infrastructure come later, informed by the case study.
- First release needs reliable NFun coercions/combinators, rewriting, and focused support automation. A general binder-aware lambda elaborator can follow.
- Generic initial-algebra theory is primarily a means to usable datatype generation.
- There is no deadline; prioritize correctness.
- Preserve one atom sort, single/nested binders, classical/noncomputable semantics, and the existing no-CI boundary.

## Sources, revisions, and actual coverage

| Source | Inspected revision/location | Review/build status |
| --- | --- | --- |
| Current Lean branch | `fasapa/next`, `2c45db82373bd21a24b964a38c3d777d0b44efde` | All current Lean source, exports, Lake configuration, README, roadmap, migration diff and patch inspected; fresh local project rebuild passed |
| Shared Lean ancestor | `1646471e9c2f36303fb087a933ff85ee73382d74` | History/diff inspected; previous 4.28 build claim not rerun |
| Lambda branch | `9f04655838b77283a056705cf5554dc48806e7db` | All branch additions and shared-core changes inspected; separately migrated 4.34.1 build passed; original 4.28 build not rerun |
| Algebraic branch | `983adeb9b80f75fb7c77c05acfd2fcef16db1d46` | Both added modules fully inspected; direct compilation fails at obsolete imports; normalized scratch experiments described below |
| [Rocq main](https://github.com/fasapa/nominal/tree/78f41a6c7ca1b55814b7b7c7d734ad4decaac523) | `78f41a6c7ca1b55814b7b7c7d734ad4decaac523`, `/tmp/nominal-rocq-audit` | All 19 `.v` files/source assumptions and project membership inspected; build unavailable |
| Article-linked Rocq tag | `lsfa2025`, `fc7b95a47539fa2dc39f41f293c7d943a0d8b22d` | Fetched into scratch; compared project list, lambda/substitution, permutation instances and excluded experiment with main |
| [Articles](https://github.com/fasapa/nominal-sets-article/tree/8c8c05d25f0918280fa2446a9ee78921bf9a8fa4) | `8c8c05d25f0918280fa2446a9ee78921bf9a8fa4`, `/home/fab/Documents/nominal/articles` | Local TeX, inclusion graphs, substantive short/extended drafts and published article inspected; PDFs not rebuilt |
| Pitts | [ref/nominalsets.pdf](../../ref/nominalsets.pdf) | Relevant full-book material inspected: support, abstraction/FCB, categorical constructions, algebraic signatures, structural induction/recursion; not a page-by-page book audit |
| Isabelle Nominal | Official `CR`, `CR_Takahashi`, Nominal infrastructure/example sources | Source comparison for term/rule induction and confluence; Isabelle not run |

Remote read-only revision checks confirmed all three requested Lean branch tips, Rocq main/tag, and article HEAD. The article repository required its configured SSH access; an unauthenticated HTTPS check failed before SSH succeeded. No remote refs in the working Lean repository were modified.

At review start, `git status --short` was:

```text
 M README.md
?? .codex/
?? docs/
```

There were **no uncommitted Lean migration changes**. Commit `2c45db8` already contains the version upgrade, action priorities, computability adjustments, quotient elaboration changes, and explicit-freshness fix. The roadmap's earlier “working tree, not committed” wording was stale. The uncommitted README edit only changes the roadmap link's wording. Existing documentation and the saved patch were untracked; their existence does not imply a recorded Git artifact.

The branch relationship is:

```text
1646471
├── 2c45db8                    fasapa/next: core migration
├── 4bdeeaa ── 9f04655         lambda: two commits
└── 983adeb                   algebraic: one commit
```

### Verification results

| Check | Result and limitation |
| --- | --- |
| `lake build` in current working tree | Passed, 1,003 jobs; initially replayed cached project artifacts |
| Fresh source/config copy to `/tmp/nominal-core-review.ss059u_u`, then `lake build` | Passed, 1,003 jobs, rebuilt project modules with a fresh project build directory; reused pinned dependency artifacts |
| Export lambda tip, `git apply --check` and apply saved patch | Passed; source patch needs current 4.34.1 toolchain/manifest and matching dependency revision separately |
| `lake build Nominal Instances` in `/tmp/nominal-lambda-review.FQ5W8o` | Passed, 1,014 jobs, fresh project build directory, reused dependencies |
| Source import-closure inventory | All 24 current project modules are reachable from `Nominal`; all 32 migrated project modules are reachable from the pair `Nominal`/`Instances`. Scratch probe modules are excluded from these counts |
| Automated `Lean.collectAxioms` sweep | Current: 1,165 declarations; migrated core+lambda: 1,581. No dependencies outside the standard three listed above in the selected project/private namespaces |
| Core positive examples | Passed: four-argument freshness, duplicates/type expansion without shadowing, NFun coercions/ext/curry, action coherence, abstraction/concretion, and least-support counterexample |
| Lambda positive examples | Passed: nested NFun extensionality, rewriting/currying, substitution under a shadowing binder, and a capture-avoidance example requiring binder renaming |
| Negative tactic/macro examples | Failed with the predicted errors; these failures are evidence of the findings below, not a failed supported-library build |
| Algebraic original files with current environment | Fail immediately: unknown module prefix `NominalSets` |
| Algebraic scratch import/namespace normalization | Structural file elaborates **with admissions**; algebraic file still has interpretation/typeclass/universe errors. Neither result verifies the branch's theory |
| Admission-free algebraic witnesses against current core | Passed: contradiction from fixed-substitution equivariance; empty support for an arbitrary carrier with discrete action |
| Rocq `make` | Failed before compilation: `coq_makefile: No such file or directory`. No installed Rocq/Coq executable was found; no `Print Assumptions` claim is made |
| `git diff --check` | Passed for tracked changes; final documentation checked separately because it was initially untracked |

The axiom sweep selects names beginning `Nominal.`, `_private.Nominal.`, and, for the lambda export, `LambdaCalculus.`/`_private.Instances.`. It is a broad project-declaration dependency check, not an audit of every imported Mathlib declaration or of Lean's implementation. Headline `#print axioms` checks separately included `supp_supports`, `someAny`, `supp_quotient_eq_sInter`, `NameAbs.supp_abs`, `NameAbs.liftFCB_abs`, `NameAbs.liftFreshParam_unique`, `NFun.curry_eval`, `Term.strong_ind`, `Term.RecRel.unique`, `Term.recNoContext_lam`, `Term.subst_subst`, and `Term.supp_eq_fv`.

There are no active `sorry`, custom axioms, `unsafe` declarations, or disabled kernel checks found in the inspected integrated Lean source or lambda additions. Linter suppression for unused tactic-test variables is not a logical assumption. Synthetic `sorry` expressions printed in failed scratch elaboration diagnostics are not declarations admitted into the library.

## What works and should be preserved

| Area | Assessment |
| --- | --- |
| Atoms/permutations | `Name` requires decidable equality and infinitude, not countability. Finite permutations are genuine finite bijections; swap factorization/support arguments are present. |
| Actions | Current conjugation priorities restore the intended action on finite permutations. `SMul`, `MulAction`, `PermType`, and `Nominal` projections agree definitionally in the tested cases. Keep `PFun` separate from ordinary functions: Mathlib's ordinary function action is pointwise, whereas nominal functions require conjugation. |
| Support | `supports` means pointwise fixing of a finite set implies fixing the element. Least support is proved to support and to be minimal. The core distinguishes `StrongSupports`; it does not contain the paper's false converse. |
| Freshness/quantification | Freshness is disjointness of least supports. Some/Any explicitly requires joint equivariance. Cofinite disjunction/negation/implication laws carry the needed finite-or-cofinite hypotheses. They do not assert unrestricted self-duality of the cofinite filter. |
| Quotients | Action descends through an equivariant setoid, and quotient support is the intersection of representative supports. This is proved, not assumed. |
| Abstraction | Alpha equality, fresh representatives, support deletion, binder renaming and abstraction extensionality have meaningful statements and proofs. Nested single abstractions fit the current mathematics. |
| Concretion | Defined exactly when the chosen atom is fresh for the abstraction; a different fresh binder returns the renamed body. The implementation is stronger and more accurate than its short docstring. |
| FCB | The partial formulation uniformly supplies total, fresh outputs for all bodies on a cofinite atom set. Lifting, support bounds, computation and uniqueness are proved, with parameterized lifting available. |
| NFun | Support evidence lives in proof fields. `const` and `comp` still compute; both tested evaluations return `7`. Application and basic higher-order use do not require a redesign. Currying already accepts finitely supported input, not only equivariant input. |
| Lambda | Raw terms and quotient terms correctly have different supports. The strong induction motive need not be equivariant. Relational iteration proves totality and uniqueness before using classical choice. Substitution composition has the appropriate distinctness/freshness hypotheses. |

Several apparent restrictions are mathematically necessary and should not be “simplified” away. `NFun.supp_const` and `const_injective` require a nonempty domain; the unconditional support theorem gives only inclusion. Equivariant maps can shrink support, so the all-atoms concretion/map equality requires injectivity, while the fresh-atoms version does not. `liftFresh_proj` assumes every atom is fresh for every body; it is not a general function extracting the body of an abstraction.

## Actionable findings

Severity is relative to the affected component: **P1** blocks the claimed mathematics or delivery of that component; **P2** is a substantive API/usability/build/documentation problem; **P3** is a lower-impact clarification or optional generalization. No P0 defect in the integrated logical theory was found. “Missing feature” and “research question” do not mean an existing theorem is false. References without a branch label are to `2c45db8`; lambda line numbers are in the migrated export unless explicitly stated.

Finding IDs in this report are a separate index from the roadmap's stable task IDs. The remedy/dependency fields below refer to **roadmap tasks**, even when the same short identifier also labels a review finding.

### V-01 — Integration and build coverage are narrower than a successful core build

**P2; build/integration gap.** References: `lakefile.toml:4`, current `Nominal.lean`; lambda `lakefile.toml` and `Instances.lean`; `docs/migrations/lambda-4.34.1.patch`.

**Evidence/impact:** Current default target is only `Nominal`, and no lambda library exists here. The lambda branch declares `Instances` but also defaults only to `Nominal`. Its migration patch applies cleanly to its own tip; applying it wholesale to current HEAD would duplicate shared changes and mishandle the NFun split. A core build cannot certify the case study, and neither default build certifies the unexported algebraic modules.

**Remedy/dependencies:** B-04/B-05: integrate branch-only results deliberately, preserving current compatibility/computability/freshness changes. Add a persistent local examples target and either include both supported libraries by default or prominently document the two-target command. No CI is needed.

**Verification:** fresh project-artifact builds of `Nominal Instances` after integration; enumerate the import closure; run persistent consumer examples and headline axiom checks. Record integration revision separately from the successful scratch migration.

### T-01 — `choose_fresh` loses shadowed locals

**P2; confirmed tactic defect.** References: `Nominal/Set/Freshness/Tactic.lean:195` (`expandFromArgs`) and `:213` (automatic elaboration path).

**Evidence/impact:** Both paths collect `FVarId`s and reconstruct terms from `userName`. With two locals displayed as `x✝ x`, `choose_fresh a from X` generates `aFresh1 aFresh2 : a # x`, omitting the older local. Automatic scanning has the same defect. A consuming example fails because `a # x` cannot discharge `a # x✝`. The kernel remains sound; the tactic's coverage promise is false.

**Remedy/dependencies:** C-01: preserve expression/free-variable identity throughout collection and proof construction. Do not reconstruct local expressions from display names. This repair also applies to explicit type expansion and must not be described only as an automatic-scan issue.

**Verification:** both forms with same-name/same-type and same-name/different-type locals, and goals requiring freshness for every selected local. A minimal reproduction is in the appendix.

### T-02 — Automatic freshness scans explicit instance declarations, not available instances

**P2; confirmed tactic defect.** Reference: `Freshness/Tactic.lean:145–160`, `findNominalDecls`.

**Evidence/impact:** An atom-only context fails despite the canonical atom instance. With `[Nominal α X] (x : X) (b : α)`, scanning succeeds but supplies only freshness for `x`. Products, abstractions and NFuns are similarly missed unless an instance of exactly their type is explicitly local. This contradicts the documented “all declarations whose type has a Nominal instance” behavior.

**Remedy/dependencies:** C-01 after B-02: establish the atom type, synthesize instances for eligible locals, isolate speculative unification, filter auxiliary declarations, and diagnose ambiguity. Preserve the working explicit `from` route.

**Verification:** atom-only, mixed, product, abstraction and NFun contexts, requiring all facts; ambiguous atom contexts should produce an actionable diagnostic. Do not use a `True` goal as coverage evidence.

### T-03 — `split_fresh` does not reliably produce all nested leaves

**P2; confirmed tactic defect.** Reference: `Freshness/Tactic.lean:44–45`, macro rules and nearby examples.

**Evidence/impact:** The unnamed form on `a # (x,y,z)` leaves `a # y ∧ a # z` unsplit. The named flat pattern works on a right-associated tuple but fails on `a # ((x,y),z)` because the conjunction tree has another association. Existing `True`-valued examples do not exercise the promised conclusions.

**Remedy/dependencies:** C-02, independent of lambda integration: recursively flatten freshness conjunctions on both sides, define accessible names, and validate requested name counts/nonsplittable inputs.

**Verification:** consumer proofs using every leaf for both associations, left/right products, collisions and naming errors. Preserve successful named right-associated behavior.

### T-04 — Single-item freshness names contradict the documentation

**P3; confirmed documentation/API mismatch.** References: `Freshness/Tactic.lean:92–93` versus `:126–128`.

**Evidence/impact:** `choose_fresh a from b with h` produces `h1`, not `h`; the default is `aFresh1`, not documented `ha`. The documented proof fails with an unknown identifier.

**Remedy/dependencies:** C-01/D-01: choose and document one stable naming convention; keep explicit compatibility if changing it.

**Verification:** compile documented single/multiple-input examples, consuming the exact advertised names.

### N-01 — Expose the missing function adapters before expanding automation

**P2; usability/missing API.** References: current `NFun.lean:138–141,309,554`; lambda `NFun/Basic.lean:205` onward and `:607–617` (`curry_eval`).

**Evidence/impact:** Application, `List.map f`, `(g ∘ f) x`, partial application of curried NFuns, `ext`, and rewriting all passed. However, there is no public NFun `uncurry`; its implementation and support proof appear inside `curry_eval`. `Function.uncurry f` does not automatically adapt an NFun-valued codomain. A function-level composition equality closes by `rfl` while `simp` alone makes no progress. The lambda branch already adds `NFun.equivariant`, `ofCaptures`, and `fromParam`; reuse these instead of creating duplicate adapters.

**Remedy/dependencies:** N-01 through N-04 after B-04: expose `uncurry`, stable coercion/application equations, beta/eta/action/support laws, and ergonomic fixed-parameter adapters. Preserve the distinction between ordinary functions, equivariant maps and finitely supported maps. Add notation only if concrete client proofs justify it.

**Verification:** a small benchmark suite covering nested nominal results, captured parameters, pair/curried handlers, composition and rewriting without structure-field manipulation; include necessary empty-domain edge cases.

### N-02 — `nfun` treats global function identifiers as captures

**P2; confirmed prototype defect.** Lambda reference: `Nominal/Set/NFun/Tactic.lean:136–160,247–249`, `collectFreeNames` and expansion.

**Evidence/impact:** `nfun fun a => Term.var a` and `nfun fun x => _root_.id x` demand a `Nominal` instance on an ordinary function type. The comment promises filtering through elaboration, but the macro passes collected syntax identifiers directly into capture support. Existing examples do not establish ordinary constructor usability.

**Remedy/dependencies:** M-01/M-02/N-04: distinguish resolved globals from actual local free variables and generate kernel-checked support obligations. A global is not automatically equivariant: its support must follow from a registered theorem or explicit certificate. A limited, honest interface plus focused automation suffices for the first release.

**Verification:** qualified/unqualified constructor and ordinary function examples; also a deliberately unsupported ordinary function that must be rejected or leave an explicit proof obligation.

### N-03 — `nfun` mishandles lexical scope and overpromises syntax

**P2 for scoping; P3 for documentation; confirmed defects.** Lambda reference: `NFun/Tactic.lean:143–157,180–194,215–249`.

**Evidence/impact:** `let y := c; y`, a tuple `match`, and nested `nfun` each leak bound identifiers into the capture list and fail with unknown identifiers. A multi-binder ordinary lambda cannot construct an expected curried NFun. Documented `(capturing S)` and `(bind a)` forms do not exist; actual syntax is `[capturing ident+]`, which cannot express an explicitly empty capture list.

**Remedy/dependencies:** M-01 defines the supported language and escape hatch; M-02 may later replace syntax traversal with expected-type/expression-aware elaboration. Correct current documentation and reject unsupported forms clearly. General elaboration is not a release prerequisite under the author's decision.

**Verification:** alpha-renaming of Lean locals must preserve behavior; cover shadowing, `let`, tuple patterns, nested lambdas, `match`, empty captures and informative negative diagnostics. Never bypass support proofs to make syntax elaborate.

### C-01 — Universe restrictions are real but do not block the agreed case study

**P3; confirmed generality limitation.** References: `EquivalenceClass.lean:48,75,105,163`; `NameAbstraction.lean:97,131`; same-universe parameters in `Concretion.lean`/`FCB.lean`.

**Evidence/impact:** With independent `α : Type u`, `X : Type v`, `NFun α X X` elaborates, while `NameAbs α X` and the generic quotient nominal instance fail. Small atoms with larger semantic carriers are unavailable. The current same-universe lambda calculus is unaffected.

**Remedy/dependencies:** C-07: document the restriction now. If a client needs generalization, start with quotient instances, then abstraction in `Type (max u v)`, then elimination APIs. Do not tie first-release completion to unsupported future universes or multiple atom sorts.

**Verification:** independent-universe quotient/abstraction/concretion examples and complete core/lambda builds after any generalization.

`PermType`'s atom parameter is an `outParam` (`PermType.lean:102`), favoring a default atom/action inferred from the carrier. This supports the agreed single-sort workflow but is not a general multi-sort action interface. Explicit instance choices for discrete carriers and documentation of that inference convention belong to roadmap C-07; tagged/multiple atoms need their own future specification.

### C-02 — Container and discrete-data support should follow client needs

**P2 when required by a client, otherwise P3; missing API.** References: `PermType.lean:146–197`; `Nominal.lean:121–202`.

**Evidence/impact:** Lists, arbitrary finite sets and a reusable discrete wrapper are absent. Atom finite sets are supported. Unit/Bool nominal structures are deliberately explicit definitions; Nat/Int have trivial-action definitions but no corresponding general nominal convenience definitions. With Nat used as atoms, silently using its atom action for numeric data would be inappropriate.

**Remedy/dependencies:** C-03/N-01: provide only containers needed by actual contexts/handlers, with a discrete wrapper or explicit instance choice for data. Avoid adding ambiguous competing global actions.

**Verification:** typeclass inference, action coherence, support equations and a real context/size-function client. A full collection library is not necessary for untyped confluence.

### C-03 — Several useful freshness/FCB formulations remain behind low-level obligations

**P2; API strengthening opportunity.** References: `FreshQuantifier.lean:191,227,244,401–514`; `FCB.lean:700–743`.

**Evidence/impact:** Some/Any is sound, but supported predicates with fixed parameters need adapters. Total/partial freshness theorems expose cofinite equations rather than all-inputs-fresh-for-function equations. Parameterized FCB lifting has cofinite computation and uniqueness, but lacks a direct convenient fresh-for-parameter computation interface. These are derived interfaces, not missing foundations.

**Remedy/dependencies:** C-04/C-06/N-04: derive precisely the wrappers consumed by lambda and function tooling, reusing Some/Any and existing support bounds. Keep uniformity over all bodies explicit in FCB.

**Verification:** a fixed-parameter predicate and a parameterized binder handler should compute at an explicitly fresh atom without manually rebuilding finite exception sets. Preserve nonempty/totality hypotheses where needed.

### L-01 — Public quotient inversion should precede reduction proofs

**P2; missing public API.** Lambda references: `Basic.lean:350,355,523–527,743`; `Recursion.lean:135–184`.

**Evidence/impact:** Raw `AEq` variable/application injectivity exists, but direct quotient constructor injectivity is not exposed as a complete basic interface. Constructor disjointness is supplied in Recursion; relation inversion is private and repeats quotient/raw-representative manipulation. Lambda equality via `NameAbs` is already public.

**Remedy/dependencies:** L-01/R-01 after B-04: consolidate quotient injectivity, disjointness, same-binder equality and inversion at a chosen fresh binder in Basic. Keep raw proofs behind that interface.

**Verification:** prove constructor/inversion examples and the first reduction inversion lemma using only public quotient APIs; no raw `AEq` case split should be needed by the client.

### L-02 — The supported-handler iterator needs a clearer public result contract

**P2; theorem-strength/interface gap.** Lambda references: `Recursion.lean:81–90,263,303–323`.

**Evidence/impact:** Application/binder handlers receive recursive results, not original subterms. Thus `recNoContext` is an iterator, not a direct primitive recursor. It returns a bare `Term α → Y`; relation uniqueness is proved, but there is no public result-support/NFun package, functional uniqueness, or avoidance-set-independence interface. Clients such as substitution re-establish nominal behavior separately.

**Remedy/dependencies:** L-02/N-04: first document the exact supported handlers, common finite support bound and FCB condition. Export support/uniqueness/independence results needed by clients. Derive primitive recursion with a `Term × Y` accumulator when needed, with appropriate FCB, or use a dedicated verified relation. The current iterator is sufficient for substitution.

**Verification:** same function built with two valid avoidance bounds is extensionally equal; its support lies in the handler bound; a parameterized client uses the NFun result directly. A primitive-recursion example must actually inspect an original child, not only its recursive result.

### L-03 — Strong term induction is present; fresh rule induction and confluence are absent

**P1 relative to first-release completion; missing feature, not a defect in existing induction.** Lambda references: `Induction.lean:86–115`; `Instances/LambdaCalculus.lean`; all four current lambda modules.

**Evidence/impact:** `strong_ind` permits arbitrary `P : Term α → Z → Prop`, fresh binders for a nominal context, and induction hypotheses quantified over contexts. No reduction relation, fresh reduction-derivation induction, parallel diamond, closure correspondence or Church–Rosser theorem exists. Quotient indices alone do not turn ordinary relation induction into BVC rule induction.

**Remedy/dependencies:** R-01 through R-07, detailed below. Define relations and prove equivariance plus binder-renaming compatibility; derive fresh rule induction before using BVC reasoning about derivations. Require contextual reduction under lambdas and open terms.

**Verification:** a substitution-compatibility proof consuming fresh rule induction, followed by explicit confluence, convertibility-to-joinability and normal-form uniqueness statements. No closed-term, termination or normal-form-existence assumption may silently replace the intended theorem.

### P-01 — Elaboration boundaries have measurable value; documentation overstates one of them

**P2 usability risk; P3 documentation correction.** Lambda reference: `Substitution.lean:156,213–233,255`.

**Evidence/impact:** Original migrated source builds. In independent scratch copies, removing only `seal Fresh in` causes the substitution equivariance proof to hit the default 200,000-heartbeat limit (`whnf`/tactic execution; approximately 7.38 seconds in this run). Removing only `seal subst` passes (approximately 1.48 seconds). Consequently the comment claiming both are necessary is not reproduced on this toolchain. The need for the Fresh boundary is reproduced. These are single local measurements, not a portable benchmark or asymptotic analysis.

Explicit `choose_fresh` consumer examples with 4, 16 and 64 atoms passed in approximately 1.39, 1.54 and 4.62 seconds, including process startup. The proof generator traverses a left-associated union separately for each membership path; monitor scaling rather than infer a general performance defect from these small timings.

**Remedy/dependencies:** N-05/M-03: retain boundaries until controlled replacement measurements justify a change; expose computation lemmas and profile concrete `isDefEq`/support rewriting. Qualify the historical performance comment. Do not globally raise heartbeat limits or unfold relational recursion as the default fix.

**Verification:** record toolchain/options, minimal reproducer and before/after timings; preserve the same theorem statement and axiom dependencies. Current evidence is recorded without changing either seal.

### D-01 — Module documentation needs a declaration-level pass

**P3; confirmed documentation defects.** References include `Concretion.lean:124–125` (“otherwise none”); `FCB.lean:9–10` and `Support.lean:15–16` (obsolete `NominalSets` paths); `FreshQuantifier.lean` inventory (`freshFTotal` versus actual `freshFT:499`); `Equivariant.lean:186,214` (curry/uncurry descriptions reversed); lambda `Substitution.lean:33` (`subst_lemma` versus `subst_subst`); lambda README/Induction references to absent `Beta`, `Pitts`, `nfun_ext` facilities.

**Evidence/impact:** The implemented statements can be correct while their advertised behavior or declaration names mislead clients. Recursion's “No equivariance proof is needed” wording also ignores the essential `RecRel.swap_equiv` proof; the accurate distinction is that predicates on quotient terms need no separate alpha-respectfulness proof.

**Remedy/dependencies:** D-01/C-06/B-04: reconcile inventories with declarations and imports; distinguish planned/experimental/current facilities and correct concretion behavior. Document the raw `Nominal/Syntax` sketch as such, not as the lambda case study or a finished unification package.

**Verification:** compile documentation examples with exact names and compare the module map to the supported build closure.

## Algebraic branch: mathematical specification must precede proof work

The following references are to `origin/fasapa/algebraic`, not the integrated core. Its own `Algebraic.lean:9` labels it a stub. All headline constructions have admitted bodies or depend on them; import failures currently prevent even that admitted skeleton from being checked as a module.

### A-01 — The proposed lambda signature has an empty initial algebra

**P1; confirmed specification defect.** References: `Algebraic.lean:132–157` (`NomSortExpr`, `interpSort`), `:400–417` (`LambdaSig`, `Lambda`, `var`).

**Evidence/impact:** `.data` denotes the recursive carrier, so the signature expresses `X + X × X + [A]X`, not `A + X × X + [A]X`. The former sends the empty nominal set to itself, and the empty algebra is initial: its unique map to every other algebra is a homomorphism. A total atom constructor into its initial carrier is impossible. Comments recognizing the distinction do not change the actual definition of `Lambda`.

**Remedy/dependencies:** A-01 before A-02/A-03: add an atom arity interpreted as `α`, distinct from recursive positions; use identity on atom positions in maps and `True` there in predicate lifting. One atom sort is enough.

**Verification:** work out atom-only, nullary, recursive and lambda functors by reduction, including their empty-carrier cases, before attempting initiality proofs.

### A-02 — Fixed-parameter substitution is not equivariant

**P1; confirmed false intended theorem.** Reference: `Algebraic.lean:604–605`, `Lambda.subst_equivariant`; compare correct joint law at `:608–609`.

**Evidence/impact:** For distinct `a,b`, substitution for `a` by `var b` sends both `var a` and `var b` to `var b`. Equivariance under `swap a b` would force `var a = var b`. A generic admission-free Lean witness proves the contradiction from variable injectivity/equivariance and these two equations. This also shows why equivariant-only fold handlers cannot directly express fixed-parameter substitution.

**Remedy/dependencies:** A-01/A-03: retain joint equivariance, and give fixed substitution finite support bounded by `{a} ∪ supp s`. Use supported recursion or an equivariant function into a nominal function carrier over parameters.

**Verification:** the two-variable counterexample must remain rejected as an equivariance theorem; prove the joint permutation and fixed-support laws with meaningful open-term examples.

### A-03 — Signature interpretation has circular instance and universe problems

**P1 implementation blocker; confirmed beyond imports.** References: `Algebraic.lean:152–173,200–212`.

**Evidence/impact:** `NameAbs α (interpSort α X σ)` requires the recursively interpreted nominal structure before the later `interpSort.instNominal` exists. Scratch normalization reproduces failed instance synthesis. `Unit`/`Empty` also inhabit universe zero rather than arbitrary `Type u`; `PermType.instUnit ▸ sorry` uses a structure where transport requires equality; product-instance names are stale. Repairing imports is insufficient.

**Remedy/dependencies:** A-02 after corrected signatures: interpret a carrier and its canonical nominal structure together, or separate raw shape interpretation from nominal semantics. Use `PUnit`/`PEmpty` or a deliberate universe restriction. Keep action projections coherent.

**Verification:** explicitly compile the interpretation module, nested binder/product examples and its action laws without admissions. The observed errors are from a 4.34.1 normalization experiment, not an original-4.28 build claim.

### A-04 — Generic induction omits induction hypotheses and freshness

**P2; confirmed statement-strength defect.** References: `Algebraic.lean:357–377`, `initialAlg_induction`/`initialAlg_induction_fresh`; `:558–564`, concrete fresh induction.

**Evidence/impact:** The step assumes `P (str x)` for every argument outright; no lifted recursive hypotheses appear. The “fresh” theorem's context `z` does not occur in its obligations. It gives neither useful structural induction nor a fresh-binder case. Requiring the user's fixed-parameter predicate to be equivariant excludes routine parameter-dependent proofs.

**Remedy/dependencies:** A-01/A-03: define predicate lifting through arities, expose recursive premises, and strengthen over avoidance contexts/permutations to derive arbitrary-predicate BVC induction.

**Verification:** a proof that genuinely consumes a recursive hypothesis and a freshness fact, with a free external parameter and nested binders. Merely proving constructor surjectivity does not satisfy this criterion.

### A-05 — Structural/initiality APIs sometimes state a weaker or different property

**P2; confirmed specification defects.** References: `Algebraic.lean:293–298`; `Structural.lean:228–229,263–265,298–301,383–387,483–504`.

**Evidence/impact:** `InitialAlg.algebraIso` is not tied to `algebra.str`. `discreteEquiv_symm` repeats a forward equation. The proposed second left-adjunction identity repeats uncurry-after-curry. `rightAdj_characterization` does not use `f`/`hf`; `rightAdj_counit_unit` does not mention the counit; the other right identity adds unnecessary freshness. `expEquiv_symm_abs` omits the inverse's promised computation formula. `liftAbs_equalizer` is pointwise congruence, not preservation of an equalizer object. Proving these statements would not establish the advertised universal properties.

**Remedy/dependencies:** A-01/A-04: formulate the intended maps, both inverse laws and the needed naturality/universal property; tie the constructor isomorphism to its structure map. Implement only categorical machinery used by the chosen construction.

**Verification:** inspect theorem types before proofs; instantiate the actual maps on small signatures and use both directions to derive a client property. An unused parameter is a warning to investigate, not by itself proof of falsity.

### A-06 — Generalized support is falsely quantified over arbitrary quotient actions

**P1; confirmed false statement.** Reference: `Structural.lean:583–584`, `NameAbs.supp_genAbs`.

**Evidence/impact:** The theorem assumes an arbitrary `[Nominal α (GenNameAbs α X Y)]`. Give that underlying quotient type the trivial action; all its supports are empty. With canonical atom actions on `X=Y=α` and distinct `a,b`, its claimed right side is `supp b \ supp a = {b}`, contradicting the empty left side. A compiled witness verifies the general discrete-action support fact; the quotient instantiation is a mathematical counterexample to the statement.

**Remedy/dependencies:** A-01/A-04: construct the canonical quotient action and state the theorem for that action, or require adequate compatibility rather than an arbitrary instance.

**Verification:** prove equivariance of the quotient projection and the support formula for the specified action; a caller-supplied unrelated discrete action must not satisfy the API's premises.

### A-07 — Non-preservation of products is not nonexistence of every set equivalence

**P1; confirmed overstrong/false statement, mathematical counterexample.** Reference: `Structural.lean:619–622`, `genAbs_finset_not_preserve_prod`; Pitts Example 4.25.

**Evidence/impact:** The code denies any bare `Equiv` between `[Finset A](X×Y)` and `[Finset A]X × [Finset A]Y` for some `X,Y`. Pitts instead shows that a particular canonical comparison fails to be onto. For countably infinite atoms and nonempty `X`, the quotient has cardinality `max(ℵ₀, |X|)`: upper bound from `Finset A × X`; lower bounds from the injective empty-binder map on `X` and from the invariant cardinality of the binder. The two product types therefore have equal cardinalities for all nonempty `X,Y`; if either is empty both sides are empty. Classical choice supplies bare equivalences. This cardinal argument was checked mathematically, not formalized in Lean.

**Remedy/dependencies:** A-01/A-04: define the canonical comparison and prove its failure of surjectivity, for example using the pair consisting of an empty-bound free atom and a singleton-bound atom. Keep bare equivalence, equivariant equivalence, natural isomorphism and invertibility of a particular map distinct.

**Verification:** prove the explicit missed-image example. Do not try to prove the current stronger negative statement.

### A-08 — The separated-product declaration does not express its documented construction

**P2; confirmed type/specification mismatch; associated source question.** Reference: `Structural.lean:423–425`, `sepProdDistribEquiv`.

**Evidence/impact:** `SepProd α X` means `X * A`. Consequently the declaration relates `[A]((X×Y)*A)` to `(([A]X×Y)*A) + ((X×[A]Y)*A)`, not the documented binary separated product. Under the intended canonical actions, at `X=Y=Unit` these have nominal orbit shapes `A+1` and `A+A`: the former has a fixed point, the latter none. An equivariant isomorphism is impossible, although a **bare** set equivalence exists for infinite atoms; the literal declaration only asks for the latter.

The printed formula in local Pitts Exercise 4.6 also merits correction/rechecking: at `X=Y=Unit`, its stated `[A](X*Y) ≅ [A]X*Y + X*[A]Y` would identify a singleton with two elements. Its piecewise conditions overlap when the binder is fresh for both operands. The inspected [official errata](https://www.cl.cam.ac.uk/~amp12/papers/nomsns/errata.pdf) does not list this exercise. This is an independently derived apparent source error, not an established published erratum.

**Remedy/dependencies:** A-01/A-04: do not adopt the formula merely because it is attributed to the book. Specify the intended binary product and account for overlap/vacuous binding, or omit this unused extension.

**Verification:** Unit/Unit and atom examples, including equivariance and both inverse laws, before any generic claim.

### A-09 — The algebraic files are not ready to export or merge

**P1 before integration; contained experimental status.** References: first imports of `Structural.lean`/`Algebraic.lean`, absent exports in branch `Nominal/Set.lean`, `InitialAlg:279` and its instance.

**Evidence/impact:** Obsolete `NominalSets.*` imports and namespace, extensive active `sorry` bodies, independently admitted action structures and the preceding specification defects prevent a verified package. A successful build of the branch's unchanged umbrella would not inspect them. The comment claiming correct signatures in Structural is contradicted by the statement review.

**Remedy/dependencies:** A-01 through A-04/B-05: keep the sketch explicitly experimental; integrate individual proved pieces only after statement review, explicit module compilation and dependency inspection.

**Verification:** no `sorryAx` in each newly supported module's exported closure, coherent action instances and a working concrete signature. A raw count of `sorry` tokens is not a completion metric.

## Rocq and article findings

Article paths below are relative to the article repository at the pinned revision. Rocq paths are relative to the specified Rocq revision. These findings concern historical/source accuracy; they are not imported assumptions of Lean.

### H-01 — Least support is incorrectly presented as strong support

**P1 mathematical exposition defect.** Reference: `LSFA 2025 (EPTCS)/EPTCS/const-nominal.tex:22–25`, equation (3) in the [published article](https://arxiv.org/html/2509.25883v1); parallel manuscript copies.

**Evidence/impact:** For distinct atoms, swapping `a,b` fixes the unordered finite set `{a,b}` while moving both members of its least support. Thus fixing an element does not imply fixing its least support pointwise. The integrated Lean library proves the counterexample in the appendix and correctly keeps strong support separate.

**Remedy/dependencies:** D-03: replace the biconditional by the support implication, or explicitly restrict to strongly supported elements. Do not weaken correct Lean support theory to match the prose.

**Verification:** retain the two-atom counterexample and check all uses of the converse in each article version. Record publication corrections separately from repository implementation.

### H-02 — The paper's action convention conflicts with its stated multiplication

**P2 mathematical exposition defect.** Reference: `EPTCS/const-nominal.tex:5–8` and corresponding displayed action law.

**Evidence/impact:** The text identifies multiplication with ordinary function composition, then writes `g • (h • x) = (h * g) • x`. With usual composition the order is `g * h`. Rocq's swap-list multiplication uses its own opposite-order convention consistently, whereas Lean uses the standard `mul_smul`. Readers cannot transfer equations without fixing the convention.

**Remedy/dependencies:** D-03: use the standard left-action order in mathematical prose or explicitly define opposite multiplication and explain the Rocq encoding. Avoid silently switching conventions.

**Verification:** check two noncommuting swaps on three distinct atoms, not only a single involutive swap; compare both implementations' composition equations.

### H-03 — Constructive limitations and function support are overstated

**P2; claims need correction/qualification.** References: `EPTCS/const-nominal.tex:74,87`; `EPTCS/discussion-related.tex:18`; extended notes on `Prop`.

**Evidence/impact:** The cited Swan result establishes implications to WLPO; its general least-support discussion even derives stronger bounded excluded-middle consequences. It does not justify the manuscript's unqualified equivalence with WLPO. The claim that Some/Any or induction needs a nominal calculus merely because of `Prop` is also too broad: one can state relational equivariance and prove appropriate logical equivalences; current Rocq already proves concrete Some/Any and alpha-compatible induction. Finally, nominal domain/codomain alone do not make every ordinary function finitely supported. [Swan, Theorems 3.3 and 3.5](https://arxiv.org/pdf/1702.01556).

**Remedy/dependencies:** D-03/C-04: state exactly which support-function/least-support principle, base theory and implication are known; distinguish interface choices from impossibility results. Require finite-support evidence for arbitrary functions. Retain the valid constructive motivation for supplied supports and setoids.

For example, parity from natural-number atoms to a discrete Bool is not finitely supported: outside any proposed finite support, swap one even and one odd atom. The swap fixes the proposed support but changes the function. Both endpoint types are nominal.

**Verification:** theorem-by-theorem citation correspondence and explicit hypotheses; a supported predicate example should demonstrate what is available without claiming arbitrary predicates supported.

### H-04 — The article-linked Rocq tag has active admitted dependencies

**P1 for claims about that archived formalization; historical issue.** References: `lsfa2025` `theories/Instances/Perm.v:9–13`, `PermPermT`/`PermNominal`; `_CoqProject`; `Example/Lambda.v:3`.

**Evidence/impact:** Both instances end in `Proof. Admitted.` in the fetched tag and belong to the active project/import closure. Main fills them with proofs at `Instances/Perm.v:11–31`. The tag's Lambda and Substitution source files are otherwise identical to main, including `alpha_ind`, `alpha_rec`, and `subst_comp`. Therefore neither “the tag has no lambda results” nor “the tag's whole source closure is admission-free” is accurate. Full transitive Rocq assumption output remains unverified because the compiler is unavailable.

**Remedy/dependencies:** D-03: document archived admissions and their resolution in main; distinguish theorem source presence from complete dependencies. Publish a reproducible corrected artifact/version if making a current completeness claim, without rewriting historical tags during this review.

**Verification:** rebuild pinned tag and main with compatible Rocq/stdpp; run `Print Assumptions` for the instances, freshness/abstraction results, `alpha_ind`, `alpha_rec` equations and `subst_comp`.

### H-05 — An excluded historical extensional-function axiom is inconsistent with stored support data

**P1 if reused; excluded/deleted experiment.** Reference: `lsfa2025` `theories/Instances/ExtensionalSupportedFunctions.v:7–12,48,83`.

**Evidence/impact:** This record stores `f_supp` as computational data but uses Leibniz equality and postulates equality from pointwise agreement. Bundle the same constant function once with empty support and once with a singleton support; both certificates are valid. The axiom equates the records, and projection equates their different support fields. This is stronger than ordinary functional extensionality. The file also contains a real final admission. It is **absent from `_CoqProject` and not imported by supported modules**, and is removed in current main. Main's `SupportedFunctions.v` uses pointwise setoid equality and avoids this contradiction.

**Remedy/dependencies:** D-03: explicitly label this historical experiment excluded; do not resurrect it as an extensionality shortcut. For extensional equality, keep support as proof-only existence, quotient away certificates, or retain the sound pointwise setoid.

**Verification:** assumption/import-closure audit and the distinct-support-record counterexample. No claim of a Rocq-compiled contradiction is made here.

### H-06 — The excluded Rocq concretion sketch cannot be restored by syntax repair alone

**P2; dormant implementation/specification defect.** Reference: main `theories/Concretion.v:6–22`; absence from `_CoqProject`.

**Evidence/impact:** The file has obsolete representation/syntax references and is not built. More fundamentally, it tests nonmembership in a supplied support, which can overapproximate semantic dependence. Give a discrete body a padded support `{b}` and take `a ≠ b`. Representatives `[a]x` and `[b]x` are alpha-equivalent, yet its proposed concretion at `b` returns `None` for the former and `Some x` for the latter. The active Rocq semantic freshness relation deliberately avoids identifying freshness with nonmembership in arbitrary supplied support. Lean's least-support implementation does not have this problem.

**Remedy/dependencies:** D-03/C-06: mark the sketch excluded; if revisited, use a representation/domain condition based on semantic freshness or justified exact supports, with a well-definedness proof.

**Verification:** alpha-equivalent representatives with padded supports must give equal partial results. A successful syntax-only port would be insufficient.

### H-07 — Extended drafts need a precise type/theorem correspondence pass

**P2; draft accuracy and publication-status gap.** References: both top-level `main.tex:103–106` inclusion lists; `Nominal Sets in Rocq (Extended)/Extended Version/main-extended.tex:108–116`; in that nested directory, `recursion-principle.tex:9–36`, `alpha-principles.tex:28`, `induction-principle.tex:30,51`, and `substitution.tex:1`.

**Evidence/impact:** A directory called “Extended” is not itself evidence that its extra sections are included: both top-level mains still input the short article's four sections. The separate nested extended main reaches the induction/recursion material. That material describes an iterator, calls a function `Λ → ℕ` a type-valued motive, uses conjunction where a package of handler types is intended, and contains an alpha-rule conclusion using `M` twice despite a premise involving `M,N`. Its FCB/support snippets do not consistently match current semantic freshness. A stored support equal to `L` in Rocq must not become a claim that Lean's *least* support equals every chosen bound `L`. The extended substitution file is not a completed account of the implementation.

The draft also identifies the arbitrary avoidance set `L` with support of the predicate, although `alpha_ind` assumes neither that the predicate is supported nor that `L` supports it. Even a support upper bound would not justify the claimed freshness equivalence. Its description of all provable propositional equality as reduction/convertibility likewise needs correction. These are draft exposition errors; the corresponding source induction statement has the appropriate hypotheses.

**Remedy/dependencies:** D-03/D-02: select the intended manuscript entry point, distinguish draft/editorial text from published claims, and map each displayed statement to its exact source theorem. Describe iteration versus primitive recursion and chosen versus least support explicitly.

**Verification:** build the intended manuscript version when publication work resumes, compile/check its code examples against the pinned development, and inspect all input files rather than only the directory title.

## Constructive-to-classical correspondence

| Concept | Rocq source | Lean source and deliberate difference |
| --- | --- | --- |
| Names | `Name.v`, abstract `ATOMIC` module implemented with naturals | `Core/Name.lean`: arbitrary decidably equal infinite type; no countability assumption |
| Permutations | `Permutation.v`, swap lists with extensional equivalence and list-order multiplication | `Core/FinitePerm.lean`, actual finite bijections; standard composition |
| Equality/actions | `PermT.v`, setoid equality plus `Proper` obligations | `PermType` extends `MulAction`; equality is Lean equality; quotient boundaries are explicit |
| Support | `Nominal.v`, supplied finite `Support` and swap-fixing law | `Nominal.finSupp` is existence in `Prop`; `supp` is classically selected least support |
| Freshness | `Fresh.v`, existential swap witness and equivalent universal condition | `Freshness/Basic.lean`, support disjointness; atom form is nonmembership in least support |
| Functions | `Instances/SupportedFunctions.v`, actual support field plus pointwise setoid equality | `PFun`/`NFun`, conjugation wrapper plus proof-only finite-support existence; extensional equality from Lean foundations |
| Abstraction | `NameAbstraction.v`, pair record with alpha setoid | `NameAbstraction.lean`, quotient by alpha equivalence, exact support deletion |
| Freshness theorem | `FreshnessTheorem.v`, constructive total function and Some/Any computation | `FreshQuantifier.lean`, total and partial formulations, cofinite computation, support/uniqueness and classical extraction |
| FCB | Lambda's `fcb_some_any`, `_flam`, associated proofs | General reusable `FCB.lean`, partial/total/parameterized interfaces; some useful logical wrappers still absent |
| Term induction | `Example/Lambda.v:382`, `alpha_ind`, requires alpha-compatible predicate | Lambda `strong_ind:86`, arbitrary predicate on quotient terms; context-generalized IH |
| Iteration | `Example/Lambda.v:781`, `alpha_rec`, constructive permutation-parameter construction | Lambda `Recursion.lean`, graph relation, totality/uniqueness, classical choice |
| Substitution | `Example/Substitution.v:48,87`, `subst`, `subst_comp` | Lambda `Substitution.lean`, computation/forget/freshness/joint equivariance/composition/support bound |
| Rule induction/confluence | Not present in inspected main/tag sources | Not present in current/lambda Lean sources; release work remains |

`ATOMIC`'s `Parameter`/`Axiom` fields are module-signature requirements, realized by definitions/instances in `Atom`; they are not unexplained active global axioms. The two `Admitted` occurrences inside a commented alternative alpha-equivalence experiment in main `Example/Lambda.v:131–146` are also not active assumptions. These must be distinguished from the active tag admissions in H-04 and the excluded experiment in H-05.

The `exact_no_check` token in main `Example/Lambda.v:246` occurs in a proof-producing Ltac helper that first constructs a typed proof and then uses `abstract`. It is not an additional axiom or evidence that final declaration checking has been disabled.

Classical choice and noncomputable operations are an intentional Lean design decision. Removing setoid respectfulness obligations and selecting quotient-level functions changes the engineering contract and extraction behavior; it does not invalidate the constructive precursor. Conversely, a constructive chosen support is not generally invariant under setoid equality or minimal. Do not transport exact support equations without checking this distinction.

## Practical NFun design recommendation

Keep the existing representation and its `FunLike` application. The observed failures do not justify replacing it wholesale. Establish examples first, then make the ordinary operations predictable:

1. Integrate and review the lambda branch's existing equivariant/captured/parameter adapters.
2. Expose `uncurry` and useful fixed-argument adapters, with pointwise equations, support bounds, action laws and curry/uncurry inverse laws. Use `DFunLike.congr_fun` and existing `ext` rather than another extensionality mechanism.
3. Choose a normalization policy: `simp` should expose application equations and ordinary-function coercions without expanding support certificates or relational recursion. Avoid mutually reversing simp rules.
4. Supply focused proof-producing support automation for identity, constants, evaluation, application, products, composition, curry/uncurry and registered equivariant constructors. Infer an upper bound from supported captures, not a purported exact least support.
5. Preserve an explicit support/proof escape hatch and local diagnostics. A function's type does not guarantee finite support, and arbitrary global constants cannot be trusted as equivariant.
6. Treat a general expected-type, binder-aware `nfun` elaborator as later work. If the prototype remains shipped, label its supported subset and make examples honest.

An NFun abstraction map deserves a small separate specification when a client needs it. The tempting equation `[a]x ↦ [a]f(x)` is not valid on every representative for arbitrary supported `f`; choose a binder fresh for `f`, prove independence, and expose the equation under `a # f`. Reuse FCB/fresh-representative machinery. This is a useful interface direction, not authorization to implement it in this review.

### Optional cleanup after client-facing gaps

**P3; maintainability opportunities, not release blockers.** References: lambda `NameAbstraction.lean`'s added `abs_unique_parametric`, `Recursion.lean:263` (`RecRel.unique`), and the branch diff of `FCB.lean` changing helpers from private to public; current `Concretion.lean`'s extensionality aliases and large handwritten module inventories.

**Evidence/impact:** The lambda uniqueness proof repeats a fresh-representative/FCB pattern despite a general parameterized helper in the branch. Several FCB implementation helpers become public without a deliberate supported-API boundary. Hand-maintained declaration inventories already drift (D-01). These increase maintenance effort; there is no evidence that all aliases or long proofs should be removed.

**Remedy/dependencies:** Roadmap B-04/C-05/C-06/D-01: review which helpers clients actually need, compare hypotheses before reusing the parameterized uniqueness lemma, and consolidate documentation around stable entry points. Preserve intentional aliases and computational/proof boundaries. Treat namespace/header/reducibility warnings individually; do not globally suppress them or rename the hierarchy for style alone.

**Verification:** affected module plus downstream lambda builds, unchanged public theorem statements/axioms, and simpler real client proofs. Any proof refactor must demonstrate benefit rather than merely reduce line count.

## BVC reasoning and the remaining Church–Rosser path

The lambda strong induction principle is already strong enough for many mathematical proofs: it generalizes induction hypotheses over all nominal contexts, so a nested binder can avoid parameters and previously selected binders. It does not demand equivariance of the user's predicate. This result should be preserved verbatim through integration.

For reduction, the induction object changes from a term to a **derivation**. A fresh binder must be chosen consistently in premises, source/target terms and the contraction result. Relation equivariance, substitution renaming and fresh inversion supply that consistency. The official Isabelle [CR development](https://isabelle.in.tum.de/library/HOL/HOL-Nominal-Examples/CR.html) separately declares equivariance and obtains nominal induction for beta and parallel reduction; its term induction is a distinct facility. The [Takahashi example](https://isabelle.in.tum.de/library/HOL/HOL-Nominal-Examples/CR_Takahashi.html) provides an alternative complete-development route. These are architectural reference points, not imported Lean proofs.

Recommended dependency order:

1. **B-04/B-05:** integrate the independently verified lambda work on the current core; establish complete local build and persistent regression/axiom commands.
2. **C-01/C-02, N-01, L-01:** repair freshness coverage/identity/splitting, establish NFun consumer examples and stabilize quotient constructor/inversion APIs. These workstreams can proceed independently after integration.
3. **N-02–N-04; L-02/L-03, alongside the following semantics steps:** improve adapters and rewriting where actual handlers/proofs expose friction. Export iterator support/uniqueness as needed. Focused support automation can help a concrete client; completing N/M is not a prerequisite for the reduction/confluence work.
4. **R-01/R-02:** complete needed substitution identity/renaming compatibility; define full contextual beta and parallel reduction on quotient terms. Prove equivariance and freshness preservation.
5. **R-03:** derive fresh rule induction/inversion generalized over an avoidance context. If rules impose fresh-binder premises, prove equivalence with the intended unrestricted quotient-level reduction.
6. **R-04:** prove parallel substitution compatibility for both related subjects and related replacements. This is stronger than reducing only the subject under a fixed replacement.
7. **R-05:** choose direct parallel diamond as the initial recommendation. Complete development is a valid alternative, but syntax-inspecting application behavior may need primitive-recursion access or a dedicated well-defined graph. Choose based on the concrete proof interface, not historical preference.
8. **R-06:** prove `beta ⊆ parallel ⊆ beta*`, identify closures, obtain beta confluence, and derive Church–Rosser for beta convertibility. Use suitable existing Mathlib relation lemmas after checking their orientation/hypotheses.
9. **R-07/D and the required N/M subset:** prove uniqueness of normal forms; finish client-driven interface polish/focused automation, the compiling tutorial, documentation, assumptions and release record. Do not claim termination or existence of normal forms.
10. **General M, then A/P later:** use the completed case study to specify broader tooling; correct the restricted signature and prototype generic raw syntax plus alpha quotient; only then derive/generate its public nominal interface.

The first nine steps are concrete deliverable work. Generic initial-algebra theory, generalized binders and datatype commands must not become prerequisites for manual untyped confluence. Function usability remains a release requirement even if the confluence proof can be completed manually.

## Generic construction and eventual generation

Given the author's goal, a restricted generic raw-syntax construction plus alpha quotient is the preferred first experiment. Add atom positions; keep recursive positions strictly positive; specify the semantics of single/nested binders; establish action, support, alpha equivalence and quotient constructors; then derive the same induction/iteration contract as the manual lambda example. Prove that the generated lambda instance agrees with the existing one, and test a second language within the same grammar before broadening it.

A direct constructor through `NameAbs α Syntax` must resolve the circular nominal-instance requirement and demonstrate strict positivity through the abstraction representation; the sketch supplies no kernel-accepted resolution. This is not a proof that every conceivable direct encoding is impossible. The existence of an abstraction exponential isomorphism does not license arbitrary negative/function-space recursive occurrences.

An initial-chain construction remains mathematically viable but would require actual chain colimits, coherent action/support, functorial maps, preservation of the relevant filtered colimits and the initial universal property. Binary product/sum isomorphisms are insufficient evidence. The algebraic introduction also reverses the book's adjunction references: `[A]` has a left adjoint in Theorem 4.12 and a right adjoint in 4.13; the latter makes `[A]` a left adjoint preserving colimits. There is no need to implement the entire Structural catalog to generate the agreed binding grammar.

## First-release completion criteria

Release completion should require all of the following, with a recorded revision and local evidence:

- The core and lambda case study are integrated and reached by a documented complete build from tracked source and pinned dependencies; important examples are persistent. No CI requirement.
- No admissions/custom unproved assumptions in supported Lean modules; representative and broad project axiom checks report only the accepted foundations.
- Fresh-name selection covers its documented inputs, preserves local identity, and gives meaningful diagnostics. Nested freshness splitting has tested naming/association behavior.
- Public action/support/freshness/quotient/abstraction/concretion/FCB interfaces are documented and demonstrated, including nested binders. Necessary hypotheses and same-universe/single-sort limitations are explicit.
- NFun application, composition, curry/uncurry, partial application, rewriting and supported construction work in actual lambda handlers with little wrapper boilerplate. Focused support automation produces kernel-checked proofs and exposes unsupported obligations. General lambda elaboration may remain deferred.
- Quotient lambda constructor/inversion, support, strong term induction, iterator computation/uniqueness and substitution laws are public enough for semantics proofs. Any stronger recursion interface is justified by an actual client.
- Full open-term contextual beta confluence, Church–Rosser for convertibility and uniqueness of normal forms are proved. Fresh rule induction or an explicitly justified alternative supports every BVC step.
- A compiling tutorial demonstrates alpha renaming, genuinely capture-avoiding substitution, substitution composition, term versus rule induction and the confluence argument.
- Confirmed release-blocking defects are resolved; deferred research and prototype syntax are explicitly labeled. Algebraic stubs/generalized binders/multiple atom sorts/universe generalization/datatype generation are not silently counted as delivered.
- Paper/Rocq/Lean correspondence and archived admissions are described accurately. Publication changes, if any, have their own verified version record.

## Reproduction appendix

Scratch files are review artifacts and may disappear. The essential reproductions are included here so findings do not depend exclusively on `/tmp` paths. These are experiments, not newly integrated tests.

### Shadowed-local freshness failure

Run with current `lake env lean`:

```lean
import Nominal
open Nominal.Core Nominal.Set

example {α X : Type} [Name α] [Nominal α X] (x : X) :
    ∀ y : X, ∃ a : α, a # x ∧ a # y := by
  intro x
  choose_fresh a from X
  exact ⟨a, aFresh1, aFresh2⟩
```

Expected current failure: `aFresh1` has type `a # x` but the goal requires freshness for `x✝`. Replacing `from X` by automatic scanning reproduces the same identity loss.

### Least support need not be strong support

This **passes** against current core:

```lean
import Nominal
open Nominal.Core Nominal.Set

example {α : Type} [Name α] (a b : α) (hne : a ≠ b) :
    ¬ StrongSupports (supp ({a,b} : Finset α)) ({a,b} : Finset α) := by
  rw [supp_finset]
  intro h
  have hfix : swap a b • ({a,b} : Finset α) = {a,b} := by
    simp [PermType.finset_smul, Finset.pair_comm]
  have bad := (h (swap a b)).mpr hfix a (by simp)
  exact hne (by simpa using bad.symm)
```

### Prototype macro failures

In the migrated lambda export, these definitions fail for the reasons in N-02/N-03:

```lean
import Instances
open Nominal.Core Nominal.Set LambdaCalculus
variable {α X : Type} [Name α] [Nominal α X]
noncomputable section

def autoVar : NFun α α (Term α) := nfun fun a => Term.var a
def localLet (c : X) : NFun α X X := nfun fun x => let y := c; y
```

The existing proof-backed `NFun.equivariant Term.var (by intro π a; simp)` succeeds in that branch. Thus the failure concerns the macro, not the mathematical existence of the supported constructor.

### Broad axiom check

```lean
import Nominal
import Lean.Util.CollectAxioms
open Lean Elab Command

set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  let mut unusual : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "Nominal." ||
        n.toString.startsWith "_private.Nominal." then
      count := count + 1
      let ax ← collectAxioms n
      let extra := ax.filter fun a =>
        a != `propext && a != `Classical.choice && a != `Quot.sound
      if !extra.isEmpty then
        unusual := unusual + 1
        logInfo m!"{n}: {extra}"
  logInfo m!"Checked {count}; unusual dependencies: {unusual}"
```

The heartbeat override here affects only audit traversal, not acceptance of library proofs. For the lambda export, import `Instances` and include the `LambdaCalculus.` and `_private.Instances.` prefixes.

### Reproduce the separate lambda migration

Use a fresh directory outside the working tree; do not apply this patch to `fasapa/next`:

```sh
review_dir=$(mktemp -d /tmp/nominal-lambda-repro.XXXXXX)
git archive 9f04655838b77283a056705cf5554dc48806e7db | tar -x -C "$review_dir"
git -C "$review_dir" apply --check "$PWD/docs/migrations/lambda-4.34.1.patch"
git -C "$review_dir" apply "$PWD/docs/migrations/lambda-4.34.1.patch"
cp lean-toolchain lake-manifest.json "$review_dir/"
python3 - "$review_dir/lakefile.toml" <<'PY'
from pathlib import Path
import sys
p = Path(sys.argv[1])
p.write_text(p.read_text().replace('v4.28.0', 'v4.34.1'))
PY
# Reuse the existing matching dependencies, as in this review.
# This does not test clean-machine dependency installation.
mkdir -p "$review_dir/.lake"
ln -s "$PWD/.lake/packages" "$review_dir/.lake/packages"
cd "$review_dir"
lake build Nominal Instances
```

The saved source patch SHA-256 is `7f154a3b1d0a175ed5f1d5c4cb458c9d8caf713b35c379d1694acc1396ffc276`. The inspected Pitts PDF SHA-256 is `546104434ce6388d2aed248428cc8bde653bf98780cee55265f686e7290f0794`.

### Local evidence retained during review

- `/tmp/nominal-core-review-build.log`: fresh core project build.
- `/tmp/nominal-lambda-review-build.log`: separate migrated lambda build.
- `/tmp/CoreReviewPass.lean`, `/tmp/CoreReviewCoherence.lean`: successful core clients/coherence/counterexample.
- `/tmp/CoreReview.lean`, `/tmp/CoreReviewShadow.lean`: intentional tactic/universe failures.
- `/tmp/nominal-lambda-review.FQ5W8o/ReviewSuccess.lean`, `ReviewFailures.lean`, `ReviewMoreFailures.lean`: positive lambda clients and prototype failures.
- `/tmp/NominalAxiomReview.lean`, `/tmp/NominalLambdaAxiomReview.lean`: broad axiom sweeps.
- `/tmp/nominal-algebraic-review/Witnesses.lean`, `algebraic-build.log`: independent witnesses and normalized interpretation failures.
- `/tmp/NominalFreshPerf{4,16,64}.lean`, `/tmp/NoSubstSeal.lean`, `/tmp/NoFreshSeal.lean` and corresponding seal logs: performance probes.

## Limits of verification

Fresh project artifacts were rebuilt, but dependencies came from the existing pinned local cache. A clean-machine dependency-download/bootstrap test was not performed. Original Lean 4.28 branches were source-reviewed, not rebuilt in this review. The algebraic branch was not repaired or certified by its normalized experiments. Rocq proofs were source-reviewed but not compiler-checked, and their exact transitive `Print Assumptions` output remains pending. Article TeX/PDF builds and Isabelle session builds were not run. Other Rocq research branches and older `msc`/`wbl21` releases were not audited. The apparent Pitts Exercise 4.6 issue and generalized-quotient cardinality counterexample are mathematical analyses, not newly formalized library results. Performance measurements are limited local probes.

These limits are retained as open verification work in the roadmap rather than converted into completion claims.
