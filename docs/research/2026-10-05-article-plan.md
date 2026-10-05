# Research notes and evolving mathematical article

Date: 2026-10-05. Proposed writing workflow for the
[package research](2026-10-05-package-architecture.md), not a publication claim.
The article should develop alongside proofs and client experience; it should
not present proposed package contracts as already established results.

## Keep one owner for each kind of claim

| Artifact | Role | Update rule |
| --- | --- | --- |
| [Research brief](2026-10-05-nominal-package-brief.md) | Settled user decisions, intent and unresolved choices | Append decisions with date, alternatives and reason; preserve superseded positions |
| Dated investigation notes | Mathematical arguments, literature readings, counterexamples and design alternatives | Record exact source version, statement assumptions, Lean evidence and limitations |
| `docs/research/probes/` | Small reproducible experiments, including guarded failures | Each probe states purpose, command and nonclaims; keep out of supported umbrellas until deliberately promoted |
| [Package roadmap](../nominal-package-roadmap.md) | PKG task IDs, dependency/status tracking, delivered verification | Link to notes instead of copying proofs; mark complete only against stated acceptance criteria; keep the prior library roadmap as historical evidence |
| Future `docs/research/claims.md` | Statement-to-evidence ledger | Add a row whenever the manuscript makes or changes a substantive claim |
| Future `docs/article/` | Coherent evolving exposition | Use the ledger; distinguish proved, source-attributed and proposed sections visibly |
| Per-increment spec/plan | Approved implementation boundaries and execution checks | Written only for the next bounded increment; link its PKG and existing task IDs |

The future paths are proposed, not files silently created by this task.
Use Markdown for the initial article sections so theorem statements and evidence
can evolve cheaply. Move to a single LaTeX entry point plus included sections and
a versioned bibliography when the exposition stabilizes or a venue requires it.
Do not maintain independent Markdown and TeX versions of the same prose.
No external manuscript repository is modified by this plan.

## Claim ledger format

Each claim should record: stable claim ID; exact mathematical statement and
hypotheses; status; Lean declaration/module and source revision; proof dependency
policy; source/theorem/page when inherited; commands actually run; counterexample
or failure history; manuscript location; next unresolved obligation.

Possible initial entries (examples of the ledger format):

| ID | Statement/status | Precise evidence | Limitation |
| --- | --- | --- | --- |
| CL-001 | Least support is not necessarily strong support — integrated counterexample | `Examples/CoreContracts.lean`, unordered atom-pair example; standard foundations | Does not refute least-support existence |
| CL-002 | Arbitrary-motive, context-generalized fresh term induction — integrated | [`Term.strong_ind`](../../Instances/LambdaCalculus/Induction.lean); current baseline and audit | Concrete lambda theorem; generic generation remains proposed |
| CL-003 | Supported iteration with guarded lambda equations and uniqueness — integrated | [`Term.recNoContext_lam`, `recNoContext_unique`, `recNoContext_supports`](../../Instances/LambdaCalculus/Recursion.lean) | Iteration, not primitive or dependent recursion |
| CL-004 | Fresh rule induction for unrestricted beta/parallel — integrated | [`Term.Beta.strong_ind`, `Term.Parallel.strong_ind`](../../Instances/LambdaCalculus/ReductionInduction.lean) | Relation-specific proofs; no arbitrary-judgment theorem inferred |
| CL-005 | Church–Rosser and normal-form uniqueness for open contextual terms — integrated | [`Term.BetaEq.church_rosser`, `Term.BetaEq.normal_unique`](../../Instances/LambdaCalculus/ChurchRosser.lean) | No normalization/existence claim |
| CL-006 | Compatible raw Prop predicates correspond to quotient predicates — scratch | [Predicate probes](2026-10-05-predicate-foundations.md), named descent/pullback results | Not a generated dependent eliminator |
| CL-007 | Straight recursive NameAbs encoding is rejected — scratch negative | [BackendPositivity.lean](probes/BackendPositivity.lean), exact guarded diagnostics | Not a universal impossibility theorem |
| CL-008 | Unconditional abstraction mapping for supported functions fails — scratch theorem | [BackendCounterexamples.lean](probes/BackendCounterexamples.lean), `no_unconditional_const_abs_map` | Fresh-binder mapping remains possible research |
| CL-009 | Generic fresh rule criterion — primary-source theorem | [2025 comparison](2026-10-05-isabelle-comparison.md), Definition 6/Theorem 7 | No Lean port or Isabelle build in this research turn |
| CL-010 | Complete generated syntax/function/judgment workflow — proposed | PKG-07 acceptance criterion | No implementation/generation result yet |

Record actual declaration names when creating the ledger; a descriptive label is
not an adequate theorem reference. Re-run audits after a dependency-changing
proof refactor. A cached build, direct source elaboration, fresh project build
using cached dependencies, and clean dependency bootstrap are separate fields.

## Detailed article outline

### 1. Problem, audience and demonstrable scope

Explain the workflow for researchers defining first-order syntax with binders,
operations and judgments. State classical Lean, one atom sort, finite syntax,
single/nested binders, and ordinary Prop reasoning. Introduce the five chosen
studies and explain which release/stage each actually reaches. Give a complete
small user program before describing implementation. While the DSL is proposed,
typeset examples as proposals and use the compiling manual tutorial as evidence.

Evidence: [tutorial](../tutorial.md),
[compiling tutorial](../../Examples/Tutorial.lean), PKG-07 through PKG-10.

### 2. Nominal mathematics and foundations

Specify atoms and finite permutations, action coherence, finite versus least
versus strong support, freshness and equivariance. Explain actual quotients,
classical choice and theorem-level computation. State the conjugation action on
supported functions and why it remains separate from ordinary pointwise actions.
Avoid treating the constructive Rocq choices as universal restrictions.

Statements: `supports_iff_swap`, `supp_supports`, `supp_le`,
`supp_equivariant`, `NFun.supp_apply_le`; sources in
[`Support`](../../Nominal/Set/Support.lean),
[`Nominal`](../../Nominal/Set/Nominal.lean),
[`NFun.Basic`](../../Nominal/Set/NFun/Basic.lean).
Use the [pinned correspondence](../research-correspondence.md) for external
versions and unresolved compiler evidence.

### 3. Predicates and the boundaries of quotient reasoning

Distinguish truth values, predicates, formula syntax, expressions and proofs.
Develop the supported powerset/NFun comparison, action/equality laws, logical
closure and quantifier support bounds. State Some/Any with its hypotheses.
Prove the alpha-compatible raw predicate/quotient predicate bridge, then
separate genuinely dependent families and coherent transport. Explain why fresh
induction can quantify over arbitrary motives despite these supported objects.

Evidence: [foundations note](2026-10-05-predicate-foundations.md), Pitts exact
numbered results, Copello 2016/2018, PKG-01. Include unsupported predicates and
the no-supported-fresh-selector result as boundaries of automation.

### 4. Binding signatures and construction of syntax

State the accepted grammar mathematically, including atom/data/recursive
positions, category indices, binding scopes, universes and positivity.
Describe raw construction, alpha relation, canonical quotient action and exact
support. Explain fresh/common representatives and constructor inversion.
For every generated carrier, identify the actual constructor map. State an
initiality theorem only if its map class, existence and uniqueness are proved;
do not substitute an unrelated type isomorphism.

Evidence: [backend comparison](2026-10-05-backend-comparison.md), PKG-02/04.
Show `let` scope and a binder over a product. Record unsupported containers and
what proofs would be needed to extend them.

### 5. Fresh induction, iteration and primitive recursion

Give separate statements for arbitrary-motive term induction, supported
iteration, primitive recursion using original subterms, and any later dependent
eliminator. Explain generalized avoidance contexts and nested binders.
Derive binder compatibility through NameAbs, concretion, FCB and fresh
representatives. Prove equations, uniqueness and support rather than claiming
definitional computation. If product reconstruction yields primitive recursion,
show the reconstruction invariant and binder descent explicitly.

Evidence: existing [lambda induction](../../Instances/LambdaCalculus/Induction.lean)
and [iterator](../../Instances/LambdaCalculus/Recursion.lean); PKG-03/05.
State where later generic results strengthen or merely instantiate these APIs.

### 6. Inductive judgments and the variable convention

Define the accepted rule grammar and certified semantic extension route.
Distinguish relation equivariance, fixed-parameter support, alpha compatibility,
refreshability and freshness preservation. Explain how all affected premises,
IHs and conclusions move together. Compare generated derivation proofs with a
generic monotone-operator theorem; state equivalence to the intended ordinary
inductive relation. Present both parallel contraction and an eigenvariable rule.

Evidence: [ReductionInduction](../../Instances/LambdaCalculus/ReductionInduction.lean),
[ReductionInversion](../../Instances/LambdaCalculus/ReductionInversion.lean),
original Nominal, Nominal2 and the 2025 theorem, PKG-06. Include a rejected rule
whose nominated binder is semantically free in the conclusion.

### 7. The proof-producing package interface

Explain command elaboration, normalized scope metadata, proof registries,
transactional failures, generated declaration names and ordinary Lean usage.
Show captured parameters, shadowed locals, higher-order functions, rewriting,
and a manual proof completing an unsupported automatic obligation. Describe
which proofs are generic and which are generated. Identify the trusted base as
Lean's normal kernel plus accepted standard axioms, not the metaprogram's claims.

Evidence: [proposed contracts](2026-10-05-package-contracts.md), eventually
generated acceptance tests. Report timing/size observations only with a pinned
configuration and controlled comparison; do not invent performance benefits.

### 8. Case studies, each with a distinct test

| Case study | Mathematical story | Package question tested |
| --- | --- | --- |
| Lambda calculus | Substitution, parallel diamond and Church–Rosser replay | Full syntax/function/judgment workflow, unrestricted reduction, open terms |
| First-order logic | Natural-deduction substitution admissibility | Multiple categories, finite contexts, eigenvariables and fresh rule induction |
| Lambda with let | Expansion correctness and substitution compatibility | Nonrecursive binder scope, original subterms and translation between generated languages |
| π-calculus | Bound transitions and fresh residual inversion; later a selected congruence result | Joint label/continuation binding, rule transport and channel names |
| Modal μ-calculus (proposed variant) | Positive substitution, semantic interpretation and fixed-point unfolding | Positivity independent of alpha support; μ/ν binders and semantic environments |

Do not claim all five are complete when only the first workflow is delivered.
For π and μ, state the chosen semantics before theorem statements. An arbitrary
semantic environment may lie outside the finitely supported function space;
the semantics must be modeled honestly instead of demanding unsupported global
instances. Bisimulation/coinduction is an additional semantic layer, not an
automatic consequence of nominal datatype generation.

### 9. Difficulties, failed approaches and limitations

Preserve: absent atom arity in the old lambda signature; false fixed-substitution
equivariance; direct recursive NameAbs failure; support/action incoherence;
unconditional supported abstraction mapping; finite-support quantifier limits;
choice-selected fresh functions; dependent coherence; rejected rule binders;
the ordinary recursion/container grammar boundary. State each as a theorem,
counterexample, compiler result or research risk, according to its evidence.

Separate problems inherited from an old sketch from properties of the completed
current core. List unsupported features and proof escape hatches without turning
them into unsound automatic promises.

### 10. Related work and reproducibility

Compare Pitts, original Isabelle Nominal, Nominal2, Copello's compatible
predicates, the Rocq precursor and other relevant generated binding frameworks
by exact theorem assumptions and user contracts. Extend the survey before any
priority claim. Include source hashes/revisions, toolchains, compilation commands,
axiom reports and explicit unavailable external builds. Explain which results
are inherited, re-proved under different foundations, generalized, or only
engineering interfaces. Finish with open mathematical questions, not speculative
claims of novelty or publication readiness.

## Sustainable update cycle

For every increment: record the question and discriminating test; preserve the
failed probe if any; review the statement; prove and compile; audit dependencies;
add a client that consumes the claimed fact; update the ledger and task status;
then revise the corresponding article section. A theorem rename updates the
ledger and its links in the same change. A changed hypothesis reopens dependent
claims. A proposed command becomes a demonstrated command only when the example
compiles through the supported import boundary.

At each milestone, perform a short consistency review across grammar, generated
contracts, case-study acceptance, ledger and manuscript. Avoid a second enormous
hand-maintained declaration inventory. A small future script can check linked
declaration names and Markdown paths if maintaining them becomes burdensome;
it is not a prerequisite for the first mathematical increment. No CI or recurring
automation is proposed or installed by this research task.
