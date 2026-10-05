# Nominal package: architecture and research roadmap proposal

Date: 2026-10-05. **For review; architecture and implementation are not approved.**
Branch: `fasapa/nominal-package`; HEAD:
`4279ba92efacd77b3b96e507631502272b489999`.

The intended result is a package through which researchers declare syntax,
operations and ordinary `Prop` judgments, then reason with explicit freshness
and avoidance. The nominal account and every generated guarantee must be checked
by Lean's kernel. This document recommends a direction, separates its remaining
proof obligations, and proposes a first implementation increment for approval.
It does not claim that the package or any command shown below exists.

Current task status and acceptance checklists are maintained in the separate
[nominal-package roadmap](../nominal-package-roadmap.md). The earlier library
roadmap retains the completed first-deliverable history.

## Reading order and evidence labels

1. [Requirements and decisions](2026-10-05-nominal-package-brief.md).
2. [Predicates, quotients and induction](2026-10-05-predicate-foundations.md).
3. [Isabelle and rule-induction comparison](2026-10-05-isabelle-comparison.md).
4. [Backend comparison and counterexamples](2026-10-05-backend-comparison.md).
5. [Proposed syntax and generated contracts](2026-10-05-package-contracts.md).
6. [Research-writing workflow and article outline](2026-10-05-article-plan.md).

**U** means a user decision; **I** an integrated existing theorem;
**S** a kernel-checked standalone scratch result; **L** a source reading;
**P** a proposed contract or design; **O** an unresolved obligation.
Successful probes under `docs/research/probes/` are S, never I. All new research
documents remain uncommitted. Earlier notes and roadmap history are retained.

## Decisions made in this discussion

- **U:** preserve the completed core and Church–Rosser client, classical Lean,
  actual quotients, least support, ordinary `Prop`, one atom sort, single/nested
  binders, multiple syntax categories, dedicated commands, and no CI/deadline.
- **U:** lambda calculus remains a required case study, including Church–Rosser.
- **U:** first-order logic with substitution admissibility is the second workflow.
- **U:** the case-study portfolio also includes lambda calculus with `let`,
  π-calculus and μ-calculus. The author selected `let` over imperative locals.
- **P:** finish the first complete generated workflow with lambda and first-order
  logic, then add the other three as explicit portfolio milestones. This staging
  does not remove any selected case study from the research program.
- **O:** exact command spelling, the complete μ-calculus variant, π transition
  convention, and approval of the first implementation increment remain open.

The optional interpreted nominal formula logic discussed earlier is not a
requirement. First-order and μ-calculus formulas are **object-language case-study
syntax**; they do not replace Lean `Prop` as the package's proposition language.

## Recommendation: a staged hybrid with a narrow public boundary

Use a normalized binding schema, a reusable proved nominal core, and
proof-producing per-declaration generation. Initially generate ordinary raw
recursive syntax and its alpha quotient for each declaration. Keep raw carriers
and relation witnesses behind generated constructors, equations, inversion,
support, induction and recursion APIs. Share mathematical lemmas and certificate
interfaces as repetition becomes evident in the two first workflows.

A normalized signature is useful metadata; a universal generic raw term carrier
is a separate choice. Do not make the latter a prerequisite. Retain it as a
competitor in a bounded backend comparison if it materially reduces the proof
generator. No initial-chain construction or unification engine is required.

| Approach | Mathematical construction | Benefit | Main cost/risk | Proposed disposition |
| --- | --- | --- | --- | --- |
| Generic interpreted syntax | Indexed raw trees for a finite binding signature, generic alpha relation, quotient family and generic theorems | Shared proofs; systematic mutual signatures | Indexed recursion/transport, quotient constructor interfaces, larger proof before first client; generic signature correctness becomes central | Keep as an evaluated alternative; scratch raw staging is not a completed construction |
| Per-declaration generation | Emit ordinary raw inductives, alpha relation and quotient; generate proof terms for every contract | Closest to working lambda pattern; concrete names and diagnostics | Repeated theorem generation, metaprogram maintenance, risk of encoding mathematical reasoning in fragile tactics | Good first concrete backend; use shared theorem interfaces |
| Staged hybrid **recommended** | Per-declaration carriers plus reusable arity/abstraction/quotient/recursion/rule certificates; optionally exchange backend later | Early client evidence and reusable mathematics; small trusted boundary | Must prove adequacy of each emitted carrier and avoid certificates that merely restate the whole problem | Select only after reviewing contracts and first increment |

The generator is untrusted automation: generated definitions and proofs pass the
ordinary kernel. Certificates are checked Lean terms, not parser assertions or
trusted attributes. The public theorem contract should remain stable if the
internal carrier changes. An arbitrary equivalence of types is insufficient:
any backend comparison must commute with each constructor and the canonical
action, preserve the selected binder scopes, and transport the promised
computation/induction interfaces.

## Proposed signature and universe policy

Normalize constructor fields using this schematic grammar:

```text
S ::= unit | atom | data D | rec category | S × S | bind S
Declaration ::= a finite family of named categories and finite constructor lists
```

Here `bind S` is one atom abstracting **the entire value of S**; nesting it
expresses ordered nested single binders. Constructor alternatives provide sums.
`data D` is nonrecursive external data with a specified nominal action; it is
not silently given the discrete action. A binder enclosing `data D` binds the
atom in that value's nominal support, including when D is opaque to the generator.
`rec category` is a direct recursive
position. Atom positions are distinct from recursive positions and constant
labels. Language atoms, rule schematic variables, and Lean metavariables have
different roles and are never identified.

Scope examples: lambda has `bind (rec Term)`; let has
`rec Term × bind (rec Term)`; a shared residual binder can use
`bind (label-data × rec Process)`. The binder of let does not scope over its
defining term. Product inside versus outside `bind` changes the semantics.
Overlapping independent clauses for the same body are rejected. Shadowing and
vacuous single binders are allowed; distinctness is a fresh-presentation fact,
not part of the raw syntax definition.

**P:** finite mutual direct recursion is the target grammar. Bootstrap first
with one category, then acyclic multi-category declarations, and gate mutual
acceptance on a genuine cyclic test before advertising it. The positive raw
indexed probe only proves that its raw staging is accepted by Lean; generic
alpha equivalence and mutual fresh induction remain O.

No recursive function spaces, arbitrary nested containers, dependent syntax
indices, pattern/list/set binders, or multiple atom sorts enter the first
automatic grammar. A fixed finite arity can be expanded into products. A later
container registry would need proved action, support, mapping, relation and
predicate-lifting laws plus a kernel-accepted recursion construction. An
ordinary list used for judgment contexts is a smaller, separate library
dependency; it does not authorize `List (rec Term)` in syntax declarations.

Keep atoms, generated carriers, external nominal fields and semantic recursion
codomains in a common `Type u` initially, reflecting current `NameAbs`/FCB and
iterator restrictions. `Prop` remains `Sort 0` and can serve as the NFun codomain;
the probes check this distinction. Use `PUnit`/`PEmpty` or explicit lifting where
needed, not universe-zero `Unit`/`Empty` by accident. Avoidance-context universe
generalization can be added only with explicit tests. Atom type/action metadata
must be explicit internally despite the existing `outParam` convenience.

## Predicates, definitions and induction: complementary layers

1. **Ordinary quotient predicates:** clients write `P : T → Prop` and relation
   motives without support premises. Pullback to raw syntax is alpha-compatible;
   descent of a raw predicate requires invariance under the alpha relation.
2. **Certified supported predicates:** provide an explicit atom-indexed interface
   backed by NFun-to-Prop or an equivalent supported subset. Function/proposition
   extensionality gives ordinary extensional equality. The conjugation action is
   `(π • P) x = P (π⁻¹ • x)`. Fixed nominal parameters contribute support.
3. **Automation:** inspect elaborated expressions and local identities, use
   proved logical/operation laws to generate certificates, and expose unsolved
   obligations. It neither reads semantic proof contents nor infers support
   merely from the carrier types or occurrence of `Classical.choice`.

The proposed internal starting point is NFun-to-Prop with an explicit local
`letI` selecting the trivial truth-value action at a fixed atom type; a generic
`local instance {α}` declaration does not solve the registration failure.
Expose an atom-indexed predicate wrapper only if it
improves instance inference. Do not install a broad global `Nominal α Prop`
instance before coherence tests. Supported subsets offer a mathematically
equivalent view, not an escape from support obligations.

Finite Boolean operations and suitably jointly supported quantification retain
finite support; arbitrary external unions of supported predicates need not.
Some/Any needs certified support, often provided through a jointly equivariant
relation and a nominal context; users need not supply an exact least support.
The unsupported fresh-selector
counterexample rules out automatic nominal certification of arbitrary classical
choices. A uniquely characterized graph, as in current iteration, is different:
its symmetry and uniqueness can prove support after choice.

For genuinely dependent motives `M : T → Sort v`, quotient recursion needs
coherent transport. Lean supplies dependent quotient eliminators; mere
alpha-compatible maps between raw fibers are not the full coherence contract.
The package's first promised induction is Prop-valued; dependent elimination is
an explicitly separate research extension, not declared impossible.

## Generated contracts and component responsibilities

| Component | User supplies | Generated/checkable result | Failure or escape hatch |
| --- | --- | --- | --- |
| Datatype command | Categories, constructors, fields, binding scopes, external nominal types | Exact alpha quotient, distinctness/inversion, canonical action, support/free atoms, fresh representatives, arbitrary-motive fresh induction | Reject unsupported scope/recursion; show location and expected shape |
| Function command | Equations, nominal captures, declared structural recursion mode | Ordinary callable function plus certified NFun view; guarded binder equations, support upper bound, joint equivariance when justified, uniqueness | Named support, FCB/compatibility, coverage or termination goals; manual proofs permitted |
| Judgment command | Positive rules, ordinary Prop indices, bound/eigenvariable annotations, registered operations | Ordinary inductive relation, equivariance/support, fresh cases and rule induction when certified | Identify rule, side condition or premise that lacks transport/refreshability proof |
| Proof tools | Selected avoidance context, registered proved lemmas | Freshness selection/splitting, binder alignment, action/support rewriting | Explicit proof goals; no fallback to unproved certificates |

Exact contracts and proposed syntax are in the
[client note](2026-10-05-package-contracts.md). The following distinctions are
nonnegotiable acceptance conditions:

- **Iteration:** handlers receive recursive results. Preserve the existing
  computation, uniqueness and support-bound independence contracts.
- **Primitive recursion:** handlers additionally receive original children.
  A product construction with a reconstruction component is a candidate proof,
  not an already supplied recursor. In a binder case, the pair of child and
  result must be transported together and satisfy the appropriate FCB.
- **Dependent elimination:** separately specified family and coherence;
  neither of the first two automatically provides it.
- **Term versus rule induction:** rule induction retains premise derivations
  and context-generalized IHs. Term induction cannot supply this contract.
- **Support versus equivariance:** fixed substitution has support bounded by
  the fixed variable/replacement; joint equivariance permutes all parameters.
- **Equivariance versus FCB:** an equivariant handler can still leak its binder.
  Binder result freshness and representative independence need proofs.

FCB applies at the actual binding scope. In a let constructor, first lift the
scoped body and then combine it with the unscoped right-hand side. Requiring
the displayed binder fresh for the entire let result would reject valid terms
where it occurs freely in the right-hand side.

Function definitions should be ordinary public constants with named support
theorems and a discoverable supported view. An alternative is an NFun public
constant using the already good coercions. Compare both through ordinary
higher-order consumers, `rw`, `simp`, and `ext` before fixing generated naming.
Do not wrap every user-facing call in packaging operations.

For judgments, start with finite positive Horn rules and explicit nominal
parameters. Certify side-condition equivariance, premise transport and unchanged
conclusions when binders are refreshed. For a general semantic route, compare
the refreshability criterion in the [2025 source](2026-10-05-isabelle-comparison.md)
with per-rule proof generation. Neither all predicates being supported nor
freshness preservation of every relation is a sound universal assumption.
The existing reductions happen to have useful freshness-preservation theorems;
other judgments may need different local transport arguments.

## Decision register

Each row is a proposed decision unless marked U. These entries preserve the
alternatives and name the evidence that could change the recommendation.

| ID | Recommendation and alternatives | Rationale/evidence | Assumptions, dependencies and unresolved issues |
| --- | --- | --- | --- |
| AD-01 | Hybrid; alternatives generic universal carrier or entirely bespoke generation | Current lambda quotient is I; direct NameAbs recursion fails in S; Isabelle source supports staged generation | Prove shared certificate interfaces are useful; generic quotient still open |
| AD-02 | Arbitrary motives plus supported predicate layer; alternatives supported-only motives or interpreted logic | Current strong induction I; Pitts/Copello/Isabelle comparison L; Prop descent S | Choose scoped representation/instance policy; dependent coherence remains separate |
| AD-03 | Restricted grammar above; alternatives silently inherited Lean datatype grammar or broad container functors | Explicit scope and positive raw staging S; old atom-arity counterexample | Mutual alpha/fresh induction gate; universes kept narrow |
| AD-04 | Ordinary functions with certified views; alternative public NFun constants | Tutorial I demonstrates adapters and rewriting | Test definitional/coercion behavior and naming on real generated handlers |
| AD-05 | Rule certificates before automation; compare per-rule transport with semantic refreshability | ReductionInduction I; Nominal2 and 2025 criterion L | Generic sufficient theorem or generated proof must cover unrestricted beta and FOL eigenvariables |
| AD-06 | No unconditional supported abstraction map | S counterexample for constant atom output; existing FCB I | Provide equations only at binders fresh for function/parameters; composition laws need proofs |
| AD-07 | Five-study portfolio U, staged lambda/FOL then let/π/μ P | User selections; each adds a distinct stress test | Precise later semantics selected before their implementation increments |
| AD-08 | Notes plus claim ledger and evolving article | User research-method requirement U | Local manuscript only; no novelty, venue or publication claim |

## Dependency-ordered increments

The table below records the architectural proposal. Use the
[separate package roadmap](../nominal-package-roadmap.md) for ongoing tracking,
task checklists and the package work log.

These new PKG IDs refine existing M/A/P tasks without replacing or completing
them. **Only PKG-00 is a delivered research proposal. All implementation rows
are proposed/TODO and require agreement before execution.** Each implementation
increment gets its own reviewed spec and plan; this is not blanket authorization.

| ID / existing tasks | Dependency | Bounded output and proof obligations | Acceptance and verification |
| --- | --- | --- | --- |
| PKG-00 / A-01, P-01 | Completed tasks 1–9 | This evidence-based proposal, five-study portfolio, source/probe records | Review links, statuses and decisions; existing build/tutorial/audit; no package claim |
| PKG-01 / C-04, M-03 | Proposal/first increment agreement | Small predicate foundation: explicit truth action, supported-predicate/subset equivalence, raw/quotient Prop descent, basic logical support and Some/Any | Fixed-atom predicate; unsupported predicate/selector counterexamples; arbitrary-motive client unchanged; targeted/full builds and axiom audit |
| PKG-02 / A-01, A-02, P-01 | AD-01/03 review; may proceed independently of most PKG-01 lemmas | Manual one-category schema-to-carrier certificate; constructors, alpha equivalence, action and exact support; compare per-declaration vs generic cost | Lambda plus let scope shape and empty datatype; exact map laws, constructor commutation and negative grammar tests; no parser yet |
| PKG-03 / A-03, L interfaces | PKG-02 | Fresh cases/induction and supported iteration; total single-valued graph; guarded equations, uniqueness, support | Recover existing lambda reconstruction/substitution contracts without stronger assumptions; renamed/shadowed/nested binders |
| PKG-04 / A-04, P-01 | PKG-02/03 | Multi-category and direct mutual extension; focused finite-context List infrastructure | Term/Formula; synthetic genuine mutual cycle; support equations and generalized IHs; reject recursive containers until proved |
| PKG-05 / P-02, M-02/04 | PKG-03/04; required PKG-01 interface | Datatype/function command vertical slice; expression-aware captures; proof/diagnostic registries; primitive recursor or explicitly separate increment before claiming it | Generated lambda substitution and a function consuming original subterms; ordinary higher-order rewriting; rollback on failure; no placeholder declarations |
| PKG-06 / P-02/03, R-03 experience | PKG-03, PKG-01; certification may start before parser | Generic fresh rule theorem or per-rule generation; ordinary relation/equivariance and refreshability/transport contracts | Unrestricted beta/parallel plus FOL ∀-intro/∃-elim; counterexample rule that leaks binder rejected; arbitrary motives retained |
| PKG-07 / P-03 | PKG-05/06 | First complete workflow on generated lambda and FOL | All criteria below, complete local builds/examples, declaration-based audits and independent statement review |
| PKG-08 / P-03 extension | PKG-07 | Generated lambda with nonrecursive let; expansion, substitution compatibility and contextual reduction simulation | Binder scopes only over body; capture/shadowing/open examples; let expansion correctness to base lambda |
| PKG-09 / P-03 extension | PKG-07; residual scope certificate | Small monadic π fragment with input, output, restriction, parallel; choose transition convention | Transition equivariance and fresh bound-residual inversion, then one scoped behavioral congruence theorem after separate spec |
| PKG-10 / P-03 extension | PKG-07; positivity/semantic interface | Positive modal μ-calculus syntax and substitution, then semantics | Alpha-invariant semantics, monotonicity, substitution interpretation and μ/ν unfolding; arbitrary valuations not assumed supported |
| PKG-11 / D extension | Parallel with every row | Claim ledger, article sections, failed approaches and reproducible evidence | Every mathematical claim linked to Lean theorem or labeled source/proposal; no publication gate implied |

PKG-05 should split if primitive recursion or command elaboration requires more
than one reviewable change. First establish the mathematical recursor using a
real client; do not disguise an iterator with a new name. PKG-06 likewise splits
into a proved rule contract and its generator. General initiality is optional:
if claimed, define the map class, actual structure map, commuting algebra-morphism
law and uniqueness, and prove those statements for the emitted constructors.

## First complete workflow: precise completion criterion

**Generated lambda:** user declarations alone produce the public syntax theory,
substitution and beta/parallel judgments. Prove simultaneous parallel
substitution, diamond, beta/parallel closure correspondence, beta confluence,
convertibility-to-joinability and normal-form uniqueness for arbitrary open terms
with contextual reduction. The mathematical proof may follow the completed
client; no handwritten raw-alpha or fresh-rule derivation proof may be required
in that client. Prove a constructor-commuting equivariant equivalence to the
existing `Term α` and compare substitution/relations. Reusing the existing
Church–Rosser theorem by that equivalence alone does not count as replaying the
proof through generated interfaces. Keep the original modules intact.

**Generated first-order logic:** separate Term and Formula categories, nested
quantifiers, capture-avoiding term/formula substitution, finite contexts, and
ordinary natural-deduction judgments with eigenvariable rules. Prove
`Γ ⊢ φ → substContext x s Γ ⊢ substFormula x s φ` with the intended premises
and no hidden closedness assumption. Both universal introduction and existential
elimination must exercise fresh rule induction, with parameters generalized in
IHs. Include a substitution that forces renaming and a derivation whose
eigenvariable clashes with the replacement before refreshing. Syntax-only
examples or substitution composition alone do not meet this criterion.

**Shared usability:** proofs use constructors, application equations, inversion,
freshness and explicit avoidance. Include a primitive-recursion consumer, nested
shadowing, fixed nominal parameters, opaque unsupported operations and failed
grammar/certificate examples. Diagnostics identify the obligation and allow a
proof-backed escape hatch. The automatic grammar and the manual certified
extension route must be documented separately.

**Validation:** supported build plus explicit generated clients, no `sorryAx` or
custom axioms, representative `#print axioms` and broad module-origin audit,
import coverage, unchanged original clients, and theorem-statement review.
Record whether builds reuse dependencies or cached project artifacts. No CI,
executable fresh-name service, strong normalization, or publication is required.

## Bounded experiments and stop conditions

| Probe | Decisive question | Present evidence / next gate |
| --- | --- | --- |
| Predicate foundations | Can ordinary Prop descend, support logic, and coexist with arbitrary motives? | S files and exact results in predicate note; production instance choice remains open |
| Direct NameAbs recursion | Does Lean accept the apparent semantic recursive constructor? | S guarded failures isolate instance circularity and kernel occurrence checking; do not use this encoding |
| Raw staging and universes | Can direct mutual raw syntax and bundled arity interpretation elaborate? | S positive probes; alpha/induction/initiality deliberately not inferred |
| Supported abstraction mapping | Can `[a]x ↦ [a](f x)` be unconditional for supported f? | S negative counterexample; use fresh-binder conditions |
| First carrier certificate | Can actual constructors recover exact support and fresh induction? | PKG-02/03 future experiment; revise backend if transport/proof generation outweighs shared generic construction |
| Rule refreshing | Can unchanged conclusions and all premise IHs be retained for beta and FOL? | Existing lambda I, semantic source L; generic Lean theorem/generator O |
| Dependent motive | Which coherent families descend through quotients? | Small S checks do not justify unrestricted generated dependent recursion |
| Grammar diagnostics | Can rejected input leave no partial public package? | Future elaborator acceptance test, including negative recursion, overlapping scopes, undeclared captures and opaque functions |

Do not broaden syntax to repair a failed proof without recording the new grammar
and obligations. Do not weaken an induction/recursion statement to make generation
succeed. A failed probe is a research result to retain, not an invitation to
insert an axiom or merge the old branch.

## Proposed first implementation increment and author choices

**Recommendation for approval: PKG-01, a small predicate-foundations API.** Promote
only reviewed scratch statements for Prop descent, supported predicates, basic
logical operations and Some/Any; choose the explicit/scoped instance boundary;
add consumers and counterexamples. Keep arbitrary term/rule motives unchanged.
No syntax command, generic carrier or case-study replacement belongs to this
increment. Before coding, prepare its detailed implementation plan and obtain
the requested execution agreement.

Focused choices remaining:

1. Approve this predicate-first increment and the staged hybrid direction, or
   prefer the carrier-certificate experiment PKG-02 first?
2. For the first grammar, accept direct finite mutual recursion as a gated target
   with products/nested single binders and no arbitrary recursive containers?
3. For later π work, choose early versus late labeled semantics; for μ work,
   choose the positive modal μ-calculus versus a different intended variant.
   These choices do not block PKG-01 or the lambda/FOL work.

No permission to commit, push, publish, merge, or implement the package is
inferred from reviewing this research proposal.

## Verification record for this research turn

- Inspected branch, history, status and all requested existing documentation.
  The actual branch was already correct; no branch switch occurred.
- `lake build Nominal Instances Examples` passed, 1,033 jobs, largely cached;
  the default targets are Nominal and Instances, with Examples requested explicitly.
- Direct `lake env lean Examples/Tutorial.lean` passed without diagnostics.
- Direct `lake env lean Examples/AxiomAudit.lean` checked 1,859 project
  declarations, with only `propext`, `Classical.choice`, and `Quot.sound`.
- Research probe commands, axiom evidence and negative-test meanings are
  recorded in the two investigation notes. They remain outside supported imports.
- Final link, whitespace, preservation and probe rechecks are recorded in the
  research work log in the [package roadmap](../nominal-package-roadmap.md).

This was not a fresh project rebuild or clean dependency bootstrap. External
Isabelle/Rocq/Agda artifacts were not built. No production Lean source,
dependency, CI file or existing case-study theorem was changed.
