# Nominal package: architecture and research roadmap proposal

Date: 2026-10-05. **For review; architecture and implementation are not approved.**
Branch: `fasapa/nominal-package`; original evidence baseline:
`4279ba92efacd77b3b96e507631502272b489999`.

Revised under the author's settled [architectural freedom](README.md#architectural-freedom)
and [Package location](README.md#implementation-location) decisions. All needed
infrastructure may be newly authored under top-level `Package/`. The existing
core is evidence and an optional dependency; its APIs and implementation choices
do not constrain the new design. The current revision started at `7fed53a`.

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
Successful probes under `docs/research/probes/` are S, never I. The initial notes
and five probes were later included in `7fed53a`; this revision updates their
design implications without changing the proofs. Earlier evidence remains
reference evidence, not certification of a future Package implementation.

## Decisions made in this discussion

- **U:** preserve the completed core and Church–Rosser client as reference material, classical Lean,
  actual quotients, least support, ordinary `Prop`, one atom sort, single/nested
  binders, multiple syntax categories, dedicated commands, and no CI/deadline.
- **U:** lambda calculus remains a required case study, including Church–Rosser.
- **U:** first-order logic with substitution admissibility is the second workflow.
- **U:** the case-study portfolio also includes lambda calculus with `let`,
  π-calculus and μ-calculus. The author selected `let` over imperative locals.
- **U:** reuse, adaptation and from-scratch implementation are all allowed for
  every layer; old APIs, instances, universes, seals and proof techniques are
  optional design choices. Backward compatibility is not required.
- **U:** all new implementation belongs in top-level `Package/`, outside
  `Nominal/`. Foundation prerequisites are explicit tasks before PKG-01.
- **P:** finish the first complete generated workflow with lambda and first-order
  logic, then add the other three as explicit portfolio milestones. This staging
  does not remove any selected case study from the research program.
- **O:** exact command spelling, the complete μ-calculus variant, π transition
  convention, and approval of the first implementation increment remain open.

The optional interpreted nominal formula logic discussed earlier is not a
requirement. First-order and μ-calculus formulas are **object-language case-study
syntax**; they do not replace Lean `Prop` as the package's proposition language.

## Recommendation: a staged hybrid with a narrow public boundary

One candidate uses a normalized binding schema, a shared proved nominal core, and
proof-producing per-declaration generation. Initially generate ordinary raw
recursive syntax and its alpha quotient for each declaration. Keep raw carriers
and relation witnesses behind generated constructors, equations, inversion,
support, induction and recursion APIs. Share mathematical lemmas and certificate
interfaces as repetition becomes evident in the two first workflows.

That shared core can be entirely new. Compare the candidate with other designs
on their proof obligations and user experience, without giving the existing
implementation automatic preference. `Package/` may choose different action,
support, function and abstraction interfaces; any reuse is a documented decision.

A normalized signature is useful metadata; a universal generic raw term carrier
is a separate choice. Do not make the latter a prerequisite. Retain it as a
competitor in a bounded backend comparison if it materially reduces the proof
generator. No initial-chain construction or unification engine is required.

| Approach | Mathematical construction | Benefit | Main cost/risk | Proposed disposition |
| --- | --- | --- | --- | --- |
| Generic interpreted syntax | Indexed raw trees for a finite binding signature, generic alpha relation, quotient family and generic theorems | Shared proofs; systematic mutual signatures | Indexed recursion/transport, quotient constructor interfaces, larger proof before first client; generic signature correctness becomes central | Keep as an evaluated alternative; scratch raw staging is not a completed construction |
| Per-declaration generation | Emit ordinary raw inductives, alpha relation and quotient; generate proof terms for every contract | Concrete names and diagnostics; reference lambda pattern supplies evidence | Repeated theorem generation, metaprogram maintenance, risk of encoding mathematical reasoning in fragile tactics | Evaluate a concrete backend with newly designed or adopted theorem interfaces |
| Staged hybrid **candidate recommendation** | Per-declaration carriers plus shared arity/abstraction/quotient/recursion/rule certificates, possibly all newly authored | Early client evidence and shared mathematics; small trusted boundary | Must prove adequacy of each emitted carrier and avoid certificates that merely restate the whole problem | Reassess after foundation contracts; no inherited-core or compatibility requirement |

The generator is untrusted automation: generated definitions and proofs pass the
ordinary kernel. Certificates are checked Lean terms, not parser assertions or
trusted attributes. Agree public mathematical contracts for the new package
and revise them explicitly when research warrants it; this does not freeze the
reference API. If a backend correspondence is claimed, an arbitrary equivalence
of types is insufficient: the claimed correspondence must commute with the
relevant constructors and canonical
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

Specify universes in the new foundation contract. The reference NameAbs/FCB and
iterator have common-universe restrictions; these are not limits imposed on
`Package/`. A common-universe first construction is one bounded option, while
independent atom/carrier/result universes are another to test. `Prop` is `Sort 0`
and the old NFun probes accept it as a codomain; a new representation needs its
own check. Choose universe-correct units/empty types and explicit lifts where
needed. Review atom inference directly rather than inheriting `outParam`.

## Predicates, definitions and induction: complementary layers

1. **Ordinary quotient predicates:** clients write `P : T → Prop` and relation
   motives without support premises. Pullback to raw syntax is alpha-compatible;
   descent of a raw predicate requires invariance under the alpha relation.
2. **Certified supported predicates:** provide an explicit atom-indexed interface
   backed by an adopted NFun-to-Prop interface, a new supported-function design,
   supported subsets, or a direct predicate structure. Function/proposition
   extensionality gives ordinary extensional equality. The conjugation action is
   `(π • P) x = P (π⁻¹ • x)`. Fixed nominal parameters contribute support.
3. **Automation:** inspect elaborated expressions and local identities, use
   proved logical/operation laws to generate certificates, and expose unsolved
   obligations. It neither reads semantic proof contents nor infers support
   merely from the carrier types or occurrence of `Classical.choice`.

NFun-to-Prop with fixed-atom `letI` is a checked reference option, not the selected
foundation. Its generic `local instance {α}` registration fails in the tested
old typeclass design; this is not a universal limitation on a new design.
Compare explicit structures, different class parameters, atom-indexed wrappers
and supported subsets using ordinary-use clients. Coherence, extensionality and
support laws must be proved for whichever interface is chosen. No wrapper name
or existing instance arrangement is mandatory.

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
| Datatype command | Categories, constructors, fields, binding scopes, external nominal types | Alpha equality matching the specified binding semantics, distinctness/inversion, canonical action, support/free atoms, fresh representatives, arbitrary-motive fresh induction | Reject unsupported scope/recursion; show location and expected shape |
| Function command | Equations, nominal captures, declared structural recursion mode | Ordinary callable function plus certified supported view; guarded binder equations, support upper bound, joint equivariance when justified, uniqueness | Named support, binder-compatibility, coverage or termination goals; manual proofs permitted |
| Judgment command | Positive rules, ordinary Prop indices, bound/eigenvariable annotations, registered operations | Ordinary inductive relation, equivariance/support, fresh cases and rule induction when certified | Identify rule, side condition or premise that lacks transport/refreshability proof |
| Proof tools | Selected avoidance context, registered proved lemmas | Freshness selection/splitting, binder alignment, action/support rewriting | Explicit proof goals; no fallback to unproved certificates |

Exact contracts and proposed syntax are in the
[client note](2026-10-05-package-contracts.md). The following distinctions are
nonnegotiable acceptance conditions:

- **Iteration:** handlers receive recursive results. Prove computation,
  uniqueness and support-bound independence with the intended mathematical
  strength; old theorem names and handler packaging are not required.
- **Primitive recursion:** handlers additionally receive original children.
  A product construction with a reconstruction component is a candidate proof,
  not an already supplied recursor. In a binder case, the pair of child and
  result must be transported together with a proved binder-descent condition;
  the reference FCB interface is one possible method.
- **Dependent elimination:** separately specified family and coherence;
  neither of the first two automatically provides it.
- **Term versus rule induction:** rule induction retains premise derivations
  and context-generalized IHs. Term induction cannot supply this contract.
- **Support versus equivariance:** fixed substitution has support bounded by
  the fixed variable/replacement; joint equivariance permutes all parameters.
- **Equivariance versus FCB:** an equivariant handler can still leak its binder.
  Binder result freshness and representative independence need proofs.

Any FCB-style proof applies at the actual binding scope. In a let constructor, a
possible construction first lifts the
scoped body and then combine it with the unscoped right-hand side. Requiring
the displayed binder fresh for the entire let result would reject valid terms
where it occurs freely in the right-hand side.

Function definitions should be ordinary public constants with named support
theorems and a discoverable supported view. An alternative is a bundled public
constant; the reference NFun coercions are useful evidence for that option.
Compare candidate interfaces through ordinary
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
| AD-01 | Hybrid candidate; alternatives generic universal carrier or entirely bespoke generation, each with freely designed foundations | Reference lambda quotient is I; tested direct NameAbs recursion fails in S; Isabelle source supports staged generation | Reassess after new foundation contracts; shared core need not be the old library |
| AD-02 | Arbitrary motives plus supported predicate layer; alternatives supported-only motives or interpreted logic | Current strong induction I; Pitts/Copello/Isabelle comparison L; Prop descent S | Choose scoped representation/instance policy; dependent coherence remains separate |
| AD-03 | Restricted grammar above; alternatives broader proved grammar or container functors | Explicit scope and positive raw staging S; old atom-arity counterexample | Mutual alpha/fresh induction gate; new universe policy requires its own evidence |
| AD-04 | Ordinary functions with certified views; alternative bundled function constants | Reference tutorial I demonstrates adapters and rewriting | Choose new/adopted packaging by client tests, without an old NFun compatibility mandate |
| AD-05 | Rule certificates before automation; compare per-rule transport with semantic refreshability | ReductionInduction I; Nominal2 and 2025 criterion L | Generic sufficient theorem or generated proof must cover unrestricted beta and FOL eigenvariables |
| AD-06 | No unconditional supported abstraction map | S counterexample for constant atom output; existing FCB I | Provide equations only at binders fresh for function/parameters; composition laws need proofs |
| AD-07 | Five-study portfolio U, staged lambda/FOL then let/π/μ P | User selections; each adds a distinct stress test | Precise later semantics selected before their implementation increments |
| AD-08 | Notes plus claim ledger and evolving article | User research-method requirement U | Local manuscript only; no novelty, venue or publication claim |
| AD-09 | Architectural freedom U: reuse, adapt or rebuild any layer | User clarified that existing infrastructure is learning material | Preserve reference source and mathematical goals; certify new implementations independently |
| AD-10 | Top-level Package location U and explicit foundation prerequisites | User selected Package outside Nominal and requested a full roadmap revision | Plan Package targets/imports/audits and missing foundations before PKG-01 |

## Dependency-ordered increments

The [separate package roadmap](../nominal-package-roadmap.md) now owns the full
order, acceptance criteria and work log. Its prerequisite chain explicitly
avoids assuming that the reference core is the new foundation:

1. **PKG-F01:** inspect the pinned algebraic sketch's actual source, recheck its
   assessment and identify useful ideas, false statements and unresolved proof
   obligations. Use that evidence to decide foundation contracts and per-layer
   reuse/adapt/rebuild choices, universes, action coherence and validation.
2. **PKG-F02:** establish the Package module, build, import and axiom-audit boundary.
3. **PKG-F03:** establish the selected atom, permutation and action foundations.
4. **PKG-F04:** prove the required support, freshness and quotient interfaces.
5. **PKG-F05:** establish the minimal function/predicate-input interface needed by
   the selected predicate representation; a full old-NFun replacement is not
   automatically required.
6. **PKG-01:** build predicate foundations against those checked interfaces.

The additional **PKG-F06** binder/abstraction-descent task provides foundations
for **PKG-03** induction and iteration. It may be developed alongside predicates
when dependencies allow. **PKG-02** builds the actual syntax-carrier contract;
**PKG-04** extends categories; **PKG-05/06** produce definition and judgment
facilities; **PKG-07** validates the complete lambda/FOL workflow. **PKG-08–10**
cover let, pi and mu, while **PKG-11** maintains the article/evidence record.

Existing PKG IDs retain their meaning; foundation tasks are new prerequisites,
not claims of completed work. Reusing a layer may discharge a task after its
contracts, dependencies and Package consumers are checked. Independent proofs
are also allowed. Do not mark a prerequisite done merely because a corresponding
old declaration exists. This replaces the initial proposal's assumption that
PKG-01 could directly promote scratch lemmas on the existing core.

Split mathematical contracts and command generation into manageable reviewed
increments. Initiality remains optional: if claimed, state the map class,
actual structure map, commuting law and uniqueness for the emitted constructors.
No foundational choice is approved by the existence of this proposal.

## First complete workflow: precise completion criterion

**Generated lambda:** user declarations alone produce the public syntax theory,
substitution and beta/parallel judgments. Prove simultaneous parallel
substitution, diamond, beta/parallel closure correspondence, beta confluence,
convertibility-to-joinability and normal-form uniqueness for arbitrary open terms
with contextual reduction. The mathematical proof may follow the completed
client; no handwritten raw-alpha or fresh-rule derivation proof may be required
in that client. Establish the intended language and theorem semantics through
its generated contracts. An equivalence with reference `Term α` is an optional
comparison technique; if used, prove the advertised constructor/action/relation
laws. Old-API compatibility and such an equivalence are not mandatory. Merely
transporting the existing Church–Rosser theorem does not count as replaying a
proof through generated interfaces. Keep the reference modules intact.

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

**Validation:** explicit Package build and generated clients, no `sorryAx` or
custom axioms, representative `#print axioms` and a module-origin audit covering
new Package declarations, import coverage, and theorem-statement review. Check
reference preservation separately. A successful old library build does not
validate new Package modules or require the two designs to share their instances.
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

## Next foundation decision and PKG-01 readiness

Begin with **PKG-F01**, including direct inspection of `Algebraic.lean` and
`Structural.lean` at `983adeb9b80f75fb7c77c05acfd2fcef16db1d46`, as specified in
the [roadmap](../nominal-package-roadmap.md#pkg-f01--algebraic-sketch-investigation-and-foundation-contract).
Record which ideas to adopt, adapt, rederive, defer or reject; the existing
assessment is evidence to verify, not a substitute for reading the source.
Review the new Package foundation and its dependency map. Complete or explicitly
discharge the F02–F05 prerequisites before treating
PKG-01 as ready. The first design session should identify what is missing and
propose a bounded next increment; it need not build the entire nominal library.

For PKG-01, compare predicate representations using mathematical contracts and
ordinary-use examples. Reimplement as much supporting infrastructure as is
justified, with those dependencies recorded under the foundation tasks. Retain
ordinary Prop, arbitrary-motive reasoning and honest support bounds. A reviewed
scratch statement can guide a new proof; it need not dictate the implementation.

Focused choices remaining:

1. Which foundational interfaces and reuse/adapt/rebuild choices best serve the
   predicate task and later clients? Review the concrete next spec and plan.
2. Which candidate backend and universe policy meets the agreed mathematical
   grammar and interface requirements with manageable proof obligations?
3. For later pi work, choose transition semantics; for mu work, choose the
   intended variant. These choices need not delay predicate-foundation design.

Architectural freedom and the Package location are settled user decisions, not
questions to ask again. No permission to commit, push, publish or merge is
inferred from this research. Production implementation follows agreement on its
concrete scope and plan.

## Verification record for the original investigation

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


## Policy revision verification boundary

This revision changes documentation and sequencing at the author's request.
The historical build/probe evidence above was not rerun or extended. Existing
production source and all scratch Lean files, including two newly observed
untracked predicate probes, remain unchanged. Package build/audit setup and new
proofs are future roadmap work.
