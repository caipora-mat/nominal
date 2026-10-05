# Propositions and induction in the nominal package

This research note separates the logical questions that affect the proposed
nominal package. The author wants a detailed comparison of Pitts, Isabelle,
Copello and the existing quotient-based Lean development before selecting an
architecture. The user-facing target is ordinary Lean propositions and judgments,
supported by nominal theory and dedicated commands.

Date: 2026-10-05. Historical baseline: `4279ba92efacd77b3b96e507631502272b489999` plus the
preserved working tree, on `fasapa/nominal-package`. This is an initial
investigation, not a complete foundations comparison. No package implementation
was changed. Isolated Lean experiments are identified separately below.

The current documentation revision, starting from
`7fed53a2e5fc67379f86f085515e310e7c1fddb7`, applies the
[architectural freedom policy](README.md#architectural-freedom). New
implementation belongs under top-level `Package/`; the existing `Nominal/`,
`Instances/` and probes remain reference material. Actions, support, `NFun`,
predicate machinery, `NameAbs`, quotients and induction can all be reused,
adapted or replaced, including implementations from scratch. Their present
APIs, classes, universes, seals, module structure and representations impose no
compatibility obligation. Mathematical correctness, theorem strength, ordinary
Lean `Prop` and the selected case studies remain the goals. Neither reuse nor a
rewrite is prescribed. This policy update does not change the experimental
baseline or establish results for any new representation.

## Distinctions that the architecture must preserve

| Concept | Meaning | What it does not establish |
| --- | --- | --- |
| A truth value `p : Prop` | A proposition, which can be given a trivial permutation action | That a predicate depending on atoms has empty support |
| A predicate `P : X → Prop` | A property of values of `X`; under conjugation with trivial truth-value action, `(π • P) x = P (π⁻¹ • x)` | That every such predicate is finitely supported |
| Alpha compatibility | A predicate on raw syntax is preserved by alpha equivalence | Equivariance under permutations of free atoms, or finite support |
| Finite support | Permutations fixing a finite atom set preserve the predicate | Empty support or invariance under all permutations |
| Equivariance | Invariance under simultaneous permutation of the relevant inputs | That fixing one input preserves equivariance |
| An arbitrary induction motive | A predicate supplied to an induction theorem | A nominal object that must itself have support |

For example, the predicate `fun x => x = a`, with `a` fixed, is supported but not
equivariant. Its truth value at one argument and the entire predicate function
are different objects. For a further mathematical test, parity on natural-number
atoms is not finitely supported under all finite permutations: outside any
candidate finite support, swap an even and an odd atom. These examples should
prevent a future API from conflating the rows of the table.

## Pitts and the nominal powerset

The relevant construction located in the local [Pitts book](../../ref/nominalsets.pdf)
is the nominal powerset `Pfs X`, Definition 2.26, section 2.5, printed pages 39–40.
Its elements are finitely supported subsets of `X`. The truth-value object in
the associated Boolean topos has trivial action, while predicates/subsets have
the action induced by their domain. Section 2.5 develops logical operations and
a finite-support principle with restrictions on quantified functions/subsets.

Section 3.2 supplies Some/Any and logical laws for the fresh quantifier. The
finite-support/equivariance assumptions matter: they cannot be dropped when
applying cofinite quantification to arbitrary predicates.

Section 8.6, Theorem 8.21 and Corollary 8.22, printed pages 148–150, uses finitely
supported predicates and predicate lifting through the signature to formulate
alpha-structural induction. This is a concrete generic construction to study.
It does not establish that every possible user induction motive must be encoded
as a finitely supported predicate in a different formalization.

Section 7.5, especially Remark 7.16, distinguishes internally finitely supported
fixed-point constructions from the ordinary external powerset treatment. This
matters for a future generic account of user-defined inductive judgments. A
nominal powerset is not automatically a complete lattice under every external
family of intersections or unions.

These are the precise located source constructions behind the investigation of
“nominal propositions.” A separate nominal formula datatype or object-logic proof
system has not been established as necessary for the package.

## What the Lean proposition restrictions do and do not say

Lean has proof irrelevance, restricted elimination from proofs into data, and
propositional extensionality. In particular, `propext` converts an equivalence
of propositions to their equality. These facts should be distinguished from
whether a metaprogram can inspect elaborated expressions.
[Lean reference on propositions](https://lean-lang.org/doc/reference/latest/The-Type-System/Propositions/).

A semantic predicate need not be analyzed as formula syntax to define its
permutation action: precompose it with inverse permutation of the argument.
Function and propositional extensionality then support reasoning about predicate
equality. The scratch experiment below confirms this route with the reference
library. It does not require the new package to retain `PFun` or the current
function instances: the conjugation/pointwise-action distinction must remain
explicit in whichever action design is chosen. No inspection of a proof's
runtime contents is involved.

Conversely, a metaprogram may inspect syntax/elaborated expressions to generate
proofs, but that does not establish finite support of arbitrary functions or
predicates. The generated certificate must justify the claim. A proposed formula
DSL, a reflected Lean expression, a semantic predicate and a proof of that
predicate are four distinct representations.

Ordinary quotient predicates respect equality automatically. Defining such a
predicate from a raw predicate still requires proving its invariance under the
quotient relation. Quotients move that obligation to the construction boundary;
they do not make an ill-defined raw property meaningful.
[Lean reference on quotients](https://lean-lang.org/doc/reference/latest/The-Type-System/Quotients/).

The author's experience that setoids were essential in the constructive Rocq
development should be analyzed under its exact equality, extensionality,
quotient and computational assumptions. It should not be restated as a general
impossibility theorem about Lean `Prop`. The inspected Rocq supported-function
representation uses pointwise setoid equality to avoid equating records that
contain different computational support witnesses. Its `alpha_ind` separately
requires alpha compatibility. These are related engineering/foundational choices,
but not a single consequence of restricted proof elimination.

## Copello and the quotient induction interface

Copello, Szasz and Tasistro's 2018 paper, section 4.2 and Figure 16, derives
generic induction for an alpha-compatible predicate `P : μ F → Set` and a finite
avoidance list. It does not require finite support or equivariance of `P`.
Figure 17 gives a related BVC proof principle. Here Agda `Set` permits type-valued
families; it must not be mechanically equated with Lean's proof-irrelevant `Prop`.
[Primary paper](https://arxiv.org/pdf/1807.01870).

The existing Lean `Term.strong_ind` and `Term.strong_ind_finset` in
`Instances/LambdaCalculus/Induction.lean` accept arbitrary predicates on quotient
terms. Alpha equivalence has become equality of their arguments, so clients
need no separate alpha-compatibility certificate. The proofs still establish
fresh induction by strengthening over permutations and contexts. They are
evidence for the promised strength of user-facing reasoning; their proof bodies,
theorem names and quotient implementation need not be retained by `Package/`.

Likewise, `Beta.strong_ind` and `Parallel.strong_ind` in
`Instances/LambdaCalculus/ReductionInduction.lean` accept arbitrary predicates
on endpoints and a nominal context. The **relation's** equivariance is used to
transport derivations; this is not a requirement that the user's motive be
equivariant. Avoidance contexts are not asserted to be the motive's support.

Alpha-compatible raw predicates and quotient predicates therefore offer a
promising bridge to study if that construction route is selected. The later
[predicate investigation](2026-10-05-predicate-foundations.md) proves a
`Prop`-valued descent/pullback correspondence in the reference setting. Adapt or
reprove the relevant correspondence for a different representation. For
type-valued dependent motives, investigate transport and coherence separately;
do not claim that the same simple argument settles all dependent elimination,
or that dependent quotient elimination is universally impossible.

## Isabelle treats predicate permutations and logic explicitly

Nominal2 gives Boolean truth values trivial permutation action and functions a
conjugation action. Its theory includes logical-operator equivariance, quantified
predicates, set comprehension, and permutation-simplification infrastructure.
Thus absence of a separately named nominal-proposition wrapper would not mean
absence of a theory of predicates. The comparison should examine what is proved
and automated, not only type names.
[Nominal2 theory document, sections 4–6](https://www.isa-afp.org/browser_info/current/AFP/Nominal2/document.pdf).

The original Nominal manual, section 4.2, equation (4.2), also presents strong
induction with context-generalized hypotheses and binder freshness for the
selected context, without a finite-support premise on the user predicate. Its
section 4.5 treats fresh rule induction separately.
[Original Nominal manual](https://isabelle.in.tum.de/nominal/manual/nominal_datatype_manual.pdf).

Original Isabelle Nominal and Nominal2 must be distinguished in the full
comparison. Isabelle and Agda were not built here. The exact Copello statements
above were checked in the 2018 paper; full-text retrieval of the earlier 2016
paper was unsuccessful, so no exact 2016 theorem correspondence is claimed.
Web sources were accessed on 2026-10-05. The later
[predicate](2026-10-05-predicate-foundations.md) and
[Isabelle](2026-10-05-isabelle-comparison.md) notes record the subsequently
obtained 2016 paper and more precise Isabelle versions. The retrieval failure
above records this initial investigation's scope; use the pinned later evidence
before relying on the comparison in a publication.

## Checked Lean experiments

An isolated file `/tmp/NominalPredicateResearch.lean` was compiled by both the
investigator and the coordinating reviewer using:

```sh
lake env lean /tmp/NominalPredicateResearch.lean
```

It exited successfully. There were style suggestions concerning local instances;
there were no admissions. Printed dependencies for its named results were only
`propext`, `Classical.choice`, and `Quot.sound`. This was a direct scratch-file
check against built imports at the historical baseline, not a new full-library
build or integrated API. Neither this scratch result nor a reference-library
build validates new `Package/` code.

The experiment established:

- A local `Nominal α Prop` with trivial action and empty support.
- Predicate permutation by inverse precomposition via `PFun α X Prop`.
- Equivalence of existing logical `EquivariantPred` and function equivariance
  under that truth-value action, using `propext`.
- A supported equality predicate with a fixed atom parameter, using
  `NFun.fromParam`, and a proof that it need not be equivariant.
- Alpha-respectfulness of any predicate already defined on quotient lambda terms.
- Some/Any for `P : NFun α α Prop`, derived from the existing relational theorem
  via equivariant evaluation.
- Nonexistence of a finitely supported function selecting an atom outside every
  finite input set.

The core of the supported-predicate experiment was:

```lean
@[instance_reducible] def propNominal {α : Type u} [Name α] : Nominal α Prop where
  smul _ P := P
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  finSupp _ := ⟨∅, fun _ _ => rfl⟩

-- With letI : Nominal α Prop := propNominal:
--   NFun α X Prop packages a supported predicate.
--   (π • (PFun.mk P : PFun α X Prop)) x = P (π⁻¹ • x).
```

This is evidence about the tested interface, not a recommendation to install a
global instance. Its atom `outParam` makes instance inference for a carrier such
as `Prop` an API question; the probe used an explicit local instance. Compare
explicit actions or parameters, redesigned classes, wrappers, supported subsets
and alternative supported-function representations. The registration failure
checked in the later predicate note concerns the old interface and does not
rule out a differently designed `Prop` interface. Scoped instances alone are
not evidence of a solution. Each candidate needs its own coherence and usability
checks; the choices are not limited to adapters around `NFun`.

## Classical choice needs its own support argument

Using classical choice in the Lean metatheory does not make every chosen
function nominal. Pitts section 2.7, Theorem 2.29, gives a relevant failure of
internal choice. The following smaller counterexample passed against the
reference library:

```lean
theorem no_supported_fresh_selector {α : Type u} [Name α]
    (f : NFun α (Finset α) α) (hf : ∀ s, f s ∉ s) : False := by
  have h := NFun.supp_apply_le f (supp f)
  rw [supp_atom, supp_finset, Finset.union_self] at h
  exact hf (supp f) (h (Finset.mem_singleton_self _))
```

Classical Lean can choose a fresh atom for each finite set, but no function doing
so at all inputs satisfies this finite-support contract. In contrast, a
choice-defined operation can be shown equivariant/supported when its relation
and uniqueness properties justify that conclusion. The existing lambda iterator
is a useful source of that proof pattern.

## Research hypotheses and required next evidence

The semantic working hypothesis is a layered design: alpha-equated syntax at the
public boundary, arbitrary-predicate fresh induction for clients, and a reusable
supported-predicate theory for logical operations, Some/Any, definition support
and automation. Alpha-compatible predicates may remain useful internally when
constructing or comparing quotients. This is a hypothesis, not an accepted
implementation architecture or a theorem that all layers can be generated for
every signature. In particular, it does not select the existing action, support,
function, abstraction or quotient implementations.

Assign the following evidence obligations to the relevant architecture and
implementation stages, with foundation decisions before the dependent work:

1. Exact source/theorem correspondence for Pitts, Copello, Rocq, original Isabelle
   Nominal, Nominal2 and the current Lean principles, including their assumptions.
2. A Lean comparison of candidate action/support and predicate interfaces,
   including NFun-to-Prop and supported subsets as reference choices, with
   action/equality, universes, inference and useful logical laws tested under
   the selected foundations. Reuse, adaptation and replacement are all open.
3. For a quotient-based route, a proof of the raw-alpha-compatible/quotient-predicate
   bridge for the intended generic signature, with a separate analysis of dependent
   motives; another representation needs its corresponding well-definedness laws.
4. Explicit criteria for generating relation equivariance and fresh rule induction.
   Successful term induction does not alone establish these criteria.
5. Tests with fixed parameters, arbitrary motives, unsupported predicates and
   choice-defined functions. Negative results must delimit automation honestly.
6. A user-facing account of failed automatic obligations and expert escape hatches.
7. A statement of which predicate facilities are required for the first workflow,
   and which enrich the theory without becoming prerequisites for that workflow.
   The [package roadmap](../nominal-package-roadmap.md) places PKG-F01–PKG-F05
   before bounded PKG-01: select foundation contracts, establish `Package/`
   build/audit coverage, provide the chosen atom/action and support/freshness
   foundations, and provide only the function/predicate-input machinery that
   the selected predicate representation needs. This is not an instruction to
   reconstruct the full existing core or `NFun` catalogue before PKG-01.
8. Validation for the new declarations in `Package/`, including client proofs and
   an axiom audit, rather than counting old builds or probes as certification.
   This documentation-only revision creates no package modules or build targets.

The [research brief](2026-10-05-nominal-package-brief.md) records the requirements
that motivated this investigation. No conclusion here reintroduces a constructive
restriction that the author has explicitly waived for the Lean project.
