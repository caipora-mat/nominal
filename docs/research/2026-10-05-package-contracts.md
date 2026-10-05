# Client contracts for the proposed nominal package

Date: 2026-10-05. Source baseline: `4279ba92efacd77b3b96e507631502272b489999`
on `fasapa/nominal-package`, including the preserved working-tree documentation.
This note records source inspection and proposed contracts. It adds no commands,
generated declarations, recursors, judgment packages, or new proved mathematics
to the library. All command examples below are **non-compiling design sketches**.
Their spelling is illustrative; their mathematical obligations are the subject
of the proposal.

Read this with the [research brief](2026-10-05-nominal-package-brief.md),
[propositions investigation](2026-10-05-propositions-and-induction.md),
[tutorial](../tutorial.md), and [release assessment](../release-assessment.md).
The relevant existing roadmap tasks are L-01–L-03, R-01–R-07, A-01–A-03,
P-01–P-03, and M-02–M-04. A source inventory here does not change their statuses
or make the package implementation complete.

The user selected first-order logic with substitution admissibility as a second
case study, and subsequently selected a five-example portfolio: lambda calculus,
first-order logic, lambda calculus extended with let, π-calculus, and μ-calculus.
The let example has subsequently been selected for local binding, with
`let x := t in u` binding only occurrences in `u`, and let-expansion correctness
as its target. Lambda plus first-order logic is the proposed first complete
workflow. The later examples' precise semantic contracts remain to be specified;
the portfolio is not evidence that all their requirements fit the first
implementation increment.

## 1. What the completed lambda client actually requires

The current development already proves Church–Rosser for arbitrary open quotient
terms and full contextual beta reduction. Its successful client boundary should
be reproduced by a generator before replacing any manual construction. The
[2026-10-02 review](../reviews/2026-10-02-development-review.md) describes an
earlier snapshot: its claims that integration, reduction, fresh rule induction,
or Church–Rosser are absent are historical. Its distinctions between iteration,
primitive recursion, and fresh rule induction remain relevant.

| Source and declarations | Observed contract | Consequence for generated interfaces |
| --- | --- | --- |
| [Basic.lean](../../Instances/LambdaCalculus/Basic.lean): `Term`, `var`, `app`, `lam`, `var_inj`, `app_inj`, `lam_inj`, constructor disjointness | Alpha equality is ordinary quotient equality. Same-binder lambda injectivity is available; equality of different binders uses abstraction equality. | Export ordinary constructors, injectivity/disjointness, and binder-aware equality. Do not expose a false pair-style injectivity law for binders. |
| Basic: `supp_eq_fv`, `supp_term_var`, `supp_term_app`, `supp_term_lam`, `fresh_term_lam` | Supports are exact free-variable sets; abstraction removes its binder. In particular `a # lam a t` even when `a` occurs freely in `t`. | Give useful support/freshness equations for the canonical action. Distinguish freshness for an abstraction from freshness for its body. |
| Basic: `term_lam_eq_iff`, `lam_eq_swap`, `lam_eq_iff_at_fresh`, `exists_lam_eq_at_fresh`, `lam_eq_iff_common_fresh` | Quotient constructors connect to `NameAbs`; a chosen fresh binder has a unique body; two abstractions can be aligned at one binder. | Reuse abstraction theory and expose chosen/common-binder views. Clients should not unfold raw alpha equivalence. |
| [Induction.lean](../../Instances/LambdaCalculus/Induction.lean): `strong_ind`, `strong_ind_finset` | An arbitrary motive `P : Term α → Z → Prop`, a nominal context `Z`, and hypotheses at every recursive context; lambda binders avoid the chosen context. | Preserve arbitrary predicates and context-generalized induction hypotheses. An avoidance context is not a support certificate for the motive. |
| [Recursion.lean](../../Instances/LambdaCalculus/Recursion.lean): `recNoContext`, `recNoContextNFun` | Supported **iteration** through three handlers, with common finite support bound and guarded fresh-result condition for the binder handler. | Do not relabel the existing iterator as primitive recursion or dependent elimination. Hide proof packaging only when it can be justified. |
| Recursion: constructor equations, `recNoContext_unique`, `recNoContext_independent`, `recNoContext_supports`, `supp_recNoContextNFun_le` | Public equations, functional uniqueness, independence of a valid avoidance bound, and support of the returned function. | Generate theorem-level equations and uniqueness/support contracts, not only a function and an opaque graph. |
| [Substitution.lean](../../Instances/LambdaCalculus/Substitution.lean): `subst`, `subst_var`, `subst_app`, `subst_lam`, `subst_lam_rename` | Fixed parameters produce a supported operation; the lambda equation needs freshness for the variable and replacement. | Capture parameters explicitly, infer a support upper bound, and expose guarded computation plus renaming. |
| Substitution: `subst_equivariant`, `subst_subst`, `supp_subst_le`, `subst_rename`, `subst_eq_of_lam_eq` | Joint equivariance, substitution composition with its actual hypotheses, a support upper bound, and contraction independence from the chosen binder. | Joint action laws and binder-transport laws are distinct contracts; neither is implied merely by constructing a quotient datatype. |
| [Beta.lean](../../Instances/LambdaCalculus/Beta.lean) and [Parallel.lean](../../Instances/LambdaCalculus/Parallel.lean): inductive relations, `equivariant`, `supp_le`, `fresh`, inversion | Ordinary Lean `Prop` relations on quotient endpoints; all reduction rules are unrestricted. Parallel contraction has two recursive premises. | Preserve the specified relation. Fresh induction must not silently redefine it by adding freshness premises to its constructors. |
| [ReductionInduction.lean](../../Instances/LambdaCalculus/ReductionInduction.lean): `Beta.strong_ind`, `Parallel.strong_ind` and finite-set variants | Arbitrary endpoint motives; each recursive premise retains both its derivation and an IH at every context. The contraction binder avoids the context and argument endpoints. | Generate fresh **derivation** induction separately from term induction. Keep all premises and all IHs. |
| [ReductionInversion.lean](../../Instances/LambdaCalculus/ReductionInversion.lean): `lam_iff_at_fresh`, `lam_iff_same`, `lam_lam_iff`, `lam_iff_common_fresh`, `app_iff_at_fresh`, context-fresh forms | Inversion aligns binders; parallel application inversion retains both congruence and contraction branches, which may overlap. | Provide usable rule inversion, not only an induction theorem. Do not conflate overlapping rule alternatives. |
| [ParallelSubstitution.lean](../../Instances/LambdaCalculus/ParallelSubstitution.lean): `Parallel.subst`, `subst_left`, `subst_right` | Both subject and replacement may reduce: `t ⇉ t' → s ⇉ s' → t[x := s] ⇉ t'[x := s']`. | A generated replay must consume both contraction IHs and preserve open terms and arbitrary substitution variables. |
| [ParallelDiamond.lean](../../Instances/LambdaCalculus/ParallelDiamond.lean): `Parallel.diamond` | Direct diamond from fresh rule induction, inversion, and simultaneous substitution. The competing target is the induction context. | A general syntax-inspecting complete-development function is not a dependency discovered by this proof. |
| [ReductionClosure.lean](../../Instances/LambdaCalculus/ReductionClosure.lean) and [ChurchRosser.lean](../../Instances/LambdaCalculus/ChurchRosser.lean) | `BetaStar`, `BetaEq`, reduction inclusions, closure equality, confluence, Church–Rosser, and normal-form uniqueness reuse Mathlib relation infrastructure. | Generated judgment machinery should interoperate with ordinary relation APIs; it need not generate a new closure theory. |

The [compiling tutorial](../../Examples/Tutorial.lean) provides particularly
useful acceptance tests: `nestedAlpha` permits shadowing, `replaceVariable` keeps
noncomputable support evidence inside a proof field, `substituteSupport` exposes
the fixed-parameter bound, `rebuildUnique` uses ordinary function equality,
`renameToAvoidCapture` demonstrates actual capture avoidance, and
`parallelPreservesFreshWhen` captures an arbitrary `q : α → Prop` without a
support premise. `substituteRelatedInputs` and `diamondForDuplication` exercise
the reductions rather than merely invoking tactics in a proof of `True`.

The client has one atom sort; `Name α` requires infinitude and decidable equality,
not countability. Current term induction and iteration use the atom universe for
their context/result; fresh rule induction permits a separate context universe.
A package proposal must choose and document its universes rather than silently
claiming unrestricted ones.

## 2. Four principles that must remain separate

**Term induction into `Prop`.** The existing `Term.strong_ind` proves arbitrary
`P : Term α → Z → Prop` from constructor cases. The lambda case receives
`a # z` and `∀ d, P t d`. It does not require a nominal action on `P`. The
quotient makes alpha-compatible argument replacement ordinary equality; the
freshness theorem still needs its own proof. A nested use can instantiate an IH
at a context extended by the enclosing binder.

**Supported iteration.** Write the handlers as
`fᵥ : NFun α α Y`, `fₐ : NFun α (Y × Y) Y`, and
`fL : NFun α (α × Y) Y`. The current theorem requires all three supports to
lie in `A`, together with `∀ a y, a # A → a # fL (a,y)`.
The last condition ranges over every `y`, not only reachable recursive results.
The result satisfies the variable/application equations and the lambda equation
when `a # A`. The existing construction proves graph totality and uniqueness
before extracting a function by classical choice. Its support lies in `A`;
a nonempty bound does not prove equivariance. The uniqueness theorem even
accepts an ordinary candidate function, without first assuming that candidate
is supported.

**Primitive recursion.** A primitive handler receives the original child and
the value computed for that child. For lambda syntax, proposed handler inputs
are `(t, rₜ, u, rᵤ)` at application and `(a, t, rₜ)` at abstraction. An iterator
into `Term × Y`, with a proof that its first projection reconstructs the input,
is a candidate derivation; a dedicated relational graph is another. Neither
route has been delivered as a public primitive-recursion interface. Support,
binder compatibility, constructor equations, and uniqueness must be proved for
the actual route. A weakened FCB premise applying only to reachable pairs would
be a new theorem, not an undocumented use of the current iterator.

**Dependent elimination.** A data-valued family `C : Term α → Type v` adds
transport between fibers when alpha-equal presentations of the input are used.
Ordinary arbitrary-`Prop` induction and an iterator into a fixed nominal carrier
do not settle its constructor/transport coherence or computation equations.
Neither unrestricted dependent elimination nor its impossibility follows from
the existing client. The first contract must explicitly state which dependent
families, if any, are supported. Do not turn this separate research obligation
into a finite-support requirement on ordinary proof motives.

Fresh derivation induction belongs alongside these distinctions, not under
term induction: its recursive objects are rule derivations, and its binder
renaming must preserve the relation's premises and conclusion.

## 3. Proposed user workflow, expressed as non-compiling sketches

Every code block in this section is pseudocode. In particular, `nominal_datatype`,
`nominal_function`, `nominal_inductive`, `fresh_induction`, `recursive`, and
`binding` below are proposed interfaces, not installed Lean commands.

### 3.1 Syntax with single and nested binders

```text
nominal_datatype Term (Atom : Type u) [Name Atom] where
  | var (a : Atom)
  | app (left right : Term)
  | lam (a : Atom) (body : Term) binds a in body

-- Ordinary constructor use; repeated displayed binders remain legal.
example : lam a (lam a (var a)) = lam b (lam c (var c)) := ...

-- A proof may request fresh representatives, including avoiding outer binders.
theorem property (t : Term) (external : X) (A : Finset Atom) : P t external A := by
  fresh_induction t avoiding (external, A)
  case lam a body ha ih =>
    -- ha : a # (external, A)
    -- ih can be used at (external, insert a A).
    ...
```

`binds a in body` specifies exactly the scope of one atom. Nesting repeats that
construction; it is not simultaneous set/list/pattern binding. A let constructor
would write `letE (a) (rhs) (body) binds a in body`, keeping `rhs` outside the
scope. The generator must record that difference explicitly. Nested scopes must
use local-variable identities rather than the spelling of `a`.

The proposed minimum signature has finitely many categories and constructors,
atom fields distinct from recursive-category fields, ordinary fixed data fields,
finite products of fields, and lexically scoped single-atom binder nodes.
Category dependencies may be acyclic, as in terms followed by formulas.
The consolidated architecture proposes finite direct mutual recursion as a
gated target and permits a single binder over a product of fields. These are
proposed contracts, not implemented features; the two-category FOL example
alone does not test a genuine mutual cycle. See the
[backend grammar](2026-10-05-backend-comparison.md) and PKG-04 acceptance gate.
Arbitrary recursive containers and function-space recursive fields are not
silently included by this proposal.

Generated theorem names should be predictable, qualified by the datatype and
constructor, inspectable through ordinary `#check`, and usable without a tactic.
The exact naming scheme is an implementation decision. The required content is
the constructor/action/support/equality/induction/iteration contract in section 1.

### 3.2 A function with fixed nominal parameters

```text
nominal_function subst (x : Atom) (replacement : Term) : Term → Term
  avoiding (x, replacement)
  | var a     => if a = x then replacement else var a
  | app t u   => app (subst x replacement t) (subst x replacement u)
  | lam a t   => lam a (subst x replacement t)
                  when a # (x, replacement)
```

The user writes equations and relevant mathematical freshness. The command
must infer or ask the user to prove that its handlers are supported and that
the binder output is fresh. It must then justify a total, representative-
independent operation. The generated lambda equation is guarded; the notation
does not grant arbitrary raw pattern matching on quotient representatives.

Required outputs include ordinary application, the guarded equations, a renaming
equation, functional uniqueness, and a supported view satisfying
`supp (subst x replacement) ⊆ {x} ∪ supp replacement` under conjugation.
The separate joint law permutes `x`, `replacement`, and the subject together.
No theorem asserting equivariance of every fixed `subst x replacement` is valid.
Composition remains a client theorem with its actual hypotheses: `x ≠ y` and
`x # r` in `t[x := s][y := r] = t[y := r][x := s[y := r]]`.

### 3.3 A primitive-recursion probe using original children

```text
nominal_function record : Term → Term by primitive_recursion
  | var a => var a
  | app t u with recursive rt ru => app t (app rt ru)
  | lam a t with recursive rt    => lam a (app t rt)
```

This is deliberately a small interface probe, not a new lambda semantics.
The application branch uses both the original `t` and its recursive result `rt`;
the lambda branch binds the atom in both the original and processed body.
A test must use the resulting equations and distinguish `t` from `rt`.
Re-expressing it through an accumulator is an implementation strategy, not an
excuse to omit the public original-child contract.

The superficially similar proposal `bodies (lam a t) = {t}` into finite sets of
unabstracted terms must fail: alpha-renaming the input changes the free atom of
the exposed body. A binder-sensitive function cannot be accepted solely because
all recursive calls are structurally smaller. Its output must respect alpha
equality, and a nominal result must meet the promised support contract.

### 3.4 An inductive judgment and a proof using fresh rule induction

```text
nominal_inductive Parallel : Term → Term → Prop where
  | var : Parallel (var a) (var a)
  | app : Parallel t t' → Parallel s s' →
          Parallel (app t s) (app t' s')
  | lam : Parallel t t' → Parallel (lam a t) (lam a t')
          binding a in (t, t')
  | beta : Parallel t t' → Parallel s s' →
           Parallel (app (lam a t) s) (subst a s' t')
           binding a in (t, t') using subst_binder_transport

theorem simultaneousSubstitution (ht : Parallel t t') (hs : Parallel s s') :
    Parallel (subst x s t) (subst x s' t') := by
  fresh_induction ht avoiding (x, s, s')
  case beta a body body' arg arg' hbody harg ha has has' ihbody iharg =>
    -- ihbody and iharg each accept newly chosen substitution contexts.
    -- ha supplies a ≠ x and a fresh for both replacements.
    rewrite [subst_application, subst_abstraction ha, subst_composition]
    exact Parallel.beta (ihbody (x, s, s') hs) (iharg (x, s, s') hs)
  ...
```

Here the `binding` annotation requests a certified renaming action on the named
rule parameters. It is not an axiom or a new semantic freshness premise on
`Parallel.beta`. In contraction, the body premise is renamed, while the argument
premise is left unchanged. Substitution's binder-transport theorem preserves the
conclusion. The generated induction step exposes both premise derivations,
both generalized IHs, and the relevant freshness facts. The actual source proof
is `Parallel.subst`; its statement and hypotheses are the reference contract.

The same fresh-induction command must accept a motive capturing an arbitrary
`q : Atom → Prop`, as in the existing tutorial. Registering `q` as supported
must not become a hidden precondition for this proof facility.

## 4. Agreed second study: first-order logic and substitution admissibility

### Language and exact proposed theorem

Use a small first-order language with a fixed finite vocabulary: variable terms,
one constant and one binary function symbol, one binary predicate symbol,
falsity, implication, and universal/existential quantifiers. Fixed symbol names
are ordinary constructor tags, so the example does not require an arbitrary-
arity container grammar. More symbols can be added without changing the binder
theory. This is ordinary object-language syntax, not a representation of Lean
propositions and not a proposed restriction on user proof motives.

```text
nominal_datatype FTerm where
  | var (a : Atom)
  | const
  | func (left right : FTerm)

nominal_datatype Formula where
  | rel (left right : FTerm)
  | bot
  | imp (antecedent consequent : Formula)
  | all (a : Atom) (body : Formula) binds a in body
  | ex  (a : Atom) (body : Formula) binds a in body

-- Two categories, one atom sort; nested quantifiers use repeated constructors.
all x (ex y (rel (func (var x) (var y)) (var z)))
```

Declare capture-avoiding substitutions on both categories and prove formula
substitution composition. Use finite contexts, proposed concretely as lists of
formulas; duplicates and order are permitted, and lookup is membership. The
headline theorem is:

```text
theorem Derives.substitution (h : Derives Γ φ) (x : Atom) (s : FTerm) :
  Derives (Γ.map (substFormula x s)) (substFormula x s φ)
```

There is no closedness premise, global fresh-variable convention, or restriction
on occurrences of `x` in `Γ`, `φ`, or `s`. The proof must consume fresh
**derivation** induction and the substitution equations. Formula substitution
composition is a prerequisite and a smaller acceptance test; it does not by
itself satisfy this selected judgment-level theorem.

The current core supplies nominal finite **atom** sets, not a general nominal
instance for arbitrary `List X` or `Finset X`; see `PermType.instFinset` in
[PermType.lean](../../Nominal/Set/PermType.lean) and `Nominal.instFinsetNominal` in
[Nominal.lean](../../Nominal/Set/Nominal.lean). The finite-list context choice
therefore requires a focused, coherent List action/nominality/support interface.
An explicit generated `Context.nil`/`Context.cons Formula Context` category is
an alternative. This dependency must be implemented and verified, not assumed
from `List.map` working on ordinary functions. It does not require recursive
containers inside the generated term/formula signatures.

### Natural-deduction rules to include

Use ordinary intuitionistic natural deduction in `Prop`, with the following
finite presentation. `φ[a := t]` denotes capture-avoiding formula substitution.

| Rule | Premises | Conclusion |
| --- | --- | --- |
| Assumption | `φ ∈ Γ` | `Γ ⊢ φ` |
| Falsity elimination | `Γ ⊢ ⊥` | `Γ ⊢ φ` |
| Implication introduction | `φ :: Γ ⊢ ψ` | `Γ ⊢ φ → ψ` |
| Implication elimination | `Γ ⊢ φ → ψ`; `Γ ⊢ φ` | `Γ ⊢ ψ` |
| Universal introduction | `Γ ⊢ φ`; `a # Γ` | `Γ ⊢ ∀a.φ` |
| Universal elimination | `Γ ⊢ ∀a.φ` | `Γ ⊢ φ[a := t]` |
| Existential introduction | `Γ ⊢ φ[a := t]` | `Γ ⊢ ∃a.φ` |
| Existential elimination | `Γ ⊢ ∃a.φ`; `φ :: Γ ⊢ ψ`; `a # (Γ, ψ)` | `Γ ⊢ ψ` |

No logical equality axioms or arithmetic theory are needed. Universal
introduction and existential elimination have genuine eigenvariable side
conditions. These belong to the intended logic; they are different from adding
an arbitrary external freshness restriction to every derivation constructor.

### What simultaneous premise/conclusion transport means here

For universal introduction, rename `a` to a sufficiently fresh `b`, and write
`σ = swap a b`. Joint equivariance transports the premise
`Γ ⊢ φ` to `σ • Γ ⊢ σ • φ`. The old side condition `a # Γ` and chosen
freshness `b # Γ` prove `σ • Γ = Γ`. Alpha equality identifies
`∀a.φ` with `∀b.(σ • φ)`. The conclusion therefore remains the same quotient
formula. A general fresh-induction theorem must retain the IH for the renamed
premise at any requested substitution context.

Existential elimination is the stronger test. Choose `b` fresh for the bodies,
`Γ`, `ψ`, and external avoidance parameters. Rename the discharged assumption
and its derivation together:

```text
Γ ⊢ ∃a.φ                becomes the same premise via alpha equality
φ :: Γ ⊢ ψ             becomes (swap a b • φ) :: Γ ⊢ ψ
a # (Γ, ψ)             becomes b # (Γ, ψ)
Γ ⊢ ψ                  remains exactly the same conclusion
```

The second transformation uses equivariance plus freshness of **both** names
for `Γ` and `ψ`. Renaming only the displayed quantifier, or only the conclusion,
does not justify the renamed second premise. The scoped occurrence metadata
must include the body occurring in the discharged assumption. It must not
rename unrelated free atoms in `Γ` or `ψ`.

Universal elimination and existential introduction have a different pattern.
Their binder can be renamed inside the quantified formula by alpha equality,
and `φ[a := t] = (swap a b • φ)[b := t]` preserves the instantiated endpoint.
This equation requires `b` fresh for the original abstraction `all a φ`
(respectively `ex a φ`); choosing `b # φ` is a sufficient stronger condition.
Without it, take distinct `a,b`, `φ = rel (var b) (var b)`, and `t = const`:
the two sides differ. The generated theorem must retain its freshness premise.
The replacement `t` is not globally swapped. This is the formula analogue of
`Term.subst_rename`; bare joint equivariance of substitution does not express it.

In the admissibility proof, select all rule binders fresh for `(x,s)` in addition
to their rule-specific requirements. Composition then gives
`(φ[a := t])[x := s] = (φ[x := s])[a := t[x := s]]` under `a ≠ x` and `a # s`.
Freshness preservation of substitution ensures the eigenvariable remains fresh
for the substituted context and conclusion. Both existential-elimination IHs
must be used; recursive hypotheses must allow new contexts. Ordinary formula
induction cannot replace this induction over derivations.

### Why this example, and what it does not establish

FOL adds a category embedded in another category, two quantifiers, finite
contexts, discharged assumptions, and eigenvariables spanning several premises.
It stresses the complete syntax/function/judgment workflow without making
mutual syntax, multiple atom sorts, arbitrary function-symbol arities, or cut
elimination immediate prerequisites.

Simply typed lambda-calculus preservation would be a useful later client, but
shares more syntax with the first example. Formula substitution composition
alone is smaller but misses fresh rule induction. FOL cut elimination tests much
more proof theory and is unnecessary to establish this package contract. These
are scope tradeoffs, not claims that the rejected examples are mathematically
inferior. The selected theorem remains substantial enough to reveal a judgment
generator that handles only the shape of beta reduction.

## 5. The five-example portfolio and its extension boundaries

The user selected the portfolio; the following rows distinguish evidence already
available from proposed theorem targets. No row claims a generated implementation.

| Example | Candidate deliverable | Specific pressure on the package |
| --- | --- | --- |
| Lambda calculus | Replay the existing open-term Church–Rosser proof with generated syntax/functions/judgments and ordinary closure lemmas. | Establish the reference interface and preserve both contraction IHs, common-binder inversion, and supported fixed parameters. |
| First-order logic | The substitution-admissibility theorem specified above, including universal introduction and existential elimination. | Multiple categories, finite formula contexts, discharged assumptions, eigenvariable transport in several premises. |
| Lambda calculus with let | Let-expansion correctness for `let x := t in u`, whose binder scopes only `u`; fix the exact equality/reduction semantics before implementing the theorem. | Mixed scoped and unscoped recursive fields in one constructor; substitution must protect the body binder while still substituting into the right-hand side. Expansion should agree with application of an abstraction and preserve alpha equality. |
| Monadic π-calculus | Candidate: alpha-invariance and equivariance of transitions, with a substantive scope-extrusion/fresh-rule-induction client. | An input binder scopes its continuation but not its channel; a restriction binder scopes a process. Bound-output residuals can bind an atom jointly across a label and target, so process syntax alone does not settle judgment binding. |
| Modal μ-calculus | Candidate: capture-avoiding substitution and semantic substitution/unfolding for positive fixed-point formulas. | Binder-aware syntactic positivity, semantic least fixed points, and valuation parameters. Valuations as arbitrary functions must not be declared nominal without a proof. |

For the selected let example, a concrete expansion contract is:

```text
-- Proposed syntax/equations, not existing commands or checked declarations.
| letE (a : Atom) (rhs body : LTerm) binds a in body

expand (letE a rhs body) =
  Term.app (Term.lam a (expand body)) (expand rhs)

expand (t[a := s]) = (expand t)[a := expand s]

-- Candidate operational correctness statement:
t →let u  implies  expand t →β* expand u
```

Here `→let` would be the full contextual reduction containing the lambda beta
rule and `letE a rhs body →let body[a := rhs]`. The displayed simulation is a
proposed precise reading of let-expansion correctness, to be fixed with the
chosen semantics; it does not assert a proved reflection or bisimulation law.

The correct support equation is
`supp (letE a rhs body) = supp rhs ∪ (supp body \ {a})`. The original binder
may occur freely in `rhs`. Consequently a blanket FCB obligation demanding
`a # expand (letE a rhs body)` would be false. Binder lifting must first act on
the scoped body, then combine its result with the untouched right-hand-side
component. Renaming the binder changes `body` and preserves `rhs`, including
free occurrences of the old binder in `rhs`. This is a useful first test beyond
constructors where every recursive field lies inside the same binder scope.

These last two target suggestions require source-informed specification before
implementation. For π-calculus, fix early/late/open semantics and the treatment
of bound residuals; do not claim those alternatives are interchangeable. For
μ-calculus, fix the modal signature, positivity criterion, and semantic theorem.
One atom sort can represent the bound names within each selected language;
multiple examples do not require all their roles to coexist as independent
atom sorts in one carrier.

Arbitrary valuations can be ordinary Lean parameters without being finitely
supported nominal objects. Putting them in a freshness context
requires additional evidence or a deliberately restricted representation. A
future proof may instead quantify such parameters in an arbitrary motive while
using a separate, finitely supported avoidance context. Neither restriction nor
such a proof technique should be chosen accidentally by instance inference.

Fresh allocation is another boundary: classical choice can select an atom
outside any finite set, but no finitely supported function does that for every
input finite set. The [propositions investigation](2026-10-05-propositions-and-induction.md)
records a checked counterexample. A relational fresh-allocation semantics or
an alpha-quotiented result may be appropriate, but noncomputability alone does
not establish its nominal function contract.

## 6. Accepted and rejected judgment forms

This is a proposed restricted automatic grammar, not a theorem that every
well-formed Lean inductive relation has a generated nominal interface.

The initial target is a finite family of `Prop`-valued relations on first-order
nominal data, with rules consisting of a finite telescope of data parameters,
a finite list of positive atomic recursive premises, certified side conditions,
and one atomic conclusion. For the first two examples a single relation at a
time suffices. Mutual relation families require an explicit simultaneous proof
principle before being advertised. Free nominal parameters must be explicit in
the relation's action contract.

| Proposed form | Treatment |
| --- | --- |
| `R t u → R s v → R (app t s) (app u v)` | Accepted shape; both premise proofs and both generalized IHs are generated. |
| Equality/disequality/freshness and membership in a certified finite context | Accepted with their proved permutation/transport laws; no unverified side-condition oracle. |
| Registered external predicates or function calls in rule indices | Accepted after instantiating a proof of the necessary action/transport law for the actual expression and parameters. |
| Explicit single-atom rule binders with occurrences in premises and conclusion | Accepted only after a certificate proves transport of every scoped occurrence and preservation of the conclusion tuple. |
| A fixed arbitrary `q : Atom → Prop` used in a rule premise | No automatic equivariance claim. Generalize `q` as an acted-on parameter, supply sufficient support/action evidence for a relative interface, or use ordinary Lean without the requested nominal theorem. This does not restrict an arbitrary `q` captured by a later induction motive. |
| Recursive occurrence beneath negation or to the left of an implication inside a premise, e.g. `(R x → False) → R y` | Outside the positive rule grammar; Lean positivity must also succeed. |
| Recursive premises under arbitrary `∀`, `∃`, higher-order functions, or containers | Outside the first automatic subset until a corresponding premise/IH lifting contract is proved. A finite telescope of rule data variables is not this higher-order recursion form. |
| Pattern/list/set/simultaneous binders, multiple atom sorts, dependent relation indices requiring unsupported transport | Rejected by the first grammar with a precise explanation; not silently approximated by single binding. |
| An annotation calling a freely exposed atom a binder | Rejected when conclusion preservation fails, even if the relation itself is equivariant. |

A simple failure test is the equivariant relation with constructor
`Seen.intro (a) : Seen (var a)`. Marking `a` as freshenable while keeping the
conclusion fixed is invalid. If the proposed strong rule induction allowed
`a # z` in its sole case, the motive `fun t z => z # t` would prove an atom fresh
for itself. Relation equivariance alone therefore cannot justify the requested
binder annotation.

### Required certificate for one rule binder

For a rule environment, old binder `a`, and sufficiently fresh `b`, a
proof-producing command needs the following information:

1. A precise map of scoped parameter occurrences, with a simultaneous renamed
   environment. Lexical binding metadata alone identifies candidates; it does
   not prove this map admissible.
2. For every recursive premise, either an unchanged premise up to equality or
   a proved permutation transport of that premise, including all its indices.
   Side-condition proofs are transported as well. Different premises may use
   different permutations; parallel contraction already requires this.
3. Equality of the original and renamed **whole conclusion tuple**, after using
   abstraction, substitution, and fixed-residual-parameter laws as appropriate.
   Establishing only that the new tuple satisfies the relation is too weak to
   finish an arbitrary motive at the original indices.
4. An induction argument whose IHs actually cover the transported recursive
   premises. The current pattern strengthens ordinary derivation induction over
   permutations and contexts, so the IH is applied to a permutation of the
   original strict subderivation. Merely constructing some new derivation of a
   premise does not ensure that it is covered by the induction hypothesis.
5. Freshness for the requested external context and any residual rule parameters,
   and compatibility for nested freshening in the chosen order.

The current lambda implementations use support/freshness preservation of
reduction to choose one fresh atom from fewer source objects. A generic rule
scheme could instead choose it fresh for all finitely many relevant endpoint
objects. The package must prove the scheme it uses; support decrease is a useful
property of beta/parallel reduction, not an automatic property of every
equivariant judgment.

Ordinary inductive constructors, equivariance, fresh induction, and fresh
inversion should be separately named generated results. If a requested theorem
cannot be generated, the diagnostic must identify the missing mathematical
obligation. Do not silently return an interface advertised as complete or leave
half-generated public declarations after command failure.

## 7. Responsibility and proof escape hatches

| Facility | User supplies | Generator/automation must justify | Explicit escape hatch |
| --- | --- | --- | --- |
| Datatype | Categories, fields, atom sort, lexical binding scopes, fixed data actions if not discrete by declaration. | Accepted grammar and positivity; coherent raw/quotient construction or other carrier; action laws; alpha equality; canonical nominal instance; support equations; constructor discrimination/inversion; induction/iteration contracts. | A proved external nominal carrier/action and registered constructor interface. Unsupported signatures require another construction, not an unchecked annotation. |
| Function | Equations, explicit parameters, intended freshness side conditions, requested recursion mode and result. | Recursive-call admissibility or termination; handler support; alpha compatibility/guarded FCB; totality and uniqueness; equations and renaming; ordinary and NFun views with exact advertised bounds. | Local Lean proofs of support/FCB/transport/termination; direct proved graph or quotient lift; existing `NFun.ofFun`, `ofSupports`, `ofCaptures`, `equivariant`, or `fromParam` as appropriate. |
| Judgment | Prop-valued rule signatures, side conditions, rule-binder scopes, semantics of eigenvariables. | Positivity; relation equivariance or accurately stated support-relative law; per-rule freshening certificates; IH transport; fresh induction and inversion preserving every rule alternative. | Supply missing action/binder-transport lemmas in ordinary Lean. A handwritten relation/principle can be registered only with its checked theorem, not by trust in its name. |
| Proof automation | Selected avoidance context and optional local lemmas/certificates. | Fresh existence for eligible nominal objects; every split freshness fact; support/action rewriting justified by proved rules; complete elaborated proof terms. | Show the unsolved goal and relevant captured parameters; accept a direct proof or a smaller explicit avoidance set. An unsupported motive remains permitted for ordinary induction. |

The function interface needs an additional distinction: a structurally recursive
definition on raw syntax may terminate and still fail alpha descent, while a
well-defined ordinary quotient function may fail finite support. Those failures
need different diagnostics. Classical choice is a permitted construction tool,
not a support certificate. Generated upper bounds must be labeled as bounds;
captured atoms can cancel, so a syntactic capture analysis does not compute least
support in general.

For every generated theorem, the proof obligations remain visible through
ordinary Lean declarations. A language-level error should name the offending
clause, scope, or captured value and show the unresolved mathematical condition.
It should distinguish a statement refuted by a counterexample from an obligation
the current automation simply cannot solve.

## 8. Sound support automation and expression identity

The existing [`NFun.Basic`](../../Nominal/Set/NFun/Basic.lean) and
[`NFun.Tactic`](../../Nominal/Set/NFun/Tactic.lean) provide proof-backed
constructors, `supports_nfun`, and `nfun_simp`. The `nfun` macro is documented as
experimental; the package must not assume it already handles arbitrary globals,
shadowing, `let`, `match`, or nested functions. This note performs no fresh macro
failure reproduction and makes no new defect claim about those cases.

A future implementation should elaborate first and inspect local-variable
identities (`FVarId`s) and expression structure, preserving binder scopes,
universe parameters, implicit arguments, and the chosen action instances.
Source identifier spelling is not capture identity. A global declaration is
not automatically equivariant, and a local value of ordinary function type is
not automatically finitely supported.

The proposed registry stores or indexes **theorems**, such as a support bound,
joint equivariance equation, binder-output freshness theorem, or judgment
transport lemma. Registration must validate the theorem's shape. Applying a
registry entry must instantiate and kernel-check that theorem for the actual
elaborated expression. A string tag such as “equivariant” without a corresponding
proof must not discharge an obligation. Equal types with different action
instances must not be conflated; preserve the separation of `PFun` conjugation
from ordinary pointwise function actions.

Initial search should be compositional and bounded: variables with proved
support, constants with certificates, constructor application, products,
composition, curry/uncurry, evaluation, and registered operations. Case splits
and conditions require their own action laws. Failed inference should report
the missing certificate and allow an explicit proof without unfolding quotient
internals. General automation for every Lean expression is not a sound contract.

Regression tests should include shadowed names, derived nominal instances,
captured fixed parameters, a supported non-equivariant function, an arbitrary
unsupported global, nested scopes, and differing action instances. Positive
tests must consume generated equations/freshness/IHs in substantive conclusions;
negative tests must check the intended diagnostic. The arbitrary predicate in
an induction motive must remain accepted even when the same predicate lacks a
support certificate needed for a nominal-function or rule-equivariance request.

## 9. Acceptance evidence and remaining decisions

For lambda replay, require the current theorem strengths: open terms, unrestricted
reduction, both parallel-substitution inputs varying, ordinary quotient equality,
arbitrary motives, nested avoidance contexts, fresh inversion, and actual
Church–Rosser/normal-form-uniqueness consumers. No normal-form-existence or
termination theorem is required. A generated proof of a weakened closed-term
statement does not reproduce the reference client.

For FOL, require formula support/alpha/substitution equations and the unrestricted
admissibility theorem above. Persistent consumers should include substitution
that must rename a quantifier, repeated displayed binders, two syntactic
categories, a nonempty assumption context, universal introduction, existential
elimination consuming both IHs, and at least one transported premise whose
original eigenvariable clashes with the requested substitution context.

For primitive recursion, require a client such as `record` that uses an original
child and its recursive result, plus its computation and support/uniqueness
theorems. This is an additional package requirement, not a missing proof step in
the completed Church–Rosser argument. Dependent data-valued elimination requires
its own stated scope and validation plan.

Before implementing the command grammar, settle: mutual syntax/relations; nested
recursive containers; the exact primitive-recursion admissibility theorem;
public universe bounds; judgment binder-certificate types; finite context
representation; and the remaining portfolio language/semantics choices. Keep
user-facing declarations independent of the selected generic, per-declaration,
or hybrid backend wherever their mathematical contracts agree.

This note was checked against current local source declarations and the listed
research/release documents. Historical correspondence is taken from the pinned
[research correspondence](../research-correspondence.md); no external source was
rebuilt or newly certified here. No Lean files or production code were edited,
and no new DSL example was compiled. Local link and whitespace checks validate
this document only; builds and axiom audits must be recorded separately with
the exact commands and revision when the implementation work occurs.
