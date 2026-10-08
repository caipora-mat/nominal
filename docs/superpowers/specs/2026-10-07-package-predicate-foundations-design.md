# PKG-01: predicate foundations

Date: 2026-10-07; representation and written-spec approval recorded 2026-10-08.
**Written specification and implementation plan approved for native execution.**
Execution is native; the author subsequently grouped Tasks 4–5 as phase 01b
and Tasks 6–7 as phase 01c. The current run completed only Task 8 and stops here. Earlier handoffs remain historical.
Task: [PKG-01](../../nominal-package-roadmap.md#pkg-01--predicate-foundations).
Inspection baseline: `fasapa/nominal-package`,
`3c9d8dc527f7705b24c0308a2527e659ae933874` (`some predicate + function support`),
with a clean index and working tree. F02–F05 are delivered and committed.
The approved F05 hybrid is a dependency, not a design question reopened here.

The author authorized source investigation, bounded scratch experiments, research
notes, article exposition and this specification. The author selected **scoped
`И` notation alongside a named fresh-quantifier operation** during the investigation.
On 2026-10-08 the author selected **choice 1: the direct predicate record**.
The author then approved the full written specification, including the three
phases. The [implementation plan](../plans/2026-10-08-package-predicate-foundations.md)
fixes public names, module ownership, consumers and verification steps.
The author approved that plan and selected native execution in fresh contexts
on 2026-10-08. Tasks 1–3 now deliver the complete predicate-value and logical
calculus phase 01a, uncommitted, including bundled quantifiers and supported
collection operations. Tasks 4–5 now deliver general pullback and ordinary/supported
quotient descent, completing phase 01b uncommitted. Tasks 6–7 now complete
phase 01c: ordinary cofinite theory, Some/Any, contexts and bundled fresh projection,
with proved boundaries. Task 8 now completes public integration, all
specification criteria and the independent whole-change review. PKG-01 is
complete, uncommitted; later PKG tasks were not started.
Nothing is committed by this session.

## 1. Intent, scope and selected representation

Provide reusable predicate mathematics for ordinary Lean `Prop`: supported
predicate values, logical support and quantification, equivariant-surjective
pullback and quotient descent, and cofinite fresh quantification with Some/Any.
Ordinary unsupported predicates remain usable as functions and induction motives.
Support evidence is required at the particular nominal operation that needs it.

Use the selected **direct predicate record with proof-only finite support**, with
named, proved views into the existing supported-function and supported-subset
carriers. Derive action/support results through F05 and Boolean structure through
Mathlib; the direct record is an application interface, not a second foundation.

Separate three review units within PKG-01:

1. **01a — Predicate values and logical calculus.**
2. **01b — General pullback and ordinary/supported quotient descent.**
3. **01c — Cofinite quantification, Some/Any and nominal logical laws.**

The ordinary parts of 01b and 01c do not depend on the storage choice. Their
bundled endpoints depend on 01a. All three are required to complete PKG-01;
delivering a wrapper alone does not meet its criterion. F06, syntax generators,
judgment commands, support automation, binder descent, recursion and case studies
are outside this specification. No new foundational rebuild, dependency upgrade,
global action replacement, CI or reference-library migration is proposed.

## 2. Delivered inputs and Mathlib reuse

The detailed current-source inventory and checked evidence are in the
[investigation](../../research/2026-10-07-pkg01-predicate-foundations.md).
The essential starting points are:

| Delivered input | Use here |
| --- | --- |
| `SupportsPred`, `FinitelySupportedPred`, `renamePred` | Keep ordinary input certificates and the established renaming operation |
| `predicateObjectEquiv`, support/map/Set correspondences | Derive carrier views and their action/support agreement |
| Predicate monotonicity, precomposition, sections and equality support | Reuse directly; add logical operations and missing reflection, not duplicates |
| `SupportedMap`, `FunctionObject`, `ActionSupport.supports_map_iff` | Supported-function view, action transfer, exact support through equivariant injections |
| Elementwise/carrier least support and freshness | No second least-support choice; individual parameter evidence remains sufficient |
| Explicit `QuotientAction.mulAction`, projection equivariance/surjectivity | Canonical action for supported descent; no automatic quotient instance |
| `Setoid.liftEquiv` | Ordinary quotient-function universal property, adapted to Iff compatibility with `propext` |
| `Function.FactorsThrough` | Existing fiber-compatibility vocabulary and proved predicate adapter |
| `BooleanSubalgebra`, `Equiv.booleanAlgebra`, `Function.Injective.booleanAlgebra` | Inherit or transfer Boolean/order laws after proving nominal closure |
| `Filter.cofinite`, `eventually_cofinite`, finite exclusions and reindexing | Definition and ordinary filter theory for the fresh quantifier |

The predicate carrier, logical calculus and predicate pullback/descent are now
delivered, together with the ordinary and bundled fresh-quantifier interface.
Final integration and the independent whole-change review now pass.
Existing object-support/fiber results do not fill the predicate descent gap.
The old direct-SPred recommendation is historical: supported maps now exist.

## 3. Representation comparison

| Candidate | Ordinary use and reuse | Cost and disposition |
| --- | --- | --- |
| Direct `X → Prop` record with a support proof | `p x : Prop`, Iff ext, ordinary higher-order use; exactly the certificate already expressed by `SupportsPred` | Needs explicit function/subset equivalences; **selected by the author on 2026-10-08** |
| `SupportedMap A X (Discrete A Prop)` specialization | Existing action, nominality, supported combinators and extensionality | Application returns `Discrete A Prop`; exposing `.val` or a second function coercion conflicts with the desired public application boundary; retain as a named view |
| Distinct predicate-facing wrapper over that specialization | Same successful Prop-facing consumers as the direct record; action transfers through one projection | Viable close alternative; stores the function encoding under a logical interface and still needs Iff ext, constructors, Boolean structure and subset adapters |
| Supported-subset subtype / Boolean-subalgebra carrier | Direct inherited Boolean structure and set interpretation | A plain subtype does not provide `p x`/`List.map p`; an explicit FunLike adapter works. Viable, but the public API still needs a named function-like boundary and controlled Set action |

No candidate is rejected as mathematically unsound. Direct and wrapper probes
both pass ordinary application, Iff rewriting, `ext`, `simp`, higher-order use,
independent universes and proof independence. The direct record avoids making
discrete truth conversion part of its primary data projection. Its small bridges
allow reuse of the supported-function theory instead of independently rebuilding
action laws and support mathematics. There is no performance or user-study claim.

The author's subsequent comparison request prompted equally detailed wrapper
checks: its action, nominality, exact support, Boolean transfer and higher-order
map consumers also compile. Both stores have definitionally equal conversion
round trips and logical-versus-map precomposition. The author selected the direct
record after this comparison. The choice makes logical fields primary; it does
not assert a demonstrated computation or general usability advantage over the
wrapper. The alternatives remain documented as design evidence.

The plain specialization should not acquire a competing Prop-valued FunLike
instance alongside its existing discrete-valued instance. The subset alternative
must not acquire a second global Set action. These are interface constraints,
not deficiencies in their underlying mathematics.

### Public carrier and computation

For independently quantified `A : Type u`, `X : Type v`:

```text
structure SupportedPred (A : Type u) (X : Type v)
    [MulAction (Perm A) X] : Type v where
  toFun     : X → Prop
  supported : FinitelySupportedPred A toFun

ofFun A p hp : SupportedPred A X
ofSupports A p S hS : SupportedPred A X

(ofFun A p hp) x ↔ p x
(ofFun A p hp : X → Prop) = p
p = q ↔ ∀ x, p x ↔ q x
```

Use `FunLike` with **one automatic coercion, to `X → Prop`**, an Iff-based
`@[ext]` theorem, pointwise congruence and directed application/coercion simp
lemmas. `ext x; ...` must leave an Iff goal. `rw [h x]` must rewrite ordinary
propositions. A changed existence proof or a different sufficient bound gives
the same value, by proof irrelevance. No finite support is stored as data.
No coercion from an arbitrary predicate supplies a certificate automatically.

The literal-proof probe found a local elaboration requirement:
`FinitelySupportedPred` is presently a semireducible `def`. Constructor simp
lemmas should quantify the proof as
`hp : ∃ S : Finset A, SupportsPred S p`, which is definitionally equivalent.
This makes literal `⟨S,hS⟩` calls simplify, without changing F05's definition
or adding a global reducibility setting. Test both named and literal evidence.

### Views, action and support

Provide explicit `toMap`, `ofMap`, `toObject`, `toSet`, and certified `ofSet`.
The required equivalences are

```text
SupportedPred A X ≃ SupportedMap A X (Discrete A Prop)
SupportedPred A X ≃ {U : Set X // FinitelySupportedPred A (fun x => x ∈ U)}
```

Each equivalence has application/membership, inverse and action laws. In particular:

```text
(p.toMap x).val = p x
p.toObject = predicateObject A (fun x => p x)
x ∈ p.toSet ↔ p x
(π • p) x ↔ p (π⁻¹ • x)
(π • p) (π • x) ↔ p x
(π • p).toMap = π • p.toMap
(π • p).toSet = π • p.toSet             -- existing Pointwise Set action
Supports S p ↔ SupportsPred S (fun x => p x)
Supports S p ↔ Supports S p.toMap
Nominal A (SupportedPred A X)
```

The action may be defined by `renamePred` and certified using F05 transport;
transfer action laws along the injective `toMap` with
`Function.Injective.mulAction`. Prove exact support through the same embedding.
The subset action is the restriction of the existing scoped Set image action,
with stability supplied by F05; it is not a new action on bare `Set X`.
Its membership law is also equivalent to
`∃ y, y ∈ p.toSet ∧ π • y = x`.

With `Infinite A`, require least-support agreement with both supported views
and with the existing elementwise certificate for `predicateObject A p`.
For the bare `p.toSet`, use its induced elementwise support certificate; do
not write carrier-level `support A p.toSet` or assume `Nominal A (Set X)`.
An ordinary predicate with individual support evidence can use that object
directly; it need not first be bundled. Evaluation is jointly invariant as an
ordinary relation, or equivariant with codomain `Discrete A Prop`.

## 4. Universe, action and hypothesis policy

* Atom, carrier, quantified carrier, parameter and index universes are independent.
  `SupportedPred A X : Type v` does not rise to the atom universe.
* Basic carrier, logical support, Boolean structure, sections and descent need
  neither `Infinite A` nor nominality of the domain. Actions are selected through
  existing `MulAction (Perm A)` instances; A is explicit at ambiguous constructors.
* `Infinite A` is used for least-support/freshness consequences and witness-based
  Some/Any. It is not a premise for defining cofinite truth or its support transport.
* Keep `DecidableEq A` on displayed finite unions and image bounds as in F05.
  Common-bound statements and existential forms need no global equality premise;
  use classical decisions locally in proof fields. No computable body should
  become noncomputable solely because its support proof uses choice.
* The named fresh quantifier needs no action at all. Its nominal laws specialize
  to the canonical atom action. Do not silently quantify cofinally over arbitrary
  nominal carriers and reuse atom Some/Any.
* No action or nominality instance is installed on bare `Prop`; no competing
  action is installed on ordinary arrows or `Set`. Explicit quotient constructors
  continue to fix the intended action. No atom `outParam` is introduced.

General parent statements must describe the mechanism actually used. In
particular, scalar-invariance reflection uses only `SMul`; group-function support
reflection may use F05's group action and arbitrary sufficient sets. Do not add
a parallel generic logical-support definition merely to express these parents.

## 5. Logical calculus

### Ordinary certificates first

For ordinary predicates with the indicated certificates, export:

| Operation | Sufficient bound / premises |
| --- | --- |
| Constant truth value `fun _ => b`, for any `b : Prop` | Empty bound |
| `¬p` | Same bound as p; support reflection also holds by double negation |
| `p ∧ q`, `p ∨ q`, `p → q`, `p ↔ q` | Common bound S if it supports both; union of separate bounds S,T as a corollary |
| `p ∘ f` | Reuse F05 precomposition, union with the ordinary map bound |
| Fixed parameter section | Reuse F05 section rules, requiring only that parameter's certificate |

Expose existential finite-supportedness corollaries without a global decidable
equality premise. Over infinite atoms derive least-support inclusions from these
bounds, with equality for complement. Do not label conjunction/disjunction/
implication bounds exact. Connectors are jointly equivariant; fixing an operand
can leave nonempty support.

### Boolean and order interface

Construct the supported subsets as a `BooleanSubalgebra (Set X)`: nominal
closure supplies `supClosed'`, `infClosed'`, `compl_mem'`, and `bot_mem'`.
Transfer its Boolean algebra to the chosen record with `Equiv.booleanAlgebra`,
or equivalently the existing injective-transfer theorem with the explicit
operation equations. Use one coherent order/operation structure, with

```text
p ≤ q ↔ ∀ x, p x → q x
(⊥ : SupportedPred A X) x ↔ False
(⊤ : SupportedPred A X) x ↔ True
(p ⊓ q) x ↔ p x ∧ q x
(p ⊔ q) x ↔ p x ∨ q x
pᶜ x ↔ ¬ p x
(p ⇨ q) x ↔ (p x → q x)
biimp p q x ↔ (p x ↔ q x)
```

Provide the needed subtraction computation lemma inherited from Boolean
structure. `biimp` is derived from implication and conjunction. Set membership
and function application are connected by named lemmas, not competing automatic
coercions. The action preserves Boolean operations and the pointwise order.
Do not implement a second manual Boolean algebra or an unrestricted
`CompleteLattice (SupportedPred A X)` instance. Mathlib's complete lattice of
**Boolean subalgebras** is a different carrier from the elements of one subalgebra.

### Whole-carrier, restricted and family quantification

For `R : X × Y → Prop` with the joint product action:

```text
SupportsPred S R → SupportsPred S (fun x => ∀ y, R (x,y))
SupportsPred S R → SupportsPred S (fun x => ∃ y, R (x,y))
```

Both need only the selected actions on X,Y. Reindex y by the permutation's
bijection. Include empty Y and a genuinely non-nominal acted Y in consuming
checks. Bundle the results as `SupportedPred.all` / `.ex` with these application
Iffs, support inclusions and action laws. These names are proposed public names;
the written implementation plan will fix declaration spelling.

Restricted quantification by `D : X × Y → Prop` is quantification of
`D (x,y) → R (x,y)` or `D (x,y) ∧ R (x,y)`; combine the joint bounds of D and R.
The most general premise is support of that combined body itself. Separate
support of D and R is a sufficient constructor, not a necessary admission rule.
For a fixed `D : Y → Prop`, use equivariant projection precomposition. Do not
invent a global action on a subtype cut out by a merely supported D.

Distinguish these family contracts:

1. **Uniform bound, external index:** for any `I : Sort w`,
   `(∀ i, SupportsPred S (P i))` supports both `∀ i, P i x` and `∃ i, P i x`.
   I needs no action or inhabitance. Sectionwise support with different bounds
   is not this hypothesis.
2. **Jointly supported indexed relation:** an acted I and a certificate for
   `R : X × I → Prop` give the whole-carrier theorem above. Indices are renamed;
   there need not be a common bound for the fixed-index sections.
3. **Supported collection of supported predicates:** derive union/intersection
   for `F : SupportedPred A (SupportedPred A X)` by quantifying
   `F p ∧ p x` or `F p → p x`. Evaluation is jointly invariant, so every bound
   of F supports the result. Supply the membership equations and bound/action
   laws; no arbitrary external-family completeness follows.

Do not rebuild supported currying. `curryAt` uses the particular parameter's
support; a full curry needs supported sections, with nominality of the parameter
carrier as one sufficient convenience. The F05 admission condition remains.

## 6. Pullback and quotient descent

### Reusable reflection mechanism

The ordinary scalar parent can state, for `[SMul M X] [SMul M Y]`, an
action-preserving surjection q and each scalar m:

```text
(∀ x, P (q (m • x)) ↔ P (q x)) ↔ (∀ y, P (m • y) ↔ P y).
```

Surjective substitution and the action equation prove this; no group laws,
finite support, atom type or nominality enter. Do not define a competing generic
`SupportsPred` to package it. For actual support objects, use the existing
function-action generality:

```text
[DivisionMonoid G] [SMul G B] [MulAction G X] [MulAction G Y] [MulAction G Z]
q : X → Y, equivariant q, Surjective q, S : Set B
F : FunctionObject G Y Z
--------------------------------------------------------------
MulAction.Supports G S (precompObject q F) ↔ MulAction.Supports G S F
```

Use `ActionSupport.supports_map_iff`: precomposition is an equivariant injection
when q is equivariant and surjective. Its action proof uses q's equation at the
inverse scalar, without group cancellation, so `DivisionMonoid` suffices.
Reuse existing composition/function bodies; only add the focused adapter
justified here, with its application law.

The required ordinary nominal specialization, for **arbitrary** `P : Y → Prop`, is

```text
Equivariant A q → Surjective q →
  (SupportsPred S (P ∘ q) ↔ SupportsPred S P).
```

Preservation alone needs no surjectivity and is also obtainable from F05.
Existential support is preserved and reflected; with `Infinite A`, the
corresponding predicate objects have equal elementwise least supports.
No nominality assumption on X or Y is allowed here. Provide bundled pullback,
ordinary computation, and exact support under surjectivity. Fixed equivariant q
gives an action-preserving map of predicate carriers.

### Ordinary descent, before any nominal hypotheses

For any `s : Setoid X`, define a transparent predicate-facing compatibility
alias with the exact meaning

```text
Compatible s p := ∀ x y, s.r x y → (p x ↔ p y).
```

Prove adapters to `s ≤ Setoid.ker p` and
`Function.FactorsThrough p (Quotient.mk s)`. Use `propext` and `Iff.of_eq`.
Adapt `(Setoid.liftEquiv s).symm` via subtype equivalence to obtain

```text
(Quotient s → Prop) ≃ {p : X → Prop // Compatible s p}.
```

The public `descend` operation can name this existing lift. Required laws are

```text
descend s p hp (Quotient.mk s x) ↔ p x
pullback (descend s p hp) = p
descend s (pullback P) (compatibility_of_pullback P) = P
```

The constructor equation should be definitionally computable through the chosen
adapter where the Mathlib lift permits it, and always available as directed
`simp`. Round trips are ordinary function equality. Descent is independent of
compatibility proof. No support or action premise is added to this layer.

### Supported and action-compatible descent

Add `[MulAction (Perm A) X]` and `hs : SMulInvariant (Perm A) s`. Fix the action by

```text
letI := QuotientAction.mulAction s hs
```

Specialize general pullback reflection using `.equivariant_mk` and
`Quotient.mk_surjective`, giving for each finite S:

```text
SupportsPred S P ↔ SupportsPred S (P ∘ Quotient.mk s)
SupportsPred S (descend s p hp) ↔ SupportsPred S p.
```

Compatibility is preserved by `renamePred`; prove this with invariant s and
inverse permutation. Restrict the ordinary equivalence to

```text
SupportedPred A (Quotient s) ≃
  {p : SupportedPred A X // Compatible s (fun x => p x)}.
```

Give both inverse laws, representative computation, action compatibility and
exact sufficient-support correspondence. The compatible subtype has the
restricted action; source nominality is not required. Over infinite atoms
derive exact least-support equality and freshness agreement against any
individually supported context. Derive, rather than separately define, logical
operation preservation through the computation laws.

Neither this theorem nor the supported equivalence supplies a representative
attaining its quotient class's support. Dependent data-valued descent needs
transport coherence and is outside this Prop correspondence.

## 7. Cofinite fresh quantification and Some/Any

### Ordinary operator and notation

```text
Freshly (p : A → Prop) : Prop := ∀ᶠ a in Filter.cofinite, p a
```

This is meaningful for every type A and predicate p, without actions, support or
infinitude. Provide the cofinite-filter equation and the equivalent finite-set
exception form. Reuse `Filter.eventually_cofinite` rather than redefine a filter.

The author selected opt-in notation, provisionally in a dedicated
`NominalPackage.FreshQuantifier` scope:

```text
И a, p a
И a : A, p a
```

Both elaborate to `Freshly`; the named API stays available without opening the
scope. Test binder hygiene, type inference and coexistence with ordinary
quantifiers. Do not overload `Fresh`, which already denotes support disjointness.

### Laws and their different hypotheses

Write C p for `Freshly p` only in the following specification table.

| Law | Hypotheses |
| --- | --- |
| `C True`; pointwise implication/congruence preserves C | None |
| `C (fun a => p a ∧ q a) ↔ C p ∧ C q` | None |
| `C (fun _ => b) ↔ b`; `C p → ∃ a, p a`; `¬ C False` | `Infinite A`, or general filter nontriviality in an inherited parent |
| `C (p ∘ e) ↔ C p` | Any `e : A ≃ B`, `p : B → Prop`, independent universes; no support or infinitude |
| `C (fun a => ∀ i, R a i) → ∀ i, C (fun a => R a i)` | None |
| `(∃ i, C (fun a => R a i)) → C (fun a => ∃ i, R a i)` | None |
| Converse of the universal direction | Finite index is sufficient; arbitrary index is not |
| Converse of the existential direction | Finite index alone is insufficient; a shared finite support bound with infinite atoms suffices, including arbitrary index types |
| `C (¬p) ↔ ¬ C p` | `Infinite A` and p finite or cofinite; finite support is a sufficient nominal premise |
| `C (p ∨ q) ↔ C p ∨ C q` | One operand eventually decided (`C p ∨ C (¬p)` or the symmetric alternative); in particular one supported atom predicate suffices |
| `C (p → q) ↔ (C p → C q)` | Eventually decided p; in particular supported antecedent p, arbitrary q; no infinitude |
| `C (p ↔ q) ↔ (C p ↔ C q)` | Eventual decision of both operands; both supported is a sufficient nominal interface; no infinitude |

Here connective expressions denote pointwise predicates. Keep general filter
lemmas at the weakest valid level when Mathlib already has them. Add only small
missing eventual-decision adapters. Do not require support for conjunction,
monotonicity or the valid one-way quantifier rules. Conversely, ordinary cofinite
truth is not an ultrafilter on all atom subsets.

For a particular pair these decision premises need not be necessary. For example,
an already cofinite operand suffices for the Iff law with an arbitrary other
operand; one merely supported operand does not. Export a useful direct eventual
version where it avoids stronger support assumptions. The implication/Iff laws
above remain valid for the bottom filter on finite atom types, unlike self-dual
negation.

A two-element index of an infinite/coinfinite predicate and its complement
already refutes the unrestricted existential converse. For finite families of
supported predicates, a common finite bound can instead be assembled from
the individual bounds. A common bound for every section gives full universal
interchange for an arbitrary external index without infinitude: use a single
atom outside the bound in the infinite case and the bottom cofinite filter in
the finite case. For existential interchange the same shared-bound premise
suffices with `Infinite A`, or alternatively with `Nonempty I`. These are
stronger hypotheses than separate sectionwise support. The empty-index case
explains the distinction: over finite atoms C False holds, while an existential
over an empty index fails.

### Supplied-bound Some/Any

Assume `[Infinite A]`, canonical atom action, `S : Finset A`,
`hp : SupportsPred S p`. Export all of:

```text
Freshly p ↔ ∃ a, a ∉ S ∧ p a
Freshly p ↔ ∀ a, a ∉ S → p a
a ∉ S → (Freshly p ↔ p a)
```

No least-support computation or decidable equality instance is part of these
public premises. Outside swaps show p is constant off S; finite exclusions and
`Filter.cofinite_neBot` yield a fresh witness. The finite-or-cofinite classification
has weaker hypotheses than Some/Any: for any atom type,
`FinitelySupportedPred A p` is equivalent to finiteness of the truth set or of
its complement. On finite carriers this is immediate; on infinite carriers
outside-swap constancy proves the forward direction. Finite sets and their
complements give the converse. The certificate remains separate from the
ordinary predicate.

With any extra `T : Finset A`, the same equivalences allow simultaneous
avoidance `a ∉ S ∧ a ∉ T`, or an enlarged proved bound. Arbitrary additional
atoms do not alter the truth value. For a jointly supported relation with a
particular parameter c, reuse F05 sections with `Supports T c` or
`hc : FinitelySupported A c`; the sufficient exclusion is the union of the
relation and parameter bounds. For jointly invariant relations use the
parameter bound alone. Least-support freshness is a derived convenience:
`hc.Fresh a` may discharge the parameter avoidance, without `Nominal A C`.

For `R : X × A → Prop` under the joint action, require

```text
SupportsPred S R → SupportsPred S (fun x => Freshly (fun a => R (x,a))).
```

This preservation theorem needs neither `Infinite A` nor nominality of X:
cofinite reindexing by an atom permutation proves it even on finite A.
Supply the bundled operator `SupportedPred.fresh` and its application/action
laws using this result; its least-support inclusion adds `Infinite A`.

## 8. Acceptance and decisive evidence

The [research note](../../research/2026-10-07-pkg01-predicate-foundations.md)
distinguishes freshly checked scratch proofs from inherited evidence and future
integration obligations. Final implementation must consume the public import,
without unfolding representation proofs to make ordinary clients work.

| Consumer or boundary | Required conclusion |
| --- | --- |
| Fixed-atom equality | Singleton support, renamed parameter equation, and non-equivariance under a moving swap |
| Ordinary ergonomics | `p x : Prop`, higher-order arguments, Iff rewriting, `ext`, proof independence, named/literal evidence simp |
| Universes/actions | Independent universe parameters and two atom sorts; no Prop action or competing arrow/Set action |
| Nonminimal bounds | Logical certificate and meaningful Some/Any conclusion using a supplied larger bound |
| Quantification | Empty quantified carrier and non-nominal acted carrier; no accidental Nonempty/Nominal premise |
| Particular parameters | A supported element in a carrier containing unsupported elements; bound actually consumed |
| Ordinary descent | Unsupported predicate descends through a compatible quotient; no finite-support evidence requested |
| Pullback | Both support directions and exact least support with equivariant surjection; non-surjective counterexample |
| Quotient boundary | Canonical selected action and round trips; alpha-incompatible raw predicate provably cannot descend |
| Fresh reasoning | Supplied/enlarged bounds, extra finite avoidance, individual parameter certificates, joint-support projection |
| Unsupported ordinary predicates | Infinite/coinfinite example remains legal but has no support certificate; ordinary induction consumer accepted |
| External union | Supported singletons have an unsupported infinite/coinfinite union |
| Quantifier scope | Equality/disequality refute unjustified fresh ∃/∀ interchange; no cofinite generalization to all nominal carriers |
| Choice | No finitely supported global selector fresh for every finite input set; ordinary classical choice remains legal |
| Trust and computation | Representative signatures and axiom dependencies; no admissions/custom axioms; support witnesses confined to proofs |

## 9. Dependency-ordered phases and verification

The delivered module boundaries below retain the approved scope and import
layering under `Package/Foundations/`.

| Phase | Modules / dependencies | Completion criterion |
| --- | --- | --- |
| 01a — complete, uncommitted | `PredicateLogic.lean` over F05; `SupportedPredicate.lean` over ordinary logic and SupportedFunction; `SupportedPredicateLogic.lean` over the carrier | Ordinary logical and quantified support; all four representation views; coherent action/nominality; transferred Boolean structure; supported-family union/intersection; ordinary-use and empty/non-nominal consumers |
| 01b ordinary — complete, uncommitted | `PredicateDescent.lean` using Mathlib setoid/fiber APIs, F05 support and F04 canonical action | Ordinary correspondence, reusable reflection, canonical quotient support/renaming, unsupported descent and non-surjectivity/non-descent counterexamples |
| 01b bundled — complete, uncommitted | `SupportedPredicateDescent.lean` over ordinary descent and 01a | Supported compatible-subtype equivalence with application, inverse, action and sufficient/least-support laws |
| 01c ordinary — complete, uncommitted | `FreshQuantifier.lean` over Mathlib cofinite and F05 support | Ordinary filter interface, scoped notation, supplied-bound Some/Any, minimal logical hypotheses, parameter and joint-support results, classification and negative boundaries |
| 01c bundled — complete, uncommitted | `SupportedPredicateFresh.lean` over 01a and ordinary fresh quantification | Bundled fresh projection, ordinary computation, equivariance and support bound |
| Integration — complete, uncommitted | Public root, expanded audit prints, import coverage, README and article | All phase criteria and consumers pass together; no reference-library imports or new global-action conflicts |

Start with 01a for a stable public carrier; ordinary 01b and 01c proof work can
be independent of it. Neither waits for F06. Each later written plan must name
its remaining acceptance cells; splitting sessions does not silently drop them.
The approved implementation plan supplies the executable steps for this dependency model.

During implementation compile affected modules, then run:

```sh
lake build Package +Package.Tests.AxiomAudit
lake env lean Package/Tests/AxiomAudit.lean
python3 Package/Scripts/check-imports.py
lake env lean path/to/standalone-consumer.lean
git diff --check
```

Use the pinned Lean/Mathlib and the existing audit allowing only `propext`,
`Classical.choice`, `Quot.sound`. Check generic theorem signatures to expose
accidental hypotheses. Consumers must use the generated facts in their conclusions;
expected failures should be proved obstructions or bounded guarded diagnostics.
Keep the author's existing policy reserving persistent Package usage examples
for case studies; research probes do not change that build policy.

Develop and reconcile `docs/article/sections/predicates.tex` with the proofs:
Boolean closure versus external completeness, quantification by reindexing,
ordinary descent versus support reflection, and supplied-bound Some/Any with
its logical limits. Keep representation comparisons and operational records
in research notes. Compile the article and check its hypotheses and references;
do not claim a proposed public interface implemented in the manuscript.

## 10. Review choices and remaining obligations

The author selected the direct logical record and scoped `И` notation, then
approved this full written specification on 2026-10-08. Its three phases and
complete acceptance scope are approved. There is no newly identified mathematical
prerequisite or need to revisit the F05 hybrid. The author subsequently approved
the [written implementation plan](../plans/2026-10-08-package-predicate-foundations.md)
and explicitly selected native execution, with a fresh context per numbered task.
Production authorization comes from that subsequent approval; the original
investigation and storage selection alone did not authorize it.

The probes established feasibility; Tasks 1–7 now supply the production
computation/action laws, bundled logical/quantified/family endpoints, compatible
subtype integration and public notation/coercion interface. Task 8 checked them
together with complete target/audit/article reconciliation and independent review. Finite-index universal filter
corollaries should reuse Mathlib and be checked explicitly; existential
interchange requires the stronger hypotheses above, including empty-index care.
Larger-client elaboration cost remains unmeasured; do not promise it from tiny probes.

The written-spec and plan-review gates are complete. Execute the approved plan
natively, with the final independent review at Task 8. The author explicitly
grouped Tasks 4–5 for phase 01b and Tasks 6–7 for phase 01c. Tasks 1–7 and
phases 01a–01c are complete in the working tree. Task 8, complete specification
coverage and the independent whole-change review also pass. PKG-01 is complete
and uncommitted; the current run stops before any later task.
The plan and active roadmap record their verification and external evidence.
