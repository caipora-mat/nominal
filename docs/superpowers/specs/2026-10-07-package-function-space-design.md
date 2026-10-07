# PKG-F05: function spaces and predicate inputs

Date: 2026-10-07. **Written specification and native plan approved; implementation, checks and independent review complete.**
Task: [PKG-F05](../../nominal-package-roadmap.md#pkg-f05--function-space-and-predicate-input-foundation).
Baseline: `fasapa/nominal-package`,
`32f3dba551761881409bbc7453054e214e582269`, initially clean.
F04 is complete and committed. This specification does not reopen it.
Names below express the mathematical design. The
[implementation plan](../plans/2026-10-07-package-function-space.md) fixes the
public spelling and tasks; the author approved native execution. The interfaces
are implemented; integrated checks and independent final review pass.

## 1. Intent and recommendation

Provide a mathematically reusable foundation for functions and predicate
inputs, with ordinary application, composition, fixed parameters, higher-order
use, extensionality and rewriting. Retain selected actions, independent
universes, ordinary Lean `Prop`, and evidence for individual values. Do not
assume a whole carrier nominal merely to reason about one supported element.

The approved design is a hybrid of three interoperating interfaces:

1. Ordinary functions with `SupportsMap` / finite-support certificates, and
   ordinary predicates with `SupportsPred` certificates.
2. A distinct **full function carrier** with conjugation action, so existing
   `Supports`, `FinitelySupported`, least support and freshness apply unchanged.
3. A **proof-field supported-function bundle**, for functions whose finite
   support is part of the value's contract.

The default is contextual: ordinary inputs for mathematical definitions and
theorem entry points; bundles for persistent supported outputs and nominal
higher-order parameters. Neither wrapper is a mandatory intermediate step in
ordinary application. No implicit conversion may certify an arbitrary function.

The [investigation](../../research/2026-10-07-function-space-foundations.md)
compares ordinary-only, full-object-only, bundle-only and hybrid designs, with
Mathlib/Pitts evidence and bounded probes. Ordinary-only inputs lose convenient
nominal reasoning about the function as a value; bundle-only inputs exclude
unsupported functions and arbitrary motives. The hybrid accepts the adapter
cost to preserve both mathematical scopes.

## 2. Representation and action boundary

Use independent `G : Type uG`, `A : Type uA`, `X : Type uX`,
`Y : Type uY`, `Z : Type uZ`. Proposed full carrier:

```text
FunctionObject G X Y : Type (max uX uY)
  toFun : X → Y
```

G is an explicit phantom parameter; it must not raise the carrier universe.
No action or support witness is stored in the value. Instances use the already
selected actions on X and Y. A one-field structure gives a distinct head for
typeclass search; a transparent abbreviation of `X → Y` would not isolate the
competing action. `ofFun G f` and the ordinary-function projection are inverse
as ordinary type equivalences. That equivalence is **not generally** equivariant when
the bare arrow has its ordinary pointwise action.

Install conjugation only on the distinct carrier:

```text
(g • F) x = g • F (g⁻¹ • x)
```

The construction of the action itself needs only `DivisionMonoid G` and
`MulAction G X`, `MulAction G Y`, as the probe confirms. The cancellation,
fixed-point and evaluation contracts below use `Group G`. The curry/uncurry
action equations already hold under `DivisionMonoid G`; their ordinary round
trips need no actions at all.
This separates the weakest construction hypothesis from the natural group
function-space interface. No atom properties are needed here.

Preserve bare function pointwise action, bare permutation left multiplication,
and existing selected actions. Do not install an alternative global or scoped
conjugation action on ordinary arrows. Do not install a global action or
nominality instance on `Prop`. No atom `outParam` is introduced.

`FunLike` provides coercion to ordinary functions for both function carriers.
Use named `toObject` for a bundle's projection to its full object, avoiding a
second automatic coercion route. Ordinary-to-object adapters take G or A
explicitly: phantom inference cannot reliably recover the atom sort from an
ordinary function. A function type and the selected domain/codomain actions
must be sufficient to identify each theorem's meaning without action guessing.

## 3. General group contracts

Assume `[Group G] [MulAction G X] [MulAction G Y]` and corresponding
actions on any further carriers. Export application equations and extensionality:

```text
ofFun G f x = f x
F = H ↔ ∀ x, F x = H x
(g • F) (g • x) = g • F x
g • F = F ↔ ∀ x, F (g • x) = g • F x
```

The first two require no action. Evaluation `eval (F,x) := F x` is an
equivariant ordinary function on the product. Supply it as a Mathlib
`MulActionHom` as well as its ordinary action equation; do not introduce a new
equivariant-map record. For the permutation specialization:

```text
Equivariant A f ↔ ∀ π, π • ofFun (Perm A) f = ofFun (Perm A) f
Equivariant.toMulActionHom : Equivariant A f → X →[Perm A] Y
```

The reverse adapter uses `map_smul`; ordinary application is unchanged.
The adapter is proof packaging, not an action on `MulActionHom`.

Identity, constants, composition and pairing use ordinary computational bodies:

```text
id x = x                       const y x = y
comp H F x = H (F x)            pair F H x = (F x, H x)
g • id = id
g • const y = const (g • y)
g • comp H F = comp (g • H) (g • F)
g • pair F H = pair (g • F) (g • H)
```

Composition and pairing are jointly equivariant. Constants form an equivariant
map `Y → FunctionObject G X Y`. Include ordinary identity/associativity and
projection equations sufficient to rewrite these operations. Do not add
category instances or an unrelated algebra of operators.

Full-space currying is an equivariant equivalence, without support assumptions:

```text
FunctionObject G (X × Y) Z ≃
  FunctionObject G X (FunctionObject G Y Z)
curry F x y = F (x,y)
uncurry H (x,y) = H x y
uncurry (curry F) = F           curry (uncurry H) = H
curry (g • F) = g • curry F    uncurry (g • H) = g • uncurry H
```

Reuse `Function.curry` / `Function.uncurry` and ordinary inverse laws; the new
proof obligation is compatibility with the selected conjugation actions.
All these laws include empty domains.

### Arbitrary supporting sets

For an independent bound carrier B with `[SMul G B]`, use Mathlib directly:

```text
MulAction.Supports G S (ofFun G f) ↔
  ∀ g, (∀ b ∈ S, g • b = b) → ∀ x, f (g • x) = g • f x
```

Here `S : Set B`. Do not duplicate Mathlib's support definition. Monotonicity
comes from its existing theorem. Full curry/uncurry preserve and reflect every
such bound. Support is preserved and reflected by an equivariant injection:
cancel that injection after applying its action equation. This small reusable
lemma should be shared by the bundle embedding and the curry equivalence;
it needs only scalar operations and the injection's action equation.

For transport by the same group, require `[MulAction G B]` and prove
`Supports G (g • S) (g • F) ↔ Supports G S F` by conjugating a fixer.
Reuse the previously checked generalization proof if suitable; Mathlib's
commuting-action `.smul` has a different premise. Keep this additive, without
rewriting completed F04 modules just to reorganize them.

These are sufficient-set statements. Least finite support is not contained in
every arbitrary supporting set: the complement of `{a}` supports the atom a,
yet omits a. No arbitrary-set minimality theorem is part of this design.

## 4. Finite map certificates and elementwise bounds

Take the delivered `Perm A` and selected actions, with no atom infinitude or
carrier-wide nominality unless stated. Define the ordinary-input interface by
the following contract, with a proved correspondence to object support:

```text
SupportsMap S f :=
  ∀ π, (∀ a ∈ S, π a = a) → ∀ x, f (π • x) = π • f x
FinitelySupportedMap A f := ∃ S : Finset A, SupportsMap S f
SupportsMap S f ↔ Supports S (ofFun (Perm A) f)
FinitelySupportedMap A f ↔ FinitelySupported A (ofFun (Perm A) f)
SupportsMap ∅ f ↔ Equivariant A f
```

A definition directly by the displayed equation keeps certificates readable;
prove the correspondence once, then derive the support calculus through it.
Do not create an independent least-support choice for ordinary functions.
An ordinary function may instead use its certificate's corresponding object
and the delivered `hx.support`.

Required sufficient-bound contracts:

| Input evidence | Conclusion |
| --- | --- |
| `S ⊆ T`, `SupportsMap S f` | `SupportsMap T f` |
| `SupportsMap S f` | `SupportsMap (π • S) (fun x => π • f (π⁻¹ • x))` and the converse transport equivalence |
| `SupportsMap S f`, `Supports T x` | `Supports (S ∪ T) (f x)` |
| `SupportsMap S g`, `SupportsMap T f` | `SupportsMap (S ∪ T) (g ∘ f)` |
| `Supports S y` | `SupportsMap S (Function.const X y)` |
| `SupportsMap S f`, `SupportsMap T g` | `SupportsMap (S ∪ T) (fun x => (f x,g x))` |
| `SupportsMap S F`, `Supports T p`, `F : P × X → Y` | `SupportsMap (S ∪ T) (fun x => F (p,x))` |
| `Equivariant A F`, `Supports T p` | The previous section has bound T |

Visible finite unions/image notation retains `[DecidableEq A]` and the
`Pointwise` scope where needed. Existential finite-supportedness versions need
neither global decidable equality nor infinitude: construct witnesses inside
proofs using local classical reasoning. Export the common-bound evaluation
form too, so no union is necessary when one bound already supports both inputs.

With `[Infinite A]`, the particular certificates `hf`, `hx` give:

```text
support_of (f x) ⊆ hf.support ∪ hx.support
support_of (g ∘ f) ⊆ hg.support ∪ hf.support
support_of (fun x => F (p,x)) ⊆ hF.support ∪ hp.support
hf.support = ∅ ↔ Equivariant A f
```

Here `support_of` and the function-certificate projections are explanatory
notation for the existing elementwise support operation, not new total support
functions. Include certificate agreement whenever an independently supplied
output proof appears. Evaluation freshness for a supported third value follows
from disjointness with both function and input supports; retain the atom
specialization as a corollary. These conclusions are inclusions/implications.
Application and composition can erase support.

### Exact equalities and empty domains

The following exact results have independent justifications:

- Full curry/uncurry preserve every bound and hence least support, using
  equivariance in both directions.
- Pairing into a product has support equal to the union of the two function
  supports: projections prove the reverse bounds. No nonempty-domain premise.
- `SupportsMap S (const y) ↔ Supports S y` needs `[Nonempty X]` for reflection;
  so do finite-support reflection, exact least support and injectivity of the
  constant constructor (unless a separate subsingleton hypothesis trivializes it).
  The sharp action-free injectivity statement is
  `Injective (Function.const X : Y → X → Y) ↔ Nonempty X ∨ Subsingleton Y`.
- With `[IsEmpty X]`, all maps `X → Y` coincide and are invariant, including
  constants whose values are unsupported. Their least support is empty over
  infinite atoms. No inhabitant or support proof for Y is needed for the unique
  empty-domain map.

### Context bounds as a foundation for later tooling

The author's follow-up proposes inspecting the local context and combining it
with user-provided values to obtain a sufficient support. Support need not be
inferred from the function type or minimized. F05 must accommodate that route:

```text
SupportsMap S₀ E → Supports T c →
  SupportsMap (S₀ ∪ T) (fun x => E (c,x))
```

Here c may be a nested tuple of captures, with T built from supplied bounds
for its components. If E is jointly equivariant, T alone suffices. Extra
supported values or a larger explicit bound are harmless by monotonicity.
This is the section theorem, not an additional support representation. It
requires neither least support nor whole-carrier nominality. Classical least
support remains an optional source of a bound when only existence is known.

Keep atom/action selection separate from support construction. An explicit A
or a surrounding expected acted type can select the former. The latter needs
proof that each relevant capture has the claimed bound and that the operation
respects the action. A bare local function/predicate must have a conjugation or
logical certificate; its ordinary pointwise support is not interchangeable.
An arbitrary global function or choice expression is not certified merely
because the local context has been enumerated. Taking the unknown function
itself as an uncertified capture would be circular.

F05 exports the explicit-bound and existential forms consumed by such tooling.
Later tooling may inspect elaborated local-variable identities, combine proved
capture bounds with user values, and apply registered action/support theorems.
It must expose unresolved proof obligations and preserve shadowing and action
coherence. Do not implement a context scanner, infer a least support, require
all unused locals supported, or claim a constructive formalization in F05.
Pitts' Equivariance Principle, parameter warning and choice warning (§1.5,
pp. 21–22), and Finite Support Principle (§2.5, p. 40) motivate these obligations.
Urban's supplied *Nominal Techniques in Isabelle/HOL*, §5, Definition 5,
Lemma 11 and Examples 1–2, provides a concrete precedent: free variables suggest
a bound, while swapping equations prove it. The F04 `supports_iff_swap` theorem
already supplies the connection to all pointwise-fixing finite permutations.
This supports context-first examples with explicit proofs, without selecting a
syntax scanner or importing Isabelle-specific function-space limitations.

## 5. Supported-function values

Proposed representation:

```text
SupportedMap A X Y : Type (max uX uY)
  toObject : FunctionObject (Perm A) X Y
  supported : FinitelySupported A toObject
```

Only the selected actions on X and Y are parameters; neither is assumed nominal.
The proof field stores existence, not a finite bound as data. Supply `ofFun A f hf`,
`ofSupports A f S hS`, ordinary application/coercion lemmas, `FunLike` and `@[ext]`.
For any two support proofs of the same underlying function the bundles are equal.

Conjugation restricts to this carrier using `FinitelySupported.smul`.
Reuse Mathlib's `Function.Injective.mulAction` to transfer the laws through
`toObject` after defining scalar multiplication. `SubMulAction` already provides
an alternative invariant-subset carrier/action and subtype hom. The dedicated
record is proposed for a stable function-like public interface, not to duplicate
generic restriction theory; its supported-subtype correspondence is mandatory.
The projection is an equivariant injection; prove

```text
Supports S F ↔ Supports S F.toObject ↔ SupportsMap S (fun x => F x)
Nominal A (SupportedMap A X Y)
support A F = F.supported.support                 -- Infinite A
```

These also specify the action-preserving equivalence with the supported subtype
of the full function carrier. They are not claims that every full function is
supported. Least support and freshness reuse the delivered generic interfaces.

Provide bundle identity, evaluation, composition, pairing, proof-certified
constants and parameter fixing with the same computation equations as ordinary
functions. `const y hy` accepts particular support evidence; a nominal-carrier
adapter may infer it. The empty-domain constructor must accept an arbitrary
ordinary function from an empty carrier without needing support of its values.

Evaluation is itself equivariant and therefore may be packaged as a supported
map `(SupportedMap A X Y × X) → Y`, even if X and Y are not nominal. A further
higher-order consumer still needs its own equivariance/support theorem; ordinary
function application or `List.map` does not create one automatically.

### Currying with the correct admission condition

`uncurry : SupportedMap A X (SupportedMap A Y Z) → SupportedMap A (X × Y) Z`
is unconditional under the selected actions. It is an equivariant injection,
preserves and reflects sufficient support and, over infinite atoms, preserves
least support. It does not need X, Y or Z nominal.

For `F : SupportedMap A (X × Y) Z`, export:

```text
curryAt F x hx : SupportedMap A Y Z
  where hx : FinitelySupported A x
curryAt F x hx y = F (x,y)
```

For an entire bundled curry the exact admissibility condition is

```text
sectionsSupported F := ∀ x : X,
  FinitelySupportedMap A (fun y => F (x,y))
curryWithSections F hs : SupportedMap A X (SupportedMap A Y Z)
```

The supplied proofs are irrelevant to equality. The outer curry has the same
sufficient bounds and least support as F: full curry preserves bounds, and the
equivariant inclusion of supported sections reflects them. State both round
trips, using the section certificate automatically supplied by an existing
bundled H in `curryWithSections (uncurry H) … = H`.

`[Nominal A X]` supplies `sectionsSupported F` and the convenient `curry F`.
No nominality on Y or Z is necessary. Under that premise, curry and uncurry
give an equivariant equivalence of the two supported-function carriers.
For arbitrary X, the exact equivalence is between section-admissible F and
the bundled curried functions, not the whole binary-function bundle.

Do not assert unconditional bundled curry: take unsupported p in P, nonempty
X, and the equivariant projection `(p,x) ↦ p`. Its section is the unsupported
constant p. Conversely section support is weaker than parameter support:
an invariant constant-valued F can have supported sections even at unsupported
parameters. This is why `curryWithSections` is not replaced by nominality.

## 6. Predicate inputs and the later predicate bundle

For ordinary `P : X → Prop`, with only `[MulAction (Perm A) X]`:

```text
SupportsPred S P :=
  ∀ π, (∀ a ∈ S, π a = a) → ∀ x, (P (π • x) ↔ P x)
FinitelySupportedPred A P := ∃ S : Finset A, SupportsPred S P
renamePred π P x := P (π⁻¹ • x)
```

No action on bare Prop is an implicit premise. Reuse the delivered distinct
discrete carrier to connect predicates to functions:

```text
predicateObject A P : FunctionObject (Perm A) X (Discrete A Prop)
predicateObject A P x = Discrete.mk (P x)
SupportsPred S P ↔ Supports S (predicateObject A P)
SupportsPred S P ↔ SupportsMap S (fun x => Discrete.mk (P x))
```

The ordinary type equivalence has inverse `F ↦ fun x => (F x).val`.
Propositional and function extensionality prove its round trips. Renaming
commutes with this bridge; no extra full-predicate wrapper is necessary in F05.
The predicate action agrees with explicit `arrowAction`, and the membership
equation agrees with direct image of satisfying sets. No competing Set action
is installed. This view retains ordinary proposition application and Iff
rewriting without forcing users to unwrap discrete truth values.

F05 supplies monotonicity, empty-bound invariance, transport and finite-support
existence correspondence, plus these input operations:

```text
SupportsPred S P → SupportsMap T f → SupportsPred (S ∪ T) (P ∘ f)
SupportsPred S R → Supports T p → SupportsPred (S ∪ T) (fun x => R (p,x))
```

The jointly invariant R specialization needs only the parameter bound. A
fixed-atom equality predicate is supported by `{a}` and, over infinite atoms,
has exact support `{a}` through its predicate object; it is not invariant under
a swap moving a. In an arbitrary atom type the noninvariance witness needs
another distinct atom; infinitude is a sufficient uniform premise.

A later supported-predicate bundle must offer ordinary `P x`, Iff extensionality,
proof-witness independence, inverse-precomposition action, a nominality proof
without requiring X nominal, and an action-preserving correspondence to both
supported subsets and `SupportedMap A X (Discrete A Prop)`. A direct `toFun`
record can expose the better Prop-facing interface while deriving its theory
through that correspondence. Its final storage choice is reserved for PKG-01.

PKG-01 owns full logical operations/quantification, Some/Any, arbitrary supported
families, quotient-predicate descent, and **surjective-equivariant predicate
pullback support reflection**. Generic support reflection along the injective
bundle inclusion is required here; it does not implement that later pullback
API. No global completeness instance for supported predicates is implied.
F06 owns binders/concretion/descent; later tasks own generators, automation and
recursion. Arbitrary motives remain ordinary Prop-valued functions.

## 7. Proposed phases and module boundaries

These are review units under the existing PKG-F05 ID, not new top-level tasks
or an approved implementation plan. Each phase includes exposition reconciliation.

| Phase | Proposed files under `Package/Foundations/` | Dependencies and acceptance |
| --- | --- | --- |
| F05a: group function objects | `FunctionAction.lean` | Mathlib group/action/FunLike/Hom; full conjugation carrier, coherent ordinary coercion, evaluation/composition/product/curry laws; general support equation/transport/reflection; no atom-specific theory hidden in this module |
| F05b: ordinary input certificates | `FunctionSupport.lean`, `PredicateSupport.lean` | F05a + delivered F04; finite map/predicate correspondence, elementwise bounds and fixed parameters, explicit discrete-truth bridge, unsupported boundaries; no predicate logic or quotient descent |
| F05c: supported values and admissible curry | `SupportedFunction.lean` | F05a/b + F04; nominal proof-field bundle, ext/coercion/computation laws, exact embedding support, core combinators, curryAt/curryWithSections/nominal-domain curry, empty-domain behavior |

Keep generic arbitrary-set support adapters local to the appropriate new module
unless a small shared `ActionSupport.lean` is justified during plan review.
Avoid foundational refactoring unrelated to these dependencies. Public exports
enter `Package.lean`; production imports remain free of `Nominal/`/`Instances/`.
The import checker and axiom audit must classify all new production modules.
No new global tactic, macro, function syntax, category instance, dependency,
CI job or persistent `Package/Examples` layer is required.

F05 completion requires all three phases, not just sufficient inputs to begin
a predicate experiment. PKG-01 can be planned against F05b's stable contracts;
its chosen supported-function correspondence also uses F05c. F06 must name the
part of this interface it actually uses. Neither later task is completed here.

## 8. Acceptance matrix and verification

| Check | What it must establish |
| --- | --- |
| Action separation | Conjugation fixes identity; a nontrivial atom swap changes the ordinary pointwise identity; bare arrow computation remains `rfl` |
| Ordinary use | Application and `List.map` for both ordinary/certified inputs and bundles; `rw` through coercions; `ext x` and nested `ext x y`; no certificate unfolding |
| Universes/inference | Symbolically independent atom/domain/codomain universes; simultaneous distinct atom sorts; explicit A/G at ambiguous adapter boundaries |
| Higher order | Nominal evaluation and a returned supported section; support theorem uses generated evidence; arbitrary ordinary higher-order consumers get no automatic support claim |
| Elementwise generality | Fixed-parameter and evaluation consumers with no carrier-wide nominal instances; one supplied certificate actually used |
| Curry | Full equivariant round trips; supported curry with section evidence and with nominal X; projection refutes the unconditional version |
| Empty domains | Unique empty-domain function supported without supported codomain values; constant reflection/exact support/injectivity require nonemptiness |
| Predicate boundary | Ordinary Iff use, explicit discrete-truth correspondence, fixed-atom equality supported but not equivariant; no Prop instance search |
| Negative mathematics | Infinite/coinfinite predicate unsupported; no supported global finite-set fresh selector; complement-of-singleton arbitrary-set support counterexample |
| Computability | Ordinary computable bodies remain computable with classical least-support witnesses confined to proof fields; evaluate a concrete constructor |
| Trust | Inspect representative declaration signatures and `#print axioms`; production audit allows only `propext`, `Classical.choice`, `Quot.sound` |

During future implementation compile affected modules, then run
`lake build Package +Package.Tests.AxiomAudit`, the direct audit,
`python3 Package/Scripts/check-imports.py`, and `git diff --check`.
Compile standalone consumers explicitly and compile the article. Record actual
checks and cache conditions in the roadmap; no command here is a claim it ran.
Current research probe results and limitations are recorded separately in the
investigation. Do not promote a scratch representation solely because it compiles.

## 9. Article, risks and review boundary

`docs/article/sections/functions.tex` explains group function spaces, evaluation,
fixed parameters, the supported-curry obstruction, ordinary predicates and the
choice boundary. It states standard mathematics with proof ideas and precise
Pitts references, independently of unimplemented Lean declarations. Unresolved
representation alternatives and engineering evidence stay in research notes.

Material risks are adapter proliferation, ambiguous atom inference, competing
coercion paths, and accidentally overstating supported curry. The specified
single coercion route, explicit atom arguments, proof-field correspondence and
section-admissibility tests address them. Simp should reduce applications and
coercions to ordinary operations; reverse conversion laws stay named rather
than creating rewrite loops. No performance conclusion follows from these
small elaboration probes.

The author approved the hybrid's scope and contextual default, supported values
in F05c, and deferral of final supported-predicate storage to PKG-01 on
2026-10-07. The [implementation plan](../plans/2026-10-07-package-function-space.md)
now specifies the module split, public names, consuming checks and execution
sequence. Its extra ActionSupport module is the small shared adapter boundary
permitted by §7; it does not reopen delivered F04.

The author subsequently approved the written implementation plan and selected
native execution before production changes. The implementation and integrated
checks and independent final review are complete with no findings. The two
new proof predicates FinitelySupportedMap and SectionsSupported use reducible
aliases after literal-evidence simp consumers demonstrated the need. Their
mathematical contracts are unchanged. All changes remain uncommitted.
