# Discrete permutation sets: structure, definition and Mathlib reuse

Date: 2026-10-05. Research for PKG-F01/PKG-F03a and the concurrent PKG-11
article. The investigation retained the `Discrete` structure. A subsequent
authorized refactor briefly used `MulAction.ofEndHom 1`, but the author then
requested the original explicit action record for readability. That record is
restored; the carrier and public theorem statements are unchanged. This is not
a delivery of F04 support theory.

## Mathematical object before representation

`Discrete A X` encodes the **discrete `Perm(A)`-set on X**, written Δ_A(X):
its underlying set is X and every permutation acts as the identity. A one-field
Lean structure uses a canonically bijective copy of that underlying set; a
regular type-tag definition keeps definitional equality with X. Both represent
the same mathematical construction.

Every orbit is a singleton. The empty set supports every element, and is
therefore its least support. These are mathematical consequences, not a claim
that the new Package already implements general support or freshness. If X
already has another action, Δ_A(X) forgets that action and assigns the trivial
one. It is not the fixed-point subset or the orbit quotient. Wrap/unwrap are
ordinary set bijections, not generally equivariant to X's original action.

Primary reference: Pitts, *Nominal Sets*, CUP **2013**, Example **1.5** in §1.2,
printed **p.15**, and Example **2.5** in §2.1, printed **p.30**. These were
checked in the local PDF (PDF pages 31 and 46; publication date from page 6).
The `val` field is the implementation's underlying-value projection; its name
adds no mathematics, and one field does not mean one inhabitant.

## Recommendation

**Retain the structure for the current action-facing interface.** A regular
`def` is a valid and useful alternative, not intrinsically incoherent. It gives
substantial direct reuse of values, predicates, functions and containers.
However, action selection on existing expressions can preserve their inferred
raw type despite a type ascription. Predictable use therefore still needs named
tagging/untagging functions, or explicit typed binders/instance arguments.
The current structure makes that boundary mandatory.

**Available Mathlib construction; explicit record retained.** Independently of the carrier
choice, the existing `MulAction.ofEndHom 1` supplies exactly the trivial action.
A compiled probe established equality by `rfl` with the original handwritten
Package action record. The author preferred the original direct description
`smul _ d := d` and its two `rfl` laws, so the production implementation retains
that record. The Mathlib alternative remains verified research evidence, not
the selected encoding. No new dependency or public theorem is introduced.

**Do not replace the structure with an `abbrev` plus a global trivial-action
instance.** The isolated abbreviation probe changes the selected action on bare
atoms and arbitrary carriers, while Mathlib's higher-priority group self-action
still wins on the tagged group. This demonstrates inappropriate instance
selection, not an observed incoherence between SMul and MulAction.

Revisit the structure/def choice if a case study demonstrates that the
container-adaptation cost outweighs the explicit action boundary. No runtime or
elaboration-performance advantage was measured or claimed.

## What the tests establish

| Concern | Regular def tag | Current structure |
| --- | --- | --- |
| Generic tagged variables use trivial action | Passed | Passed |
| Bare atoms/groups/functions retain their canonical actions | Passed | Passed |
| Abstract bare carriers do not gain action/support instances | Guarded rejection passed | Guarded action rejection passed |
| Atom/carrier universes and two atom carriers | Passed, carrier stays `Type v` | Passed, carrier stays `Type v` |
| SMul/MulAction coherence for tested carrier shapes | Definitionally equal | Definitionally equal |
| Wrap/unwrap round trips | `rfl` | `rfl` already |
| Reuse ordinary values/functions/predicates/containers | Direct term reuse by definitional equality | Explicit constructor/projection, composition or container map |
| Reuse across phantom atom labels A/B | Definitionally possible; does not grant the other label's action instance | Requires explicit reconstruction |
| Inhabited/DecidableEq inherited automatically | No; explicit forwarding works | No in current minimal interface; explicit instances can be supplied |
| Bare type ascription guarantees the intended action | No | A raw value is rejected until wrapped |
| Deliberate local replacement of the tagged action | Possible | Also possible; a structure cannot prevent explicit instance replacement |
| Prototype empty support under selected action | Passed | Passed; neither probe supplies least-support theory |

The asymmetry of type ascription was checked in both directions:

```lean
-- For a regular def D A X := X and its registered trivial action:
π • (x : D A A) = π x    -- x was introduced as x : A
π • (d : A) = d          -- d was introduced as d : D A A
```

At `A = Bool`, swapping false/true genuinely moves `(false : D Bool Bool)` in
the tested expression. Adding scalar and result type annotations does not fix
that example. `D.mk false`, a Mathlib-style identity-valued equivalence applied
to false, its inverse, and explicitly targeted `SMul.smul` do select the tagged
action. This finite carrier is legitimate for the F03a action layer; no
infinitude premise is being dropped from a support-intersection theorem.

An existing raw pair or raw finite singleton shows the same behavior. A pair
literal with an expected tagged component type can instead receive tagged
actions. Named container conversions and typed local binders resolve the tested
cases. Reusing an already elaborated function preserves the operations selected
in its body; changing a definitionally equal apparent function type does not
re-elaborate that body.

Even arithmetic illustrates the distinction: for `d : Alias A Nat`, both
`d + 1` and `(d : Nat) + 1` fail without an addition instance on Alias. A named
`fromAlias d + 1` or a local `let n : Nat := d` works. The benefit of a regular
def is therefore ordinary term compatibility, not automatic transfer of all
operations and typeclasses.

## Source investigation and existing Mathlib concepts

Pinned environment: repository HEAD
`76966b1f2e44f594517442b6572e33abaa9038e0` plus the completed uncommitted F02/F03a
increment; Lean **4.34.1**, compiler commit
`5045d0056413266e57c625dcd7c365b10e377c52`; Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`. Source paths below refer to that
installed compiler or pinned Mathlib, not a moving branch.

| Source/declaration | Mathematical or engineering role | Disposition |
| --- | --- | --- |
| `Mathlib/Algebra/Group/Action/End.lean:159`, `MulAction.ofEndHom` | An action from a homomorphism into endomorphisms; the trivial homomorphism produces the discrete action | Verified alternative; the author retained the direct record for readability. The module is already imported. |
| Same file, `MulAction.toEndHom` | The endomorphism representation of an existing action | Reuse when this representation is needed; no parallel construction required |
| `CategoryTheory/Action/Basic.lean:73`, `Action.trivial` | Bundled trivial action on an object | Existing exact mathematical construction; unnecessary categorical interface for this boundary |
| `CategoryTheory/Action/Concrete.lean:211`, `Action.instMulAction` | Converts a concrete bundled action to ordinary MulAction | Available route, but imports more categorical infrastructure than ofEndHom |
| `Algebra/Group/TypeTags/Basic.lean:42–57`, Additive/Multiplicative | Regular-def carrier tags with explicit conversion equivalences and transferred instances | Valid precedent for the def alternative |
| `Order/OrderDual.lean:23–37`, OrderDual | Opposite order; regular-def carrier, explicit conversions recommended | Confirms that definitional equality does not remove the need for API discipline |
| `CategoryTheory/Discrete/Basic.lean:48–58`, Discrete | Discrete category, represented by a structure to control API leakage | Structure precedent only; different mathematical concept from a discrete permutation set |
| `Algebra/Opposites.lean:48–65`, PreOpposite/MulOpposite | Opposite multiplication with a structure wrapper | Further evidence that Mathlib uses both encodings deliberately |
| `GroupTheory/GroupAction/Defs.lean`, MulAction.fixedPoints | Fixed elements of an already selected action | Existing property vocabulary: triviality is fixedPoints = Set.univ; not a carrier tag |

Targeted searches of the pinned Mathlib found no matching general-purpose
unbundled carrier tag such as `WithTrivialAction` or `TrivMulAction`. This is a
statement about the searched interface, not absence of the mathematics.
`CategoryTheory.Discrete` must not be reused solely because its name matches.

Compiler evidence: `Lean/Elab/DefView.lean:140–145` marks abbreviations reducible;
`Lean/ReducibilityAttrs.lean:31–33` gives ordinary definitions semireducibility;
`Lean/Meta/SynthInstance.lean:958–964` selects instances transparency.
`Lean/Meta/Basic.lean:1319–1324` and `Init/MetaTypes.lean:51–66` explain that
this mode does not unfold semireducible carrier tags. This verifies why a
regular def can separate instance search even while default definitional
checking equates its carrier with X.

The official [instance-synthesis reference](https://lean-lang.org/doc/reference/latest/Type-Classes/Instance-Synthesis/)
and [reducibility reference](https://lean-lang.org/doc/reference/latest/Definitions/Recursive-Definitions/)
were also consulted on 2026-10-05 for the general explanation. They are rolling
references; installed 4.34.1 source and local probes govern exact transparency
claims. The attempted versioned 4.34.0 instance-synthesis URL was unavailable.
No external dependency download or toolchain change was needed.

## Reproduction and limits

All five files below passed direct `lake env lean` checks using existing built
imports. Expected failures are guarded. Representative printed axioms are only
`propext`, `Classical.choice`, `Quot.sound`, or subsets (some conversion results
have no axioms). These are independent scratch experiments, not new Package
modules or persistent case-study examples. They do not implement F04, replace
Discrete, or prove compatibility with every future class/elaborator context.
The briefly applied action-instance refactor was reverted at the author's request,
as recorded above. All original probes are preserved; follow-up verification is
recorded in the roadmap.

The exact source blocks retain reproducibility without depending on `/tmp`
persistence. Extract each block to its named file and run its command from the
repository root. The abbreviation experiment must remain in a separate
compilation unit because it deliberately registers a blanket action instance.


### Regular-def action separation

Command: `lake env lean /tmp/nominal-discrete-actions-20261005/DefAction.lean`.

SHA-256: `26703c82e76a09dcc5d30e4595f0e9fbe2cbaf7d332e9236814428f09f2cce35`.

```lean
import Package.Foundations.Action
import Mathlib.GroupTheory.GroupAction.Support
import Mathlib.Algebra.Group.Action.Pi

namespace DefActionProbe
open NominalPackage
universe u v w z

def D (_A : Type u) (X : Type v) : Type v := X
namespace D
instance instMulAction (A : Type u) (X : Type v) : MulAction (Perm A) (D A X) where
  smul _ x := x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

def mk {A : Type u} {X : Type v} (x : X) : D A X := x
def val {A : Type u} {X : Type v} (x : D A X) : X := x
end D

namespace D
@[implicit_reducible]
def of {A : Type u} {X : Type v} : X ≃ D A X :=
  ⟨fun x => x, fun x => x, fun _ => rfl, fun _ => rfl⟩
@[implicit_reducible]
def equiv (A : Type u) (X : Type v) : D A X ≃ X := of.symm
end D

/-- error: failed to synthesize instance of type class
  MulAction (Perm A) X

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command. -/
#guard_msgs in
example (A : Type u) (X : Type v) : MulAction (Perm A) X := inferInstance

/-- error: failed to synthesize instance of type class
  SMul (Perm A) X

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command. -/
#guard_msgs in
example (A : Type u) (X : Type v) : SMul (Perm A) X := inferInstance

/-- error: failed to synthesize instance of type class
  MulAction (Perm B) (D A X)

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command. -/
#guard_msgs in
example (A : Type u) (B : Type v) (X : Type w) : MulAction (Perm B) (D A X) := inferInstance

-- Independent atom/carrier universes and preservation of carrier universe.
example (A : Type u) (X : Type v) : Type v := D A X
example (A : Type u) (X : Type v) (π : Perm A) (x : D A X) : π • x = x := rfl
example (A : Type u) (π : Perm A) (x : A) : π • x = π x := rfl
example (A : Type u) (π : Perm A) (x : D A A) : π • x = x := rfl
example (A : Type u) (π σ : Perm A) : π • σ = π * σ := rfl
example (A : Type u) (π : Perm A) (σ : D A (Perm A)) : π • σ = σ := rfl
example (A : Type u) (X : Type v) (π : Perm A) (f : X → A) (x : X) :
    (π • f) x = π (f x) := rfl
example (A : Type u) (X : Type v) (π : Perm A) (f : D A (X → A)) :
    π • f = f := rfl

-- The same ordinary carrier may be separately tagged with unrelated atom types.
example (A : Type u) (B : Type v) (X : Type w) (π : Perm A) (σ : Perm B)
    (x : D A X) (y : D B X) : (π • x, σ • y) = (x, y) := rfl
example (A : Type u) (X : Type v) (Y : Type w) (π : Perm A)
    (a : A) (x : D A X) (y : D A Y) :
    π • (a, (x, y)) = (π a, (x, y)) := rfl

-- Both forms of selected action agree definitionally at the tested generic types.
example (A : Type u) (X : Type v) :
    (inferInstance : SMul (Perm A) (D A X)) =
    (inferInstance : MulAction (Perm A) (D A X)).toSMul := rfl
example (A : Type u) :
    (inferInstance : SMul (Perm A) A) =
    (inferInstance : MulAction (Perm A) A).toSMul := rfl
example (A : Type u) :
    (inferInstance : SMul (Perm A) (Perm A)) =
    (inferInstance : MulAction (Perm A) (Perm A)).toSMul := rfl
example (A : Type u) (X : Type v) :
    (inferInstance : SMul (Perm A) (X → A)) =
    (inferInstance : MulAction (Perm A) (X → A)).toSMul := rfl

-- Runtime distinction is witnessed by a nonidentity finite permutation.
theorem bare_bool_moves : Perm.swap false true • false = true := by
  change Perm.swap false true false = true
  exact Perm.swap_apply_left false true

theorem tagged_bool_fixed : Perm.swap false true • D.mk (A := Bool) false = false := rfl

theorem actions_differ :
    (Perm.swap false true • false : Bool) ≠
    (Perm.swap false true • D.mk (A := Bool) false : D Bool Bool) := by
  rw [bare_bool_moves, tagged_bool_fixed]
  decide

-- Tagged values accept bare inputs by definitional equality, not a registered coercion.
def acceptTagged {A : Type u} {X : Type v} (x : D A X) : X := x
example (A : Type u) (X : Type v) (x : X) : acceptTagged (A := A) x = x := rfl
example (A : Type u) (X : Type v) (x : D A X) : (id : X → X) x = x := rfl

-- An elaborated term retains its inferred type; an ascription need not insert a tag.
theorem bare_ascription (A : Type u) (π : Perm A) (x : A) :
    π • (x : D A A) = π x := rfl

theorem tagged_ascription (A : Type u) (π : Perm A) (x : D A A) :
    π • (x : A) = x := rfl

theorem scalar_and_result_ascription (π : Perm Bool) :
    ((π : Perm Bool) • (false : D Bool Bool) : D Bool Bool) = π false := rfl

theorem typed_literal_still_moves :
    (Perm.swap false true • (false : D Bool Bool) : D Bool Bool) ≠ false := by
  change Perm.swap false true false ≠ false
  rw [Perm.swap_apply_left]
  decide

theorem explicit_smul_parameter (π : Perm Bool) :
    @SMul.smul (Perm Bool) (D Bool Bool) inferInstance π false = false := rfl

theorem equiv_constructor_fixed (π : Perm Bool) :
    π • D.of (A := Bool) false = D.of (A := Bool) false := rfl

theorem equiv_inverse_fixed (π : Perm Bool) :
    π • (D.equiv Bool Bool).symm false = (D.equiv Bool Bool).symm false := rfl

-- Bare local actions do not alter the D-tagged instance under ordinary synthesis.
example (A : Type u) (X : Type v) [MulAction (Perm A) X]
    (π : Perm A) (x : D A X) : π • x = x := rfl
example (A : Type u) (X : Type v) [SMul (Perm A) X]
    (π : Perm A) (x : D A X) : π • x = x := rfl
example (A : Type u) (X : Type v) [inst : MulAction (Perm A) (D A X)] :
    (inferInstance : SMul (Perm A) (D A X)) = inst.toSMul := rfl

-- Deliberately supplying a local tagged action changes it, as it can for a structure.
@[instance_reducible]
def movingTagged (A : Type u) : MulAction (Perm A) (D A A) where
  smul π x := π x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

theorem local_tagged_override (A : Type u) (π : Perm A) (x : D A A) :
    letI := movingTagged A
    π • x = π x := rfl

-- This behavior does not depend on a nonempty or infinite atom/carrier.
example (π : Perm Empty) (x : D Empty Nat) : π • x = x := rfl
example (π : Perm Unit) (x : D Unit Empty) : π • x = x := rfl
example (π : Perm Empty) (x : D Empty Unit) : π • x = x := rfl
example (A : Type u) (_π : Perm A) (x : D A Empty) : False := Empty.elim x

-- Finite-support evidence is indexed by the selected action; no least-support operation.
class FinSupported (A : Type u) (X : Type v) [MulAction (Perm A) X] : Prop where
  finite_support : ∀ x : X, ∃ S : Set A, S.Finite ∧ MulAction.Supports (Perm A) S x

instance (A : Type u) (X : Type v) : FinSupported A (D A X) where
  finite_support _x := ⟨∅, Set.finite_empty, fun _ _ => rfl⟩

theorem discrete_empty_support (A : Type u) (X : Type v) (x : D A X) :
    MulAction.Supports (Perm A) (∅ : Set A) x := fun _ _ => rfl

theorem bare_bool_not_empty_support :
    ¬ MulAction.Supports (Perm Bool) (∅ : Set Bool) false := by
  intro h
  have hfix := h (Perm.swap false true) (by simp)
  have hmove : Perm.swap false true • false = true := bare_bool_moves
  rw [hmove] at hfix
  cases hfix

-- Support's inferred carrier follows the same ascription behavior.
theorem bare_ascription_not_empty_support :
    ¬ MulAction.Supports (Perm Bool) (∅ : Set Bool) (false : D Bool Bool) :=
  bare_bool_not_empty_support

theorem constructor_has_empty_support :
    MulAction.Supports (Perm Bool) (∅ : Set Bool) (D.mk (A := Bool) false) :=
  discrete_empty_support Bool Bool _

/-- error: failed to synthesize instance of type class
  FinSupported A X

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command. -/
#guard_msgs in
example (A : Type u) (X : Type v) [MulAction (Perm A) X] : FinSupported A X := inferInstance

#print axioms actions_differ
#print axioms typed_literal_still_moves
#print axioms equiv_constructor_fixed
#print axioms local_tagged_override
#print axioms discrete_empty_support
#print axioms bare_bool_not_empty_support
#print axioms bare_ascription_not_empty_support
#print axioms constructor_has_empty_support

end DefActionProbe
```

### Structure comparison

Command: `lake env lean /tmp/nominal-discrete-actions-20261005/StructureAction.lean`.

SHA-256: `ea989f839afac429334d3c335018c69e51bcb6de6a2f9f10b6d34decf7174ad4`.

```lean
import Package.Foundations.Action
import Mathlib.GroupTheory.GroupAction.Support
import Mathlib.Algebra.Group.Action.Pi

namespace StructureActionProbe
open NominalPackage
universe u v w

/-- error: failed to synthesize instance of type class
  MulAction (Perm A) X

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command. -/
#guard_msgs in
example (A : Type u) (X : Type v) : MulAction (Perm A) X := inferInstance

/-- error: failed to synthesize instance of type class
  SMul (Perm A) X

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command. -/
#guard_msgs in
example (A : Type u) (X : Type v) : SMul (Perm A) X := inferInstance

/-- error: failed to synthesize instance of type class
  MulAction (Perm B) (Discrete A X)

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command. -/
#guard_msgs in
example (A : Type u) (B : Type v) (X : Type w) : MulAction (Perm B) (Discrete A X) := inferInstance

-- The production structure is the baseline; there is no replacement declaration here.
example (A : Type u) (X : Type v) : Type v := Discrete A X
example (A : Type u) (π : Perm A) (a : A) : π • a = π a := rfl
example (A : Type u) (X : Type v) (π : Perm A) (x : Discrete A X) : π • x = x := rfl
example (A : Type u) (π σ : Perm A) : π • σ = π * σ := rfl
example (A : Type u) (π : Perm A) (σ : Discrete A (Perm A)) : π • σ = σ := rfl
example (A : Type u) (X : Type v) (π : Perm A) (f : X → A) (x : X) :
    (π • f) x = π (f x) := rfl
example (A : Type u) (X : Type v) (π : Perm A) (f : Discrete A (X → A)) :
    π • f = f := rfl
example (A : Type u) (B : Type v) (X : Type w) (π : Perm A) (σ : Perm B)
    (x : Discrete A X) (y : Discrete B X) : (π • x, σ • y) = (x, y) := rfl
example (A : Type u) (X : Type v) (Y : Type w) (π : Perm A)
    (a : A) (x : Discrete A X) (y : Discrete A Y) :
    π • (a, (x, y)) = (π a, (x, y)) := rfl
example (A : Type u) (X : Type v) [MulAction (Perm A) X]
    (π : Perm A) (x : Discrete A X) : π • x = x := rfl
example (A : Type u) (X : Type v) [SMul (Perm A) X]
    (π : Perm A) (x : Discrete A X) : π • x = x := rfl

example (A : Type u) (X : Type v) :
    (inferInstance : SMul (Perm A) (Discrete A X)) =
    (inferInstance : MulAction (Perm A) (Discrete A X)).toSMul := rfl
example (A : Type u) :
    (inferInstance : SMul (Perm A) A) =
    (inferInstance : MulAction (Perm A) A).toSMul := rfl
example (A : Type u) :
    (inferInstance : SMul (Perm A) (Perm A)) =
    (inferInstance : MulAction (Perm A) (Perm A)).toSMul := rfl
example (A : Type u) (X : Type v) :
    (inferInstance : SMul (Perm A) (X → A)) =
    (inferInstance : MulAction (Perm A) (X → A)).toSMul := rfl

example (π : Perm Empty) (x : Discrete Empty Nat) : π • x = x := rfl
example (π : Perm Unit) (x : Discrete Unit Empty) : π • x = x := rfl
example (π : Perm Empty) (x : Discrete Empty Unit) : π • x = x := rfl
example (A : Type u) (x : Discrete A Empty) : False := Empty.elim x.val

def acceptTagged {A : Type u} {X : Type v} (x : Discrete A X) : X := x.val

/-- error: Application type mismatch: The argument
  false
has type
  Bool
but is expected to have type
  Discrete Bool ?m.1
in the application
  acceptTagged false -/
#guard_msgs (error, drop info) in
#check acceptTagged (A := Bool) false

theorem named_constructor_fixed (π : Perm Bool) :
    π • Discrete.mk false = (Discrete.mk false : Discrete Bool Bool) := rfl

theorem different_atom_actions :
    (Perm.swap false true • false : Bool) ≠
    (Perm.swap false true • (Discrete.mk false : Discrete Bool Bool)).val := by
  change Perm.swap false true false ≠ false
  rw [Perm.swap_apply_left]
  decide

@[instance_reducible]
def movingTagged (A : Type u) : MulAction (Perm A) (Discrete A A) where
  smul π x := ⟨π x.val⟩
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

theorem local_tagged_override (A : Type u) (π : Perm A) (x : Discrete A A) :
    letI := movingTagged A
    π • x = Discrete.mk (π x.val) := rfl

class FinSupported (A : Type u) (X : Type v) [MulAction (Perm A) X] : Prop where
  finite_support : ∀ x : X, ∃ S : Set A, S.Finite ∧ MulAction.Supports (Perm A) S x

instance (A : Type u) (X : Type v) : FinSupported A (Discrete A X) where
  finite_support _x := ⟨∅, Set.finite_empty, fun _ _ => rfl⟩

theorem discrete_empty_support (A : Type u) (X : Type v) (x : Discrete A X) :
    MulAction.Supports (Perm A) (∅ : Set A) x := fun _ _ => rfl

#print axioms different_atom_actions
#print axioms discrete_empty_support
#print axioms local_tagged_override
end StructureActionProbe
```

### Abbreviation counterexample

Command: `lake env lean /tmp/nominal-discrete-actions-20261005/AbbrevAction.lean`.

SHA-256: `d0118d10c53d0c3573533ebe1fc6ed63ad05c54e270649aec8394b8d85644efd`.

```lean
import Package.Foundations.Action
import Mathlib.Algebra.Group.Action.Pi

namespace AbbrevActionProbe
open NominalPackage
universe u v w

-- Kept in a separate compilation unit: this instance intentionally leaks to bare X.
abbrev D (_A : Type u) (X : Type v) : Type v := X
instance dAction (A : Type u) (X : Type v) : MulAction (Perm A) (D A X) where
  smul _ x := x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

theorem arbitrary_carrier_fixed (A : Type u) (X : Type v) (π : Perm A) (x : X) :
    π • x = x := rfl

theorem bare_atom_fixed (A : Type u) (π : Perm A) (x : A) : π • x = x := rfl

theorem tagged_atom_fixed (A : Type u) (π : Perm A) (x : D A A) : π • x = x := rfl

theorem bare_atom_action_changed :
    (Perm.swap false true • false : Bool) ≠ Perm.swap false true false := by
  change false ≠ Perm.swap false true false
  rw [Perm.swap_apply_left]
  decide

-- The higher-priority group-self action still wins over this particular blanket instance.
theorem bare_group_mult (A : Type u) (π σ : Perm A) : π • σ = π * σ := rfl

theorem tagged_group_mult (A : Type u) (π : Perm A) (σ : D A (Perm A)) :
    π • σ = π * σ := rfl

theorem tagged_group_not_discrete :
    Perm.swap false true • (1 : D Bool (Perm Bool)) ≠ 1 := by
  change Perm.swap false true * 1 ≠ 1
  intro h
  have h' := congrArg (fun σ : Perm Bool => σ false) h
  simp at h'

-- Ordinary functions have also changed: their codomain atom action is now trivial.
theorem bare_function_fixed (A : Type u) (X : Type v) (π : Perm A) (f : X → A) :
    π • f = f := rfl

theorem tagged_function_fixed (A : Type u) (X : Type v) (π : Perm A)
    (f : D A (X → A)) : π • f = f := rfl

-- Phantom atom labels impose no action-selection distinction after abbreviation reduction.
theorem wrong_label_accepted (A : Type u) (B : Type v) (X : Type w)
    (π : Perm B) (x : D A X) : π • x = x := rfl

example (A : Type u) :
    (inferInstance : SMul (Perm A) (Perm A)) =
    (inferInstance : MulAction (Perm A) (Perm A)).toSMul := rfl
example (A : Type u) (X : Type v) :
    (inferInstance : SMul (Perm A) (X → A)) =
    (inferInstance : MulAction (Perm A) (X → A)).toSMul := rfl

#print axioms bare_atom_action_changed
#print axioms tagged_group_not_discrete
#print axioms bare_function_fixed
end AbbrevActionProbe
```

### Ordinary-use and container comparison

Command: `lake env lean /tmp/DiscreteUsabilityProbe.lean`.

SHA-256: `dd55187835910c762f19ead65ed274fb0f44274c0719fc9e16ff92ee362dddef`.

```lean
import Package.Foundations.Action
import Mathlib.Data.Finset.Basic

namespace DiscreteUsabilityProbe

universe u v w z

def Alias (_A : Type u) (X : Type v) : Type v := X

variable {A : Type u} {B : Type w} {X : Type v} {Y : Type z}

def toAlias (x : X) : Alias A X := x
def fromAlias (d : Alias A X) : X := d

theorem alias_roundtrip (d : Alias A X) : toAlias (fromAlias d) = d := rfl
theorem carrier_roundtrip (x : X) : fromAlias (toAlias (A := A) x) = x := rfl

example (x : X) : Alias A X := x
example (d : Alias A X) : X := d
example (d : Alias A X) : Alias B X := d

example (f : X → Y) : Alias A X → Y := f
example (P : X → Prop) : Alias A X → Prop := P
example (f : X → Y) (d : Alias A X) : f d = f (fromAlias d) := rfl
example (f : X → Y) (x : X) : (f : Alias A X → Y) x = f x := rfl

def aliasLet (d : Alias A Nat) : Nat := let n : Nat := d; n + 1
def aliasMatch (d : Alias A (Option X)) : Option X :=
  match d with
  | none => none
  | some x => some x

example (d : Alias A Nat) : aliasLet d = fromAlias d + 1 := rfl
example (d : Alias A Nat) : Nat := by
  fail_if_success exact d + 1
  fail_if_success exact (d : Nat) + 1
  exact fromAlias d + 1
example (x : X) : aliasMatch (A := A) (some x) = some x := rfl

example (d : Alias A X) (x : X) (h : d = x) (f : X → Y) : f d = f x := by rw [h]
example (f g : Alias A X → Y) (h : ∀ x : X, f x = g x) : f = g := by
  ext x
  exact h x

example (p : X × Y) : Alias A X × Alias A Y := p
example (xs : List X) : List (Alias A X) := xs
example (xs : List X) (f : X → Y) : List.map (f : Alias A X → Y) xs = xs.map f := rfl
example (s : Finset X) : Finset (Alias A X) := s

example [Inhabited X] : Inhabited (Alias A X) := by
  fail_if_success exact inferInstance
  exact inferInstanceAs (Inhabited X)

example [DecidableEq X] : DecidableEq (Alias A X) := by
  fail_if_success exact inferInstance
  exact inferInstanceAs (DecidableEq X)

example : Inhabited (Alias Nat Nat) := by
  fail_if_success exact inferInstance
  exact inferInstanceAs (Inhabited Nat)

example : DecidableEq (Alias Nat Nat) := by
  fail_if_success exact inferInstance
  exact inferInstanceAs (DecidableEq Nat)

section ForwardedInstances

local instance aliasInhabited [Inhabited X] : Inhabited (Alias A X) :=
  inferInstanceAs (Inhabited X)
local instance aliasDecidableEq [DecidableEq X] : DecidableEq (Alias A X) :=
  inferInstanceAs (DecidableEq X)

example [Inhabited X] : (default : Alias A X) = (default : X) := rfl
example [DecidableEq X] (x : X) (s : Finset X) :
    decide ((x : Alias A X) ∈ (s : Finset (Alias A X))) = decide (x ∈ s) := rfl

end ForwardedInstances

example [Inhabited X] : Inhabited (NominalPackage.Discrete A X) := by
  fail_if_success exact inferInstance
  exact ⟨⟨default⟩⟩

example [DecidableEq X] : DecidableEq (NominalPackage.Discrete A X) := by
  fail_if_success exact inferInstance
  intro a b
  exact decidable_of_iff (a.val = b.val) (by cases a; cases b; simp)

theorem structure_roundtrip (d : NominalPackage.Discrete A X) :
    NominalPackage.Discrete.mk d.val = d := rfl

example (x : X) : NominalPackage.Discrete A X := by
  fail_if_success exact x
  exact ⟨x⟩

example (d : NominalPackage.Discrete A X) : X := by
  fail_if_success exact d
  exact d.val

example (d : NominalPackage.Discrete A X) : NominalPackage.Discrete B X := by
  fail_if_success exact d
  exact ⟨d.val⟩

example (f : X → Y) : NominalPackage.Discrete A X → Y := by
  fail_if_success exact f
  exact fun d => f d.val

example (P : X → Prop) : NominalPackage.Discrete A X → Prop := by
  fail_if_success exact P
  exact fun d => P d.val

example (d : NominalPackage.Discrete A X) :
    (match d with | ⟨x⟩ => x) = d.val := rfl

example (d e : NominalPackage.Discrete A X) (h : d.val = e.val) : d = e := by
  cases d
  cases e
  cases h
  rfl

example (f g : NominalPackage.Discrete A X → Y) (h : ∀ x : X, f ⟨x⟩ = g ⟨x⟩) :
    f = g := by
  ext d
  exact h d.val

example (p : X × Y) : NominalPackage.Discrete A X × NominalPackage.Discrete A Y := by
  fail_if_success exact p
  exact (⟨p.1⟩, ⟨p.2⟩)

example (xs : List X) : List (NominalPackage.Discrete A X) := by
  fail_if_success exact xs
  exact xs.map NominalPackage.Discrete.mk

example (s : Finset X) : Finset (NominalPackage.Discrete A X) := by
  fail_if_success exact s
  exact s.map (NominalPackage.Discrete.equiv A X).symm.toEmbedding

section SelectedActions

open NominalPackage

instance : MulAction (Perm A) (Alias A X) where
  smul _ d := d
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

def rawRename (π : Perm Bool) : Bool → Bool := fun x => π • x
def aliasRename (π : Perm Bool) : Alias Bool Bool → Alias Bool Bool := fun x => π • x

theorem raw_function_reuse (π : Perm Bool) (x : Alias Bool Bool) :
    (rawRename π : Alias Bool Bool → Alias Bool Bool) x = π x := rfl
theorem alias_function_reuse (π : Perm Bool) (x : Bool) :
    (aliasRename π : Bool → Bool) x = x := rfl

theorem pair_literal_is_tagged :
    Perm.swap false true • ((false, false) : Alias Bool Bool × Alias Bool Bool) =
      (false, false) := rfl

theorem raw_pair_ascription_still_raw (p : Bool × Bool) (π : Perm Bool) :
    π • (p : Alias Bool Bool × Alias Bool Bool) = (π p.1, π p.2) := rfl

def toAliasPair (p : X × Y) : Alias A X × Alias A Y := p

theorem named_pair_is_tagged (π : Perm A) (p : X × Y) :
    π • toAliasPair (A := A) p = p := rfl

theorem bound_pair_is_tagged (π : Perm Bool) :
    (let p : Alias Bool Bool × Alias Bool Bool := (false, false); π • p) =
      (false, false) := rfl

open scoped Pointwise

local instance selectedAliasDecidableEq [DecidableEq X] : DecidableEq (Alias A X) :=
  inferInstanceAs (DecidableEq X)

def toAliasFinset (s : Finset X) : Finset (Alias A X) := s

theorem ascribed_finset_still_raw :
    Perm.swap false true • (({false} : Finset Bool) : Finset (Alias Bool Bool)) = {true} := by
  simp only [Finset.smul_finset_singleton, Perm.smul_atom, Perm.swap_apply_left]

theorem named_finset_is_tagged [DecidableEq X] (π : Perm A) (s : Finset X) :
    π • toAliasFinset (A := A) s = s := by
  change Finset.image (fun x : X => x) s = s
  exact Finset.image_id

end SelectedActions

#check @Alias
#check @NominalPackage.Discrete
#print axioms alias_roundtrip
#print axioms carrier_roundtrip
#print axioms structure_roundtrip
#print axioms raw_function_reuse
#print axioms alias_function_reuse
#print axioms pair_literal_is_tagged
#print axioms raw_pair_ascription_still_raw
#print axioms bound_pair_is_tagged
#print axioms ascribed_finset_still_raw
#print axioms named_finset_is_tagged

end DiscreteUsabilityProbe
```

### Direct Mathlib reuse

Command: `lake env lean /tmp/DiscreteMathlibReuse.lean`.

SHA-256: `e0ad23b23f09b9892a6d58283f9859e76f01a874f9c34e939b7f6cdae4e770ac`.

```lean
import Package
import Mathlib.GroupTheory.GroupAction.Support

namespace DiscreteMathlibReuse
open NominalPackage
universe u v

/-- The trivial homomorphism encodes the mathematical discrete action. -/
@[instance_reducible]
def viaMathlib (A : Type u) (X : Type v) : MulAction (Perm A) (Discrete A X) :=
  MulAction.ofEndHom (1 : Perm A →* Function.End (Discrete A X))

theorem same_action (A : Type u) (X : Type v) :
    viaMathlib A X = (inferInstance : MulAction (Perm A) (Discrete A X)) := rfl

theorem computation (A : Type u) (X : Type v) (π : Perm A) (d : Discrete A X) :
    letI := viaMathlib A X
    π • d = d := rfl

theorem projection (A : Type u) (X : Type v) (π : Perm A) (d : Discrete A X) :
    letI := viaMathlib A X
    (π • d).val = d.val := rfl

theorem empty_support (A : Type u) (X : Type v) (d : Discrete A X) :
    letI := viaMathlib A X
    MulAction.Supports (Perm A) (∅ : Set A) d := by
  intro π _
  rfl

#print axioms same_action
#print axioms computation
#print axioms empty_support
end DiscreteMathlibReuse
```
