# Algebraic source investigation for PKG-F01

Research draft, 2026-10-05. This is source assessment and bounded proof evidence,
not an approved implementation plan or a claim that PKG-F01 is complete.
The checkout inspected was `fasapa/nominal-package` at
`76966b1f2e44f594517442b6572e33abaa9038e0`. The existing untracked handoff and
predicate probes were preserved. This investigation creates only this note in
the repository; new Lean experiments are in `/tmp`.

Both required files were read directly with `git show` from
`983adeb9b80f75fb7c77c05acfd2fcef16db1d46`. Below, **A:L** means line L of
`Nominal/Set/Algebraic.lean` at that revision, and **S:L** means line L of
`Nominal/Set/Structural.lean` there. These are historical Git references, not
files in the current production library. Additional historical dependency
references use the same revision unless explicitly marked current.

The [earlier backend assessment](2026-10-05-backend-comparison.md) is broadly
supported by direct inspection. Its diagnoses should remain separated: several
contracts are false, some are merely weaker than their comments, many useful
mathematical ideas have no implementation, and the historical modules fail
before elaborating because their import paths are obsolete. None of these
findings requires repairing or adopting that branch.

## Source and build boundary

The sketch pins Lean and Mathlib 4.28.0. Its first imports are
`NominalSets.Structural` and `NominalSets.FCB`; the same Git tree instead has
`Nominal/Set/...` modules. Its `Nominal/Set.lean` exports neither sketch file.
The files themselves use `namespace NominalSets`, while inspected dependencies
use `Nominal.Set`. A default historical library build would therefore not certify
these sketches even if the supported umbrella compiled.

Untouched copies extracted to `/tmp/nominal-algebraic-F01-IWrzIx/` both fail
immediately under the current pinned Lean/Mathlib 4.34.1:

```text
Algebraic.lean:1:0: error: unknown module prefix 'NominalSets'
Structural.lean:1:0: error: unknown module prefix 'NominalSets'
```

This confirms the present import barrier. It is not a Lean 4.28 build result,
nor a check of all subsequent declarations. No namespace/import normalization,
historical dependency installation, checkout, merge, or repair was attempted.
The old review's normalized-file experiments remain historical evidence with
their stated limits. Source inspection shows active admitted bodies, including
the carrier, actions, maps and theorem proofs. S:10–11's claim that stub
signatures are correct is contradicted by the contracts below. The occasional
non-admitted wrapper, such as A:338–343 `foldHom`, depends on admitted results.

## Declaration findings and dispositions

Here **adopt** means retain a mathematical requirement or idea, not import
unverified code. **Adapt** means correct or strengthen the contract. **Rederive**
means prove the requirement for the selected Package representation. **Defer**
means omit it from the first lambda/FOL prerequisite chain. **Reject** applies to
the specified false contract or invalid shortcut, not automatically to its whole
mathematical subject.

### 1. Signature positions must distinguish atoms, data and recursion

**P1, false intended specification; reject `LambdaSig` as a lambda signature,
adapt the arity idea.** A:132–157 has only recursive `data`, `unit`, `prod` and
`nameAbs`; `interpSort ... .data = X`. A:183–187 and A:394–400 nevertheless use
`.data` for `var : A → Lambda`. Consequently its lambda functor is
`F(X) = X + X × X + [A]X`, with an additional empty summand from the list encoding,
and not `A + X × X + [A]X`.

For the intended nominal category, `F(Empty)` is empty: in particular `[A]Empty`
is a quotient of `A × Empty`. Empty therefore has a unique algebra structure
and a unique homomorphism to every algebra. If A:312–335 really supplies
initiality, the claimed initial carrier is empty up to isomorphism. A:417's
total atom constructor cannot then exist. The comment at A:388–391 acknowledges
the atom distinction but the actual definition at A:400 does not implement the
suggested correction. This is a mathematical contradiction in the intended
combined specifications, not merely an unfinished constructor proof.

Use distinct `Atom`, `Data(k)` and `Rec(i)` positions. Recursive functor maps
leave atoms and external data unchanged; permutations act on their nominal
values. Atom/data/unit positions supply `True` to a recursive-premise lifting,
whereas `Rec(i)` supplies the motive for child i. Test atom-only, nullary and
recursive-only signatures, then a term/formula family with different result
categories. FOL does not require multiple atom sorts: one atom sort and multiple
syntax categories are distinct requirements. The old list-of-arities encoding
is useful finite metadata, but needs constructor labels and result categories
if generalized to the agreed grammar.

### 2. The interpreter is not yet an elaborated functor or a recursive carrier

**P1, representation/elaboration obstacle; adapt staging, reject direct
semantic nesting as an assumed construction.** A:152–157 asks for
`NameAbs α (interpSort α X σ)` before supplying the recursive nominal structure;
the proposed instance is only declared at A:162–173. The `Unit`/`Empty` clauses
also need universe-correct carriers. The repeated `PermType` and `Nominal`
instances must select coherent actions; merely having an inhabitant of each
class is insufficient.

The rerun `BackendStaging.lean` supplies both carrier and nominal structure at
each recursive interpretation step and uses universe-polymorphic `PUnit`.
This checks one shared-universe repair of this local staging issue. It does not
prove that `interpSort`, `sigFunctor`, or a generic fixed point exists as written.
Bundled objects, explicit structures and a different class policy remain
available Package choices; the old `outParam` policy need not be retained.

The rerun `BackendPositivity.lean` independently guards the nominal-instance
failure for direct recursion through `NameAbs`, a kernel positivity failure
after supplying a discrete action, and the analogous failure for a minimal
`Quot` wrapper. These reject the tested declarations, not every generic or
quotient-based construction. A raw syntax/quotient construction and an actual
initial-chain construction remain alternatives with different proof costs.

### 3. Functor maps and algebra morphisms are useful precise contracts

**Missing proofs; adopt the equations, rederive maps for the chosen grammar.**
A:219–236 `sigMap` includes equivariance, identity and composition requirements.
A:245–261 `NomAlgebra` and `NomAlgebra.Hom` correctly distinguish equivariant
structure maps and equivariant homomorphisms, with the commuting equation
`h (in x) = alg (F h x)`. Their bodies and functor laws are not implemented.

The binder case should use a proved equivariant abstraction map. Historical
`Concretion.lean:475–505,535–542` already contains the relevant representative,
equivariance, uniqueness, identity and composition proofs for its own
representation. Adoption or adaptation of that dependency is possible, but it
does not certify a fresh Package representation. This map requires neither
an adjunction catalogue nor exponential sorts. Public maps need per-shape
equations, including identity on atom/data positions, and recursive composition
tests under products and two nested binders.

### 4. Initiality must use the actual constructors and specified morphisms

**P2, incomplete isomorphism contract; adapt initiality, defer a categorical
construction until the backend requires it.** A:312–335's fold, equivariance,
commutation and uniqueness describe a useful initiality property in
equivariant maps once the functor is corrected. A:293–298's `algebraIso` is
merely an equivariant type equivalence; no equation identifies its forward map
with `(InitialAlg.algebra ...).str` from A:289–290. Its name and comment alone
do not establish Lambek's lemma for that actual structure map.

If exported, require `algebraIso.toFun = in`, both inverse equations and the
canonical action. Constructor disjointness/injectivity and computation must
refer to those same maps. A uniqueness theorem in equivariant maps does not
provide iteration for arbitrary supported fixed handlers.

The initial-chain comments A:272–278 are a construction proposal, not a proof
that the required omega-colimit exists or is preserved. Binary product/sum
isomorphisms do not prove omega-chain preservation. A:42–43 also reverses the
adjoint roles compared with the sketch's own S:343–364 and S:435–471: having a
right adjoint makes abstraction a left adjoint, hence relevant to preservation
of colimits. An omega-stage fixed point must not be confused with eventual
stabilization at a finite stage. No theorem rules out the categorical route;
it simply carries obligations absent from this source.

### 5. Generic induction has no recursive hypotheses or fresh case

**P2, weak statement rather than false theorem; reject as the required
induction interface, rederive predicate lifting and strong induction.**
A:357–364 assumes `P (str x)` for every x outright. The comments A:361–362 do
not introduce hypotheses in Lean. A:371–377 repeats the same step and never
uses its context z in an obligation. No declaration defines a recursive
predicate lifting. These could follow from constructor surjectivity and need
not be false, but they cannot support a structural proof.

The concrete `Lambda.induction_fresh` at A:558–564 does expose IHs and binder
freshness, unlike the generic declaration. It still requires
`EquivariantPred α P`, whose dependency definition is exactly invariance under
every permutation (`Equivariant.lean:118`). This is a real restriction, not
finite support and not an arbitrary motive. The ordinary lambda induction at
A:546–551 likewise imposes an unnecessary restriction for the intended public
arbitrary-motive contract.

Two separate interfaces are needed:

1. An equivariant semantic predicate lifting can use recursive predicates at
   child positions and representative independence in a binder. A supported
   variant needs explicit freshness/descent conditions. Such a lifting must
   not claim an unrestricted representative equation for arbitrary predicates.
2. Public strong induction should allow arbitrary motives `P_i : T_i → C → Prop`
   and IHs generalized over contexts, with binders fresh for the current C.
   Its proof can strengthen over permutations and representatives. This is not
   the same as storing the user's motive in a supported predicate object.

Current `Instances/LambdaCalculus/Induction.lean:88–99` is evidence for the
second contract on that specific quotient, not a proof for generic new syntax.
The required mutual/nested implementation still needs its own theorem. Validate
it with a consumer that uses both an IH at a changed context and a fresh-binder
fact. Proving `True` after obtaining those facts is insufficient.

The new scratch proof below establishes a precise negative gate: even the
finitely supported fixed predicate `x = c` cannot descend by the unguarded
equation `L (abs a x) ↔ x = c` at every representative. Equal self-bindings
`abs c c = abs b b` would force `b = c`. This does not refute freshness-guarded
supported predicate lifting or arbitrary-motive induction.

### 6. Equivariant iteration does not yet cover substitution or primitive recursion

**P1, false fixed-substitution claim; reject it, adapt supported iteration.**
A:483–524 `Lambda.rec` accepts only equivariant handlers and only recursive
results. Its computation/uniqueness requirements are useful *iteration*
requirements. It gives neither original subterms to handlers nor a supported
extension for fixed nominal parameters. A:568–580's proposed substitution
recipe cannot directly instantiate it with arbitrary fixed `(x,s)`.

A:604–605 incorrectly says every fixed substitution is equivariant. The rerun
`BackendCounterexamples.fixed_subst_not_equivariant` proves the contradiction
for `a := var b`, `a ≠ b`, using the current reference substitution. The correct
joint action equation appears separately at A:608–609. Require joint
equivariance when all parameters move, finite support after fixing parameters,
and binder computation under the relevant freshness condition.

Adopt the distinction between equivariant fold and supported iteration.
Rederive the latter by a supported binder-descent theorem or a checked
parameterized construction. Historical FCB has an actual quantified contract:
`FCB.lean:110` requires cofinitely many atoms, uniformly for all bodies, to give
a defined result fresh for the binder. `liftFCB` at :269–311 returns a supported
function with guarded/cofinite computation and uniqueness;
`liftFreshParam` at :700–717 includes joint parameter equivariance. These are
candidate dependencies, not a license to accept an arbitrary binder handler.

Defer primitive recursion to its explicit later task. If derived by iteration
into `(original subterm, result)`, prove reconstruction and keep both components
inside the same binder scope. Neither this product trick nor the name `rec`
automatically establishes dependent elimination, termination for arbitrary
user recursion, or fresh induction on derivations.

### 7. Structural abstraction maps are useful; many advertised laws need correction

**Mostly missing proofs or P2 contract mismatches; adapt selected maps and
defer the catalogue.** S:159–180 product and S:187–204 sum maps state useful
forward equations and equivariance. Product reconstruction must choose one
common fresh binder, as its inverse equation acknowledges. These can help
shared-binder products or original/result pairing, but the first predicate
increment need not implement them unless a selected proof uses them.

S:276–292 `liftAbs_NFun` states an interesting enriched map with action,
identity and composition laws, but no representative computation or support
bound. Add `a # f → mapAbs f (abs a x) = abs a (f x)` and a bound on map support.
The existing rerun `no_unconditional_const_abs_map` refutes the unguarded
equation using a constant supported map from Unit to a fixed atom. It does not
refute an enriched map. Equivariant maps can have an unguarded computation
equation; supported maps require this distinction.

The following statements are weaker than their advertised results, not
counterexamples to the underlying mathematics:

| Historical declaration | Actual issue | Correct contract if needed |
| --- | --- | --- |
| S:228–229 `discreteEquiv_symm` | Repeats forward computation; never mentions `.symm` | Inverse sends x to `abs a x`, with inverse law |
| S:263–265 `expEquiv_symm_abs` | Only says some body represents the inverse at a fresh atom | Characterize that body's application by the advertised concretion formula |
| S:298–301 `liftAbs_equalizer` | Pointwise congruence at one equal input | Map and universal property for the actual equalizer object, if preservation is claimed |
| S:370–387 left-adjunction identities | Both displayed results are evaluation of the same curry/uncurry direction | Define transpose/uncurry maps and prove both composites, or correctly state unit/counit triangles |
| S:483–485 `rightAdj_characterization` | Does not use f in its conclusion | Define the transpose of f and its pointwise formula |
| S:496–498 `rightAdj_counit_unit` | Just unit evaluation, with no counit | Actual composite involving counit and abstraction of unit |
| S:503–504 `rightAdj_unit_counit` | Fresh-atom counit computation, not the full advertised map identity | Prove the composite on `RightAdj` functions extensionally |

S:423–425 `sepProdDistribEquiv` uses a unary `SepProd α X = X * A`
(S:311–312) where its comment describes a binary separated product. At discrete
Unit/Unit the literal canonical-action types have orbit shapes `A+1` and `A+A`,
so the intended equivariant equivalence cannot hold. This is not a disproof of
the literal bare `Equiv` for countably infinite atoms. Reject that claimed
equivariant contract and defer the construction. No publication-error or errata
claim is needed for Package's first workflow; the earlier source question was
not re-investigated here.

### 8. Generalized abstraction shows why action and map compatibility are mandatory

**P1 false arbitrary-action support theorem; reject that statement, defer
generalized binders.** S:539–575 defines a relation and quotient, but S:583–584
`supp_genAbs` accepts any caller-supplied nominal structure on that quotient.
A discrete structure forces its left-hand support to be empty. For canonical
atom x=a and y=b with `a ≠ b`, its right-hand side is `{b}`. The remedy is a
specified canonical quotient action and projection equivariance before exact
support; a newtype or explicit bundled structure can make this boundary clear.
This is a mathematical counterexample, not a newly formalized generalized
quotient. S:589–591's fresh representative statement should not be declared
false merely because it also has an extra instance parameter: that instance
does not occur in its conclusion's supports.

**P1 false bare-equivalence negative theorem; reject its literal contract.**
S:619–622 claims there cannot be bare equivalences for every X,Y. For countably
infinite atoms and nonempty X, the generalized finite-set abstraction quotient
has underlying cardinality `max(ℵ₀, |X|)`: empty binders inject X, binder size
gives the countable lower bound, and `Finset A × X` bounds it above. The two
product sides thus have equal cardinality for all nonempty X,Y; the empty cases
are empty. Choice gives bare equivalences. The correct failure is of the
canonical product comparison, which outputs equal binder cardinalities on its
two sides and misses pairs with different cardinalities. This reasoning checks
the earlier assessment against the actual relation S:539–544, but is not a
Lean cardinality proof.

The criticism of a bare `Equiv` must be applied precisely. S:517–526's two
negative enriched-adjunction declarations are different existential
counterexample claims; their failure of natural/enriched adjunction cannot be
inferred solely from their types, nor does the preceding cardinality argument
refute them. They are deferred without a new proof claim. S:596–598's bounded
generalized-alpha witness and S:608–614's generalized map/right adjoint are also
outside the first workflow; no new validation is claimed for them.

## Required dependency boundary for the first workflow

The source supports this small dependency analysis, independent of backend
selection and without privileging the existing foundation:

| Idea | Disposition for design | Dependencies and acceptance evidence |
| --- | --- | --- |
| Single-atom arity grammar, multiple categories, scoped nested binders | Adapt | Distinct Atom/Data/Rec, constructor result indices; lambda/FOL and nonrecursive-let scope examples |
| Coherent actions and supported values | Adopt requirement; select implementation separately | Same action used by support, abstraction and quotient laws; negative discrete-action example excluded |
| Equivariant arity maps and algebra homomorphism equation | Adopt contract, rederive | Canonical product/abstraction maps; identity/composition and atom/data identity equations |
| Supported functions and fixed parameters | Adopt requirement, adapt interfaces | Conjugation, application, support bounds; substitution's joint law and fixed-support counterexample |
| Predicate lifting and quotient-predicate descent | Rederive | Ordinary Prop, explicit representative compatibility; guarded fixed-predicate positive example and negative probe below |
| Arbitrary-motive fresh induction | Adopt requirement, rederive | Actual IHs, context/permutation strengthening, coherent nested fresh choices; consuming client |
| Supported binder elimination and iteration | Adapt or rederive | Scoped compatibility/freshness and support; chosen-representative computation and uniqueness |
| Actual constructor initiality/isomorphism | Adapt; implementation depends on backend | Canonical in/map, inverse laws, equivariant uniqueness; constructor-compatible validation |
| Product/sum abstraction structural maps | Adapt when consumed | Common fresh representatives, forward/inverse action and computation laws |
| Initial-chain proof and full adjunction/exponential catalogue | Defer unless chosen construction needs them | Actual colimit/universal-property proofs, not binary structural isomorphisms alone |
| Primitive recursion, derivation induction, generalized/multiple binders | Separate later contracts or defer | Cannot be claimed from a term iterator or single-binder proof |

For PKG-01, none of the admitted initial-algebra/structural catalogue is a
prerequisite. Needed contracts are coherent nominal inputs, supported predicates
with ordinary application, logical support, and quotient predicate descent.
F01 must still choose or explicitly leave open the action/representation/universe
policy; this investigation does not decide that policy by inheriting the sketch.
The source review also gives no reason to require all structural adjunctions
before a manually certified lambda/FOL carrier. Any new implementation belongs
under `Package/`, after the agreed bounded foundation increment.

## Reproducible bounded evidence

Commands rerun in this investigation, using current cached project imports:

```sh
git status --short
git branch --show-current
git rev-parse HEAD
git log -5 --oneline
git show 983adeb9b80f75fb7c77c05acfd2fcef16db1d46:Nominal/Set/Algebraic.lean
git show 983adeb9b80f75fb7c77c05acfd2fcef16db1d46:Nominal/Set/Structural.lean
lake env lean docs/research/probes/BackendCounterexamples.lean
lake env lean docs/research/probes/BackendPositivity.lean
lake env lean docs/research/probes/BackendStaging.lean
lake env lean /tmp/nominal-algebraic-F01-IWrzIx/Algebraic.lean
lake env lean /tmp/nominal-algebraic-F01-IWrzIx/Structural.lean
lake env lean /tmp/nominal-algebraic-F01-IWrzIx/PredicateDescent.lean
```

The three existing probes and final scratch predicate probe exited 0. Positive
printed axiom lists contain only `propext`, `Classical.choice`, `Quot.sound`, or
a subset. The positivity probe's expected failures are guarded and its process
exits 0. The two untouched historical copies exited 1 with the import errors
recorded above. The first new predicate run emitted one unused-simp-argument
warning; the final scratch file removed that argument and reran without warnings.
No existing probe was edited.

The new scratch file is retained verbatim here so that `/tmp` persistence is not
required to reproduce this small result:

```lean
import Nominal

open Nominal.Core Nominal.Set
universe u
namespace AlgebraicSourceProbe
variable {α : Type u} [Name α]

-- An arbitrary body predicate cannot compute unchanged at every representative.
theorem no_unguarded_predicate_lift (c : α) :
    ¬ ∃ L : NameAbs α α → Prop, ∀ a x, L (abs a x) ↔ x = c := by
  rintro ⟨L, hL⟩
  obtain ⟨b, hbc⟩ := exists_ne c
  have hrep : abs c c = abs b b := by
    apply NameAbs.abs_eq_iff_of_ne hbc.symm |>.mpr
    simp [hbc.symm]
  have hc : L (abs c c) := (hL c c).mpr rfl
  have hb : L (abs b b) := hrep ▸ hc
  exact hbc ((hL b b).mp hb)

#print axioms no_unguarded_predicate_lift
end AlgebraicSourceProbe
```

Additional source inspection covered the pinned `lean-toolchain`, `lakefile.toml`,
`Nominal/Set.lean`, `Equivariant.lean`, and relevant `NameAbstraction.lean`,
`Concretion.lean` and `FCB.lean` definitions, together with current
`Instances/LambdaCalculus/Induction.lean` and the public recursion declarations.
These reads establish the quoted contracts, not a new external dependency build.
No full library rebuild, fresh project build, clean dependency bootstrap or
historical external build was run. Current-root production code and build
configuration were not changed. This note does not mark any implementation task
or the remaining F01 design/agreement gates complete.

Documentation checks found the local Markdown link valid and the retained Lean
block byte-for-byte equal to the final compiled scratch file. The new note has
no trailing whitespace; `git diff --check` reported no diagnostics. The separate
`git diff --no-index --check /dev/null` check emitted no whitespace diagnostics
and exited 1 because the new file differs from `/dev/null`.
