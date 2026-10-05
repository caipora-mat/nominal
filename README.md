# Nominal Sets in Lean 4

A Lean 4 / Mathlib formalization of nominal set theory following Pitts' *Nominal Sets* (CUP 2013).

See [the roadmap and progress tracker](docs/roadmap.md) for task status, dependencies,
nominal-function ergonomics, and the completed lambda-calculus Church–Rosser case study.

The new package phase has a separate
[nominal-package roadmap](docs/nominal-package-roadmap.md), covering generated
syntax, functions, judgments and the agreed five case studies.

## Toolchain

Lean v4.34.1 / Mathlib v4.34.1, pinned by `lean-toolchain` and `lake-manifest.json`.

Start with the [compiling tutorial](docs/tutorial.md), backed by
[Examples/Tutorial.lean](Examples/Tutorial.lean). It follows fresh atoms, alpha
renaming, supported functions, iteration and capture-avoiding substitution through
fresh rule induction, parallel diamond, Church–Rosser and normal-form uniqueness.
[Local validation](docs/validation.md) documents setup, complete build coverage,
axiom checks, and fresh project-artifact builds.

## Foundations and scope

This library deliberately uses classical reasoning, actual quotients, and least
supports. `Nominal.finSupp` and `NFun`'s support evidence live in proof fields;
least support, fresh-value extraction, binder iteration and semantic substitution
may be noncomputable. Computable NFun operations such as constants and composition
retain executable bodies when support witnesses stay in `Prop`. The axiom audit
allows only Lean's standard `propext`, `Classical.choice`, and `Quot.sound`.

`Name α` requires decidable equality and infinitude, not countability. This release
uses one atom sort and single or nested binders. The `outParam` in `PermType` and
`Nominal` lets instance search infer a default atom type/action from the carrier;
it is not an automatic multiple-sort interface. Generic quotient instances,
`NameAbs`, concretion, FCB, and the lambda iterator currently share the atom and
carrier universe. Discrete Unit/Bool instances are explicit choices; Nat/Int have
explicit permutation actions but no supplied general nominal instance. Current
lambda clients use atoms, products, and finite atom sets as avoidance contexts.

`PFun` separates conjugation on functions from Mathlib's ordinary pointwise
action. Fixing an element need not fix its least support pointwise; strong support
is a separate property. These boundaries and action coherence have persistent
[core contract examples](Examples/CoreContracts.lean).

The [release assessment](docs/release-assessment.md) records delivered polish and
deferred research. [Research correspondence](docs/research-correspondence.md)
pins the Rocq and article evidence and distinguishes inspected sources from
external builds and publication corrections.

## Project Structure

```
Nominal.lean              # top-level: imports Core + Set
Nominal/
  Wheels.lean             # utility lemmas; pick_new tactic
  Core.lean               # re-exports Core.*
  Core/
    Name.lean             # Name typeclass (DecidableEq + Infinite)
    FinitePerm.lean       # FinitePerm α ≤ Equiv.Perm α
  Set.lean                # re-exports Set.*
  Set/
    PermType.lean         # PermType typeclass + instances
    PFun.lean             # PFun newtype (conjugation action on functions)
    Equivariant.lean      # equivariance predicates and bundled equivariant maps
    Swap.lean             # swap transposition + movedFinset lemmas
    Support.lean          # supports / FinSupported; Pitts Prop. 2.1
    Nominal.lean          # Nominal typeclass; supp; all Nominal instances
    EquivalenceClass.lean # equivariant quotients and their nominal structure
    Freshness.lean        # re-exports Freshness.*
    Freshness/
      Basic.lean          # Fresh (#) relation
      Tactic.lean         # choose_fresh and split_fresh tactics
    NFun.lean             # compatibility umbrella for NFun.Basic + NFun.Tactic
    NFun/
      Basic.lean         # finitely supported functions and proof-backed constructors
      Tactic.lean        # support tactic and experimental nfun macro
    FreshQuantifier.lean  # И quantifier; someAny (Pitts 3.9)
    NameAbstraction.lean  # NameAbs ([A]X); abs / ⟪a⟫ x; supp_abs
    Concretion.lean       # concreteAt (⊙); liftAbs; Prop. 4.9; ext
    FCB.lean              # FCB / liftFCB (Thm 4.15); liftFresh (Cor 4.17)
Instances.lean            # lambda-calculus case-study umbrella
Instances/
  LambdaCalculus.lean     # imports all twelve case-study modules
  LambdaCalculus/
    Basic.lean           # alpha quotient, action, support/free variables
    Induction.lean       # strong induction with fresh binders
    Recursion.lean       # supported iteration, computation, uniqueness and support
    Substitution.lean    # capture-avoiding substitution and composition
    Beta.lean            # full contextual beta reduction and nominal properties
    Parallel.lean        # parallel reduction, reflexivity, and nominal properties
    ReductionInduction.lean # fresh rule induction with arbitrary nominal contexts
    ReductionInversion.lean # chosen/common fresh-binder reduction inversion
    ParallelSubstitution.lean # simultaneous compatibility with substitution
    ParallelDiamond.lean # direct diamond property on arbitrary open quotient terms
    ReductionClosure.lean # beta sequences and convertibility via Mathlib closures
    ChurchRosser.lean    # beta confluence, convertibility, and normal-form uniqueness
```

## Key API

| Concept | Type | Key lemmas |
|---|---|---|
| Atoms | `Name α` | — |
| Finite perms | `FinitePerm α` | `swap_factorization`, `eq_closure_isSwap` |
| Perm-set | `PermType α X` | instances for atoms, products, `Option`, `Finset`, `PFun` |
| Transposition | `swap a b` | `swap_smul_eq_of_not_mem`, `movedFinset_swap_smul_subset` |
| Equivariance | `IsEquivariant α f`, `IsEquivariant₂ α f` | `hf.toNFun`, `NFun.fromParam` |
| Support | `supports s x` | `supports_iff_swap` (Pitts 2.1), `supports_inter`, `supports_smul` |
| Nominal set | `Nominal α X`, `supp x` | `supp_supports`, `supp_le`, `supp_equivariant`, `supp_atom`, `supp_prod` |
| Freshness | `x # y` | `fresh_atom_left`, `fresh_swap`, `fresh_prod_right`, `exists_fresh_atom` |
| Fresh quant. | `И a, ϕ a` | `someAny` (Pitts 3.9), `freshQuantifier_and` |
| FS functions | `NFun α X Y` | `curry`, `uncurry`, `comp`, `supp_apply_le`, `fresh_apply` |
| Name abs. | `NameAbs α X`, `⟪a⟫ x` | `abs_eq_iff` (Lemma 4.3), `supp_abs` (Prop. 4.5), `fresh_abs` |
| Concretion | `F ⊙ a` | `concreteAt_abs_self/fresh/not_fresh`, `abs_concreteAt_eq` (Prop. 4.9), `nameAbs_ext` (4.16) |
| Functor | `liftAbs hf` | `liftAbs_abs`, `liftAbs_unique`, `liftAbs_id`, `liftAbs_comp` |
| FCB | `FCB F`, `liftFCB` | `liftFCB_abs` (4.33), `liftFCB_abs_of_fresh`, `supp_liftFCB_le`, `liftFCB_unique` |
| Elim. principle | `liftFresh f` | `liftFresh_abs`, `liftFresh_equivariant`, `liftFresh_unique` |

**Design note:** `PFun α X Y` wraps `X → Y` with the conjugation action to avoid a diamond with Mathlib's `Pi.instSMul`.

NFuns support ordinary application, higher-order arguments, `rw`, and nested
`ext x y`. `simp` exposes applications and coerced functions without unfolding
support certificates. `DFunLike.congr_fun h x` extracts a pointwise equality.
Use `f.curry p` for partial application, `f.uncurry` for a pair-based function,
and `NFun.fromParam f hf p` to fix a parameter of a jointly equivariant operation.
Fixing a parameter gives a support upper bound, not automatic equivariance.

`supports_nfun [rules] from f c` proves explicit support obligations using
capture bounds and proved action equations in `nfun_simp`. For example, the
substitution variable handler uses `supports_nfun from x s` with `{x} ∪ supp s`.
Unregistered operations need explicit rules or a direct proof.

The `nfun` macro remains experimental. Automatic capture inference accepts the
tested single-binder subset and rejects `let`, `match`, and nested functions;
global identifiers are still not automatically distinguished from captures.
Its explicit override is `nfun [capturing a b c] fun x => body`.
Use `NFun.equivariant`, `hf.toNFun`, `NFun.ofSupports`, or `NFun.ofCaptures`
with explicit proofs when the macro is unsuitable. When a support set itself is
noncomputable, `NFun.ofFun f ⟨S, hS⟩` keeps it inside the proof field and can
preserve a computable function body.
The lambda case study includes full contextual beta reduction, parallel reduction,
beta sequences/convertibility, and fresh rule induction/inversion. Both
`Term.Beta.strong_ind` and `Term.Parallel.strong_ind` accept arbitrary predicates
on endpoints and a nominal context, with context-generalized hypotheses for every
recursive premise. Their finite-set variants are `strong_ind_finset`. Fresh
inversion can retain, choose, or obtain a common binder; parallel application
inversion preserves both congruence and contraction alternatives.
`Term.Parallel.subst` proves simultaneous substitution compatibility:
`t ⇉ t' → s ⇉ s' → t[x := s] ⇉ t'[x := s']`, for arbitrary open terms and
substitution variables. Its `subst_left` and `subst_right` corollaries fix the
replacement or subject respectively. `Term.Parallel.diamond` joins any two
parallel steps from a common source with two further parallel steps, using
Mathlib's `Relation.Join Parallel`.
`Term.Beta.to_parallel` and `Term.Parallel.to_betaStar` relate the two reductions;
`Term.betaStar_iff_parallelStar` identifies their reflexive-transitive closures.
`Term.BetaStar.confluent` joins finite beta reductions from a common source.
`Term.BetaEq.church_rosser` joins beta-convertible terms, and `Term.BetaEq.iff_join`
gives the converse as well. `Term.BetaNormal` means no outgoing beta step;
`Term.BetaStar.normal_unique` and `Term.BetaEq.normal_unique` give equality of
normal quotient terms. These results apply to arbitrary open terms and reduction
under lambdas; neither termination nor existence of normal forms is claimed.

The separate raw `Nominal.Syntax` sketch is excluded from this branch for now.

## Build

```bash
lake build
# Complete supported libraries plus tutorial, regressions and axiom audit.
lake build Nominal Instances Examples
lake env lean Examples/AxiomAudit.lean
```

The default build covers both `Nominal` and `Instances`, including the NFun tactic
module and all twelve lambda-calculus modules.

The explicit `Examples` target also covers the nominal-function
[API](Examples/NFun.lean), [support tooling](Examples/NFunSupport.lean), and
[lambda clients](Examples/NFunLambda.lean). They include expected failures,
empty-domain laws, computation checks, and axiom audits. Run all supported
libraries and these regressions with `lake build Nominal Instances Examples`.

[Reduction examples](Examples/LambdaReduction.lean) cover open terms, all beta
contexts, capture avoidance, alpha-renamed binders, simultaneous parallel
contraction, and the absence of one-step beta successors for variables. They
also audit the axiom dependencies of the public lambda development.

[Fresh reduction consumers](Examples/LambdaFreshReduction.lean) exercise
arbitrary predicates, external parameters, nested binders with enlarged avoidance
contexts, both parallel-contraction premises, and fresh inversion across
alpha-renamed binders. They are included in the `Examples` target.

[Parallel substitution examples](Examples/LambdaParallelSubstitution.lean) cover
genuine reductions in both substituted inputs, alpha-renaming to avoid capture,
repeated-binder shadowing, both corollaries, and the contraction/composition case.
They are included in the `Examples` target with an axiom audit.

[Parallel diamond examples](Examples/LambdaParallelDiamond.lean) give explicit
joining terms for mixed contraction/congruence and differing simultaneous
contractions, including open terms and alpha-renamed binders. They are included
in the `Examples` target with an axiom audit.

[Church–Rosser examples](Examples/LambdaChurchRosser.lean) give a beta peak from
a duplicating redex, a common open reduct, conversions with forward and backward
steps, reduction under a lambda, and applications of normal-form uniqueness.
They are included in `Examples` with an audit of the headline theorem axioms.
The mathematical case study and task-9 tutorial/interface polish are described in
[the release assessment](docs/release-assessment.md); the roadmap records exact
verification evidence and remaining external research checks.

## Freshness tactic regressions

```bash
lake build Examples
# Directly elaborate the regression file:
lake env lean Examples/Freshness.lean
# Validate both supported libraries and the regressions together:
lake build Nominal Instances Examples
```

[Examples/Freshness.lean](Examples/Freshness.lean) tests automatic and explicit
freshness selection, shadowing, derived instances, ambiguity, nested splitting,
and diagnostics. Its axiom audit rejects admissions and dependencies beyond the
standard `propext`, `Classical.choice`, and `Quot.sound` foundations.

`choose_fresh a` scans eligible locals using instance synthesis;
`choose_fresh a from X x` mixes type expansion and explicit terms. Generated names
are always indexed: `aFresh1`, `aFresh2`, …, or `h1`, `h2`, … with `with h`.
`split_fresh h` recursively splits products into `h_1`, `h_2`, …, skipping occupied
names. Its `with` form requires one distinct, unused name per leaf. See the
[tactic documentation](Nominal/Set/Freshness/Tactic.lean) for ordering, filtering,
atom-sort selection, and failure behavior.

## References

- A. M. Pitts, *Nominal Sets: Names and Symmetry in Computer Science*, CUP 2013.
- V. Choudhury, nominal sets in Agda.
- D. Paranhos, nominal sets in Rocq.
