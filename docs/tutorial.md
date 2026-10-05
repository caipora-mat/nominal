# From fresh names to Church–Rosser

This tutorial follows the complete, kernel-checked client in
[Examples/Tutorial.lean](../Examples/Tutorial.lean). Open that file beside this
page: its sections and theorem names follow the order below. It imports only
`Instances` and the axiom-audit utility, and uses quotient-level operations
throughout.

From the repository root, with the pinned Lean and Mathlib versions:

```sh
lake build Nominal Instances Examples
lake env lean Examples/Tutorial.lean
```

The first command builds the supported libraries and every example module,
including this tutorial. The second checks this particular source directly after
building its imports. Each tutorial declaration is also checked for unexpected
axiom dependencies when the file is elaborated. See
[local validation](validation.md) for the complete reproducibility procedure.

## Atoms, support, and fresh selection

All examples work with an arbitrary `α : Type u` and `[Name α]`.
[`Name`](../Nominal/Core/Name.lean) supplies decidable equality and infinitely
many atoms. A `Nominal α X` supplies a finite-permutation action on `X` with
finite support. `supports S x` says that every permutation fixing the finite set
`S` pointwise fixes `x`; [`supp x`](../Nominal/Set/Nominal.lean) is its least
finite support. These are different statements: a convenient support bound need
not be the least support, and a permutation fixing `x` need not fix `supp x`
pointwise.

For an atom, `a # x` means `a ∉ supp x`. More generally, freshness means disjoint
supports. In the lambda quotient, support is exactly the set of free atoms:
[`Term.supp_eq_fv`, `supp_term_var`, `supp_term_app`, and
`supp_term_lam`](../Instances/LambdaCalculus/Basic.lean). The tutorial's
`supportOfOpenAbstraction` computes the support of `λa. a x` as `{x}` when
`x ≠ a`; binding removes `a` from the body's support.

`freshForTermAndAtom` selects a name avoiding both a term `t` and an atom `x`:

```lean
choose_fresh a from (t, x) with hf
split_fresh hf1 with hat hax
exact ⟨a, hat, (fresh_atoms a x).mp hax⟩
```

[`choose_fresh` and `split_fresh`](../Nominal/Set/Freshness/Tactic.lean) construct
proofs of freshness. With the prefix `hf`, selected inputs receive indexed
names `hf1`, `hf2`, and so on; this example has one selected product. The split
then names its component facts explicitly. The proof consumes these facts to
obtain the promised inequality. The underlying existence result is
[`exists_fresh_atom`](../Nominal/Set/Freshness/Basic.lean); this is a logical
selection principle, not an executable fresh-name service.

## Alpha equality and nested binders

Use `Term.var`, `Term.app`, and `Term.lam` to construct alpha-equated syntax.
Ordinary Lean equality already identifies alpha-equivalent terms.
`alphaIdentity` proves `λa. a = λb. b` using
[`Term.lam_eq_swap`](../Instances/LambdaCalculus/Basic.lean): a lambda may be
presented at any atom fresh for the whole lambda, with the corresponding swap
applied to its body. The body itself need not be fresh for its original binder.

`nestedAlpha` proves `λa. λa. a = λb. λc. c`, including arbitrary coincidences
among the three displayed atoms. The inner binder shadows the outer one on the
left. Nested binding is handled by ordinary nesting of single binders, without
a global distinct-name assumption.

For inversion, [`lam_inj`, `lam_eq_iff_at_fresh`, and
`lam_eq_iff_common_fresh`](../Instances/LambdaCalculus/Basic.lean) compare bodies
at the same or a chosen common binder. The general abstraction API underlying
these results is [`NameAbs`](../Nominal/Set/NameAbstraction.lean), with
[`concretion`](../Nominal/Set/Concretion.lean) for opening an abstraction at a
fresh atom. Clients do not need raw alpha-equivalence or quotient representatives.

## Practical supported functions

[`NFun α X Y`](../Nominal/Set/NFun/Basic.lean) packages a function with finite
support under conjugation:
`(π • f) x = π • f (π⁻¹ • x)`. Ordinary Lean function spaces retain their
separate pointwise action; `PFun` provides the deliberate boundary between them.
Every equivariant function is finitely supported, but fixing a nominal parameter
usually gives only finite support.

The tutorial constructs equivariant constructor handlers with
`NFun.equivariant`. Its `replaceVariable` handler uses the explicit constructor
`NFun.ofFun` and a proof that `{x} ∪ supp s` supports its conditional body.
[`supports_nfun from x s`](../Nominal/Set/NFun/Tactic.lean) proves that obligation
using the captures and registered action equations. The set is an upper bound,
not a claim of exact least support. Keeping the noncomputable support witness
inside the proof field allows this particular function body to remain computable.
The named theorem `replaceVariableSupported` states the `FinSupported` certificate
explicitly, so `replaceVariableAt` computes by ordinary `simp`. In this example,
passing the existential witness directly to `NFun.ofFun` obstructs simplification
because of proof-argument transparency; the named certificate avoids that issue.
An explicit `change` to the underlying function body is another local escape hatch.
`NFun.ofSupports` and `NFun.ofCaptures` are alternatives when an explicit support
set is convenient. An unregistered operation can use `supports_nfun [rules]`
or a direct proof; arbitrary functions do not automatically have finite support.

The next examples demonstrate the existing interface in a lambda client:

| Tutorial declaration | Operation and underlying interface |
|---|---|
| `replaceVariableAt` | Ordinary application of a proof-backed constructor |
| `partialApplication` | `application.curry t s = app t s` |
| `curryRoundTrip` | `NFun.uncurry_curry` via `simp` |
| `partialSupport` | `NFun.supp_curry_apply_le` bounds captures after fixing `t` |
| `composeAndMap` | `NFun.comp`, ordinary `List.map`, and coercion simplification |
| `rewriteUnderFunction` | `rw` beneath an ordinary higher-order consumer |
| `substitute`, `substituteSupport` | `NFun.fromParam` and `supp_fromParam_le` |
| `substitutionComposition` | `ext t` followed by a pointwise substitution law |

`substitute x s` fixes the variable and replacement of the jointly equivariant
substitution operation. Its support is contained in `{x} ∪ supp s`; no claim
that each fixed substitution is equivariant is made.

The `nfun` syntax remains a prototype. Automatic capture inference supports the
tested single-binder subset and rejects `let`, `match`, and nested functions;
global identifiers are not automatically classified as equivariant operations.
Use the proof-backed constructors above for the supported path. Explicit
`nfun [capturing ...]` is an escape hatch for the tested prototype cases, not a
general binder-aware elaborator. The positive and expected-failure examples in
[NFunSupport.lean](../Examples/NFunSupport.lean) fix the current contract.

## Iteration, its equations, and strong term induction

[`Term.recNoContext`](../Instances/LambdaCalculus/Recursion.lean) takes three
supported handlers: an atom handler, a pair-of-results application handler, and
an atom/result abstraction handler. A finite set `A` must support all three.
The abstraction handler also needs the guarded fresh-condition-for-binders
(FCB): `a # A → a # f_L (a, y)`.

The tutorial's `abstractionFCB` proves this condition with
[`NFun.fcb_of_binder`](../Nominal/Set/NFun/Basic.lean), because the constructor binds
its atom in the result. Equivariance alone would not establish that condition.
`rebuild` uses `recNoContextNFun` to obtain the iterator directly as a supported
function, and `rebuildSupport` obtains empty support from the exported bound.

The public computation rules are `recNoContext_var`, `recNoContext_app`, and
`recNoContext_lam`. The lambda equation requires `a # A`; our reconstruction
uses `A = ∅`, so every binder qualifies. For other handlers, alpha-renaming can
first move the binder outside `A`. `recNoContext_unique` characterizes the
iterator by these equations. `rebuildUnique` applies it to an ordinary candidate
function `g`, whose own lambda equation may use a different finite avoidance
set `B`. Neither finite support nor equivariance of `g` is an extra premise.
`recNoContext_independent` expresses independence of the chosen valid handler
bound.

Despite its historical name, this is **iteration**: the application and
abstraction handlers receive recursively computed results, not the original
subterms as additional arguments. The operation is extracted by classical
choice from a proved total, single-valued relation. Its laws are theorem-level
equations, not an executable evaluation or a primitive-recursion contract.

`rebuildIdentity` is a term-induction proof using
[`Term.strong_ind_finset`](../Instances/LambdaCalculus/Induction.lean). It has
one case per constructor and an induction hypothesis for each subterm. The
general `Term.strong_ind` works with an arbitrary predicate `P : Term α → Z → Prop`
and a nominal avoidance context `Z`: each recursive hypothesis is available at
**every** context, and the lambda binder is fresh for the selected context.
There is no equivariance or finite-support requirement on `P`. To enlarge the
context beneath a nested binder, use that general form; the persistent
[`freshBinders`](../Examples/LambdaInterface.lean) example records the outer
binders in the recursive context.

## Substitution that must rename a binder

`renameToAvoidCapture` starts from `(λy. x)[x := y]`, with `x ≠ y`. Keeping `y`
as the binder would capture the free replacement. The proof selects `z` fresh
for `x,y`, uses [`subst_lam_rename`](../Instances/LambdaCalculus/Substitution.lean),
then applies `subst_lam` under the condition `z # (x, var y)`.
The result is `λz. y`, and the theorem also proves `¬ y # λz. y`: the replacement
really stays free. No executable choice of `z` or representative inspection is
needed.

`substitutionComposition` proves equality of two composed supported functions
by `ext t`, reducing to [`Term.subst_subst`](../Instances/LambdaCalculus/Substitution.lean):

```text
t[x := s][y := r] = t[y := r][x := s[y := r]]
```

The hypotheses `x ≠ y` and `x # r` are necessary parts of this interface.
The library proof uses strong term induction with an avoidance set containing
both variables and the replacement supports. In its lambda case,
`subst_fresh_of_fresh` discharges freshness for the substituted replacement.
Neither hypothesis can be dropped simply because terms are alpha quotients.

## Strong term induction versus fresh rule induction

Term induction analyzes syntax. Proving a property of `h : t ⇉ t'` instead
requires induction on a **derivation**: the parallel contraction rule has both
a body premise and an argument premise, whose endpoints must stay aligned
after binder renaming.

[`Term.Parallel.strong_ind`](../Instances/LambdaCalculus/ReductionInduction.lean)
and `Term.Beta.strong_ind` provide this fresh rule induction. They accept
arbitrary endpoint predicates with a nominal context, and expose both the
premise derivations and their context-generalized induction hypotheses.
The contraction binder avoids the context and the argument(s), without needing
freshness for its own body. The underlying reductions are unrestricted.

`parallelPreservesFreshWhen` derives freshness preservation while capturing an
arbitrary predicate `q : α → Prop` in its motive. `q` needs no action or support
certificate. The lambda and contraction cases use binder freshness for the
atom context `x` to rule out `x = a`; the contraction case uses **both** induction
hypotheses. This illustrates where the Barendregt variable convention is a
proved induction facility. The larger
[fresh derivation examples](../Examples/LambdaFreshReduction.lean) also
instantiate recursive hypotheses at contexts enlarged by enclosing binders.

## The confluence argument and normal forms

The remaining tutorial uses arbitrary open terms with reduction allowed under
lambdas. The proof dependencies can be read in order:

1. [`Parallel.subst`](../Instances/LambdaCalculus/ParallelSubstitution.lean)
   proves `t ⇉ t' → s ⇉ s' → t[x := s] ⇉ t'[x := s']`. Its proof uses fresh
   rule induction and substitution composition in the contraction case.
   `substituteRelatedInputs` exercises genuine reductions of both inputs.
2. [`Parallel.diamond`](../Instances/LambdaCalculus/ParallelDiamond.lean)
   joins two parallel steps by two further parallel steps. Fresh inversion at
   a common binder and simultaneous substitution compatibility handle the
   contraction cases. `diamondForDuplication` applies it to the peak from
   `(λa. a a) ((λb. b) x)`.
3. [`Beta.to_parallel`, `Parallel.to_betaStar`, and
   `betaStar_iff_parallelStar`](../Instances/LambdaCalculus/ChurchRosser.lean)
   identify the generated finite directed sequences.
   [`BetaStar`](../Instances/LambdaCalculus/ReductionClosure.lean), written
   `→β*`, is Mathlib's reflexive-transitive closure; `BetaEq`, written `≡β`,
   is its equivalence-generation relation on beta steps.
4. Parallel diamond gives confluence of its closure using Mathlib's relation
   theorem, hence `BetaStar.confluent` for finite beta reductions. The tutorial's
   `duplicationSequence` serializes a parallel contraction to the common open
   reduct `x x`, and `joinDuplicationReduct` joins an arbitrary competing reduct.
5. `BetaEq.church_rosser` gives a common directed reduct from a conversion that
   may contain steps in either direction. `joinConvertible` uses this theorem;
   `BetaEq.iff_join` states the converse as well.

`BetaNormal t` means that there is no outgoing beta step, even a step from `t`
to itself. `variableApplicationNormal` establishes that `x x` is normal using
constructor inversion. `uniqueNormalResult` combines the explicit sequence
above with `BetaEq.normal_unique`: any normal term convertible to that source
equals `x x` as a quotient term. `BetaStar.normal_unique` gives the corresponding
result for two normal reducts of one source.

This is uniqueness **when a normal form exists**. The library does not claim
normalization, termination, or a terminating reduction strategy for the untyped
lambda calculus.

## Scope and foundations

The development uses the usual classical Lean foundations (`propext`,
`Classical.choice`, and `Quot.sound`), actual quotients, and least supports.
`supp`, the semantic iterator, and substitution may be noncomputable. The
support proof of `replaceVariable` does not make its underlying conditional
function noncomputable; semantic substitution has a different contract.

This case study has one atom sort and single binders that may nest. `Term α`,
its term-induction context, and its iterator result currently use the same
universe as `α`; fresh rule induction permits a separate context universe.
Some core constructions have their own universe parameters, so this restriction
should not be read as a theorem that every nominal construction requires equal
universes. Multiple atom sorts, generalized binding signatures, primitive
recursion, generic datatype generation, and a general `nfun` elaborator remain
outside this first deliverable.
