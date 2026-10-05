# Working on the nominal library

These instructions apply throughout this repository. Follow the user's current
instructions when they refine the scope or priorities below.

## Purpose and priorities

This is a research formalization of nominal sets in Lean, descended from a
constructive Rocq development. The Lean library deliberately uses classical
reasoning, actual quotients, and least supports.

The first deliverable is a polished reusable core and a lambda-calculus case
study culminating in Church–Rosser. Proofs should support natural reasoning with
binders and justified Barendregt Variable Convention principles.

- Prioritize cleanup, reliable interfaces, and the gaps needed to finish the
  lambda-calculus proof. Learn later infrastructure requirements from that client.
- Support one atom sort, single binders, and nested binders initially.
- Classical reasoning and noncomputable semantic operations are acceptable.
  Executable substitution and fresh-name generation are not release requirements.
- `NFun` usability matters: coercions, currying, composition, partial application,
  higher-order use, and rewriting should require little wrapper manipulation.
- Improve focused support automation where useful. General metaprogramming,
  generic algebraic constructions, and datatype generation must not block
  Church–Rosser.
- Do not reintroduce the excluded raw `Nominal.Syntax` sketch or incorporate
  Murillo's syntax/unification branch unless the user requests it.
- CI is not required. Do not add or modify CI workflows as routine project work.

## Start with the current state

Read [README.md](README.md) and the relevant tasks in
[docs/roadmap.md](docs/roadmap.md). Consult
[the development review](docs/reviews/2026-10-02-development-review.md) for evidence
and known issues, but remember that it describes an earlier snapshot.

Inspect `git status`, the current branch, and relevant history before editing.
The intended work branch is `fasapa/next`; do not switch branches automatically
or overwrite unrelated changes. Untracked examples and documentation may be
active user work. Preserve them.

Verify claims against current source and build results. In particular, do not
repeat historical claims that the lambda library is unintegrated or that a
removed migration patch still exists. Treat the roadmap as a maintained tracker,
not proof that every listed declaration or behavior is present.

## Repository layout

- `Nominal/Core/`: atoms and finite permutations.
- `Nominal/Set/`: actions, equivariance, support, freshness, quotients, name
  abstraction, concretion, supported functions, and FCB lifting.
- `Nominal/Set/NFun/Basic.lean`: the supported-function interface and combinators.
- `Nominal/Set/NFun/Tactic.lean`: support tooling and the experimental `nfun` macro.
- `Nominal/Set/Freshness/Tactic.lean`: fresh-name selection and freshness splitting.
- `Instances/LambdaCalculus/`: quotient syntax, strong term induction, supported
  iteration, and capture-avoiding substitution; extend this case study for semantics.
- `Nominal.lean` and `Instances.lean`: public library entry points.
- `Examples/`: standalone examples; check whether a file is a passing example or
  an intended defect reproducer before treating it as part of validation.
- `docs/roadmap.md`: task IDs, dependencies, completion criteria, and work log.
- `docs/reviews/`: dated assessments whose findings must be checked against later changes.
- `ref/`: reference material, including Pitts' *Nominal Sets*.

## Mathematical and Lean conventions

- Review theorem statements as well as proofs. Do not weaken a statement or add
  assumptions merely to make a proof compile; explain any intentional change.
- Do not introduce `sorry`, `admit`, custom axioms, or disabled kernel checking
  into supported code. Clearly distinguish experimental placeholders from proved results.
- Standard classical Lean foundations are intentional. Distinguish them from
  `sorryAx` and additional assumptions when inspecting proof dependencies.
- Preserve the distinction between finite support, least support, and strong
  support. A permutation fixing an element need not fix its support pointwise.
- Fixed-parameter functions can be finitely supported without being equivariant.
  Joint equivariance must permute all relevant nominal parameters.
- Preserve `PFun`'s conjugation action and its separation from ordinary pointwise
  function actions. Check action coherence when changing instances or priorities,
  especially on finite permutations and function spaces.
- Keep noncomputable support witnesses inside proof fields when the underlying
  operation can remain computable.
- Reuse existing abstraction, Some/Any, concretion, and FCB results before adding
  parallel infrastructure. Search for equivalent lemmas before introducing new ones.
- Distinguish strong induction on terms from strong induction on derivations,
  and iteration from primitive recursion with access to original subterms.
- Give public operations useful application/computation lemmas. Prefer public
  interfaces over unfolding quotient implementations or large recursive definitions.
- Preserve deliberate `seal` boundaries unless measured evidence justifies changing them.
- Keep simp rules directed and terminating. Avoid broad instance, reducibility,
  or linter changes to conceal a local problem.
- Follow surrounding naming, namespace, notation, and module conventions. Explain
  non-obvious mathematical hypotheses and proof strategies in documentation.

## Function tooling and regression examples

Do not assume the experimental `nfun` macro handles arbitrary globals, shadowing,
`let`, `match`, or nested lambdas correctly. Use proof-backed constructors when
needed, and reproduce a limitation before reporting it as a current defect.

For future elaborator work, use elaborated expressions and local-variable
identities rather than identifier spelling. Preserve hygiene and instance
coherence. Arbitrary ordinary functions need not be finitely supported, and
arbitrary global functions are not automatically equivariant.

For tactic fixes, reproduce the failure first and retain a small example whose
conclusion uses the generated facts. Proving `True` after invoking a tactic does
not establish that it produced the promised hypotheses. Cover relevant shadowing,
derived instances, nested products, and failure diagnostics.

Prefer existing `FunLike`/`DFunLike`, `simp`, and `ext` mechanisms where they
already work. New syntax or tactics should solve demonstrated client problems.

## Local verification

Use the versions pinned in `lean-toolchain`, `lakefile.toml`, and
`lake-manifest.json`. Upgrade Lean and Mathlib together only as part of the task;
do not silently change dependencies to repair a proof.

```sh
lake build
lake build Nominal Instances
lake env lean path/to/Example.lean
git diff --check
```

The first two commands currently cover the same supported libraries; one full
build suffices when that coverage has been confirmed. Check standalone examples
explicitly because being present in `Examples/` does not make them default targets.

Compile affected modules while iterating, then check the supported dependent
targets before reporting success. For significant mathematical changes, inspect
representative public results with `#print axioms`. Resolve new diagnostics or
explain their cause. Distinguish cached builds, fresh project builds using cached
dependencies, and clean dependency bootstraps in reports.

Documentation-only changes need link/content and diff checks, not a Lean rebuild.
Do not claim verification that was not run. Report unavailable tools and untested
cases explicitly. Inspect admission scans in context: comments and abstract
module-signature requirements are not automatically active unproved assumptions.

## Progress tracking and reviews

For substantive work, use the relevant stable roadmap task ID. Update its status,
checkboxes, dependencies, and work log with the delivered result and verification
evidence. Mark work complete only after its completion criterion is met.
Distinguish committed work, working-tree changes, and scratch experiments.

For reviews, give actionable findings with file/declaration references, severity,
evidence, impact, a proposed remedy, and a verification method. Separate confirmed
defects from missing features, ergonomic problems, and research questions. Record
what works and should be preserved. A request to review does not authorize silently
implementing the recommendations or merging branches.

Use as many agents as useful for substantial independent investigations. Assign
clear scopes and disjoint edit ownership, coordinate shared files, and verify
their findings before integration. Simple tasks do not require delegation.

Keep changes focused and reviewable. Ask questions when an unresolved research
choice materially affects the work; continue independent work in the meantime.
Do not repeat permission requests for work already authorized by the user.

## Research references

- Original Rocq development: <https://github.com/fasapa/nominal>.
- Article sources: <https://github.com/fasapa/nominal-sets-article>.
- Pitts' *Nominal Sets*: `ref/nominalsets.pdf`.

Record the exact revision or publication version when comparing sources. Supplied
Rocq supports and setoid equality do not translate mechanically into Lean least
supports and quotient equality. Distinguish historical releases from current main,
and check primary sources before making mathematical or research-priority claims.
