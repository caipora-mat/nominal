# Research correspondence and verification limits

This is a source correspondence account, not a claim that the external
developments were rebuilt or that a manuscript was corrected. Task 9 changed
only this Lean repository. The older
[development review](reviews/2026-10-02-development-review.md) retains the detailed
historical findings H-01–H-07; its statements about unfinished Lean reduction
and missing lambda integration describe the old snapshot.

## Pinned evidence

| Source | Version inspected | Kind of evidence |
| --- | --- | --- |
| Lean | `b74ad349fa1b0e77dbb59b8225abe84be8e5b617` plus task-9 working-tree changes | Kernel-checked local builds and audits; [commands and limits](validation.md) |
| [Rocq main snapshot](https://github.com/fasapa/nominal/tree/78f41a6c7ca1b55814b7b7c7d734ad4decaac523) | `78f41a6c7ca1b55814b7b7c7d734ad4decaac523` | Read-only local Git source inspection; not a claim about today's remote tip |
| [Rocq article artifact](https://github.com/fasapa/nominal/tree/fc7b95a47539fa2dc39f41f293c7d943a0d8b22d) | `lsfa2025`, `fc7b95a47539fa2dc39f41f293c7d943a0d8b22d` | Compared project membership, assumptions, and lambda/substitution files with main |
| [Article sources](https://github.com/fasapa/nominal-sets-article/tree/8c8c05d25f0918280fa2446a9ee78921bf9a8fa4) | `8c8c05d25f0918280fa2446a9ee78921bf9a8fa4` | Read-only TeX inspection; no TeX build or edits |
| [Published account](https://arxiv.org/html/2509.25883v1) | *Nominal Sets in Rocq*, arXiv:2509.25883v1, 30 September 2025 | Versioned HTML checked; distinct from extended manuscript sources |
| [Pitts, *Nominal Sets*](../ref/nominalsets.pdf) | CUP 2013; local PDF SHA-256 `546104434ce6388d2aed248428cc8bde653bf98780cee55265f686e7290f0794` | Library's mathematical reference; not a new page-by-page audit |

Rocq, `coqc`, `coq_makefile`, and opam were unavailable during task 9. Accordingly
there is no new Rocq build or `Print Assumptions` result. The supplied local
Rocq and article snapshots match the pinned revisions above. Other research
branches, including Murillo's syntax/unification work, were not inspected.

## Theorem and representation correspondence

Rocq paths below are under `theories/` at the pinned main/tag snapshots. The
lambda and substitution files are byte-identical between those two revisions,
although their imported permutation-instance proofs differ.

| Topic | Rocq source | Lean interface and deliberate difference |
| --- | --- | --- |
| Names/permutations | `Name.v`, `Permutation.v` | [`Name`, `FinitePerm`](../Nominal/Core.lean): infinite decidable atoms and actual finite bijections; no countability requirement |
| Actions/equality | `PermT.v`; setoid equality and respectfulness | [`PermType`](../Nominal/Set/PermType.lean) extends `MulAction`; Lean equality and explicit equivariant quotients |
| Support/freshness | `Nominal.v`, `Fresh.v`; supplied finite supports, semantic freshness | [`supp`, `supp_supports`, `supp_le`](../Nominal/Set/Nominal.lean); least supports and disjointness, not equality with an arbitrary supplied bound |
| Functions | `Instances/SupportedFunctions.v`; stored support, pointwise setoid equality | [`PFun`](../Nominal/Set/PFun.lean)/[`NFun`](../Nominal/Set/NFun/Basic.lean); conjugation and proof-only finite-support existence, ordinary extensional equality |
| Abstraction | `NameAbstraction.v`; pairs with alpha setoid | [`NameAbs`, `abs_eq_iff`, `supp_abs`](../Nominal/Set/NameAbstraction.lean); actual quotient, exact support deletion |
| Freshness theorem | `FreshnessTheorem.v`: `freshness_theorem_some_any`, `freshness_theorem` | [`someAny`, `freshnessTheorem`, `freshnessTheorem_total`](../Nominal/Set/FreshQuantifier.lean); cofinite formulations and classical extraction; broad convenience wrappers remain optional |
| Binder lifting | `Example/Lambda.v`: `fcb_some_any`, `_flam` | [`FCB`, `liftFCB`, `liftFresh`, `liftFreshParam`](../Nominal/Set/FCB.lean); reusable partial/total/parameterized lifting and uniqueness |
| Term induction | `Example/Lambda.v`: `alpha_ind` | [`Term.strong_ind`, `strong_ind_finset`](../Instances/LambdaCalculus/Induction.lean); arbitrary predicate on quotient terms and context-generalized IH, no predicate equivariance assumption |
| Iteration | `Example/Lambda.v`: `alpha_rec`, its three constructor equations | [`recNoContext`, `recNoContextNFun`](../Instances/LambdaCalculus/Recursion.lean); graph totality/uniqueness then classical choice, public support/uniqueness contracts; handlers see recursively computed values, not original children |
| Substitution | `Example/Substitution.v`: `subst`, `subst_comp` | [`Term.subst`, `subst_subst`](../Instances/LambdaCalculus/Substitution.lean); capture avoidance and composition with distinctness/freshness premises retained |
| Reduction/confluence | No corresponding declarations in the inspected supported Rocq source | [`Beta`, `Parallel`, fresh rule induction, diamond, Church–Rosser](../Instances/LambdaCalculus.lean); full contextual reduction of open terms and uniqueness of normal forms |

This describes the delivered engineering and mathematics, without a novelty or
priority claim. A constructive supplied support need not be least, equivariant
as chosen data, or invariant under the setoid equality. Those facts cannot be
transferred mechanically into Lean's exact support equations. Similarly,
fixed-parameter substitution is supported, while its equivariance theorem
permutes the subject, variable, and replacement together.

## Archived assumptions and excluded experiments

At `lsfa2025`, `Instances/Perm.v` contains active `Admitted` proofs for
`PermPermT` and `PermNominal`. Both are listed in `_CoqProject` and imported by
the lambda development. Main supplies proofs. Thus source presence of
`alpha_ind`, `alpha_rec`, and `subst_comp` is established for both revisions;
an admission-free transitive dependency claim for the archived theorems is not.
Their exact dependency sets still require compatible builds and
`Print Assumptions`.

The active-project source scan at pinned main finds no `Admitted` after nested
comments are removed. `Name.v`'s `ATOMIC` signature requirements are implemented
by `Atom`; they must not be counted as unexplained global assumptions.
Commented alternative alpha-equivalence experiments are also not active proofs.

The tag's `Instances/ExtensionalSupportedFunctions.v` is absent from the build
list/import closure and deleted from main. Its extensionality axiom identifies
records that can store different support sets for the same function, so it must
not be reused as an extensionality principle for that representation. This is
an excluded historical experiment, not an assumption of the supported Lean code.
Main's excluded `Concretion.v` sketch tests a supplied support bound: padded
bounds can make alpha-equivalent representatives produce different partial
results. Lean's [`concreteAt_none_iff`](../Nominal/Set/Concretion.lean) instead
uses semantic freshness derived from least support. Neither excluded Rocq file
was repaired or compiler-checked here.

## Publication corrections still separate from this release

The published v1 links `lsfa2025` and describes alpha-structural principles as
future work. That publication status must be distinguished from the implemented
source in the linked artifact and from Lean's completed case study.
[Published v1](https://arxiv.org/html/2509.25883v1).

The following corrections remain editorial work in the external sources:

- Equation (3)'s converse conflates least support with strong support. Swapping
  two distinct atoms fixes their unordered pair but moves both support atoms;
  [CoreContracts](../Examples/CoreContracts.lean) checks this counterexample.
- With ordinary function composition, the left-action law has order
  `(g * h) • x = g • (h • x)`. The reversed order in the published display needs
  correction or an explicit opposite-multiplication convention. Rocq's swap-list
  operation and Lean's usual composition must be translated deliberately.
- Nominal endpoints alone do not imply finite support of every function.
  Some/Any needs the relevant equivariance/support hypotheses. A limitation of
  a particular `Prop` interface does not prove logical impossibility of
  relational Some/Any or alpha-compatible induction.

These points agree with the source-level findings in the
[historical review](reviews/2026-10-02-development-review.md#rocq-and-article-findings)
and the checked [published formulas](https://arxiv.org/html/2509.25883v1).

For the constructive-support claim, Swan's **arXiv:1702.01556v1**, Theorems 3.3
and 3.5, derives WLPO from the specified general support principles; Remark 3.6
gives the stronger restricted excluded-middle consequence for some principles.
These results do not establish the manuscript's unqualified equivalence with
WLPO. State the base constructive theory and the exact principle and implication.
[Swan's versioned paper](https://arxiv.org/pdf/1702.01556v1).

At the pinned article revision, `LSFA 2025 (EPTCS)/EPTCS/main.tex` includes the
short article's four sections. The nested
`Nominal Sets in Rocq (Extended)/Extended Version/main-extended.tex` reaches the
extended alpha-principle material; the directory name alone is not an inclusion
claim. The older review records incorrect draft alpha-rule bodies, motive and
handler types, and identification of arbitrary avoidance sets with predicate
support. These remain external draft issues; the Lean tutorial states the
checked contracts. No manuscript version is claimed amended or rebuilt.

D-03 therefore remains partial: this repository now has a pinned correspondence
account, while compatible Rocq builds/assumption reports and publication
corrections remain explicitly unverified external work.
