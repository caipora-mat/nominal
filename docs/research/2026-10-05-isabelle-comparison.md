# Isabelle comparison and rule-induction criteria

Date: 2026-10-05. Research evidence, not a port or an implemented Lean package.
Read with the [predicate investigation](2026-10-05-predicate-foundations.md),
[contracts](2026-10-05-package-contracts.md), and
[architecture proposal](2026-10-05-package-architecture.md).

The documentation revision at
`7fed53a2e5fc67379f86f085515e310e7c1fddb7` follows the
[architectural freedom policy](README.md#architectural-freedom). New
implementation, including replacement foundations, belongs under top-level
`Package/`. Existing Lean code and the sources below are evidence and possible
proof material, not required APIs or representations. Reuse, adaptation and
replacement of actions, support, functions, predicates, abstraction, quotients
and induction are all available; inherited classes, universes, modules, seals
and compatibility interfaces impose no mandate. Preserve the mathematical
contracts and theorem strengths. The recorded source versions and checks below
remain historical evidence; this revision runs no external build or Lean probe.

## Versions and verification boundary

| Source | Inspected version | Evidence |
| --- | --- | --- |
| Urban–Berghofer, *Nominal Isabelle* manual | Title-page date 22 December 2008; PDF SHA-256 `7a95a7fa82f5967b5ba17f04a1fb01486e765e710373d421e6a48a11096cbec1` | Full PDF obtained; §§4.2–4.5 and Church–Rosser example checked |
| Urban–Kaliszyk, *General Bindings and Alpha-Equivalence in Nominal Isabelle* | LMCS 8(2:14), 2012, DOI `10.2168/LMCS-8(2:14)2012`; PDF SHA-256 `39d67a606e4861fa7205679ac9f3d4c849df6cd4ba1b93d9711d78208213258e` | Published paper, especially §§4–7 |
| AFP Nominal2 source | Isabelle AFP development mirror commit `0f498441e41026d1f5e677300353f5ba31a77f5a`, commit timestamp 2026-10-05 00:46:51 UTC | Six files downloaded at that exact revision and source-reviewed; not an Isabelle release/build claim |
| van Brügge–McKinna–Popescu–Traytel, *Barendregt Convenes with Knaster and Tarski* | PACMPL 9, POPL, Article 57, January 2025; DOI `10.1145/3704893`; version-of-record PDF SHA-256 `a15ca78261cf66d9fd90c73f63d331f00ec0bed7691e9684ecca25549a0c6bbf` | Definition 6, Theorem 7, §§6–7 and implementation discussion checked |
| Reference Lean client | `4279ba92efacd77b3b96e507631502272b489999` plus preserved working tree | Historical local libraries/examples build, direct tutorial and axiom audit; details in architecture proposal; does not validate `Package/` |

Primary links: [original manual](https://isabelle.in.tum.de/nominal/manual/nominal_datatype_manual.pdf),
[published Nominal2 paper](https://lmcs.episciences.org/813/pdf),
[pinned Nominal2 tree](https://github.com/isabelle-prover/mirror-afp-devel/tree/0f498441e41026d1f5e677300353f5ba31a77f5a/thys/Nominal2),
[2025 rule-induction paper](https://eprints.whiterose.ac.uk/id/eprint/222673/1/3704893.pdf).

`isabelle`, `coqc`, `rocq`, and `opam` were unavailable in this session. No
external proof development was built. Browser retrieval of several Nominal2
HTML pages failed; pinned source download succeeded after the sandbox DNS
restriction required approved network access. Downloads stayed in `/tmp`.
The initially downloaded moving `master` file was replaced as evidence by files
fetched using the exact commit above. This does not identify the revision behind
earlier unversioned AFP browser pages.

## Original Nominal: the relevant contracts

The 2008 manual's equation (4.2), printed p.34, generalizes every induction
hypothesis over a freshness context and makes the lambda binder fresh for that
context. It has no finite-support premise on the property being proved.
Section 4.5 treats rule induction separately: relation equivariance and
variable-convention compatibility obligations are required. The earlier
Church–Rosser example adds freshness premises to its parallel contraction rule
and explains the resulting equivalence obligation. Section 4.4's
`nominal_primrec` exposes freshness conditions in equations and proof obligations.
These are three separate contracts, not consequences of a syntax declaration
alone. [Manual, §§4.2–4.5 and pp.10–12](https://isabelle.in.tum.de/nominal/manual/nominal_datatype_manual.pdf).

Lean correspondence: preserve the arbitrary-motive strength demonstrated by
`Term.strong_ind` and both reduction `strong_ind` theorems. Their names, proofs
and concrete action/quotient implementations are optional references for new
`Package/` results. The reference Lean relations are unrestricted; their proofs
explicitly rename body premises and use `subst_rename`. Adopting an older
package's stronger syntactic side conditions would require an equivalence
theorem, not a silent weakening of the intended reduction semantics.

## Nominal2: predicates, generation, and functions

The published 2012 construction defines raw syntax, alpha relations and
quotients, then derives the public reasoning infrastructure. Lemmas 6.1–6.2
establish equivariance/equivalence prerequisites; Theorem 6.3 identifies support
with free atoms; equation (7.1) supplies context-generalized strong induction.
Its proof uses size measures and fresh cases. Section 4 restricts binding
clauses so a body's scope is unambiguous. Generalized list/set binding modes are
additional semantic choices, not interchangeable annotations. This gives a
precedent for generated proofs and explicit scope metadata, but does not settle
Lean positivity or require that this project support generalized binders.
[Published paper, §§4–7](https://lmcs.episciences.org/813/pdf).

The pinned implementation supplies more precise engineering evidence:

| File/declarations | Source reading | Consequence for this proposal |
| --- | --- | --- |
| `Nominal2_Base.thy`: `permute_fun_def`, `permute_bool_def`, `permute_fun_app_eq` | Function action is conjugation; Boolean truth values have trivial action | Preserve the conjugation/pointwise distinction in the chosen Lean action interface; `PFun α X Prop` is one reference realization, not a required wrapper |
| Same file: `eq_eqvt`, `Not_eqvt`, `conj_eqvt`, `imp_eqvt`, `all_eqvt`, `ex_eqvt`, `Collect_eqvt` | Logical operations have proved permutation laws | Expression-aware proof generation needs certified logic rules under the selected foundations; existing proofs may be reused, adapted or replaced without introducing a separate formula logic |
| `Nominal2.thy` and `nominal_dt_quot.ML`: `define_qtypes`, `lift_raw_const`, `prove_fsupp`, `prove_strong_induct` | Separate metadata/raw/alpha/quotient modules; explicit theorem generation | Keep proof responsibilities modular and kernel checked |
| `nominal_function_core.ML`: `mk_compat_proof_obligations`, `mk_completeness`, `define_graph`, `mk_uniqueness_case` | Compatibility, coverage and graph uniqueness are distinct proof tasks | Do not infer well-definedness or support merely from equations that look recursive |
| `nominal_inductive.ML`: `mk_vc_compat`, `prove_strong_inductive`, `fresh_thm` | Generates finiteness and freshness-for-conclusion obligations and constructs a context-generalized proof | Rule metadata must describe which variables can be refreshed while the conclusion is preserved |

Links to exact inspected sources:
[base theory](https://github.com/isabelle-prover/mirror-afp-devel/blob/0f498441e41026d1f5e677300353f5ba31a77f5a/thys/Nominal2/Nominal2_Base.thy),
[quotient generation](https://github.com/isabelle-prover/mirror-afp-devel/blob/0f498441e41026d1f5e677300353f5ba31a77f5a/thys/Nominal2/nominal_dt_quot.ML),
[functions](https://github.com/isabelle-prover/mirror-afp-devel/blob/0f498441e41026d1f5e677300353f5ba31a77f5a/thys/Nominal2/nominal_function_core.ML),
[rule induction](https://github.com/isabelle-prover/mirror-afp-devel/blob/0f498441e41026d1f5e677300353f5ba31a77f5a/thys/Nominal2/nominal_inductive.ML).

These observations do not imply that every ordinary Isabelle function is
finitely supported. In Lean, a truth value having empty support likewise does
not give its entire predicate empty support. Ordinary `Prop` goals and a
certified supported-predicate object serve different purposes.

Source SHA-256 values for reproduction:

```text
Nominal2_Base.thy        654c71808713e38eb5ee375344f16dc8f491237946a99fcde8a84cba41626246
Nominal2.thy             2aa1b08cbe81bf8df273e30cd8fb682132ca7e6a59f063acbbd8794cb8be12c1
nominal_dt_alpha.ML      2b3ed4ebc29f49503d7014c213aae376ba4e223e734bf23fecdfab020b4e208f
nominal_dt_quot.ML       b61762c6a95b2b221e870f3edb0607b97232c4a75e49775767875686da6a78df
nominal_function_core.ML d5553f74e7837dc513218e9e5b39b8903850fd4c503cd852a94c8a4bfe942025
nominal_inductive.ML     5f7b5b11cc23fe71c4ec32a04ebb6b81e4fac146dff2cfea8642425f85a6a329
```

## A newer sufficient criterion for rule induction

The 2025 paper's Definition 6 and Theorem 7 use a nominal carrier `T` and an operator
`G : (T → Prop) → Finset Atom → T → Prop` (notation translated to Lean).
Besides monotonicity and equivariance, refreshability requires that, for an
equivariant candidate predicate `R`, `G R B t` can be re-established with some
`B'` disjoint from `supp t`, leaving `t` unchanged. The theorem then gives strong
induction for an arbitrary motive, generalized over parameters with a finite
avoidance assignment. The parameters need not themselves form a nominal set.
Section 10 reports automation of equivariance while refreshability remains a
user obligation. This is a source theorem, not a Lean result in this repository.
[Definition 6, Theorem 7, §10](https://eprints.whiterose.ac.uk/id/eprint/222673/1/3704893.pdf).

**Proposed research application.** Compare at least these two implementations of
the judgment contract on beta, parallel reduction, and first-order eigenvariable
rules under the chosen `Package/` foundations:

1. Generate a derivation-induction proof informed by the reference Lean client,
   with local renaming/transport certificates for each rule. This route may use
   a new relation, action or abstraction representation and new proofs.
2. Prove a general semantic theorem of the above shape and generate its
   operator and certificates. Prove that the generated ordinary inductive
   relation equals the specified least closure.

The second route could reduce generator complexity; it adds a generic theorem
and a relation/least-closure correspondence obligation. Neither route permits
assuming that relation equivariance alone makes every rule binder refreshable.
The finite rule grammar, restricted to declarations whose certificates are
discharged, is the proposed automatic subset. Manual certificates could later
admit more rules without expanding the parser's trusted role. Other proof routes
remain possible if their obligations and resulting theorem strengths are made
explicit and checked; this comparison does not prescribe a representation.

An important semantic target is the reference unrestricted `Parallel.beta`:
the body premise changes under a swap, the replacement premise is preserved,
and substitution renaming preserves the target. An implementation that simply
adds a freshness premise and never proves equivalence fails the target. This
target preserves reduction behavior, not the old declaration name or API.

## Cross-source conclusion and remaining evidence

Pitts' supported powersets, Copello's alpha-compatible raw predicates, quotient
descent, and arbitrary-motive strong induction address different boundaries.
Isabelle's predicate action and automation fit this layered reading. The
[predicate note](2026-10-05-predicate-foundations.md) supplies the precise
Pitts/Copello/Rocq correspondence and Lean probes; the initial propositions note
is retained as earlier evidence rather than silently promoted to a design.

Before implementing the judgment generator, require the selected rule proof
route to pass both reduction and eigenvariable examples in `Package/`. The
earlier Lean proofs provide comparison material, not certification for a new
representation. Name any foundational requirements in the
[package roadmap](../nominal-package-roadmap.md): PKG-F01–PKG-F05 precede bounded
predicate task PKG-01, and later judgment work must list additional dependencies
explicitly. This is neither an implicit full rewrite nor a requirement to retain
the current core. New package build targets and an audit reaching the new
declarations must be established; the reference-library audit cannot stand in
for them. This documentation revision creates no implementation or build setup.

A broader survey of binding-aware datatype work (including bounded natural
functors) belongs in the
article's related-work record; no exhaustiveness or novelty claim is made here.
The selected five case studies are tests of this package's promised contracts,
not evidence that those contracts have already been generated.

## Sources for the added case studies

For π-calculus, Bengtson–Parrow, *Formalising the pi-calculus using nominal
logic*, LMCS **5(2:16)**, 2009, DOI `10.2168/LMCS-5(2:16)2009`, supplies an
established nominal case study with alpha-equated agents, strong induction and
several transition/bisimulation variants. The publication entry and abstract
were inspected here; no exact theorem correspondence or rebuilt π development
is claimed. Its role is to motivate explicit selection of transition semantics
and bound-residual scope before PKG-09.
[Published entry](https://lmcs.episciences.org/832).

For μ-calculus, Bradfield–Stirling's author-hosted *Modal Mu-Calculi* manuscript,
§§3.3–3.4, distinguishes syntactic positivity from alpha binding and defines
semantics using arbitrary variable valuations into sets of states. This supports
the proposed positivity/valuation acceptance tests, not a claim that such
valuations are nominal. The inspected file is the 30-page author manuscript,
not silently identified with the paginated 2007 *Handbook of Modal Logic*
chapter; SHA-256 `00525398d8999dd9b7e5d274f76b8c24c350b5a374169f235481ad0b45266fcf`,
accessed 2026-10-05. The modal variant is still a proposal for the author's
selected μ-calculus study.
[Author manuscript](https://www.julianbradfield.org/Research/MLH-bradstir.pdf).
