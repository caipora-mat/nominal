# Task 9: first-deliverable assessment

Baseline: `fasapa/next` at `b74ad34` (Church–Rosser), 2026-10-05. Changes described
here are uncommitted. Existing README changes and untracked documentation were
preserved. The [2026-10-02 review](reviews/2026-10-02-development-review.md) is a
historical snapshot: lambda integration, freshness defects, NFun adapters, and
the reduction/confluence gaps it identified have since been addressed.

## Gap assessment and dependency order

| Priority | Verified gap at task start | Disposition and validation |
| --- | --- | --- |
| Required usability, L-02/L-03 | `recNoContext` exposed computation equations, but function uniqueness and returned support/NFun contracts required graph knowledge | Expose theorem-level contracts while preserving the graph, handler requirements, and seals; iterator consumers and axiom audit |
| Useful polish, C-05/N | The same fixed-supported-function application equation occurred in the support tactic and iterator internals | Share a public NFun lemma; compile both consumers |
| Required documentation, C/D/R-07 | No single compiling path from fresh atoms through Church–Rosser; stale module names and concretion prose | Add the tutorial, correct module documentation, document foundations and boundaries |
| Required reproducibility, B-05/D-04 | Broad audits/fresh builds depended on temporary probes; two existing examples were outside the umbrella | Integrate every example; retain import-closure check, module-origin axiom audit and source-snapshot build script with dependency-cache limits |
| External verification, D-03 | Historical Rocq and manuscript claims lacked a current, scoped correspondence account | Pin source evidence and outstanding checks in [research correspondence](research-correspondence.md); do not claim external builds or corrections |

The execution checklist is ordered by dependency:

- [x] Inventory completed NFun/core/reduction APIs and classify remaining gaps.
- [x] Consolidate the demonstrated helper and expose iterator contracts; validate consumers.
- [x] Finish the compiling tutorial and accurate API/foundation documentation.
- [x] Build every supported module/example, check axioms/coherence, and rebuild fresh project artifacts.
- [x] Inspect the final diff and update roadmap statuses only against delivered criteria.

No confirmed mathematical defect was found in the completed Church–Rosser
argument. A finished confluence theorem alone was insufficient for this task:
the iterator interface, tutorial, reproducible validation, and documented
boundaries were required first-deliverable work.

## Client boundaries and lessons

`Basic.lean` constructs the alpha quotient and proves constructor/inversion,
action, and support facts. `Induction.lean` derives arbitrary-predicate strong
term induction. `Recursion.lean` owns relational iteration and classical choice.
Those implementation layers necessarily know about representatives or graph
proofs. Substitution and the reduction/confluence clients should use the public
constructor, fresh induction/inversion, iterator, and substitution equations.

The direct diamond proof uses fresh rule induction with the competing target as
the nominal context. Inversion aligns binders, and simultaneous substitution
compatibility handles the contraction overlap. Closure transfer then uses
Mathlib's relation API. There is no demonstrated need for primitive recursion,
complete development, extra container instances, or a general syntax elaborator.

Preserve arbitrary predicates and context-generalized induction hypotheses:
the avoidance context need not be the predicate's support. Keep supported
fixed-parameter operations distinct from jointly equivariant operations.
Reuse NFun coercions, curry/uncurry, `fromParam`, and `supports_nfun`; a new
adapter or tactic should address a reproducible client problem. A named theorem
with type `FinSupported ...` also makes ordinary `simp` work for `NFun.ofFun`
construction; an inline existential witness can obstruct implicit-transparency
matching. The tutorial demonstrates the named-proof route, and an explicit
`change` remains a fallback. This is a documented ergonomic limitation, not a
support inference claim.

Deferred research remains general binder-aware elaboration, broader support
search, general Some/Any/FCB convenience wrappers, generic algebraic carriers,
datatype generation, multiple atom sorts, generalized binders, universe
generalization, and executable fresh-name/substitution machinery. These are
not silently counted as delivered or made prerequisites for this release.

## Validation and readiness

The baseline `lake build Nominal Instances Examples` passed (1,028 jobs).
The final three-target build passes (1,033 jobs). The import-closure check reaches
all 37 core/case-study modules and all 15 example modules, counting umbrellas.
Two older examples were added to the `Examples` umbrella after inspection found
they were only being run directly. Their missing copyright headers and the new
audit's header were corrected; the audit heartbeat explanation was moved to the
location required by the linter. No linter was disabled for these diagnostics.

The broad axiom audit now selects declarations by their originating module,
including root and `Equiv.Perm` declarations that namespace-only scans missed.
All 1,859 declarations use only `propext`, `Classical.choice`, and `Quot.sound`;
22 headline results are also printed explicitly. Existing example audits cover
their client proofs. Independent reviews checked iterator statement strength,
action coherence, the tutorial and build coverage, with no unresolved important
finding. A source-name check resolved 578 declaration inventory entries; the
remaining entry, `nfun`, is syntax rather than a declaration.

No speedup is claimed. All existing `seal` boundaries, instance priorities and
proof strengths are preserved; the new APIs reduce client exposure to graph
witnesses. NFun computation checks and the existing performance baseline remain
in the N-01–N-05 evidence. Local wall times are validation observations, not
controlled before/after performance measurements.

The final source-snapshot build in `/tmp/nominal-fresh-5t8pueey` passed all 1,033
jobs with no warnings or errors, followed by the same 1,859-declaration audit.
It began without project artifacts and reused pinned dependency artifacts.
The build script plus explicit audit took 43.25 seconds wall time locally;
this is an observation, not an elaboration speedup claim. Source/config SHA-256:
`c3d05a4d32303bf10ec56952487916ac6aae92077a962184000f7c13f63d4170`.

The final working-tree build and direct axiom audit also passed without warnings
or errors. Import/link checks and `git diff --check` passed; new untracked files
were included in the separate whitespace/link review. The final diff was reviewed.
See [validation instructions](validation.md) for reproduction.

**Readiness:** the scoped classical core and Church–Rosser case study are ready
as a local first research deliverable. No confirmed release-blocking defect
remains in the supported Lean development. This assessment includes the API,
tutorial and validation work, not just the confluence theorem. The deliverable
is an uncommitted working-tree snapshot; nothing was committed, pushed or
published, and no CI or external repository was changed.

**Unverified external work:** a clean dependency bootstrap was not tested;
Rocq/compiler assumption checks and article corrections remain pending under
D-03. General Some/Any wrappers, broader automation and the other deferred
research listed above remain unfinished without blocking the supported scope.
A future publication claiming external artifact completeness must resolve those
external checks separately.
