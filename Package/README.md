# Package foundation kernel

This is the F02 + F03a increment of the new nominal package. It uses the pinned
Lean/Mathlib 4.34.1 and imports Mathlib directly. The reference `Nominal/` and
`Instances/` development remains separate.

```lean
import Package
open NominalPackage
open scoped Pointwise -- for the finite-set image action
```

`Perm A` is the subgroup of `Equiv.Perm A` with a finite moved-point set.
It supports ordinary application, group operations, coercion to `Equiv.Perm`,
`ext`, and directed computation lemmas. The group needs neither infinite atoms
nor decidable equality; `Perm.swap` takes `[DecidableEq A]`.

| Interface | Public declarations |
| --- | --- |
| Group/application | `Perm.ext`, `one_apply`, `mul_apply`, `inv_apply_apply`, `apply_inv_apply`, `toEquiv_*` |
| Moved points | `Perm.moved`, `moved_finite`, `moved_mul_subset`, `moved_inv`, `moved_conj` |
| Swaps | `Perm.swap`, `swap_apply_left/right`, `swap_apply_of_ne_of_ne`, `swap_self`, `swap_inv`, `swap_mul_self`, `conj_swap`, `moved_swap` |
| Canonical atom action | `Perm.smul_atom`; inherited from Mathlib, with no competing atom instance |
| Products | Standard componentwise Mathlib action and projection equations |
| Finite atom sets | `Perm.smul_finset`, `Perm.mem_smul_finset`; requires the consumer's `Pointwise` scope and decidable equality |
| Explicit discrete data | `Discrete A X`, `Discrete.equiv`, `smul_mk`, `smul_val` |
| Ordinary equivariant maps | `Equivariant A f`, `Equivariant.id`, `.comp`, `.fst`, `.snd`, `.pair` |

Atom and carrier universes are independent. `Discrete A X : Type v` retains the
universe of `X : Type v`. Its ordinary type equivalence to X does not identify
an independently chosen action on X. Bare permutation groups keep their usual
left-multiplication action; bare functions keep the pointwise codomain action.
Neither is silently changed to conjugation.

Persistent usage examples are reserved for future case studies. This increment
contains the foundation modules and their audit, without a `Package/Examples`
layer. It supplies no support, freshness, quotient, binder or recursion theory;
F03b retains the support-facing permutation obligations, and PKG-01 is later work.

## Verification

```sh
lake build Package +Package.Tests.AxiomAudit
lake env lean Package/Tests/AxiomAudit.lean
python3 Package/Scripts/check-imports.py --self-test
python3 Package/Scripts/check-imports.py
git diff --check
```

The public root imports both foundation modules. The coverage script inventories
all Package Lean sources and checks the separate production and audit closures.
It rejects unclassified sources, missing local imports, production-to-audit
imports and reference-library dependencies. Its header parser is pinned Lean's
`--deps-json`; per-file errors are checked even when the process exits zero.
Header discovery does not replace full Lean compilation or validate body syntax.
The checker self-tests use temporary source trees outside the repository.

The audit traverses production declarations by their originating module, including
private names, and checks transitive axiom dependencies. It fails on zero
production declarations or any axiom beyond `propext`, `Classical.choice` and
`Quot.sound`. Its rejection tests use simulated names, never new axiom declarations.
Run the direct audit command when Lake reports its compiled module is cached.

The default Lake targets and old validation scripts still cover the reference
library only. `lake build Nominal Instances Examples`, its direct axiom audit,
and `python3 scripts/check-imports.py` check reference preservation separately.
The old fresh-build helper does not copy Package and cannot certify a fresh
Package build. Report cache/rebuild conditions for commands actually run.

The accompanying [LaTeX article](../docs/article/main.tex) describes the mathematics
and its implementation. Compile it from `docs/article` with:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir=/tmp/nominal-package-article-build main.tex
```

Create that output directory if necessary. Keep generated manuscript files out
of the source tree. Task status and evidence live in the
[package roadmap](../docs/nominal-package-roadmap.md).
