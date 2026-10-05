# Local validation

Use the versions recorded in `lean-toolchain`, `lakefile.toml`, and
`lake-manifest.json`: Lean **4.34.1**, Mathlib **4.34.1** at
`d13f23b723b8a846827a245b89c10fc7d3f11612`. Keep the manifest; `lake update`
is not part of validation. No CI is required.

## Setup from a source checkout

Install [elan](https://github.com/leanprover/elan), Git, and the platform C/C++
build tools. In the repository directory, run:

```sh
elan toolchain install leanprover/lean4:v4.34.1
lake exe cache get
lake build Nominal Instances Examples
```

Lake fetches the dependencies pinned by the manifest; Mathlib's cache command
downloads matching dependency artifacts. Initial setup needs network access and
disk space for the toolchain and dependencies. This recipe is documented for a
new developer; the task-9 validation reused installed tools and dependencies and
**did not test a clean dependency bootstrap**.

## Complete supported check

```sh
lake build Nominal Instances Examples
lake env lean Examples/AxiomAudit.lean
python3 scripts/check-imports.py
git diff --check
```

`lake build` defaults to `Nominal` and `Instances`; it omits examples.
The explicit three-target command checks every supported source module and all
current `Examples/*.lean` modules, including the [tutorial](../Examples/Tutorial.lean).
The [Examples umbrella](../Examples.lean) imports the supported examples;
new example files must be added to its import closure to join this check.
Expected failures inside `fail_if_success` and `#guard_msgs` are regression
checks; these example modules themselves must compile successfully.

The [axiom audit](../Examples/AxiomAudit.lean) prints headline dependencies and
fails if any declaration originating in the supported project modules
uses anything beyond `propext`, `Classical.choice`, and `Quot.sound`. It includes
public/private declarations and root or `Equiv.Perm` names defined by `Nominal`
and `Instances`, not every Mathlib declaration. Running it directly avoids relying on Lake's replay of a cached
audit. Other example modules also audit their own client proofs.

For a focused check, build imports first, then run, for example:

```sh
lake build Nominal Instances
lake env lean Examples/Tutorial.lean
lake env lean Examples/CoreContracts.lean
lake env lean Examples/Freshness.lean
lake env lean Examples/NFun.lean
lake env lean Examples/NFunSupport.lean
lake env lean Examples/NFunLambda.lean
```

The full target additionally includes constructor/induction consumers,
contextual beta and parallel reductions, fresh inversion, simultaneous
substitution, diamond, Church–Rosser, and normal-form uniqueness. See
[the tutorial](tutorial.md) and [the release assessment](release-assessment.md).

## Fresh project artifacts

```sh
python3 scripts/fresh-build.py
```

The [script](../scripts/fresh-build.py) copies the current core, case study,
examples, and pinned configuration into a new printed `/tmp/nominal-fresh-*`
directory. It starts without `.lake/build`, links the existing `.lake/packages`,
builds all three targets, and reruns the axiom audit. It preserves the working
tree and retains the snapshot for inspection. The printed SHA-256 fingerprints
sorted relative paths and contents of the copied source/configuration, before
any artifacts or dependency links exist. This verifies fresh **project**
elaboration using cached **dependencies**; it is neither a clean-machine test
nor a build from committed sources when the working tree has changes.

Inspect warnings individually. Current policy keeps the scoped naming-linter
exception for the established `Nominal.Set.Nominal` name and explicit discrete
action definitions; it does not globally disable warnings. No seal boundaries
should be removed without paired measurements on an actual client.

For timing a client, build its imports and use `/usr/bin/time` with
`lake env lean Examples/NFunLambda.lean`. Record the source revision, repeated
runs, machine/cache conditions, and the same command on both versions before
claiming an improvement. Task 9 claims API improvements, not a speedup.
