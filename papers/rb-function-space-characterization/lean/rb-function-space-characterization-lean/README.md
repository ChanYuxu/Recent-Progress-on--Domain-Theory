# A function-space characterization of RB-domains: standalone Lean 4 project

This package depends directly only on Mathlib. Required supporting definitions and proofs are included in the package.

## Build

Lean and Mathlib are pinned to `v4.30.0-rc2`; the lockfile fixes Mathlib commit `5450b53e5ddc75d46418fabb605edbf36bd0beb6` and its transitive dependencies.

From this directory, run:

```sh
lake exe cache get
lake build
lake env lean --trust=0 StandaloneAxiomAudit.lean
```

The public entry point is `RBFunctionSpaceCharacterization.lean`. Original `Practice.DomainTheory.Papers.*` import paths and declaration names remain available. The package includes 40 Lean files; generated build caches are excluded.

## Mathematical scope

The preserved 9 paper modules cover the RB characterization through `thm:rb-characterization`, including the universal test target and finite-cover extraction. The later countably based uniform-test theorem and the FS-domain section remain outside this formalized scope. The original manuscript source SHA-256 is `05f491994ac8fd569ac3dbfc565db9ebd30c0cac4c686aa7429284dd5e4c2e54`.

## Assumptions

The final characterization retains the two cited external inputs `RBFunctionSpace.rb_functionSpace_continuous` and `RBFunctionSpace.continuous_functionSpace_compact_or_pointedComponents`. The bundled supporting textbook modules retain their historical axioms and admitted results; `StandaloneAxiomAudit.lean` rejects any additional axiom or `sorryAx` dependency in every paper declaration. The universal equivalence retains the original same-universe target restriction.

`LEAN-FILE-HASHES.sha256` binds the released Lean sources. Compilation and packaging checks do not replace source-fidelity assessment or human expert review; human review remains pending.
