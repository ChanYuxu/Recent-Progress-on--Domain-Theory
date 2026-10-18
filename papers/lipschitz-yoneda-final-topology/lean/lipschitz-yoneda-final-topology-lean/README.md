# Final topologies of Lipschitz Yoneda-continuous maps: standalone Lean 4 project

This package depends directly only on Mathlib. Required supporting definitions and proofs are included in the package.

## Build

Lean and Mathlib are pinned to `v4.30.0-rc2`; the lockfile fixes Mathlib commit `5450b53e5ddc75d46418fabb605edbf36bd0beb6` and its transitive dependencies.

From this directory, run:

```sh
lake exe cache get
lake build
lake env lean --trust=0 StandaloneAxiomAudit.lean
```

The public entry point is `LipschitzYonedaFinalTopology.lean`. Original `Practice.DomainTheory.Papers.*` import paths and declaration names remain available. The package includes 41 Lean files; generated build caches are excluded.

## Mathematical scope

The preserved 38 paper modules include the generalized main implication and its checked completion constructions. The remaining manuscript boundaries in `FORMALIZATION_STATUS.md` are unchanged. Human expert review remains pending.

## Assumptions

The paper declaration audit permits only `propext`, `Classical.choice`, and `Quot.sound`.

`LEAN-FILE-HASHES.sha256` binds the released Lean sources. Compilation and packaging checks do not replace source-fidelity assessment or human expert review; human review remains pending.
