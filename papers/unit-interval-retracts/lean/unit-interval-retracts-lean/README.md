# Unit-interval retracts of quasicontinuous domains: standalone Lean 4 project

This package depends directly only on Mathlib. Required supporting definitions and proofs are included in the package.

## Build

Lean and Mathlib are pinned to `v4.30.0-rc2`; the lockfile fixes Mathlib commit `5450b53e5ddc75d46418fabb605edbf36bd0beb6` and its transitive dependencies.

From this directory, run:

```sh
lake exe cache get
lake build
lake env lean --trust=0 StandaloneAxiomAudit.lean
```

The public entry point is `UnitIntervalRetracts.lean`. Original `Practice.DomainTheory.Papers.*` import paths and declaration names remain available. The package includes 24 Lean files; generated build caches are excluded.

## Mathematical scope

The preserved 17 paper modules contain the concrete lattice, finite approximation, quasicontinuity, noncontinuity, counterexample and splitting declarations. Four supporting order/topology modules are bundled locally. The original manuscript source SHA-256 is `00c59c1953e50628793d3f7a789187aa3051405999b4d72ddfbd29af41c00b04`. Item-by-item source-fidelity review remains a separate requirement.

## Assumptions

The paper declaration audit permits only `propext`, `Classical.choice`, and `Quot.sound`.

`LEAN-FILE-HASHES.sha256` binds the released Lean sources. Compilation and packaging checks do not replace source-fidelity assessment or human expert review; human review remains pending.
