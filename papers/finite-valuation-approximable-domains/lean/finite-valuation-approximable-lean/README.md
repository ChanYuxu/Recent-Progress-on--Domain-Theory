# Finite-Valuation Approximable Domains: Lean 4 companion

This standalone Lake project depends directly only on pinned Mathlib. The local `OrderTheory.lean` provides the required order and domain theory interfaces.

## Build

```sh
lake exe cache get
lake build
lake env lean FiniteValuationApproximable/AxiomAudit.lean
```

The toolchain and dependencies are fixed in `lean-toolchain`, `lakefile.toml`, and `lake-manifest.json`.

## Entry points and scope

`FiniteValuationApproximable.lean` is the aggregate import. `FiniteValuationApproximable/MainTheorems.lean` collects the four main-theorem clauses and the categorical and monadic consequences. `FiniteValuationApproximable/AxiomAudit.lean` prints the transitive axiom dependencies of the headline results.

The main theorem has Lean proofs using only `propext`, `Classical.choice`, and `Quot.sound`. Detailed coverage and the unformalized comparison material are described in `FiniteValuationApproximable/FORMALIZATION_STATUS.md`. Compilation does not by itself establish manuscript-to-Lean semantic fidelity or replace human mathematical review.
