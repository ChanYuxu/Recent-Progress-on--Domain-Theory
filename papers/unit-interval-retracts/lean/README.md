# Lean source browser

The standalone project is under [`unit-interval-retracts-lean/README.md`](unit-interval-retracts-lean/README.md). The downloadable [`lean-source.zip`](../lean-source.zip) contains the same 30 project files, including 24 Lean sources.

Mathlib is the only direct external dependency. From the extracted project root, run:

```sh
lake exe cache get
lake build
lake env lean --trust=0 StandaloneAxiomAudit.lean
```

The project README describes the mathematical scope and assumptions.
