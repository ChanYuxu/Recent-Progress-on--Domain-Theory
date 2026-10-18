# Lean source browser

The standalone project is under [`rb-function-space-characterization-lean/README.md`](rb-function-space-characterization-lean/README.md). The downloadable [`lean-source.zip`](../lean-source.zip) contains the same 46 project files, including 40 Lean sources.

Mathlib is the only direct external dependency. From the extracted project root, run:

```sh
lake exe cache get
lake build
lake env lean --trust=0 StandaloneAxiomAudit.lean
```

The project README describes the mathematical scope and assumptions.
