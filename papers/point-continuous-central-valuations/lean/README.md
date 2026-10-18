# Lean source browser

The standalone project is under [`point-central-fubini-lean/README.md`](point-central-fubini-lean/README.md). The downloadable [`lean-source.zip`](../lean-source.zip) contains the same 47 project files, including 41 Lean sources.

Mathlib is the only direct external dependency. From the extracted project root, run:

```sh
lake exe cache get
lake build
lake env lean PointCentralFubini/AxiomAudit.lean
```

The project README describes the mathematical scope and assumptions.
