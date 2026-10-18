# Lean source browser

The standalone project is under [`finite-valuation-approximable-lean/README.md`](finite-valuation-approximable-lean/README.md). The downloadable [`lean-source.zip`](../lean-source.zip) contains the same 92 project files, including 86 Lean sources.

Mathlib is the only direct external dependency. From the extracted project root, run:

```sh
lake exe cache get
lake build
lake env lean FiniteValuationApproximable/AxiomAudit.lean
```

The project README describes the mathematical scope and assumptions.
