# Lean source browser

The standalone project is under [`corecompact-simplified-lean/README.md`](corecompact-simplified-lean/README.md). The downloadable [`lean-source.zip`](../lean-source.zip) contains the same 75 project files, including 69 Lean sources.

Mathlib is the only direct external dependency. From the extracted project root, run:

```sh
lake exe cache get
lake build
```

The project README describes the mathematical scope and assumptions.
