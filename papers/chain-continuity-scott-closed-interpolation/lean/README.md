# Lean source browser

The standalone project is under [`chain-approximation-lean/README.md`](chain-approximation-lean/README.md). The downloadable [`lean-source.zip`](../lean-source.zip) contains the same 31 project files, including 27 Lean sources.

Mathlib is the only direct external dependency. From the extracted project root, run:

```sh
lake exe cache get
lake build ChainApproximation
```

See the [source-version note](../SOURCE-VERSIONS.md) for differences between the accompanying PDF and the formalized manuscript.
