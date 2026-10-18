# Continuity and Interpolation for Chain Approximation: Lean 4 companion

This standalone project depends directly only on pinned Mathlib. It contains 27 Lean files covering chain approximation, Scott-closed interpolation, and the locally finite Jónsson algebra construction.

## Build

The toolchain and dependencies are fixed in `lean-toolchain`, `lakefile.toml`, and `lake-manifest.json`.

```sh
lake exe cache get
lake build ChainApproximation
```

The aggregate entry point is `ChainApproximation.lean`. The main theorem is in `ChainApproximation/Main.lean`; the locally finite Jónsson construction is in `ChainApproximation/JonssonLF.lean`.

## Mathematical scope

The Lean development corresponds to the earlier manuscript *Continuity and Interpolation for Chain Approximation*, SHA-256 `fb98ea2b95418ee17dcebaee23c905a089a32ceb56a7a8d2217ec3806d80f8d1`. It includes the 19 numbered results of that version and directly proves the locally finite Jónsson existence consequence. Devlin's more general theorem and its published proof are not formalized.

The accompanying arXiv v1 PDF adds a countably based proposition and a Scott-basis clause to the main theorem. Those additions have not been source-audited in this development. See the website's source-version note before treating this package as complete coverage of arXiv v1.

The recorded transitive axiom footprint contains only `propext`, `Classical.choice`, and `Quot.sound`, with no project-local mathematical axiom or admitted proof. Human mathematical approval remains pending.
