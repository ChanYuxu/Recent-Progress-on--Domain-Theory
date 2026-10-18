# Point-Continuous and Central Valuations: Lean 4 companion

This standalone Lake project depends directly only on Mathlib, pinned with Lean to `v4.30.0-rc2`.

## Build

```sh
lake exe cache get
lake build
lake env lean PointCentralFubini/AxiomAudit.lean
```

Import `PointCentralFubini` for the complete development. The public theorem modules include `Central.lean`, `SecondCountable.lean`, `Incidence.lean`, and `SorgenfreyFubini.lean` under `PointCentralFubini/`.

## Mathematical scope and assumptions

The development covers Sections 2–5 of *Point-Continuous and Central Valuations: Countable Spaces and the Sorgenfrey–Smyth dcpo*. The appendix and explanatory remarks are outside the formalized scope.

The 23 numbered main-text items comprise 19 proved results, three cited literature assumptions, and one definition. Supporting results introduce additional literature assumptions: ten cited axioms remain in total. They have not been reproved internally, so the development is not fully self-contained. Their declarations, statements and sources are listed in `external-sources.json`; item coverage and proof boundaries are in `FORMALIZATION_STATUS.md`.

There are no admitted proofs or unregistered manuscript-theorem axioms in the paper development. Independent source-to-Lean review and human mathematical approval remain pending.
