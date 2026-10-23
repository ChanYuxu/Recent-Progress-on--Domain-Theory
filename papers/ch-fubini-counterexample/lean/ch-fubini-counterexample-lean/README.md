# The Fubini Problem for Continuous Valuations on dcpos: A Counterexample under the Continuum Hypothesis

This standalone Lean 4 project contains the mathematical source of the CH-conditional counterexample, with mathlib as its only declared package dependency. It does not import the separately formalized Domain Theory textbook.

## Build

With elan installed and network access for the pinned dependencies:

```sh
lake exe cache get
lake build
lake env lean --trust=0 Verification.lean
```

`lean-toolchain` and `lake-manifest.json` pin the environment. The target is `CHFubini`. `Verification.lean` expands the main assertion, explicitly includes the second dcpo assertion and the actual inner-integral continuity statements, and prints selected axiom footprints.

## Read the proof

Start with [MainStatement.lean](CHFubini/MainStatement.lean), then [MainTheorems.lean](CHFubini/MainTheorems.lean). The public main declaration is `CHFubini.paper_main`:

```text
CH → ∀ ε : ℝ, 0 < ε → ε < 1 → CounterexampleAt ε
```

The source objects are in [SourceConstruction.lean](CHFubini/SourceConstruction.lean), the actual layer-cake integral in [Foundations.lean](CHFubini/Foundations.lean), and the numbered source interfaces in [SourceResults.lean](CHFubini/SourceResults.lean).

## Scope, origin, and limitations

Read [VERIFICATION.md](VERIFICATION.md) and [verification-snapshot.json](verification-snapshot.json). This package preserves the reviewed mathematical `.lean` files byte-for-byte and adds a separate direct verification probe. Proofs adapted from earlier projects retain their origin comments; this is not a claim that every component was written from scratch.

The analytic main theorem is proved, but the whole manuscript is not completely formalized. In particular, categorical monad noncommutativity is not encoded, the final quasicontinuous/core-compact positive boundary is not encoded, and the fixed named sequence exposes only the three-property specification rather than the complete recursive selection specification. CH is an explicit hypothesis, not a proved axiom.

The original audit automation was found to have false-green paths. It is intentionally excluded, along with its old success manifests, experimental candidates, deliberate negative fixtures, and `.lake` caches. The snapshot below records the separate fresh recheck, not an acceptance claim based on the historical release gate. Human expert approval remains pending.

The separately distributed PDF has editorial-only title, PDF-metadata, and AI-disclosure updates. The hash of its private manuscript source is distinguished from the original audited manuscript hash in the snapshot metadata; no mathematical text or Lean proof was changed. The paper TeX is intentionally not included.
