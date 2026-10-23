# Verification snapshot and its boundaries

Snapshot date: 2026-10-15. This is a record of the fresh independent recheck of the original mathematical project, not a newly invented success status for this archive.

## Checked result

`CHFubini.paper_main` proves the manuscript's CH-conditional analytic main theorem, with the genuine probability valuations, full order-product Scott-open incidence witness, both actual Choquet integrals, the exact product formula and bounds, and both Scott-continuous profiles.

The audited manuscript SHA-256 is:

```text
6124b207a3addaa2adb9b02b6b5825dd8953548bca5913c2fadea66894174979
```

That hash identifies the private source used by the original recheck. A later editorial manuscript snapshot changed only its title and PDF title metadata to “The Fubini Problem for Continuous Valuations on dcpos: A Counterexample under the Continuum Hypothesis”, added an AI-use declaration stating that GPT generated the initial counterexample construction, and removed the competing-interest declaration. Outside the title, PDF title metadata, and declaration blocks it is byte-identical to the audited version. Its hash and this distinction are recorded in `verification-snapshot.json`; these edits are not presented as a new formal audit. The paper TeX source is intentionally not distributed. The mathematical Lean sources and pinned environment files are unchanged and retain their verified per-file hashes.

## Fresh machine evidence

- Lean: `v4.30.0-rc2`.
- mathlib commit: `5450b53e5ddc75d46418fabb605edbf36bd0beb6`.
- Project-cache-independent `lake build`: passed, 3,472 jobs. External dependency caches were reused; this was not a from-zero rebuild of mathlib.
- A subsequent fresh `--trust=0` type probe passed. `Verification.lean` preserves that probe's source.
- Independent inventory: 569 declarations from the 31 mathematical modules and their root module, including private/generated declarations.
- Independent checked-environment dependency graph: 45,672 reachable declarations; 379 project declarations in the main theorem's closure.
- No project-local axioms, `sorryAx`, or unsafe dependency was found.
- Actual foundational axiom footprint: `propext`, `Classical.choice`, `Quot.sound`.
- Fresh separate source/construction, topology/interface, and audit-integrity reviews were completed. This is not human expert approval.

The per-file hash equality connects this distribution to that checked source. It does not make a future changed archive verified automatically. Rebuild and repeat the affected checks after edits.

## What is not certified

1. **Full manuscript coverage.** The categorical continuous-valuation monad and the bridge to its noncommutativity are not formalized. The Section 7 quasicontinuous/core-compact positive boundary is not formalized. The three questions in the manuscript remain questions.
2. **Full specification of the fixed named sequence.** The complete recursion/avoidance existence theorem is proved. The chosen `paperSequence` is instead selected through the weaker proved injectivity plus A-properties specification. Its three properties are proved and suffice for the main theorem; no claim is made that the fixed chosen sequence already has an exported complete enumeration/recursive-condition certificate.
3. **Legacy audit reliability.** The old release gate accepted unknown relation labels, empty evidence, a false coverage count, and an added unimported axiom module in isolated tests. Its old unsafe classifier also missed unsafe opaque constants. These tools and historical success manifests are not distributed here. The recorded main-theorem result uses the independent fresh recheck instead.
4. **Human approval and foundational trust.** Human review is pending. Lean's kernel/toolchain and the usual mathlib foundations remain trust boundaries. The result is conditional on CH and is not a ZFC-only counterexample or an independence proof.

This package is a source snapshot with reproducible build/type-probe commands, not a complete portable copy of every raw recheck log. The sanitized metadata records the original recheck evidence hashes for identification, without embedding machine-specific absolute paths.
