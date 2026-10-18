# Verification and source-version note

## Source identity

- Official arXiv v1: [arXiv:2610.22033v1](https://arxiv.org/abs/2610.22033v1), source SHA-256 `70d3b3895089df5564b68fa9fa225833e09d311d11d82382d41e229df61c6e73`.
- Hash-bound audit target: the pre-upload frozen draft, source SHA-256 `9bba1776d112ff696b933960a63eefc627bb65f41f3cc4013025daeab82337bc`.

The two source files are not byte-identical. A direct unified diff has seven editorial regions: the abstract, short introductory and preliminary explanations, display delimiters, the transfer-theorem preface, one section heading, and the generative-AI declaration. No numbered theorem, lemma, proposition, definition, mathematical construction, or proof body changed. Accordingly, the Lean development covers the mathematical content used in arXiv v1, while the formal audit remains explicitly bound to the frozen pre-upload source rather than to the arXiv source file itself.

## Recorded validation

The original local project records:

- a clean project build and a separate project-cache-free rebuild;
- `--trust=0` checks on the principal source-facing declarations;
- 69 active Lean modules and 1,379 project declarations, including 128 private declarations;
- no project-local axioms, `sorryAx`, or unsafe proof dependency;
- only `propext`, `Classical.choice`, and `Quot.sound` in the allowed transitive axiom footprint;
- an independent adversarial review covering the manuscript, the construction, and the formalized He--Zhang dependency.

The original status is machine-checked and independently reviewed, with human expert review pending. On 16 October 2026, the copied mathematical source was compared byte-for-byte with the original Lean tree and the original project again completed `lake build CoreCompactSimplified` successfully. The file-by-file digests in `LEAN-FILE-HASHES.sha256` identify this distribution.

The revised supplementary material supplied alongside the website article is a separate document. Its six pointed finite-configuration cases, positive-height variants, direct unpointed example, and additional comparisons are not claimed to be formalized by this Lean package.

No manuscript TeX source is included in this distribution.
