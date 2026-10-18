# Lean 4 companion to arXiv:2610.22033

This standalone Lake project contains the Lean 4 development for the construction and results in Yuxu Chen's paper [*A non-sober core-compact meet-continuous dcpo*](https://arxiv.org/abs/2610.22033v1).

The principal declarations are:

- `CoreCompactSimplified.main_theorem`: the complete existence theorem, including non-local compactness;
- `CoreCompactSimplified.coreCompact_meetContinuous_not_sober`: the negative answer to the sobriety question;
- `CoreCompactSimplified.locallyCompact_sober_not_CsigmaUnique`: the Scott-closed-lattice non-uniqueness consequence;
- `CoreCompactSimplified.HeZhang.theorem_4_13`: the formalized sobriety theorem used to derive non-local compactness.

Build with:

```sh
lake build CoreCompactSimplified
```

Lean 4.30.0-rc2 and the pinned mathlib revision are recorded in `lean-toolchain` and `lake-manifest.json`.

## Source and verification boundary

The hash-bound audit was performed against a pre-upload frozen draft. The official arXiv v1 source is not byte-for-byte identical: its editorial changes rewrite the abstract, shorten explanatory prose, adjust display formatting and section headings, and revise the generative-AI declaration. Direct comparison found no change to a numbered mathematical statement or proof body. See `VERIFICATION.md` for the exact hashes and validation status.

The original audit reports machine checks and an independent adversarial review as passed, with human expert review still pending. This distribution preserves the mathematical `.lean` files and the pinned build metadata, but omits private audit logs, absolute local paths, and every manuscript TeX source.
