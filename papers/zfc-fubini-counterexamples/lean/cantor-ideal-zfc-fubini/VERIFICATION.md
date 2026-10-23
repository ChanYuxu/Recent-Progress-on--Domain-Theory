# Verification status

The frozen-source project audit completed on 16 October 2026 with the status `machine_accepted_human_pending`.

- 20 numbered results, 31 definitions, 13 operative claims, and 50 equation labels in the frozen manuscript were mapped;
- clean and independent-cache builds of all 50 modules passed;
- import-all checks ran with `--trust=0`;
- 1,216 project declarations and 180 mapping declarations were examined;
- the main counterexample, noncentrality, categorical noncommutativity, and the stated stage-centrality result are present in the dependency chain;
- no project-local mathematical axioms, `sorry`, `unsafe`, or `partial` dependencies were reported;
- the allowed logical dependencies were `propext`, `Classical.choice`, and `Quot.sound`;
- the independent source review reported no unresolved mathematical findings.

Several Lean proofs use standard routes different from the prose proof—for example inner regularity for directed open covers, a direct compactness argument for joint openness, Mathlib's infinite-product interface, and a direct comparison of the two canonical double-strength maps. These proof-route differences are not missing assumptions, but they prevent the development from being described as a line-by-line transcription.

This package contains the mathematical sources and pinned build files, not the very large local audit logs. A successful rebuild establishes that the included declarations type-check in the pinned environment. It does not replace mathematical review. Human expert review is pending, and the source-version boundary in `SOURCE-MATCH.md` remains in force.

For public distribution, seven provenance comments were changed from absolute local filesystem paths to project-relative paths. This is a comment-only privacy redaction: no Lean declaration or proof term was changed. The frozen audited copies and their hashes remain recorded in the private audit project.
