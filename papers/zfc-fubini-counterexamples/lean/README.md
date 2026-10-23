# Lean 4 developments

This directory contains two standalone Lean 4 projects corresponding to the two ZFC counterexample constructions discussed in the article.

- [`filter-density-zfc-fubini`](filter-density-zfc-fubini/README.md) formalizes the density-topology and filter-dcpo construction.
- [`cantor-ideal-zfc-fubini`](cantor-ideal-zfc-fubini/README.md) formalizes the Cantor-space and null-ideal construction.

Each project pins Lean and Mathlib and records the frozen manuscript version to which its source-fidelity audit was bound. The article provides the later revised PDFs; manuscript TeX sources are not included in the Lean packages. The two versions must not be conflated: the current PDFs preserve the core constructions and conclusions, but they have not yet received a new item-by-item, hash-bound fidelity audit.

Human expert review remains pending for both developments.
