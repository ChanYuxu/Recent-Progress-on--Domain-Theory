# Source match

The completed source-fidelity audit is bound to a private frozen manuscript snapshot:

- SHA-256: `8948117e90bb7672ff31610f6bdaab3a89c8961652857940ff7d62619288b3c4`
- length: 1,254 lines

The PDF currently distributed with the article was compiled from a later private, revised manuscript snapshot:

- SHA-256: `e8426062fcfa5b4da2ffa79747944073af8967c26014c34f609766c7dcdf9626`
- length: 1,403 lines

The paper TeX sources are intentionally not distributed. The later manuscript preserves the same Cantor-space/null-ideal construction and final Fubini counterexample, but it reformulates and strengthens several statements. For example, the displayed lower bound for the final constant is sharpened to `1/4 ≤ q ≤ 1/2`, and some intermediate interfaces are reorganized. No new item-by-item, hash-bound manuscript-to-Lean audit has been run for that later source. The Lean project should therefore be described as a complete audited formalization of the frozen manuscript, and as a matching formal development for the core construction in the revised PDF—not as an exact line-by-line formalization of the revised PDF.
