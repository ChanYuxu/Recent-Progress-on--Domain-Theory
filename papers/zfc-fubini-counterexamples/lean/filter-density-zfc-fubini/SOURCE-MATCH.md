# Source match

The completed source-fidelity audit is bound to a private frozen manuscript snapshot:

- SHA-256: `8f16f81ce85634fffcfb6443fbcee19f725812cc001fab6946fe72d52c90c9d2`
- length: 1,285 lines

The PDF currently distributed with the article was compiled from a later private, reference-checked manuscript snapshot:

- SHA-256: `bbc4235f1f61d9fe1927fc870df9169bb6a5e3eb3a9aee7b77bd20a9d29219fa`
- length: 1,952 lines

The paper TeX sources are intentionally not distributed. The later manuscript says that its mathematical construction, probability law, and radii are unchanged, but it also expands and reorganizes several statements and background interfaces. No new item-by-item, hash-bound manuscript-to-Lean audit has been run for that later source. The Lean project should therefore be described as a complete audited formalization of the frozen manuscript, and as a matching formal development for the core construction in the revised PDF—not as an exact line-by-line formalization of the revised PDF.
