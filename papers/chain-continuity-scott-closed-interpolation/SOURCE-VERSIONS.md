# Paper and Lean source versions

The PDF in this package is [arXiv:2610.18692v1](https://arxiv.org/abs/2610.18692v1), *Chain Continuity and Scott-Closed Interpolation*, submitted on 13 October 2026. It has 20 pages and SHA-256 `271006a8e40402f0303f6d2454d13cd9491ce1a77934b8b0f024a1270389c653`.

The accompanying Lean project was source-mapped and independently reviewed against an earlier author-supplied private manuscript snapshot, *Continuity and Interpolation for Chain Approximation*, SHA-256 `fb98ea2b95418ee17dcebaee23c905a089a32ceb56a7a8d2217ec3806d80f8d1`. The paper TeX is intentionally not distributed. The arXiv v1 source differs; its main TeX file has SHA-256 `e8ae7b02a6ec9e4a10eb37ec09374064106b6932e53a5cf7effb2f30c6bd95ca`.

Comparing the numbered result statements by their source labels gives the following substantive changes:

| arXiv v1 change | Status in the preserved Lean project |
| --- | --- |
| New `prop:countably-based`: every countably based continuous dcpo is strongly chain-continuous and has chain-below equal to way-below | No source-facing theorem for this new proposition was included in the earlier snapshot audit. |
| `thm:main` additionally says that the upper sections of the relational square form a basis for the Scott topology | The earlier main result and Scott-openness argument are proved, but this added basis clause was not part of the source-facing theorem reviewed against the earlier snapshot. |
| `thm:sharp` explicitly says “chain-continuous algebraic complete lattice” instead of “chain-continuous dcpo” | The existing Lean development separately proves algebraicity and uses the complete-lattice instance for substructures; the v1 wording has not received a fresh source-mapping review. |

The other 19 numbered result labels are shared by the two source versions. The recorded source review concerns the **earlier** snapshot, not the revised arXiv v1 text. The Lean development proves the locally finite Jónsson algebra existence consequence directly; it does not formalize Devlin’s more general theorem or reproduce its published proof. Human mathematical approval remains pending.
