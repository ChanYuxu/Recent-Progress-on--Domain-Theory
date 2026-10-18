# Formalization status: final topologies of Lipschitz Yoneda-continuous maps

## Source and scope

- Source SHA-256: `3b1e4238812210a9c90235a4bf484739a51e7516e32a1882705f5d1496fdfd0d`
- Source title: *Final Topologies of Lipschitz Yoneda-Continuous Maps: A Cone-Forest Theorem, Metric Completeness, and Completion Visibility*
- Lean toolchain: Lean `v4.30.0-rc2`, pinned by this repository

This is a rigorous partial formalization of the manuscript that **does prove
its headline theorem**:

```lean
theorem QuasiMetric.IsContinuous.propertyD
    (hcontinuous : d.IsContinuous)
    (hcomplete : d.IsYonedaComplete) :
    d.PropertyD
```

The theorem and its complete local dependency path contain no `sorry`,
`admit`, project-specific `axiom`, `opaque`, or `unsafe` declaration.  The
representative kernel audit reports only `propext`, `Classical.choice`, and
`Quot.sound`.  The separate metric characterization and the later
completion-visibility specialization are not claimed as formalized.

## Status vocabulary

- **P3 — kernel checked:** the stated Lean declaration is proved, with no
  project-specific axiom and no admitted proof.
- **P2 — represented with a declared boundary:** a faithful core is encoded,
  but the stated source claim has an explicit restriction or missing clause.
- **P1 — interface or paper proof only:** dependencies are identified, but no
  Lean proof of the complete source claim is present.
- **P0 — not represented:** no corresponding Lean statement is claimed.

## Claim ledger

| Source claim | Source locator | Lean artifact | Status | Exact boundary |
|---|---:|---|---|---|
| Property D and its formal characterizations, `prop:formal-iff` | lines 185–228 | `LayeredTopology.lean` | P3 | Quotient-map, universal-continuity, Sierpiński, and closed-set formulations are all proved. Integer index `n` represents source layer `n+1`. |
| Increasing layers and cofinal integer cover (F1) | lines 303–308 | `QuasiMetric.IsLipschitz.mono`, `integerLayer_mono`, `integerLayer_cover`, `propertyD_iff_all_positive_layers` | P3 | Lower semicontinuity and Yoneda continuity are independent of the selected Lipschitz constant, exactly as in the source. |
| Quasi-metric, formal balls, `d`-Scott topology, Cauchy nets and `d`-limits | lines 108–179 | `QuasiMetric.lean` | P2 | The direct net records quantify over directed index types in the carrier universe. Universe-lift invariance is used where needed but not packaged as a general theorem. |
| Standardness consequences for directed formal balls | lines 278–298 and cited GLN results | `StandardConsequences.lean`, `CauchyWeightedSubnet.lean` | P3 | Radius-infimum, shift/unshift of suprema, Cauchy weighted subnets, and the equivalence between zero-radius suprema and `d`-limits are proved from the local definitions. |
| Upperness, `lem:upper` | lines 355–370 | `QuasiMetric.layerwiseOpen_isUpper` | P3 | Uses the cofinal integer layers and the exact specialization-order restriction theorem for subtypes. |
| Cone formula, finite maxima, and finite interpolation (F4 and `lem:interpolation`) | lines 320–351 and 375–421 | `Cones.lean`, `Interpolation.lean`, `SharpContinuity.lean`, `SharpConverse.lean`, `ConeContinuity.lean`, `StandardConeFacts.lean` | P3 | Scott continuity of the sharp transform, lower semicontinuity and Yoneda continuity of cones, and the finite interpolation statement are all discharged from standardness and the source-facing hypotheses used by the algebraic theorem. |
| Compact path space and cone-forest construction inside `thm:algebraic` | lines 423–443 and 447–661 | `Forest.lean`, `ConeForest.lean`, `PathEndpoint.lean`, `ConeApproximation.lean`, `ConeForestConstruction.lean`, `AlgebraicCore.lean` | P3 | Recursive levels, finite and infinite endpoints, zero-radius formal-ball suprema, path continuity, compact saturation, uniform margins, and the final compact-open neighborhood are assembled. |
| Algebraic Yoneda-complete case, `thm:algebraic` | lines 447–661 | `QuasiMetric.IsAlgebraic.propertyD` in `AlgebraicTheorem.lean` | P3 | The theorem uses the manuscript's equivalent source-facing characterization: standardness plus enough center points. |
| Quasi-metric retract transfer, `lem:retract` | lines 668–697 | `Retract.lean`, `LowerMapSuprema.lean`, `YonedaDScottRetract.propertyD` | P3 | Nonexpansiveness, Yoneda continuity, `d`-Scott continuity, layer preservation, the retraction equation, arbitrary pointwise suprema of lower maps, and Scott continuity of precomposition are all proved. Source and target currently live in the same universe. |
| Rounded-ideal formal-ball completion | cited GLN Section 7 | `FormalBallRoundedIdeal.lean`, `FormalBallHausdorff.lean`, `FormalBallCompletion.lean`, `FormalBallNormalization.lean`, `FormalBallCompletionIso.lean` | P3 | Rounded ideals, aperture normalization, Hausdorff quasi-metric, and the order isomorphism `σ : B(S(X,d)) ≃o RI(B(X,d),≺)` are constructed directly. |
| Completion is algebraic and Yoneda-complete | cited GLN Section 7 | `RoundedIdealDomain.lean`, `CompletionCenterPoints.lean` | P3 | Directed ideal unions, formal-ball dcpo structure, standardness, Yoneda completeness, formal-ball continuity, enough center points, and algebraicity are proved. |
| Way-below section and `d-lim` projection, GLN Lemmas 7.2–7.7 / Proposition 7.8 | cited in F5 | `FormalBallFunctor.lean`, `FormalBallWayBelow.lean`, `CompletionRetract.lean` | P3 | Way-below interpolation, `≪ ⇒ ≺`, shift invariance, `q ↦ ↓↓q`, ideal suprema, the two Scott-continuous formal-ball maps, nonexpansiveness, Yoneda continuity, `d`-Scott continuity, and the left-inverse equation are proved. |
| Main theorem, `thm:main` | lines 255–258 and 699–703 | `QuasiMetric.IsContinuous.propertyD`, `continuous_yonedaComplete_propertyD` in `MainTheorem.lean` | P3 | Exact source-facing implication: continuous plus Yoneda-complete implies property D. |
| Functional corollary, `cor:functional` | lines 705–714 | `QuasiMetric.IsContinuous.continuous_iff_integerLayerwise` | P3 | Stated for the cofinal integer layers used by the Lean layer system; `propertyD_iff_all_positive_layers` supplies the equivalence with all positive finite constants. |
| Metric characterization, `thm:metric-iff` | lines 263–266 and 716–798 | — | P1 | The ordinary-metric bridge, agreement of metric and Yoneda completeness, and the incomplete-space boundary functional are not formalized here. |
| Extension formula and recovery, `lem:extension-formula` | lines 831–913 | `CompletionFormula.correctedSupremum`, `strictSuperlevel_correctedSupremum`; way-below section in `CompletionRetract.lean` | P2/P1 | The strict-superlevel formula and the recovery section are present, but their identification with the manuscript's simultaneous extension operator is not yet packaged. |
| Layerwise extension and completion visibility | lines 924–1050 | `CompletionFormula.isOpen_strictSuperlevel_correctedSupremum`, `LayerSystem.propertyD_iff_continuous_extension` | P3/P1 | The abstract topological equivalence is P3 from explicit extension/recovery data. Its source-specific simultaneous-extension instance and compact-set visibility corollaries remain P1. |
| Yoneda completeness is not necessary, `prop:not-necessary` | lines 1057–1095 | `OrderExample.lean` | P3 | The natural-number order quasi-metric is Cauchy but not Yoneda-complete; all positive layers coincide and property D follows. |

## Main proof route represented in Lean

1. `AlgebraicTheorem.lean` proves property D for algebraic
   Yoneda-complete spaces using the completed cone-forest construction.
2. `FormalBallCompletionIso.lean`, `RoundedIdealDomain.lean`, and
   `CompletionCenterPoints.lean` prove that the formal-ball completion is
   algebraic and Yoneda-complete.
3. `FormalBallWayBelow.lean` and `CompletionRetract.lean` construct the
   section `x ↦ ↓↓(x,0)` and the ideal-supremum projection and prove that
   they form a nonexpansive Yoneda- and `d`-Scott-continuous retract.
4. `LowerMapSuprema.lean` transfers property D along that retract.
5. `MainTheorem.lean` composes the preceding theorems to obtain the headline
   result.

## Module map

- Foundational topology and quasi-metrics: `LayeredTopology.lean`,
  `QuasiMetric.lean`, `DomainStructure.lean`, `Retract.lean`,
  `LowerMapSuprema.lean`.
- Algebraic cone-forest proof: `Cones.lean`, `CenterPoints.lean`,
  `Interpolation.lean`, `Forest.lean`, `ConeForest.lean`,
  `FormalBallChains.lean`, `PathEndpoint.lean`, `AlgebraicCore.lean`,
  `ConeApproximation.lean`, `ConeForestConstruction.lean`,
  `SharpContinuity.lean`, `SharpConverse.lean`, `ConeContinuity.lean`,
  `StandardConeFacts.lean`, `StandardConsequences.lean`,
  `CauchyWeightedSubnet.lean`, `AlgebraicTheorem.lean`.
- Rounded-ideal completion and retract: `FormalBallRoundedIdeal.lean`,
  `FormalBallHausdorff.lean`, `FormalBallCompletion.lean`,
  `FormalBallNormalization.lean`, `FormalBallCompletionIso.lean`,
  `RoundedIdealDomain.lean`, `CompletionCenterPoints.lean`,
  `FormalBallFunctor.lean`, `FormalBallWayBelow.lean`,
  `CompletionRetract.lean`.
- Headline theorem and audits: `MainTheorem.lean`, `AxiomAudit.lean`,
  `Upperness.lean`, `OrderExample.lean`, `CompletionVisibility.lean`, and
  the facade `../LipschitzYonedaFinalTopology.lean`.

## Verification

From the package root, run:

```sh
lake exe cache get
lake build
lake env lean --trust=0 StandaloneAxiomAudit.lean
```

The standalone audit checks every declaration owned by a paper module and permits only `propext`, `Classical.choice`, and `Quot.sound`. Compilation and the axiom audit do not replace source-fidelity assessment or human expert review.
