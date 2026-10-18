import CoreCompactNonSober.DefinitionChecks
import Mathlib.Topology.Sets.Closeds

/-!
Source-facing definitions for the 2026-10-15 simplified manuscript.
The imported order/topological definitions and their elementary bridges are
reviewed reuse; no legacy counterexample theorem is imported here.
-/

set_option autoImplicit false

universe u

namespace CoreCompactSimplified

open Set TopologicalSpace CoreCompactNonSober

/-- Condition (i) of Theorem `thm:transfer`, for all ambient points. -/
def LowerNeighborhoodApproximation {L : Type u} [PartialOrder L] (D : Set L) : Prop :=
  ∀ (p : L) (V : ScottOpens L), p ∈ V →
    ∃ d : D, (d : L) ∈ V ∧ (d : L) ≤ p

/-- Condition (ii), with arbitrary nonempty directed ambient sets and their
actual least upper bounds. No sequence reduction or lattice assumption. -/
def CommonLowerWitness {L : Type u} [PartialOrder L] (D : Set L) : Prop :=
  ∀ (U : ScottOpens D) (q : D), q ∈ U →
    ∀ (E : Set L), NonemptyDirected E →
    ∀ (s : L), IsLUB E s → (q : L) ≤ s →
      ∃ (r : D), r ∈ U ∧ r ≤ q ∧ ∃ e ∈ E, (r : L) ≤ e

abbrev ScottCloseds (L : Type u) [PartialOrder L] :=
  @TopologicalSpace.Closeds L (scottTopology L)

/-- Literal closed-set restriction, not an unspecified isomorphism. -/
def ClosedRestrictionIsomorphism {L : Type u} [PartialOrder L] (D : Set L) : Prop :=
  ∃ e : ScottCloseds L ≃o ScottCloseds D,
    ∀ (C : ScottCloseds L) (d : D), d ∈ e C ↔ (d : L) ∈ C

/-- All assertions in the generic transfer theorem, including the inverse of
the specified restriction map. Extra dcpo/no-greatest fields expose facts
proved in the printed proof, not assumptions on the subset. -/
structure TransferConclusion {L : Type u} [PartialOrder L] (D : Set L) : Prop where
  dcpo : IsDcpo D
  restriction : RestrictionFrameIsomorphism D
  upward_open : ∀ U : ScottOpens D,
    @IsOpen L (scottTopology L) (upperHull (Subtype.val '' (U : Set D)))
  upward_trace : ∀ (U : ScottOpens D) (d : D),
    (d : L) ∈ upperHull (Subtype.val '' (U : Set D)) ↔ d ∈ U
  trace_upward : ∀ V : ScottOpens L,
    upperHull (Subtype.val '' (Subtype.val ⁻¹' (V : Set L) : Set D)) = (V : Set L)
  meetContinuous : MeetContinuous D
  compact : ScottCompact D
  secondCountable : ScottSecondCountable D
  coreCompact : ScottCoreCompact D
  not_sober : ¬ ScottSober D
  noGreatest : NoGreatestElement D
  closed_restriction : ClosedRestrictionIsomorphism D
  not_orderIso : ¬ Nonempty (L ≃o D)

/-- The source's full main-theorem conclusion. No cardinality conclusion or
extra assumption from an earlier manuscript is included. -/
structure MainConclusion {L : Type u} [CompleteLattice L] (D : Set L) : Prop where
  proper : D ⊂ Set.univ
  subdcpo : IsSubDcpo D
  dcpo : IsDcpo D
  ambient_compact : ScottCompact L
  ambient_secondCountable : ScottSecondCountable L
  ambient_locallyCompact : ScottLocallyCompact L
  ambient_coreCompact : ScottCoreCompact L
  ambient_sober : ScottSober L
  retained_meetContinuous : MeetContinuous D
  retained_compact : ScottCompact D
  retained_secondCountable : ScottSecondCountable D
  retained_coreCompact : ScottCoreCompact D
  retained_not_sober : ¬ ScottSober D
  retained_not_locallyCompact : ¬ ScottLocallyCompact D
  restriction : RestrictionFrameIsomorphism D
  closed_restriction : ClosedRestrictionIsomorphism D
  not_orderIso : ¬ Nonempty (L ≃o D)

def MainStatement : Prop :=
  ∃ (L : Type) (lattice : CompleteLattice L),
    letI := lattice
    ∃ D : Set L, MainConclusion D

end CoreCompactSimplified
