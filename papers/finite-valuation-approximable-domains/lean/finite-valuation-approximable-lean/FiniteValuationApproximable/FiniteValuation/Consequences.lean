import FiniteValuationApproximable.FiniteValuation.StageFS
import FiniteValuationApproximable.FiniteValuation.ProbabilityFS

/-!
# Unconditional consequences of the finite-stage erosion theorem

The earlier abstract and probability modules deliberately exposed the two
finite-stage inputs.  `DirectedSup` and `StageFS` prove both inputs, so this
module records the corresponding premise-free source-facing theorems.
-/

set_option autoImplicit false

universe u w

namespace FiniteValuationApproximable

open AbstractApproximation
open SubprobabilityVector

/-- Every concrete finite subprobability stage is a continuous dcpo. -/
theorem finiteStagesAreContinuousDcpos :
    FiniteStagesAreContinuousDcpos.{u} := by
  intro P
  exact Erosion.finiteSubprobability_isContinuousDcpo (P := P)

/-- Every concrete finite stage is FVA, now without a caller-supplied domain
premise. -/
theorem finiteStage_isFVA_unconditional (P : FinitePoset.{u}) :
    IsFVA.{u, u} P.VSub :=
  finiteStages_areFVA finiteStagesAreContinuousDcpos P

/-- Unconditional countable-basis consequence for every FVA dcpo. -/
theorem IsFVA.isOmegaContinuousDcpo_unconditional
    {D : Type u} [PartialOrder D] (hD : IsFVA.{u, w} D) :
    AbramskyJung.Chapter2.IsOmegaContinuousDcpo D :=
  hD.isOmegaContinuousDcpo finiteStagesHaveFSApproximateIdentities

section Probability

variable {Q : Type u} [Fintype Q] [PartialOrder Q]

/-- Premise-free positive FS construction for a finite poset with a least
element. -/
theorem probability_hasFSApproximateIdentity_of_least_unconditional
    (bot : Q) (hbot : ∀ x : Q, bot ≤ x) :
    Nonempty (FSApproximateIdentity (ProbabilityVector Q)) :=
  probability_hasFSApproximateIdentity_of_least
    finiteStagesHaveFSApproximateIdentities bot hbot

/-- Premise-free FS characterization of normalized probabilities. -/
theorem probability_hasFSApproximateIdentity_iff_least_unconditional
    [Nonempty Q] :
    Nonempty (FSApproximateIdentity (ProbabilityVector Q)) ↔
      HasLeastElement Q :=
  probability_hasFSApproximateIdentity_iff_least
    finiteStagesHaveFSApproximateIdentities

/-- Premise-free continuous-dcpo result for normalized probabilities over a
finite poset with a least point. -/
theorem probability_isContinuousDcpo_of_least_unconditional
    (bot : Q) (hbot : ∀ x : Q, bot ≤ x) :
    AbramskyJung.Chapter2.IsContinuousDcpo (ProbabilityVector Q) :=
  probability_isContinuousDcpo_of_least
    finiteStagesAreContinuousDcpos bot hbot

/-- Full premise-free positive conclusion: normalized probabilities over a
finite poset with a least point form an omega-continuous dcpo and carry an FS
approximate identity. -/
theorem probability_positive
    (bot : Q) (hbot : ∀ x : Q, bot ≤ x) :
    AbramskyJung.Chapter2.IsOmegaContinuousDcpo (ProbabilityVector Q) ∧
      Nonempty (FSApproximateIdentity (ProbabilityVector Q)) :=
  probability_positive_conditional finiteStagesHaveFSApproximateIdentities
    finiteStagesAreContinuousDcpos bot hbot

end Probability

end FiniteValuationApproximable
