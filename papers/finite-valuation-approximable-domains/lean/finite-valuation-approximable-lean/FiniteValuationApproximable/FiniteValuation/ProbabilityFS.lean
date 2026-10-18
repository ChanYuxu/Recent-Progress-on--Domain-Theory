import FiniteValuationApproximable.FiniteValuation.Probability
import FiniteValuationApproximable.Abstract.CountableBasis

/-!
# FS classification for normalized finite probabilities

This module bridges the exact order isomorphism and negative separator theorem
from `Probability.lean` to the abstract FS/FVA interfaces.  It formalizes the
remaining order-theoretic logic of source items `prop:probability-positive`,
`prop:probability-negative`, and `cor:probability-characterization` (source
lines 1078--1151 of `main17-4b2e65f0f963`).

Two semantic inputs are kept explicit rather than postulated:

* `FiniteStagesHaveFSApproximateIdentities` is discharged by the full erosion
  theorem for finite subprobability stages;
* `FiniteStagesAreContinuousDcpos` is the standard valuation-domain result
  needed to upgrade the transported FS approximation to a countably based
  continuous dcpo.

Thus the FS-approximate-identity characterization below is exact conditional
on the first input, while the domain/countable-basis conclusion is exact
conditional on both.
-/

set_option autoImplicit false
set_option linter.unnecessarySimpa false

universe u v

namespace FiniteValuationApproximable

open scoped Classical
open AbstractApproximation
open AbramskyJung.Chapter2
open SubprobabilityVector

section OrderIsomorphisms

variable {D : Type u} {E : Type v} [Preorder D] [Preorder E]

/-- Every order isomorphism preserves arbitrary existing directed suprema. -/
theorem orderIso_scottContinuous (e : D ≃o E) :
    AbramskyJung.Chapter2.ScottContinuous e := by
  constructor
  · exact e.monotone
  · intro A x hA hx
    constructor
    · intro y hy
      rcases hy with ⟨a, ha, rfl⟩
      exact e.monotone (hx.1 ha)
    · intro y hy
      have hUpper : IsUpperBound A (e.symm y) := by
        intro a ha
        apply e.le_iff_le.mp
        simpa using hy ⟨a, ha, rfl⟩
      have hxy : x ≤ e.symm y := hx.2 (e.symm y) hUpper
      simpa using e.monotone hxy

/-- An order isomorphism, oriented from source to target, is a continuous
section--retraction pair. -/
def orderIsoContinuousSectionRetractionPair (e : D ≃o E) :
    AbramskyJung.Chapter3.ContinuousSectionRetractionPair D E where
  s := e
  r := e.symm
  monotone_s := e.monotone
  monotone_r := e.symm.monotone
  retract := e.symm_apply_apply
  continuous_s := orderIso_scottContinuous e
  continuous_r := orderIso_scottContinuous e.symm

end OrderIsomorphisms

/-- The separate standard domain-theoretic input for finite
subprobability-valuation stages. -/
def FiniteStagesAreContinuousDcpos : Prop :=
  ∀ P : FinitePoset.{u},
    AbramskyJung.Chapter2.IsContinuousDcpo P.VSub

/-- The generator half of source item `lem:generators`: the standalone finite
valuation-domain input upgrades every concrete finite stage to FVA via the
constant identity factorization. -/
theorem finiteStages_areFVA
    (hDomains : FiniteStagesAreContinuousDcpos.{u})
    (P : FinitePoset.{u}) : IsFVA.{u, u} P.VSub :=
  finiteStage_isFVA P (hDomains P)

section ProbabilityFS

variable {Q : Type u} [Fintype Q] [PartialOrder Q]

/-- Pin the canonical subtype `Fintype` instance used by
`probabilityOrderIso`; this avoids ambiguity with unrelated bundled-category
instances that are also visible in the transitive imports. -/
abbrev DeletedSubprobability (bot : Q) :=
  @SubprobabilityVector (WithoutPoint bot)
    (Subtype.fintype fun x : Q => x ≠ bot)

/-- Transport an FS approximate identity along the exact least-point deletion
order isomorphism from `Probability.lean`. -/
noncomputable def probabilityFSApproximateIdentity
    (bot : Q) (hbot : ∀ x : Q, bot ≤ x)
    (A : FSApproximateIdentity (DeletedSubprobability bot)) :
    FSApproximateIdentity (ProbabilityVector Q) :=
  A.pullback
    (orderIsoContinuousSectionRetractionPair
      (probabilityOrderIso bot hbot))

/-- Positive half of the source classification at the FS-approximation layer. -/
theorem probability_hasFSApproximateIdentity_of_least
    (hStages : FiniteStagesHaveFSApproximateIdentities.{u})
    (bot : Q) (hbot : ∀ x : Q, bot ≤ x) :
    Nonempty (FSApproximateIdentity (ProbabilityVector Q)) := by
  let P : FinitePoset.{u} := {
    carrier := WithoutPoint bot
    fintype := Subtype.fintype fun x : Q => x ≠ bot
    partialOrder := inferInstance
  }
  rcases hStages P with ⟨A⟩
  exact ⟨probabilityFSApproximateIdentity bot hbot A⟩

/-- The exact negative half: without a least point, no sequential FS
approximate identity can exist, since even one of its maps would have a finite
separator. -/
theorem probability_noFSApproximateIdentity_of_no_least
    [Nonempty Q] (hno : ¬ HasLeastElement Q) :
    ¬ Nonempty (FSApproximateIdentity (ProbabilityVector Q)) := by
  rintro ⟨A⟩
  apply no_finiteSeparator_of_no_least hno (A.map 0)
  exact A.finitelySeparated 0

/-- Source item `cor:probability-characterization`, exactly at the FS
approximate-identity layer and conditional only on the finite-stage erosion
theorem. -/
theorem probability_hasFSApproximateIdentity_iff_least
    [Nonempty Q]
    (hStages : FiniteStagesHaveFSApproximateIdentities.{u}) :
    Nonempty (FSApproximateIdentity (ProbabilityVector Q)) ↔
      HasLeastElement Q := by
  constructor
  · intro hA
    by_contra hno
    exact probability_noFSApproximateIdentity_of_no_least hno hA
  · rintro ⟨bot, hbot⟩
    exact probability_hasFSApproximateIdentity_of_least hStages bot hbot

/-- The least-point deletion isomorphism also transports the continuous-dcpo
structure of the subprobability stage. -/
theorem probability_isContinuousDcpo_of_least
    (hDomains : FiniteStagesAreContinuousDcpos.{u})
    (bot : Q) (hbot : ∀ x : Q, bot ≤ x) :
    AbramskyJung.Chapter2.IsContinuousDcpo (ProbabilityVector Q) := by
  let P : FinitePoset.{u} := {
    carrier := WithoutPoint bot
    fintype := Subtype.fintype fun x : Q => x ≠ bot
    partialOrder := inferInstance
  }
  let sr := orderIsoContinuousSectionRetractionPair
    (probabilityOrderIso bot hbot)
  exact AbramskyJung.Chapter3.theorem_3_1_4_retract_continuous_domain
    sr (hDomains P)

/-- Full positive conclusion represented in the local APIs: normalized
probabilities over a finite poset with a least point form an omega-continuous
dcpo and carry a sequential FS approximate identity. -/
theorem probability_positive_conditional
    (hStages : FiniteStagesHaveFSApproximateIdentities.{u})
    (hDomains : FiniteStagesAreContinuousDcpos.{u})
    (bot : Q) (hbot : ∀ x : Q, bot ≤ x) :
    AbramskyJung.Chapter2.IsOmegaContinuousDcpo (ProbabilityVector Q) ∧
      Nonempty (FSApproximateIdentity (ProbabilityVector Q)) := by
  rcases probability_hasFSApproximateIdentity_of_least
      hStages bot hbot with ⟨A⟩
  have hcont := probability_isContinuousDcpo_of_least
    hDomains bot hbot
  exact ⟨⟨hcont.1,
      FiniteValuationApproximable.FSApproximateIdentity.isOmegaContinuousDomain
        A hcont.hasBasis⟩,
    ⟨A⟩⟩

end ProbabilityFS

end FiniteValuationApproximable
