import ZFCFubini.StageCentrality
import ZFCFubini.StageFamily
import ZFCFubini.Noncentral
import ZFCFubini.SubprobIntegralContinuity
import ZFCFubini.SubprobRealValuation

/-!
The complete source rem:decreasing-family. In particular, the exclusion of a
single stage uses the printed central-stage/noncentral-limit argument. The
separate diagnostic point evaluations in SourceStageDiagnostics are not used
to replace this argument. Each real observation's infimum is also explicit.
-/

set_option autoImplicit false
open Set Topology TopologicalSpace MeasureTheory
open scoped ENNReal
universe v

namespace ZFCFubini

/-- Same proof route as the manuscript: every stage is central, eta is not. -/
theorem sourceEta_ne_stage_of_centrality (M : NullSet) :
    sourceEtaValuation ≠ sourceStageEta M := by
  intro he
  apply sourceEta_not_central
  rw [he]
  exact sourceStageEta_central M

/-- Positive stage centrality in the manuscript's literal real integral,
against an arbitrary real-encoded continuous subprobability partner. The
general real/ENN valuation equivalence covers all such source partners. -/
theorem sourceStageEta_real_commute
    (M : NullSet) (Q : Type v) [PartialOrder Q] (hQ : IsDcpo Q)
    (ν : SubprobValuation (WithScott Q)) (f : SourceQ × Q → UnitInterval)
    (hf : ScottContinuous f) :
    paperIntegral (sourceStageProbability M) (fun H => subprobPaperIntegral ν
        (fun y => (f (WithScott.ofScott H, WithScott.ofScott y)).val)) =
      subprobPaperIntegral ν (fun y => paperIntegral (sourceStageProbability M)
        (fun H => (f (WithScott.ofScott H, WithScott.ofScott y)).val)) := by
  have h := Central.subprobPaperIntegral_unit
    ⟨(sourceStageProbability M).val, (sourceStageProbability M).property.subprobability⟩
    (sourceStageEta_central M) Q hQ ν f hf
  simpa only [subprobPaperIntegral_probability] using h

/-- The same equation for literally real-valued source partner data, through
the proved bijection and literal integral-definition bridge. -/
theorem sourceStageEta_real_partner_commute
    (M : NullSet) (Q : Type v) [PartialOrder Q] (hQ : IsDcpo Q)
    (ν : RealSubprobValuation (WithScott Q)) (f : SourceQ × Q → UnitInterval)
    (hf : ScottContinuous f) :
    paperIntegral (sourceStageProbability M) (fun H => ν.integral
        (fun y => (f (WithScott.ofScott H, WithScott.ofScott y)).val)) =
      ν.integral (fun y => paperIntegral (sourceStageProbability M)
        (fun H => (f (WithScott.ofScott H, WithScott.ofScott y)).val)) := by
  simp only [RealSubprobValuation.integral_eq_subprobPaperIntegral]
  exact sourceStageEta_real_commute M Q hQ ν.toENN f hf

namespace Paper

/-- Every clause of the final numbered remark, for the actual source family.
The stage-centrality component is polymorphic in the partner universe. -/
theorem decreasing_family :
    IsCompact (Set.univ : Set Omega) ∧ T2Space Omega ∧
    (∀ M : NullSet, Continuous (sourceFamily M) ∧
      (sourceStageEta M).Probability ∧ Central.{0, v} (sourceStageEta M)) ∧
    (∀ A : ScottOpens SourceQ,
      Antitone (fun M => sourceStageEta M A) ∧
      realMass sourceEtaProbability A = ⨅ M : NullSet, realMass (sourceStageProbability M) A) ∧
    (∀ A : ScottOpens SourceQ, sourceEtaValuation A = ⨅ M : NullSet, sourceStageEta M A) ∧
    sourceEtaValuation.Probability ∧ ¬ Central.{0, 0} sourceEtaValuation ∧
    (∀ M : NullSet, sourceEtaValuation ≠ sourceStageEta M) := by
  exact ⟨isCompact_univ, inferInstance,
    fun M => ⟨sourceFamily_continuous M, sourceStageEta_probability M, sourceStageEta_central M⟩,
    fun A => ⟨sourceStageEta_mass_antitone A, sourceEta_real_iInf_stage A⟩,
    sourceEta_iInf_stage, sourceEta_probability, sourceEta_not_central,
    sourceEta_ne_stage_of_centrality⟩

end Paper
end ZFCFubini
