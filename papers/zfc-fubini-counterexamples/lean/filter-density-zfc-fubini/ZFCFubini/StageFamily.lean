import ZFCFubini.SourceValuation
import ZFCFubini.SubprobIntegralBridge

/-!
Literal decreasing source family and its pointwise infimum, also in the
manuscript's real-mass encoding. Stabilization attains the infimum separately
for EACH Scott-open observation; no single index is claimed to attain the
whole valuation. Positive centrality of the stages is proved elsewhere.
-/

set_option autoImplicit false
open Set Topology TopologicalSpace MeasureTheory
open scoped ENNReal

namespace ZFCFubini

noncomputable def sourceStageProbability (M : NullSet) :
    ProbabilityValuation (WithScott SourceQ) :=
  ⟨sourceStageEta M, sourceStageEta_probability M⟩

theorem sourceStageEta_mass_antitone (A : ScottOpens SourceQ) :
    Antitone (fun M => sourceStageEta M A) := by
  intro M N hMN
  change sourceStageEta N A ≤ sourceStageEta M A
  rw [sourceStageEta_apply, sourceStageEta_apply]
  apply measure_mono
  intro t ht
  exact (Topology.IsScott.isUpperSet_of_isOpen (D := Set.univ) A.isOpen)
    (sourceG_antitone t hMN) ht

theorem sourceStageEta_mass_attained (A : ScottOpens SourceQ) :
    ∃ M0 : NullSet, sourceStageEta M0 A = sourceEtaValuation A := by
  obtain ⟨M0, hM0⟩ := sourcePsi_stabilization A
  exact ⟨M0, congrArg parameterMeasure (hM0 M0 le_rfl)⟩

theorem sourceEta_le_stage_realMass (M : NullSet) (A : ScottOpens SourceQ) :
    realMass sourceEtaProbability A ≤ realMass (sourceStageProbability M) A :=
  ENNReal.toReal_mono (probability_mass_ne_top (sourceStageProbability M) A)
    (sourceEta_le_stage M A)

theorem sourceStage_realMass_attained (A : ScottOpens SourceQ) :
    ∃ M0 : NullSet,
      realMass sourceEtaProbability A = realMass (sourceStageProbability M0) A := by
  obtain ⟨M0, hM0⟩ := sourceStageEta_mass_attained A
  exact ⟨M0, (congrArg ENNReal.toReal hM0).symm⟩

theorem sourceEta_realMass_isGLB (A : ScottOpens SourceQ) :
    IsGLB (Set.range (fun M => realMass (sourceStageProbability M) A))
      (realMass sourceEtaProbability A) := by
  constructor
  · rintro b ⟨M, rfl⟩
    exact sourceEta_le_stage_realMass M A
  · intro b hb
    obtain ⟨M0, hM0⟩ := sourceStage_realMass_attained A
    rw [hM0]
    exact hb (Set.mem_range_self M0)

theorem sourceEta_real_iInf_stage (A : ScottOpens SourceQ) :
    realMass sourceEtaProbability A = ⨅ M : NullSet, realMass (sourceStageProbability M) A :=
  (sourceEta_realMass_isGLB A).ciInf_eq.symm

end ZFCFubini
