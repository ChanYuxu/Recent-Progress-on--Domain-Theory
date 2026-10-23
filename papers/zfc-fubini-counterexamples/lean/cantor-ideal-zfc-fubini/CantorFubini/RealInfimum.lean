import CantorFubini.SecondValuation
import CantorFubini.PaperIntegral
import CantorFubini.SourceModel

/-! Ordinary-real bridges for the first valuation formula and the
decreasing-infimum assertions of source Remark 6.5. The companion module
`CentralPushforward` proves centrality of every actual stage, completing
the mathematical assertions of that remark. -/

set_option autoImplicit false
open Set Topology TopologicalSpace MeasureTheory
namespace CantorFubini

theorem eta_real_infimum (A₀ : ScottOpens (ScottOpens (IdealPoint cantorMeasure))) :
    (eta A₀).toReal = ⨅ M : NullIndex cantorMeasure, (etaStage M A₀).toReal := by
  rw [eta_eq_iInf_etaStage]
  exact ENNReal.toReal_iInf (fun M =>
    probability_mass_ne_top ⟨etaStage M, etaStage_probability M⟩ A₀)

/-- The printed ordinary-real decreasing-infimum assertions in Remark 6.5;
the stage-centrality assertion is proved in `CentralPushforward`. -/
theorem source_decreasing_real_infimum :
    (∀ M : NullIndex cantorMeasure, (etaStage M).Probability) ∧
    (∀ M N : NullIndex cantorMeasure, M ≤ N →
      ∀ A₀ : ScottOpens (ScottOpens (IdealPoint cantorMeasure)),
        (etaStage N A₀).toReal ≤ (etaStage M A₀).toReal) ∧
    (∀ A₀ : ScottOpens (ScottOpens (IdealPoint cantorMeasure)),
      (eta A₀).toReal = ⨅ M : NullIndex cantorMeasure, (etaStage M A₀).toReal) := by
  refine ⟨etaStage_probability, ?_, eta_real_infimum⟩
  intro M N hMN A₀
  apply ENNReal.toReal_mono
    (probability_mass_ne_top ⟨etaStage M, etaStage_probability M⟩ A₀)
  apply measure_mono
  exact stageEvent_antitone (G cantorMeasure randomOpen)
    (G_antitone cantorMeasure randomOpen) A₀ hMN

/-- The source first-valuation formula with ordinary real [0,1] mass and
the completed fair-coin measure on the exact maximal trace. -/
theorem source_nu_real (H : ScottOpens (IdealPoint cantorMeasure)) :
    realMass ⟨nu cantorMeasure, nu_probability cantorMeasure⟩ H =
      (cantorMeasure.completion (trace H : Set Cantor)).toReal := by
  rw [realMass, nu_apply, completed_cantor_mass]

end CantorFubini
