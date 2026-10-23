import ZFCFubini.NullIndex
import ZFCFubini.FilterTraceSequence
import ZFCFubini.RandomOpen

/-! The actual density-circle/filter model and the specified source ν and G_M.
This is not a generic witness package assumed by the main theorem. -/

set_option autoImplicit false
open Set TopologicalSpace MeasureTheory Topology
open scoped ENNReal
namespace ZFCFubini

def circleModel : FilterDcpo.Model Circle where
  tau := densityTopology
  ordinary_le := fun _ hU => ordinary_isOpen_densityTopology hU

abbrev SourceP := FilterDcpo.Point circleModel
abbrev SourceQ := ScottOpens SourceP

theorem sourceP_isDcpo : IsDcpo SourceP := FilterDcpo.point_isDcpo circleModel

noncomputable def sourceNu : DValuation SourceP :=
  @Valuation.push Circle densityTopology (WithScott SourceP) inferInstance densityValuation
    (fun y => WithScott.toScott (FilterDcpo.e circleModel y))
    (FilterDcpo.e_continuous circleModel)

@[simp] theorem sourceNu_apply (H : SourceQ) :
    sourceNu H = volume (FilterDcpo.trace H) := rfl

theorem sourceNu_probability : sourceNu.Probability := by
  change densityValuation ⊤ = 1
  exact densityValuation_probability

noncomputable def sourceG (M : NullSet) (t : Omega) : SourceQ :=
  FilterDcpo.H_ordinary circleModel (randomOpen t) ⊔
    FilterDcpo.L circleModel (conullOpen M)

theorem sourceG_continuous (M : NullSet) :
    Continuous (fun t => WithScott.toScott (sourceG M t)) :=
  randomOpen_scott_sup_continuous (FilterDcpo.H_ordinary circleModel)
    (FilterDcpo.ordinaryH_scottContinuous circleModel) (FilterDcpo.L circleModel (conullOpen M))

theorem sourceG_antitone (t : Omega) : Antitone (fun M => sourceG M t) := by
  intro M N hMN
  exact sup_le_sup_left (FilterDcpo.L_mono circleModel
    (show conullOpen N ≤ conullOpen M from Set.compl_subset_compl.mpr hMN)) _

theorem trace_sup {X : Type*} [MetricSpace X] {M : FilterDcpo.Model X}
    (H Z : ScottOpens (FilterDcpo.Point M)) :
    FilterDcpo.trace (H ⊔ Z) = FilterDcpo.trace H ∪ FilterDcpo.trace Z := rfl

theorem trace_H_ordinary {X : Type*} [MetricSpace X] (M : FilterDcpo.Model X)
    (U : Opens X) : FilterDcpo.trace (FilterDcpo.H_ordinary M U) = U := by
  ext y
  change (@IsOpen X M.tau (U : Set X) ∧ y ∈ U) ↔ y ∈ U
  exact and_iff_right (M.ordinary_le _ U.isOpen)

theorem sourceG_trace (M : NullSet) (t : Omega) :
    FilterDcpo.trace (sourceG M t) = (randomOpen t : Set Circle) ∪ M.valᶜ := by
  rw [sourceG, trace_sup, trace_H_ordinary, FilterDcpo.trace_L]
  rfl

end ZFCFubini
