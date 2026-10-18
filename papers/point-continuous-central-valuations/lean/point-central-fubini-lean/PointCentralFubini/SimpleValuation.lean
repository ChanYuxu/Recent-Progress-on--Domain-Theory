import PointCentralFubini.MeasureIncidence
import PointCentralFubini.IntegrationExtra
import PointCentralFubini.ValuationLimits

/-! Finite sums of weighted Dirac valuations for Proposition 4.2. -/
set_option autoImplicit false
open Set Topology TopologicalSpace MeasureTheory
open scoped ENNReal BigOperators
universe u v
namespace PointCentralFubini
namespace Valuation
variable {X : Type u} [TopologicalSpace X] {I : Type v}

noncomputable def finsetSum (s : Finset I) (μ : I → Valuation X) : Valuation X where
  mass U := ∑ i ∈ s, μ i U
  strict := by simp only [strict,Finset.sum_const_zero]
  modular U V := by
    rw [← Finset.sum_add_distrib,← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => (μ i).modular U V)
  continuous := scottContinuous_finset_sum s (fun i => (μ i).mass) (fun i _ => (μ i).continuous)

@[simp] theorem finsetSum_apply (s : Finset I) (μ : I → Valuation X) (U : Opens X) :
    finsetSum s μ U = ∑ i ∈ s, μ i U := rfl

noncomputable def simple (s : Finset I) (w : I → ℝ≥0∞) (a : I → X) : Valuation X :=
  finsetSum s (fun i => (dirac (a i)).scale (w i))

@[simp] theorem simple_apply (s : Finset I) (w : I → ℝ≥0∞) (a : I → X) (U : Opens X) :
    simple s w a U = ∑ i ∈ s, w i * dirac (a i) U := rfl

theorem integral_simple_evaluation (η : DValuation (Opens X)) (s : Finset I)
    (w : I → ℝ≥0∞) (a : I → X) :
    integral η (fun U => simple s w a (WithScott.ofScott U)) =
      ∑ i ∈ s, w i * η (pointOpen (a i)) := by
  change integral η (fun U => ∑ i ∈ s, w i * dirac (a i) (WithScott.ofScott U)) = _
  refine (integral_finset_sum η s
    (fun i U => w i * dirac (a i) (WithScott.ofScott U))
    (fun i _ => scott_isLSC ((dirac (a i)).scale (w i)).continuous)).trans ?_
  apply Finset.sum_congr rfl
  intro i _
  rw [fpr_integral_smul η _ _ (scott_isLSC (dirac (a i)).continuous),
    integral_dirac_evaluation]

end Valuation
end PointCentralFubini
