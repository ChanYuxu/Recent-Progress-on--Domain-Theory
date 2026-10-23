import CantorFubini.CentralFiniteRange
import CantorFubini.ValuationMeasureBridge

/-! New exact directed-limit and LSC properties of finite clopen parameter
approximations. Parameter integration is always against the actual Radon
measure; partner integration is against the supplied continuous valuation. -/

set_option autoImplicit false
open Set Topology TopologicalSpace MeasureTheory
open scoped BigOperators ENNReal
universe u v w
namespace CantorFubini

theorem isVLSC_finset_sum_of_mem {Y : Type v} [TopologicalSpace Y] {ι : Type w}
    (S : Finset ι) (f : ι → Y → ℝ≥0∞) (hf : ∀ i ∈ S, IsVLSC (f i)) :
    IsVLSC (fun y => ∑ i ∈ S, f i y) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using (isVLSC_const (X := Y) 0)
  | @insert i S hi ih =>
    simpa only [Finset.sum_insert hi] using
      (hf i (Finset.mem_insert_self i S)).add
        (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

namespace ClopenStep
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
variable [CompactSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
variable {k : X → Y → ℝ≥0∞}

theorem parameter_integral_isVLSC (s : ClopenStep k) (μ : Measure X)
    [Measure.InnerRegular μ] [SFinite μ] :
    IsVLSC (fun y => vIntegral (radonValuation μ) (fun x => s.val x y)) := by
  have he : (fun y => vIntegral (radonValuation μ) (fun x => s.val x y)) =
      fun y => ∑ v ∈ s.rangeFinset, μ (s.fiber v : Set X) * v y := by
    funext y
    rw [vIntegral_radonValuation μ _ (s.parameter_isVLSC y),
      s.lintegral_parameter_eq_sum μ y]
  rw [he]
  exact isVLSC_finset_sum_of_mem s.rangeFinset _
    (fun v hv => (s.section_isVLSC_of_mem hv).const_mul _)

end ClopenStep

section CompactLimits
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
variable [CompactSpace X] [T2Space X] [TotallyDisconnectedSpace X]
variable (k : X → Y → ℝ≥0∞) (hk : IsVLSC (fun z : X × Y => k z.1 z.2))
include hk

/-- Exact partner-section integration at the directed supremum. -/
theorem partner_integral_eq_iSup (ρ : Valuation Y) (x : X) :
    vIntegral ρ (k x) = ⨆ s : ClopenStep k, vIntegral ρ (s.val x) := by
  have he : k x = fun y => ⨆ s : ClopenStep k, s.val x y :=
    funext (fun y => (clopenStep_iSup k hk x y).symm)
  rw [he]
  apply vIntegral_iSup_directed ρ _ (fun s => s.lsc x)
  intro s t
  obtain ⟨r, hsr, htr⟩ := ClopenStep.directed (k := k) s t
  exact ⟨r, hsr x, htr x⟩

/-- The partner partial integral is an actual LSC function on the parameter. -/
theorem partner_integral_isVLSC (ρ : Valuation Y) :
    IsVLSC (fun x => vIntegral ρ (k x)) := by
  have he : (fun x => vIntegral ρ (k x)) =
      fun x => ⨆ s : ClopenStep k, vIntegral ρ (s.val x) :=
    funext (partner_integral_eq_iSup k hk ρ)
  rw [he]
  exact isVLSC_iSup _ (fun s => s.integral_section_isVLSC ρ)

/-- Exact parameter-section integration at the directed supremum. -/
theorem parameter_integral_eq_iSup (α : Valuation X) (y : Y) :
    vIntegral α (fun x => k x y) =
      ⨆ s : ClopenStep k, vIntegral α (fun x => s.val x y) := by
  have he : (fun x => k x y) = fun x => ⨆ s : ClopenStep k, s.val x y :=
    funext (fun x => (clopenStep_iSup k hk x y).symm)
  rw [he]
  apply vIntegral_iSup_directed α _ (fun s => s.parameter_isVLSC y)
  intro s t
  obtain ⟨r, hsr, htr⟩ := ClopenStep.directed (k := k) s t
  exact ⟨r, (fun x => hsr x y), (fun x => htr x y)⟩

variable [MeasurableSpace X] [OpensMeasurableSpace X]

/-- The actual Radon-parameter partial integral is LSC on the arbitrary
partner space, derived through finite clopen approximants. -/
theorem parameter_integral_isVLSC (μ : Measure X) [Measure.InnerRegular μ] [SFinite μ] :
    IsVLSC (fun y => vIntegral (radonValuation μ) (fun x => k x y)) := by
  have he : (fun y => vIntegral (radonValuation μ) (fun x => k x y)) =
      fun y => ⨆ s : ClopenStep k, vIntegral (radonValuation μ) (fun x => s.val x y) :=
    funext (parameter_integral_eq_iSup k hk (radonValuation μ))
  rw [he]
  exact isVLSC_iSup _ (fun s => s.parameter_integral_isVLSC μ)

end CompactLimits
end CantorFubini
