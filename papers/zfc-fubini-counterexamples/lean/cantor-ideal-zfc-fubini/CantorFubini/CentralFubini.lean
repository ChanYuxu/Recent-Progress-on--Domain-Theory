import CantorFubini.CentralLimits
import CantorFubini.ValuationIntegralLinearity

/-! New compact zero-dimensional parameter Fubini theorem. The proof first
computes both integrals on genuine finite clopen fibers, then passes to the
proved arbitrary directed supremum of all such approximants. -/

set_option autoImplicit false
open Set Topology TopologicalSpace MeasureTheory
open scoped BigOperators ENNReal
universe u v w
namespace CantorFubini

theorem vIntegral_finset_sum_of_mem {Y : Type v} [TopologicalSpace Y] {ι : Type w}
    (ρ : Valuation Y) (S : Finset ι) (f : ι → Y → ℝ≥0∞)
    (hf : ∀ i ∈ S, IsVLSC (f i)) :
    vIntegral ρ (fun y => ∑ i ∈ S, f i y) = ∑ i ∈ S, vIntegral ρ (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    simp only [Finset.sum_insert hi]
    rw [vIntegral_add ρ (hf i (Finset.mem_insert_self i S))
      (isVLSC_finset_sum_of_mem S f (fun j hj => hf j (Finset.mem_insert_of_mem hj)))]
    rw [ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))]

namespace ClopenStep
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
variable [CompactSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
variable {k : X → Y → ℝ≥0∞}

/-- The actual valuation and measure iterated integrals commute for each
finite clopen approximant, by the disjoint-fiber formula and proved
valuation-integral finite linearity. -/
theorem fubini (s : ClopenStep k) (μ : Measure X) [Measure.InnerRegular μ] [SFinite μ]
    (ρ : Valuation Y) :
    vIntegral ρ (fun y => vIntegral (radonValuation μ) (fun x => s.val x y)) =
      vIntegral (radonValuation μ) (fun x => vIntegral ρ (s.val x)) := by
  classical
  have he : (fun y => vIntegral (radonValuation μ) (fun x => s.val x y)) =
      fun y => ∑ v ∈ s.rangeFinset, μ (s.fiber v : Set X) * v y := by
    funext y
    rw [vIntegral_radonValuation μ _ (s.parameter_isVLSC y),
      s.lintegral_parameter_eq_sum μ y]
  rw [he, vIntegral_finset_sum_of_mem]
  · calc
      (∑ v ∈ s.rangeFinset, vIntegral ρ (fun y => μ (s.fiber v : Set X) * v y)) =
          ∑ v ∈ s.rangeFinset, μ (s.fiber v : Set X) * vIntegral ρ v := by
        apply Finset.sum_congr rfl
        intro v hv
        exact vIntegral_const_mul ρ _ (s.section_isVLSC_of_mem hv)
      _ = ∫⁻ x, vIntegral ρ (s.val x) ∂μ :=
        (s.lintegral_comp_eq_sum μ (vIntegral ρ)).symm
      _ = vIntegral (radonValuation μ) (fun x => vIntegral ρ (s.val x)) :=
        (vIntegral_radonValuation μ _ (s.integral_section_isVLSC ρ)).symm
  · intro v hv
    exact (s.section_isVLSC_of_mem hv).const_mul _

end ClopenStep

section CompactFubini
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
variable [CompactSpace X] [T2Space X] [TotallyDisconnectedSpace X]
variable [MeasurableSpace X] [OpensMeasurableSpace X]

/-- Fubini for an actual Radon measure on a compact Hausdorff totally
disconnected parameter space and an arbitrary continuous valuation on any
partner space. The integrand is LSC for their ordinary product topology. -/
theorem compact_parameter_fubini (μ : Measure X) [Measure.InnerRegular μ] [SFinite μ]
    (ρ : Valuation Y) (k : X → Y → ℝ≥0∞)
    (hk : IsVLSC (fun z : X × Y => k z.1 z.2)) :
    vIntegral ρ (fun y => vIntegral (radonValuation μ) (fun x => k x y)) =
      vIntegral (radonValuation μ) (fun x => vIntegral ρ (k x)) := by
  have hp : (fun y => vIntegral (radonValuation μ) (fun x => k x y)) =
      fun y => ⨆ s : ClopenStep k, vIntegral (radonValuation μ) (fun x => s.val x y) :=
    funext (parameter_integral_eq_iSup k hk (radonValuation μ))
  have hq : (fun x => vIntegral ρ (k x)) =
      fun x => ⨆ s : ClopenStep k, vIntegral ρ (s.val x) :=
    funext (partner_integral_eq_iSup k hk ρ)
  have hpd : Directed (· ≤ ·) (fun s : ClopenStep k =>
      fun y => vIntegral (radonValuation μ) (fun x => s.val x y)) := by
    intro s t
    obtain ⟨r, hsr, htr⟩ := ClopenStep.directed (k := k) s t
    exact ⟨r, (fun y => vIntegral_mono _ (fun x => hsr x y)),
      (fun y => vIntegral_mono _ (fun x => htr x y))⟩
  have hqd : Directed (· ≤ ·) (fun s : ClopenStep k =>
      fun x => vIntegral ρ (s.val x)) := by
    intro s t
    obtain ⟨r, hsr, htr⟩ := ClopenStep.directed (k := k) s t
    exact ⟨r, (fun x => vIntegral_mono ρ (hsr x)),
      (fun x => vIntegral_mono ρ (htr x))⟩
  rw [hp, hq, vIntegral_iSup_directed ρ _
    (fun s => s.parameter_integral_isVLSC μ) hpd,
    vIntegral_iSup_directed (radonValuation μ) _
      (fun s => s.integral_section_isVLSC ρ) hqd]
  exact iSup_congr (fun s => s.fubini μ ρ)

end CompactFubini
end CantorFubini
