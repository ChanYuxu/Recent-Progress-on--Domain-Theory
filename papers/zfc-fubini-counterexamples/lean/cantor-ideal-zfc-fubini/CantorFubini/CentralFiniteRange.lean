import CantorFubini.CentralApproximation
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-! New finite clopen fiber integration formulas. They concern the actual
parameter measure and do not presuppose any Fubini law for valuations. -/

set_option autoImplicit false
open Set Topology TopologicalSpace MeasureTheory
open scoped BigOperators ENNReal
universe u v
namespace CantorFubini
namespace ClopenStep
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
variable [CompactSpace X] {k : X → Y → ℝ≥0∞}

noncomputable def rangeFinset (s : ClopenStep k) : Finset (Y → ℝ≥0∞) :=
  s.range_finite.toFinset

@[simp] theorem mem_rangeFinset (s : ClopenStep k) (v : Y → ℝ≥0∞) :
    v ∈ s.rangeFinset ↔ v ∈ range s.val := s.range_finite.mem_toFinset

def fiber (s : ClopenStep k) (v : Y → ℝ≥0∞) : Opens X :=
  ⟨{x | s.val x = v}, s.locally_constant.isOpen_fiber v⟩

theorem fiber_isClopen (s : ClopenStep k) (v : Y → ℝ≥0∞) :
    IsClopen (s.fiber v : Set X) := s.locally_constant.isClopen_fiber v

theorem section_isVLSC_of_mem (s : ClopenStep k) {v : Y → ℝ≥0∞}
    (hv : v ∈ s.rangeFinset) : IsVLSC v := by
  obtain ⟨x, rfl⟩ := (s.mem_rangeFinset v).mp hv
  exact s.lsc x

/-- Every function of the finitely many locally constant section values is
the sum of its disjoint clopen fiber contributions. -/
theorem comp_eq_sum (s : ClopenStep k) (F : (Y → ℝ≥0∞) → ℝ≥0∞) (x : X) :
    F (s.val x) = ∑ v ∈ s.rangeFinset, (s.fiber v : Set X).indicator (fun _ => F v) x := by
  classical
  symm
  rw [Finset.sum_eq_single (s.val x)]
  · exact indicator_of_mem rfl _
  · intro v hv hvx
    exact indicator_of_notMem (show x ∉ (s.fiber v : Set X) from fun h => hvx h.symm) _
  · intro hx
    exact False.elim (hx ((s.mem_rangeFinset _).mpr (mem_range_self x)))

theorem comp_isLocallyConstant (s : ClopenStep k) (F : (Y → ℝ≥0∞) → ℝ≥0∞) :
    IsLocallyConstant (fun x => F (s.val x)) := s.locally_constant.comp F

theorem integral_section_isVLSC (s : ClopenStep k) (ρ : Valuation Y) :
    IsVLSC (fun x => vIntegral ρ (s.val x)) := by
  intro a
  exact s.locally_constant {v : Y → ℝ≥0∞ | a < vIntegral ρ v}

variable [MeasurableSpace X] [OpensMeasurableSpace X]

/-- Exact finite-range parameter integration against the supplied measure. -/
theorem lintegral_comp_eq_sum (s : ClopenStep k) (μ : Measure X)
    (F : (Y → ℝ≥0∞) → ℝ≥0∞) :
    (∫⁻ x, F (s.val x) ∂μ) = ∑ v ∈ s.rangeFinset, μ (s.fiber v : Set X) * F v := by
  classical
  have he : (fun x => F (s.val x)) =
      fun x => ∑ v ∈ s.rangeFinset, (s.fiber v : Set X).indicator (fun _ => F v) x :=
    funext (s.comp_eq_sum F)
  rw [he, lintegral_finset_sum]
  · apply Finset.sum_congr rfl
    intro v hv
    rw [lintegral_indicator_const (s.fiber v).isOpen.measurableSet, mul_comm]
  · intro v hv
    exact measurable_const.indicator (s.fiber v).isOpen.measurableSet

theorem lintegral_parameter_eq_sum (s : ClopenStep k) (μ : Measure X) (y : Y) :
    (∫⁻ x, s.val x y ∂μ) = ∑ v ∈ s.rangeFinset, μ (s.fiber v : Set X) * v y :=
  s.lintegral_comp_eq_sum μ (fun v => v y)

end ClopenStep
end CantorFubini
