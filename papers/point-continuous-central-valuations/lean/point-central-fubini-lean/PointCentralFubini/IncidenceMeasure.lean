import PointCentralFubini.MeasureIncidence
import PointCentralFubini.IntegrationExtra
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

/-! The finite Borel measure Λ in the reverse inequality of Proposition 4.2. -/
set_option autoImplicit false
open Set Topology TopologicalSpace MeasureTheory Filter Function
open scoped ENNReal BigOperators
universe u
namespace PointCentralFubini

variable {X : Type u} [TopologicalSpace X]

def incidenceRestriction (m : TauMeasure X) (B : Set X) : WithScott (Opens X) → ℝ≥0∞ :=
  fun U => m.measure (((WithScott.ofScott U : Opens X) : Set X) ∩ B)

theorem incidenceRestriction_isLSC (m : TauMeasure X) {B : Set X}
    (hB : MeasurableSet[borel X] B) : IsLSC (incidenceRestriction m B) := by
  have h := scott_isLSC (m.restrict B hB).directed_opens
  simpa only [TauMeasure.restrict_apply,incidenceRestriction] using h

theorem incidenceRestriction_iUnion (m : TauMeasure X) (B : ℕ → Set X)
    (hB : ∀ n, MeasurableSet[borel X] (B n)) (hd : Pairwise (Disjoint on B))
    (U : WithScott (Opens X)) :
    incidenceRestriction m (⋃ n, B n) U = ∑' n, incidenceRestriction m (B n) U := by
  letI : MeasurableSpace X := borel X
  letI : BorelSpace X := ⟨rfl⟩
  simp only [incidenceRestriction,inter_iUnion]
  apply measure_iUnion
  · exact fun i j hij => (hd hij).mono inter_subset_right inter_subset_right
  · exact fun i => (WithScott.ofScott U).isOpen.measurableSet.inter (hB i)

theorem incidenceRestriction_integral_iUnion (m : TauMeasure X) (η : DValuation (Opens X))
    (B : ℕ → Set X) (hB : ∀ n, MeasurableSet[borel X] (B n))
    (hd : Pairwise (Disjoint on B)) :
    integral η (incidenceRestriction m (⋃ n, B n)) =
      ∑' n, integral η (incidenceRestriction m (B n)) := by
  let f : ℕ → WithScott (Opens X) → ℝ≥0∞ := fun N U =>
    ∑ n ∈ Finset.range N, incidenceRestriction m (B n) U
  have hf : ∀ N, IsLSC (f N) := fun N =>
    IsLSC.finset_sum (Finset.range N) _ (fun n _ => incidenceRestriction_isLSC m (hB n))
  have hm : Monotone f := by
    intro N M hNM U
    exact Finset.sum_le_sum_of_subset (Finset.range_mono hNM)
  have he : incidenceRestriction m (⋃ n, B n) = fun U => ⨆ N, f N U := by
    funext U
    rw [incidenceRestriction_iUnion m B hB hd,ENNReal.tsum_eq_iSup_nat]
  rw [he,fpr_integral_iSup η f hf hm.directed_le,ENNReal.tsum_eq_iSup_nat]
  apply iSup_congr; intro N
  exact integral_finset_sum η (Finset.range N) _
    (fun n _ => incidenceRestriction_isLSC m (hB n))

noncomputable def incidenceMeasure (m : TauMeasure X) (η : DValuation (Opens X)) :
    @Measure X (borel X) := by
  letI : MeasurableSpace X := borel X
  let mass : ∀ B : Set X, MeasurableSet B → ℝ≥0∞ :=
    fun B _ => integral η (incidenceRestriction m B)
  refine Measure.ofMeasurable mass ?_ ?_
  · change integral η (incidenceRestriction m ∅) = 0
    have he : incidenceRestriction m ∅ = fun _ => 0 := by
      funext U; simp [incidenceRestriction]
    rw [he,integral_zero]
  · intro B hB hd
    exact incidenceRestriction_integral_iUnion m η B hB hd

theorem incidenceMeasure_apply (m : TauMeasure X) (η : DValuation (Opens X))
    {B : Set X} (hB : MeasurableSet[borel X] B) :
    incidenceMeasure m η B = integral η (incidenceRestriction m B) := by
  letI : MeasurableSpace X := borel X
  unfold incidenceMeasure
  exact Measure.ofMeasurable_apply _ hB

theorem incidenceMeasure_apply_le (m : TauMeasure X) (η : DValuation (Opens X))
    {B : Set X} (hB : MeasurableSet[borel X] B) :
    incidenceMeasure m η B ≤ η ⊤ * m.measure B := by
  rw [incidenceMeasure_apply m η hB,mul_comm]
  exact integral_le_const η (fun _ => measure_mono inter_subset_right)

theorem incidenceMeasure_le (m : TauMeasure X) (η : DValuation (Opens X)) :
    incidenceMeasure m η ≤ η ⊤ • m.measure := by
  letI : MeasurableSpace X := borel X
  apply Measure.le_iff.mpr
  intro B hB
  simpa only [Measure.smul_apply,smul_eq_mul] using incidenceMeasure_apply_le m η hB

theorem incidenceMeasure_finite (m : TauMeasure X) (η : DValuation (Opens X))
    (hη : η.Finite) : incidenceMeasure m η univ ≠ ⊤ :=
  ne_top_of_le_ne_top (ENNReal.mul_ne_top hη m.finite)
    (incidenceMeasure_apply_le m η MeasurableSet.univ)

theorem incidenceMeasure_absolutelyContinuous (m : TauMeasure X) (η : DValuation (Opens X)) :
    incidenceMeasure m η ≪ m.measure :=
  Measure.absolutelyContinuous_of_le_smul (incidenceMeasure_le m η)

theorem incidenceMeasure_rnDeriv (m : TauMeasure X) (η : DValuation (Opens X))
    (hη : η.Finite) (B : Set X) (hB : MeasurableSet[borel X] B) :
    @lintegral X (borel X) (m.measure.restrict B)
      ((incidenceMeasure m η).rnDeriv m.measure) =
      integral η (incidenceRestriction m B) := by
  letI : MeasurableSpace X := borel X
  letI : IsFiniteMeasure m.measure := ⟨m.finite.lt_top⟩
  letI : IsFiniteMeasure (incidenceMeasure m η) := ⟨(incidenceMeasure_finite m η hη).lt_top⟩
  rw [Measure.setLIntegral_rnDeriv' (incidenceMeasure_absolutelyContinuous m η) hB,
    incidenceMeasure_apply m η hB]

end PointCentralFubini
