import ZFCFubini.ParameterMeasure
import Mathlib.MeasureTheory.Covering.DensityTheorem
import Mathlib.MeasureTheory.Measure.NullMeasurable

/-!
Actual one-dimensional density on R/Z, at all positive radii, and the
completion bridge. No conclusion about density is a class hypothesis.
-/

set_option autoImplicit false
open Set Filter Metric MeasureTheory TopologicalSpace Topology
open scoped ENNReal Topology symmDiff

namespace ZFCFubini

/-- The completed normalized Haar measure is mathlib's genuine completion. -/
noncomputable def completedHaar : Measure (NullMeasurableSpace Circle volume) :=
  (volume : Measure Circle).completion

/-- This is the exact completion measurability equivalence, not a replacement
of completed measurability by Borel measurability. -/
theorem completedHaar_measurable_iff (A : Set Circle) :
    @MeasurableSet (NullMeasurableSpace Circle volume) inferInstance A ↔
      NullMeasurableSet A (volume : Measure Circle) := Iff.rfl

theorem completedHaar_apply (A : Set Circle) : completedHaar A = volume A := rfl

instance completedHaar_complete : completedHaar.IsComplete :=
  inferInstanceAs ((volume : Measure Circle).completion.IsComplete)

instance completedHaar_probability : IsProbabilityMeasure completedHaar where
  measure_univ := UnitAddCircle.measure_univ

theorem circle_volume_ball (x : Circle) (r : ℝ) :
    volume (ball x r) = ENNReal.ofReal (min 1 (2 * r)) := by
  rw [← (AddCircle.closedBall_ae_eq_ball (x := x) (ε := r)).measure_eq,
    AddCircle.volume_closedBall]

theorem circle_volume_ball_pos (x : Circle) {r : ℝ} (hr : 0 < r) :
    0 < volume (ball x r) := by
  rw [circle_volume_ball, ENNReal.ofReal_pos]
  exact lt_min (by norm_num) (mul_pos (by norm_num) hr)

/-- Constant two is a uniform doubling constant for actual circle Haar. -/
instance circleHaar_doubling : IsUnifLocDoublingMeasure (volume : Measure Circle) where
  exists_measure_closedBall_le_mul'' := by
    refine ⟨2, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with r hr x
    have hr0 : 0 < r := hr
    rw [AddCircle.volume_closedBall, AddCircle.volume_closedBall]
    norm_num only [ENNReal.coe_ofNat]
    rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    apply ENNReal.ofReal_le_ofReal
    by_cases h : 2 * r ≤ 1
    · rw [min_eq_right h]
      exact (min_le_right _ _).trans (by ring_nf; rfl)
    · rw [min_eq_left (le_of_not_ge h)]
      exact (min_le_left _ _).trans (by norm_num)

/-- Printed ordinary-open-ball real density ratio. Raw `volume` is legitimate
here because `completedHaar_apply` proves equality of completed masses. -/
noncomputable def densityRatio (A : Set Circle) (x : Circle) (r : ℝ) : ℝ :=
  (volume (A ∩ ball x r)).toReal / (volume (ball x r)).toReal

/-- Exactly the all-radii limit r downarrow 0 in the manuscript. -/
def densityPoints (A : Set Circle) : Set Circle :=
  {x | Tendsto (densityRatio A x) (𝓝[>] (0 : ℝ)) (𝓝 1)}

/-- Closed balls from the library density theorem become ordinary open balls
pointwise in the radius, through their proved a.e. equality. -/
theorem densityPoints_ae_restrict (A : Set Circle) :
    ∀ᵐ x ∂(volume : Measure Circle).restrict A, x ∈ densityPoints A := by
  have h := IsUnifLocDoublingMeasure.ae_tendsto_measure_inter_div
    (volume : Measure Circle) A 1
  filter_upwards [h] with x hx
  have hc := hx (fun _ : ℝ => x) id tendsto_id
    (by filter_upwards [self_mem_nhdsWithin] with r hr; simpa using hr.le)
  have ho : Tendsto
      (fun r : ℝ => volume (A ∩ ball x r) / volume (ball x r))
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    apply hc.congr
    intro r
    dsimp only [id_eq]
    rw [(AddCircle.closedBall_ae_eq_ball (x := x) (ε := r)).measure_eq,
      ((ae_eq_refl A).inter (AddCircle.closedBall_ae_eq_ball (x := x) (ε := r))).measure_eq]
  have ht := (ENNReal.tendsto_toReal (by simp : (1 : ℝ≥0∞) ≠ ∞)).comp ho
  simpa only [ENNReal.toReal_one, ENNReal.toReal_div, densityPoints,
    mem_setOf_eq, densityRatio, Function.comp_def] using ht

theorem densityRatio_nonneg (A : Set Circle) (x : Circle) (r : ℝ) :
    0 ≤ densityRatio A x r := by unfold densityRatio; positivity

theorem densityRatio_le_one (A : Set Circle) (x : Circle) (r : ℝ) :
    densityRatio A x r ≤ 1 := by
  unfold densityRatio
  exact div_le_one_of_le₀ (ENNReal.toReal_mono (measure_ne_top _ _)
    (measure_mono inter_subset_right)) ENNReal.toReal_nonneg

theorem densityRatio_mono {A B : Set Circle} (hAB : A ⊆ B) (x : Circle) (r : ℝ) :
    densityRatio A x r ≤ densityRatio B x r := by
  unfold densityRatio
  apply div_le_div_of_nonneg_right _ ENNReal.toReal_nonneg
  exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (inter_subset_inter_left _ hAB))

theorem densityPoints_mono {A B : Set Circle} (hAB : A ⊆ B) :
    densityPoints A ⊆ densityPoints B := by
  intro x hx
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hx tendsto_const_nhds
    (densityRatio_mono hAB x) (densityRatio_le_one B x)

theorem densityRatio_congr_ae {A B : Set Circle}
    (hAB : A =ᵐ[(volume : Measure Circle)] B) (x : Circle) (r : ℝ) :
    densityRatio A x r = densityRatio B x r := by
  unfold densityRatio
  rw [(hAB.inter (ae_eq_refl (ball x r))).measure_eq]

theorem densityPoints_congr_ae {A B : Set Circle}
    (hAB : A =ᵐ[(volume : Measure Circle)] B) : densityPoints A = densityPoints B := by
  ext x
  have he := funext (densityRatio_congr_ae hAB x)
  simp only [densityPoints, mem_setOf_eq, he]

theorem densityRatio_compl_add (A : Set Circle)
    (hA : NullMeasurableSet A (volume : Measure Circle)) (x : Circle)
    {r : ℝ} (hr : 0 < r) :
    densityRatio A x r + densityRatio Aᶜ x r = 1 := by
  have hsum : volume (A ∩ ball x r) + volume (Aᶜ ∩ ball x r) = volume (ball x r) := by
    simpa only [inter_comm, diff_eq, compl_compl] using
      measure_inter_add_diff₀ (μ := (volume : Measure Circle)) (ball x r) hA
  have hreal : (volume (A ∩ ball x r)).toReal +
      (volume (Aᶜ ∩ ball x r)).toReal = (volume (ball x r)).toReal := by
    rw [← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _), hsum]
  unfold densityRatio
  rw [← add_div, hreal, div_self]
  exact ne_of_gt (ENNReal.toReal_pos (circle_volume_ball_pos x hr).ne' (measure_ne_top _ _))

theorem densityPoints_disjoint_compl (A : Set Circle)
    (hA : NullMeasurableSet A (volume : Measure Circle)) :
    Disjoint (densityPoints A) (densityPoints Aᶜ) := by
  apply disjoint_left.mpr
  intro x hx hy
  have ht : Tendsto (fun r => densityRatio A x r + densityRatio Aᶜ x r)
      (𝓝[>] (0 : ℝ)) (𝓝 (1 + 1 : ℝ)) := hx.add hy
  have he : (fun r => densityRatio A x r + densityRatio Aᶜ x r)
      =ᶠ[𝓝[>] (0 : ℝ)] fun _ => (1 : ℝ) := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact densityRatio_compl_add A hA x hr
  have hb := tendsto_nhds_unique ht (tendsto_const_nhds.congr' he.symm)
  norm_num at hb

/-- The full printed density theorem, including completion measurability of
the exact all-radii density-point set. -/
theorem densityPoints_ae_eq (A : Set Circle)
    (hA : NullMeasurableSet A (volume : Measure Circle)) :
    densityPoints A =ᵐ[(volume : Measure Circle)] A := by
  have h₁ := ae_imp_of_ae_restrict (densityPoints_ae_restrict A)
  have h₂ := ae_imp_of_ae_restrict (densityPoints_ae_restrict Aᶜ)
  filter_upwards [h₁, h₂] with x hx hy
  apply propext
  constructor
  · intro hxD
    by_contra hxA
    exact (disjoint_left.mp (densityPoints_disjoint_compl A hA)) hxD (hy hxA)
  · exact hx

theorem densityPoints_nullMeasurable (A : Set Circle)
    (hA : NullMeasurableSet A (volume : Measure Circle)) :
    NullMeasurableSet (densityPoints A) (volume : Measure Circle) :=
  hA.congr (densityPoints_ae_eq A hA).symm

/-- Printed one-dimensional circle density theorem, with measurability in
the actual completed sigma algebra and completed symmetric-difference mass. -/
theorem circle_density_theorem (A : Set Circle)
    (hA : @MeasurableSet (NullMeasurableSpace Circle volume) inferInstance A) :
    @MeasurableSet (NullMeasurableSpace Circle volume) inferInstance (densityPoints A) ∧
      completedHaar (A ∆ densityPoints A) = 0 := by
  refine ⟨densityPoints_nullMeasurable A hA, ?_⟩
  exact measure_symmDiff_eq_zero_iff.mpr (densityPoints_ae_eq A hA).symm

/-- This literal family is the manuscript's tau, using the completed Haar
measurability proved equivalent above. -/
def DensityOpen (U : Set Circle) : Prop :=
  NullMeasurableSet U (volume : Measure Circle) ∧ U ⊆ densityPoints U

end ZFCFubini
