import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

/-! Ordinary real-threshold translation lemmas for the genuine lower integral.
No valuation law is assumed here. In the last lemma the negative half-axis is
explicitly constant: a clamped `ofReal` profile does not have that property in
general, so it must not be silently substituted for this extended profile. -/

set_option autoImplicit false
open Set MeasureTheory
open scoped ENNReal
namespace ZFCFubini

theorem threshold_shift_halfline (g : ℝ → ℝ≥0∞) (c : ℝ) :
    (∫⁻ a : ℝ in Ici c, g (a - c)) = ∫⁻ a : ℝ in Ici 0, g a := by
  have h := (measurePreserving_add_right (volume : Measure ℝ) c).setLIntegral_comp_preimage_emb
    (MeasurableEquiv.addRight c).measurableEmbedding (fun a => g (a - c)) (Ici c)
  have hpre : (fun a : ℝ => a + c) ⁻¹' Ici c = Ici 0 := by
    ext a
    simp only [mem_preimage, mem_Ici]
    exact (by constructor <;> intro h <;> linarith)
  rw [hpre] at h
  simpa only [add_sub_cancel_right] using h.symm

theorem threshold_split_halfline (g : ℝ → ℝ≥0∞) (c : ℝ) (hc : 0 ≤ c) :
    (∫⁻ a : ℝ in Ici 0, g a) =
      (∫⁻ a : ℝ in Ico 0 c, g a) + ∫⁻ a : ℝ in Ici c, g a := by
  have hd : Disjoint (Ico (0 : ℝ) c) (Ici c) :=
    Set.disjoint_left.mpr (fun _ ha hb => not_lt_of_ge hb ha.2)
  have he : Ico (0 : ℝ) c ∪ Ici c = Ici 0 := by
    ext a
    constructor
    · rintro (ha | ha)
      · exact ha.1
      · exact hc.trans ha
    · intro ha
      by_cases hac : a < c
      · exact Or.inl ⟨ha, hac⟩
      · exact Or.inr (le_of_not_gt hac)
  have h := lintegral_union (μ := (volume : Measure ℝ)) (f := g) measurableSet_Ici hd
  rw [he] at h
  exact h

theorem threshold_shift_constant_negative (g : ℝ → ℝ≥0∞) (m : ℝ≥0∞)
    (hnegative : ∀ a : ℝ, a < 0 → g a = m) (c : ℝ) (hc : 0 ≤ c) :
    (∫⁻ a : ℝ in Ici 0, g (a - c)) =
      ENNReal.ofReal c * m + ∫⁻ a : ℝ in Ici 0, g a := by
  rw [threshold_split_halfline (fun a => g (a - c)) c hc, threshold_shift_halfline]
  congr 1
  calc
    (∫⁻ a : ℝ in Ico 0 c, g (a - c)) = ∫⁻ _a : ℝ in Ico 0 c, m :=
      setLIntegral_congr_fun measurableSet_Ico (fun a ha => hnegative (a - c) (sub_neg.mpr ha.2))
    _ = ENNReal.ofReal c * m := by
      rw [setLIntegral_const, Real.volume_Ico, sub_zero, mul_comm]

end ZFCFubini
