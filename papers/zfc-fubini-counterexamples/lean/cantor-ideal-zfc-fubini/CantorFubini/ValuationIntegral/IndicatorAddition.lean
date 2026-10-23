import CantorFubini.ValuationIntegral
import Mathlib.MeasureTheory.Group.LIntegral

/-!
Adding one finite positive open indicator.  Modularity is used at each strict
level, followed by translation of Lebesgue measure on the threshold line.
Only a finite auxiliary integral is cancelled; no subtraction of infinities
and no extension of the original valuation to a measure is used.
-/

set_option autoImplicit false
open Set Topology TopologicalSpace MeasureTheory
open scoped ENNReal
universe u v

namespace CantorFubini

theorem IsVLSC.indicator {X : Type u} [TopologicalSpace X]
    {f : X → ℝ≥0∞} (hf : IsVLSC f) (U : Opens X) :
    IsVLSC ((U : Set X).indicator f) := by
  intro a
  have he : {x | a < (U : Set X).indicator f x} = (U : Set X) ∩ {x | a < f x} := by
    ext x
    by_cases hx : x ∈ U <;> simp [hx]
  rw [he]
  exact U.isOpen.inter (hf a)

theorem vLevel_indicator_fun {X : Type u} [TopologicalSpace X]
    {f : X → ℝ≥0∞} (hf : IsVLSC f) (U : Opens X) (a : ℝ≥0∞) :
    vLevel ((U : Set X).indicator f) a = U ⊓ vLevel f a := by
  apply Opens.ext
  ext x
  by_cases hx : x ∈ U <;> simp [vLevel_eq hf, vLevel_eq (hf.indicator U), hx]

theorem vIntegral_indicator_fun_le {X : Type u} [TopologicalSpace X]
    (μ : Valuation X) (f : X → ℝ≥0∞) (U : Opens X) :
    vIntegral μ ((U : Set X).indicator f) ≤ vIntegral μ f := by
  apply vIntegral_mono
  intro x
  by_cases hx : x ∈ U <;> simp [hx]

theorem lintegral_Ioi_translate (h : ℝ → ℝ≥0∞) (c : ℝ) :
    (∫⁻ t : ℝ in Ioi c, h (t - c)) = ∫⁻ t : ℝ in Ioi 0, h t := by
  have he : (Ioi c).indicator (fun t => h (t - c)) =
      fun t => (Ioi (0 : ℝ)).indicator h (t + -c) := by
    funext t
    simp only [← sub_eq_add_neg]
    by_cases ht : c < t <;> simp [ht, sub_pos]
  rw [← lintegral_indicator measurableSet_Ioi, he,
    lintegral_add_right_eq_self, lintegral_indicator measurableSet_Ioi]

theorem lintegral_Ioi_piecewise_translate (h : ℝ → ℝ≥0∞)
    (A : ℝ≥0∞) (c : ℝ) (hc : 0 ≤ c) :
    (∫⁻ t : ℝ in Ioi 0, if t < c then A else h (t - c)) =
      ENNReal.ofReal c * A + ∫⁻ t : ℝ in Ioi 0, h t := by
  classical
  have he : (Ioi (0 : ℝ)).indicator (fun t => if t < c then A else h (t - c))
      =ᵐ[volume] fun t =>
        (Ioo (0 : ℝ) c).indicator (fun _ => A) t +
          (Ioi c).indicator (fun t => h (t - c)) t := by
    filter_upwards [volume.ae_ne c] with t htc
    by_cases ht : 0 < t
    · by_cases htc' : t < c
      · have hct : ¬c < t := not_lt_of_ge htc'.le
        simp [ht, htc', hct]
      · have hct : c < t := lt_of_le_of_ne (not_lt.mp htc') htc.symm
        simp [ht, htc', hct]
    · have hct : ¬c < t := not_lt_of_ge ((not_lt.mp ht).trans hc)
      simp [ht, hct]
  calc
    (∫⁻ t : ℝ in Ioi 0, if t < c then A else h (t - c)) =
        ∫⁻ t : ℝ, (Ioo (0 : ℝ) c).indicator (fun _ => A) t +
          (Ioi c).indicator (fun t => h (t - c)) t := by
      rw [← lintegral_indicator measurableSet_Ioi]
      exact lintegral_congr_ae he
    _ = (∫⁻ t : ℝ in Ioo 0 c, A) + ∫⁻ t : ℝ in Ioi c, h (t - c) := by
      rw [lintegral_add_left (measurable_const.indicator measurableSet_Ioo),
        lintegral_indicator measurableSet_Ioo, lintegral_indicator measurableSet_Ioi]
    _ = ENNReal.ofReal c * A + ∫⁻ t : ℝ in Ioi 0, h t := by
      rw [lintegral_Ioi_translate]
      simp [Real.volume_Ioo, mul_comm]

noncomputable def indicatorShiftOpen {X : Type u} [TopologicalSpace X]
    (f : X → ℝ≥0∞) (U : Opens X) (c : ℝ≥0∞) (t : ℝ) : Opens X :=
  if t < c.toReal then U else U ⊓ vLevel f (ENNReal.ofReal (t - c.toReal))

theorem vLevel_add_indicator_pair {X : Type u} [TopologicalSpace X]
    {f : X → ℝ≥0∞} (hf : IsVLSC f) (U : Opens X)
    (c : ℝ≥0∞) (hc : c ≠ ∞) (t : ℝ) (ht : 0 < t) :
    vLevel (fun x => f x + (U : Set X).indicator (fun _ => c) x) (ENNReal.ofReal t) =
        vLevel f (ENNReal.ofReal t) ⊔ indicatorShiftOpen f U c t ∧
      vLevel ((U : Set X).indicator f) (ENNReal.ofReal t) =
        vLevel f (ENNReal.ofReal t) ⊓ indicatorShiftOpen f U c t := by
  have hfc := hf.add (isVLSC_indicator U c)
  have hca : ENNReal.ofReal c.toReal = c := ENNReal.ofReal_toReal hc
  have hsmall : ENNReal.ofReal (t - c.toReal) ≤ ENNReal.ofReal t :=
    ENNReal.ofReal_le_ofReal (sub_le_self _ ENNReal.toReal_nonneg)
  have hlt (hct : ¬t < c.toReal) (x : X) :
      ENNReal.ofReal t < f x + c ↔ ENNReal.ofReal (t - c.toReal) < f x := by
    have he : ENNReal.ofReal t = ENNReal.ofReal (t - c.toReal) + c := by
      calc
        ENNReal.ofReal t = ENNReal.ofReal ((t - c.toReal) + c.toReal) := by
          rw [sub_add_cancel]
        _ = ENNReal.ofReal (t - c.toReal) + ENNReal.ofReal c.toReal :=
          ENNReal.ofReal_add (sub_nonneg.mpr (not_lt.mp hct)) ENNReal.toReal_nonneg
        _ = ENNReal.ofReal (t - c.toReal) + c := by rw [hca]
    rw [he, ENNReal.add_lt_add_iff_right hc]
  constructor
  · rw [vLevel_eq hfc, vLevel_eq hf]
    by_cases hct : t < c.toReal
    · rw [indicatorShiftOpen, if_pos hct]
      apply Opens.ext
      ext x
      change (ENNReal.ofReal t < f x + (U : Set X).indicator (fun _ => c) x) ↔
        ENNReal.ofReal t < f x ∨ x ∈ U
      by_cases hx : x ∈ U
      · have htc : ENNReal.ofReal t < c := by
          rw [← hca]
          exact ENNReal.ofReal_lt_ofReal_iff'.mpr ⟨hct, ht.trans hct⟩
        have hsum : ENNReal.ofReal t < f x + c :=
          htc.trans_le (le_add_of_nonneg_left (zero_le (f x)))
        simp [hx, hsum]
      · simp [hx]
    · rw [indicatorShiftOpen, if_neg hct, vLevel_eq hf]
      apply Opens.ext
      ext x
      change (ENNReal.ofReal t < f x + (U : Set X).indicator (fun _ => c) x) ↔
        ENNReal.ofReal t < f x ∨ (x ∈ U ∧ ENNReal.ofReal (t - c.toReal) < f x)
      by_cases hx : x ∈ U
      · simp only [Set.indicator_of_mem hx, hx, true_and, hlt hct x]
        constructor
        · exact Or.inr
        · rintro (h | h)
          · exact hsmall.trans_lt h
          · exact h
      · simp [hx]
  · rw [vLevel_indicator_fun hf U]
    by_cases hct : t < c.toReal
    · rw [indicatorShiftOpen, if_pos hct, inf_comm]
    · rw [indicatorShiftOpen, if_neg hct, vLevel_eq hf, vLevel_eq hf]
      apply Opens.ext
      ext x
      change (x ∈ U ∧ ENNReal.ofReal t < f x) ↔
        ENNReal.ofReal t < f x ∧ (x ∈ U ∧ ENNReal.ofReal (t - c.toReal) < f x)
      exact ⟨fun h => ⟨h.2, h.1, hsmall.trans_lt h.2⟩,
        fun h => ⟨h.2.1, h.1⟩⟩

theorem vIntegral_add_indicator {X : Type u} [TopologicalSpace X]
    (μ : Valuation X) {f : X → ℝ≥0∞} (hf : IsVLSC f)
    (U : Opens X) (c : ℝ≥0∞) (hc : c ≠ ∞) :
    vIntegral μ (fun x => f x + (U : Set X).indicator (fun _ => c) x) =
      vIntegral μ f + c * μ U := by
  classical
  by_cases hfin : vIntegral μ f = ∞
  · rw [hfin, top_add]
    apply top_unique
    rw [← hfin]
    exact vIntegral_mono μ (fun x => le_add_of_nonneg_right (zero_le _))
  let g : X → ℝ≥0∞ := (U : Set X).indicator f
  have hg : IsVLSC g := hf.indicator U
  have hgne : vIntegral μ g ≠ ∞ :=
    ne_top_of_le_ne_top hfin (vIntegral_indicator_fun_le μ f U)
  have hmod (t : ℝ) (ht : 0 < t) :
      vLevelMass μ (fun x => f x + (U : Set X).indicator (fun _ => c) x) t +
          vLevelMass μ g t =
        vLevelMass μ f t +
          (if t < c.toReal then μ U else vLevelMass μ g (t - c.toReal)) := by
    obtain ⟨hadd, hinter⟩ := vLevel_add_indicator_pair hf U c hc t ht
    have hB : μ (indicatorShiftOpen f U c t) =
        if t < c.toReal then μ U else vLevelMass μ g (t - c.toReal) := by
      unfold indicatorShiftOpen
      split_ifs
      · rfl
      · rw [show vLevelMass μ g (t - c.toReal) =
          μ (U ⊓ vLevel f (ENNReal.ofReal (t - c.toReal))) from
          congrArg μ (vLevel_indicator_fun hf U _)]
    unfold vLevelMass
    rw [hadd, hinter]
    exact (μ.modular _ _).symm.trans (congrArg (fun b => μ (vLevel f (ENNReal.ofReal t)) + b) hB)
  have hi :
      vIntegral μ (fun x => f x + (U : Set X).indicator (fun _ => c) x) + vIntegral μ g =
        (vIntegral μ f + c * μ U) + vIntegral μ g := by
    calc
      vIntegral μ (fun x => f x + (U : Set X).indicator (fun _ => c) x) + vIntegral μ g =
          ∫⁻ t : ℝ in Ioi 0,
            vLevelMass μ (fun x => f x + (U : Set X).indicator (fun _ => c) x) t +
              vLevelMass μ g t := by
        exact (lintegral_add_left (vLevelMass_measurable μ _) _).symm
      _ = ∫⁻ t : ℝ in Ioi 0, vLevelMass μ f t +
          (if t < c.toReal then μ U else vLevelMass μ g (t - c.toReal)) := by
        apply setLIntegral_congr_fun measurableSet_Ioi
        exact hmod
      _ = vIntegral μ f + (c * μ U + vIntegral μ g) := by
        rw [lintegral_add_left (vLevelMass_measurable μ f),
          lintegral_Ioi_piecewise_translate _ _ _ ENNReal.toReal_nonneg,
          ENNReal.ofReal_toReal hc]
        rfl
      _ = (vIntegral μ f + c * μ U) + vIntegral μ g := (add_assoc _ _ _).symm
  exact (ENNReal.add_left_inj hgne).mp hi

end CantorFubini
