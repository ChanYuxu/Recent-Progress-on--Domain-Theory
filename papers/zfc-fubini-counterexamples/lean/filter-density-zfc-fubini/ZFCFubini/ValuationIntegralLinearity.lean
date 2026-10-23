import ZFCFubini.ValuationIntegralApprox
import ZFCFubini.IntegralThresholdShift
import Mathlib.Order.ScottContinuity.Complete

/-! Linearity from modularity and an actual real-threshold translation.
The intermediate restriction is still a valuation on opens, not a measure.
Only a bounded intermediate integral is cancelled; full MCT removes that
temporary bound. -/

set_option autoImplicit false
open Set Topology TopologicalSpace MeasureTheory
open scoped ENNReal NNReal Classical
universe u v
namespace ZFCFubini
variable {X : Type u} [TopologicalSpace X]

namespace Valuation
def restrictOpen (μ : Valuation X) (U : Opens X) : Valuation X where
  mass V := μ (U ⊓ V)
  strict := by simpa using μ.strict
  modular V W := by
    have h := μ.modular (U ⊓ V) (U ⊓ W)
    rw [← inf_sup_left, inf_inf_inf_comm, inf_idem] at h
    exact h
  continuous := by
    have h : ScottContinuous (fun V : Opens X => U ⊓ V) :=
      ScottContinuous.of_map_sSup (fun A _ _ => by rw [inf_sSup_eq, sSup_image])
    exact h.comp μ.continuous

@[simp] theorem restrictOpen_apply (μ : Valuation X) (U V : Opens X) :
    μ.restrictOpen U V = μ (U ⊓ V) := rfl

theorem restrictOpen_subprobability (μ : Valuation X) (hμ : μ.Subprobability) (U : Opens X) :
    (μ.restrictOpen U).Subprobability := by
  change μ (U ⊓ ⊤) ≤ 1
  simpa using hμ.mass_le_one U
end Valuation

noncomputable def extendedRestrictionLevel (U : Opens X) (f : X → ℝ≥0∞) (a : ℝ) :
    Opens X := if a < 0 then U else U ⊓ integralLevel f a

theorem extendedRestrictionLevel_inf (U : Opens X) (f : X → ℝ≥0∞)
    (hf : IsLSC f) (a : ℝ) (c : ℝ≥0) :
    integralLevel f a ⊓ extendedRestrictionLevel U f (a - c) = U ⊓ integralLevel f a := by
  classical
  unfold extendedRestrictionLevel
  split_ifs with hac
  · exact inf_comm _ _
  · have hlev : integralLevel f a ≤ integralLevel f (a - c) :=
      interior_mono (fun x hx => (ENNReal.ofReal_le_ofReal (sub_le_self a c.property)).trans_lt hx)
    apply le_antisymm
    · exact le_inf (inf_le_right.trans inf_le_left) inf_le_left
    · exact le_inf inf_le_right (le_inf inf_le_left (inf_le_right.trans hlev))

theorem integralLevel_add_openStep (f : X → ℝ≥0∞) (hf : IsLSC f)
    (U : Opens X) (c : ℝ≥0) (a : ℝ) (ha : 0 ≤ a) :
    integralLevel (f + openStep (c, U)) a =
      integralLevel f a ⊔ extendedRestrictionLevel U f (a - c) := by
  rw [integralLevel_of_isLSC _ (hf.add (openStep_isLSC _)), integralLevel_of_isLSC _ hf]
  apply Opens.ext
  ext x
  change (ENNReal.ofReal a < f x + openStep (c, U) x) ↔
    (ENNReal.ofReal a < f x ∨ x ∈ extendedRestrictionLevel U f (a - c))
  by_cases hx : x ∈ (U : Set X)
  · simp only [openStep, Set.indicator_of_mem hx]
    by_cases hac : a < (c : ℝ)
    · have hsum : ENNReal.ofReal a < f x + (c : ℝ≥0∞) :=
        ((ENNReal.ofReal_lt_coe_iff ha).2 hac).trans_le
          (by simpa only [add_comm] using (le_self_add : (c : ℝ≥0∞) ≤ c + f x))
      rw [extendedRestrictionLevel, if_pos (sub_neg.mpr hac)]
      exact iff_of_true hsum (Or.inr hx)
    · have hca : (c : ℝ) ≤ a := le_of_not_gt hac
      have hcc : (c : ℝ≥0∞) ≤ ENNReal.ofReal a := by
        rw [← ENNReal.ofReal_coe_nnreal]
        exact ENNReal.ofReal_le_ofReal hca
      have he : (ENNReal.ofReal a < f x + (c : ℝ≥0∞)) ↔
          ENNReal.ofReal (a - c) < f x := by
        rw [ENNReal.ofReal_sub a (q := (c : ℝ)) c.property, ENNReal.ofReal_coe_nnreal]
        exact (ENNReal.sub_lt_iff_lt_right ENNReal.coe_ne_top hcc).symm
      rw [he]
      rw [extendedRestrictionLevel, if_neg (not_lt.mpr (sub_nonneg.mpr hca))]
      change (ENNReal.ofReal (a - c) < f x) ↔
        (ENNReal.ofReal a < f x ∨ x ∈ (U : Set X) ∧ x ∈ integralLevel f (a - c))
      rw [integralLevel_of_isLSC _ hf]
      change (ENNReal.ofReal (a - c) < f x) ↔
        (ENNReal.ofReal a < f x ∨ x ∈ (U : Set X) ∧ ENNReal.ofReal (a - c) < f x)
      simp only [hx, true_and]
      exact ⟨Or.inr, fun h => h.elim
        (fun h => (ENNReal.ofReal_le_ofReal (sub_le_self a c.property)).trans_lt h) id⟩
  · simp only [openStep, Set.indicator_of_notMem hx, add_zero]
    unfold extendedRestrictionLevel
    split_ifs
    · change (ENNReal.ofReal a < f x) ↔ (ENNReal.ofReal a < f x ∨ x ∈ (U : Set X))
      simp only [hx, or_false]
    · change (ENNReal.ofReal a < f x) ↔
        (ENNReal.ofReal a < f x ∨ x ∈ (U : Set X) ∧ x ∈ integralLevel f (a - c))
      simp only [hx, false_and, or_false]

noncomputable def extendedRestrictionProfile (μ : Valuation X) (U : Opens X)
    (f : X → ℝ≥0∞) (a : ℝ) : ℝ≥0∞ := μ (extendedRestrictionLevel U f a)

theorem extendedRestrictionProfile_measurable (μ : Valuation X) (U : Opens X)
    (f : X → ℝ≥0∞) (hf : IsLSC f) : Measurable (extendedRestrictionProfile μ U f) := by
  have he : extendedRestrictionProfile μ U f =
      (Iio (0 : ℝ)).piecewise (fun _ => μ U) (integralProfile (μ.restrictOpen U) f) := by
    funext a
    by_cases ha : a < 0 <;>
      simp [extendedRestrictionProfile, extendedRestrictionLevel, Set.piecewise, ha, integralProfile]
  rw [he]
  exact measurable_const.piecewise measurableSet_Iio
    (integralProfile_lowerSemicontinuous _ f hf).measurable

theorem integral_extendedRestrictionProfile (μ : Valuation X) (U : Opens X)
    (f : X → ℝ≥0∞) :
    (∫⁻ a : ℝ in Ici 0, extendedRestrictionProfile μ U f a) =
      choquetIntegral (μ.restrictOpen U) f := by
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ici] with a ha
  have ha' : 0 ≤ a := ha
  simp [extendedRestrictionProfile, extendedRestrictionLevel, not_lt.mpr ha',
    integralProfile]
  rfl

theorem integralProfile_add_openStep (μ : Valuation X) (f : X → ℝ≥0∞)
    (hf : IsLSC f) (U : Opens X) (c : ℝ≥0) (a : ℝ) (ha : 0 ≤ a) :
    integralProfile μ (f + openStep (c, U)) a + integralProfile (μ.restrictOpen U) f a =
      integralProfile μ f a + extendedRestrictionProfile μ U f (a - c) := by
  unfold integralProfile extendedRestrictionProfile
  rw [integralLevel_add_openStep f hf U c a ha]
  change μ (integralLevel f a ⊔ extendedRestrictionLevel U f (a - c)) +
    μ (U ⊓ integralLevel f a) = _
  rw [← extendedRestrictionLevel_inf U f hf a c]
  exact (μ.modular _ _).symm

theorem choquetIntegral_le_nnreal (μ : Valuation X) (hμ : μ.Subprobability)
    {f : X → ℝ≥0∞} (C : ℝ≥0) (hfC : ∀ x, f x ≤ C) :
    choquetIntegral μ f ≤ C := by
  calc
    choquetIntegral μ f ≤ choquetIntegral μ (fun _ => (C : ℝ≥0∞)) :=
      choquetIntegral_mono μ hfC
    _ = (C : ℝ≥0∞) * μ ⊤ := choquetIntegral_const_nnreal μ C
    _ ≤ C := by simpa using mul_le_mul_left' hμ (C : ℝ≥0∞)

theorem choquetIntegral_add_openStep_bounded (μ : Valuation X) (hμ : μ.Subprobability)
    (f : X → ℝ≥0∞) (hf : IsLSC f) (C : ℝ≥0) (hfC : ∀ x, f x ≤ C)
    (U : Opens X) (c : ℝ≥0) :
    choquetIntegral μ (f + openStep (c, U)) = choquetIntegral μ f + (c : ℝ≥0∞) * μ U := by
  have he :
      (∫⁻ a : ℝ in Ici 0, integralProfile μ (f + openStep (c, U)) a +
        integralProfile (μ.restrictOpen U) f a) =
      ∫⁻ a : ℝ in Ici 0, integralProfile μ f a +
        extendedRestrictionProfile μ U f (a - c) := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ici] with a ha
    exact integralProfile_add_openStep μ f hf U c a ha
  rw [lintegral_add_left (integralProfile_lowerSemicontinuous μ _
        (hf.add (openStep_isLSC _))).measurable,
    lintegral_add_left (integralProfile_lowerSemicontinuous μ f hf).measurable] at he
  have hnegative : ∀ a : ℝ, a < 0 → extendedRestrictionProfile μ U f a = μ U := by
    intro a ha
    simp [extendedRestrictionProfile, extendedRestrictionLevel, ha]
  rw [threshold_shift_constant_negative _ (μ U) hnegative (c : ℝ) c.property,
    ENNReal.ofReal_coe_nnreal, integral_extendedRestrictionProfile] at he
  have hfin : choquetIntegral (μ.restrictOpen U) f ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.coe_ne_top
      (choquetIntegral_le_nnreal _ (μ.restrictOpen_subprobability hμ U) C hfC)
  apply (ENNReal.add_left_inj hfin).mp
  simpa only [← choquetIntegral_eq_profile, add_assoc] using he

theorem choquetIntegral_add_openStep (μ : Valuation X) (hμ : μ.Subprobability)
    (f : X → ℝ≥0∞) (hf : IsLSC f) (U : Opens X) (c : ℝ≥0) :
    choquetIntegral μ (f + openStep (c, U)) = choquetIntegral μ f + (c : ℝ≥0∞) * μ U := by
  let g (F : Finset ℝ≥0) : X → ℝ≥0∞ := lowerStep f hf F + openStep (c, U)
  have hg (F : Finset ℝ≥0) : IsLSC (g F) :=
    (lowerStep_isLSC f hf F).add (openStep_isLSC _)
  have hgd : Directed (· ≤ ·) g := by
    intro F G
    obtain ⟨H, hFH, hGH⟩ := lowerStep_directed f hf F G
    exact ⟨H, fun x => add_le_add (hFH x) le_rfl, fun x => add_le_add (hGH x) le_rfl⟩
  have he : f + openStep (c, U) = fun x => ⨆ F : Finset ℝ≥0, g F x := by
    funext x
    change f x + openStep (c, U) x = ⨆ F : Finset ℝ≥0, lowerStep f hf F x + openStep (c, U) x
    rw [← ENNReal.iSup_add, iSup_lowerStep]
  calc
    choquetIntegral μ (f + openStep (c, U)) = choquetIntegral μ (fun x => ⨆ F, g F x) :=
      congrArg (choquetIntegral μ) he
    _ = ⨆ F, choquetIntegral μ (g F) := choquetIntegral_iSup μ g hg hgd
    _ = ⨆ F, choquetIntegral μ (lowerStep f hf F) + (c : ℝ≥0∞) * μ U := by
      apply iSup_congr
      intro F
      exact choquetIntegral_add_openStep_bounded μ hμ _ (lowerStep_isLSC f hf F)
        (finiteOpenStepBound _) (finiteOpenStep_le _) U c
    _ = (⨆ F, choquetIntegral μ (lowerStep f hf F)) + (c : ℝ≥0∞) * μ U :=
      (ENNReal.iSup_add _).symm
    _ = choquetIntegral μ f + (c : ℝ≥0∞) * μ U := by
      rw [← choquetIntegral_eq_iSup_lowerStep]

theorem choquetIntegral_add (μ : Valuation X) (hμ : μ.Subprobability)
    {f g : X → ℝ≥0∞} (hf : IsLSC f) (hg : IsLSC g) :
    choquetIntegral μ (f + g) = choquetIntegral μ f + choquetIntegral μ g := by
  let C := choquetIntegral μ f
  have hbase (a : X → ℝ≥0∞) : C ≤ choquetIntegral μ (f + a) :=
    choquetIntegral_mono μ (fun x => le_self_add)
  by_cases hC : C = ∞
  · have hsum : choquetIntegral μ (f + g) = ∞ := top_unique (hC ▸ hbase g)
    change choquetIntegral μ (f + g) = C + choquetIntegral μ g
    rw [hsum, hC, top_add]
  let F : (X → ℝ≥0∞) → ℝ≥0∞ := fun a => choquetIntegral μ (f + a) - C
  have htranslate (a : X → ℝ≥0∞) : F a + C = choquetIntegral μ (f + a) :=
    tsub_add_cancel_of_le (hbase a)
  have hFmod (a b : X → ℝ≥0∞) (ha : IsLSC a) (hb : IsLSC b) :
      F a + F b = F (a ⊔ b) + F (a ⊓ b) := by
    have hsup : (f + a) ⊔ (f + b) = f + (a ⊔ b) := by
      funext x
      exact (add_max (f x) (a x) (b x)).symm
    have hinf : (f + a) ⊓ (f + b) = f + (a ⊓ b) := by
      funext x
      exact (add_min (f x) (a x) (b x)).symm
    have hmod := choquetIntegral_modular μ (hf.add ha) (hf.add hb)
    rw [hsup, hinf] at hmod
    apply (ENNReal.add_left_inj (ENNReal.add_ne_top.mpr ⟨hC, hC⟩)).mp
    calc
      (F a + F b) + (C + C) = (F a + C) + (F b + C) := by ac_rfl
      _ = choquetIntegral μ (f + a) + choquetIntegral μ (f + b) := by rw [htranslate, htranslate]
      _ = choquetIntegral μ (f + (a ⊔ b)) + choquetIntegral μ (f + (a ⊓ b)) := hmod
      _ = (F (a ⊔ b) + C) + (F (a ⊓ b) + C) := by rw [htranslate, htranslate]
      _ = (F (a ⊔ b) + F (a ⊓ b)) + (C + C) := by ac_rfl
  have hFsup (a : Finset ℝ≥0 → X → ℝ≥0∞) (ha : ∀ i, IsLSC (a i))
      (had : Directed (· ≤ ·) a) : F (fun x => ⨆ i, a i x) = ⨆ i, F (a i) := by
    have hplus : f + (fun x => ⨆ i, a i x) = fun x => ⨆ i, (f + a i) x := by
      funext x
      exact ENNReal.add_iSup _
    have hpd : Directed (· ≤ ·) (fun i => f + a i) := by
      intro i j
      obtain ⟨k, hik, hjk⟩ := had i j
      exact ⟨k, fun x => add_le_add le_rfl (hik x), fun x => add_le_add le_rfl (hjk x)⟩
    simp only [F, hplus, choquetIntegral_iSup μ _ (fun i => hf.add (ha i)) hpd,
      ENNReal.iSup_sub]
  have hFind (U : Opens X) (c : ℝ≥0) :
      F ((U : Set X).indicator (fun _ => (c : ℝ≥0∞))) = (c : ℝ≥0∞) * μ U := by
    change choquetIntegral μ (f + openStep (c, U)) - C = _
    rw [choquetIntegral_add_openStep μ hμ f hf U c]
    exact ENNReal.add_sub_cancel_left hC
  have hFg := choquetIntegral_unique_of_modular_iSup μ hμ F hFmod hFsup hFind g hg
  change choquetIntegral μ (f + g) = C + choquetIntegral μ g
  rw [← htranslate g, hFg, add_comm]

theorem IsLSC.mul_const (c : ℝ≥0) {f : X → ℝ≥0∞} (hf : IsLSC f) :
    IsLSC (fun x => (c : ℝ≥0∞) * f x) :=
  isLSC_iff_lowerSemicontinuous.mpr
    ((ENNReal.continuous_const_mul ENNReal.coe_ne_top).comp_lowerSemicontinuous
      hf.lowerSemicontinuous (fun _ _ h => mul_le_mul_left' h (c : ℝ≥0∞)))

theorem choquetIntegral_mul_const (μ : Valuation X) (hμ : μ.Subprobability)
    (c : ℝ≥0) {f : X → ℝ≥0∞} (hf : IsLSC f) :
    choquetIntegral μ (fun x => (c : ℝ≥0∞) * f x) = (c : ℝ≥0∞) * choquetIntegral μ f := by
  by_cases hc : c = 0
  · subst c
    simp only [ENNReal.coe_zero, zero_mul, choquetIntegral_zero]
  have hc0 : (c : ℝ≥0∞) ≠ 0 := by exact_mod_cast hc
  let F : (X → ℝ≥0∞) → ℝ≥0∞ :=
    fun a => (c : ℝ≥0∞)⁻¹ * choquetIntegral μ (fun x => (c : ℝ≥0∞) * a x)
  have hscaleSup (a b : X → ℝ≥0∞) :
      (fun x => (c : ℝ≥0∞) * (a ⊔ b) x) =
        (fun x => (c : ℝ≥0∞) * a x) ⊔ (fun x => (c : ℝ≥0∞) * b x) := by
    funext x
    exact mul_max _ _ _
  have hscaleInf (a b : X → ℝ≥0∞) :
      (fun x => (c : ℝ≥0∞) * (a ⊓ b) x) =
        (fun x => (c : ℝ≥0∞) * a x) ⊓ (fun x => (c : ℝ≥0∞) * b x) := by
    funext x
    exact mul_min _ _ _
  have hFmod (a b : X → ℝ≥0∞) (ha : IsLSC a) (hb : IsLSC b) :
      F a + F b = F (a ⊔ b) + F (a ⊓ b) := by
    unfold F
    rw [← mul_add, choquetIntegral_modular μ (ha.mul_const c) (hb.mul_const c),
      ← hscaleSup, ← hscaleInf, mul_add]
  have hFsup (a : Finset ℝ≥0 → X → ℝ≥0∞) (ha : ∀ i, IsLSC (a i))
      (had : Directed (· ≤ ·) a) : F (fun x => ⨆ i, a i x) = ⨆ i, F (a i) := by
    have he : (fun x => (c : ℝ≥0∞) * ⨆ i, a i x) =
        fun x => ⨆ i, (c : ℝ≥0∞) * a i x := by
      funext x
      exact ENNReal.mul_iSup _ _
    have hcd : Directed (· ≤ ·) (fun i x => (c : ℝ≥0∞) * a i x) := by
      intro i j
      obtain ⟨k, hik, hjk⟩ := had i j
      exact ⟨k, fun x => mul_le_mul_left' (hik x) _, fun x => mul_le_mul_left' (hjk x) _⟩
    simp only [F, he, choquetIntegral_iSup μ _ (fun i => (ha i).mul_const c) hcd,
      ENNReal.mul_iSup]
  have hFind (U : Opens X) (d : ℝ≥0) :
      F ((U : Set X).indicator (fun _ => (d : ℝ≥0∞))) = (d : ℝ≥0∞) * μ U := by
    have he : (fun x => (c : ℝ≥0∞) * (U : Set X).indicator (fun _ => (d : ℝ≥0∞)) x) =
        (U : Set X).indicator (fun _ => ((c * d : ℝ≥0) : ℝ≥0∞)) := by
      funext x
      by_cases hx : x ∈ (U : Set X) <;> simp [hx, ENNReal.coe_mul]
    change (c : ℝ≥0∞)⁻¹ * choquetIntegral μ _ = _
    rw [he, choquetIntegral_indicator_nnreal, ENNReal.coe_mul, mul_assoc,
      ENNReal.inv_mul_cancel_left hc0 ENNReal.coe_ne_top]
  have hFf := choquetIntegral_unique_of_modular_iSup μ hμ F hFmod hFsup hFind f hf
  calc
    choquetIntegral μ (fun x => (c : ℝ≥0∞) * f x) = (c : ℝ≥0∞) * F f :=
      (ENNReal.mul_inv_cancel_left hc0 ENNReal.coe_ne_top).symm
    _ = (c : ℝ≥0∞) * choquetIntegral μ f := congrArg (fun a => (c : ℝ≥0∞) * a) hFf

end ZFCFubini
