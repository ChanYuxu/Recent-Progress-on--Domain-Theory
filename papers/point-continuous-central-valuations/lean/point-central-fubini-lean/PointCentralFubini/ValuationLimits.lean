import PointCentralFubini.OpenFubini
import Mathlib.Order.ScottContinuity.Complete
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
set_option autoImplicit false
open Set Topology TopologicalSpace MeasureTheory
open scoped ENNReal
universe u v w
namespace PointCentralFubini
variable {X : Type u} [TopologicalSpace X]

theorem integral_mono_valuation {μ ν : Valuation X} (h : μ ≤ ν) (f : X → ℝ≥0∞) :
    integral μ f ≤ integral ν f := by
  apply lintegral_mono; exact fun _ => h _

/-- Directed convergence in the valuation, derived from the explicitly cited
functional representation and its three integration laws. -/
theorem integral_valuation_iSup (μ : Valuation X) {ι : Type v} [Nonempty ι]
    (ν : ι → Valuation X) (hd : Directed (· ≤ ·) ν)
    (hμ : ∀ U, μ U = ⨆ i, ν i U) (f : X → ℝ≥0∞) (hf : IsLSC f) :
    integral μ f = ⨆ i, integral (ν i) f := by
  let F : (X → ℝ≥0∞) → ℝ≥0∞ := fun g => ⨆ i, integral (ν i) g
  have hF : FunctionalLaws F := by
    constructor
    · intro f g hf hg
      change (⨆ i, integral (ν i) (f+g)) = (⨆ i, integral (ν i) f) + ⨆ i, integral (ν i) g
      simp_rw [fpr_integral_add (hf := hf) (hg := hg)]
      symm
      apply ENNReal.iSup_add_iSup
      intro i j; obtain ⟨k,hik,hjk⟩ := hd i j
      exact ⟨k,add_le_add (integral_mono_valuation hik f) (integral_mono_valuation hjk g)⟩
    · intro a g hg
      change (⨆ i, integral (ν i) (fun x => a*g x)) = a * ⨆ i, integral (ν i) g
      simp_rw [fpr_integral_smul (hf := hg)]
      exact (ENNReal.mul_iSup _ _).symm
    · intro κ _ g hg hgd
      change (⨆ i, integral (ν i) (fun x => ⨆ j, g j x)) = ⨆ j, ⨆ i, integral (ν i) (g j)
      simp_rw [fpr_integral_iSup (hf := hg) (hd := hgd)]
      exact iSup_comm
  have hG : FunctionalLaws (integral μ) :=
    ⟨fpr_integral_add μ,fpr_integral_smul μ,fun g hg hd => fpr_integral_iSup μ g hg hd⟩
  have he := fpr_functional_unique F (integral μ) hF hG
    (fun U => by change (⨆ i, integral (ν i) (indicator U)) = _
                 simp_rw [integral_indicator]; exact (hμ U).symm) f hf
  exact he.symm

namespace Valuation

noncomputable def scale (a : ℝ≥0∞) (μ : Valuation X) : Valuation X where
  mass U := a * μ U
  strict := by rw [μ.strict,mul_zero]
  modular U V := by rw [← mul_add,← mul_add,μ.modular]
  continuous := μ.continuous.comp <| ScottContinuous.of_map_sSup <|
    fun A _ _ => by rw [ENNReal.mul_sSup,sSup_image]

@[simp] theorem scale_apply (a : ℝ≥0∞) (μ : Valuation X) (U : Opens X) :
    μ.scale a U = a * μ U := rfl

@[simp] theorem scale_one (μ : Valuation X) : μ.scale 1 = μ := by
  ext U; exact one_mul _

@[simp] theorem scale_scale (μ : Valuation X) (a b : ℝ≥0∞) :
    (μ.scale b).scale a = μ.scale (a*b) := by
  ext U; exact (mul_assoc _ _ _).symm

/-- Positive finite scaling is continuous for the point topology. -/
theorem pointContinuous_scale {μ : Valuation X} (hμ : PointContinuous μ) (a : ℝ≥0∞) :
    PointContinuous (μ.scale a) := by
  letI : TopologicalSpace (Opens X) := pointTopology X
  have hm : ScottContinuous (fun x : ℝ≥0∞ => a*x) :=
    ScottContinuous.of_map_sSup (fun A _ _ => by rw [ENNReal.mul_sSup,sSup_image])
  exact ((scott_continuous_iff _).mp hm).comp hμ

noncomputable def normalizer (μ : Valuation X) : ℝ≥0∞ := max 1 (μ ⊤)

 theorem normalizer_ne_zero (μ : Valuation X) : μ.normalizer ≠ 0 :=
  ne_of_gt ((by norm_num : (0 : ℝ≥0∞) < 1).trans_le (le_max_left _ _))

 theorem normalizer_ne_top {μ : Valuation X} (hμ : μ.Finite) : μ.normalizer ≠ ⊤ := by
  exact ne_top_of_lt (max_lt (by norm_num) (lt_top_iff_ne_top.mpr hμ))

 theorem normalized_subprobability {μ : Valuation X} (hμ : μ.Finite) :
    (μ.scale μ.normalizer⁻¹).Subprobability := by
  change μ.normalizer⁻¹ * μ ⊤ ≤ 1
  calc
    _ ≤ μ.normalizer⁻¹ * μ.normalizer := mul_le_mul_right (le_max_right _ _) _
    _ = 1 := ENNReal.inv_mul_cancel μ.normalizer_ne_zero (normalizer_ne_top hμ)

 theorem unnormalize {μ : Valuation X} (hμ : μ.Finite) :
    (μ.scale μ.normalizer⁻¹).scale μ.normalizer = μ := by
  rw [scale_scale,ENNReal.mul_inv_cancel μ.normalizer_ne_zero (normalizer_ne_top hμ),scale_one]
end Valuation

 theorem integral_scale (μ : Valuation X) (a : ℝ≥0∞) (ha : a ≠ ⊤) (f : X → ℝ≥0∞) :
    integral (μ.scale a) f = a * integral μ f :=
  lintegral_const_mul' a _ ha
end PointCentralFubini
