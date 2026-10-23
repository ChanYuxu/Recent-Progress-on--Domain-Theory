import ZFCFubini.ValuationOrder
import Mathlib.Topology.Semicontinuity.Lindelof
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-! Basic laws for the actual strict-level Choquet integral from Foundations.
No representation of a valuation by a measure is assumed. -/

set_option autoImplicit false
open Set Topology TopologicalSpace MeasureTheory
open scoped ENNReal NNReal
universe u v w
namespace ZFCFubini

variable {X : Type u} [TopologicalSpace X]

theorem isLSC_iff_lowerSemicontinuous {f : X → ℝ≥0∞} :
    IsLSC f ↔ LowerSemicontinuous f :=
  lowerSemicontinuous_iff_isOpen_preimage.symm

theorem IsLSC.lowerSemicontinuous {f : X → ℝ≥0∞} (hf : IsLSC f) :
    LowerSemicontinuous f := isLSC_iff_lowerSemicontinuous.mp hf

theorem IsLSC.const (c : ℝ≥0∞) : IsLSC (fun _ : X => c) :=
  isLSC_iff_lowerSemicontinuous.mpr lowerSemicontinuous_const

theorem IsLSC.add {f g : X → ℝ≥0∞} (hf : IsLSC f) (hg : IsLSC g) :
    IsLSC (f + g) :=
  isLSC_iff_lowerSemicontinuous.mpr (hf.lowerSemicontinuous.add hg.lowerSemicontinuous)

theorem IsLSC.sup {f g : X → ℝ≥0∞} (hf : IsLSC f) (hg : IsLSC g) : IsLSC (f ⊔ g) :=
  isLSC_iff_lowerSemicontinuous.mpr (hf.lowerSemicontinuous.sup hg.lowerSemicontinuous)

theorem IsLSC.inf {f g : X → ℝ≥0∞} (hf : IsLSC f) (hg : IsLSC g) : IsLSC (f ⊓ g) :=
  isLSC_iff_lowerSemicontinuous.mpr (hf.lowerSemicontinuous.inf hg.lowerSemicontinuous)

theorem IsLSC.iSup {ι : Type v} (f : ι → X → ℝ≥0∞) (hf : ∀ i, IsLSC (f i)) :
    IsLSC (fun x => ⨆ i, f i x) := by
  intro r
  have he : {x | r < ⨆ i, f i x} = ⋃ i, {x | r < f i x} := by
    ext x
    simp only [mem_setOf_eq, mem_iUnion, lt_iSup_iff]
  rw [he]
  exact isOpen_iUnion (fun i => hf i r)

theorem IsLSC.indicator (U : Opens X) (c : ℝ≥0∞) :
    IsLSC ((U : Set X).indicator (fun _ => c)) :=
  isLSC_iff_lowerSemicontinuous.mpr
    (U.isOpen.lowerSemicontinuous_indicator (zero_le c))

/-- Interior is part of the existing totalization, not a change of integral. -/
noncomputable def integralLevel (f : X → ℝ≥0∞) (a : ℝ) : Opens X :=
  ⟨interior {x | ENNReal.ofReal a < f x}, isOpen_interior⟩

noncomputable def integralProfile (μ : Valuation X) (f : X → ℝ≥0∞) (a : ℝ) : ℝ≥0∞ :=
  μ (integralLevel f a)

theorem choquetIntegral_eq_profile (μ : Valuation X) (f : X → ℝ≥0∞) :
    choquetIntegral μ f = ∫⁻ a : ℝ in Ici 0, integralProfile μ f a := rfl

theorem integralLevel_of_isLSC (f : X → ℝ≥0∞) (hf : IsLSC f) (a : ℝ) :
    integralLevel f a = ⟨{x | ENNReal.ofReal a < f x}, hf _⟩ :=
  Opens.ext (hf _).interior_eq

theorem integralLevel_mono {f g : X → ℝ≥0∞} (hfg : f ≤ g) (a : ℝ) :
    integralLevel f a ≤ integralLevel g a :=
  interior_mono (fun x hx => hx.trans_le (hfg x))

theorem integralProfile_antitone (μ : Valuation X) (f : X → ℝ≥0∞) :
    Antitone (integralProfile μ f) := by
  intro a b hab
  exact μ.mono (interior_mono (fun x hx => (ENNReal.ofReal_le_ofReal hab).trans_lt hx))

theorem choquetIntegral_mono (μ : Valuation X) {f g : X → ℝ≥0∞} (hfg : f ≤ g) :
    choquetIntegral μ f ≤ choquetIntegral μ g :=
  lintegral_mono (fun a => μ.mono (integralLevel_mono hfg a))

@[simp] theorem choquetIntegral_zero (μ : Valuation X) :
    choquetIntegral μ (fun _ => 0) = 0 := by
  unfold choquetIntegral
  have he (a : ℝ) :
      (⟨interior {x : X | ENNReal.ofReal a < 0}, isOpen_interior⟩ : Opens X) = ⊥ := by
    ext x
    simp
  simp only [he, μ.strict, lintegral_zero]

/-- Finite open indicators are computed directly on the real threshold axis. -/
theorem choquetIntegral_indicator_nnreal (μ : Valuation X) (U : Opens X) (c : ℝ≥0) :
    choquetIntegral μ ((U : Set X).indicator (fun _ => (c : ℝ≥0∞))) =
      (c : ℝ≥0∞) * μ U := by
  rw [choquetIntegral_eq_layerCake _ _ (IsLSC.indicator U c)]
  have he : (fun a : ℝ => μ
      ⟨{x | ENNReal.ofReal a < (U : Set X).indicator (fun _ => (c : ℝ≥0∞)) x},
        IsLSC.indicator U c _⟩) =ᵐ[volume.restrict (Ici (0 : ℝ))]
      (Iio (c : ℝ)).indicator (fun _ => μ U) := by
    filter_upwards [ae_restrict_mem measurableSet_Ici] with a ha
    by_cases hac : a < (c : ℝ)
    · rw [Set.indicator_of_mem (show a ∈ Iio (c : ℝ) from hac)]
      congr 1
      apply Opens.ext
      ext x
      change (ENNReal.ofReal a < (U : Set X).indicator (fun _ => (c : ℝ≥0∞)) x) ↔
        x ∈ (U : Set X)
      by_cases hx : x ∈ (U : Set X)
      · simp only [Set.indicator_of_mem hx, mem_setOf_eq]
        exact iff_of_true ((ENNReal.ofReal_lt_coe_iff ha).2 hac) hx
      · simp only [Set.indicator_of_notMem hx, mem_setOf_eq, not_lt_zero, hx]
    · rw [Set.indicator_of_notMem (show a ∉ Iio (c : ℝ) from hac)]
      have hlevel : (⟨{x | ENNReal.ofReal a <
          (U : Set X).indicator (fun _ => (c : ℝ≥0∞)) x},
          IsLSC.indicator U c _⟩ : Opens X) = ⊥ := by
        ext x
        change (ENNReal.ofReal a < (U : Set X).indicator (fun _ => (c : ℝ≥0∞)) x) ↔ False
        by_cases hx : x ∈ (U : Set X)
        · simp only [Set.indicator_of_mem hx, mem_setOf_eq, Opens.mem_bot, iff_false]
          exact fun h => hac ((ENNReal.ofReal_lt_coe_iff ha).1 h)
        · simp [hx]
      rw [hlevel, μ.strict]
  rw [lintegral_congr_ae he, setLIntegral_indicator measurableSet_Iio,
    setLIntegral_const]
  have hset : Iio (c : ℝ) ∩ Ici (0 : ℝ) = Ico 0 (c : ℝ) := by
    ext a
    simp only [mem_inter_iff, mem_Iio, mem_Ici, mem_Ico, and_comm]
  rw [hset, Real.volume_Ico, sub_zero, ENNReal.ofReal_coe_nnreal, mul_comm]

theorem choquetIntegral_const_nnreal (μ : Valuation X) (c : ℝ≥0) :
    choquetIntegral μ (fun _ => (c : ℝ≥0∞)) = (c : ℝ≥0∞) * μ ⊤ := by
  simpa using choquetIntegral_indicator_nnreal μ ⊤ c

theorem choquetIntegral_le_one (μ : Valuation X) (hμ : μ.Subprobability)
    {f : X → ℝ≥0∞} (hf1 : ∀ x, f x ≤ 1) : choquetIntegral μ f ≤ 1 := by
  calc
    choquetIntegral μ f ≤ choquetIntegral μ (fun _ => (1 : ℝ≥0∞)) :=
      choquetIntegral_mono μ hf1
    _ = μ ⊤ := by simpa using choquetIntegral_const_nnreal μ 1
    _ ≤ 1 := hμ

end ZFCFubini
