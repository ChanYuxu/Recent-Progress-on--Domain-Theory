import CantorFubini.ValuationIntegral
import CantorFubini.SourceIntegralOrder

/-! Exact bridges between the nonnegative Choquet integral and the source's
ordinary-real strict-level-set integral. The hypotheses expose all bounds
needed for ENNReal.toReal and for restricting real thresholds to [0,1]. -/

set_option autoImplicit false
open Set Topology TopologicalSpace MeasureTheory
open scoped ENNReal
universe u
namespace CantorFubini

theorem isVLSC_ofReal {X : Type u} [TopologicalSpace X]
    {f : X → ℝ} (hf : IsRealLSC f) : IsVLSC (fun x => ENNReal.ofReal (f x)) := by
  intro a
  by_cases ha : a = ∞
  · subst a
    simp
  · convert hf a.toReal using 1
    ext x
    exact ENNReal.lt_ofReal_iff_toReal_lt ha

theorem isRealLSC_toReal_of_le_one {X : Type u} [TopologicalSpace X]
    {f : X → ℝ≥0∞} (hf : IsVLSC f) (hf1 : ∀ x, f x ≤ 1) :
    IsRealLSC (fun x => (f x).toReal) := by
  intro a
  by_cases ha : a < 0
  · have he : {x | a < (f x).toReal} = univ := by
      ext x
      simp only [mem_setOf_eq, mem_univ, iff_true]
      exact ha.trans_le ENNReal.toReal_nonneg
    rw [he]
    exact isOpen_univ
  · convert hf (ENNReal.ofReal a) using 1
    ext x
    exact (ENNReal.ofReal_lt_iff_lt_toReal (le_of_not_gt ha)
      (ne_top_of_le_ne_top ENNReal.one_ne_top (hf1 x))).symm

theorem vIntegral_le_one {X : Type u} [TopologicalSpace X]
    (μ : SubprobValuation X) {f : X → ℝ≥0∞} (hf1 : ∀ x, f x ≤ 1) :
    vIntegral μ.val f ≤ 1 := by
  calc
    vIntegral μ.val f ≤ vIntegral μ.val (fun _ => 1) := vIntegral_mono μ.val hf1
    _ = μ.val ⊤ := by rw [vIntegral_const, one_mul]
    _ ≤ 1 := μ.property

theorem ofReal_sourceIntegral {X : Type u} [TopologicalSpace X]
    (μ : SubprobValuation X) (f : X → ℝ) :
    ENNReal.ofReal (sourceIntegral μ.val f) = ∫⁻ a : ℝ in Icc (0 : ℝ) 1,
      μ.val ⟨interior {x | a < f x}, isOpen_interior⟩ := by
  change ENNReal.ofReal (∫ a : ℝ in Icc (0 : ℝ) 1, subprobLevelMass μ f a) = _
  rw [ofReal_integral_eq_lintegral_ofReal (subprobLevelMass_integrable μ f)
    (Filter.Eventually.of_forall (fun _ => ENNReal.toReal_nonneg))]
  apply lintegral_congr
  intro a
  exact ENNReal.ofReal_toReal (subprob_mass_ne_top μ _)

theorem vIntegral_ofReal_eq_sourceIntegral {X : Type u} [TopologicalSpace X]
    (μ : SubprobValuation X) (f : X → ℝ) (hf1 : ∀ x, f x ≤ 1) :
    vIntegral μ.val (fun x => ENNReal.ofReal (f x)) =
      ENNReal.ofReal (sourceIntegral μ.val f) := by
  classical
  have hlevel (a : ℝ) (ha : 0 ≤ a) :
      vLevelMass μ.val (fun x => ENNReal.ofReal (f x)) a =
        μ.val ⟨interior {x | a < f x}, isOpen_interior⟩ := by
    apply congrArg μ.val
    apply Opens.ext
    apply congrArg interior
    ext x
    exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg ha
  have hzero (a : ℝ) (ha : 1 < a) :
      vLevelMass μ.val (fun x => ENNReal.ofReal (f x)) a = 0 := by
    rw [hlevel a (by linarith)]
    have he : {x | a < f x} = ∅ := by
      ext x
      simp only [mem_setOf_eq, mem_empty_iff_false, iff_false]
      exact not_lt_of_ge ((hf1 x).trans ha.le)
    simp only [he, interior_empty]
    exact μ.val.strict
  calc
    vIntegral μ.val (fun x => ENNReal.ofReal (f x)) =
        ∫⁻ a : ℝ in Ioc (0 : ℝ) 1,
          vLevelMass μ.val (fun x => ENNReal.ofReal (f x)) a := by
      rw [vIntegral, ← lintegral_indicator measurableSet_Ioi,
        ← lintegral_indicator measurableSet_Ioc]
      apply lintegral_congr
      intro a
      by_cases ha0 : 0 < a
      · by_cases ha1 : a ≤ 1
        · simp [ha0, ha1]
        · simp [ha0, ha1, hzero a (lt_of_not_ge ha1)]
      · simp [ha0]
    _ = ∫⁻ a : ℝ in Icc (0 : ℝ) 1,
        vLevelMass μ.val (fun x => ENNReal.ofReal (f x)) a :=
      setLIntegral_congr Ioc_ae_eq_Icc
    _ = ∫⁻ a : ℝ in Icc (0 : ℝ) 1,
        μ.val ⟨interior {x | a < f x}, isOpen_interior⟩ :=
      setLIntegral_congr_fun measurableSet_Icc (fun a ha => hlevel a ha.1)
    _ = ENNReal.ofReal (sourceIntegral μ.val f) := (ofReal_sourceIntegral μ f).symm

theorem sourceIntegral_eq_vIntegral_toReal {X : Type u} [TopologicalSpace X]
    (μ : SubprobValuation X) (f : X → ℝ) (hf1 : ∀ x, f x ≤ 1) :
    sourceIntegral μ.val f =
      (vIntegral μ.val (fun x => ENNReal.ofReal (f x))).toReal := by
  rw [vIntegral_ofReal_eq_sourceIntegral μ f hf1,
    ENNReal.toReal_ofReal (sourceIntegral_nonneg μ.val f)]

theorem sourceIntegral_toReal {X : Type u} [TopologicalSpace X]
    (μ : SubprobValuation X) (f : X → ℝ≥0∞) (hf1 : ∀ x, f x ≤ 1) :
    sourceIntegral μ.val (fun x => (f x).toReal) = (vIntegral μ.val f).toReal := by
  have hreal1 (x : X) : (f x).toReal ≤ 1 :=
    ENNReal.toReal_le_of_le_ofReal (by norm_num) (by simpa using hf1 x)
  rw [sourceIntegral_eq_vIntegral_toReal μ _ hreal1]
  congr 1
  congr 1
  funext x
  exact ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.one_ne_top (hf1 x))

end CantorFubini
