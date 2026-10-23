import ZFCFubini.PaperIntegral

/-! Genuine change of variables for the already defined integrals.
Every strict level is the literal inverse image under the specified map.
No functional law, Fubini theorem or categorical conclusion is assumed. -/

set_option autoImplicit false
open Set TopologicalSpace MeasureTheory
open scoped ENNReal
universe u v
namespace ZFCFubini

theorem IsLSC.comp {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    {f : Y → ℝ≥0∞} (hf : IsLSC f) (g : X → Y) (hg : Continuous g) :
    IsLSC (fun x => f (g x)) := fun r => (hf r).preimage hg

theorem IsRealLSC.comp {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    {f : Y → ℝ} (hf : IsRealLSC f) (g : X → Y) (hg : Continuous g) :
    IsRealLSC (fun x => f (g x)) := fun r => (hf r).preimage hg

theorem choquetIntegral_push {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y]
    (μ : Valuation X) (g : X → Y) (hg : Continuous g)
    (f : Y → ℝ≥0∞) (hf : IsLSC f) :
    choquetIntegral (μ.push g hg) f = choquetIntegral μ (fun x => f (g x)) := by
  rw [choquetIntegral_eq_layerCake _ _ hf,
    choquetIntegral_eq_layerCake _ _ (hf.comp g hg)]
  apply lintegral_congr
  intro a
  rfl

noncomputable def probabilityPush {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y]
    (μ : ProbabilityValuation X) (g : X → Y) (hg : Continuous g) : ProbabilityValuation Y :=
  ⟨μ.val.push g hg, by change μ.val ⊤ = 1; exact μ.property⟩

theorem probabilityPush_realMass {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y]
    (μ : ProbabilityValuation X) (g : X → Y) (hg : Continuous g) (U : Opens Y) :
    realMass (probabilityPush μ g hg) U =
      realMass μ ⟨g ⁻¹' (U : Set Y), U.isOpen.preimage hg⟩ := rfl

theorem paperIntegral_push {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y]
    (μ : ProbabilityValuation X) (g : X → Y) (hg : Continuous g)
    (f : Y → ℝ) (hf : IsRealLSC f) :
    paperIntegral (probabilityPush μ g hg) f = paperIntegral μ (fun x => f (g x)) := by
  rw [paperIntegral_eq_strictLevels _ _ hf,
    paperIntegral_eq_strictLevels _ _ (hf.comp g hg)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun _ => rfl)

end ZFCFubini
