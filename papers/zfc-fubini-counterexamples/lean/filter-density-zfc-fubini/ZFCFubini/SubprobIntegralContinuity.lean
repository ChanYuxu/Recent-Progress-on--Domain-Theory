import ZFCFubini.SubprobIntegralBridge
import ZFCFubini.ValuationIntegralMCT

/-!
The real inner integral in the centrality statement is itself Scott-continuous.
This rules out relying on an interior totalization of a non-LSC outer input.
Every partner is an arbitrary dcpo-order type in its own universe; no ordinary
product topology or countable directed-continuity restriction is substituted.
-/

set_option autoImplicit false
open Set Topology TopologicalSpace MeasureTheory
open scoped ENNReal
universe u v

namespace ZFCFubini

theorem scottContinuous_toReal_of_le_one
    {P : Type u} [Preorder P] {f : P → ℝ≥0∞} (hf : ScottContinuous f)
    (hf1 : ∀ p, f p ≤ 1) : ScottContinuous (fun p => (f p).toReal) := by
  have hfinite (p : P) : f p ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (hf1 p)
  intro D hn hd p hp
  have hlu := hf hn hd hp
  constructor
  · rintro b ⟨d, hdD, rfl⟩
    exact ENNReal.toReal_mono (hfinite p) (hlu.1 (mem_image_of_mem _ hdD))
  · intro z hz
    obtain ⟨d, hdD⟩ := hn
    have hz0 : 0 ≤ z := ENNReal.toReal_nonneg.trans (hz (mem_image_of_mem _ hdD))
    apply ENNReal.toReal_le_of_le_ofReal hz0
    apply hlu.2
    rintro b ⟨a, haD, rfl⟩
    exact (ENNReal.le_ofReal_iff_toReal_le (hfinite a) hz0).mpr
      (hz (mem_image_of_mem _ haD))

theorem subprobPaperIntegral_section_scottContinuous
    {P : Type u} {Q : Type v} [PartialOrder P] [PartialOrder Q]
    (ν : SubprobValuation (WithScott Q)) (f : P × Q → UnitInterval)
    (hf : ScottContinuous f) :
    ScottContinuous (fun p => subprobPaperIntegral ν
      (fun q => (f (p, WithScott.ofScott q)).val)) := by
  let g : P → WithScott Q → ℝ≥0∞ :=
    fun p q => ENNReal.ofReal (f (p, WithScott.ofScott q)).val
  have hglsc (p : P) : IsLSC (g p) :=
    scott_isLSC ((((ScottContinuous.const p).prodMk ScottContinuous.id).comp hf).comp
      (unit_coe_scottContinuous.comp ofReal_scottContinuous))
  have hgsc (q : WithScott Q) : ScottContinuous (fun p => g p q) :=
    (((ScottContinuous.id.prodMk (ScottContinuous.const (WithScott.ofScott q))).comp hf).comp
      unit_coe_scottContinuous).comp ofReal_scottContinuous
  have hi := choquetIntegral_scottContinuous_param ν.val g hglsc hgsc
  have hi1 (p : P) : choquetIntegral ν.val (g p) ≤ 1 := by
    apply choquetIntegral_le_one ν.val ν.property
    intro q
    simpa only [g, ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal (f _).property.2
  have hir := scottContinuous_toReal_of_le_one hi hi1
  convert hir using 1
  funext p
  rw [choquetIntegral_ofReal_eq_subprobPaperIntegral ν _ (fun q => (f _).property.2),
    ENNReal.toReal_ofReal (subprobPaperIntegral_nonneg ν _)]

theorem subprobPaperIntegral_section_isRealLSC
    {P : Type u} {Q : Type v} [PartialOrder P] [PartialOrder Q]
    (ν : SubprobValuation (WithScott Q)) (f : P × Q → UnitInterval)
    (hf : ScottContinuous f) :
    IsRealLSC (fun p : WithScott P => subprobPaperIntegral ν
      (fun q => (f (WithScott.ofScott p, WithScott.ofScott q)).val)) :=
  scott_isRealLSC (subprobPaperIntegral_section_scottContinuous ν f hf)

end ZFCFubini
