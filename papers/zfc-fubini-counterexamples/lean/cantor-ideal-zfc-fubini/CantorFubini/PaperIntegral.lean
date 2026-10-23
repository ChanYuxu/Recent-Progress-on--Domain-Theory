/- Adapted from ZFC_Fubini_Lean/ZFCFubini/PaperIntegral.lean; original SHA256 3562e9df1cf74bb00b178f175aa60ea8a3e5eb34d3351f616ebb96790a6fe816. Current source is formalized-manuscript.tex. -/
import CantorFubini.Foundations
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
The source integral is an ordinary REAL strict-level-set integral on [0,1].
The interior only totalizes the definition outside its specified LSC domain;
`paperIntegral_eq_strictLevels` proves it disappears on every source input.
Finite ENNReal mass is explicitly connected to [0,1]-valued real mass below.
No unproved equivalence to an unrelated integral is assumed.
-/

set_option autoImplicit false
open Set Topology TopologicalSpace MeasureTheory
open scoped ENNReal
universe u v
namespace CantorFubini

abbrev UnitInterval := Set.Icc (0 : ℝ) 1

def unitZero : UnitInterval := ⟨0, by constructor <;> norm_num⟩
def unitOne : UnitInterval := ⟨1, by constructor <;> norm_num⟩

def IsRealLSC {X : Type u} [TopologicalSpace X] (f : X → ℝ) : Prop :=
  ∀ a : ℝ, IsOpen {x | a < f x}

abbrev ProbabilityValuation (X : Type u) [TopologicalSpace X] :=
  {μ : Valuation X // μ.Probability}

noncomputable def realMass {X : Type u} [TopologicalSpace X]
    (μ : ProbabilityValuation X) (U : Opens X) : ℝ := (μ.val U).toReal

theorem realMass_mem_unit {X : Type u} [TopologicalSpace X]
    (μ : ProbabilityValuation X) (U : Opens X) : realMass μ U ∈ Icc (0 : ℝ) 1 := by
  refine ⟨ENNReal.toReal_nonneg, ?_⟩
  apply ENNReal.toReal_le_of_le_ofReal (by norm_num)
  simpa using μ.property.subprobability.mass_le_one U

@[simp] theorem realMass_empty {X : Type u} [TopologicalSpace X]
    (μ : ProbabilityValuation X) : realMass μ ⊥ = 0 := by
  simp [realMass, μ.val.strict]

@[simp] theorem realMass_univ {X : Type u} [TopologicalSpace X]
    (μ : ProbabilityValuation X) : realMass μ ⊤ = 1 := by
  change (μ.val ⊤).toReal = 1
  rw [show μ.val ⊤ = 1 from μ.property]
  simp

noncomputable def paperIntegral {X : Type u} [TopologicalSpace X]
    (μ : ProbabilityValuation X) (f : X → ℝ) : ℝ :=
  ∫ a : ℝ in Icc (0 : ℝ) 1,
    realMass μ ⟨interior {x | a < f x}, isOpen_interior⟩

theorem paperIntegral_eq_strictLevels {X : Type u} [TopologicalSpace X]
    (μ : ProbabilityValuation X) (f : X → ℝ) (hf : IsRealLSC f) :
    paperIntegral μ f = ∫ a : ℝ in Icc (0 : ℝ) 1,
      realMass μ ⟨{x | a < f x}, hf a⟩ := by
  unfold paperIntegral
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro a
  have he : (⟨interior {x | a < f x}, isOpen_interior⟩ : Opens X) =
      ⟨{x | a < f x}, hf a⟩ := Opens.ext (hf a).interior_eq
  exact congrArg (realMass μ) he

theorem probability_mass_ne_top {X : Type u} [TopologicalSpace X]
    (μ : ProbabilityValuation X) (U : Opens X) : μ.val U ≠ ∞ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (μ.property.subprobability.mass_le_one U)

theorem realMass_mono {X : Type u} [TopologicalSpace X]
    (μ : ProbabilityValuation X) : Monotone (realMass μ) := by
  intro U V hUV
  exact ENNReal.toReal_mono (probability_mass_ne_top μ V) (μ.val.mono hUV)

theorem realMass_modular {X : Type u} [TopologicalSpace X]
    (μ : ProbabilityValuation X) (U V : Opens X) :
    realMass μ U + realMass μ V = realMass μ (U ⊔ V) + realMass μ (U ⊓ V) := by
  simpa only [realMass, ENNReal.toReal_add (probability_mass_ne_top μ U)
    (probability_mass_ne_top μ V), ENNReal.toReal_add (probability_mass_ne_top μ (U ⊔ V))
    (probability_mass_ne_top μ (U ⊓ V))] using congrArg ENNReal.toReal (μ.val.modular U V)

theorem realMass_scottContinuous {X : Type u} [TopologicalSpace X]
    (μ : ProbabilityValuation X) : ScottContinuous (realMass μ) := by
  intro D hn hd p hp
  refine ⟨?_, ?_⟩
  · rintro b ⟨U, hU, rfl⟩
    exact realMass_mono μ (hp.1 hU)
  · intro z hz
    have hn' : D.Nonempty := hn
    obtain ⟨U₀, hU₀⟩ := hn
    have hz0 : 0 ≤ z := (realMass_mem_unit μ U₀).1.trans (hz (mem_image_of_mem _ hU₀))
    apply ENNReal.toReal_le_of_le_ofReal hz0
    apply (μ.val.continuous hn' hd hp).2
    rintro b ⟨U, hU, rfl⟩
    exact (ENNReal.le_ofReal_iff_toReal_le (probability_mass_ne_top μ U) hz0).mpr
      (hz (mem_image_of_mem _ hU))

noncomputable def realMassUnit {X : Type u} [TopologicalSpace X]
    (μ : ProbabilityValuation X) (U : Opens X) : UnitInterval :=
  ⟨realMass μ U, realMass_mem_unit μ U⟩

theorem realMassUnit_scottContinuous {X : Type u} [TopologicalSpace X]
    (μ : ProbabilityValuation X) : ScottContinuous (realMassUnit μ) := by
  intro D hn hd p hp
  have hreal := realMass_scottContinuous μ hn hd hp
  refine ⟨?_, ?_⟩
  · rintro b ⟨U, hU, rfl⟩
    exact hreal.1 (mem_image_of_mem _ hU)
  · intro z hz
    apply hreal.2
    rintro b ⟨U, hU, rfl⟩
    exact hz (mem_image_of_mem _ hU)

noncomputable def levelMass {X : Type u} [TopologicalSpace X]
    (μ : ProbabilityValuation X) (f : X → ℝ) (a : ℝ) : ℝ :=
  realMass μ ⟨interior {x | a < f x}, isOpen_interior⟩

theorem levelMass_antitone {X : Type u} [TopologicalSpace X]
    (μ : ProbabilityValuation X) (f : X → ℝ) : Antitone (levelMass μ f) := by
  intro a b hab
  apply realMass_mono μ
  exact interior_mono (fun _ hx => lt_of_le_of_lt hab hx)

theorem levelMass_integrable {X : Type u} [TopologicalSpace X]
    (μ : ProbabilityValuation X) (f : X → ℝ) :
    IntegrableOn (levelMass μ f) (Icc (0 : ℝ) 1) := by
  have hmeas : AEStronglyMeasurable (levelMass μ f)
      (volume.restrict (Icc (0 : ℝ) 1)) :=
    (levelMass_antitone μ f).measurable.aestronglyMeasurable
  have hconst : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Icc (0 : ℝ) 1) :=
    integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  apply hconst.mono' hmeas
  exact Filter.Eventually.of_forall (fun a => by
    have h := realMass_mem_unit μ ⟨interior {x | a < f x}, isOpen_interior⟩
    change |realMass μ ⟨interior {x | a < f x}, isOpen_interior⟩| ≤ 1
    rw [abs_of_nonneg h.1]
    exact h.2)

theorem unit_coe_scottContinuous : ScottContinuous (fun x : UnitInterval => x.val) := by
  intro D hn hd x hx
  refine ⟨?_, ?_⟩
  · rintro y ⟨d, hdD, rfl⟩
    exact hx.1 hdD
  · intro b hb
    by_cases h1 : 1 ≤ b
    · exact x.property.2.trans h1
    have hb1 : b ≤ 1 := le_of_lt (lt_of_not_ge h1)
    by_cases h0 : 0 ≤ b
    · exact hx.2 (show (⟨b, h0, hb1⟩ : UnitInterval) ∈ upperBounds D from
        fun d hdD => hb (mem_image_of_mem _ hdD))
    · obtain ⟨d, hdD⟩ := hn
      exact False.elim (h0 (d.property.1.trans (hb (mem_image_of_mem _ hdD))))

theorem scott_real_Ioi_open (r : ℝ) :
    IsOpen {x : WithScott ℝ | r < WithScott.ofScott x} := by
  have hc : IsClosed (Iic (WithScott.toScott r)) := isClosed_Iic
  convert hc.isOpen_compl using 1
  ext x
  change (r < (WithScott.ofScott x : ℝ)) ↔ ¬ (WithScott.ofScott x : ℝ) ≤ r
  exact lt_iff_not_ge

theorem scott_isRealLSC {P : Type u} [PartialOrder P] {f : P → ℝ}
    (hf : ScottContinuous f) : IsRealLSC (fun x : WithScott P => f (WithScott.ofScott x)) :=
  fun r => (scott_real_Ioi_open r).preimage ((scott_continuous_iff f).mp hf)

theorem unit_scott_isRealLSC {P : Type u} [PartialOrder P] {f : P → UnitInterval}
    (hf : ScottContinuous f) :
    IsRealLSC (fun x : WithScott P => (f (WithScott.ofScott x)).val) :=
  scott_isRealLSC (hf.comp unit_coe_scottContinuous)

end CantorFubini
