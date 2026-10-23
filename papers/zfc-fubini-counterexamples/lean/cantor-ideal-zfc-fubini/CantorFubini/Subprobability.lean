import CantorFubini.Corollaries

/-! Subprobability bridges and indicator integration. Adapted from this
project's PaperIntegral.lean SHA256 3c172a0e2ec506a80df33820b44ddc2ef6bdf4763d3dd4c609a56e087e8ff63b
and PaperIntegralCalculations.lean SHA256 94a960ba4877a3ca6425427a3651b2a547cf347322117d936ed845e7b0cdeb88.
Only normalization is omitted; finite mass, modularity and full directed
continuity retain proved ordinary-real/unit-interval bridges. -/
set_option autoImplicit false
open Set Topology TopologicalSpace MeasureTheory
open scoped ENNReal
universe u
namespace CantorFubini
noncomputable def subprobRealMass {X : Type u} [TopologicalSpace X]
    (μ : SubprobValuation X) (U : Opens X) : ℝ := (μ.val U).toReal

theorem subprobRealMass_mem_unit {X : Type u} [TopologicalSpace X]
    (μ : SubprobValuation X) (U : Opens X) : subprobRealMass μ U ∈ Icc (0 : ℝ) 1 := by
  refine ⟨ENNReal.toReal_nonneg, ?_⟩
  apply ENNReal.toReal_le_of_le_ofReal (by norm_num)
  simpa using μ.property.mass_le_one U

@[simp] theorem subprobRealMass_empty {X : Type u} [TopologicalSpace X]
    (μ : SubprobValuation X) : subprobRealMass μ ⊥ = 0 := by
  simp [subprobRealMass, μ.val.strict]

theorem subprob_mass_ne_top {X : Type u} [TopologicalSpace X]
    (μ : SubprobValuation X) (U : Opens X) : μ.val U ≠ ∞ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (μ.property.mass_le_one U)

theorem subprobRealMass_mono {X : Type u} [TopologicalSpace X]
    (μ : SubprobValuation X) : Monotone (subprobRealMass μ) := by
  intro U V hUV
  exact ENNReal.toReal_mono (subprob_mass_ne_top μ V) (μ.val.mono hUV)

theorem subprobRealMass_modular {X : Type u} [TopologicalSpace X]
    (μ : SubprobValuation X) (U V : Opens X) :
    subprobRealMass μ U + subprobRealMass μ V = subprobRealMass μ (U ⊔ V) + subprobRealMass μ (U ⊓ V) := by
  simpa only [subprobRealMass, ENNReal.toReal_add (subprob_mass_ne_top μ U)
    (subprob_mass_ne_top μ V), ENNReal.toReal_add (subprob_mass_ne_top μ (U ⊔ V))
    (subprob_mass_ne_top μ (U ⊓ V))] using congrArg ENNReal.toReal (μ.val.modular U V)

theorem subprobRealMass_scottContinuous {X : Type u} [TopologicalSpace X]
    (μ : SubprobValuation X) : ScottContinuous (subprobRealMass μ) := by
  intro D hn hd p hp
  refine ⟨?_, ?_⟩
  · rintro b ⟨U, hU, rfl⟩
    exact subprobRealMass_mono μ (hp.1 hU)
  · intro z hz
    have hn' : D.Nonempty := hn
    obtain ⟨U₀, hU₀⟩ := hn
    have hz0 : 0 ≤ z := (subprobRealMass_mem_unit μ U₀).1.trans (hz (mem_image_of_mem _ hU₀))
    apply ENNReal.toReal_le_of_le_ofReal hz0
    apply (μ.val.continuous hn' hd hp).2
    rintro b ⟨U, hU, rfl⟩
    exact (ENNReal.le_ofReal_iff_toReal_le (subprob_mass_ne_top μ U) hz0).mpr
      (hz (mem_image_of_mem _ hU))

noncomputable def subprobRealMassUnit {X : Type u} [TopologicalSpace X]
    (μ : SubprobValuation X) (U : Opens X) : UnitInterval :=
  ⟨subprobRealMass μ U, subprobRealMass_mem_unit μ U⟩

theorem subprobRealMassUnit_scottContinuous {X : Type u} [TopologicalSpace X]
    (μ : SubprobValuation X) : ScottContinuous (subprobRealMassUnit μ) := by
  intro D hn hd p hp
  have hreal := subprobRealMass_scottContinuous μ hn hd hp
  refine ⟨?_, ?_⟩
  · rintro b ⟨U, hU, rfl⟩
    exact hreal.1 (mem_image_of_mem _ hU)
  · intro z hz
    apply hreal.2
    rintro b ⟨U, hU, rfl⟩
    exact hz (mem_image_of_mem _ hU)

theorem sourceIntegral_realIndicator {X : Type u} [TopologicalSpace X]
    (μ : SubprobValuation X) (U : Opens X) :
    sourceIntegral μ.val (realIndicator U) = subprobRealMass μ U := by
  classical
  rw [sourceIntegral_eq_strictLevels μ.val _ (realIndicator_isRealLSC U)]
  have hcut (a : ℝ) (ha : 0 ≤ a) :
      subprobRealMass μ ⟨{x | a < realIndicator U x}, realIndicator_isRealLSC U a⟩ =
        if a < 1 then subprobRealMass μ U else 0 := by
    by_cases h1 : a < 1
    · have he : (⟨{x | a < realIndicator U x}, realIndicator_isRealLSC U a⟩ : Opens X) = U := by
        ext x
        by_cases hx : x ∈ U <;> simp [realIndicator, hx, h1, not_lt.mpr ha]
      rw [he, if_pos h1]
    · have he : (⟨{x | a < realIndicator U x}, realIndicator_isRealLSC U a⟩ : Opens X) = ⊥ := by
        ext x
        by_cases hx : x ∈ U <;> simp [realIndicator, hx, h1, not_lt.mpr ha]
      rw [he, subprobRealMass_empty, if_neg h1]
  calc
    (∫ a : ℝ in Icc (0 : ℝ) 1, subprobRealMass μ
        ⟨{x | a < realIndicator U x}, realIndicator_isRealLSC U a⟩) =
        ∫ a : ℝ in Icc (0 : ℝ) 1, if a < 1 then subprobRealMass μ U else 0 :=
      setIntegral_congr_fun measurableSet_Icc (fun a ha => hcut a ha.1)
    _ = subprobRealMass μ U := by
      simpa using real_integral_constant_cutoff (subprobRealMass μ U) 1 (by norm_num) le_rfl

end CantorFubini
