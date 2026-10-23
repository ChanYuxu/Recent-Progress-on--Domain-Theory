import CantorFubini.Subprobability

/-! Order, normalization and change of variables for the manuscript's bounded
ordinary-real strict-level-set integral. These facts are for actual arbitrary
subprobability valuations; no measure extension is assumed. -/

set_option autoImplicit false
open Set Topology TopologicalSpace MeasureTheory
open scoped ENNReal
universe u v
namespace CantorFubini

noncomputable def subprobLevelMass {X : Type u} [TopologicalSpace X]
    (μ : SubprobValuation X) (f : X → ℝ) (a : ℝ) : ℝ :=
  subprobRealMass μ ⟨interior {x | a < f x}, isOpen_interior⟩

theorem subprobLevelMass_antitone {X : Type u} [TopologicalSpace X]
    (μ : SubprobValuation X) (f : X → ℝ) : Antitone (subprobLevelMass μ f) := by
  intro a b hab
  apply subprobRealMass_mono μ
  exact interior_mono (fun _ hx => lt_of_le_of_lt hab hx)

theorem subprobLevelMass_integrable {X : Type u} [TopologicalSpace X]
    (μ : SubprobValuation X) (f : X → ℝ) :
    IntegrableOn (subprobLevelMass μ f) (Icc (0 : ℝ) 1) := by
  have hmeas : AEStronglyMeasurable (subprobLevelMass μ f)
      (volume.restrict (Icc (0 : ℝ) 1)) :=
    (subprobLevelMass_antitone μ f).measurable.aestronglyMeasurable
  have hconst : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Icc (0 : ℝ) 1) :=
    integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  apply hconst.mono' hmeas
  exact Filter.Eventually.of_forall (fun a => by
    have h := subprobRealMass_mem_unit μ ⟨interior {x | a < f x}, isOpen_interior⟩
    change |subprobRealMass μ ⟨interior {x | a < f x}, isOpen_interior⟩| ≤ 1
    rw [abs_of_nonneg h.1]
    exact h.2)

theorem sourceIntegral_nonneg {X : Type u} [TopologicalSpace X]
    (μ : Valuation X) (f : X → ℝ) : 0 ≤ sourceIntegral μ f :=
  integral_nonneg (fun _ => ENNReal.toReal_nonneg)

theorem sourceIntegral_le_one {X : Type u} [TopologicalSpace X]
    (μ : SubprobValuation X) (f : X → ℝ) : sourceIntegral μ.val f ≤ 1 := by
  have hconst : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Icc (0 : ℝ) 1) :=
    integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  have h := integral_mono (subprobLevelMass_integrable μ f) hconst
    (fun a => (subprobRealMass_mem_unit μ
      ⟨interior {x | a < f x}, isOpen_interior⟩).2)
  simpa [sourceIntegral, subprobLevelMass, subprobRealMass, Real.volume_Icc] using h

theorem sourceIntegral_mono {X : Type u} [TopologicalSpace X]
    (μ : SubprobValuation X) {f g : X → ℝ} (hfg : ∀ x, f x ≤ g x) :
    sourceIntegral μ.val f ≤ sourceIntegral μ.val g := by
  apply integral_mono (subprobLevelMass_integrable μ f)
    (subprobLevelMass_integrable μ g)
  intro a
  exact subprobRealMass_mono μ
    (interior_mono (fun x hx => lt_of_lt_of_le hx (hfg x)))

theorem IsRealLSC.comp_continuous {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] {f : Y → ℝ}
    (hf : IsRealLSC f) (g : X → Y) (hg : Continuous g) :
    IsRealLSC (fun x => f (g x)) :=
  fun a => (hf a).preimage hg

theorem sourceIntegral_push {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y]
    (μ : Valuation X) (g : X → Y) (hg : Continuous g)
    (f : Y → ℝ) (hf : IsRealLSC f) :
    sourceIntegral (μ.push g hg) f = sourceIntegral μ (fun x => f (g x)) := by
  rw [sourceIntegral_eq_strictLevels _ _ hf,
    sourceIntegral_eq_strictLevels _ _ (hf.comp_continuous g hg)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun _ => rfl)

theorem sourceIntegral_const {X : Type u} [TopologicalSpace X]
    (μ : SubprobValuation X) (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    sourceIntegral μ.val (fun _ => c) = (μ.val ⊤).toReal * c := by
  classical
  have hf : IsRealLSC (fun _ : X => c) := by
    intro a
    by_cases h : a < c <;> simp [h]
  rw [sourceIntegral_eq_strictLevels _ _ hf]
  have hlevels (a : ℝ) :
      (μ.val ⟨{x : X | a < c}, hf a⟩).toReal =
        if a < c then (μ.val ⊤).toReal else 0 := by
    by_cases ha : a < c
    · have he : (⟨{x : X | a < c}, hf a⟩ : Opens X) = ⊤ := by
        ext x; simp [ha]
      rw [he, if_pos ha]
    · have he : (⟨{x : X | a < c}, hf a⟩ : Opens X) = ⊥ := by
        ext x; simp [ha]
      rw [he, μ.val.strict, if_neg ha, ENNReal.toReal_zero]
  simp_rw [hlevels]
  exact real_integral_constant_cutoff _ _ hc0 hc1

end CantorFubini
