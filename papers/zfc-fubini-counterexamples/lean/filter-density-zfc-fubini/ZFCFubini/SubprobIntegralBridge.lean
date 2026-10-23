import ZFCFubini.NNIntegralCalculations
import ZFCFubini.PaperIntegralCalculations

/-!
The manuscript's bounded REAL strict-level integral for arbitrary continuous
subprobability valuations, not only probabilities. This extends the encoding
bridge needed by its positive centrality assertion. The original probability
definition is unchanged and agrees definitionally with this one. Integrability,
range and the zero positive-axis tail are proved, not assumed.
-/

set_option autoImplicit false
open Set TopologicalSpace MeasureTheory Topology
open scoped ENNReal Classical
universe u v

namespace ZFCFubini

noncomputable def subprobRealMass {X : Type u} [TopologicalSpace X]
    (μ : SubprobValuation X) (U : Opens X) : ℝ := (μ.val U).toReal

theorem subprob_mass_ne_top {X : Type u} [TopologicalSpace X]
    (μ : SubprobValuation X) (U : Opens X) : μ.val U ≠ ∞ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (μ.property.mass_le_one U)

theorem subprobRealMass_mem_unit {X : Type u} [TopologicalSpace X]
    (μ : SubprobValuation X) (U : Opens X) : subprobRealMass μ U ∈ Icc (0 : ℝ) 1 := by
  refine ⟨ENNReal.toReal_nonneg, ?_⟩
  apply ENNReal.toReal_le_of_le_ofReal (by norm_num)
  simpa using μ.property.mass_le_one U

theorem subprobRealMass_mono {X : Type u} [TopologicalSpace X]
    (μ : SubprobValuation X) : Monotone (subprobRealMass μ) := by
  intro U V hUV
  exact ENNReal.toReal_mono (subprob_mass_ne_top μ V) (μ.val.mono hUV)

@[simp] theorem subprobRealMass_empty {X : Type u} [TopologicalSpace X]
    (μ : SubprobValuation X) : subprobRealMass μ ⊥ = 0 := by
  simp [subprobRealMass, μ.val.strict]

theorem subprobRealMass_modular {X : Type u} [TopologicalSpace X]
    (μ : SubprobValuation X) (U V : Opens X) :
    subprobRealMass μ U + subprobRealMass μ V =
      subprobRealMass μ (U ⊔ V) + subprobRealMass μ (U ⊓ V) := by
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
    have hz0 : 0 ≤ z :=
      (subprobRealMass_mem_unit μ U₀).1.trans (hz (mem_image_of_mem _ hU₀))
    apply ENNReal.toReal_le_of_le_ofReal hz0
    apply (μ.val.continuous hn' hd hp).2
    rintro b ⟨U, hU, rfl⟩
    exact (ENNReal.le_ofReal_iff_toReal_le (subprob_mass_ne_top μ U) hz0).mpr
      (hz (mem_image_of_mem _ hU))

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

noncomputable def subprobPaperIntegral {X : Type u} [TopologicalSpace X]
    (μ : SubprobValuation X) (f : X → ℝ) : ℝ :=
  ∫ a : ℝ in Icc (0 : ℝ) 1, subprobLevelMass μ f a

theorem subprobPaperIntegral_eq_strictLevels {X : Type u} [TopologicalSpace X]
    (μ : SubprobValuation X) (f : X → ℝ) (hf : IsRealLSC f) :
    subprobPaperIntegral μ f = ∫ a : ℝ in Icc (0 : ℝ) 1,
      subprobRealMass μ ⟨{x | a < f x}, hf a⟩ := by
  unfold subprobPaperIntegral subprobLevelMass
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun a => congrArg (subprobRealMass μ)
    (Opens.ext (hf a).interior_eq))

@[simp] theorem subprobPaperIntegral_probability {X : Type u} [TopologicalSpace X]
    (μ : ProbabilityValuation X) (f : X → ℝ) :
    subprobPaperIntegral ⟨μ.val, μ.property.subprobability⟩ f = paperIntegral μ f := rfl

theorem subprobPaperIntegral_nonneg {X : Type u} [TopologicalSpace X]
    (μ : SubprobValuation X) (f : X → ℝ) : 0 ≤ subprobPaperIntegral μ f := by
  apply integral_nonneg
  intro a
  exact ENNReal.toReal_nonneg

theorem subprobPaperIntegral_le_one {X : Type u} [TopologicalSpace X]
    (μ : SubprobValuation X) (f : X → ℝ) : subprobPaperIntegral μ f ≤ 1 := by
  have hconst : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Icc (0 : ℝ) 1) :=
    integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  have hi : (∫ a : ℝ in Icc (0 : ℝ) 1, (1 : ℝ)) = 1 := by
    simp [integral_const, measureReal_def, Real.volume_Icc]
  rw [← hi]
  exact integral_mono (subprobLevelMass_integrable μ f) hconst
    (fun a => (subprobRealMass_mem_unit μ _).2)

theorem subprobPaperIntegral_mem_unit {X : Type u} [TopologicalSpace X]
    (μ : SubprobValuation X) (f : X → ℝ) : subprobPaperIntegral μ f ∈ Icc (0 : ℝ) 1 :=
  ⟨subprobPaperIntegral_nonneg μ f, subprobPaperIntegral_le_one μ f⟩

/-- Equality of the literal nonnegative and real strict-level integrals for
any bounded-above-by-one function. Both sides are genuinely integrable where
needed; no default value of a nonintegrable Bochner integral is used. -/
theorem choquetIntegral_ofReal_eq_subprobPaperIntegral
    {X : Type u} [TopologicalSpace X] (μ : SubprobValuation X) (f : X → ℝ)
    (hf1 : ∀ x, f x ≤ 1) :
    choquetIntegral μ.val (fun x => ENNReal.ofReal (f x)) =
      ENNReal.ofReal (subprobPaperIntegral μ f) := by
  let g : ℝ → ℝ≥0∞ := fun a => μ.val
    ⟨interior {x | ENNReal.ofReal a < ENNReal.ofReal (f x)}, isOpen_interior⟩
  have hlevel (a : ℝ) (ha : 0 ≤ a) :
      (⟨interior {x | ENNReal.ofReal a < ENNReal.ofReal (f x)}, isOpen_interior⟩ : Opens X) =
        ⟨interior {x | a < f x}, isOpen_interior⟩ := by
    have hSet : {x | ENNReal.ofReal a < ENNReal.ofReal (f x)} = {x | a < f x} :=
      Set.ext (fun x => ENNReal.ofReal_lt_ofReal_iff_of_nonneg ha)
    exact Opens.ext (congrArg interior hSet)
  have hprofile (a : ℝ) (ha : 0 ≤ a) :
      g a = ENNReal.ofReal (subprobLevelMass μ f a) := by
    change μ.val _ = ENNReal.ofReal ((μ.val _).toReal)
    rw [hlevel a ha]
    exact (ENNReal.ofReal_toReal (subprob_mass_ne_top μ _)).symm
  have htail (a : ℝ) (ha : 1 < a) : g a = 0 := by
    have hSet : {x | ENNReal.ofReal a < ENNReal.ofReal (f x)} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      have hax : a < f x := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by linarith)).mp hx
      exact (not_lt_of_ge (hf1 x)) (ha.trans hax)
    have hOpen : (⟨interior {x | ENNReal.ofReal a < ENNReal.ofReal (f x)},
        isOpen_interior⟩ : Opens X) = ⊥ := by
      apply Opens.ext
      simp only [hSet, interior_empty, Opens.coe_bot]
      rfl
    change μ.val _ = 0
    rw [hOpen]
    exact μ.val.strict
  have hIndicator : (Ici (0 : ℝ)).indicator g = (Icc (0 : ℝ) 1).indicator g := by
    funext a
    by_cases ha0 : 0 ≤ a
    · by_cases ha1 : a ≤ 1
      · simp only [Set.indicator, Set.mem_Ici, Set.mem_Icc, ha0, ha1, and_self]
      · have hga : g a = 0 := htail a (lt_of_not_ge ha1)
        simp [Set.indicator, ha0, ha1, hga]
    · simp [Set.indicator, ha0]
  change (∫⁻ a : ℝ in Ici (0 : ℝ), g a) =
    ENNReal.ofReal (∫ a : ℝ in Icc (0 : ℝ) 1, subprobLevelMass μ f a)
  calc
    _ = ∫⁻ a : ℝ in Icc (0 : ℝ) 1, g a := by
      rw [← lintegral_indicator measurableSet_Ici, ← lintegral_indicator measurableSet_Icc,
        hIndicator]
    _ = ∫⁻ a : ℝ in Icc (0 : ℝ) 1, ENNReal.ofReal (subprobLevelMass μ f a) :=
      setLIntegral_congr_fun measurableSet_Icc (fun a ha => hprofile a ha.1)
    _ = ENNReal.ofReal (∫ a : ℝ in Icc (0 : ℝ) 1, subprobLevelMass μ f a) :=
      (ofReal_integral_eq_lintegral_ofReal (subprobLevelMass_integrable μ f)
        (Filter.Eventually.of_forall (fun a => ENNReal.toReal_nonneg))).symm

/-- A proved real-valued consequence of the existing `Commute` predicate,
for the source's actual [0,1]-valued Scott-continuous integrands and arbitrary
subprobability partners, including partners in a different universe. -/
theorem Commute.subprobPaperIntegral_unit
    {P : Type u} {Q : Type v} [PartialOrder P] [PartialOrder Q]
    (μ : SubprobValuation (WithScott P)) (ν : SubprobValuation (WithScott Q))
    (h : Commute μ.val ν.val) (f : P × Q → UnitInterval) (hf : ScottContinuous f) :
    subprobPaperIntegral μ (fun x => subprobPaperIntegral ν
        (fun y => (f (WithScott.ofScott x, WithScott.ofScott y)).val)) =
      subprobPaperIntegral ν (fun y => subprobPaperIntegral μ
        (fun x => (f (WithScott.ofScott x, WithScott.ofScott y)).val)) := by
  let g : P × Q → ℝ≥0∞ := fun z => ENNReal.ofReal (f z).val
  have hg : ScottContinuous g :=
    (hf.comp unit_coe_scottContinuous).comp ofReal_scottContinuous
  have hg1 (z : P × Q) : g z ≤ 1 := by
    simpa only [g, ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal (f z).property.2
  have he := h g hg hg1
  have hleft :
      (fun x : WithScott P => choquetIntegral ν.val
        (fun y => g (WithScott.ofScott x, WithScott.ofScott y))) =
      (fun x => ENNReal.ofReal (subprobPaperIntegral ν
        (fun y => (f (WithScott.ofScott x, WithScott.ofScott y)).val))) := by
    funext x
    exact choquetIntegral_ofReal_eq_subprobPaperIntegral ν _ (fun y => (f _).property.2)
  have hright :
      (fun y : WithScott Q => choquetIntegral μ.val
        (fun x => g (WithScott.ofScott x, WithScott.ofScott y))) =
      (fun y => ENNReal.ofReal (subprobPaperIntegral μ
        (fun x => (f (WithScott.ofScott x, WithScott.ofScott y)).val))) := by
    funext y
    exact choquetIntegral_ofReal_eq_subprobPaperIntegral μ _ (fun x => (f _).property.2)
  rw [hleft, hright,
    choquetIntegral_ofReal_eq_subprobPaperIntegral μ _
      (fun x => subprobPaperIntegral_le_one ν _),
    choquetIntegral_ofReal_eq_subprobPaperIntegral ν _
      (fun y => subprobPaperIntegral_le_one μ _)] at he
  have he' := congrArg ENNReal.toReal he
  simpa only [ENNReal.toReal_ofReal (subprobPaperIntegral_nonneg μ _),
    ENNReal.toReal_ofReal (subprobPaperIntegral_nonneg ν _)] using he'

theorem Central.subprobPaperIntegral_unit
    {P : Type u} [PartialOrder P] (μ : SubprobValuation (WithScott P))
    (h : Central.{u, v} μ.val) (Q : Type v) [PartialOrder Q] (hQ : IsDcpo Q)
    (ν : SubprobValuation (WithScott Q))
    (f : P × Q → UnitInterval) (hf : ScottContinuous f) :
    subprobPaperIntegral μ (fun x => subprobPaperIntegral ν
        (fun y => (f (WithScott.ofScott x, WithScott.ofScott y)).val)) =
      subprobPaperIntegral ν (fun y => subprobPaperIntegral μ
        (fun x => (f (WithScott.ofScott x, WithScott.ofScott y)).val)) :=
  Commute.subprobPaperIntegral_unit μ ν (h.2 Q hQ ν.val ν.property) f hf

end ZFCFubini
