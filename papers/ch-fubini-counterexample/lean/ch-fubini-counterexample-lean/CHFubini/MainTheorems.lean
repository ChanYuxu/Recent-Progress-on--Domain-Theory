import CHFubini.SourceMeasure
import CHFubini.SourceSmyth
import CHFubini.RhoTests
import CHFubini.ChoquetCalculations
import CHFubini.CompleteLatticeWellFiltered
import CHFubini.SourceConstruction

/-! The source's concrete CH witnesses and the two actual Choquet integrals.
The construction of a, alpha and rho is in the dependency graph of paper_main;
none of their asserted continuity or integral values is an external premise.
-/

set_option autoImplicit false
open Set Topology TopologicalSpace MeasureTheory
open scoped ENNReal
namespace CHFubini

local instance : NoAtoms (volume : Measure UnitAddCircle) := unitCircle_volume_noAtoms
local instance : Measure.InnerRegular (volume : Measure UnitAddCircle) :=
  unitCircle_volume_innerRegular

@[simp] theorem compactNeighborhood_singleton_eq_pointOpen
    {X : Type} [TopologicalSpace X] (x : X) :
    compactNeighborhood (WithScott.ofScott (singletonMap x)) = pointOpen x := by
  apply Opens.ext
  ext V
  change ({x} : Set X) ⊆ (WithScott.ofScott V : Opens X) ↔ x ∈ WithScott.ofScott V
  exact singleton_subset_iff

theorem source_first_iterated_integral
    {ε : ℝ} (hε : 0 < ε) (a : OmegaOneStage → UnitAddCircle)
    (hnull : ∀ N : Set UnitAddCircle, MeasurableSet N → volume N = 0 →
      {x : SourcePoint a | x.val ∈ N}.Countable)
    (α : Valuation (SourcePoint a)) (hα : α.Probability)
    (hfull : ∀ β s, α (WithScott.ofScott (sourceStage a (circleRadius ε) β s)) = 1) :
    choquetIntegral (limitingValuation volume a hnull (circleRadius ε) (circleRadius_pos hε))
      (fun V => choquetIntegral (sourceMu a α)
        (indicator (leftSection incidenceOpen (WithScott.ofScott V)))) = 1 := by
  simp only [choquetIntegral_indicator,leftSection_incidence_eq_box,sourceMu_box]
  have hf : IsLSC (fun V : WithScott (Opens (SourcePoint a)) => α (WithScott.ofScott V)) :=
    scott_isLSC α.continuous
  have hcalc := choquetIntegral_eq_of_unit_superlevels
    (limitingValuation volume a hnull (circleRadius ε) (circleRadius_pos hε))
    (fun V : WithScott (Opens (SourcePoint a)) => α (WithScott.ofScott V)) hf 1 (by
      intro t _
      change limitingValuation volume a hnull (circleRadius ε) (circleRadius_pos hε)
        (massTest α (ENNReal.ofReal t)) = _
      rw [rho_massTest_value volume a hnull (circleRadius ε) (circleRadius_pos hε) α hα hfull]
      simp only [ENNReal.ofReal_lt_one])
  simpa only [ENNReal.ofReal_one] using hcalc

theorem source_second_iterated_integral
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) (a : OmegaOneStage → UnitAddCircle)
    (hnull : ∀ N : Set UnitAddCircle, MeasurableSet N → volume N = 0 →
      {x : SourcePoint a | x.val ∈ N}.Countable)
    (α : Valuation (SourcePoint a)) (hα : α.Probability) :
    choquetIntegral (sourceMu a α)
      (fun C => choquetIntegral
        (limitingValuation volume a hnull (circleRadius ε) (circleRadius_pos hε))
        (indicator (rightSection incidenceOpen (WithScott.ofScott C)))) =
      ENNReal.ofReal (qEpsilon ε) := by
  let ρ := limitingValuation volume a hnull (circleRadius ε) (circleRadius_pos hε)
  simp only [choquetIntegral_indicator,rightSection_incidence_eq_compactNeighborhood]
  change choquetIntegral (α.push singletonMap (sourceSingleton_continuous a))
    (fun C => ρ (compactNeighborhood (WithScott.ofScott C))) = _
  rw [choquetIntegral_push α singletonMap (sourceSingleton_continuous a) _
    (scott_isLSC (compactProfile_scottContinuous ρ.mass ρ.continuous))]
  have he : (fun C : WithScott (SourceSmyth a) =>
      ρ (compactNeighborhood (WithScott.ofScott C))) ∘ singletonMap =
      (fun _ : SourcePoint a => ENNReal.ofReal (qEpsilon ε)) := by
    funext x
    simp only [Function.comp_apply,compactNeighborhood_singleton_eq_pointOpen]
    exact rho_point_value hε hε1 a hnull x
  rw [he,choquetIntegral_const α hα]

/-- Exact main theorem with the manuscript's specified constructions. -/
theorem counterexampleAt_of_CH (hCH : CH) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    CounterexampleAt ε := by
  let a := paperSequence hCH
  let α := paperAlpha hCH
  have hα : α.Probability := paperAlpha_probability hCH
  let hnull := paperNullTrace hCH
  let ρ := paperRho hCH ε hε
  have hfull : ∀ β s, α (WithScott.ofScott (sourceStage a (circleRadius ε) β s)) = 1 :=
    paperAlpha_stage_mass hCH ε
  obtain ⟨hdcpo,_,hfirst,hsober,hwell⟩ := source_smyth_properties a
  obtain ⟨_,hqpos,hqle,_⟩ := qEpsilon_bounds hε hε1
  refine ⟨SourceSmyth a,inferInstance,Opens (SourcePoint a),inferInstance,
    hdcpo,hfirst,hsober,hwell,opens_scott_isWellFiltered _,
    sourceMu a α,ρ,incidenceOpen,sourceMu_probability a α hα,
    limitingValuation_probability volume a hnull (circleRadius ε) (circleRadius_pos hε),
    ?_,?_,hqpos,hqle,hε1,source_f_profile_scott a α,source_g_profile_scott ρ⟩
  · exact source_first_iterated_integral hε a hnull α hα hfull
  · exact source_second_iterated_integral hε hε1 a hnull α hα

/-- Theorem 1.1, not a proposition definition or a conditional construction
interface. The sole set-theoretic premise is the explicit CH equality. -/
theorem paper_main : PaperMainClaim := counterexampleAt_of_CH

end CHFubini

#print axioms CHFubini.paper_main
