import CHFubini.LimitingValuation
import CHFubini.CircleProbability
import CHFubini.EventValues

/-! The two exact test families M_x and H_r used by the manuscript. Their
values are derived from the actual tail maps, not supplied as valuation fields.
-/

set_option autoImplicit false
open Set Topology TopologicalSpace MeasureTheory
open scoped ENNReal
universe u
namespace CHFubini

def pointOpen {X : Type u} [TopologicalSpace X] (x : X) : ScottOpens (Opens X) := by
  refine ⟨{U | x ∈ WithScott.ofScott U}, ?_⟩
  rw [IsScott.isOpen_iff_isUpperSet_and_dirSupInaccOn (D := Set.univ)]
  refine ⟨?_,?_⟩
  · exact fun _ _ hUV hx => hUV hx
  · intro A _ hn hd U hU hx
    rw [hU.unique (isLUB_sSup A)] at hx
    obtain ⟨V,hV,hxV⟩ := Opens.mem_sSup.mp hx
    exact ⟨V,hV,hxV⟩

theorem source_nullTrace_countable {T : Type u} (a : OmegaOneStage → T)
    {N : Set T} (hN : (Set.range a ∩ N).Countable) :
    {x : SourcePoint a | x.val ∈ N}.Countable := by
  apply (hN.preimage (SourcePoint.val_injective a)).mono
  intro x hx
  exact ⟨x.mem_range,hx⟩

theorem sourcePsi_point {T : Type u} [PseudoMetricSpace T] [SecondCountableTopology T]
    (a : OmegaOneStage → T) (r : ℕ → ℝ) (x : SourcePoint a) :
    (sourcePsi a r (pointOpen x) : Set (ℕ → T)) =
      {s | x.val ∈ randomBallUnion r s} := by
  obtain ⟨β,hβ⟩ := source_countable_initial_containment a {x} (countable_singleton x)
  have hx : ∃ β, x ∈ sourceInitial a β := ⟨β,hβ (mem_singleton x)⟩
  exact limitPreimage_pointMembership_eq (sourceStage a r)
    (fun V => ((WithScott.ofScott V : Opens (SourcePoint a)) : Set _))
    (sourceInitial a) (fun s => {x : SourcePoint a | x.val ∈ randomBallUnion r s})
    (sourceStage_decode a r) x hx

theorem rho_point_value {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (a : OmegaOneStage → UnitAddCircle)
    (hnull : ∀ N : Set UnitAddCircle, MeasurableSet N → volume N = 0 →
      {x : SourcePoint a | x.val ∈ N}.Countable)
    (x : SourcePoint a) :
    limitingValuation volume a hnull (circleRadius ε) (circleRadius_pos hε) (pointOpen x) =
      ENNReal.ofReal (qEpsilon ε) := by
  rw [limitingValuation_apply,sourcePsi_point]
  exact pointHit_probability hε hε1 x.val

def massTest {X : Type u} [TopologicalSpace X] (α : Valuation X) (r : ℝ≥0∞) :
    ScottOpens (Opens X) :=
  ⟨{V | r < α (WithScott.ofScott V)},scott_isLSC α.continuous r⟩

theorem massTest_empty {X : Type u} [TopologicalSpace X]
    (α : Valuation X) (hα : α.Probability) {r : ℝ≥0∞} (hr : 1 ≤ r) :
    massTest α r = ⊥ := by
  apply Opens.ext
  apply eq_empty_iff_forall_notMem.mpr
  intro V hV
  exact (not_lt_of_ge ((hα.subprobability.mass_le_one _).trans hr)) hV

theorem sourcePsi_massTest_univ {T : Type u} [PseudoMetricSpace T]
    [SecondCountableTopology T] (a : OmegaOneStage → T) (radii : ℕ → ℝ)
    (α : Valuation (SourcePoint a))
    (hfull : ∀ β s, α (WithScott.ofScott (sourceStage a radii β s)) = 1)
    {r : ℝ≥0∞} (hr : r < 1) :
    (sourcePsi a radii (massTest α r) : Set (ℕ → T)) = univ :=
  limitPreimage_mass_superlevel_univ (sourceStage a radii)
    (fun V => α (WithScott.ofScott V)) 1 r hfull hr

theorem rho_massTest_value {T : Type u}
    [MetricSpace T] [CompactSpace T] [SecondCountableTopology T]
    [MeasurableSpace T] [BorelSpace T] (ν : Measure T) [IsProbabilityMeasure ν]
    (a : OmegaOneStage → T)
    (hnull : ∀ N : Set T, MeasurableSet N → ν N = 0 →
      {x : SourcePoint a | x.val ∈ N}.Countable)
    (radii : ℕ → ℝ) (hradii : ∀ n, 0 < radii n)
    (α : Valuation (SourcePoint a)) (hα : α.Probability)
    (hfull : ∀ β s, α (WithScott.ofScott (sourceStage a radii β s)) = 1)
    (r : ℝ≥0∞) :
    limitingValuation ν a hnull radii hradii (massTest α r) = if r < 1 then 1 else 0 := by
  classical
  by_cases hr : r < 1
  · rw [if_pos hr,limitingValuation_apply,sourcePsi_massTest_univ a radii α hfull hr]
    exact measure_univ
  · rw [if_neg hr,massTest_empty α hα (le_of_not_gt hr),limitingValuation_apply,sourcePsi_empty]
    exact measure_empty

/-- The actual stage valuations xi_beta are continuous probability laws. -/
noncomputable def stageValuation {T : Type u}
    [MetricSpace T] [CompactSpace T] [SecondCountableTopology T]
    [MeasurableSpace T] [BorelSpace T] (ν : Measure T) [IsProbabilityMeasure ν]
    (a : OmegaOneStage → T) (r : ℕ → ℝ) (β : OmegaOneStage) :
    DValuation (Opens (SourcePoint a)) := by
  letI : Measure.InnerRegular (productLaw ν) := productLaw_innerRegular ν
  exact (radonValuation (productLaw ν)).push (sourceStage a r β) (sourceStage_continuous a r β)

theorem stageValuation_probability {T : Type u}
    [MetricSpace T] [CompactSpace T] [SecondCountableTopology T]
    [MeasurableSpace T] [BorelSpace T] (ν : Measure T) [IsProbabilityMeasure ν]
    (a : OmegaOneStage → T) (r : ℕ → ℝ) (β : OmegaOneStage) :
    (stageValuation ν a r β).Probability := by
  letI : Measure.InnerRegular (productLaw ν) := productLaw_innerRegular ν
  exact (radonValuation_probability (productLaw ν)).push _ _

theorem limitingValuation_eq_inf_stages {T : Type u}
    [MetricSpace T] [CompactSpace T] [SecondCountableTopology T]
    [MeasurableSpace T] [BorelSpace T] (ν : Measure T) [IsProbabilityMeasure ν]
    (a : OmegaOneStage → T)
    (hnull : ∀ N : Set T, MeasurableSet N → ν N = 0 →
      {x : SourcePoint a | x.val ∈ N}.Countable)
    (r : ℕ → ℝ) (hr : ∀ n, 0 < r n)
    (H : ScottOpens (Opens (SourcePoint a))) :
    limitingValuation ν a hnull r hr H = ⨅ β, stageValuation ν a r β H := by
  change productLaw ν (limitPreimage (sourceStage a r) (H : Set _)) =
    ⨅ β, productLaw ν (sourceStage a r β ⁻¹' (H : Set _))
  apply le_antisymm
  · exact le_iInf (fun β => measure_mono (iInter_subset _ β))
  · obtain ⟨σ,hσ⟩ := limitPreimage_eventually_eq omegaOneStage_countablyBounded
      (sourceStage a r) H (sourceStage_event_antitone a r H)
      (fun β => H.isOpen.preimage (sourceStage_continuous a r β))
    calc
      (⨅ β, productLaw ν (sourceStage a r β ⁻¹' (H : Set _))) ≤
          productLaw ν (sourceStage a r σ ⁻¹' (H : Set _)) := iInf_le _ σ
      _ = _ := congrArg (productLaw ν) (hσ σ le_rfl)

end CHFubini
