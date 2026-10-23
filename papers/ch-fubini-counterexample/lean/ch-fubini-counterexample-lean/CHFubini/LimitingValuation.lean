import CHFubini.TailTopology
import CHFubini.RandomOpenContinuity
import CHFubini.RadonValuation
import Mathlib.Order.ScottContinuity.Complete

/-! The manuscript's actual random tail maps, their eventual event map, and
the limiting continuous probability valuation. The only source-set property
in the general helper is its explicit countable trace on ambient null sets;
the CH construction proves this property for the paper's chosen source.
Carrier existence, Baire agreement, independence, and arbitrary-union
null-defect are theorems in the dependency chain, not fields of an assumed
valuation/existence package.
-/

set_option autoImplicit false
open Set Topology TopologicalSpace MeasureTheory
open scoped ENNReal
universe u v
namespace CHFubini

def sourceTailOpen {T : Type u} [TopologicalSpace T]
    (a : OmegaOneStage → T) (β : OmegaOneStage) : Opens (SourcePoint a) :=
  ⟨sourceTail a β,sourceTail_isOpen a β⟩

theorem sourceTailOpen_antitone {T : Type u} [TopologicalSpace T]
    (a : OmegaOneStage → T) : Antitone (sourceTailOpen a) := by
  intro β γ hβγ x hx
  exact hβγ.trans hx

/-- Equations (4.1)-(4.3): F_beta(s)=T_beta union h^-1(U_s), on the actual
generated tail source and its entire open-set lattice. -/
noncomputable def sourceStage {T : Type u} [PseudoMetricSpace T]
    (a : OmegaOneStage → T) (r : ℕ → ℝ)
    (β : OmegaOneStage) (s : ℕ → T) : WithScott (Opens (SourcePoint a)) :=
  WithScott.toScott (tailRandomOpen (sourceTailOpen a β) SourcePoint.val
    (source_val_continuous a) r s)

theorem sourceStage_continuous {T : Type u} [PseudoMetricSpace T]
    (a : OmegaOneStage → T) (r : ℕ → ℝ) (β : OmegaOneStage) :
    Continuous (sourceStage a r β) :=
  tailRandomOpen_continuous (sourceTailOpen a β) SourcePoint.val
    (source_val_continuous a) r

theorem sourceStage_event_antitone {T : Type u} [PseudoMetricSpace T]
    (a : OmegaOneStage → T) (r : ℕ → ℝ)
    (H : Opens (WithScott (Opens (SourcePoint a)))) :
    Antitone (fun β => sourceStage a r β ⁻¹' (H : Set _)) :=
  tailRandomOpen_event_antitone (sourceTailOpen a) (sourceTailOpen_antitone a)
    SourcePoint.val (source_val_continuous a) r H.isOpen

theorem sourceStage_decode {T : Type u} [PseudoMetricSpace T]
    (a : OmegaOneStage → T) (r : ℕ → ℝ) (β : OmegaOneStage) (s : ℕ → T) :
    ((WithScott.ofScott (sourceStage a r β s) : Opens (SourcePoint a)) : Set _) =
      (sourceInitial a β)ᶜ ∪ {x | x.val ∈ randomBallUnion r s} := by
  change sourceTail a β ∪ SourcePoint.val ⁻¹' randomBallUnion r s = _
  rw [sourceTail_eq_initial_compl]
  rfl

/-- Equation psi-rho's event map, proved to be genuinely ordinary-open. -/
def sourcePsi {T : Type u} [PseudoMetricSpace T] [SecondCountableTopology T]
    (a : OmegaOneStage → T) (r : ℕ → ℝ)
    (H : Opens (WithScott (Opens (SourcePoint a)))) : Opens (ℕ → T) :=
  ⟨limitPreimage (sourceStage a r) (H : Set _),
    limitPreimage_isOpen omegaOneStage_countablyBounded (sourceStage a r) H
      (sourceStage_event_antitone a r H)
      (fun β => H.isOpen.preimage (sourceStage_continuous a r β))⟩

theorem sourcePsi_mono {T : Type u} [PseudoMetricSpace T] [SecondCountableTopology T]
    (a : OmegaOneStage → T) (r : ℕ → ℝ) : Monotone (sourcePsi a r) :=
  fun _ _ h => limitPreimage_mono (sourceStage a r) h

@[simp] theorem sourcePsi_empty {T : Type u} [PseudoMetricSpace T]
    [SecondCountableTopology T] (a : OmegaOneStage → T) (r : ℕ → ℝ) :
    sourcePsi a r ⊥ = ⊥ := by
  apply Opens.ext
  exact limitPreimage_empty _

@[simp] theorem sourcePsi_univ {T : Type u} [PseudoMetricSpace T]
    [SecondCountableTopology T] (a : OmegaOneStage → T) (r : ℕ → ℝ) :
    sourcePsi a r ⊤ = ⊤ := by
  apply Opens.ext
  exact limitPreimage_univ _

theorem sourcePsi_inter {T : Type u} [PseudoMetricSpace T]
    [SecondCountableTopology T] (a : OmegaOneStage → T) (r : ℕ → ℝ)
    (H K : Opens (WithScott (Opens (SourcePoint a)))) :
    sourcePsi a r (H ⊓ K) = sourcePsi a r H ⊓ sourcePsi a r K := by
  apply Opens.ext
  exact limitPreimage_inter _ _ _

theorem sourcePsi_union {T : Type u} [PseudoMetricSpace T]
    [SecondCountableTopology T] (a : OmegaOneStage → T) (r : ℕ → ℝ)
    (H K : Opens (WithScott (Opens (SourcePoint a)))) :
    sourcePsi a r (H ⊔ K) = sourcePsi a r H ⊔ sourcePsi a r K := by
  apply Opens.ext
  apply limitPreimage_union omegaOneStage_countablyBounded (sourceStage a r) H K
  · exact sourceStage_event_antitone a r H
  · exact sourceStage_event_antitone a r K
  · exact fun β => H.isOpen.preimage (sourceStage_continuous a r β)
  · exact fun β => K.isOpen.preimage (sourceStage_continuous a r β)

theorem sourcePsi_countable_union {T : Type u} [PseudoMetricSpace T]
    [SecondCountableTopology T] (a : OmegaOneStage → T) (r : ℕ → ℝ)
    {J : Type v} [Countable J]
    (H : J → Opens (WithScott (Opens (SourcePoint a)))) :
    sourcePsi a r (⨆ j, H j) = ⨆ j, sourcePsi a r (H j) := by
  apply Opens.ext
  simpa only [sourcePsi,Opens.coe_iSup] using
    limitPreimage_iUnion omegaOneStage_countablyBounded (sourceStage a r)
    (fun j => (H j : Set _)) (fun j => sourceStage_event_antitone a r (H j))
    (fun j β => (H j).isOpen.preimage (sourceStage_continuous a r β))

/-- Source Proposition 4.7 on this specified source and actual random opens.
It has no countability or directedness condition on the family of tests. -/
theorem source_null_defect {T : Type u}
    [MetricSpace T] [CompactSpace T] [SecondCountableTopology T]
    [MeasurableSpace T] [BorelSpace T] (ν : Measure T) [IsProbabilityMeasure ν]
    (a : OmegaOneStage → T)
    (hnullTrace : ∀ N : Set T, MeasurableSet N → ν N = 0 →
      {x : SourcePoint a | x.val ∈ N}.Countable)
    (r : ℕ → ℝ) (hr : ∀ n, 0 < r n)
    {J : Type v} (H : J → Opens (WithScott (Opens (SourcePoint a)))) :
    productLaw ν ((sourcePsi a r (⨆ j, H j) : Set _) \
      ⋃ j, (sourcePsi a r (H j) : Set _)) = 0 := by
  change productLaw ν
    (limitPreimage (sourceStage a r) ((⨆ j, H j : Opens _) : Set _) \
      ⋃ j, limitPreimage (sourceStage a r) (H j : Set _)) = 0
  rw [Opens.coe_iSup]
  refine random_ball_arbitrary_union_defect_null omegaOneStage_countablyBounded ν
    (sourceInitial a) (sourceInitial_mono a) (sourceInitial_countable a)
    (source_countable_initial_containment a) SourcePoint.val hnullTrace r hr
    (sourceStage a r) (fun V => ((WithScott.ofScott V : Opens (SourcePoint a)) : Set _))
    ?_ (sourceStage_decode a r) (fun j => (H j : Set _)) ?_ ?_
  · intro U V h
    apply WithScott.ofScott.injective
    exact Opens.ext h
  · exact fun β j => (H j).isOpen.preimage (sourceStage_continuous a r β)
  · exact fun j => sourceStage_event_antitone a r (H j)

/-- The actual limiting valuation rho, not an assumed record of its laws.
All valuation fields are proved from the preceding null-defect theorem. -/
noncomputable def limitingValuation {T : Type u}
    [MetricSpace T] [CompactSpace T] [SecondCountableTopology T]
    [MeasurableSpace T] [BorelSpace T] (ν : Measure T) [IsProbabilityMeasure ν]
    (a : OmegaOneStage → T)
    (hnullTrace : ∀ N : Set T, MeasurableSet N → ν N = 0 →
      {x : SourcePoint a | x.val ∈ N}.Countable)
    (r : ℕ → ℝ) (hr : ∀ n, 0 < r n) :
    DValuation (Opens (SourcePoint a)) where
  mass H := productLaw ν (sourcePsi a r H : Set _)
  strict := by simp
  modular H K := by
    rw [sourcePsi_union,sourcePsi_inter]
    exact (measure_union_add_inter (sourcePsi a r H : Set _)
      (sourcePsi a r K).isOpen.measurableSet).symm
  continuous := by
    letI : Measure.InnerRegular (productLaw ν) := productLaw_innerRegular ν
    apply ScottContinuous.of_map_sSup
    intro S hn hd
    letI : Nonempty S := hn.to_subtype
    let G : S → Opens (ℕ → T) := fun H => sourcePsi a r H.val
    have hdir : Directed (· ≤ ·) G := by
      intro H K
      obtain ⟨V,hV,hHV,hKV⟩ := hd H.val H.property K.val K.property
      exact ⟨⟨V,hV⟩,sourcePsi_mono a r hHV,sourcePsi_mono a r hKV⟩
    have hsup : (sSup S : Opens (WithScott (Opens (SourcePoint a)))) =
        ⨆ H : S, H.val := sSup_eq_iSup' S
    have hnull := source_null_defect ν a hnullTrace r hr (fun H : S => H.val)
    rw [← hsup] at hnull
    have hsub : (⨆ H : S, G H : Opens (ℕ → T)) ≤ sourcePsi a r (sSup S) := by
      apply iSup_le
      intro H
      exact sourcePsi_mono a r (le_sSup H.property)
    have hnull' : productLaw ν
        ((sourcePsi a r (sSup S) : Set _) \ ((⨆ H : S, G H : Opens _) : Set _)) = 0 := by
      simpa only [Opens.coe_iSup,G] using hnull
    have he := measure_eq_measure_of_null_diff hsub hnull'
    calc
      productLaw ν (sourcePsi a r (sSup S) : Set _) =
          productLaw ν ((⨆ H : S, G H : Opens (ℕ → T)) : Set _) := he.symm
      _ = ⨆ H : S, productLaw ν (G H : Set _) :=
        (radonValuation (productLaw ν)).map_iSup G hdir
      _ = sSup ((fun H => productLaw ν (sourcePsi a r H : Set _)) '' S) := by
        rw [sSup_image]
        exact iSup_subtype'' S (fun H => productLaw ν (sourcePsi a r H : Set _))

@[simp] theorem limitingValuation_apply {T : Type u}
    [MetricSpace T] [CompactSpace T] [SecondCountableTopology T]
    [MeasurableSpace T] [BorelSpace T] (ν : Measure T) [IsProbabilityMeasure ν]
    (a : OmegaOneStage → T)
    (hnullTrace : ∀ N : Set T, MeasurableSet N → ν N = 0 →
      {x : SourcePoint a | x.val ∈ N}.Countable)
    (r : ℕ → ℝ) (hr : ∀ n, 0 < r n)
    (H : Opens (WithScott (Opens (SourcePoint a)))) :
    limitingValuation ν a hnullTrace r hr H = productLaw ν (sourcePsi a r H : Set _) := rfl

theorem limitingValuation_probability {T : Type u}
    [MetricSpace T] [CompactSpace T] [SecondCountableTopology T]
    [MeasurableSpace T] [BorelSpace T] (ν : Measure T) [IsProbabilityMeasure ν]
    (a : OmegaOneStage → T)
    (hnullTrace : ∀ N : Set T, MeasurableSet N → ν N = 0 →
      {x : SourcePoint a | x.val ∈ N}.Countable)
    (r : ℕ → ℝ) (hr : ∀ n, 0 < r n) :
    (limitingValuation ν a hnullTrace r hr).Probability := by
  change productLaw ν (sourcePsi a r ⊤ : Set _) = 1
  rw [sourcePsi_univ]
  exact measure_univ

end CHFubini
