import CHFubini.SourceMeasure
import CHFubini.SourceSmyth
import CHFubini.RhoTests

/-! Fixed, named versions of the manuscript's actual objects. Choice is used
only on proved existence theorems. The selected sequence, trace measure,
valuation restriction, random maps, singleton pushforward and incidence set
are not arbitrary witnesses carrying the final desired conclusion.
-/
set_option autoImplicit false
open Set Topology TopologicalSpace MeasureTheory
open scoped ENNReal
namespace CHFubini

local instance : NoAtoms (volume : Measure UnitAddCircle) := unitCircle_volume_noAtoms
local instance : Measure.InnerRegular (volume : Measure UnitAddCircle) :=
  unitCircle_volume_innerRegular

noncomputable def paperSequence (hCH : CH) : OmegaOneStage → UnitAddCircle :=
  (exists_CH_circle_points hCH).choose

theorem paperSequence_spec (hCH : CH) :
    Function.Injective (paperSequence hCH) ∧
    (∀ B : Set UnitAddCircle, MeasurableSet B → volume B = 0 → ∃ β,
      range (paperSequence hCH) ∩ B ⊆ initialSegment (paperSequence hCH) β ∧
      (range (paperSequence hCH) ∩ B).Countable) ∧
    (∀ C : Set UnitAddCircle, IsCompact C → 0 < volume C →
      (range (paperSequence hCH) ∩ C).Nonempty) ∧
    (∀ E : Set UnitAddCircle, MeasurableSet E →
      (range (paperSequence hCH) ∩ E).Countable → volume E = 0) :=
  (exists_CH_circle_points hCH).choose_spec

abbrev PaperSource (hCH : CH) := SourcePoint (paperSequence hCH)
abbrev PaperP (hCH : CH) := SourceSmyth (paperSequence hCH)
abbrev PaperL (hCH : CH) := Opens (PaperSource hCH)
abbrev PaperOmega := ℕ → UnitAddCircle
noncomputable def paperLaw : Measure PaperOmega := productLaw volume

noncomputable def paperSourceMeasure (hCH : CH) : Measure (PaperSource hCH) :=
  (exists_source_measure_and_valuation volume (paperSequence hCH) (paperSequence_spec hCH).2.2.2).choose

theorem paperSourceMeasure_spec (hCH : CH) :
    IsProbabilityMeasure (paperSourceMeasure hCH) ∧
    ∀ B : Set UnitAddCircle, MeasurableSet B →
      paperSourceMeasure hCH (SourcePoint.val ⁻¹' B) = volume B := by
  have hs := (exists_source_measure_and_valuation volume
    (paperSequence hCH) (paperSequence_spec hCH).2.2.2).choose_spec
  exact ⟨hs.1,hs.2.1⟩

noncomputable def paperAlpha (hCH : CH) : Valuation (PaperSource hCH) :=
  sourceValuation volume (paperSequence hCH) (paperSourceMeasure hCH) (paperSourceMeasure_spec hCH).2

theorem paperAlpha_probability (hCH : CH) : (paperAlpha hCH).Probability :=
  sourceValuation_probability volume (paperSequence hCH)
    (paperSourceMeasure hCH) (paperSourceMeasure_spec hCH).2

theorem paperNullTrace (hCH : CH) :
    ∀ N : Set UnitAddCircle, MeasurableSet N → volume N = 0 →
      {x : PaperSource hCH | x.val ∈ N}.Countable :=
  source_nullTrace_of_ambient_null_trace volume (paperSequence hCH)
    (fun N hN hN0 => ((paperSequence_spec hCH).2.1 N hN hN0).choose_spec.2)

noncomputable def paperRho (hCH : CH) (ε : ℝ) (hε : 0 < ε) : DValuation (PaperL hCH) :=
  limitingValuation volume (paperSequence hCH) (paperNullTrace hCH)
    (circleRadius ε) (circleRadius_pos hε)

theorem paperRho_probability (hCH : CH) (ε : ℝ) (hε : 0 < ε) :
    (paperRho hCH ε hε).Probability :=
  limitingValuation_probability volume (paperSequence hCH) (paperNullTrace hCH)
    (circleRadius ε) (circleRadius_pos hε)

noncomputable def paperMu (hCH : CH) : DValuation (PaperP hCH) :=
  sourceMu (paperSequence hCH) (paperAlpha hCH)

theorem paperMu_probability (hCH : CH) : (paperMu hCH).Probability :=
  sourceMu_probability (paperSequence hCH) (paperAlpha hCH) (paperAlpha_probability hCH)

noncomputable def paperW (hCH : CH) : ScottOpens (PaperP hCH × PaperL hCH) := incidenceOpen

theorem paperAlpha_stage_mass (hCH : CH) (ε : ℝ) (β : OmegaOneStage) (s : PaperOmega) :
    paperAlpha hCH (WithScott.ofScott (sourceStage (paperSequence hCH) (circleRadius ε) β s)) = 1 :=
  sourceValuation_tailRandomOpen_mass volume (paperSequence hCH)
    (paperSourceMeasure hCH) (paperSourceMeasure_spec hCH).2 (circleRadius ε) β s

end CHFubini
