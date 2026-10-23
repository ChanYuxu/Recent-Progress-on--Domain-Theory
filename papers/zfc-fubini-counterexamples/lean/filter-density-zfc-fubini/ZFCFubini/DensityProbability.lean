import ZFCFubini.DensityValuation
import ZFCFubini.CircleProbability

/-!
Source-facing probability bridges for the frozen ZFC manuscript. This module
only packages the actual proved hitting construction, using the same exceptional
null set for both conclusions. It does not alter any frozen construction.
-/

set_option autoImplicit false
open Set MeasureTheory TopologicalSpace
open scoped ENNReal Topology
universe u

namespace ZFCFubini

/-- A relatively open subset of an ordinary compact carrier is ambient measurable.
The measured relative set is its specified subtype inclusion image. -/
theorem compact_relative_open_ambient_measurable {X : Type u}
    [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [OpensMeasurableSpace X]
    {D : Set X} (hD : IsCompact D) {W : Set D} (hW : IsOpen W) :
    MeasurableSet (Subtype.val '' W) := by
  obtain ⟨O, hO, rfl⟩ := isOpen_induced_iff.mp hW
  rw [Subtype.image_preimage_val]
  exact hD.isClosed.measurableSet.inter hO.measurableSet

/-- The literal ambient Borel statement, independent of any larger supplied
sigma algebra on the ambient space. -/
theorem compact_relative_open_ambient_borel {X : Type u}
    [TopologicalSpace X] [T2Space X]
    {D : Set X} (hD : IsCompact D) {W : Set D} (hW : IsOpen W) :
    @MeasurableSet X (borel X) (Subtype.val '' W) := by
  letI : MeasurableSpace X := borel X
  letI : BorelSpace X := ⟨rfl⟩
  exact compact_relative_open_ambient_measurable hD hW

/-- The precise ambient-measurability assertion preceding source `lem:hitting`
at the actual compact parameter carrier. -/
theorem parameter_relative_open_ambient_measurable {D : Set Omega}
    (hD : PositiveCarrier parameterMeasure D) {W : Set D} (hW : IsOpen W) :
    MeasurableSet (Subtype.val '' W) :=
  compact_relative_open_ambient_measurable hD.2.1 hW

theorem parameter_relative_open_ambient_borel {D : Set Omega}
    (hD : PositiveCarrier parameterMeasure D) {W : Set D} (hW : IsOpen W) :
    @MeasurableSet Omega (borel Omega) (Subtype.val '' W) :=
  compact_relative_open_ambient_borel hD.2.1 hW

/-- Source `lem:hitting`, including its finite-set consequence, with one and
the same actual completed Haar-null exceptional set in both assertions. -/
theorem hitting_source {D : Set Omega} (hD : PositiveCarrier parameterMeasure D) :
    ∃ N : NullSet,
      (∀ y ∉ (N : Set Circle),
        IsOpen {t : D | y ∈ randomOpen t.1} ∧ Dense {t : D | y ∈ randomOpen t.1}) ∧
      (∀ (F : Set Circle), F.Finite → Disjoint F (N : Set Circle) →
        ∀ W : Set D, IsOpen W → W.Nonempty → ∃ t ∈ W, F ⊆ randomOpen t.1) := by
  obtain ⟨N, hNm, hN0, hgood⟩ := hitting_lemma hD
  refine ⟨⟨N, hNm.nullMeasurableSet, hN0⟩, hgood, ?_⟩
  intro F hF hFN W hWo hWn
  exact hitting_finite hgood hF hFN hWo hWn

end ZFCFubini
