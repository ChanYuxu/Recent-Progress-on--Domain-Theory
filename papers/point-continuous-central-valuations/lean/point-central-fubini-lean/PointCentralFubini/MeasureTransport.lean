import PointCentralFubini.OuterTrace
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.MeasureTheory.Measure.Map

/-! Continuous pushforwards of tau-smooth measures and transport of full-outer traces. -/
set_option autoImplicit false
open Set Topology TopologicalSpace MeasureTheory
open scoped ENNReal
universe u v
namespace PointCentralFubini

namespace TauMeasure
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

noncomputable def map (m : TauMeasure X) (f : X → Y) (hf : Continuous f) : TauMeasure Y := by
  letI : MeasurableSpace X := borel X
  letI : BorelSpace X := ⟨rfl⟩
  letI : MeasurableSpace Y := borel Y
  letI : BorelSpace Y := ⟨rfl⟩
  refine ⟨m.measure.map f,?_,?_⟩
  · rw [Measure.map_apply hf.borel_measurable MeasurableSet.univ,preimage_univ]
    exact m.finite
  · have he : (fun U : Opens Y => m.measure.map f (U : Set Y)) =
        (m.toValuation.push f hf).mass := by
      funext U
      exact Measure.map_apply hf.borel_measurable U.isOpen.measurableSet
    exact he.symm ▸ (m.toValuation.push f hf).continuous

theorem map_apply (m : TauMeasure X) (f : X → Y) (hf : Continuous f)
    {B : Set Y} (hB : MeasurableSet[borel Y] B) :
    (m.map f hf).measure B = m.measure (f ⁻¹' B) := by
  letI : MeasurableSpace X := borel X
  letI : BorelSpace X := ⟨rfl⟩
  letI : MeasurableSpace Y := borel Y
  letI : BorelSpace Y := ⟨rfl⟩
  exact Measure.map_apply hf.borel_measurable hB

end TauMeasure

theorem fullOuterTrace_transport {X : Type u} {E : Type v}
    [TopologicalSpace X] [TopologicalSpace E] (j : X → E) (hj : IsEmbedding j)
    (M : TauMeasure E)
    (hfull : ∀ B : Set E, MeasurableSet[borel E] B → B ⊆ (range j)ᶜ → M.measure B = 0) :
    ∃ m : TauMeasure X, ∀ B : Set E, MeasurableSet[borel E] B →
      m.measure (j ⁻¹' B) = M.measure B := by
  letI : MeasurableSpace X := borel X
  letI : BorelSpace X := ⟨rfl⟩
  letI : MeasurableSpace E := borel E
  letI : BorelSpace E := ⟨rfl⟩
  obtain ⟨mA,hmA⟩ := full_outer_trace E M (range j) hfull
  let e : X ≃ₜ range j := hj.toHomeomorph
  let m : TauMeasure X := mA.map e.symm e.symm.continuous
  refine ⟨m,?_⟩
  intro B hB
  have hpre : MeasurableSet (j ⁻¹' B) := hj.continuous.borel_measurable hB
  rw [TauMeasure.map_apply mA e.symm e.symm.continuous hpre]
  have he : e.symm ⁻¹' (j ⁻¹' B) = (Subtype.val : range j → E) ⁻¹' B := by
    ext z
    have hz : j (e.symm z) = z.val := congrArg Subtype.val (e.apply_symm_apply z)
    simp only [mem_preimage,hz]
  rw [he,hmA B hB]

end PointCentralFubini
