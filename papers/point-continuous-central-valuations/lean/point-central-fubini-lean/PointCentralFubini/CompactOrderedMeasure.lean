import PointCentralFubini.OrderedVietoris
import Mathlib.MeasureTheory.Measure.Regular

/-! The explicitly cited AJK extension theorem, and the internal Radon-to-tau
bridge. The manuscript's own lift theorem is not imported as an axiom. -/
set_option autoImplicit false
open Set Topology TopologicalSpace MeasureTheory
open scoped ENNReal
universe u
namespace PointCentralFubini

structure FiniteRadonMeasure (E : Type u) [t : TopologicalSpace E] where
  measure : @Measure E (borel E)
  finite : measure univ ≠ ⊤
  innerRegular : @Measure.InnerRegular E (borel E) t measure

/-- Cited AJK Theorem 27, author-hosted corrected version `measures.pdf`,
printed page 16 (PDF page 16), lines 720--721 in the retrieved text.
Bounded continuous valuations on the upward topology of a compact ordered
space extend to finite inner-regular Borel measures on the Hausdorff topology.
Only the existence clause is used. -/
axiom ajk_compact_ordered_extension (E : Type u) [TopologicalSpace E] [PartialOrder E]
    [CompactSpace E] [OrderClosedTopology E]
    (ν : @Valuation E (upwardTopology E))
    (hν : @Valuation.Finite E (upwardTopology E) ν) :
    ∃ M : FiniteRadonMeasure E, ∀ U : @Opens E (upwardTopology E),
      M.measure (U : Set E) = @Valuation.mass E (upwardTopology E) ν U

namespace FiniteRadonMeasure
variable {E : Type u} [TopologicalSpace E]

/-- Compact inner approximation and a directed finite-subcover argument prove
tau-smoothness; it is not an additional assumption in the extension axiom. -/
def toTauMeasure (M : FiniteRadonMeasure E) : TauMeasure E := by
  letI : MeasurableSpace E := borel E
  letI : BorelSpace E := ⟨rfl⟩
  letI : Measure.InnerRegular M.measure := M.innerRegular
  refine ⟨M.measure,M.finite,?_⟩
  intro A hn hd p hp
  constructor
  · rintro z ⟨U,hU,rfl⟩
    exact measure_mono (hp.1 hU)
  · intro z hz
    change M.measure (p : Set E) ≤ z
    rw [p.isOpen.measurableSet.measure_eq_iSup_isCompact M.measure]
    apply iSup_le; intro K
    apply iSup_le; intro hKp
    apply iSup_le; intro hK
    letI : Nonempty A := hn.to_subtype
    let V : A → Set E := fun U => (U.val : Set E)
    have hdir : Directed (· ⊆ ·) V := by
      intro U W
      obtain ⟨Z,hZ,hUZ,hWZ⟩ := hd U.val U.property W.val W.property
      exact ⟨⟨Z,hZ⟩,hUZ,hWZ⟩
    have hcover : K ⊆ ⋃ U : A, V U := by
      intro x hx
      have hxp := hKp hx
      rw [hp.unique (isLUB_sSup A)] at hxp
      obtain ⟨U,hU,hxU⟩ := Opens.mem_sSup.mp hxp
      exact mem_iUnion.mpr ⟨⟨U,hU⟩,hxU⟩
    obtain ⟨U,hKU⟩ := hK.elim_directed_cover V (fun U => U.val.isOpen) hcover hdir
    exact (measure_mono hKU).trans (hz (mem_image_of_mem _ U.property))

@[simp] theorem toTauMeasure_measure (M : FiniteRadonMeasure E) :
    M.toTauMeasure.measure = M.measure := rfl

end FiniteRadonMeasure
end PointCentralFubini
