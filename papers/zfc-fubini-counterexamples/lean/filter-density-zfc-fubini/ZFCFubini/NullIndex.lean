import ZFCFubini.DensityValuation
import ZFCFubini.Stabilization

set_option autoImplicit false
open Set MeasureTheory
namespace ZFCFubini

instance nullSetNonempty : Nonempty NullSet := ⟨nullSetEmpty⟩

instance nullSetSemilatticeSup : SemilatticeSup NullSet :=
  { (inferInstance : PartialOrder NullSet) with
    sup := nullSetUnion
    le_sup_left := fun _ _ => Set.subset_union_left
    le_sup_right := fun _ _ => Set.subset_union_right
    sup_le := fun _ _ _ h₁ h₂ => Set.union_subset h₁ h₂ }

/-- The actual null-set index set is closed under every countable union.
No CH, omega-one enumeration or regularity assumption is involved. -/
theorem nullSet_countablyBounded : CountablyBounded NullSet := by
  intro A hA
  letI : Countable A := hA.to_subtype
  let N : Set Circle := ⋃ M : A, M.val.val
  have hNm : NullMeasurableSet N (volume : Measure Circle) :=
    NullMeasurableSet.iUnion (fun M => M.val.property.1)
  have hN0 : volume N = 0 := measure_iUnion_null (fun M : A => M.val.property.2)
  refine ⟨⟨N, hNm, hN0⟩, ?_⟩
  intro M hM
  exact subset_iUnion (fun K : A => K.val.val) ⟨M, hM⟩

def nullSingleton (x : Circle) : NullSet :=
  ⟨{x}, (measurableSet_singleton x).nullMeasurableSet, circle_singleton_null x⟩

def conullOpen (M : NullSet) : @TopologicalSpace.Opens Circle densityTopology := by
  letI : TopologicalSpace Circle := densityTopology
  exact ⟨M.valᶜ, densityOpen_null_compl M.property.2⟩

end ZFCFubini
