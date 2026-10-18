import PointCentralFubini.SorgenfreyBasics
import Mathlib.Topology.Separation.CompletelyRegular

/-! The compact Hausdorff compactification used in source Lemma 4.4. -/
set_option autoImplicit false
open Set Topology TopologicalSpace unitInterval
namespace PointCentralFubini

theorem sorgenfrey_isClopen_Ico (a b : Sorgenfrey) : IsClopen (Ico a b) := by
  simpa only [compl_Iio,Ici_inter_Iio] using
    (sorgenfrey_isClopen_Iio a).compl.inter (sorgenfrey_isClopen_Iio b)

instance : CompletelyRegularSpace Sorgenfrey := by
  classical
  apply completelyRegularSpace_iff_isOpen.mpr
  intro x U hU hx
  obtain ⟨V,⟨a,b,rfl⟩,hxV,hVU⟩ := sorgenfrey_basis.exists_subset_of_mem_open hx hU
  let f : Sorgenfrey → I := fun y => if y ∈ Ico a b then 0 else 1
  refine ⟨f,?_,?_,?_⟩
  · apply Continuous.if _ continuous_const continuous_const
    intro y hy
    change y ∈ frontier (Ico a b) at hy
    rw [(sorgenfrey_isClopen_Ico a b).frontier_eq] at hy
    exact False.elim (notMem_empty y hy)
  · exact if_pos hxV
  · intro y hy
    have hn : y ∉ Ico a b := fun h => hy (hVU h)
    exact if_neg hn

instance : T35Space Sorgenfrey := {}

abbrev SorgenfreyCompactification := StoneCech Sorgenfrey

def sorgenfreyCompactificationMap : Sorgenfrey → SorgenfreyCompactification := stoneCechUnit

theorem sorgenfreyCompactificationMap_embedding : IsEmbedding sorgenfreyCompactificationMap :=
  isEmbedding_stoneCechUnit

end PointCentralFubini
