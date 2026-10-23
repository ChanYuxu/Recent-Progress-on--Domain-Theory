import CantorFubini.SourceModel

/-! Unnumbered mathematical consequences of the printed kernel condition. -/
set_option autoImplicit false
open Set Topology TopologicalSpace MeasureTheory Filter
namespace CantorFubini

theorem kernel_condition_closed {K : Set Cantor} {x : Cantor}
    (hK : CantorKernelCondition K x) : IsClosed K := (kernel_condition_compact hK).isClosed

theorem kernel_condition_null {K : Set Cantor} {x : Cantor}
    (hK : CantorKernelCondition K x) : cantorMeasure K = 0 :=
  cantorMeasure_countable (kernel_condition_countable hK)

theorem kernel_condition_accumulation_unique {K : Set Cantor} {x y : Cantor}
    (hK : CantorKernelCondition K x) (hy : AccPt y (Filter.principal K)) : y = x := by
  by_contra hyx
  obtain ⟨U, V, hU, hV, hxU, hyV, hUV⟩ := t2_separation (Ne.symm hyx)
  have hf : (V ∩ K).Finite :=
    (((kernel_condition_iff K x).mp hK).2 U hU hxU).subset (by
      rintro z ⟨hzV, hzK⟩
      exact ⟨hzK, fun hzU => disjoint_left.mp hUV hzU hzV⟩)
  exact Set.Infinite.of_accPt (hy.nhds_inter (hV.mem_nhds hyV)) hf

end CantorFubini
