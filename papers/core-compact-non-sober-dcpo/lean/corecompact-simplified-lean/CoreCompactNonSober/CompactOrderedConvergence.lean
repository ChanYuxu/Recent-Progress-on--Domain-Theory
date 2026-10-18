import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.ClusterPt

/-!
# Monotone order convergence in compact ordered spaces

These are the compactness arguments used at the start of `lem:scott-ambient`.
They work with all nets, without a countability or linear-order restriction.
-/

set_option autoImplicit false

universe u

namespace CoreCompactNonSober

open Set Filter
open scoped Topology

variable {P : Type u} [PartialOrder P] [TopologicalSpace P]
  [CompactSpace P] [OrderClosedTopology P]

theorem compact_supConvergenceClass : SupConvergenceClass P := by
  constructor
  intro a E ha
  apply tendsto_nhds_of_unique_mapClusterPt
  intro b hb
  apply le_antisymm
  · exact isClosed_Iic.mem_of_mapClusterPt hb
      (Filter.Eventually.of_forall (fun e : E ↦ ha.1 e.property))
  · apply ha.2
    intro e he
    exact isClosed_Ici.mem_of_mapClusterPt hb
      (eventually_ge_atTop (⟨e, he⟩ : E))

theorem compact_infConvergenceClass : InfConvergenceClass P := by
  constructor
  intro a E ha
  apply tendsto_nhds_of_unique_mapClusterPt
  intro b hb
  apply le_antisymm
  · apply ha.2
    intro e he
    exact isClosed_Iic.mem_of_mapClusterPt hb
      (eventually_le_atBot (⟨e, he⟩ : E))
  · exact isClosed_Ici.mem_of_mapClusterPt hb
      (Filter.Eventually.of_forall (fun e : E ↦ ha.1 e.property))

end CoreCompactNonSober
