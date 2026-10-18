import CoreCompactNonSober.AmbientLattice
import CoreCompactNonSober.CompactOrderedConvergence
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Metrizable.Urysohn
import Mathlib.Topology.Order.Lattice
import Mathlib.Topology.Instances.Discrete
import Mathlib.Topology.Bases

/-!
# The auxiliary compact Hausdorff topology

Source: the auxiliary topology `τ` of `lem:lattice`. Each finite coordinate
space is discrete, heights carry the usual real topology, and the ambient
carrier carries the subtype topology. This is an auxiliary topology only;
the canonical Scott topology remains the order-determined `scottTopology`.
-/

set_option autoImplicit false

namespace CoreCompactNonSober.Ambient

open Set TopologicalSpace

instance coordinateTopology (j : Coordinate) :
    TopologicalSpace (Finset (Alphabet j)) := ⊥

instance coordinateDiscreteTopology (j : Coordinate) :
    DiscreteTopology (Finset (Alphabet j)) := ⟨rfl⟩

instance coordinateOrderClosedTopology (j : Coordinate) :
    OrderClosedTopology (Finset (Alphabet j)) where
  isClosed_le' := isClosed_discrete _

/-- The actual product/subtype topology from the manuscript. -/
instance auxiliaryTopology : TopologicalSpace Carrier :=
  inferInstanceAs (TopologicalSpace
    {p : Height × Configuration // ∀ j, (p.1 : ℝ) ≤ capacity j (p.2 j)})

theorem carrier_isClosed :
    IsClosed {p : Height × Configuration | ∀ j, (p.1 : ℝ) ≤ capacity j (p.2 j)} := by
  simp only [Set.setOf_forall]
  apply isClosed_iInter
  intro j
  exact isClosed_le (continuous_subtype_val.comp continuous_fst)
    ((continuous_of_discreteTopology (f := capacity j)).comp
      ((continuous_apply j).comp continuous_snd))

instance auxiliaryCompactSpace : CompactSpace Carrier :=
  isCompact_iff_compactSpace.mp carrier_isClosed.isCompact

instance auxiliaryT2Space : T2Space Carrier :=
  inferInstanceAs (T2Space
    {p : Height × Configuration // ∀ j, (p.1 : ℝ) ≤ capacity j (p.2 j)})

instance auxiliarySecondCountable : SecondCountableTopology Carrier := by
  haveI : SecondCountableTopology Height := inferInstance
  haveI : ∀ j : Coordinate, SecondCountableTopology (Finset (Alphabet j)) :=
    fun j ↦ inferInstance
  haveI : SecondCountableTopology Configuration := inferInstance
  haveI : SecondCountableTopology (Height × Configuration) := inferInstance
  exact TopologicalSpace.secondCountableTopology_induced
    Carrier (Height × Configuration) Subtype.val

instance auxiliaryMetrizable : MetrizableSpace Carrier := by
  infer_instance

instance auxiliaryOrderClosed : OrderClosedTopology Carrier :=
  inferInstanceAs (OrderClosedTopology
    {p : Height × Configuration // ∀ j, (p.1 : ℝ) ≤ capacity j (p.2 j)})

instance auxiliarySupConvergence : SupConvergenceClass Carrier :=
  CoreCompactNonSober.compact_supConvergenceClass

instance auxiliaryInfConvergence : InfConvergenceClass Carrier :=
  CoreCompactNonSober.compact_infConvergenceClass

theorem continuous_height : Continuous height :=
  continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val)

theorem continuous_configuration (j : Coordinate) :
    Continuous (fun p : Carrier ↦ configuration p j) :=
  (continuous_apply j).comp (continuous_snd.comp continuous_subtype_val)

theorem height_sup_interval (p q : Carrier) :
    (p ⊔ q).val.1 = p.val.1 ⊔ q.val.1 := by
  rw [← sSup_pair, height_sSup_interval, Set.image_pair, sSup_pair]

theorem configuration_sup (p q : Carrier) (j : Coordinate) :
    configuration (p ⊔ q) j = configuration p j ∪ configuration q j := by
  rw [← sSup_pair, configuration_sSup, Set.image_pair, sSup_pair]
  rfl

/-- Binary join is jointly continuous for the auxiliary topology. -/
instance auxiliaryContinuousSup : ContinuousSup Carrier where
  continuous_sup := by
    apply continuous_induced_rng.mpr
    change Continuous (fun pq : Carrier × Carrier ↦ (pq.1 ⊔ pq.2).val)
    have heq : (fun pq : Carrier × Carrier ↦ (pq.1 ⊔ pq.2).val) =
        (fun pq : Carrier × Carrier ↦
          (pq.1.val.1 ⊔ pq.2.val.1,
            fun j ↦ configuration pq.1 j ∪ configuration pq.2 j)) := by
      funext pq
      apply Prod.ext
      · exact height_sup_interval _ _
      · funext j
        exact configuration_sup _ _ j
    rw [heq]
    apply Continuous.prodMk
    · exact (continuous_fst.comp (continuous_subtype_val.comp continuous_fst)).sup
        (continuous_fst.comp (continuous_subtype_val.comp continuous_snd))
    · apply continuous_pi
      intro j
      exact (continuous_of_discreteTopology
        (f := fun ab : Finset (Alphabet j) × Finset (Alphabet j) ↦ ab.1 ∪ ab.2)).comp
          ((continuous_configuration j).comp continuous_fst |>.prodMk
            ((continuous_configuration j).comp continuous_snd))

end CoreCompactNonSober.Ambient
