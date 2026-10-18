import Practice.DomainTheory.Papers.UnitIntervalRetracts.AbstractApproximation
import Practice.DomainTheory.Papers.UnitIntervalRetracts.Lattice
import Practice.DomainTheory.Papers.UnitIntervalRetracts.SelectedNeighborhoods

/-!
# The finite-family way-below relation in the sparse interval lattice

This file discharges every field of the abstract approximation interface using
the concrete lattice and neighbourhood construction, then exposes the exact
source-facing theorems.
-/

set_option autoImplicit false
set_option linter.unnecessarySimpa false

namespace UnitIntervalRetracts

open Set Filter Topology
open AbramskyJung.Chapter2

noncomputable section

/-- A directed family with nonempty, nonsingleton intersection is finite. -/
theorem finite_of_nonsingleton_directed_sSup
    {family : Set P}
    (_hDirected : DirectedSet family)
    (hNonempty : (((sSup family : P) : Set X)).Nonempty)
    (hNotSingleton : ∀ x : X, ((sSup family : P) : Set X) ≠ {x}) :
    family.Finite := by
  let S : Set X := ((sSup family : P) : Set X)
  have hSNontrivial : S.Nontrivial := by
    by_contra hnot
    have hSubsingleton : S.Subsingleton :=
      Set.not_nontrivial_iff.mp hnot
    rcases hNonempty with ⟨x, hx⟩
    exact hNotSingleton x (hSubsingleton.eq_singleton_of_mem hx)
  have hSBounded : Bornology.IsBounded S :=
    isBounded_subset_X S
  have hdiam : 0 < Metric.diam S :=
    Metric.diam_pos hSNontrivial hSBounded
  have hSubset (A : P) (hA : A ∈ family) :
      S ⊆ (A : Set X) := by
    change ((sSup family : P) : Set X) ⊆ (A : Set X)
    rw [coe_sSup_eq_carrierIntersection]
    exact carrierIntersection_subset hA
  have hSkeleton (A : P) (hA : A ∈ family) :
      (A : Set X) ∈ Skeleton := by
    rcases A.isSparse with hA_skeleton | ⟨x, hx⟩ | hempty
    · exact hA_skeleton
    · exfalso
      apply hSNontrivial.not_subset_singleton
      rw [← hx]
      exact hSubset A hA
    · exfalso
      apply hSNontrivial.not_subset_empty
      rw [← hempty]
      exact hSubset A hA
  have hCarrierImageFinite :
      ((fun A : P => (A : Set X)) '' family).Finite := by
    apply (skeleton_large_diameter_finite hdiam).subset
    intro B hB
    rcases hB with ⟨A, hAfamily, rfl⟩
    refine ⟨hSkeleton A hAfamily, ?_⟩
    exact
      Metric.diam_mono (hSubset A hAfamily)
        (isBounded_subset_X (A : Set X))
  exact
    Set.Finite.of_finite_image hCarrierImageFinite
      SetLike.coe_injective.injOn

/-- All concrete hypotheses for the abstract finite-approximation theorem. -/
def sparseIntervalData :
    AbstractApproximation.SparseIntervalData X P where
  realized := fun A => (A : Set X)
  le_iff_realized_reverse_subset := fun _ _ => le_def
  realized_top := coe_top
  sup := sSup
  sup_isSup := isLUB_sSup
  realized_sup := by
    intro family
    rw [coe_sSup_eq_carrierIntersection]
    ext x
    simp [carrierIntersection]
  point := singleton
  realized_point := coe_singleton
  neighborhood := selectedNeighborhood
  point_mem_interior := point_mem_interior_selectedNeighborhood
  neighborhood_step := selectedNeighborhood_succ_subset_interior
  neighborhood_intersection := selectedNeighborhood_intersection
  filtered_compactness := by
    intro family O hDirected hOpen hSubset
    apply filteredCompactness hDirected hOpen
    rw [← coe_sSup_eq_carrierIntersection]
    exact hSubset
  finite_of_nonsingleton_directed_sup := by
    intro family hDirected hNonempty hNotSingleton
    exact
      finite_of_nonsingleton_directed_sSup hDirected hNonempty hNotSingleton

/-- Theorem `thm:finite-way-below`, including the top clause. -/
theorem finiteWayBelow_iff (approximants : FiniteFamily P) (K : P) :
    FiniteWayBelow approximants K ↔
      (∃ A ∈ (approximants : Set P),
        (K : Set X) ⊆ (A : Set X)) ∧
      (K : Set X) ⊆
        ⋃ A ∈ (approximants : Set P), interior (A : Set X) :=
  AbstractApproximation.SparseIntervalData.finiteWayBelow_iff
    sparseIntervalData approximants K

theorem finiteWayBelow_top (approximants : FiniteFamily P) :
    FiniteWayBelow approximants (⊤ : P) :=
  AbstractApproximation.SparseIntervalData.finiteWayBelow_top
    sparseIntervalData approximants

/-- Corollary `cor:one-point-way-below`. -/
theorem wayBelow_iff_interior (A : P) {K : P} (hK : K ≠ ⊤) :
    A ≪ K ↔ (K : Set X) ⊆ interior (A : Set X) :=
  AbstractApproximation.SparseIntervalData.wayBelow_iff_interior
    sparseIntervalData A hK

end

end UnitIntervalRetracts
