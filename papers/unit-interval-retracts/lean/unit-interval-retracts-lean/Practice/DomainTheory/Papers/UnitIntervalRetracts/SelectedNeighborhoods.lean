import Practice.DomainTheory.Papers.UnitIntervalRetracts.Neighborhoods
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# A coherently shrinking skeleton neighbourhood sequence

This file implements the recursive choice following
`eq:N-properties`--`eq:N-intersection` in the source.  Each successor is
chosen inside both the relative interior of its predecessor and a metric ball
whose radius tends to zero.
-/

set_option autoImplicit false
set_option linter.unnecessarySimpa false

namespace UnitIntervalRetracts

open Set Filter Topology

noncomputable section

/-- State carried by the recursive neighbourhood choice. -/
def NeighborhoodState (x : X) :=
  {A : P // x ∈ interior (A : Set X) ∧ (A : Set X) ∈ Skeleton}

/-- The open set in which the next skeleton neighbourhood is selected. -/
def nextNeighborhoodOpen (x : X) (n : ℕ) (A : P) : Set X :=
  interior (A : Set X) ∩
    Metric.ball x (1 / ((n : ℝ) + 2))

theorem isOpen_nextNeighborhoodOpen (x : X) (n : ℕ) (A : P) :
    IsOpen (nextNeighborhoodOpen x n A) :=
  isOpen_interior.inter Metric.isOpen_ball

theorem mem_nextNeighborhoodOpen {x : X} {n : ℕ} {A : P}
    (hx : x ∈ interior (A : Set X)) :
    x ∈ nextNeighborhoodOpen x n A := by
  constructor
  · exact hx
  · rw [Metric.mem_ball, dist_self]
    positivity

/-- One recursive step, with all properties needed later exposed explicitly. -/
theorem exists_next_neighborhood (x : X) (n : ℕ) (state : NeighborhoodState x) :
    ∃ B : P,
      x ∈ interior (B : Set X) ∧
      (B : Set X) ∈ Skeleton ∧
      (B : Set X) ⊆ interior (state.1 : Set X) ∧
      (B : Set X) ⊆ Metric.ball x (1 / ((n : ℝ) + 2)) := by
  obtain ⟨B, hB, hxB, hBsub⟩ :=
    exists_skeleton_closed_neighborhood
      (isOpen_nextNeighborhoodOpen x n state.1)
      (mem_nextNeighborhoodOpen state.2.1)
  refine ⟨ofSkeleton hB, ?_, ?_, ?_, ?_⟩
  · simpa using hxB
  · simpa using hB
  · intro y hy
    exact (hBsub hy).1
  · intro y hy
    exact (hBsub hy).2

/-- Initial skeleton neighbourhood, selected inside the whole interval. -/
noncomputable def initialNeighborhoodState (x : X) : NeighborhoodState x :=
  let witness :=
    exists_skeleton_closed_neighborhood (x := x) (O := Set.univ)
      isOpen_univ (Set.mem_univ x)
  let B : Set X := witness.choose
  let hB : B ∈ Skeleton := witness.choose_spec.1
  ⟨ofSkeleton hB, by
    simpa [B] using witness.choose_spec.2.1,
    by simpa [B] using hB⟩

/-- The chosen successor state. -/
noncomputable def nextNeighborhoodState
    (x : X) (n : ℕ) (state : NeighborhoodState x) :
    NeighborhoodState x :=
  ⟨(exists_next_neighborhood x n state).choose,
    (exists_next_neighborhood x n state).choose_spec.1,
    (exists_next_neighborhood x n state).choose_spec.2.1⟩

theorem nextNeighborhoodState_subset_interior
    (x : X) (n : ℕ) (state : NeighborhoodState x) :
    ((nextNeighborhoodState x n state).1 : Set X) ⊆
      interior (state.1 : Set X) :=
  (exists_next_neighborhood x n state).choose_spec.2.2.1

theorem nextNeighborhoodState_subset_ball
    (x : X) (n : ℕ) (state : NeighborhoodState x) :
    ((nextNeighborhoodState x n state).1 : Set X) ⊆
      Metric.ball x (1 / ((n : ℝ) + 2)) :=
  (exists_next_neighborhood x n state).choose_spec.2.2.2

/-- Recursive realization of the manuscript's sequence `N_m(x)`.

The source starts indexing at one.  We use zero-based Lean indexing; this is a
harmless reindexing, and all successor/radius statements below record the exact
correspondence.
-/
noncomputable def neighborhoodState (x : X) : ℕ → NeighborhoodState x
  | 0 => initialNeighborhoodState x
  | n + 1 => nextNeighborhoodState x n (neighborhoodState x n)

/-- The selected sparse interval element. -/
noncomputable def selectedNeighborhood (x : X) (n : ℕ) : P :=
  (neighborhoodState x n).1

theorem selectedNeighborhood_mem_skeleton (x : X) (n : ℕ) :
    (selectedNeighborhood x n : Set X) ∈ Skeleton :=
  (neighborhoodState x n).2.2

theorem point_mem_interior_selectedNeighborhood (x : X) (n : ℕ) :
    x ∈ interior (selectedNeighborhood x n : Set X) :=
  (neighborhoodState x n).2.1

theorem selectedNeighborhood_succ_subset_interior (x : X) (n : ℕ) :
    (selectedNeighborhood x (n + 1) : Set X) ⊆
      interior (selectedNeighborhood x n : Set X) := by
  exact nextNeighborhoodState_subset_interior x n (neighborhoodState x n)

theorem selectedNeighborhood_succ_subset_ball (x : X) (n : ℕ) :
    (selectedNeighborhood x (n + 1) : Set X) ⊆
      Metric.ball x (1 / ((n : ℝ) + 2)) := by
  exact nextNeighborhoodState_subset_ball x n (neighborhoodState x n)

theorem selectedNeighborhood_succ_diam_bound (x : X) (n : ℕ) :
    Metric.diam (selectedNeighborhood x (n + 1) : Set X) ≤
      2 * (1 / ((n : ℝ) + 2)) := by
  exact
    (Metric.diam_mono (selectedNeighborhood_succ_subset_ball x n)
      Metric.isBounded_ball).trans
      (Metric.diam_ball (by positivity))

theorem tendsto_selectedNeighborhood_radius :
    Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 2))
      atTop (𝓝 0) := by
  simpa [Nat.cast_add] using
    ((tendsto_add_atTop_iff_nat 2).2
      (tendsto_one_div_atTop_nhds_zero_nat :
        Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ))
          atTop (𝓝 0))
      )

/-- Equation `eq:N-intersection`, with the zero-based indexing used here. -/
theorem selectedNeighborhood_intersection (x : X) :
    ⋂₀ ((fun A : P => (A : Set X)) '' Set.range (selectedNeighborhood x)) =
      ({x} : Set X) := by
  apply Set.Subset.antisymm
  · intro y hy
    have hyAll : ∀ n : ℕ, y ∈ (selectedNeighborhood x n : Set X) := by
      intro n
      apply hy
      exact
        ⟨selectedNeighborhood x n, ⟨n, rfl⟩, rfl⟩
    have hdist :
        ∀ n : ℕ, dist y x ≤ (1 : ℝ) / ((n : ℝ) + 2) := by
      intro n
      exact
        (selectedNeighborhood_succ_subset_ball x n (hyAll (n + 1))).le
    have hdistZero : dist y x ≤ 0 :=
      ge_of_tendsto tendsto_selectedNeighborhood_radius
        (Eventually.of_forall hdist)
    have hyx : y = x :=
      dist_eq_zero.mp (le_antisymm hdistZero dist_nonneg)
    simpa [hyx]
  · intro y hy
    have hyx : y = x := by simpa using hy
    subst y
    intro A hA
    rcases hA with ⟨B, ⟨n, hn⟩, hB⟩
    subst B
    subst A
    exact interior_subset (point_mem_interior_selectedNeighborhood x n)

end

end UnitIntervalRetracts
