import CoreCompactNonSober.AmbientTopology
import Mathlib.Topology.UniformSpace.UniformApproximation
import Mathlib.Topology.MetricSpace.Pseudo.Basic

/-!
# Joint continuity of the ambient meet

Source: the uniform finite-coordinate approximation in `lem:lattice`.
The cutoff is reindexed: `meetApprox n` tests coordinates `2,...,n+1` and
its error is at most `1/(n+2)`. This is the same tail-loss estimate used in
the manuscript, including height truncation at zero.
-/

set_option autoImplicit false

namespace CoreCompactNonSober.Ambient

open Set Filter TopologicalSpace
open scoped Topology

noncomputable def meetApprox : ℕ → (Carrier × Carrier) → ℝ
  | 0, pq => min (height pq.1) (height pq.2)
  | n + 1, pq => min (meetApprox n pq)
      (capacity ⟨n + 2, by omega⟩
        (configuration pq.1 ⟨n + 2, by omega⟩ ∩
          configuration pq.2 ⟨n + 2, by omega⟩))

theorem meetApprox_nonneg (n : ℕ) (pq : Carrier × Carrier) :
    0 ≤ meetApprox n pq := by
  induction n with
  | zero => exact le_min pq.1.val.1.property.1 pq.2.val.1.property.1
  | succ n ih => exact le_min ih (capacity_nonneg _ _)

theorem meetApprox_le_min (n : ℕ) (pq : Carrier × Carrier) :
    meetApprox n pq ≤ min (height pq.1) (height pq.2) := by
  induction n with
  | zero => exact le_rfl
  | succ n ih => exact (min_le_left _ _).trans ih

theorem meetApprox_le_capacity (n : ℕ) (pq : Carrier × Carrier)
    (j : Coordinate) (hj : j.val ≤ n + 1) :
    meetApprox n pq ≤ capacity j (configuration pq.1 j ∩ configuration pq.2 j) := by
  induction n generalizing j with
  | zero => have := j.property; omega
  | succ n ih =>
    by_cases heq : j.val = n + 2
    · have heq' : j = (⟨n + 2, by omega⟩ : Coordinate) := Subtype.ext heq
      rw [heq']
      exact min_le_right _ _
    · exact (min_le_left _ _).trans (ih j (by omega))

theorem height_inf_le_meetApprox (n : ℕ) (pq : Carrier × Carrier) :
    height (pq.1 ⊓ pq.2) ≤ meetApprox n pq := by
  induction n with
  | zero =>
    exact le_min ((le_iff _ _).mp inf_le_left).1
      ((le_iff _ _).mp inf_le_right).1
  | succ n ih =>
    apply le_min ih
    have hcap := (pq.1 ⊓ pq.2).property (⟨n + 2, by omega⟩ : Coordinate)
    change height (pq.1 ⊓ pq.2) ≤ capacity ⟨n + 2, by omega⟩
      (configuration (pq.1 ⊓ pq.2) ⟨n + 2, by omega⟩) at hcap
    rw [configuration_inf] at hcap
    exact hcap

theorem min_height_sub_inv_le_capacity (pq : Carrier × Carrier) (j : Coordinate) :
    min (height pq.1) (height pq.2) - 1 / (j.val : ℝ) ≤
      capacity j (configuration pq.1 j ∩ configuration pq.2 j) := by
  have hloss := (capacity_intersection_loss j
    (configuration pq.1 j) (configuration pq.2 j)).2
  have hmin : min (height pq.1) (height pq.2) ≤
      min (capacity j (configuration pq.1 j)) (capacity j (configuration pq.2 j)) :=
    min_le_min (pq.1.property j) (pq.2.property j)
  linarith

/-- A finite approximation exceeds the actual meet height by at most its
tail bound. The proof constructs an admissible common lower bound; it does
not assume any continuity or formula for an infinite real infimum. -/
theorem meetApprox_sub_height_inf_le (n : ℕ) (pq : Carrier × Carrier) :
    meetApprox n pq - height (pq.1 ⊓ pq.2) ≤ 1 / ((n + 2 : ℕ) : ℝ) := by
  let d : ℝ := 1 / ((n + 2 : ℕ) : ℝ)
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hmin := meetApprox_le_min n pq
  have hlow_min : max 0 (meetApprox n pq - d) ≤ min (height pq.1) (height pq.2) := by
    apply max_le
    · exact le_min pq.1.val.1.property.1 pq.2.val.1.property.1
    · linarith
  have hlow_one : max 0 (meetApprox n pq - d) ≤ 1 :=
    hlow_min.trans ((min_le_left _ _).trans pq.1.val.1.property.2)
  have hadmissible : ∀ j : Coordinate,
      max 0 (meetApprox n pq - d) ≤
        capacity j (configuration pq.1 j ∩ configuration pq.2 j) := by
    intro j
    apply max_le (capacity_nonneg _ _)
    by_cases hj : j.val ≤ n + 1
    · have hhead := meetApprox_le_capacity n pq j hj
      linarith
    · have hjtail : n + 2 ≤ j.val := by omega
      have hinv : 1 / (j.val : ℝ) ≤ d :=
        one_div_le_one_div_of_le (by positivity) (by exact_mod_cast hjtail)
      have htail := min_height_sub_inv_le_capacity pq j
      linarith
  let low : Carrier :=
    ⟨(⟨max 0 (meetApprox n pq - d), le_max_left _ _, hlow_one⟩,
      fun j ↦ configuration pq.1 j ∩ configuration pq.2 j), hadmissible⟩
  have hlow_left : low ≤ pq.1 :=
    (le_iff _ _).mpr ⟨hlow_min.trans (min_le_left _ _), fun _ ↦ Finset.inter_subset_left⟩
  have hlow_right : low ≤ pq.2 :=
    (le_iff _ _).mpr ⟨hlow_min.trans (min_le_right _ _), fun _ ↦ Finset.inter_subset_right⟩
  have hheight : max 0 (meetApprox n pq - d) ≤ height (pq.1 ⊓ pq.2) :=
    ((le_iff low _).mp (le_inf hlow_left hlow_right)).1
  have hraw : meetApprox n pq - d ≤ max 0 (meetApprox n pq - d) := le_max_right _ _
  change meetApprox n pq - height (pq.1 ⊓ pq.2) ≤ d
  linarith

theorem continuous_inter_configuration (j : Coordinate) :
    Continuous (fun pq : Carrier × Carrier ↦
      configuration pq.1 j ∩ configuration pq.2 j) :=
  (continuous_of_discreteTopology
    (f := fun ab : Finset (Alphabet j) × Finset (Alphabet j) ↦ ab.1 ∩ ab.2)).comp
      (((continuous_configuration j).comp continuous_fst).prodMk
        ((continuous_configuration j).comp continuous_snd))

theorem continuous_meetApprox (n : ℕ) : Continuous (meetApprox n) := by
  induction n with
  | zero =>
    change Continuous (fun pq : Carrier × Carrier ↦ min (height pq.1) (height pq.2))
    exact (continuous_height.comp continuous_fst).min (continuous_height.comp continuous_snd)
  | succ n ih =>
    exact ih.min ((continuous_of_discreteTopology (f := capacity ⟨n + 2, by omega⟩)).comp
      (continuous_inter_configuration ⟨n + 2, by omega⟩))

theorem meetApprox_tendstoUniformly :
    TendstoUniformly meetApprox (fun pq : Carrier × Carrier ↦ height (pq.1 ⊓ pq.2)) atTop := by
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
  have hNmul : 1 < (N : ℝ) * ε := (div_lt_iff₀ hε).mp hN
  filter_upwards [eventually_ge_atTop N] with n hn
  intro pq
  have hnreal : (N : ℝ) ≤ ((n + 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : N ≤ n + 2)
  have hsmall : 1 / ((n + 2 : ℕ) : ℝ) < ε := by
    apply (div_lt_iff₀ (by positivity)).mpr
    nlinarith
  rw [Real.dist_eq, abs_sub_comm,
    abs_of_nonneg (sub_nonneg.mpr (height_inf_le_meetApprox n pq))]
  exact (meetApprox_sub_height_inf_le n pq).trans_lt hsmall

theorem continuous_height_inf :
    Continuous (fun pq : Carrier × Carrier ↦ height (pq.1 ⊓ pq.2)) :=
  meetApprox_tendstoUniformly.continuous
    (Filter.Eventually.of_forall continuous_meetApprox).frequently

/-- The binary meet operation is jointly continuous for `τ`, completing
the lattice-operation continuity assertion in `lem:lattice`. -/
instance auxiliaryContinuousInf : ContinuousInf Carrier where
  continuous_inf := by
    apply continuous_induced_rng.mpr
    change Continuous (fun pq : Carrier × Carrier ↦ (pq.1 ⊓ pq.2).val)
    have hh : Continuous (fun pq : Carrier × Carrier ↦ (pq.1 ⊓ pq.2).val.1) :=
      continuous_induced_rng.mpr continuous_height_inf
    have hc : Continuous (fun pq : Carrier × Carrier ↦ (pq.1 ⊓ pq.2).val.2) := by
      apply continuous_pi
      intro j
      have heq : (fun pq : Carrier × Carrier ↦ configuration (pq.1 ⊓ pq.2) j) =
          (fun pq : Carrier × Carrier ↦ configuration pq.1 j ∩ configuration pq.2 j) := by
        funext pq
        exact configuration_inf _ _ j
      change Continuous (fun pq : Carrier × Carrier ↦ configuration (pq.1 ⊓ pq.2) j)
      rw [heq]
      exact continuous_inter_configuration j
    exact hh.prodMk hc

end CoreCompactNonSober.Ambient
