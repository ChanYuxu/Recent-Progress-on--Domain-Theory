import CoreCompactNonSober.AmbientDefinitions
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.GCongr
import Mathlib.Algebra.Order.Floor.Semiring

/-!
# Logarithmic capacities and the loss lemma

Source: Section 3.1, `eq:capacity`, `lem:loss`. The capacity is the exact
previously reviewed definition. The helper indexed by a natural hole count
is used only to prove properties of that definition.
-/

set_option autoImplicit false

namespace CoreCompactNonSober.Ambient

theorem coordinate_pos (j : Coordinate) : 0 < j.val := by
  have := j.property
  omega

theorem coordinate_real_pos (j : Coordinate) : 0 < (j.val : ℝ) := by
  exact_mod_cast coordinate_pos j

theorem coordinate_inv_nonneg (j : Coordinate) : 0 ≤ 1 / (j.val : ℝ) :=
  le_of_lt (one_div_pos.mpr (coordinate_real_pos j))

/-- The numerical capacity as a function of the number of holes. -/
noncomputable def capacityFromHoles (j : Coordinate) (k : ℕ) : ℝ :=
  max 0 (1 - (1 / (j.val : ℝ)) * Real.logb 2 (1 + (k : ℝ)))

theorem capacity_eq_fromHoles (j : Coordinate) (A : Finset (Alphabet j)) :
    capacity j A = capacityFromHoles j (holeCount j A) :=
  rfl

theorem capacityFromHoles_nonneg (j : Coordinate) (k : ℕ) :
    0 ≤ capacityFromHoles j k :=
  le_max_left _ _

theorem capacityFromHoles_le_one (j : Coordinate) (k : ℕ) :
    capacityFromHoles j k ≤ 1 := by
  have hlog : 0 ≤ Real.logb 2 (1 + (k : ℝ)) :=
    Real.logb_nonneg (by norm_num) (by have := Nat.cast_nonneg (α := ℝ) k; linarith)
  have hprod := mul_nonneg (coordinate_inv_nonneg j) hlog
  exact max_le (by norm_num) (by linarith)

theorem capacityFromHoles_antitone (j : Coordinate) :
    Antitone (capacityFromHoles j) := by
  intro k l hkl
  have hlog : Real.logb 2 (1 + (k : ℝ)) ≤ Real.logb 2 (1 + (l : ℝ)) :=
    Real.logb_le_logb_of_le (by norm_num) (by positivity) (by exact_mod_cast Nat.add_le_add_left hkl 1)
  have hmul := mul_le_mul_of_nonneg_left hlog (coordinate_inv_nonneg j)
  exact max_le_max le_rfl (by linarith)

theorem capacity_nonneg (j : Coordinate) (A : Finset (Alphabet j)) :
    0 ≤ capacity j A :=
  capacityFromHoles_nonneg j _

theorem capacity_le_one (j : Coordinate) (A : Finset (Alphabet j)) :
    capacity j A ≤ 1 :=
  capacityFromHoles_le_one j _

theorem holeCount_antitone (j : Coordinate) : Antitone (holeCount j) := by
  intro A B hAB
  apply Finset.card_le_card
  intro z hz
  simp only [Finset.mem_sdiff] at hz ⊢
  exact ⟨hz.1, fun hzA ↦ hz.2 (hAB hzA)⟩

theorem capacity_monotone (j : Coordinate) : Monotone (capacity j) := by
  intro A B hAB
  exact capacityFromHoles_antitone j (holeCount_antitone j hAB)

@[simp] theorem capacity_univ (j : Coordinate) :
    capacity j Finset.univ = 1 := by
  simp [capacity, holeCount, Real.logb_one]

/-- A hole-count increase by at most a factor of two plus one loses at most
`1/j` of capacity; zero truncation is included in this inequality. -/
theorem capacityFromHoles_loss (j : Coordinate) (k l : ℕ)
    (hl : l ≤ 2 * k + 1) :
    capacityFromHoles j k - capacityFromHoles j l ≤ 1 / (j.val : ℝ) := by
  have harg : 1 + (l : ℝ) ≤ 2 * (1 + (k : ℝ)) := by
    have h : (l : ℝ) ≤ 2 * (k : ℝ) + 1 := by exact_mod_cast hl
    linarith
  have hlog := Real.logb_le_logb_of_le (b := (2 : ℝ)) (by norm_num)
    (by positivity : 0 < 1 + (l : ℝ)) harg
  have hlog2 : Real.logb 2 (2 * (1 + (k : ℝ))) = 1 + Real.logb 2 (1 + (k : ℝ)) := by
    rw [Real.logb_mul (by norm_num) (by positivity), Real.logb_self_eq_one (by norm_num)]
  rw [hlog2] at hlog
  have hmul := mul_le_mul_of_nonneg_left hlog (coordinate_inv_nonneg j)
  have hraw :
      1 - (1 / (j.val : ℝ)) * Real.logb 2 (1 + (k : ℝ)) ≤
        (1 - (1 / (j.val : ℝ)) * Real.logb 2 (1 + (l : ℝ))) + 1 / (j.val : ℝ) := by
    linarith
  have hlraw : 1 - (1 / (j.val : ℝ)) * Real.logb 2 (1 + (l : ℝ)) ≤
      capacityFromHoles j l := le_max_right _ _
  have hbound : capacityFromHoles j k ≤ capacityFromHoles j l + 1 / (j.val : ℝ) := by
    apply max_le
    · exact add_nonneg (capacityFromHoles_nonneg j l) (coordinate_inv_nonneg j)
    · linarith
  linarith

theorem holeCount_sdiff_singleton_le (j : Coordinate)
    (A : Finset (Alphabet j)) (z : Alphabet j) :
    holeCount j (A \ {z}) ≤ holeCount j A + 1 := by
  have hsub : Finset.univ \ (A \ {z}) ⊆ (Finset.univ \ A) ∪ {z} := by
    intro a ha
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and,
      Finset.mem_union, Finset.mem_singleton, not_and_or, not_not] at ha ⊢
    exact ha
  exact (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans (by simp [holeCount]))

/-- Source `eq:deletion-loss`. -/
theorem capacity_deletion_loss (j : Coordinate)
    (A : Finset (Alphabet j)) (z : Alphabet j) :
    0 ≤ capacity j A - capacity j (A \ {z}) ∧
      capacity j A - capacity j (A \ {z}) ≤ 1 / (j.val : ℝ) := by
  constructor
  · exact sub_nonneg.mpr (capacity_monotone j Finset.sdiff_subset)
  · apply capacityFromHoles_loss
    have h := holeCount_sdiff_singleton_le j A z
    omega

theorem holeCount_inter_le (j : Coordinate) (A B : Finset (Alphabet j)) :
    holeCount j (A ∩ B) ≤ holeCount j A + holeCount j B := by
  unfold holeCount
  rw [Finset.sdiff_inter_distrib_right]
  exact Finset.card_union_le _ _

theorem min_capacity_eq_max_holes (j : Coordinate)
    (A B : Finset (Alphabet j)) :
    min (capacity j A) (capacity j B) =
      capacityFromHoles j (max (holeCount j A) (holeCount j B)) := by
  rw [capacity_eq_fromHoles, capacity_eq_fromHoles]
  rcases le_total (holeCount j A) (holeCount j B) with h | h
  · rw [max_eq_right h, min_eq_right (capacityFromHoles_antitone j h)]
  · rw [max_eq_left h, min_eq_left (capacityFromHoles_antitone j h)]

/-- Source `eq:intersection-loss`. -/
theorem capacity_intersection_loss (j : Coordinate)
    (A B : Finset (Alphabet j)) :
    0 ≤ min (capacity j A) (capacity j B) - capacity j (A ∩ B) ∧
      min (capacity j A) (capacity j B) - capacity j (A ∩ B) ≤ 1 / (j.val : ℝ) := by
  constructor
  · exact sub_nonneg.mpr (le_min
      (capacity_monotone j Finset.inter_subset_left)
      (capacity_monotone j Finset.inter_subset_right))
  · rw [min_capacity_eq_max_holes, capacity_eq_fromHoles]
    apply capacityFromHoles_loss
    have h := holeCount_inter_le j A B
    have ha := le_max_left (holeCount j A) (holeCount j B)
    have hb := le_max_right (holeCount j A) (holeCount j B)
    omega

/-- The exact combined statement of the manuscript's first numbered lemma. -/
theorem capacity_loss (j : Coordinate)
    (A B : Finset (Alphabet j)) (z : Alphabet j) :
    (0 ≤ capacity j A - capacity j (A \ {z}) ∧
      capacity j A - capacity j (A \ {z}) ≤ 1 / (j.val : ℝ)) ∧
    (0 ≤ min (capacity j A) (capacity j B) - capacity j (A ∩ B) ∧
      min (capacity j A) (capacity j B) - capacity j (A ∩ B) ≤ 1 / (j.val : ℝ)) :=
  ⟨capacity_deletion_loss j A z, capacity_intersection_loss j A B⟩

/-- At a positive level, the zero truncation can be removed exactly. -/
theorem capacityFromHoles_ge_iff_log (j : Coordinate) (k : ℕ)
    {r : ℝ} (hr : 0 < r) :
    r ≤ capacityFromHoles j k ↔
      Real.logb 2 (1 + (k : ℝ)) ≤ (1 - r) * (j.val : ℝ) := by
  have hj := coordinate_real_pos j
  rw [capacityFromHoles, le_max_iff]
  have hdiv : (1 / (j.val : ℝ)) * Real.logb 2 (1 + (k : ℝ)) =
      Real.logb 2 (1 + (k : ℝ)) / (j.val : ℝ) := by
    rw [div_mul_eq_mul_div, one_mul]
  rw [hdiv]
  constructor
  · rintro (h | h)
    · exact False.elim (not_le_of_gt hr h)
    · exact (div_le_iff₀ hj).mp (by linarith)
  · intro h
    right
    have := (div_le_iff₀ hj).mpr h
    linarith

theorem capacity_ge_iff_rpow (j : Coordinate) (A : Finset (Alphabet j))
    {r : ℝ} (hr : 0 < r) :
    r ≤ capacity j A ↔
      1 + (holeCount j A : ℝ) ≤ (2 : ℝ) ^ ((1 - r) * (j.val : ℝ)) := by
  rw [capacity_eq_fromHoles, capacityFromHoles_ge_iff_log j _ hr]
  exact Real.logb_le_iff_le_rpow (by norm_num) (by positivity)

/-- Source `q_r(j) = floor(2^((1-r)j)) - 1`. This natural-valued version
is used only on `0 < r ≤ 1`, where the floor is at least one. -/
noncomputable def holeBound (r : ℝ) (j : Coordinate) : ℕ :=
  Nat.floor ((2 : ℝ) ^ ((1 - r) * (j.val : ℝ))) - 1

/-- The exact positive-level hole-count equivalence in `eq:hole-bound`. -/
theorem capacity_ge_iff_holeBound (j : Coordinate) (A : Finset (Alphabet j))
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    r ≤ capacity j A ↔ holeCount j A ≤ holeBound r j := by
  have hexp : 0 ≤ (1 - r) * (j.val : ℝ) :=
    mul_nonneg (sub_nonneg.mpr hr1) (le_of_lt (coordinate_real_pos j))
  have hpow : 1 ≤ (2 : ℝ) ^ ((1 - r) * (j.val : ℝ)) :=
    Real.one_le_rpow (by norm_num) hexp
  have hfloor : 1 ≤ Nat.floor ((2 : ℝ) ^ ((1 - r) * (j.val : ℝ))) :=
    Nat.le_floor (by simpa using hpow)
  rw [capacity_ge_iff_rpow j A hr]
  have hnat :
      (1 + (holeCount j A : ℝ) ≤ (2 : ℝ) ^ ((1 - r) * (j.val : ℝ))) ↔
        holeCount j A + 1 ≤ Nat.floor ((2 : ℝ) ^ ((1 - r) * (j.val : ℝ))) := by
    rw [Nat.le_floor_iff (le_trans (by norm_num) hpow)]
    simp only [Nat.cast_add, Nat.cast_one, add_comm]
  rw [hnat]
  unfold holeBound
  omega

@[simp] theorem capacity_empty (j : Coordinate) : capacity j ∅ = 0 := by
  have hDpos : 0 < (alphabetSize j : ℝ) := by
    exact_mod_cast (pow_pos (by norm_num : 0 < (2 : ℕ)) (2 ^ j.val))
  have hlogD : Real.logb 2 (alphabetSize j : ℝ) = (2 ^ j.val : ℕ) := by
    simp only [alphabetSize, Nat.cast_pow, Nat.cast_ofNat, Real.logb_pow,
      Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one]
  have hlt : (j.val : ℝ) < (2 ^ j.val : ℕ) := by
    exact_mod_cast j.val.lt_two_pow_self
  have hlog : (j.val : ℝ) ≤ Real.logb 2 (1 + (alphabetSize j : ℝ)) := by
    have hmono := Real.logb_le_logb_of_le (b := (2 : ℝ)) (by norm_num) hDpos
      (by linarith : (alphabetSize j : ℝ) ≤ 1 + (alphabetSize j : ℝ))
    rw [hlogD] at hmono
    linarith
  have hmul := mul_le_mul_of_nonneg_left hlog (coordinate_inv_nonneg j)
  have hone : (1 / (j.val : ℝ)) * (j.val : ℝ) = 1 :=
    one_div_mul_cancel (ne_of_gt (coordinate_real_pos j))
  rw [hone] at hmul
  unfold capacity holeCount
  simp only [Finset.sdiff_empty, Finset.card_univ, Fintype.card_fin]
  exact max_eq_left (by linarith)

end CoreCompactNonSober.Ambient
