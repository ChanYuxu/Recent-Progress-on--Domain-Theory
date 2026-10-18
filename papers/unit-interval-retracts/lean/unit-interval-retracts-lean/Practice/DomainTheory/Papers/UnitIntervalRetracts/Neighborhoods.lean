import Practice.DomainTheory.Papers.UnitIntervalRetracts.SparseInterval
import Mathlib.Topology.Perfect

/-!
# Closed neighborhoods from the dyadic interval skeleton

This file proves `lem:closed-neighbourhood-base` from the source manuscript.
The proof uses the floor dyadic at a sufficiently fine level.  This is a
source-equivalent witness for the manuscript's "nearest dyadic" choice.
-/

set_option autoImplicit false
set_option linter.unnecessarySimpa false

namespace UnitIntervalRetracts

open Set Filter Topology

noncomputable section

/-- The radius `2⁻ⁿ` of a basic source interval. -/
def basicRadius (i : BasicIndex) : ℝ :=
  1 / (2 : ℝ) ^ i.level

/-- The dyadic center `k / 2ⁿ` of a basic source interval. -/
def basicCenter (i : BasicIndex) : ℝ :=
  (i.position : ℝ) / (2 : ℝ) ^ i.level

theorem basicRadius_pos (i : BasicIndex) : 0 < basicRadius i := by
  exact div_pos zero_lt_one (pow_pos (by norm_num) i.level)

theorem basicLeft_eq_center_sub (i : BasicIndex) :
    basicLeft i = basicCenter i - basicRadius i := by
  simp only [basicLeft, basicCenter, basicRadius]
  ring

theorem basicRight_eq_center_add (i : BasicIndex) :
    basicRight i = basicCenter i + basicRadius i := by
  simp only [basicRight, basicCenter, basicRadius]
  ring

/-- The floor dyadic index at level `n`. -/
def floorIndex (x : X) (n : ℕ) (hn : 1 ≤ n) : BasicIndex :=
  ⟨(n, ⌊(2 : ℝ) ^ n * (x : ℝ)⌋₊), hn, by
    apply Nat.floor_le_of_le
    have hpow : 0 ≤ (2 : ℝ) ^ n := by positivity
    calc
      (2 : ℝ) ^ n * (x : ℝ) ≤ (2 : ℝ) ^ n * 1 :=
        mul_le_mul_of_nonneg_left x.2.2 hpow
      _ = ((2 ^ n : ℕ) : ℝ) := by norm_num⟩

theorem floorIndex_center_le (x : X) (n : ℕ) (hn : 1 ≤ n) :
    basicCenter (floorIndex x n hn) ≤ (x : ℝ) := by
  have hpow : 0 < (2 : ℝ) ^ n := by positivity
  have hfloor :
      ((⌊(2 : ℝ) ^ n * (x : ℝ)⌋₊ : ℕ) : ℝ) ≤
        (2 : ℝ) ^ n * (x : ℝ) :=
    Nat.floor_le (mul_nonneg hpow.le x.2.1)
  rw [basicCenter]
  change
    ((⌊(2 : ℝ) ^ n * (x : ℝ)⌋₊ : ℕ) : ℝ) / (2 : ℝ) ^ n ≤
      (x : ℝ)
  rw [div_le_iff₀ hpow]
  simpa [mul_comm] using hfloor

theorem floorIndex_lt_center_add_radius (x : X) (n : ℕ) (hn : 1 ≤ n) :
    (x : ℝ) <
      basicCenter (floorIndex x n hn) + basicRadius (floorIndex x n hn) := by
  have hpow : 0 < (2 : ℝ) ^ n := by positivity
  have hfloor :
      (2 : ℝ) ^ n * (x : ℝ) <
        ((⌊(2 : ℝ) ^ n * (x : ℝ)⌋₊ : ℕ) : ℝ) + 1 := by
    simpa using Nat.lt_floor_add_one ((2 : ℝ) ^ n * (x : ℝ))
  rw [basicCenter, basicRadius]
  change
    (x : ℝ) <
      ((⌊(2 : ℝ) ^ n * (x : ℝ)⌋₊ : ℕ) : ℝ) / (2 : ℝ) ^ n +
        1 / (2 : ℝ) ^ n
  rw [← add_div]
  rw [lt_div_iff₀ hpow]
  simpa [mul_comm] using hfloor

/-- In a perfect space, any set containing an interior point is nondegenerate. -/
theorem nontrivial_of_mem_interior
    {α : Type*} [TopologicalSpace α] [PerfectSpace α]
    {A : Set α} {x : α} (hx : x ∈ interior A) :
    A.Nontrivial := by
  have hpre : Preperfect (interior A) := isOpen_interior.preperfect
  have hnhds : interior A ∈ 𝓝 x :=
    isOpen_interior.mem_nhds hx
  rcases (preperfect_iff_nhds.mp hpre x hx (interior A) hnhds) with
    ⟨y, hy, hyne⟩
  exact ⟨x, interior_subset hx, y, interior_subset hy.2, hyne.symm⟩

/-- The floor dyadic interval contains its center point in relative interior. -/
theorem point_mem_interior_floorJ (x : X) (n : ℕ) (hn : 1 ≤ n) :
    x ∈ interior (J (floorIndex x n hn)) := by
  let i := floorIndex x n hn
  have hc : basicCenter i ≤ (x : ℝ) := floorIndex_center_le x n hn
  have hcr : (x : ℝ) < basicCenter i + basicRadius i :=
    floorIndex_lt_center_add_radius x n hn
  have hleft : basicLeft i < (x : ℝ) := by
    rw [basicLeft_eq_center_sub]
    exact (sub_lt_self _ (basicRadius_pos i)).trans_le hc
  have hright : (x : ℝ) < basicRight i := by
    simpa [basicRight_eq_center_add] using hcr
  refine interior_maximal
    (t := Subtype.val ⁻¹' Set.Ioo (basicLeft i) (basicRight i)) ?_ ?_ ?_
  · intro y hy
    exact ⟨hy.1.le, hy.2.le⟩
  · exact isOpen_Ioo.preimage continuous_subtype_val
  · exact ⟨hleft, hright⟩

/-- Every point of the chosen floor interval lies in a controlled metric ball. -/
theorem floorJ_subset_ball (x : X) (n : ℕ) (hn : 1 ≤ n) :
    J (floorIndex x n hn) ⊆
      Metric.ball x (2 * basicRadius (floorIndex x n hn)) := by
  intro y hy
  let i := floorIndex x n hn
  have hr : 0 < basicRadius i := basicRadius_pos i
  have hc : basicCenter i ≤ (x : ℝ) := floorIndex_center_le x n hn
  have hcr : (x : ℝ) < basicCenter i + basicRadius i :=
    floorIndex_lt_center_add_radius x n hn
  have hyl : basicCenter i - basicRadius i ≤ (y : ℝ) := by
    rw [← basicLeft_eq_center_sub]
    exact hy.1
  have hyr : (y : ℝ) ≤ basicCenter i + basicRadius i := by
    rw [← basicRight_eq_center_add]
    exact hy.2
  rw [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq, abs_lt]
  constructor <;> linarith

/-- `lem:closed-neighbourhood-base`: the literal skeleton supplies a closed
relative neighborhood inside every relative open neighborhood. -/
theorem exists_skeleton_closed_neighborhood
    {x : X} {O : Set X} (hO : IsOpen O) (hxO : x ∈ O) :
    ∃ B : Set X,
      B ∈ Skeleton ∧ x ∈ interior B ∧ B ⊆ O := by
  rcases (Metric.isOpen_iff.mp hO x hxO) with ⟨ε, hε, hball⟩
  rcases exists_pow_lt_of_lt_one hε (by norm_num : (1 / 2 : ℝ) < 1) with
    ⟨m, hm⟩
  let n := m + 1
  have hn : 1 ≤ n := by simp [n]
  let i := floorIndex x n hn
  have hxint : x ∈ interior (J i) := by
    exact point_mem_interior_floorJ x n hn
  have hnontrivial : (J i).Nontrivial :=
    nontrivial_of_mem_interior hxint
  refine ⟨J i, ?_, hxint, ?_⟩
  · exact ⟨{i}, by simp, by simp [basicIntersection], hnontrivial⟩
  · apply (floorJ_subset_ball x n hn).trans
    intro y hy
    apply hball
    have hscale :
        2 * basicRadius i = (1 / 2 : ℝ) ^ m := by
      simp only [i, basicRadius, floorIndex, BasicIndex.level, n]
      rw [pow_succ]
      field_simp
      norm_num [one_div_pow]
    rw [Metric.mem_ball] at hy ⊢
    rw [hscale] at hy
    exact hy.trans hm

end

end UnitIntervalRetracts
