import CoreCompactNonSober.Localization
import Mathlib.Analysis.SpecificLimits.Normed

/-! # Elementary exponential estimates used in Section 4 -/

set_option autoImplicit false

namespace CoreCompactNonSober.Localization

open Filter
open scoped Topology
open Ambient (Coordinate)

noncomputable def exponentialWidth (a : ℝ) (j : Coordinate) : ℕ :=
  Nat.floor ((2 : ℝ) ^ (a * (j.val : ℝ)))

theorem exponentialWidth_pos {a : ℝ} (ha : 0 ≤ a) (j : Coordinate) :
    0 < exponentialWidth a j := by
  have hpow : 1 ≤ (2 : ℝ) ^ (a * (j.val : ℝ)) :=
    Real.one_le_rpow (by norm_num) (mul_nonneg ha (Nat.cast_nonneg _))
  exact Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_floor (by simpa using hpow))

theorem exponentialWidth_mono {a b : ℝ} (hab : a ≤ b) (j : Coordinate) :
    exponentialWidth a j ≤ exponentialWidth b j :=
  Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le (by norm_num)
    (mul_le_mul_of_nonneg_right hab (Nat.cast_nonneg _)))

theorem exponentialWidth_le_base {a : ℝ} (ha : a ≤ 1) (j : Coordinate) :
    exponentialWidth a j ≤ baseWidth j := by
  have h := exponentialWidth_mono ha j
  have heq : exponentialWidth 1 j = baseWidth j := by
    have hf : Nat.floor (((2 ^ j.val : ℕ) : ℝ)) = 2 ^ j.val := Nat.floor_natCast _
    simpa only [exponentialWidth, baseWidth, one_mul, Real.rpow_natCast,
      Nat.cast_pow, Nat.cast_ofNat] using hf
  exact h.trans_eq heq

theorem eventually_linear_le_dyadic {a : ℝ} (ha : 0 < a) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → 2 * (n : ℝ) + 1 ≤ a * (2 : ℝ) ^ n := by
  have h₁ : Tendsto (fun n : ℕ ↦ (n : ℝ) / (2 : ℝ) ^ n) atTop (𝓝 0) := by
    simpa only [pow_one] using
      tendsto_pow_const_div_const_pow_of_one_lt 1 (by norm_num : (1 : ℝ) < 2)
  have h₂ : Tendsto (fun n : ℕ ↦ 1 / (2 : ℝ) ^ n) atTop (𝓝 0) := by
    simpa only [one_div] using
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).inv_tendsto_atTop
  have h : Tendsto (fun n : ℕ ↦ (2 * (n : ℝ) + 1) / (2 : ℝ) ^ n)
      atTop (𝓝 0) := by
    convert (h₁.const_mul 2).add h₂ using 1
    · funext n
      ring
    · norm_num
  obtain ⟨N, hN⟩ := eventually_atTop.mp (h.eventually (gt_mem_nhds ha))
  refine ⟨N, fun n hn ↦ ?_⟩
  exact ((div_lt_iff₀ (pow_pos (by norm_num : (0 : ℝ) < 2) n)).mp (hN n hn)).le

theorem eventually_block_width {a : ℝ} (ha : 0 < a) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ j : Coordinate, 2 ^ n ≤ j.val →
      2 ^ (2 * n + 1) ≤ exponentialWidth a j := by
  obtain ⟨N, hN⟩ := eventually_linear_le_dyadic ha
  refine ⟨N, ?_⟩
  intro n hn j hj
  have hcast : (2 : ℝ) ^ n ≤ (j.val : ℝ) := by exact_mod_cast hj
  have hexp : ((2 * n + 1 : ℕ) : ℝ) ≤ a * (j.val : ℝ) := by
    push_cast
    exact (hN n hn).trans (mul_le_mul_of_nonneg_left hcast ha.le)
  have hpow := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hexp
  rw [Real.rpow_natCast] at hpow
  apply Nat.le_floor
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using hpow

theorem eventually_exponential_gap {c d : ℝ} (hc : 0 ≤ c) (hcd : c < d) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (2 : ℝ) ^ (c * (n : ℝ)) + 2 ≤ (2 : ℝ) ^ (d * (n : ℝ)) := by
  have hbase : 1 < (2 : ℝ) ^ (d - c) :=
    Real.one_lt_rpow (by norm_num) (sub_pos.mpr hcd)
  have ht := tendsto_pow_atTop_atTop_of_one_lt hbase
  obtain ⟨N, hN⟩ := eventually_atTop.mp (ht.eventually (eventually_ge_atTop (3 : ℝ)))
  refine ⟨N, ?_⟩
  intro n hn
  have hratio : 3 ≤ (2 : ℝ) ^ ((d - c) * (n : ℝ)) := by
    rw [Real.rpow_mul (by norm_num), Real.rpow_natCast]
    exact hN n hn
  have hsmall : 1 ≤ (2 : ℝ) ^ (c * (n : ℝ)) :=
    Real.one_le_rpow (by norm_num) (mul_nonneg hc (Nat.cast_nonneg n))
  have heq : (2 : ℝ) ^ (d * (n : ℝ)) =
      (2 : ℝ) ^ (c * (n : ℝ)) * (2 : ℝ) ^ ((d - c) * (n : ℝ)) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  rw [heq]
  nlinarith

end CoreCompactNonSober.Localization
