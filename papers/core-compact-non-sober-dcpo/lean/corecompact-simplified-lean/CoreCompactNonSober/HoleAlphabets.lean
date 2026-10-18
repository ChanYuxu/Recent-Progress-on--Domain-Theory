import CoreCompactNonSober.WidthAbsorption
import CoreCompactNonSober.SmallSubsets
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset

/-!
# Finite hole alphabets and witness-tail capacity bounds

Source: `lem:approximating-family`, including `eq:approximation-bound`.
The finite alphabet is counted by its binomial layers, and the same
uniform cutoff works for every selected capturing slalom.
-/

set_option autoImplicit false

namespace CoreCompactNonSober.Ambient

open Set Cardinal Localization
open Filter
open scoped BigOperators
open scoped Topology

theorem holeBound_add_one_lt_baseWidth {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (j : Coordinate) : holeBound r j + 1 < baseWidth j := by
  have hpow1 : 1 ≤ (2 : ℝ) ^ ((1 - r) * (j.val : ℝ)) :=
    Real.one_le_rpow (by norm_num)
      (mul_nonneg (sub_nonneg.mpr hr1) (Nat.cast_nonneg _))
  have hfloor1 : 1 ≤ Nat.floor ((2 : ℝ) ^ ((1 - r) * (j.val : ℝ))) :=
    Nat.le_floor (by simpa using hpow1)
  have hexp : (1 - r) * (j.val : ℝ) < (j.val : ℝ) := by
    nlinarith [mul_pos hr (coordinate_real_pos j)]
  have hpow := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2) hexp
  rw [Real.rpow_natCast] at hpow
  have hf : (Nat.floor ((2 : ℝ) ^ ((1 - r) * (j.val : ℝ))) : ℝ) <
      (baseWidth j : ℕ) := by
    simp only [baseWidth, Nat.cast_pow, Nat.cast_ofNat]
    exact (Nat.floor_le (le_trans (by norm_num) hpow1)).trans_lt hpow
  have hn : Nat.floor ((2 : ℝ) ^ ((1 - r) * (j.val : ℝ))) < baseWidth j := by
    exact_mod_cast hf
  unfold holeBound
  omega

abbrev HoleAlphabet (k : ℝ) (j : Coordinate) :=
  SmallSubsets (Alphabet j) (holeBound k j)

instance holeAlphabetNonempty (k : ℝ) (j : Coordinate) : Nonempty (HoleAlphabet k j) :=
  ⟨⟨∅, by simp⟩⟩

theorem holeAlphabet_card_le {k : ℝ} (hk : 0 < k) (hk1 : k ≤ 1) (j : Coordinate) :
    Fintype.card (HoleAlphabet k j) ≤ alphabetSize (doubleCoordinate j) := by
  have hm : holeBound k j + 2 ≤ 2 ^ j.val := by
    have h := holeBound_add_one_lt_baseWidth hk hk1 j
    dsimp [baseWidth] at h
    omega
  have hD : 0 < alphabetSize j := by
    have hp : 0 < alphabetSize j := by unfold alphabetSize; positivity
    omega
  have hexp : j.val + (2 ^ j.val) * holeBound k j < (2 ^ j.val) * (2 ^ j.val) := by
    have hj := j.val.lt_two_pow_self
    nlinarith [Nat.mul_le_mul_left (2 ^ j.val) hm]
  calc
    Fintype.card (HoleAlphabet k j) ≤
        (holeBound k j + 1) * alphabetSize j ^ holeBound k j := by
      simpa only [Fintype.card_fin] using
        smallSubsets_card_le (Alphabet j) (by simpa only [Fintype.card_fin] using hD)
          (holeBound k j)
    _ ≤ (2 ^ j.val) * alphabetSize j ^ holeBound k j := by
      gcongr
      omega
    _ = 2 ^ (j.val + (2 ^ j.val) * holeBound k j) := by
      rw [pow_add, pow_mul]
      rfl
    _ ≤ 2 ^ ((2 ^ j.val) * (2 ^ j.val)) :=
      pow_le_pow_right₀ (by decide) hexp.le
    _ = alphabetSize (doubleCoordinate j) := by
      change 2 ^ ((2 ^ j.val) * (2 ^ j.val)) = 2 ^ (2 ^ (2 * j.val))
      rw [← pow_add]
      congr 2
      omega

theorem hole_alphabet_capturing_family {k e : ℝ} (hk : 0 < k) (hk1 : k ≤ 1)
    (he : 0 < e) :
    ∃ F : Set (Slalom (HoleAlphabet k) (exponentialWidth e)),
      IsCapturing F ∧ Cardinal.mk F ≤ lambda :=
  alphabet_pullback (HoleAlphabet k) (holeAlphabet_card_le hk hk1) he

noncomputable def unionHoles {k e : ℝ}
    (s : Slalom (HoleAlphabet k) (exponentialWidth e)) (j : Coordinate) :
    Finset (Alphabet j) := by
  classical
  exact (s.list j).biUnion Subtype.val

theorem unionHoles_card_le {k e : ℝ}
    (s : Slalom (HoleAlphabet k) (exponentialWidth e)) (j : Coordinate) :
    (unionHoles s j).card ≤ exponentialWidth e j * holeBound k j := by
  classical
  calc
    (unionHoles s j).card ≤ ∑ R ∈ s.list j, R.val.card := Finset.card_biUnion_le
    _ ≤ ∑ _R ∈ s.list j, holeBound k j :=
      Finset.sum_le_sum (fun R _ ↦ R.property)
    _ = (s.list j).card * holeBound k j := by simp
    _ ≤ exponentialWidth e j * holeBound k j := Nat.mul_le_mul_right _ (s.bound j)

/-- The manuscript's two cutoff inequalities, before any slalom is selected.
The witness depends only on `h,k`, not on `ψ`. -/
theorem exists_uniformWitnessCutoff {h k : ℝ}
    (hh : 0 < h) (hhk : h < k) (hk1 : k < 1) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ j : Coordinate, N ≤ j.val →
      (2 : ℝ) ^ (-((k - h) / 2) * (j.val : ℝ)) ≤ 1 / 2 ∧
        4 ≤ (2 : ℝ) ^ ((1 - h) * (j.val : ℝ)) := by
  let e : ℝ := (k - h) / 2
  have he : 0 < e := by dsimp [e]; linarith
  have hh1 : 0 < 1 - h := by linarith
  have ht₁ := tendsto_pow_atTop_atTop_of_one_lt
    (Real.one_lt_rpow (by norm_num : (1 : ℝ) < 2) he)
  have ht₂ := tendsto_pow_atTop_atTop_of_one_lt
    (Real.one_lt_rpow (by norm_num : (1 : ℝ) < 2) hh1)
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp (ht₁.eventually (eventually_ge_atTop (2 : ℝ)))
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp (ht₂.eventually (eventually_ge_atTop (4 : ℝ)))
  refine ⟨max 2 (max N₁ N₂), le_max_left _ _, ?_⟩
  intro j hj
  have hratio : 2 ≤ (2 : ℝ) ^ (e * (j.val : ℝ)) := by
    rw [Real.rpow_mul (by norm_num), Real.rpow_natCast]
    exact hN₁ j.val (by omega)
  constructor
  · change (2 : ℝ) ^ (-e * (j.val : ℝ)) ≤ 1 / 2
    rw [neg_mul, Real.rpow_neg (by norm_num)]
    simpa only [one_div] using one_div_le_one_div_of_le
      (by norm_num : (0 : ℝ) < 2) hratio
  · rw [Real.rpow_mul (by norm_num), Real.rpow_natCast]
    exact hN₂ j.val (by omega)

noncomputable def uniformWitnessCutoff {h k : ℝ}
    (hh : 0 < h) (hhk : h < k) (hk1 : k < 1) : ℕ :=
  Classical.choose (exists_uniformWitnessCutoff hh hhk hk1)

theorem uniformWitnessCutoff_spec {h k : ℝ}
    (hh : 0 < h) (hhk : h < k) (hk1 : k < 1) :
    2 ≤ uniformWitnessCutoff hh hhk hk1 ∧
      ∀ j : Coordinate, uniformWitnessCutoff hh hhk hk1 ≤ j.val →
        (2 : ℝ) ^ (-((k - h) / 2) * (j.val : ℝ)) ≤ 1 / 2 ∧
          4 ≤ (2 : ℝ) ^ ((1 - h) * (j.val : ℝ)) :=
  Classical.choose_spec (exists_uniformWitnessCutoff hh hhk hk1)

theorem witness_capacity_bound_at {h k : ℝ}
    (hh : 0 < h) (hhk : h < k) (hk1 : k < 1)
    (j : Coordinate) (hj : uniformWitnessCutoff hh hhk hk1 ≤ j.val) :
    exponentialWidth ((k - h) / 2) j * holeBound k j ≤ holeBound h j := by
  let e : ℝ := (k - h) / 2
  let c : ℝ := 1 - k + e
  have hw : (exponentialWidth e j : ℝ) ≤ (2 : ℝ) ^ (e * (j.val : ℝ)) :=
    Nat.floor_le (Real.rpow_nonneg (by norm_num) _)
  have hm : (holeBound k j : ℝ) ≤ (2 : ℝ) ^ ((1 - k) * (j.val : ℝ)) := by
    apply le_trans (Nat.cast_le.mpr (Nat.sub_le _ _))
    exact Nat.floor_le (Real.rpow_nonneg (by norm_num) _)
  have hprod : ((exponentialWidth e j * holeBound k j : ℕ) : ℝ) ≤
      (2 : ℝ) ^ (c * (j.val : ℝ)) := by
    rw [Nat.cast_mul]
    have hmul := mul_le_mul hw hm (Nat.cast_nonneg _) (Real.rpow_nonneg (by norm_num) _)
    apply hmul.trans_eq
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
    dsimp [c]
    ring
  obtain ⟨hhalf, hz4⟩ := (uniformWitnessCutoff_spec hh hhk hk1).2 j hj
  have hfactor : (2 : ℝ) ^ (c * (j.val : ℝ)) =
      (2 : ℝ) ^ (-e * (j.val : ℝ)) * (2 : ℝ) ^ ((1 - h) * (j.val : ℝ)) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
    dsimp [c, e]
    ring
  have hsmall : (2 : ℝ) ^ (c * (j.val : ℝ)) ≤
      (2 : ℝ) ^ ((1 - h) * (j.val : ℝ)) / 2 := by
    rw [hfactor]
    have := mul_le_mul_of_nonneg_right hhalf
      (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) ((1 - h) * (j.val : ℝ)))
    linarith
  push_cast at hprod
  have hfloor : exponentialWidth e j * holeBound k j + 1 ≤
      Nat.floor ((2 : ℝ) ^ ((1 - h) * (j.val : ℝ))) := by
    apply Nat.le_floor
    push_cast
    linarith
  change exponentialWidth e j * holeBound k j ≤
    Nat.floor ((2 : ℝ) ^ ((1 - h) * (j.val : ℝ))) - 1
  omega

theorem witness_capacity_bound {h k : ℝ} (hh : 0 < h) (hhk : h < k) (hk1 : k < 1) :
    ∃ N : ℕ, ∀ j : Coordinate, N ≤ j.val →
      exponentialWidth ((k - h) / 2) j * holeBound k j ≤ holeBound h j :=
  ⟨uniformWitnessCutoff hh hhk hk1, witness_capacity_bound_at hh hhk hk1⟩

theorem unionHoles_capacity_at {h k : ℝ}
    (hh : 0 < h) (hhk : h < k) (hk1 : k < 1)
    (s : Slalom (HoleAlphabet k) (exponentialWidth ((k - h) / 2)))
    (j : Coordinate) (hj : uniformWitnessCutoff hh hhk hk1 ≤ j.val) :
    h ≤ capacity j (Finset.univ \ unionHoles s j) := by
  apply (capacity_ge_iff_holeBound j _ hh (by linarith)).mpr
  have heq : holeCount j (Finset.univ \ unionHoles s j) = (unionHoles s j).card := by
    unfold holeCount
    rw [Finset.sdiff_sdiff_eq_self (Finset.subset_univ _)]
  rw [heq]
  exact (unionHoles_card_le s j).trans (witness_capacity_bound_at hh hhk hk1 j hj)

theorem unionHoles_eventual_capacity {h k : ℝ}
    (hh : 0 < h) (hhk : h < k) (hk1 : k < 1)
    (s : Slalom (HoleAlphabet k) (exponentialWidth ((k - h) / 2))) :
    ∃ N : ℕ, ∀ j : Coordinate, N ≤ j.val →
      h ≤ capacity j (Finset.univ \ unionHoles s j) := by
  exact ⟨uniformWitnessCutoff hh hhk hk1, unionHoles_capacity_at hh hhk hk1 s⟩

end CoreCompactNonSober.Ambient
