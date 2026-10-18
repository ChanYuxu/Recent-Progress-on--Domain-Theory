import CoreCompactNonSober.FinitePrefix
import CoreCompactNonSober.Protection
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Protected pair rows with their actual ambient supremum

Source: `lem:insertion` (ii), `eq:recursive-row` (2026-10-15 revision).
Rows are indexed internally by `n=0,1,...` instead of `1,2,...`.
Their specified dyadic heights are explicitly `t*(1-(1/2)^(n+1))`.
-/

set_option autoImplicit false

namespace CoreCompactNonSober.Ambient

open Set Cardinal Localization Filter
open scoped Topology

noncomputable def rowHeight (t : ℝ) (n : ℕ) : ℝ :=
  t * (1 - (1 / 2 : ℝ) ^ (n + 1))

/-- The displayed `u_(n+1) = t (1 - 2^(-(n+1)))`, written without
negative natural exponents in Lean. -/
theorem rowHeight_eq_printed (t : ℝ) (n : ℕ) :
    rowHeight t n = t * (1 - 1 / (2 : ℝ) ^ (n + 1)) := by
  simp only [rowHeight, div_pow, one_pow]

theorem rowHeight_pos {t : ℝ} (ht : 0 < t) (n : ℕ) : 0 < rowHeight t n := by
  have hi : (1 / 2 : ℝ) ^ (n + 1) < 1 :=
    pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
  exact mul_pos ht (sub_pos.mpr hi)

theorem rowHeight_lt {t : ℝ} (ht : 0 < t) (n : ℕ) : rowHeight t n < t := by
  have hi : 0 < (1 / 2 : ℝ) ^ (n + 1) := by positivity
  unfold rowHeight
  nlinarith

theorem rowHeight_strictMono {t : ℝ} (ht : 0 < t) : StrictMono (rowHeight t) := by
  intro n m hnm
  have hi := pow_lt_pow_right_of_lt_one₀ (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1) (by omega : n + 1 < m + 1)
  unfold rowHeight
  nlinarith

theorem rowHeight_tendsto (t : ℝ) : Tendsto (rowHeight t) atTop (𝓝 t) := by
  have hi : Tendsto (fun n : ℕ ↦ (1 / 2 : ℝ) ^ (n + 1)) atTop (𝓝 (0 : ℝ)) :=
    (tendsto_add_atTop_iff_nat 1).mpr
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))
  have h1 : Tendsto (fun _n : ℕ ↦ (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  simpa only [rowHeight, sub_zero, mul_one] using (h1.sub hi).const_mul t

private theorem tail_cutoff_exists {d : ℝ} (hd : 0 < d) (C : ℕ) :
    ∃ M : ℕ, C ≤ M ∧ 2 ≤ M ∧ 2 / (M : ℝ) < d ∧
      ∀ j : Coordinate, M ≤ j.val → 2 / (j.val : ℝ) < d := by
  obtain ⟨N, hN⟩ := exists_nat_gt (2 / d)
  let M := max (max C N) 2
  have hNM : N ≤ M := (le_max_right C N).trans (le_max_left _ _)
  have hM2 : 2 ≤ M := le_max_right _ _
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hmul : 2 < (N : ℝ) * d := (div_lt_iff₀ hd).mp hN
  have hcut : 2 / (M : ℝ) < d := by
    apply (div_lt_iff₀ hMpos).mpr
    have hle : (N : ℝ) ≤ M := by exact_mod_cast hNM
    nlinarith
  refine ⟨M, (le_max_left C N).trans (le_max_left _ _), hM2, hcut, ?_⟩
  intro j hj
  have hNj : (N : ℝ) ≤ (j.val : ℝ) := by
    exact_mod_cast (hNM.trans hj)
  apply (div_lt_iff₀ (coordinate_real_pos j)).mpr
  nlinarith

def pairConfiguration (p b : Carrier) (f : (j : Coordinate) → Alphabet j) (M : ℕ) :
    Configuration := fun j ↦ if j.val < M then configuration p j
      else (configuration p j ∩ configuration b j) \ {f j}

theorem pairConfiguration_prefix (p b : Carrier) (f : (j : Coordinate) → Alphabet j)
    (M : ℕ) (j : Coordinate) (hj : j.val < M) :
    pairConfiguration p b f M j = configuration p j := by
  simp only [pairConfiguration, if_pos hj]

theorem pairConfiguration_tail (p b : Carrier) (f : (j : Coordinate) → Alphabet j)
    (M : ℕ) (j : Coordinate) (hj : M ≤ j.val) :
    pairConfiguration p b f M j = (configuration p j ∩ configuration b j) \ {f j} := by
  simp only [pairConfiguration, if_neg (not_lt_of_ge hj)]

theorem pairConfiguration_subset (p b : Carrier) (f : (j : Coordinate) → Alphabet j)
    (M : ℕ) (j : Coordinate) : pairConfiguration p b f M j ⊆ configuration p j := by
  by_cases hj : j.val < M
  · rw [pairConfiguration_prefix p b f M j hj]
  · rw [pairConfiguration_tail p b f M j (by omega)]
    exact Finset.sdiff_subset.trans Finset.inter_subset_left

theorem pairConfiguration_mono (p b : Carrier) (f : (j : Coordinate) → Alphabet j)
    {M N : ℕ} (hMN : M ≤ N) (j : Coordinate) :
    pairConfiguration p b f M j ⊆ pairConfiguration p b f N j := by
  by_cases hjN : j.val < N
  · rw [pairConfiguration_prefix p b f N j hjN]
    exact pairConfiguration_subset p b f M j
  · have hjM : M ≤ j.val := hMN.trans (le_of_not_gt hjN)
    rw [pairConfiguration_tail p b f M j hjM,
      pairConfiguration_tail p b f N j (le_of_not_gt hjN)]

structure PairRow (p b : Carrier) where
  point : ℕ → Carrier
  cutoff : ℕ → ℕ
  pattern : (j : Coordinate) → Alphabet j
  cutoff_strictMono : StrictMono cutoff
  cutoff_ge : ∀ n, n ≤ cutoff n
  cutoff_ge_two : ∀ n, 2 ≤ cutoff n
  cutoff_size : ∀ n, 2 / (cutoff n : ℝ) < height p - rowHeight (height p) n
  height_eq : ∀ n, height (point n) = rowHeight (height p) n
  positive : ∀ n, Positive (point n)
  height_lt : ∀ n, height (point n) < height p
  strictMono : StrictMono point
  below_endpoint : ∀ n, point n ≤ p
  isLUB : IsLUB (Set.range point) p
  configuration_eq : ∀ (n : ℕ) (j : Coordinate), configuration (point n) j =
    if j.val < cutoff n then configuration p j
      else (configuration p j ∩ configuration b j) \ {pattern j}

theorem PairRow.cutoff_tendsto {p b : Carrier} (R : PairRow p b) :
    Tendsto R.cutoff atTop atTop :=
  tendsto_atTop_mono R.cutoff_ge tendsto_id

theorem PairRow.height_eq_printed {p b : Carrier} (R : PairRow p b) (n : ℕ) :
    height (R.point n) = height p * (1 - 1 / (2 : ℝ) ^ (n + 1)) := by
  rw [R.height_eq, rowHeight_eq_printed]

theorem PairRow.hasHole {p b : Carrier} (R : PairRow p b) (n : ℕ) : HasHole (R.point n) := by
  let j : Coordinate := ⟨max (R.cutoff n) 2, le_max_right _ _⟩
  refine ⟨j, R.pattern j, ?_⟩
  have hj : R.cutoff n ≤ j.val := le_max_left _ _
  rw [R.configuration_eq n j, if_neg (not_lt_of_ge hj)]
  simp

theorem PairRow.tailOmission {p b : Carrier} (R : PairRow p b) (n : ℕ) :
    TailOmission (R.point n) := by
  refine ⟨R.pattern, R.cutoff n, ?_⟩
  intro j hj
  rw [R.configuration_eq n j, if_neg (not_lt_of_ge hj)]
  simp

theorem pair_insertion_prescribed (P : Set Carrier) (hP : ∀ x ∈ P, Positive x)
    (hsmall : Cardinal.mk P < lambda) (p b : Carrier) (hp : Positive p)
    (hp1 : height p < 1) (hpb : height p ≤ height b) :
    ∃ R : PairRow p b, Protects P R.pattern ∧
      ∀ x ∈ P, ∀ n, ¬ x ≤ R.point n := by
  classical
  obtain ⟨f, hf⟩ := exists_protection_pattern P hP hsmall
  let u := rowHeight (height p)
  have hupos : ∀ n, 0 < u n := rowHeight_pos hp
  have hult : ∀ n, u n < height p := rowHeight_lt hp
  have hustrict : StrictMono u := rowHeight_strictMono hp
  have hex : ∀ n : ℕ, ∃ K : ℕ, n ≤ K ∧ 2 ≤ K ∧
      2 / (K : ℝ) < height p - u n ∧
      ∀ j : Coordinate, K ≤ j.val → 2 / (j.val : ℝ) < height p - u n := by
    intro n
    exact tail_cutoff_exists (sub_pos.mpr (hult n)) n
  choose K hKge hK2 hKsize hKtail using hex
  let M : ℕ → ℕ := Nat.rec (K 0) (fun n prev ↦ max (K (n + 1)) (prev + 1))
  have hKM : ∀ n, K n ≤ M n := by
    intro n
    cases n with
    | zero => exact le_rfl
    | succ n => exact le_max_left _ _
  have hMstrict : StrictMono M := by
    apply strictMono_nat_of_lt_succ
    intro n
    exact (Nat.lt_succ_self (M n)).trans_le (le_max_right _ _)
  have hMge : ∀ n, n ≤ M n := fun n ↦ (hKge n).trans (hKM n)
  have hM2 : ∀ n, 2 ≤ M n := fun n ↦ (hK2 n).trans (hKM n)
  have hMsize : ∀ n : ℕ, 2 / (Nat.cast (M n) : ℝ) < height p - u n := by
    intro n
    have hle : (Nat.cast (K n) : ℝ) ≤ (Nat.cast (M n) : ℝ) := by exact_mod_cast hKM n
    have hpos : (0 : ℝ) < (Nat.cast (K n) : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) (hK2 n))
    exact (div_le_div_of_nonneg_left (by norm_num) hpos hle).trans_lt (hKsize n)
  let A : ℕ → Configuration := fun n ↦ pairConfiguration p b f (M n)
  have hadm : ∀ (n : ℕ) (j : Coordinate), u n ≤ capacity j (A n j) := by
    intro n j
    change u n ≤ capacity j (pairConfiguration p b f (M n) j)
    rcases lt_or_ge j.val (M n) with hj | hj
    · rw [pairConfiguration_prefix p b f (M n) j hj]
      exact (hult n).le.trans (p.property j)
    · rw [pairConfiguration_tail p b f (M n) j hj]
      have htail := hKtail n j ((hKM n).trans hj)
      have hPcap := p.property j
      have hBcap := b.property j
      change height p ≤ capacity j (configuration p j) at hPcap
      change height b ≤ capacity j (configuration b j) at hBcap
      have hmin : height p ≤ min (capacity j (configuration p j)) (capacity j (configuration b j)) :=
        le_min hPcap (hpb.trans hBcap)
      have hinter := (capacity_intersection_loss j (configuration p j) (configuration b j)).2
      have hdel := (capacity_deletion_loss j (configuration p j ∩ configuration b j) (f j)).2
      have htwo : 2 / (j.val : ℝ) = 1 / (j.val : ℝ) + 1 / (j.val : ℝ) := by ring
      rw [htwo] at htail
      linarith
  let r (n : ℕ) : Carrier :=
    ⟨(⟨u n, ⟨(hupos n).le, (hult n).le.trans hp1.le⟩⟩, A n), hadm n⟩
  have hrheight : ∀ n : ℕ, height (r n) = u n := fun _ ↦ rfl
  have hrconfig : ∀ (n : ℕ) (j : Coordinate), configuration (r n) j =
      pairConfiguration p b f (M n) j := fun _ _ ↦ rfl
  have hrbelow : ∀ n, r n ≤ p := by
    intro n
    apply (le_iff _ _).mpr
    refine ⟨(hult n).le, ?_⟩
    intro j
    rw [hrconfig n j]
    exact pairConfiguration_subset p b f (M n) j
  have hrmono : Monotone r := by
    intro n m hnm
    apply (le_iff _ _).mpr
    refine ⟨hustrict.monotone hnm, ?_⟩
    intro j
    rw [hrconfig n j, hrconfig m j]
    exact pairConfiguration_mono p b f (hMstrict.monotone hnm) j
  have hrstrict : StrictMono r := by
    intro n m hnm
    apply lt_iff_le_not_ge.mpr
    refine ⟨hrmono hnm.le, ?_⟩
    intro hrev
    have hht := ((le_iff _ _).mp hrev).1
    rw [hrheight, hrheight] at hht
    exact not_le_of_gt (hustrict hnm) hht
  have hrlub : IsLUB (Set.range r) p := by
    constructor
    · rintro _ ⟨n, rfl⟩
      exact hrbelow n
    · intro q hq
      apply (le_iff _ _).mpr
      constructor
      · exact le_of_tendsto' (rowHeight_tendsto (height p))
          (fun n ↦ ((le_iff _ _).mp (hq (Set.mem_range_self n))).1)
      · intro j
        let n := j.val + 1
        have hj : j.val < M n := by
          change j.val < M (j.val + 1)
          have := hMge (j.val + 1)
          omega
        have heq : configuration (r n) j = configuration p j := by
          rw [hrconfig n j, pairConfiguration_prefix p b f (M n) j hj]
        rw [← heq]
        exact ((le_iff _ _).mp (hq (Set.mem_range_self n))).2 j
  refine ⟨{
    point := r
    cutoff := M
    pattern := f
    cutoff_strictMono := hMstrict
    cutoff_ge := hMge
    cutoff_ge_two := hM2
    cutoff_size := hMsize
    height_eq := hrheight
    positive := hupos
    height_lt := hult
    strictMono := hrstrict
    below_endpoint := hrbelow
    isLUB := hrlub
    configuration_eq := fun _ _ ↦ rfl }, hf, ?_⟩
  intro x hx n
  apply not_le_of_tail_omission hf hx (r n) (M n)
  intro j hj
  rw [hrconfig n j, pairConfiguration_tail p b f (M n) j hj]
  simp

/-- Compatibility interface. The actual insertion theorem above also
proves that the same pattern stored in the row meets every old point
arbitrarily far out, as prescribed by tail selection. -/
theorem pair_insertion (P : Set Carrier) (hP : ∀ x ∈ P, Positive x)
    (hsmall : Cardinal.mk P < lambda) (p b : Carrier) (hp : Positive p)
    (hp1 : height p < 1) (hpb : height p ≤ height b) :
    ∃ R : PairRow p b, ∀ x ∈ P, ∀ n, ¬ x ≤ R.point n := by
  obtain ⟨R, _, havoid⟩ := pair_insertion_prescribed P hP hsmall p b hp hp1 hpb
  exact ⟨R, havoid⟩

theorem PairRow.finite_prefix_domination {p b : Carrier} (R : PairRow p b)
    (hpb : height p ≤ height b) (E : Set Carrier) (hE : NonemptyDirected E)
    (hp : p ≤ sSup E) (e₀ : Carrier) (he₀ : e₀ ∈ E) (hbe₀ : b ≤ e₀) (n : ℕ) :
    ∃ e ∈ E, R.point n ≤ e := by
  apply Ambient.finite_prefix_domination E hE p b (R.point n) hp e₀ he₀ hbe₀
    (R.cutoff n) ((R.height_lt n).le.trans hpb)
  · intro j hj
    rw [R.configuration_eq n j, if_pos hj]
  · intro j hj
    rw [R.configuration_eq n j, if_neg (not_lt_of_ge hj)]
    exact Finset.sdiff_subset.trans Finset.inter_subset_right

end CoreCompactNonSober.Ambient
