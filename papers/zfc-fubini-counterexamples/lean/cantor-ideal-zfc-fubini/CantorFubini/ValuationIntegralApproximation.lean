import CantorFubini.ValuationIntegral
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Floor.Ring

/-! Increasing finite sums of open-set indicators approximate every
nonnegative lower semicontinuous function, including unbounded functions.
Only strict superlevel sets occur, so every approximation is itself LSC. -/

set_option autoImplicit false
open Set Topology TopologicalSpace MeasureTheory
open scoped ENNReal
universe u
namespace CantorFubini

noncomputable def levelPiece {X : Type u} [TopologicalSpace X]
    (f : X → ℝ≥0∞) (c : ℝ≥0∞) (k : ℕ) : X → ℝ≥0∞ :=
  (vLevel f (((k + 1 : ℕ) : ℝ≥0∞) * c) : Set X).indicator (fun _ => c)

noncomputable def levelStepSum {X : Type u} [TopologicalSpace X]
    (f : X → ℝ≥0∞) (c : ℝ≥0∞) (m : ℕ) (x : X) : ℝ≥0∞ :=
  ∑ k ∈ Finset.range m, levelPiece f c k x

theorem levelPiece_apply {X : Type u} [TopologicalSpace X]
    {f : X → ℝ≥0∞} (hf : IsVLSC f) (c : ℝ≥0∞) (k : ℕ) (x : X) :
    levelPiece f c k x = if ((k + 1 : ℕ) : ℝ≥0∞) * c < f x then c else 0 := by
  classical
  rw [levelPiece, vLevel_eq hf]
  simp only [Opens.coe_mk, Set.indicator, mem_setOf_eq]

theorem levelPiece_le {X : Type u} [TopologicalSpace X]
    (f : X → ℝ≥0∞) (c : ℝ≥0∞) (k : ℕ) (x : X) : levelPiece f c k x ≤ c := by
  classical
  unfold levelPiece
  by_cases hx : x ∈ vLevel f (((k + 1 : ℕ) : ℝ≥0∞) * c)
  · rw [Set.indicator_of_mem hx]
  · rw [Set.indicator_of_notMem hx]
    exact zero_le _

theorem levelStepSum_le_scale {X : Type u} [TopologicalSpace X]
    (f : X → ℝ≥0∞) (c : ℝ≥0∞) (m : ℕ) (x : X) :
    levelStepSum f c m x ≤ (m : ℝ≥0∞) * c := by
  calc
    levelStepSum f c m x ≤ ∑ _k ∈ Finset.range m, c :=
      Finset.sum_le_sum (fun k _ => levelPiece_le f c k x)
    _ = (m : ℝ≥0∞) * c := by simp [nsmul_eq_mul]

theorem levelStepSum_le {X : Type u} [TopologicalSpace X]
    {f : X → ℝ≥0∞} (hf : IsVLSC f) (c : ℝ≥0∞) (m : ℕ) (x : X) :
    levelStepSum f c m x ≤ f x := by
  induction m with
  | zero => simp [levelStepSum]
  | succ m ih =>
      rw [levelStepSum, Finset.sum_range_succ, levelPiece_apply hf]
      by_cases h : ((m + 1 : ℕ) : ℝ≥0∞) * c < f x
      · rw [if_pos h]
        calc
          (∑ k ∈ Finset.range m, levelPiece f c k x) + c ≤ (m : ℝ≥0∞) * c + c :=
            add_le_add (levelStepSum_le_scale f c m x) le_rfl
          _ = ((m + 1 : ℕ) : ℝ≥0∞) * c := by push_cast; ring
          _ ≤ f x := h.le
      · rw [if_neg h, add_zero]
        exact ih

theorem levelStepSum_mono_cut {X : Type u} [TopologicalSpace X]
    (f : X → ℝ≥0∞) (c : ℝ≥0∞) {m n : ℕ} (hmn : m ≤ n) (x : X) :
    levelStepSum f c m x ≤ levelStepSum f c n x :=
  Finset.sum_le_sum_of_subset (Finset.range_mono hmn)

theorem scale_le_levelStepSum {X : Type u} [TopologicalSpace X]
    {f : X → ℝ≥0∞} (hf : IsVLSC f) (c : ℝ≥0∞) {k m : ℕ} (hkm : k ≤ m)
    (x : X) (hk : (k : ℝ≥0∞) * c < f x) :
    (k : ℝ≥0∞) * c ≤ levelStepSum f c m x := by
  have hpiece (j : ℕ) (hj : j ∈ Finset.range k) : levelPiece f c j x = c := by
    rw [levelPiece_apply hf]
    apply if_pos
    apply lt_of_le_of_lt _ hk
    apply mul_le_mul_right'
    exact_mod_cast Nat.succ_le_of_lt (Finset.mem_range.mp hj)
  calc
    (k : ℝ≥0∞) * c = levelStepSum f c k x := by
      unfold levelStepSum
      simp_rw [Finset.sum_congr rfl hpiece]
      simp [nsmul_eq_mul]
    _ ≤ levelStepSum f c m x := levelStepSum_mono_cut f c hkm x

theorem isVLSC_levelStepSum {X : Type u} [TopologicalSpace X]
    (f : X → ℝ≥0∞) (c : ℝ≥0∞) (m : ℕ) : IsVLSC (levelStepSum f c m) := by
  induction m with
  | zero => simpa [levelStepSum] using (isVLSC_const (X := X) 0)
  | succ m ih =>
      have he : levelStepSum f c (m + 1) =
          fun x => levelStepSum f c m x + levelPiece f c m x := by
        funext x
        exact Finset.sum_range_succ _ _
      rw [he]
      exact ih.add (isVLSC_indicator (vLevel f (((m + 1 : ℕ) : ℝ≥0∞) * c)) c)

noncomputable def dyadicCoeff (n : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (((2 : ℝ) ^ n)⁻¹)

def dyadicCut (n : ℕ) : ℕ := (2 ^ n) * (2 ^ n)

noncomputable def dyadicOpen {X : Type u} [TopologicalSpace X]
    (f : X → ℝ≥0∞) (n k : ℕ) : Opens X :=
  vLevel f (((k + 1 : ℕ) : ℝ≥0∞) * dyadicCoeff n)

noncomputable def dyadicApprox {X : Type u} [TopologicalSpace X]
    (f : X → ℝ≥0∞) (n : ℕ) : X → ℝ≥0∞ :=
  levelStepSum f (dyadicCoeff n) (dyadicCut n)

theorem dyadicApprox_eq_sum {X : Type u} [TopologicalSpace X]
    (f : X → ℝ≥0∞) (n : ℕ) (x : X) : dyadicApprox f n x =
      ∑ k ∈ Finset.range (dyadicCut n),
        (dyadicOpen f n k : Set X).indicator (fun _ => dyadicCoeff n) x := rfl

theorem dyadicCoeff_ne_top (n : ℕ) : dyadicCoeff n ≠ ∞ := ENNReal.ofReal_ne_top

theorem dyadicCoeff_pos (n : ℕ) : 0 < dyadicCoeff n := by
  apply ENNReal.ofReal_pos.mpr
  positivity

theorem dyadicCoeff_succ_add (n : ℕ) :
    dyadicCoeff (n + 1) + dyadicCoeff (n + 1) = dyadicCoeff n := by
  unfold dyadicCoeff
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  rw [pow_succ]
  field_simp
  <;> ring

theorem cast_mul_dyadicCoeff (k n : ℕ) :
    (k : ℝ≥0∞) * dyadicCoeff n = ENNReal.ofReal ((k : ℝ) / (2 : ℝ) ^ n) := by
  have hk : (k : ℝ≥0∞) = ENNReal.ofReal (k : ℝ) := by simp
  rw [hk, dyadicCoeff, ← ENNReal.ofReal_mul (Nat.cast_nonneg k)]
  rfl

theorem dyadicCut_succ (n : ℕ) : dyadicCut (n + 1) = 4 * dyadicCut n := by
  unfold dyadicCut
  rw [pow_succ]
  ring

theorem isVLSC_dyadicApprox {X : Type u} [TopologicalSpace X]
    (f : X → ℝ≥0∞) (n : ℕ) : IsVLSC (dyadicApprox f n) :=
  isVLSC_levelStepSum f _ _

theorem dyadicApprox_le {X : Type u} [TopologicalSpace X]
    {f : X → ℝ≥0∞} (hf : IsVLSC f) (n : ℕ) (x : X) : dyadicApprox f n x ≤ f x :=
  levelStepSum_le hf _ _ _

theorem sum_range_double (F : ℕ → ℝ≥0∞) (m : ℕ) :
    (∑ k ∈ Finset.range (2 * m), F k) =
      ∑ k ∈ Finset.range m, (F (2 * k) + F (2 * k + 1)) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [show 2 * (m + 1) = 2 * m + 1 + 1 by omega,
        Finset.sum_range_succ, Finset.sum_range_succ, ih, Finset.sum_range_succ]
      simp only [add_assoc]

theorem levelPiece_refine {X : Type u} [TopologicalSpace X]
    {f : X → ℝ≥0∞} (hf : IsVLSC f) (n k : ℕ) (x : X) :
    levelPiece f (dyadicCoeff n) k x ≤
      levelPiece f (dyadicCoeff (n + 1)) (2 * k) x +
        levelPiece f (dyadicCoeff (n + 1)) (2 * k + 1) x := by
  classical
  simp only [levelPiece_apply hf]
  by_cases hk : ((k + 1 : ℕ) : ℝ≥0∞) * dyadicCoeff n < f x
  · rw [if_pos hk]
    have he : ((2 * k + 1 + 1 : ℕ) : ℝ≥0∞) * dyadicCoeff (n + 1) =
        ((k + 1 : ℕ) : ℝ≥0∞) * dyadicCoeff n := by
      rw [← dyadicCoeff_succ_add n]
      push_cast
      ring
    have h2 : ((2 * k + 1 + 1 : ℕ) : ℝ≥0∞) * dyadicCoeff (n + 1) < f x := he ▸ hk
    have h1 : ((2 * k + 1 : ℕ) : ℝ≥0∞) * dyadicCoeff (n + 1) < f x := by
      apply lt_of_le_of_lt _ h2
      apply mul_le_mul_right'
      exact_mod_cast (show 2 * k + 1 ≤ 2 * k + 1 + 1 by omega)
    rw [if_pos h1, if_pos h2, dyadicCoeff_succ_add]
  · rw [if_neg hk]
    exact zero_le _

theorem dyadicApprox_mono {X : Type u} [TopologicalSpace X]
    {f : X → ℝ≥0∞} (hf : IsVLSC f) : Monotone (dyadicApprox f) := by
  apply monotone_nat_of_le_succ
  intro n x
  calc
    dyadicApprox f n x ≤
        ∑ k ∈ Finset.range (dyadicCut n),
          (levelPiece f (dyadicCoeff (n + 1)) (2 * k) x +
            levelPiece f (dyadicCoeff (n + 1)) (2 * k + 1) x) :=
      Finset.sum_le_sum (fun k _ => levelPiece_refine hf n k x)
    _ = levelStepSum f (dyadicCoeff (n + 1)) (2 * dyadicCut n) x :=
      (sum_range_double (fun k => levelPiece f (dyadicCoeff (n + 1)) k x) _).symm
    _ ≤ dyadicApprox f (n + 1) x := by
      apply levelStepSum_mono_cut
      rw [dyadicCut_succ]
      omega

/-- Every strict real interval contains a dyadic grid value within the
corresponding expanding finite truncation. -/
theorem exists_dyadic_grid_between (a b : ℝ) (hab : a < b) (hb0 : 0 ≤ b) :
    ∃ n k : ℕ, k ≤ dyadicCut n ∧ a < (k : ℝ) / (2 : ℝ) ^ n ∧
      (k : ℝ) / (2 : ℝ) ^ n ≤ b := by
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt
    (max (b + 1) (1 / (b - a))) (by norm_num : 1 < (2 : ℝ))
  let D : ℝ := (2 : ℝ) ^ n
  have hD : 0 < D := by dsimp [D]; positivity
  have hbD : b < D := lt_trans (by linarith : b < b + 1)
    ((le_max_left _ _).trans_lt hn)
  have hgap : 1 / (b - a) < D := (le_max_right _ _).trans_lt hn
  have hgap' : 1 < D * (b - a) := (div_lt_iff₀ (sub_pos.mpr hab)).mp hgap
  let k : ℕ := Nat.floor (b * D)
  have hk_le : (k : ℝ) ≤ b * D := Nat.floor_le (mul_nonneg hb0 hD.le)
  have hk_lt : b * D < (k : ℝ) + 1 := Nat.lt_floor_add_one (b * D)
  have hleft : a < (k : ℝ) / D := (lt_div_iff₀ hD).mpr (by nlinarith)
  have hright : (k : ℝ) / D ≤ b := (div_le_iff₀ hD).mpr hk_le
  have hcap : (dyadicCut n : ℝ) = D * D := by
    simp only [dyadicCut, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, D]
  have hkcap : (k : ℝ) ≤ (dyadicCut n : ℝ) := by
    rw [hcap]
    exact hk_le.trans (mul_le_mul_of_nonneg_right hbD.le hD.le)
  exact ⟨n, k, by exact_mod_cast hkcap, hleft, hright⟩

theorem iSup_dyadicApprox {X : Type u} [TopologicalSpace X]
    {f : X → ℝ≥0∞} (hf : IsVLSC f) (x : X) :
    (⨆ n : ℕ, dyadicApprox f n x) = f x := by
  apply le_antisymm
  · exact iSup_le (fun n => dyadicApprox_le hf n x)
  · apply ENNReal.le_of_forall_nnreal_lt
    intro r hr
    obtain ⟨s, hrs, hsf⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hr
    have hrs' : (r : ℝ) < (s : ℝ) := by exact_mod_cast hrs
    obtain ⟨n, k, hkcap, hrk, hks⟩ :=
      exists_dyadic_grid_between r s hrs' s.property
    have hrk' : (r : ℝ≥0∞) ≤ (k : ℝ≥0∞) * dyadicCoeff n := by
      rw [cast_mul_dyadicCoeff]
      have he : (r : ℝ≥0∞) = ENNReal.ofReal (r : ℝ) := by simp
      rw [he]
      exact ENNReal.ofReal_le_ofReal hrk.le
    have hks' : (k : ℝ≥0∞) * dyadicCoeff n ≤ (s : ℝ≥0∞) := by
      rw [cast_mul_dyadicCoeff]
      have he : (s : ℝ≥0∞) = ENNReal.ofReal (s : ℝ) := by simp
      rw [he]
      exact ENNReal.ofReal_le_ofReal hks
    calc
      (r : ℝ≥0∞) ≤ (k : ℝ≥0∞) * dyadicCoeff n := hrk'
      _ ≤ dyadicApprox f n x := scale_le_levelStepSum hf _ hkcap x (hks'.trans_lt hsf)
      _ ≤ ⨆ m : ℕ, dyadicApprox f m x := le_iSup (fun m : ℕ => dyadicApprox f m x) n

end CantorFubini
