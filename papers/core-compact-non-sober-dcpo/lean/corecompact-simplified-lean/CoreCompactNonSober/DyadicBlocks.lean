import CoreCompactNonSober.LocalizationComposition
import CoreCompactNonSober.LocalizationPullback
import CoreCompactNonSober.WidthEstimates
import Mathlib.Data.Nat.Log
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Order.Interval.Finset.Nat

/-!
# Legacy dyadic block helpers, not used by this manuscript

These copied helpers belong to the older width-absorption proof. The current
source has no such lemma, and its `2n+2` construction is implemented instead
in `CoreCompactSimplified.AppendixPullback`. This legacy module is not imported
by `WidthAbsorption`, `HoleAlphabets`, `WitnessFamily`, or `AppendixSource`.
No current source-fidelity claim relies on its `2n+1` coding.
-/

set_option autoImplicit false

namespace CoreCompactNonSober.Localization

open Set Cardinal
open Ambient (Coordinate Alphabet alphabetSize)

abbrev BlockIndex (n : ℕ) := ↥(Finset.Ico (2 ^ n) (2 ^ (n + 1)))

abbrev BlockTuple (n : ℕ) := (j : BlockIndex n) → Fin (2 ^ j.val)

theorem blockIndex_card (n : ℕ) : Fintype.card (BlockIndex n) = 2 ^ n := by
  simp only [BlockIndex, Fintype.card_coe, Nat.card_Ico, pow_succ]
  omega

theorem blockTuple_card_le (n : ℕ) :
    Fintype.card (BlockTuple n) ≤ 2 ^ (2 ^ (2 * n + 1)) := by
  rw [Fintype.card_pi]
  calc
    ∏ j : BlockIndex n, Fintype.card (Fin (2 ^ j.val)) ≤
        ∏ _j : BlockIndex n, 2 ^ (2 ^ (n + 1)) := by
      apply Finset.prod_le_prod
      · intro j _
        exact Nat.zero_le _
      · intro j _
        simp only [Fintype.card_fin]
        exact pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ))
          (Finset.mem_Ico.mp j.property).2.le
    _ = (2 ^ (2 ^ (n + 1))) ^ (2 ^ n) := by
      rw [Finset.prod_const, Finset.card_univ, blockIndex_card]
    _ = 2 ^ (2 ^ (2 * n + 1)) := by
      rw [← pow_mul, ← pow_add]
      congr 2
      omega

abbrev BlockAlphabet (k : Coordinate) := BlockTuple (k.val - 1)

def blockSource (k : Coordinate) : Coordinate :=
  ⟨2 * k.val - 1, by have := k.property; omega⟩

theorem blockSource_injective : Function.Injective blockSource := by
  intro k l h
  apply Subtype.ext
  have hk := k.property
  have hl := l.property
  have heq := congrArg Subtype.val h
  dsimp [blockSource] at heq
  omega

theorem blockSource_ge (k : Coordinate) : k.val ≤ (blockSource k).val := by
  have := k.property
  dsimp [blockSource]
  omega

theorem blockAlphabet_card_le (k : Coordinate) :
    Fintype.card (BlockAlphabet k) ≤ Fintype.card (Alphabet (blockSource k)) := by
  have heq : 2 * (k.val - 1) + 1 = 2 * k.val - 1 := by
    have := k.property
    omega
  change Fintype.card (BlockTuple (k.val - 1)) ≤
    Fintype.card (Fin (2 ^ (2 ^ (2 * k.val - 1))))
  rw [Fintype.card_fin]
  simpa only [heq] using blockTuple_card_le (k.val - 1)

noncomputable def blockEmbedding (k : Coordinate) :
    BlockAlphabet k ↪ Alphabet (blockSource k) :=
  Classical.choice (Function.Embedding.nonempty_of_card_le (blockAlphabet_card_le k))

theorem blockCoordinate_ge_two (k : Coordinate) (j : BlockIndex (k.val - 1)) :
    2 ≤ j.val := by
  have hpow : 2 ≤ 2 ^ (k.val - 1) := by
    have hk := k.property
    simpa using pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ))
      (show 1 ≤ k.val - 1 by omega)
  exact hpow.trans (Finset.mem_Ico.mp j.property).1

def blockPoint (x : (j : Coordinate) → Fin (baseWidth j))
    (k : Coordinate) : BlockAlphabet k :=
  fun j ↦ x ⟨j.val, blockCoordinate_ge_two k j⟩

def blockOf (j : Coordinate) : Coordinate :=
  ⟨Nat.log 2 j.val + 1, by
    have hlog := Nat.log_pos (by decide : 1 < 2) j.property
    omega⟩

def indexInBlock (j : Coordinate) : BlockIndex ((blockOf j).val - 1) :=
  ⟨j.val, by
    simp only [blockOf, Nat.add_sub_cancel]
    apply Finset.mem_Ico.mpr
    exact ⟨Nat.pow_log_le_self 2 (by have := j.property; omega),
      Nat.lt_pow_succ_log_self (by decide) j.val⟩⟩

theorem blockOf_large {N : ℕ} (j : Coordinate) (hj : 2 ^ N ≤ j.val) :
    N ≤ (blockOf j).val := by
  have hlog := Nat.le_log_of_pow_le (by decide : 1 < 2) hj
  dsimp [blockOf]
  omega

@[simp] theorem blockPoint_index (x : (j : Coordinate) → Fin (baseWidth j))
    (j : Coordinate) : blockPoint x (blockOf j) (indexInBlock j) = x j := by
  rfl

noncomputable def projectBlockSlalom (a : ℝ)
    (s : Slalom BlockAlphabet (fun k ↦ baseWidth (blockSource k))) :
    Slalom (fun j ↦ Fin (baseWidth j)) (exponentialWidth a) := by
  classical
  let L (j : Coordinate) :=
    (s.list (blockOf j)).image (fun x ↦ x (indexInBlock j))
  exact {
    list := fun j ↦ if baseWidth (blockSource (blockOf j)) ≤ exponentialWidth a j
      then L j else ∅
    bound := fun j ↦ by
      split_ifs with hj
      · exact (Finset.card_image_le.trans (s.bound (blockOf j))).trans hj
      · simp }

theorem projectBlockSlalom_captures {a : ℝ} (ha : 0 < a)
    {s : Slalom BlockAlphabet (fun k ↦ baseWidth (blockSource k))}
    {x : (j : Coordinate) → Fin (baseWidth j)} (hs : Captures s (blockPoint x)) :
    Captures (projectBlockSlalom a s) x := by
  classical
  obtain ⟨M, hM⟩ := hs
  obtain ⟨N, hN⟩ := eventually_block_width ha
  refine ⟨2 ^ (max M N), ?_⟩
  intro j hj
  have hlog : max M N ≤ Nat.log 2 j.val :=
    Nat.le_log_of_pow_le (by decide : 1 < 2) hj
  have hjM : M ≤ (blockOf j).val := by dsimp [blockOf]; omega
  have hwidth : baseWidth (blockSource (blockOf j)) ≤ exponentialWidth a j := by
    have h := hN (Nat.log 2 j.val) (by omega) j
      (Nat.pow_log_le_self 2 (by have := j.property; omega))
    have heq : 2 * (Nat.log 2 j.val + 1) - 1 = 2 * Nat.log 2 j.val + 1 := by omega
    simpa only [baseWidth, blockSource, blockOf, heq] using h
  change x j ∈ if baseWidth (blockSource (blockOf j)) ≤ exponentialWidth a j
    then (s.list (blockOf j)).image (fun y ↦ y (indexInBlock j)) else ∅
  rw [if_pos hwidth]
  exact Finset.mem_image.mpr ⟨blockPoint x (blockOf j), hM (blockOf j) hjM,
    blockPoint_index x j⟩

end CoreCompactNonSober.Localization
