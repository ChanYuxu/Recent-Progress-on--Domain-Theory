import CoreCompactNonSober.LocalizationPullback
import CoreCompactNonSober.WidthEstimates
import Mathlib.Data.Nat.Log
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Intervals

/-!
# The manuscript's two-pass alphabet pullback

Source: `lem:alphabet-pullback`, lines 1158–1235. A single minimum
capturing family is used first at the coordinates `2j`, then at `2n+2`.
The intervening nonempty alphabets are exactly `T_φ(j)`, and the second
pass selects tuples in their dyadic blocks before projecting them.
-/

set_option autoImplicit false

namespace CoreCompactNonSober.Localization

open Set Cardinal
open Ambient (Coordinate Alphabet alphabetSize distinguishedLetter)
open scoped BigOperators

def doubleCoordinate (j : Coordinate) : Coordinate :=
  ⟨2 * j.val, by have := j.property; omega⟩

theorem doubleCoordinate_injective : Function.Injective doubleCoordinate := by
  intro j k h
  apply Subtype.ext
  have heq := congrArg Subtype.val h
  dsimp [doubleCoordinate] at heq
  omega

theorem doubleCoordinate_ge (j : Coordinate) : j.val ≤ (doubleCoordinate j).val := by
  dsimp [doubleCoordinate]
  omega

namespace TwoPass

/-- The source's explicitly padded sequence: at unused coordinates the
entry is the distinguished letter (internal `0`, manuscript `1`). -/
noncomputable def paddedPoint {Y : Coordinate → Type}
    {φ : Coordinate → Coordinate} (e : ∀ j, Y j ↪ Alphabet (φ j))
    (y : ∀ j, Y j) (i : Coordinate) : Alphabet i := by
  classical
  exact if hi : ∃ j, φ j = i then hi.choose_spec ▸ e hi.choose (y hi.choose)
    else distinguishedLetter i

theorem paddedPoint_at {Y : Coordinate → Type}
    {φ : Coordinate → Coordinate} (hφ : Function.Injective φ)
    (e : ∀ j, Y j ↪ Alphabet (φ j)) (y : ∀ j, Y j) (j : Coordinate) :
    paddedPoint e y (φ j) = e j (y j) := by
  classical
  unfold paddedPoint
  rw [dif_pos ⟨j, rfl⟩]
  have htransport : ∀ k (hk : φ k = φ j), hk ▸ e k (y k) = e j (y j) := by
    intro k hk
    have hkj : k = j := hφ hk
    subst k
    rfl
  exact htransport _ _

theorem paddedPoint_unused {Y : Coordinate → Type}
    {φ : Coordinate → Coordinate} (e : ∀ j, Y j ↪ Alphabet (φ j))
    (y : ∀ j, Y j) (i : Coordinate) (hi : ¬ ∃ j, φ j = i) :
    paddedPoint e y i = distinguishedLetter i := by
  unfold paddedPoint
  rw [dif_neg hi]

abbrev Index (n : ℕ) := ↥(Finset.Ico (2 ^ n) (2 ^ (n + 1)))

theorem index_card (n : ℕ) : Fintype.card (Index n) = 2 ^ n := by
  simp only [Index, Fintype.card_coe, Nat.card_Ico, pow_succ]
  omega

/-- The exact finite sum printed in the logarithmic block estimate, written
without natural-number subtraction on its right-hand side. -/
theorem block_exponent_sum_identity (n : ℕ) :
    (∑ j : Index n, 2 * j.val) + 2 ^ n = 3 * 2 ^ (2 * n) := by
  rw [Finset.sum_coe_sort, ← Finset.mul_sum]
  have hab : 2 ^ n ≤ 2 ^ (n + 1) := by
    apply pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ))
    omega
  have hsplit := Finset.sum_range_add_sum_Ico (fun i : ℕ ↦ i) hab
  have hlo := Finset.sum_range_id_mul_two (2 ^ n)
  have hhi := Finset.sum_range_id_mul_two (2 ^ (n + 1))
  have ha : 1 ≤ 2 ^ n := Nat.one_le_pow _ _ (by decide)
  have hb : 1 ≤ 2 ^ (n + 1) := Nat.one_le_pow _ _ (by decide)
  have hmullo : 2 ^ n * (2 ^ n - 1) + 2 ^ n = 2 ^ n * 2 ^ n := by
    calc
      _ = 2 ^ n * (2 ^ n - 1 + 1) := by ring
      _ = _ := by rw [Nat.sub_add_cancel ha]
  have hmulhi : 2 ^ (n + 1) * (2 ^ (n + 1) - 1) + 2 ^ (n + 1) =
      2 ^ (n + 1) * 2 ^ (n + 1) := by
    calc
      _ = 2 ^ (n + 1) * (2 ^ (n + 1) - 1 + 1) := by ring
      _ = _ := by rw [Nat.sub_add_cancel hb]
  rw [pow_succ] at hhi hmulhi hsplit
  have heq : 2 ^ (2 * n) = 2 ^ n * 2 ^ n := by
    rw [show 2 * n = n + n by omega, pow_add]
  rw [heq]
  rw [pow_succ]
  nlinarith

theorem block_exponent_sum_lt (n : ℕ) :
    (∑ j : Index n, 2 * j.val) < 2 ^ (2 * n + 2) := by
  have hs := block_exponent_sum_identity n
  have hp : 0 < (2 : ℕ) ^ (2 * n) := by positivity
  have ha : 0 ≤ (2 : ℕ) ^ n := Nat.zero_le _
  calc
    (∑ j : Index n, 2 * j.val) < 2 ^ (2 * n) * 4 := by omega
    _ = 2 ^ (2 * n + 2) := by rw [pow_add]; norm_num

def coordinate (k : Coordinate) (j : Index (k.val - 1)) : Coordinate :=
  ⟨j.val, by
    have hpow : 2 ≤ 2 ^ (k.val - 1) := by
      have hk := k.property
      simpa using pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ))
        (show 1 ≤ k.val - 1 by omega)
    exact hpow.trans (Finset.mem_Ico.mp j.property).1⟩

def source (k : Coordinate) : Coordinate :=
  ⟨2 * k.val, by have := k.property; omega⟩

theorem source_injective : Function.Injective source := doubleCoordinate_injective

theorem source_ge (k : Coordinate) : k.val ≤ (source k).val := doubleCoordinate_ge k

def blockOf (j : Coordinate) : Coordinate :=
  ⟨Nat.log 2 j.val + 1, by
    have hlog := Nat.log_pos (by decide : 1 < 2) j.property
    omega⟩

def indexInBlock (j : Coordinate) : Index ((blockOf j).val - 1) :=
  ⟨j.val, by
    simp only [blockOf, Nat.add_sub_cancel]
    exact Finset.mem_Ico.mpr
      ⟨Nat.pow_log_le_self 2 (by have := j.property; omega),
        Nat.lt_pow_succ_log_self (by decide) j.val⟩⟩

@[simp] theorem coordinate_indexInBlock (j : Coordinate) :
    coordinate (blockOf j) (indexInBlock j) = j := rfl

theorem blockOf_large {N : ℕ} (j : Coordinate) (hj : 2 ^ N ≤ j.val) :
    N ≤ (blockOf j).val - 1 := by
  simpa only [blockOf, Nat.add_sub_cancel] using
    Nat.le_log_of_pow_le (by decide : 1 < 2) hj

variable {Y : Coordinate → Type} [∀ j, Fintype (Y j)]

noncomputable def firstList (iota : ∀ j, Y j ↪ Alphabet (doubleCoordinate j))
    (y₀ : ∀ j, Y j) (φ : Slalom Alphabet baseWidth) (j : Coordinate) : Finset (Y j) := by
  classical
  let R := pullbackList iota φ j
  exact if R.Nonempty then R else {y₀ j}

theorem firstList_nonempty (iota : ∀ j, Y j ↪ Alphabet (doubleCoordinate j))
    (y₀ : ∀ j, Y j) (φ : Slalom Alphabet baseWidth) (j : Coordinate) :
    (firstList iota y₀ φ j).Nonempty := by
  classical
  unfold firstList
  dsimp only
  split_ifs with h
  · exact h
  · exact Finset.singleton_nonempty _

theorem pullback_mem_firstList (iota : ∀ j, Y j ↪ Alphabet (doubleCoordinate j))
    (y₀ : ∀ j, Y j) (φ : Slalom Alphabet baseWidth) (j : Coordinate)
    (y : Y j) (hy : iota j y ∈ φ.list (doubleCoordinate j)) :
    y ∈ firstList iota y₀ φ j := by
  classical
  have hyR : y ∈ pullbackList iota φ j := by
    unfold pullbackList
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hy
  unfold firstList
  dsimp only
  rw [if_pos ⟨y, hyR⟩]
  exact hyR

theorem firstList_card_le (iota : ∀ j, Y j ↪ Alphabet (doubleCoordinate j))
    (y₀ : ∀ j, Y j) (φ : Slalom Alphabet baseWidth) (j : Coordinate) :
    (firstList iota y₀ φ j).card ≤ 2 ^ (2 * j.val) := by
  classical
  unfold firstList
  dsimp only
  split_ifs with h
  · exact (pullbackList_card_le iota φ j).trans (φ.bound (doubleCoordinate j))
  · simp only [Finset.card_singleton]
    exact Nat.one_le_pow _ _ (by decide)

abbrev Tuple (T : (j : Coordinate) → Finset (Y j)) (k : Coordinate) :=
  (j : Index (k.val - 1)) → ↥(T (coordinate k j))

theorem tuple_card_le (T : (j : Coordinate) → Finset (Y j))
    (hT : ∀ j, (T j).card ≤ 2 ^ (2 * j.val)) (k : Coordinate) :
    Fintype.card (Tuple T k) ≤ alphabetSize (source k) := by
  classical
  rw [Fintype.card_pi]
  calc
    ∏ j : Index (k.val - 1), Fintype.card ↥(T (coordinate k j)) ≤
        ∏ j : Index (k.val - 1), 2 ^ (2 * j.val) := by
      apply Finset.prod_le_prod
      · intro _ _; exact Nat.zero_le _
      · intro j _
        rw [Fintype.card_coe]
        exact hT (coordinate k j)
    _ = 2 ^ (∑ j : Index (k.val - 1), 2 * j.val) :=
      Finset.prod_pow_eq_pow_sum _ _ _
    _ ≤ 2 ^ (2 ^ (2 * (k.val - 1) + 2)) :=
      pow_le_pow_right₀ (by decide) (block_exponent_sum_lt _).le
    _ = alphabetSize (source k) := by
      change 2 ^ (2 ^ (2 * (k.val - 1) + 2)) = 2 ^ (2 ^ (2 * k.val))
      have hk := k.property
      have heq : 2 * (k.val - 1) + 2 = 2 * k.val := by omega
      rw [heq]

noncomputable def tupleEmbedding (T : (j : Coordinate) → Finset (Y j))
    (hT : ∀ j, (T j).card ≤ 2 ^ (2 * j.val)) (k : Coordinate) :
    Tuple T k ↪ Alphabet (source k) :=
  Classical.choice (Function.Embedding.nonempty_of_card_le
    (by simpa only [Fintype.card_fin] using tuple_card_le T hT k))

def blockPoint {T : (j : Coordinate) → Finset (Y j)}
    (x : (j : Coordinate) → ↥(T j)) (k : Coordinate) : Tuple T k :=
  fun j ↦ x (coordinate k j)

theorem eventually_block_width {a : ℝ} (ha : 0 < a) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ j : Coordinate, 2 ^ n ≤ j.val →
      2 ^ (2 * n + 2) ≤ exponentialWidth a j := by
  obtain ⟨N, hN⟩ := eventually_linear_le_dyadic (a := a / 2)
    (show (0 : ℝ) < a / 2 by positivity)
  refine ⟨max N 1, ?_⟩
  intro n hn j hj
  have hlinear : 2 * (n : ℝ) + 2 ≤ a * (2 : ℝ) ^ n := by
    have hl := hN n (by omega)
    nlinarith [show (0 : ℝ) ≤ (n : ℝ) by positivity]
  have hcast : (2 : ℝ) ^ n ≤ (j.val : ℝ) := by exact_mod_cast hj
  have hexp : ((2 * n + 2 : ℕ) : ℝ) ≤ a * (j.val : ℝ) := by
    push_cast
    exact hlinear.trans (mul_le_mul_of_nonneg_left hcast ha.le)
  have hpow := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hexp
  rw [Real.rpow_natCast] at hpow
  apply Nat.le_floor
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using hpow

noncomputable def blockCutoff {a : ℝ} (ha : 0 < a) : ℕ :=
  max 1 (Classical.choose (eventually_block_width ha))

theorem blockCutoff_width {a : ℝ} (ha : 0 < a) (j : Coordinate)
    (hj : blockCutoff ha ≤ (blockOf j).val - 1) :
    baseWidth (source (blockOf j)) ≤ exponentialWidth a j := by
  have hn := (Classical.choose_spec (eventually_block_width ha))
    ((blockOf j).val - 1) ((le_max_right _ _).trans hj) j
    (Finset.mem_Ico.mp (indexInBlock j).property).1
  have heq : 2 * ((blockOf j).val - 1) + 2 = 2 * (blockOf j).val := by
    have := (blockOf j).property
    omega
  simpa only [baseWidth, source, heq] using hn

noncomputable def secondList
    (T : (j : Coordinate) → Finset (Y j))
    (hT : ∀ j, (T j).card ≤ 2 ^ (2 * j.val))
    (χ : Slalom Alphabet baseWidth) (j : Coordinate) : Finset (Y j) := by
  classical
  exact (pullbackList (tupleEmbedding T hT) χ (blockOf j)).image
    (fun v ↦ (v (indexInBlock j)).val)

theorem secondList_card_le
    (T : (j : Coordinate) → Finset (Y j))
    (hT : ∀ j, (T j).card ≤ 2 ^ (2 * j.val))
    (χ : Slalom Alphabet baseWidth) (j : Coordinate) :
    (secondList T hT χ j).card ≤ baseWidth (source (blockOf j)) := by
  classical
  exact Finset.card_image_le.trans
    ((pullbackList_card_le (tupleEmbedding T hT) χ (blockOf j)).trans
      (χ.bound (source (blockOf j))))

noncomputable def slalom
    (iota : ∀ j, Y j ↪ Alphabet (doubleCoordinate j)) (y₀ : ∀ j, Y j)
    {a : ℝ} (ha : 0 < a) (φ χ : Slalom Alphabet baseWidth) :
    Slalom Y (exponentialWidth a) := by
  classical
  let T := firstList iota y₀ φ
  let hT := firstList_card_le iota y₀ φ
  exact {
    list := fun j ↦ if blockCutoff ha ≤ (blockOf j).val - 1
      then secondList T hT χ j else {y₀ j}
    bound := fun j ↦ by
      split_ifs with hj
      · exact (secondList_card_le T hT χ j).trans (blockCutoff_width ha j hj)
      · simpa using exponentialWidth_pos ha.le j }

theorem captures
    (iota : ∀ j, Y j ↪ Alphabet (doubleCoordinate j)) (y₀ : ∀ j, Y j)
    {a : ℝ} (ha : 0 < a) {F : Set (Slalom Alphabet baseWidth)}
    (hF : IsCapturing F) (x : ∀ j, Y j) :
    ∃ φ ∈ F, ∃ χ ∈ F, Captures (slalom iota y₀ ha φ χ) x := by
  classical
  let z := paddedPoint iota x
  have hz := paddedPoint_at doubleCoordinate_injective iota x
  obtain ⟨φ, hφF, N, hφ⟩ := hF z
  let T := firstList iota y₀ φ
  have hTne := firstList_nonempty iota y₀ φ
  have hxT : ∀ j : Coordinate, N ≤ j.val → x j ∈ T j := by
    intro j hj
    apply pullback_mem_firstList iota y₀ φ j
    rw [← hz j]
    exact hφ (doubleCoordinate j) (hj.trans (doubleCoordinate_ge j))
  let x' : (j : Coordinate) → ↥(T j) := fun j ↦
    if h : x j ∈ T j then ⟨x j, h⟩ else ⟨(hTne j).choose, (hTne j).choose_spec⟩
  have hxx' : ∀ j : Coordinate, N ≤ j.val → (x' j).val = x j := by
    intro j hj
    dsimp [x']
    rw [dif_pos (hxT j hj)]
  let w := paddedPoint (tupleEmbedding T (firstList_card_le iota y₀ φ)) (blockPoint x')
  have hw := paddedPoint_at source_injective
    (tupleEmbedding T (firstList_card_le iota y₀ φ)) (blockPoint x')
  obtain ⟨χ, hχF, M, hχ⟩ := hF w
  refine ⟨φ, hφF, χ, hχF, max N (2 ^ max (blockCutoff ha) M), ?_⟩
  intro j hj
  have hjN : N ≤ j.val := (le_max_left _ _).trans hj
  have hjlarge : 2 ^ max (blockCutoff ha) M ≤ j.val := (le_max_right _ _).trans hj
  have hblock := blockOf_large j hjlarge
  have hjcut : blockCutoff ha ≤ (blockOf j).val - 1 := (le_max_left _ _).trans hblock
  have hjM : M ≤ (source (blockOf j)).val :=
    ((le_max_right _ _).trans hblock).trans
      ((Nat.sub_le _ _).trans (source_ge (blockOf j)))
  change x j ∈ if blockCutoff ha ≤ (blockOf j).val - 1 then
    secondList T (firstList_card_le iota y₀ φ) χ j else {y₀ j}
  rw [if_pos hjcut]
  apply Finset.mem_image.mpr
  refine ⟨blockPoint x' (blockOf j), ?_, ?_⟩
  · unfold pullbackList
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← hw (blockOf j)]
    exact hχ (source (blockOf j)) hjM
  · exact hxx' j hjN

end TwoPass

/-- The source-exact alphabet pullback, using the *same* minimum family in
both passes. Its concrete slaloms are `TwoPass.slalom iota y₀ he φ χ`. -/
theorem alphabet_pullback (Y : Coordinate → Type) [∀ j, Fintype (Y j)]
    [∀ j, Nonempty (Y j)]
    (hY : ∀ j, Fintype.card (Y j) ≤ alphabetSize (doubleCoordinate j))
    {e : ℝ} (he : 0 < e) :
    ∃ G : Set (Slalom Y (exponentialWidth e)),
      IsCapturing G ∧ Cardinal.mk G ≤ lambda := by
  classical
  let iota : ∀ j, Y j ↪ Alphabet (doubleCoordinate j) := fun j ↦
    Classical.choice (Function.Embedding.nonempty_of_card_le
      (by simpa only [Fintype.card_fin] using hY j))
  let y₀ : ∀ j, Y j := fun j ↦ Classical.choice (inferInstance : Nonempty (Y j))
  obtain ⟨F, hF, hcardF⟩ := exists_minimal_family (X := Alphabet) baseWidth_pos
  let c : F × F → Slalom Y (exponentialWidth e) :=
    fun p ↦ TwoPass.slalom iota y₀ he p.1.val p.2.val
  refine ⟨Set.range c, ?_, ?_⟩
  · intro x
    obtain ⟨φ, hφ, χ, hχ, hcap⟩ := TwoPass.captures iota y₀ he hF x
    exact ⟨c (⟨φ, hφ⟩, ⟨χ, hχ⟩), Set.mem_range_self _, hcap⟩
  · calc
      Cardinal.mk (Set.range c) ≤ Cardinal.mk (F × F) := Cardinal.mk_range_le
      _ = lambda * lambda := by rw [Cardinal.mk_prod, hcardF]; simp only [lift_id, lambda]
      _ = lambda := Cardinal.mul_eq_self aleph0_lt_lambda.le

end CoreCompactNonSober.Localization
