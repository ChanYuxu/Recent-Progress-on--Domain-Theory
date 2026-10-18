import CoreCompactNonSober.Localization

/-!
# Protection against earlier positive points

Source: `lem:protection`. The proof uses the proved minimal localization
cardinal, and translates failure of eventual hole membership into genuine
configuration membership at arbitrarily large coordinates.
-/

set_option autoImplicit false

namespace CoreCompactNonSober.Ambient

open Set Cardinal Localization

/-- The uniform tail deletion property used in the source's height-cut
argument: one common letter pattern is omitted beyond a finite cutoff. -/
def TailOmission (p : Carrier) : Prop :=
  ∃ f : (j : Coordinate) → Alphabet j, ∃ M : ℕ,
    ∀ j : Coordinate, M ≤ j.val → f j ∉ configuration p j

theorem TailOmission.hasHole {p : Carrier} (hp : TailOmission p) : HasHole p := by
  obtain ⟨f, M, hf⟩ := hp
  let j : Coordinate := ⟨max M 2, le_max_right _ _⟩
  exact ⟨j, f j, hf j (le_max_left _ _)⟩

theorem positive_holeCount_lt_baseWidth (p : Carrier) (hp : Positive p)
    (j : Coordinate) : holeCount j (configuration p j) < baseWidth j := by
  have hcap : 1 + (holeCount j (configuration p j) : ℝ) ≤
      (2 : ℝ) ^ ((1 - height p) * (j.val : ℝ)) :=
    (capacity_ge_iff_rpow j _ hp).mp (p.property j)
  have hexp : (1 - height p) * (j.val : ℝ) < (j.val : ℝ) := by
    have hprod := mul_pos hp (coordinate_real_pos j)
    nlinarith
  have hpow := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2) hexp
  rw [Real.rpow_natCast] at hpow
  have hcast : (holeCount j (configuration p j) : ℝ) < (baseWidth j : ℕ) := by
    simp only [baseWidth, Nat.cast_pow, Nat.cast_ofNat]
    linarith
  exact_mod_cast hcast

def holeSlalom (p : Carrier) (hp : Positive p) : Slalom Alphabet baseWidth where
  list j := Finset.univ \ configuration p j
  bound j := (positive_holeCount_lt_baseWidth p hp j).le

def Protects (P : Set Carrier) (f : (j : Coordinate) → Alphabet j) : Prop :=
  ∀ p ∈ P, ∀ N : ℕ, ∃ j : Coordinate, N ≤ j.val ∧ f j ∈ configuration p j

theorem exists_protection_pattern (P : Set Carrier)
    (hpositive : ∀ p ∈ P, Positive p) (hsmall : Cardinal.mk P < lambda) :
    ∃ f : (j : Coordinate) → Alphabet j, Protects P f := by
  let s : P → Slalom Alphabet baseWidth := fun p ↦ holeSlalom p.val (hpositive p.val p.property)
  have hsmallF : Cardinal.mk (Set.range s) < loc Alphabet baseWidth :=
    Cardinal.mk_range_le.trans_lt hsmall
  have hnot := small_family_not_capturing hsmallF
  obtain ⟨f, hf⟩ := not_forall.mp hnot
  refine ⟨f, ?_⟩
  intro p hp N
  by_contra hnone
  apply hf
  refine ⟨s ⟨p, hp⟩, Set.mem_range_self _, N, ?_⟩
  intro j hj
  change f j ∈ Finset.univ \ configuration p j
  apply Finset.mem_sdiff.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  exact fun hmem ↦ hnone ⟨j, hj, hmem⟩

theorem not_le_of_tail_omission {P : Set Carrier} {f : (j : Coordinate) → Alphabet j}
    (hf : Protects P f) {p : Carrier} (hp : p ∈ P) (q : Carrier) (N : ℕ)
    (hq : ∀ j : Coordinate, N ≤ j.val → f j ∉ configuration q j) : ¬ p ≤ q := by
  intro hpq
  obtain ⟨j, hj, hmem⟩ := hf p hp N
  exact hq j hj (((le_iff p q).mp hpq).2 j hmem)

end CoreCompactNonSober.Ambient
