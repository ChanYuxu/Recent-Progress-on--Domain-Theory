import CoreCompactNonSober.WitnessFamily
import CoreCompactNonSober.Protection
import Mathlib.Data.Set.Finite.Lattice

/-!
# Source-facing appendix and tail-selection interfaces

Authoritative manuscript SHA256:
`9bba1776d112ff696b933960a63eefc627bb65f41f3cc4013025daeab82337bc`.
This module exposes the actual minimum localization cardinal, the printed
two-pass pullback, the precise uniform-cutoff reference family, and infinite
tail membership (not just an unproved claim of infinitude).
-/

set_option autoImplicit false

namespace CoreCompactSimplified

open Set Cardinal CoreCompactNonSober CoreCompactNonSober.Ambient
  CoreCompactNonSober.Localization

/-- The cutoff convention in `Captures` is equivalent to the manuscript's
"all but finitely many coordinates" convention. -/
theorem captures_iff_finite_exceptions {Y : Coordinate → Type} {w : Width}
    (s : Slalom Y w) (x : (j : Coordinate) → Y j) :
    Captures s x ↔ ({j : Coordinate | x j ∉ s.list j} : Set Coordinate).Finite := by
  constructor
  · rintro ⟨N, hN⟩
    have hfinite : ((fun j : Coordinate ↦ j.val) ⁻¹' {i : ℕ | i < N}).Finite :=
      Set.Finite.preimage Subtype.val_injective.injOn (Set.finite_lt_nat N)
    apply hfinite.subset
    intro j hj
    change j.val < N
    by_contra h
    exact hj (hN j (by omega))
  · intro hfinite
    obtain ⟨N, hN⟩ := (hfinite.image (fun j : Coordinate ↦ j.val)).bddAbove
    refine ⟨N + 1, ?_⟩
    intro j hj
    by_contra h
    have hle : j.val ≤ N := hN ⟨j, h, rfl⟩
    omega

/-- Definition `def:localization`: the cardinal is attained by a capturing
family and is a lower bound for the size of every capturing family. -/
theorem localization_minimum (Y : Coordinate → Type)
    [∀ j, Fintype (Y j)] [∀ j, Nonempty (Y j)]
    (w : Width) (hw : ∀ j, 0 < w j) :
    ∃ F : Set (Slalom Y w), IsCapturing F ∧ Cardinal.mk F = loc Y w ∧
      ∀ G : Set (Slalom Y w), IsCapturing G → loc Y w ≤ Cardinal.mk G := by
  obtain ⟨F, hF, hcardF⟩ := exists_minimal_family (X := Y) hw
  exact ⟨F, hF, hcardF, fun _ hG ↦ loc_le_family hG⟩

/-- Lemma `lem:lambda-bounds`. -/
theorem localization_cardinal_bounds :
    Cardinal.aleph 1 ≤ lambda ∧ lambda ≤ Cardinal.continuum := lambda_bounds

/-- Lemma `lem:alphabet-pullback`, with the printed nonempty finite
alphabets and the width `floor (2^(εj))`. -/
theorem appendix_alphabet_pullback (Y : Coordinate → Type)
    [∀ j, Fintype (Y j)] [∀ j, Nonempty (Y j)]
    (hY : ∀ j, Fintype.card (Y j) ≤ alphabetSize (doubleCoordinate j))
    {e : ℝ} (he : 0 < e) :
    ∃ F : Set (Slalom Y (exponentialWidth e)),
      IsCapturing F ∧ Cardinal.mk F ≤ lambda :=
  alphabet_pullback Y hY he

/-- Lemma `lem:approximating-family`, using the manuscript's actual `R`. -/
theorem appendix_approximating_family :
    ∃ R : Set Carrier, (∀ b ∈ R, Positive b) ∧ Cardinal.mk R ≤ lambda ∧
      ∀ (p : Carrier), Positive p → ∀ U : ScottOpens Carrier, p ∈ U →
        ∃ b ∈ R, b ∈ U ∧ b ≤ p :=
  ⟨witnessFamily, witnessFamily_positive, witnessFamily_card_le, witnessFamily_approx⟩

/-- Arbitrarily late membership from the protection lemma implies genuine
infinitude of the literal set of coordinates in the manuscript. -/
theorem protection_infinite (H : Set Carrier) (f : (j : Coordinate) → Alphabet j)
    (hf : Protects H f) :
    ∀ x ∈ H, ({j : Coordinate | f j ∈ configuration x j} : Set Coordinate).Infinite := by
  intro x hx
  let A : Set Coordinate := {j | f j ∈ configuration x j}
  apply Set.Infinite.of_image Subtype.val
  apply Set.infinite_of_not_bddAbove
  rintro ⟨N, hN⟩
  obtain ⟨j, hj, hmem⟩ := hf x hx (N + 1)
  have hle : j.val ≤ N := hN ⟨j, hmem, rfl⟩
  omega

theorem exists_infinite_tail_selection (H : Set Carrier)
    (hH : ∀ x ∈ H, Positive x) (hsmall : Cardinal.mk H < lambda) :
    ∃ f : (j : Coordinate) → Alphabet j,
      ∀ x ∈ H, ({j : Coordinate | f j ∈ configuration x j} : Set Coordinate).Infinite := by
  obtain ⟨f, hf⟩ := exists_protection_pattern H hH hsmall
  exact ⟨f, protection_infinite H f hf⟩

/-- Proposition `prop:tail-selection`, proved in the appendix. -/
theorem tail_selection :
    ∃ κ : Cardinal, Cardinal.aleph0 < κ ∧ κ ≤ Cardinal.continuum ∧
      ∃ R : Set Carrier, (∀ b ∈ R, Positive b) ∧ Cardinal.mk R ≤ κ ∧
        (∀ (p : Carrier), Positive p → ∀ V : ScottOpens Carrier, p ∈ V →
          ∃ b ∈ R, b ∈ V ∧ b ≤ p) ∧
        ∀ H : Set Carrier, (∀ x ∈ H, Positive x) → Cardinal.mk H < κ →
          ∃ f : (j : Coordinate) → Alphabet j,
            ∀ x ∈ H,
              ({j : Coordinate | f j ∈ configuration x j} : Set Coordinate).Infinite :=
  ⟨lambda, aleph0_lt_lambda, lambda_bounds.2, witnessFamily,
    witnessFamily_positive, witnessFamily_card_le, witnessFamily_approx,
    exists_infinite_tail_selection⟩

/-- The cardinal assertion in Remark `rem:CH`. -/
theorem localization_cardinal_eq_aleph_one_of_CH
    (hCH : Cardinal.continuum.{0} = Cardinal.aleph 1) :
    lambda = Cardinal.aleph 1 :=
  le_antisymm (lambda_bounds.2.trans_eq hCH) lambda_bounds.1

/-- Every cardinal strictly below the chosen recursion cardinal is countable
under CH; the construction's stage-stock estimate may apply this directly. -/
theorem smaller_cardinal_countable_of_CH
    (hCH : Cardinal.continuum.{0} = Cardinal.aleph 1)
    {μ : Cardinal.{0}} (hμ : μ < lambda) : μ ≤ Cardinal.aleph0 := by
  rw [localization_cardinal_eq_aleph_one_of_CH hCH] at hμ
  by_contra h
  have hlarge : Cardinal.aleph 1 ≤ μ := Cardinal.aleph_one_le_iff.mpr (lt_of_not_ge h)
  exact (not_le_of_gt hμ) hlarge

/-- The ordinary countable diagonal argument mentioned in Remark `rem:CH`.
Unlike the general proof this invokes countable noncapture directly. -/
theorem countable_protection_pattern (H : Set Carrier)
    (hH : ∀ x ∈ H, Positive x) (hcount : H.Countable) :
    ∃ f : (j : Coordinate) → Alphabet j, Protects H f := by
  let s : H → Slalom Alphabet baseWidth := fun x ↦ holeSlalom x.val (hH x.val x.property)
  haveI : Countable H := hcount.to_subtype
  have hnot := countable_family_not_capturing (Set.range s) (Set.countable_range s)
  obtain ⟨f, hf⟩ := not_forall.mp hnot
  refine ⟨f, ?_⟩
  intro x hx N
  by_contra hnone
  apply hf
  refine ⟨s ⟨x, hx⟩, Set.mem_range_self _, N, ?_⟩
  intro j hj
  change f j ∈ Finset.univ \ configuration x j
  apply Finset.mem_sdiff.mpr
  exact ⟨Finset.mem_univ _, fun hmem ↦ hnone ⟨j, hj, hmem⟩⟩

/-- The cardinal and countable-selection assertions of Remark `rem:CH`.
Every earlier recursion stock has size below `lambda`, so this wrapper
applies to that stock without adding a regularity assumption. -/
theorem tail_selection_under_CH
    (hCH : Cardinal.continuum.{0} = Cardinal.aleph 1) :
    lambda = Cardinal.aleph 1 ∧
      ∀ H : Set Carrier, (∀ x ∈ H, Positive x) → Cardinal.mk H < lambda →
        H.Countable ∧ ∃ f : (j : Coordinate) → Alphabet j,
          ∀ x ∈ H,
            ({j : Coordinate | f j ∈ configuration x j} : Set Coordinate).Infinite := by
  refine ⟨localization_cardinal_eq_aleph_one_of_CH hCH, ?_⟩
  intro H hH hsmall
  have hcount : H.Countable := Cardinal.le_aleph0_iff_set_countable.mp
    (smaller_cardinal_countable_of_CH hCH hsmall)
  obtain ⟨f, hf⟩ := countable_protection_pattern H hH hcount
  exact ⟨hcount, f, protection_infinite H f hf⟩

end CoreCompactSimplified
