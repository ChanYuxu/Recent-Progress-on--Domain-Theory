import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Counting small finite subsets by their cardinalities

Source: appendix, proof of `lem:approximating-family`, lines 1254–1262.
The exact counting formula partitions subsets by cardinality; the printed
`(m+1) d^m` estimate then follows from the binomial estimates.
No option-list encoding is used.
-/

set_option autoImplicit false

namespace CoreCompactNonSober

open scoped BigOperators

abbrev SmallSubsets (α : Type) (m : ℕ) := {R : Finset α // R.card ≤ m}

noncomputable def smallSubsetsCardEquiv (α : Type) [Fintype α] (m : ℕ) :
    SmallSubsets α m ≃ Σ r : Fin (m + 1),
      ↥((Finset.univ : Finset α).powersetCard r.val) := by
  classical
  exact {
    toFun := fun R ↦ ⟨⟨R.val.card, by omega⟩,
      ⟨R.val, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, rfl⟩⟩⟩
    invFun := fun R ↦ ⟨R.2.val, by
      have hcard := (Finset.mem_powersetCard.mp R.2.property).2
      have hr := R.1.isLt
      omega⟩
    left_inv := fun R ↦ by rfl
    right_inv := fun R ↦ by
      obtain ⟨r, R, hR⟩ := R
      have hcard := (Finset.mem_powersetCard.mp hR).2
      cases r with
      | mk r hr =>
        dsimp at hcard
        subst r
        rfl }

theorem smallSubsets_card_eq (α : Type) [Fintype α] (m : ℕ) :
    Fintype.card (SmallSubsets α m) =
      ∑ r : Fin (m + 1), (Fintype.card α).choose r.val := by
  classical
  rw [Fintype.card_congr (smallSubsetsCardEquiv α m), Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro r _
  simp

theorem smallSubsets_card_le (α : Type) [Fintype α]
    (hα : 0 < Fintype.card α) (m : ℕ) :
    Fintype.card (SmallSubsets α m) ≤ (m + 1) * (Fintype.card α) ^ m := by
  rw [smallSubsets_card_eq]
  calc
    ∑ r : Fin (m + 1), (Fintype.card α).choose r.val ≤
        ∑ _r : Fin (m + 1), (Fintype.card α) ^ m := by
      apply Finset.sum_le_sum
      intro r _
      exact (Nat.choose_le_pow _ _).trans
        (pow_le_pow_right₀ (by omega) (by have := r.isLt; omega))
    _ = (m + 1) * (Fintype.card α) ^ m := by simp

end CoreCompactNonSober
