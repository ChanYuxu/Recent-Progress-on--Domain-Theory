import FiniteValuationApproximable.ContinuousValuation.JonesGrid

/-!
# Uniform approximation by Jones grids

The finite lower grids from `JonesGrid.lean` miss a bounded integrand by at
most one mesh.  A cutoff can be chosen uniformly from the finite bound stored
in `BoundedScottFunction`.
-/

set_option autoImplicit false
set_option linter.unnecessarySimpa false

universe u

namespace FiniteValuationApproximable
namespace ContinuousValuation
namespace JonesGrid

open scoped BigOperators ENNReal

variable {D : Type u} [Preorder D]

noncomputable section

theorem realValue_nonneg (f : BoundedScottFunction D)
    (n M : Nat) (x : D) :
    0 ≤ realValue f n M x := by
  classical
  unfold realValue
  exact Finset.sum_nonneg fun k _ => by
    by_cases hk : ENNReal.ofReal (threshold n k) < f x
    · rw [if_pos hk]
      exact delta_nonneg n
    · rw [if_neg hk]

theorem realValue_le_succ (f : BoundedScottFunction D)
    (n M : Nat) (x : D) :
    realValue f n M x ≤ realValue f n (M + 1) x := by
  classical
  unfold realValue
  rw [Finset.sum_range_succ]
  apply le_add_of_nonneg_right
  by_cases hM : ENNReal.ofReal (threshold n M) < f x
  · rw [if_pos hM]
    exact delta_nonneg n
  · rw [if_neg hM]

@[simp] theorem cap_succ (n M : Nat) :
    cap n (M + 1) = cap n M + delta n := by
  unfold cap
  push_cast
  ring

/-- If the cutoff height dominates `f x`, the grid at `x` misses it by at
most one mesh. -/
theorem upper_of_le_cap (f : BoundedScottFunction D)
    (n M : Nat) (x : D)
    (hcap : f x ≤ ENNReal.ofReal (cap n M)) :
    f x ≤ ENNReal.ofReal (realValue f n M x + delta n) := by
  induction M with
  | zero =>
      have hf0 : f x = 0 := by
        apply le_antisymm
        · simpa [cap] using hcap
        · exact bot_le
      rw [hf0]
      exact bot_le
  | succ M ih =>
      by_cases hprev : ENNReal.ofReal (cap n M) < f x
      · have hfull : realValue f n M x = cap n M :=
          realValue_eq_cap_of_last f n M x hprev
        have hmono : realValue f n M x ≤ realValue f n (M + 1) x :=
          realValue_le_succ f n M x
        have hreal : cap n (M + 1) ≤
            realValue f n (M + 1) x + delta n := by
          rw [cap_succ, ← hfull]
          exact add_le_add hmono le_rfl
        exact hcap.trans (ENNReal.ofReal_le_ofReal hreal)
      · have hcapM : f x ≤ ENNReal.ofReal (cap n M) :=
          not_lt.mp hprev
        have hrec := ih hcapM
        have hreal : realValue f n M x + delta n ≤
            realValue f n (M + 1) x + delta n :=
          add_le_add (realValue_le_succ f n M x) le_rfl
        exact hrec.trans (ENNReal.ofReal_le_ofReal hreal)

/-- For every mesh there is a finite cutoff dominating the bounded integrand
uniformly. -/
theorem exists_uniform_cutoff (f : BoundedScottFunction D) (n : Nat) :
    ∃ M : Nat, ∀ x : D, f x ≤ ENNReal.ofReal (cap n M) := by
  rcases f.bounded with ⟨c, hcTop, hfc⟩
  rcases ENNReal.exists_nat_gt hcTop with ⟨K, hcK⟩
  refine ⟨K * (n + 1), fun x => ?_⟩
  have hcapReal : cap n (K * (n + 1)) = (K : ℝ) := by
    unfold cap delta
    push_cast
    have hn : (n + 1 : ℝ) ≠ 0 := by positivity
    field_simp
  rw [hcapReal]
  simpa using (hfc x).trans hcK.le

/-- Uniform one-mesh approximation. -/
theorem exists_uniform_upper (f : BoundedScottFunction D) (n : Nat) :
    ∃ M : Nat, ∀ x : D,
      f x ≤ ENNReal.ofReal (realValue f n M x + delta n) := by
  rcases exists_uniform_cutoff f n with ⟨M, hM⟩
  exact ⟨M, fun x => upper_of_le_cap f n M x (hM x)⟩

end
end JonesGrid
end ContinuousValuation
end FiniteValuationApproximable
