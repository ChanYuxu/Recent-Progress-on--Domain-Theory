import FiniteValuationApproximable.ContinuousValuation.JonesIntegralCore
import FiniteValuationApproximable.ContinuousValuation.Superlevel

/-!
# Finite lower grids for the Jones integral

For denominator `n+1` and cutoff `M`, the grid is the finite open simple
function

`(1/(n+1)) * ∑_{k<M} χ_{(k+1)/(n+1) < f}`.

This file first proves directly that every such grid lies below `f`.  Later
files use the same explicit grids for uniform approximation and directed
monotone convergence.
-/

set_option autoImplicit false
set_option linter.unnecessarySimpa false

universe u

namespace FiniteValuationApproximable
namespace ContinuousValuation

open scoped BigOperators ENNReal

namespace JonesGrid

variable {D : Type u} [Preorder D]

noncomputable section

/-- Positive grid mesh. -/
def delta (n : Nat) : ℝ := 1 / (n + 1 : ℝ)

theorem delta_pos (n : Nat) : 0 < delta n := by
  unfold delta
  positivity

theorem delta_nonneg (n : Nat) : 0 ≤ delta n := (delta_pos n).le

/-- The `(k+1)`-st strict grid threshold. -/
def threshold (n k : Nat) : ℝ := (k + 1 : ℝ) * delta n

/-- The numerical height of a grid with `M` active levels. -/
def cap (n M : Nat) : ℝ := (M : ℝ) * delta n

@[simp] theorem threshold_eq_cap_succ (n k : Nat) :
    threshold n k = cap n (k + 1) := by
  simp [threshold, cap]

/-- A strict threshold open of the integrand. -/
def levelOpen (f : BoundedScottFunction D) (n k : Nat) : ScottOpen D :=
  f.superlevel (ENNReal.ofReal (threshold n k))

/-- The finite lower grid as an open simple function. -/
def simple (f : BoundedScottFunction D) (n M : Nat) :
    OpenSimpleFunction D where
  arity := M
  coeff := fun _ => delta n
  opens := fun i => levelOpen f n i.1
  coeff_nonneg := fun _ => delta_nonneg n

/-- Direct range-sum form of the pointwise grid value. -/
noncomputable def realValue (f : BoundedScottFunction D)
    (n M : Nat) (x : D) : ℝ :=
  ∑ k ∈ Finset.range M,
    if ENNReal.ofReal (threshold n k) < f x then delta n else 0

theorem simple_value_eq_realValue (f : BoundedScottFunction D)
    (n M : Nat) (x : D) :
    (simple f n M).value x = realValue f n M x := by
  classical
  unfold OpenSimpleFunction.value openStepValue realValue
  change (∑ i : Fin M,
      if x ∈ levelOpen f n i.1 then delta n else 0) = _
  simpa [levelOpen, BoundedScottFunction.mem_superlevel_iff] using
    (Fin.sum_univ_eq_sum_range
      (fun k : Nat =>
        if ENNReal.ofReal (threshold n k) < f x then delta n else 0) M)

/-- If the last threshold is active, every earlier threshold is active and the
grid has its full numerical height. -/
theorem realValue_eq_cap_of_last
    (f : BoundedScottFunction D) (n M : Nat) (x : D)
    (hlast : ENNReal.ofReal (cap n M) < f x) :
    realValue f n M x = cap n M := by
  classical
  unfold realValue
  calc
    (∑ k ∈ Finset.range M,
        if ENNReal.ofReal (threshold n k) < f x then delta n else 0) =
        ∑ _k ∈ Finset.range M, delta n := by
      apply Finset.sum_congr rfl
      intro k hk
      have hkNat : k + 1 ≤ M := Nat.succ_le_iff.mpr (Finset.mem_range.mp hk)
      have hreal : threshold n k ≤ cap n M := by
        unfold threshold cap
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hkNat)
          (delta_nonneg n)
      have hopen : ENNReal.ofReal (threshold n k) < f x :=
        (ENNReal.ofReal_le_ofReal hreal).trans_lt hlast
      rw [if_pos hopen]
    _ = cap n M := by
      simp [cap]

/-- Every finite grid is pointwise below the integrand. -/
theorem realValue_below
    (f : BoundedScottFunction D) (n M : Nat) (x : D) :
    ENNReal.ofReal (realValue f n M x) ≤ f x := by
  induction M with
  | zero =>
      simp [realValue]
  | succ M ih =>
      by_cases hlast : ENNReal.ofReal (cap n (M + 1)) < f x
      · rw [realValue_eq_cap_of_last f n (M + 1) x hlast]
        exact hlast.le
      · have hrec : realValue f n (M + 1) x = realValue f n M x := by
          unfold realValue
          rw [Finset.sum_range_succ]
          rw [threshold_eq_cap_succ, if_neg hlast, add_zero]
        rw [hrec]
        exact ih

theorem simple_below
    (f : BoundedScottFunction D) (n M : Nat) :
    ∀ x, ENNReal.ofReal ((simple f n M).value x) ≤ f x := by
  intro x
  rw [simple_value_eq_realValue]
  exact realValue_below f n M x

end
end JonesGrid
end ContinuousValuation
end FiniteValuationApproximable
