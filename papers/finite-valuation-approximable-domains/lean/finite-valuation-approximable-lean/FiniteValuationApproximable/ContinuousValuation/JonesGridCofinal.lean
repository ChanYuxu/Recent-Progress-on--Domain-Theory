import FiniteValuationApproximable.ContinuousValuation.JonesGridApprox

/-!
# Cofinality of the Jones grids

Every finite Scott-open simple function below a bounded integrand is bounded
by a sufficiently fine Jones grid plus one mesh.  Consequently the explicit
two-parameter grid family is cofinal in the definition of the Jones lower
integral.
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

/-- The integral of a nonnegative constant simple function over the whole
space is at most its coefficient, because `mu` is a subprobability
valuation. -/
theorem single_univ_integral_le (mu : VSub D) (c : ℝ) (hc : 0 ≤ c) :
    (OpenSimpleFunction.single c hc (ScottOpen.univ : ScottOpen D)).integral mu ≤
      ENNReal.ofReal c := by
  unfold OpenSimpleFunction.integral
  rw [OpenSimpleFunction.single_integralReal, ENNReal.ofReal_mul hc]
  rw [ENNReal.ofReal_toReal
    (ne_top_of_le_ne_top ENNReal.one_ne_top
      (mu.value_le_one (ScottOpen.univ : ScottOpen D)))]
  calc
    ENNReal.ofReal c * mu (ScottOpen.univ : ScottOpen D) ≤
        ENNReal.ofReal c * 1 := by
      gcongr
      exact mu.value_le_one (ScottOpen.univ : ScottOpen D)
    _ = ENNReal.ofReal c := mul_one _

/-- Supremum of the integrals of all explicit Jones grids. -/
noncomputable def integralSup (mu : VSub D) (f : BoundedScottFunction D) : ℝ≥0∞ :=
  ⨆ n : Nat, ⨆ M : Nat, (simple f n M).integral mu

theorem grid_integral_le_lowerIntegral (mu : VSub D)
    (f : BoundedScottFunction D) (n M : Nat) :
    (simple f n M).integral mu ≤ jonesLowerIntegral mu f :=
  JonesLowerIntegral.simple_le mu f (simple f n M) (simple_below f n M)

theorem integralSup_le_lowerIntegral (mu : VSub D)
    (f : BoundedScottFunction D) :
    integralSup mu f ≤ jonesLowerIntegral mu f := by
  unfold integralSup
  exact iSup_le fun n => iSup_le fun M => grid_integral_le_lowerIntegral mu f n M

/-- Every lower simple function is bounded in integral by the supremum of the
explicit grid integrals.  The proof uses the uniform one-mesh estimate and
then lets the mesh tend to zero. -/
theorem simple_integral_le_integralSup (mu : VSub D)
    (f : BoundedScottFunction D) (s : OpenSimpleFunction D)
    (hs : ∀ x, ENNReal.ofReal (s.value x) ≤ f x) :
    s.integral mu ≤ integralSup mu f := by
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _hsupFinite
  have hεReal : 0 < (ε : ℝ) := by exact_mod_cast hε
  rcases exists_nat_one_div_lt hεReal with ⟨n, hn⟩
  have hdelta : delta n < (ε : ℝ) := by
    simpa [delta] using hn
  rcases exists_uniform_upper f n with ⟨M, hM⟩
  let q : OpenSimpleFunction D := simple f n M
  let e : OpenSimpleFunction D :=
    OpenSimpleFunction.single (delta n) (delta_nonneg n)
      (ScottOpen.univ : ScottOpen D)
  have hpoint : ∀ x, s.value x ≤ (OpenSimpleFunction.add q e).value x := by
    intro x
    have hENN : ENNReal.ofReal (s.value x) ≤
        ENNReal.ofReal (realValue f n M x + delta n) :=
      (hs x).trans (hM x)
    have hreal : s.value x ≤ realValue f n M x + delta n :=
      (ENNReal.ofReal_le_ofReal_iff
        (add_nonneg (realValue_nonneg f n M x) (delta_nonneg n))).mp hENN
    simpa [q, e, OpenSimpleFunction.add_value,
      simple_value_eq_realValue] using hreal
  have hmono : s.integral mu ≤
      q.integral mu + e.integral mu := by
    simpa only [OpenSimpleFunction.add_integral] using
      (OpenSimpleFunction.integral_mono mu hpoint)
  have hq : q.integral mu ≤ integralSup mu f := by
    unfold integralSup
    exact le_iSup_of_le n (le_iSup_of_le M (by rfl))
  have he : e.integral mu ≤ ENNReal.ofReal (delta n) := by
    exact single_univ_integral_le mu (delta n) (delta_nonneg n)
  have hdeltaENN : ENNReal.ofReal (delta n) ≤ (ε : ℝ≥0∞) := by
    simpa using ENNReal.ofReal_le_ofReal hdelta.le
  calc
    s.integral mu ≤ q.integral mu + e.integral mu := hmono
    _ ≤ q.integral mu + ENNReal.ofReal (delta n) := add_le_add le_rfl he
    _ ≤ integralSup mu f + (ε : ℝ≥0∞) := add_le_add hq hdeltaENN

/-- The explicit Jones grids are cofinal in the lower-integral definition. -/
theorem lowerIntegral_eq_integralSup (mu : VSub D)
    (f : BoundedScottFunction D) :
    jonesLowerIntegral mu f = integralSup mu f := by
  apply le_antisymm
  · apply JonesLowerIntegral.le_of_simple_bounds
    intro s hs
    exact simple_integral_le_integralSup mu f s hs
  · exact integralSup_le_lowerIntegral mu f

end
end JonesGrid
end ContinuousValuation
end FiniteValuationApproximable
