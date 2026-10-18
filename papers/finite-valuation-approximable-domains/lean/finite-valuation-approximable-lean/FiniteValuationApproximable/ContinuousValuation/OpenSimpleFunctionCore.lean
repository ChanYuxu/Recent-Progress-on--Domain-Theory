import FiniteValuationApproximable.ContinuousValuation.OpenSimple

/-! Core algebra for nonnegative finite Scott-open simple functions. -/

set_option autoImplicit false
set_option linter.unnecessarySimpa false

universe u

namespace FiniteValuationApproximable
namespace ContinuousValuation

open scoped BigOperators ENNReal

/-- A finite nonnegative linear combination of Scott-open indicators. -/
structure OpenSimpleFunction (D : Type u) [Preorder D] where
  arity : Nat
  coeff : Fin arity → ℝ
  opens : Fin arity → ScottOpen D
  coeff_nonneg : ∀ i, 0 ≤ coeff i

namespace OpenSimpleFunction

variable {D : Type u} [Preorder D]

noncomputable def value (s : OpenSimpleFunction D) (x : D) : ℝ :=
  openStepValue s.coeff s.opens x

noncomputable def integralReal (mu : VSub D) (s : OpenSimpleFunction D) : ℝ :=
  valuationStepValue mu s.coeff s.opens

noncomputable def integral (mu : VSub D) (s : OpenSimpleFunction D) : ℝ≥0∞ :=
  ENNReal.ofReal (integralReal mu s)

theorem value_nonneg (s : OpenSimpleFunction D) (x : D) :
    0 ≤ s.value x := by
  classical
  unfold value openStepValue
  exact Finset.sum_nonneg fun i _ => by
    by_cases hxi : x ∈ s.opens i
    · simp [hxi, s.coeff_nonneg i]
    · simp [hxi]

theorem integralReal_nonneg (mu : VSub D) (s : OpenSimpleFunction D) :
    0 ≤ s.integralReal mu := by
  classical
  unfold integralReal valuationStepValue
  exact Finset.sum_nonneg fun i _ =>
    mul_nonneg (s.coeff_nonneg i) ENNReal.toReal_nonneg

/-- ENNReal-valued finite-sum formula for the integral.  Finiteness of every
valuation coordinate follows from the subprobability bound. -/
theorem integral_eq_sum (mu : VSub D) (s : OpenSimpleFunction D) :
    s.integral mu =
      ∑ i : Fin s.arity, ENNReal.ofReal (s.coeff i) * mu (s.opens i) := by
  classical
  unfold integral integralReal valuationStepValue
  rw [ENNReal.ofReal_sum_of_nonneg]
  · apply Finset.sum_congr rfl
    intro i _hi
    rw [ENNReal.ofReal_mul (s.coeff_nonneg i)]
    rw [ENNReal.ofReal_toReal
      (ne_top_of_le_ne_top ENNReal.one_ne_top (mu.value_le_one (s.opens i)))]
  · intro i _hi
    exact mul_nonneg (s.coeff_nonneg i) ENNReal.toReal_nonneg

/-- Monotonicity of a simple-function integral in the valuation argument. -/
theorem integral_mono_valuation {mu nu : VSub D} (hmu : mu ≤ nu)
    (s : OpenSimpleFunction D) :
    s.integral mu ≤ s.integral nu := by
  classical
  rw [integral_eq_sum, integral_eq_sum]
  apply Finset.sum_le_sum
  intro i _hi
  exact mul_le_mul_right (hmu (s.opens i)) (ENNReal.ofReal (s.coeff i))

def zero : OpenSimpleFunction D where
  arity := 0
  coeff := Fin.elim0
  opens := Fin.elim0
  coeff_nonneg := fun i => Fin.elim0 i

@[simp] theorem zero_value (x : D) : (zero : OpenSimpleFunction D).value x = 0 := by
  simp [value, zero, openStepValue]

@[simp] theorem zero_integralReal (mu : VSub D) :
    (zero : OpenSimpleFunction D).integralReal mu = 0 := by
  simp [integralReal, zero, valuationStepValue]

@[simp] theorem zero_integral (mu : VSub D) :
    (zero : OpenSimpleFunction D).integral mu = 0 := by
  simp [integral]

def single (c : ℝ) (hc : 0 ≤ c) (U : ScottOpen D) :
    OpenSimpleFunction D where
  arity := 1
  coeff := fun _ => c
  opens := fun _ => U
  coeff_nonneg := fun _ => hc

@[simp] theorem single_value_of_mem (c : ℝ) (hc : 0 ≤ c)
    (U : ScottOpen D) (x : D) (hx : x ∈ U) :
    (single c hc U).value x = c := by
  classical
  simp [value, single, openStepValue, hx]

@[simp] theorem single_value_of_not_mem (c : ℝ) (hc : 0 ≤ c)
    (U : ScottOpen D) (x : D) (hx : x ∉ U) :
    (single c hc U).value x = 0 := by
  classical
  simp [value, single, openStepValue, hx]

@[simp] theorem single_integralReal (mu : VSub D)
    (c : ℝ) (hc : 0 ≤ c) (U : ScottOpen D) :
    (single c hc U).integralReal mu = c * (mu U).toReal := by
  simp [integralReal, single, valuationStepValue]

def add (s t : OpenSimpleFunction D) : OpenSimpleFunction D where
  arity := s.arity + t.arity
  coeff := Fin.addCases s.coeff t.coeff
  opens := Fin.addCases s.opens t.opens
  coeff_nonneg := Fin.addCases
    (fun i => by simpa using s.coeff_nonneg i)
    (fun i => by simpa using t.coeff_nonneg i)

@[simp] theorem add_value (s t : OpenSimpleFunction D) (x : D) :
    (add s t).value x = s.value x + t.value x := by
  classical
  unfold value openStepValue
  change (∑ i : Fin (s.arity + t.arity),
      if x ∈ (add s t).opens i then (add s t).coeff i else 0) = _
  rw [Fin.sum_univ_add]
  simp [add]

@[simp] theorem add_integralReal (mu : VSub D) (s t : OpenSimpleFunction D) :
    (add s t).integralReal mu = s.integralReal mu + t.integralReal mu := by
  classical
  unfold integralReal valuationStepValue
  change (∑ i : Fin (s.arity + t.arity),
      (add s t).coeff i * (mu ((add s t).opens i)).toReal) = _
  rw [Fin.sum_univ_add]
  simp [add]

@[simp] theorem add_integral (mu : VSub D) (s t : OpenSimpleFunction D) :
    (add s t).integral mu = s.integral mu + t.integral mu := by
  rw [integral, add_integralReal, ENNReal.ofReal_add
    (integralReal_nonneg mu s) (integralReal_nonneg mu t)]
  rfl

def scale (c : ℝ) (hc : 0 ≤ c) (s : OpenSimpleFunction D) :
    OpenSimpleFunction D where
  arity := s.arity
  coeff := fun i => c * s.coeff i
  opens := s.opens
  coeff_nonneg := fun i => mul_nonneg hc (s.coeff_nonneg i)

@[simp] theorem scale_value (c : ℝ) (hc : 0 ≤ c)
    (s : OpenSimpleFunction D) (x : D) :
    (scale c hc s).value x = c * s.value x := by
  classical
  unfold value scale openStepValue
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hxi : x ∈ s.opens i <;> simp [hxi]

@[simp] theorem scale_integralReal (mu : VSub D)
    (c : ℝ) (hc : 0 ≤ c) (s : OpenSimpleFunction D) :
    (scale c hc s).integralReal mu = c * s.integralReal mu := by
  classical
  unfold integralReal scale valuationStepValue
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

end OpenSimpleFunction
end ContinuousValuation
end FiniteValuationApproximable
