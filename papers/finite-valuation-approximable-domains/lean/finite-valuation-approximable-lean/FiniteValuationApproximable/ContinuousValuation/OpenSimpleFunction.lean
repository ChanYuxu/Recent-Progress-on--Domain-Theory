import FiniteValuationApproximable.ContinuousValuation.OpenSimpleFunctionCore

/-!
# Comparison for finite Scott-open simple functions

The finite Boolean dissection proves that their valuation value is independent
of presentation.  This is the internal replacement for Jones's extension of a
valuation to the finite crescent field in Lemmas 3.9--3.10.
-/

set_option autoImplicit false
set_option linter.unnecessarySimpa false

universe u

namespace FiniteValuationApproximable
namespace ContinuousValuation
namespace OpenSimpleFunction

open scoped BigOperators ENNReal

variable {D : Type u} [Preorder D]

theorem integralReal_mono {s t : OpenSimpleFunction D}
    (mu : VSub D) (hst : ∀ x, s.value x ≤ t.value x) :
    s.integralReal mu ≤ t.integralReal mu := by
  classical
  let O : Fin (s.arity + t.arity) → ScottOpen D :=
    Fin.addCases s.opens t.opens
  let a : Fin (s.arity + t.arity) → ℝ :=
    Fin.addCases s.coeff (fun _ => 0)
  let b : Fin (s.arity + t.arity) → ℝ :=
    Fin.addCases (fun _ => 0) t.coeff
  have hab : ∀ x : D, openStepValue a O x ≤ openStepValue b O x := by
    intro x
    simpa [a, b, O, value, openStepValue, Fin.sum_univ_add] using hst x
  have h := valuationStepValue_mono_same mu O a b hab
  simpa [a, b, O, integralReal, valuationStepValue, Fin.sum_univ_add] using h

theorem integral_mono {s t : OpenSimpleFunction D}
    (mu : VSub D) (hst : ∀ x, s.value x ≤ t.value x) :
    s.integral mu ≤ t.integral mu := by
  exact ENNReal.ofReal_le_ofReal (integralReal_mono mu hst)

def indicator (U : ScottOpen D) : OpenSimpleFunction D :=
  single 1 zero_le_one U

@[simp] theorem indicator_value_of_mem (U : ScottOpen D) (x : D)
    (hx : x ∈ U) : (indicator U).value x = 1 := by
  simp [indicator, hx]

@[simp] theorem indicator_value_of_not_mem (U : ScottOpen D) (x : D)
    (hx : x ∉ U) : (indicator U).value x = 0 := by
  simp [indicator, hx]

@[simp] theorem indicator_integralReal (mu : VSub D) (U : ScottOpen D) :
    (indicator U).integralReal mu = (mu U).toReal := by
  simp [indicator]

@[simp] theorem indicator_integral (mu : VSub D) (U : ScottOpen D) :
    (indicator U).integral mu = mu U := by
  unfold integral
  rw [indicator_integralReal]
  exact ENNReal.ofReal_toReal
    (ne_top_of_le_ne_top ENNReal.one_ne_top (mu.value_le_one U))

end OpenSimpleFunction
end ContinuousValuation
end FiniteValuationApproximable
