import FiniteValuationApproximable.ContinuousValuation.OpenSimpleFunction

/-!
# The Jones lower integral: definition and elementary laws

The integral of a bounded Scott-continuous `ℝ≥0∞`-valued function is the
supremum of the valuation integrals of all finite nonnegative Scott-open step
functions below it.  This is Jones's definition on p. 52, with the finite
crescent extension replaced by the verified Boolean-signature construction.
-/

set_option autoImplicit false
set_option linter.unnecessarySimpa false

universe u

namespace FiniteValuationApproximable
namespace ContinuousValuation

open scoped ENNReal

/-- A finite Scott-open simple function lying below a bounded
Scott-continuous integrand. -/
def LowerOpenSimple {D : Type u} [Preorder D]
    (f : BoundedScottFunction D) :=
  {s : OpenSimpleFunction D //
    ∀ x, ENNReal.ofReal (s.value x) ≤ f x}

/-- Jones's lower integral, defined without an external constant. -/
noncomputable def jonesLowerIntegral {D : Type u} [Preorder D]
    (mu : VSub D) (f : BoundedScottFunction D) : ℝ≥0∞ :=
  ⨆ s : LowerOpenSimple f, s.1.integral mu

namespace JonesLowerIntegral

variable {D : Type u} [Preorder D]

theorem simple_le (mu : VSub D) (f : BoundedScottFunction D)
    (s : OpenSimpleFunction D)
    (hs : ∀ x, ENNReal.ofReal (s.value x) ≤ f x) :
    s.integral mu ≤ jonesLowerIntegral mu f := by
  exact le_iSup (fun t : LowerOpenSimple f => t.1.integral mu) ⟨s, hs⟩

theorem le_of_simple_bounds (mu : VSub D) (f : BoundedScottFunction D)
    (a : ℝ≥0∞)
    (ha : ∀ s : OpenSimpleFunction D,
      (∀ x, ENNReal.ofReal (s.value x) ≤ f x) → s.integral mu ≤ a) :
    jonesLowerIntegral mu f ≤ a := by
  unfold jonesLowerIntegral
  exact iSup_le fun s => ha s.1 s.2

theorem mono (mu : VSub D) {f g : BoundedScottFunction D}
    (hfg : f ≤ g) :
    jonesLowerIntegral mu f ≤ jonesLowerIntegral mu g := by
  unfold jonesLowerIntegral
  refine iSup_le fun s => ?_
  let t : LowerOpenSimple g :=
    ⟨s.1, fun x => (s.2 x).trans (hfg x)⟩
  exact le_iSup (fun r : LowerOpenSimple g => r.1.integral mu) t

theorem mono_valuation {mu nu : VSub D} (hmu : mu ≤ nu)
    (f : BoundedScottFunction D) :
    jonesLowerIntegral mu f ≤ jonesLowerIntegral nu f := by
  unfold jonesLowerIntegral
  refine iSup_le fun s => ?_
  exact (OpenSimpleFunction.integral_mono_valuation hmu s.1).trans
    (le_iSup (fun t : LowerOpenSimple f => t.1.integral nu) s)

private theorem indicator_simple_value
    (U : ScottOpen D) (x : D) :
    ENNReal.ofReal ((OpenSimpleFunction.indicator U).value x) =
      BoundedScottFunction.indicator U x := by
  classical
  by_cases hx : x ∈ U
  · simp [OpenSimpleFunction.indicator_value_of_mem U x hx,
      BoundedScottFunction.indicator_apply, openIndicator_of_mem hx]
  · simp [OpenSimpleFunction.indicator_value_of_not_mem U x hx,
      BoundedScottFunction.indicator_apply, openIndicator_of_not_mem hx]

/-- The lower integral of a Scott-open indicator is the valuation of that
open. -/
theorem indicator (mu : VSub D) (U : ScottOpen D) :
    jonesLowerIntegral mu (BoundedScottFunction.indicator U) = mu U := by
  apply le_antisymm
  · apply le_of_simple_bounds
    intro s hs
    calc
      s.integral mu ≤ (OpenSimpleFunction.indicator U).integral mu := by
        apply OpenSimpleFunction.integral_mono mu
        intro x
        apply (ENNReal.ofReal_le_ofReal_iff
          ((OpenSimpleFunction.indicator U).value_nonneg x)).mp
        rw [indicator_simple_value U x]
        exact hs x
      _ = mu U := OpenSimpleFunction.indicator_integral mu U
  · have hbelow : ∀ x,
        ENNReal.ofReal ((OpenSimpleFunction.indicator U).value x) ≤
          BoundedScottFunction.indicator U x := by
      intro x
      exact (indicator_simple_value U x).le
    simpa only [OpenSimpleFunction.indicator_integral] using
      simple_le mu (BoundedScottFunction.indicator U)
        (OpenSimpleFunction.indicator U) hbelow

end JonesLowerIntegral
end ContinuousValuation
end FiniteValuationApproximable
