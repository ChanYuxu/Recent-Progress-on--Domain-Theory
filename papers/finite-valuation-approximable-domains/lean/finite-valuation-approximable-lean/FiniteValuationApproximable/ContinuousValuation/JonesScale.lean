import FiniteValuationApproximable.ContinuousValuation.JonesKleisliBasic

/-! # Positive homogeneity of the Jones lower integral -/

set_option autoImplicit false
set_option linter.unnecessarySimpa false

universe u

namespace FiniteValuationApproximable
namespace ContinuousValuation

open AbramskyJung.Chapter2
open scoped BigOperators ENNReal

namespace OpenSimpleFunction

variable {D : Type u} [Preorder D]

@[simp] theorem scale_integral (mu : VSub D) (c : ℝ) (hc : 0 ≤ c)
    (s : OpenSimpleFunction D) :
    (scale c hc s).integral mu = ENNReal.ofReal c * s.integral mu := by
  unfold integral
  rw [scale_integralReal, ENNReal.ofReal_mul hc]

end OpenSimpleFunction

namespace BoundedScottFunction

variable {D : Type u} [Preorder D]

/-- Multiplication by a finite nonnegative real scalar. -/
noncomputable def scale (c : ℝ) (hc : 0 ≤ c) (f : BoundedScottFunction D) :
    BoundedScottFunction D where
  toFun := fun x => ENNReal.ofReal c * f x
  continuous := by
    constructor
    · intro x y hxy
      exact mul_le_mul_right (f.continuous.monotone hxy) (ENNReal.ofReal c)
    · intro A s hA hs
      have hf : IsSup (f '' A) (f s) := f.continuous.maps_isSup hA hs
      constructor
      · rintro _ ⟨x, hxA, rfl⟩
        exact mul_le_mul_right (hf.1 ⟨x, hxA, rfl⟩) (ENNReal.ofReal c)
      · intro y hy
        have hfEq : f s = ⨆ x : A, f x.1 :=
          isSup_image_eq_iSup_subtype f (f s) hf
        change ENNReal.ofReal c * f s ≤ y
        rw [hfEq, ENNReal.mul_iSup]
        exact iSup_le fun x => hy ⟨x.1, x.2, rfl⟩
  bounded := by
    rcases f.bounded with ⟨b, hb, hfb⟩
    exact ⟨ENNReal.ofReal c * b,
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hb,
      fun x => mul_le_mul_right (hfb x) (ENNReal.ofReal c)⟩

@[simp] theorem scale_apply (c : ℝ) (hc : 0 ≤ c)
    (f : BoundedScottFunction D) (x : D) :
    scale c hc f x = ENNReal.ofReal c * f x := rfl

end BoundedScottFunction

namespace JonesLowerIntegral

variable {D : Type u} [Preorder D]

noncomputable section

/-- Positive homogeneity of the Jones lower integral. -/
theorem scale (mu : VSub D) (c : ℝ) (hc : 0 ≤ c)
    (f : BoundedScottFunction D) :
    jonesLowerIntegral mu (BoundedScottFunction.scale c hc f) =
      ENNReal.ofReal c * jonesLowerIntegral mu f := by
  have hLower : ENNReal.ofReal c * jonesLowerIntegral mu f ≤
      jonesLowerIntegral mu (BoundedScottFunction.scale c hc f) := by
    unfold jonesLowerIntegral
    rw [ENNReal.mul_iSup]
    refine iSup_le fun s => ?_
    let t : LowerOpenSimple (BoundedScottFunction.scale c hc f) :=
      ⟨OpenSimpleFunction.scale c hc s.1, fun x => by
        rw [OpenSimpleFunction.scale_value, ENNReal.ofReal_mul hc]
        exact mul_le_mul_right (s.2 x) (ENNReal.ofReal c)⟩
    rw [← OpenSimpleFunction.scale_integral mu c hc s.1]
    exact le_iSup (fun r : LowerOpenSimple
      (BoundedScottFunction.scale c hc f) => r.1.integral mu) t
  by_cases hc0 : c = 0
  · subst c
    have hfun : BoundedScottFunction.scale 0 (by norm_num) f =
        (BoundedScottFunction.zero : BoundedScottFunction D) := by
      apply BoundedScottFunction.ext
      intro x
      simp
    rw [hfun, zero]
    simp
  · have hcpos : 0 < c := lt_of_le_of_ne hc (Ne.symm hc0)
    apply le_antisymm
    · apply le_of_simple_bounds
      intro t ht
      let q : OpenSimpleFunction D :=
        OpenSimpleFunction.scale c⁻¹ (inv_nonneg.mpr hc) t
      have hcENN0 : ENNReal.ofReal c ≠ 0 :=
        (ENNReal.ofReal_ne_zero_iff.mpr hcpos)
      have hq : ∀ x, ENNReal.ofReal (q.value x) ≤ f x := by
        intro x
        rw [OpenSimpleFunction.scale_value,
          ENNReal.ofReal_mul (inv_nonneg.mpr hc),
          ENNReal.ofReal_inv_of_pos hcpos]
        calc
          (ENNReal.ofReal c)⁻¹ * ENNReal.ofReal (t.value x) ≤
              (ENNReal.ofReal c)⁻¹ *
                (ENNReal.ofReal c * f x) :=
            mul_le_mul_right (ht x) (ENNReal.ofReal c)⁻¹
          _ = f x := ENNReal.inv_mul_cancel_left hcENN0 ENNReal.ofReal_ne_top
      have hqIntegral := simple_le mu f q hq
      have hqFormula : q.integral mu =
          (ENNReal.ofReal c)⁻¹ * t.integral mu := by
        rw [show q = OpenSimpleFunction.scale c⁻¹ (inv_nonneg.mpr hc) t by rfl,
          OpenSimpleFunction.scale_integral,
          ENNReal.ofReal_inv_of_pos hcpos]
      have htRecover : t.integral mu = ENNReal.ofReal c * q.integral mu := by
        calc
          t.integral mu = ENNReal.ofReal c *
              ((ENNReal.ofReal c)⁻¹ * t.integral mu) :=
            (ENNReal.mul_inv_cancel_left hcENN0 ENNReal.ofReal_ne_top).symm
          _ = ENNReal.ofReal c * q.integral mu := by rw [hqFormula]
      rw [htRecover]
      exact mul_le_mul_right hqIntegral (ENNReal.ofReal c)
    · exact hLower

end
end JonesLowerIntegral
end ContinuousValuation
end FiniteValuationApproximable
