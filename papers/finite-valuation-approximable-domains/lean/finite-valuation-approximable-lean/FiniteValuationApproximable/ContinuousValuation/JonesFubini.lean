import FiniteValuationApproximable.ContinuousValuation.JonesFiniteFubini

/-!
# Fubini theorem and Kleisli associativity

The general kernel exchange is obtained from the finite-simple identity by
uniform Jones-grid approximation.  This is the substantive proof behind the
Kleisli associativity law.
-/

set_option autoImplicit false
set_option linter.unnecessarySimpa false

universe u v w

namespace FiniteValuationApproximable
namespace ContinuousValuation

open AbramskyJung.Chapter2
open scoped BigOperators ENNReal

namespace JonesLowerIntegral

variable {E : Type v} [Preorder E]

noncomputable section

/-- A uniform one-mesh upper estimate bounds the lower integral by the grid
integral plus that mesh. -/
theorem le_grid_integral_add_delta (nu : VSub E)
    (h : BoundedScottFunction E) (n M : Nat)
    (hupper : ∀ y : E, h y ≤ ENNReal.ofReal
      (JonesGrid.realValue h n M y + JonesGrid.delta n)) :
    jonesLowerIntegral nu h ≤
      (JonesGrid.simple h n M).integral nu +
        ENNReal.ofReal (JonesGrid.delta n) := by
  apply le_of_simple_bounds
  intro r hr
  let e : OpenSimpleFunction E := OpenSimpleFunction.single
    (JonesGrid.delta n) (JonesGrid.delta_nonneg n)
      (ScottOpen.univ : ScottOpen E)
  have hpoint : ∀ y,
      r.value y ≤
        (OpenSimpleFunction.add (JonesGrid.simple h n M) e).value y := by
    intro y
    have hENN : ENNReal.ofReal (r.value y) ≤
        ENNReal.ofReal
          (JonesGrid.realValue h n M y + JonesGrid.delta n) :=
      (hr y).trans (hupper y)
    have hreal : r.value y ≤
        JonesGrid.realValue h n M y + JonesGrid.delta n :=
      (ENNReal.ofReal_le_ofReal_iff
        (add_nonneg (JonesGrid.realValue_nonneg h n M y)
          (JonesGrid.delta_nonneg n))).mp hENN
    simpa [e, OpenSimpleFunction.add_value,
      JonesGrid.simple_value_eq_realValue] using hreal
  have hmono := OpenSimpleFunction.integral_mono nu hpoint
  calc
    r.integral nu ≤ (JonesGrid.simple h n M).integral nu + e.integral nu := by
      simpa only [OpenSimpleFunction.add_integral] using hmono
    _ ≤ (JonesGrid.simple h n M).integral nu +
        ENNReal.ofReal (JonesGrid.delta n) :=
      add_le_add le_rfl
        (JonesGrid.single_univ_integral_le nu _ (JonesGrid.delta_nonneg n))

end
end JonesLowerIntegral

/-- Fubini exchange for the Jones integral along a valuation kernel.  The
bounded function `G` packages the pointwise inner integrals. -/
theorem jonesLowerIntegral_kernel_fubini
    {D : Type u} {E : Type v} [Preorder D] [Preorder E]
    (mu : VSub D) (k : ScottContFun D (VSub E))
    (h : BoundedScottFunction E) (G : BoundedScottFunction D)
    (hG : ∀ x : D, G x = jonesLowerIntegral (k x) h) :
    jonesLowerIntegral (jonesKleisli k mu) h =
      jonesLowerIntegral mu G := by
  apply le_antisymm
  · apply JonesLowerIntegral.le_of_simple_bounds
    intro s hs
    rw [← lowerIntegral_simpleKernelIntegral mu k s]
    apply JonesLowerIntegral.mono
    intro x
    rw [simpleKernelIntegral_apply, hG x]
    exact JonesLowerIntegral.simple_le (k x) h s hs
  · apply ENNReal.le_of_forall_pos_le_add
    intro ε hε _hfinite
    have hεReal : 0 < (ε : ℝ) := by exact_mod_cast hε
    rcases exists_nat_one_div_lt hεReal with ⟨n, hn⟩
    have hdelta : JonesGrid.delta n < (ε : ℝ) := by
      simpa [JonesGrid.delta] using hn
    rcases JonesGrid.exists_uniform_upper h n with ⟨M, hM⟩
    let s : OpenSimpleFunction E := JonesGrid.simple h n M
    let H : BoundedScottFunction D := simpleKernelIntegral k s
    let e : BoundedScottFunction D := BoundedScottFunction.scale
      (JonesGrid.delta n) (JonesGrid.delta_nonneg n)
      (BoundedScottFunction.indicator (ScottOpen.univ : ScottOpen D))
    have hpoint : G ≤ BoundedScottFunction.add H e := by
      intro x
      rw [hG x]
      have hx := JonesLowerIntegral.le_grid_integral_add_delta
        (k x) h n M hM
      simpa [H, s, e, simpleKernelIntegral_apply,
        BoundedScottFunction.indicator_apply, openIndicator] using hx
    have hmono := JonesLowerIntegral.mono mu hpoint
    have hH : jonesLowerIntegral mu H =
        s.integral (jonesKleisli k mu) := by
      exact lowerIntegral_simpleKernelIntegral mu k s
    have he : jonesLowerIntegral mu e ≤
        ENNReal.ofReal (JonesGrid.delta n) := by
      rw [show e = BoundedScottFunction.scale
          (JonesGrid.delta n) (JonesGrid.delta_nonneg n)
          (BoundedScottFunction.indicator (ScottOpen.univ : ScottOpen D)) by rfl,
        JonesLowerIntegral.scale, JonesLowerIntegral.indicator]
      simpa using mul_le_mul_right
        (mu.value_le_one (ScottOpen.univ : ScottOpen D))
        (ENNReal.ofReal (JonesGrid.delta n))
    have hsLower : s.integral (jonesKleisli k mu) ≤
        jonesLowerIntegral (jonesKleisli k mu) h := by
      exact JonesGrid.grid_integral_le_lowerIntegral
        (jonesKleisli k mu) h n M
    have hdeltaENN : ENNReal.ofReal (JonesGrid.delta n) ≤ (ε : ℝ≥0∞) := by
      simpa using ENNReal.ofReal_le_ofReal hdelta.le
    calc
      jonesLowerIntegral mu G ≤
          jonesLowerIntegral mu H + jonesLowerIntegral mu e := by
        rw [← JonesLowerIntegral.add]
        exact hmono
      _ ≤ s.integral (jonesKleisli k mu) +
          ENNReal.ofReal (JonesGrid.delta n) := by
        rw [hH]
        exact add_le_add le_rfl he
      _ ≤ jonesLowerIntegral (jonesKleisli k mu) h + (ε : ℝ≥0∞) :=
        add_le_add hsLower hdeltaENN

/-- Kleisli composition kernel. -/
noncomputable def jonesKleisliCompose
    {D : Type u} {E : Type v} {F : Type w}
    [Preorder D] [Preorder E] [Preorder F]
    (k : ScottContFun D (VSub E)) (l : ScottContFun E (VSub F)) :
    ScottContFun D (VSub F) where
  toFun x := jonesKleisli l (k x)
  continuous := (jonesKleisli_scottContinuous_input l).comp k.continuous

/-- Kleisli associativity, proved by the kernel Fubini theorem. -/
theorem jonesKleisli_assoc
    {D : Type u} {E : Type v} {F : Type w}
    [Preorder D] [Preorder E] [Preorder F]
    (k : ScottContFun D (VSub E)) (l : ScottContFun E (VSub F))
    (mu : VSub D) :
    jonesKleisli l (jonesKleisli k mu) =
      jonesKleisli (jonesKleisliCompose k l) mu := by
  apply VSub.ext
  intro U
  rw [jonesKleisli_apply, jonesKleisli_apply]
  apply jonesLowerIntegral_kernel_fubini
  intro x
  rfl

end ContinuousValuation
end FiniteValuationApproximable
