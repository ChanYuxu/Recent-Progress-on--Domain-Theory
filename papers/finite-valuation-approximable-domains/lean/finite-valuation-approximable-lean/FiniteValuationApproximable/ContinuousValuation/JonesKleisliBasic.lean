import FiniteValuationApproximable.ContinuousValuation.JonesLinearity

/-!
# The Jones Kleisli extension: construction and elementary laws

Linearity and directed monotone convergence make the coordinatewise integral
of a valuation kernel into a continuous subprobability valuation.  This file
also proves the two unit laws, continuity in the input valuation, and the
pushforward identity.  Associativity is isolated in the subsequent Fubini
module.
-/

set_option autoImplicit false
set_option linter.unnecessarySimpa false

universe u v

namespace FiniteValuationApproximable
namespace ContinuousValuation

open AbramskyJung.Chapter2
open scoped BigOperators ENNReal

namespace OpenSimpleFunction

variable {D : Type u} [Preorder D]

/-- A finite open simple function integrates against a Dirac valuation to
its value at the support point. -/
theorem integral_dirac (s : OpenSimpleFunction D) (x : D) :
    s.integral (dirac x) = ENNReal.ofReal (s.value x) := by
  classical
  unfold integral integralReal valuationStepValue value openStepValue
  apply congrArg ENNReal.ofReal
  apply Finset.sum_congr rfl
  intro i _hi
  by_cases hxi : x ∈ s.opens i
  · simp [dirac_apply, openIndicator, hxi]
  · simp [dirac_apply, openIndicator, hxi]

end OpenSimpleFunction

namespace JonesLowerIntegral

variable {D : Type u} [Preorder D]

noncomputable section

theorem zero (mu : VSub D) :
    jonesLowerIntegral mu (BoundedScottFunction.zero : BoundedScottFunction D) = 0 := by
  apply le_antisymm
  · apply le_of_simple_bounds
    intro s hs
    calc
      s.integral mu ≤ OpenSimpleFunction.zero.integral mu := by
        apply OpenSimpleFunction.integral_mono
        intro x
        have hENN : ENNReal.ofReal (s.value x) = 0 := by
          apply le_antisymm
          · simpa using hs x
          · exact bot_le
        have hs0 : s.value x = 0 :=
          le_antisymm (ENNReal.ofReal_eq_zero.mp hENN) (s.value_nonneg x)
        simpa [hs0]
      _ = 0 := OpenSimpleFunction.zero_integral mu
  · exact bot_le

/-- The lower integral against a Dirac valuation is point evaluation. -/
theorem dirac (f : BoundedScottFunction D) (x : D) :
    jonesLowerIntegral (ContinuousValuation.dirac x) f = f x := by
  apply le_antisymm
  · apply le_of_simple_bounds
    intro s hs
    rw [OpenSimpleFunction.integral_dirac]
    exact hs x
  · apply ENNReal.le_of_forall_pos_le_add
    intro ε hε _hfinite
    have hεReal : 0 < (ε : ℝ) := by exact_mod_cast hε
    rcases exists_nat_one_div_lt hεReal with ⟨n, hn⟩
    have hdelta : JonesGrid.delta n < (ε : ℝ) := by
      simpa [JonesGrid.delta] using hn
    rcases JonesGrid.exists_uniform_upper f n with ⟨M, hM⟩
    have hgrid := JonesGrid.grid_integral_le_lowerIntegral
      (ContinuousValuation.dirac x) f n M
    rw [OpenSimpleFunction.integral_dirac,
      JonesGrid.simple_value_eq_realValue] at hgrid
    have hupper := hM x
    rw [ENNReal.ofReal_add (JonesGrid.realValue_nonneg f n M x)
      (JonesGrid.delta_nonneg n)] at hupper
    have hdeltaENN : ENNReal.ofReal (JonesGrid.delta n) ≤ (ε : ℝ≥0∞) := by
      simpa using ENNReal.ofReal_le_ofReal hdelta.le
    exact hupper.trans (add_le_add hgrid hdeltaENN)

end
end JonesLowerIntegral

theorem kernelSection_mono {D : Type u} {E : Type v}
    [Preorder D] [Preorder E]
    (k : ScottContFun D (VSub E)) {U V : ScottOpen E} (hUV : U ≤ V) :
    kernelSection k U ≤ kernelSection k V := by
  intro x
  exact (k x).monotone hUV

theorem kernelSection_empty_eq_zero {D : Type u} {E : Type v}
    [Preorder D] [Preorder E] (k : ScottContFun D (VSub E)) :
    kernelSection k (ScottOpen.empty : ScottOpen E) =
      (BoundedScottFunction.zero : BoundedScottFunction D) := by
  apply BoundedScottFunction.ext
  intro x
  exact (k x).1.strict

/-- Coordinatewise integration of a valuation kernel. -/
noncomputable def jonesKleisli {D : Type u} {E : Type v}
    [Preorder D] [Preorder E]
    (k : ScottContFun D (VSub E)) (mu : VSub D) : VSub E := by
  refine ⟨{
    toFun := fun U => jonesLowerIntegral mu (kernelSection k U)
    continuous := ?_
    strict := ?_
    modular := ?_ }, ?_⟩
  · constructor
    · intro U V hUV
      exact JonesLowerIntegral.mono mu (kernelSection_mono k hUV)
    · intro A S hA hS
      let B : Set (BoundedScottFunction D) :=
        (fun U : ScottOpen E => kernelSection k U) '' A
      have hB : DirectedSet B :=
        hA.image (fun _ _ hUV => kernelSection_mono k hUV)
      have hpoint : ∀ x : D,
          IsSup ((fun f : BoundedScottFunction D => f x) '' B)
            (kernelSection k S x) := by
        intro x
        have hx := (k x).1.continuous.maps_isSup hA hS
        simpa [B, Set.image_image, Function.comp_def] using hx
      have hDMC := JonesLowerIntegral.directed_mono_convergence_integrand
        hB (kernelSection k S) hpoint mu
      simpa [B, Set.image_image, Function.comp_def] using hDMC
  · rw [kernelSection_empty_eq_zero, JonesLowerIntegral.zero]
  · intro U V
    have hmod :
        BoundedScottFunction.add (kernelSection k U) (kernelSection k V) =
          BoundedScottFunction.add
            (kernelSection k (ScottOpen.union U V))
            (kernelSection k (ScottOpen.inter U V)) := by
      apply BoundedScottFunction.ext
      intro x
      exact (k x).1.modular U V
    calc
      jonesLowerIntegral mu (kernelSection k U) +
          jonesLowerIntegral mu (kernelSection k V) =
          jonesLowerIntegral mu
            (BoundedScottFunction.add (kernelSection k U) (kernelSection k V)) :=
        (JonesLowerIntegral.add mu _ _).symm
      _ = jonesLowerIntegral mu
          (BoundedScottFunction.add
            (kernelSection k (ScottOpen.union U V))
            (kernelSection k (ScottOpen.inter U V))) := by rw [hmod]
      _ = jonesLowerIntegral mu (kernelSection k (ScottOpen.union U V)) +
          jonesLowerIntegral mu (kernelSection k (ScottOpen.inter U V)) :=
        JonesLowerIntegral.add mu _ _
  · have hsection : kernelSection k (ScottOpen.univ : ScottOpen E) ≤
        BoundedScottFunction.indicator (ScottOpen.univ : ScottOpen D) := by
      intro x
      simpa [BoundedScottFunction.indicator_apply, openIndicator] using
        (k x).value_le_one (ScottOpen.univ : ScottOpen E)
    exact (JonesLowerIntegral.mono mu hsection).trans (by
      rw [JonesLowerIntegral.indicator]
      exact mu.2)

@[simp] theorem jonesKleisli_apply {D : Type u} {E : Type v}
    [Preorder D] [Preorder E]
    (k : ScottContFun D (VSub E)) (mu : VSub D) (U : ScottOpen E) :
    jonesKleisli k mu U = jonesLowerIntegral mu (kernelSection k U) := rfl

/-- The Kleisli extension is Scott-continuous in its input valuation. -/
theorem jonesKleisli_scottContinuous_input {D : Type u} {E : Type v}
    [Preorder D] [Preorder E] (k : ScottContFun D (VSub E)) :
    AbramskyJung.Chapter2.ScottContinuous (jonesKleisli k) := by
  constructor
  · intro mu nu hmu U
    exact JonesLowerIntegral.mono_valuation hmu (kernelSection k U)
  · intro A sigma hA hsigma
    have hKA : DirectedSet (jonesKleisli k '' A) :=
      hA.image (by
        intro mu nu hmu U
        exact JonesLowerIntegral.mono_valuation hmu (kernelSection k U))
    apply VSub.isSup_of_pointwise hKA
    intro U
    have hDMC := JonesLowerIntegral.directed_mono_convergence_valuation
      hA sigma hsigma (kernelSection k U)
    have himage :
        (fun rho : VSub E => rho U) '' (jonesKleisli k '' A) =
          (fun mu : VSub D => jonesLowerIntegral mu (kernelSection k U)) '' A := by
      ext z
      constructor
      · rintro ⟨rho, ⟨mu, hmuA, rfl⟩, rfl⟩
        exact ⟨mu, hmuA, rfl⟩
      · rintro ⟨mu, hmuA, rfl⟩
        exact ⟨jonesKleisli k mu, ⟨mu, hmuA, rfl⟩, rfl⟩
    rw [himage]
    exact hDMC

/-- First Kleisli unit law. -/
theorem jonesKleisli_dirac {D : Type u} {E : Type v}
    [Preorder D] [Preorder E]
    (k : ScottContFun D (VSub E)) (x : D) :
    jonesKleisli k (ContinuousValuation.dirac x) = k x := by
  apply VSub.ext
  intro U
  rw [jonesKleisli_apply, JonesLowerIntegral.dirac]
  rfl

/-- Second Kleisli unit law. -/
theorem jonesKleisli_unit {D : Type u} [Preorder D] (mu : VSub D) :
    jonesKleisli (unit (D := D)) mu = mu := by
  apply VSub.ext
  intro U
  rw [jonesKleisli_apply]
  have hsection : kernelSection (unit (D := D)) U =
      BoundedScottFunction.indicator U := by
    apply BoundedScottFunction.ext
    intro x
    rfl
  rw [hsection, JonesLowerIntegral.indicator]

/-- Kleisli extension of `unit ∘ f` is pushforward along `f`. -/
theorem jonesKleisli_unit_comp_eq_pushforward
    {D : Type u} {E : Type v} [Preorder D] [Preorder E]
    (f : ScottContFun D E) (mu : VSub D) :
    jonesKleisli (ScottContFun.comp (unit (D := E)) f) mu =
      pushforward f mu := by
  apply VSub.ext
  intro U
  rw [jonesKleisli_apply, pushforward_apply]
  have hsection :
      kernelSection (ScottContFun.comp (unit (D := E)) f) U =
        BoundedScottFunction.indicator
          (ScottOpen.preimage f f.continuous U) := by
    apply BoundedScottFunction.ext
    intro x
    rfl
  rw [hsection, JonesLowerIntegral.indicator]

end ContinuousValuation
end FiniteValuationApproximable
