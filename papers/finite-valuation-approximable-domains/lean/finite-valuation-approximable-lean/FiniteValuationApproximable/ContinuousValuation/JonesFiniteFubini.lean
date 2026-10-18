import FiniteValuationApproximable.ContinuousValuation.JonesScale

/-!
# Finite-simple Fubini theorem for valuation kernels

For a finite Scott-open simple function `s` on the target, the function
`x ↦ ∫ s d(k x)` is again bounded and Scott-continuous.  Finite additivity
and positive homogeneity then allow its outer integral to be exchanged with
the kernel.
-/

set_option autoImplicit false
set_option linter.unnecessarySimpa false

universe u v

namespace FiniteValuationApproximable
namespace ContinuousValuation

open AbramskyJung.Chapter2
open scoped BigOperators ENNReal

variable {D : Type u} {E : Type v} [Preorder D] [Preorder E]

/-- A partial finite sum of the kernel coordinates occurring in a simple
function. -/
noncomputable def simpleKernelIntegralOn
    (k : ScottContFun D (VSub E)) (s : OpenSimpleFunction E)
    (S : Finset (Fin s.arity)) : BoundedScottFunction D where
  toFun := fun x =>
    ∑ i ∈ S, ENNReal.ofReal (s.coeff i) * k x (s.opens i)
  continuous := by
    constructor
    · intro x y hxy
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_right
        ((k.continuous.monotone hxy) (s.opens i))
        (ENNReal.ofReal (s.coeff i))
    · intro A z hA hz
      constructor
      · rintro _ ⟨x, hxA, rfl⟩
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_right
          ((k.continuous.monotone (hz.1 hxA)) (s.opens i))
          (ENNReal.ofReal (s.coeff i))
      · intro y hy
        have hcoord (i : Fin s.arity) :
            ENNReal.ofReal (s.coeff i) * k z (s.opens i) =
              ⨆ x : A, ENNReal.ofReal (s.coeff i) * k x.1 (s.opens i) := by
          have heval : IsSup
              ((fun x : D => k x (s.opens i)) '' A)
              (k z (s.opens i)) :=
            ((VSub.eval_scottContinuous (s.opens i)).comp k.continuous).maps_isSup
              hA hz
          have heq := isSup_image_eq_iSup_subtype
            (fun x : D => k x (s.opens i)) (k z (s.opens i)) heval
          rw [heq, ENNReal.mul_iSup]
        change (∑ i ∈ S,
          ENNReal.ofReal (s.coeff i) * k z (s.opens i)) ≤ y
        calc
          (∑ i ∈ S, ENNReal.ofReal (s.coeff i) * k z (s.opens i)) =
              ∑ i ∈ S, ⨆ x : A,
                ENNReal.ofReal (s.coeff i) * k x.1 (s.opens i) := by
            apply Finset.sum_congr rfl
            intro i _hi
            rw [hcoord i]
          _ = ⨆ x : A, ∑ i ∈ S,
                ENNReal.ofReal (s.coeff i) * k x.1 (s.opens i) := by
            exact finset_sum_iSup_of_directed S
              (fun i (x : A) =>
                ENNReal.ofReal (s.coeff i) * k x.1 (s.opens i)) (by
                  intro x y
                  rcases hA.2 x.2 y.2 with ⟨z, hzA, hxz, hyz⟩
                  refine ⟨⟨z, hzA⟩, fun i => ⟨?_, ?_⟩⟩
                  · exact mul_le_mul_right
                      ((k.continuous.monotone hxz) (s.opens i))
                      (ENNReal.ofReal (s.coeff i))
                  · exact mul_le_mul_right
                      ((k.continuous.monotone hyz) (s.opens i))
                      (ENNReal.ofReal (s.coeff i)))
          _ ≤ y := iSup_le fun x => hy ⟨x.1, x.2, rfl⟩
  bounded := by
    refine ⟨∑ i ∈ S, ENNReal.ofReal (s.coeff i), ?_, ?_⟩
    · exact ENNReal.sum_ne_top.2 fun i hi => ENNReal.ofReal_ne_top
    · intro x
      apply Finset.sum_le_sum
      intro i hi
      simpa using mul_le_mul_right
        ((k x).value_le_one (s.opens i)) (ENNReal.ofReal (s.coeff i))

@[simp] theorem simpleKernelIntegralOn_apply
    (k : ScottContFun D (VSub E)) (s : OpenSimpleFunction E)
    (S : Finset (Fin s.arity)) (x : D) :
    simpleKernelIntegralOn k s S x =
      ∑ i ∈ S, ENNReal.ofReal (s.coeff i) * k x (s.opens i) := rfl

theorem simpleKernelIntegralOn_empty
    (k : ScottContFun D (VSub E)) (s : OpenSimpleFunction E) :
    simpleKernelIntegralOn k s ∅ =
      (BoundedScottFunction.zero : BoundedScottFunction D) := by
  apply BoundedScottFunction.ext
  intro x
  simp

theorem simpleKernelIntegralOn_insert
    (k : ScottContFun D (VSub E)) (s : OpenSimpleFunction E)
    (S : Finset (Fin s.arity)) (i : Fin s.arity) (hi : i ∉ S) :
    simpleKernelIntegralOn k s (insert i S) =
      BoundedScottFunction.add
        (BoundedScottFunction.scale (s.coeff i) (s.coeff_nonneg i)
          (kernelSection k (s.opens i)))
        (simpleKernelIntegralOn k s S) := by
  apply BoundedScottFunction.ext
  intro x
  simp [simpleKernelIntegralOn, hi]

theorem lowerIntegral_simpleKernelIntegralOn
    (mu : VSub D) (k : ScottContFun D (VSub E))
    (s : OpenSimpleFunction E) (S : Finset (Fin s.arity)) :
    jonesLowerIntegral mu (simpleKernelIntegralOn k s S) =
      ∑ i ∈ S, ENNReal.ofReal (s.coeff i) *
        jonesLowerIntegral mu (kernelSection k (s.opens i)) := by
  classical
  induction S using Finset.induction with
  | empty =>
      rw [simpleKernelIntegralOn_empty, JonesLowerIntegral.zero]
      simp
  | @insert i S hi ih =>
      rw [simpleKernelIntegralOn_insert k s S i hi,
        JonesLowerIntegral.add,
        JonesLowerIntegral.scale,
        ih, Finset.sum_insert hi]

/-- The full finite kernel integral associated with a simple function. -/
noncomputable def simpleKernelIntegral
    (k : ScottContFun D (VSub E)) (s : OpenSimpleFunction E) :
    BoundedScottFunction D :=
  simpleKernelIntegralOn k s Finset.univ

@[simp] theorem simpleKernelIntegral_apply
    (k : ScottContFun D (VSub E)) (s : OpenSimpleFunction E) (x : D) :
    simpleKernelIntegral k s x = s.integral (k x) := by
  rw [OpenSimpleFunction.integral_eq_sum]
  rfl

/-- Finite-simple Fubini identity. -/
theorem lowerIntegral_simpleKernelIntegral
    (mu : VSub D) (k : ScottContFun D (VSub E))
    (s : OpenSimpleFunction E) :
    jonesLowerIntegral mu (simpleKernelIntegral k s) =
      s.integral (jonesKleisli k mu) := by
  rw [show simpleKernelIntegral k s =
      simpleKernelIntegralOn k s Finset.univ by rfl,
    lowerIntegral_simpleKernelIntegralOn,
    OpenSimpleFunction.integral_eq_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  rfl

end ContinuousValuation
end FiniteValuationApproximable
