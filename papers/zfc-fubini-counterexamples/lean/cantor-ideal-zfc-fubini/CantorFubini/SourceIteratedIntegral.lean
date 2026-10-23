import CantorFubini.SourceIntegralBridge

/-! Exact two-level bridge for the source's ordinary-real integral.
This is an identity for the supplied iterated integrals, without any
commutation hypothesis. -/

set_option autoImplicit false
open Set Topology TopologicalSpace MeasureTheory
open scoped ENNReal
universe u v
namespace CantorFubini

/-- Both ordinary-real integrations are exactly the finite ENNReal
integrations followed by `toReal`. No interchange is asserted here. -/
theorem sourceIntegral_iterated_eq_vIntegral
    {X : Type u} [TopologicalSpace X] {Y : Type v} [TopologicalSpace Y]
    (μ : SubprobValuation X) (ρ : SubprobValuation Y) (f : X → Y → ℝ)
    (hf1 : ∀ x y, f x y ≤ 1) :
    sourceIntegral ρ.val (fun y => sourceIntegral μ.val (fun x => f x y)) =
      (vIntegral ρ.val (fun y => vIntegral μ.val
        (fun x => ENNReal.ofReal (f x y)))).toReal := by
  have hinner (y : Y) : sourceIntegral μ.val (fun x => f x y) =
      (vIntegral μ.val (fun x => ENNReal.ofReal (f x y))).toReal :=
    sourceIntegral_eq_vIntegral_toReal μ _ (fun x => hf1 x y)
  simp_rw [hinner]
  apply sourceIntegral_toReal ρ
  intro y
  apply vIntegral_le_one μ
  intro x
  simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal (hf1 x y)

end CantorFubini
