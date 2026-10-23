import ZFCFubini.ValuationMonad
import ZFCFubini.ValuationBindIntegral

/-!
# Integration-defined multiplication and the categorical monad laws

This module uses the proved integral-substitution theorem; in its monad-law
applications, valuation evaluation functions are bounded by one. No unproved
associativity premise is stored in the construction.
-/

set_option autoImplicit false
open Set Topology TopologicalSpace CategoryTheory
open scoped ENNReal Classical
universe u

namespace ZFCFubini.ValuationMonad

def identityKernel (P : DcpoCat.{u}) : WithScott (obj P) → SubprobValuation (WithScott P) :=
  WithScott.ofScott

theorem identityKernel_continuous (P : DcpoCat.{u}) :
    Continuous (fun x => WithScott.toScott (identityKernel P x)) := continuous_id

theorem evaluation_isLSC (P : DcpoCat.{u}) (U : ScottOpens P) :
    IsLSC (fun ν : WithScott (obj P) => (WithScott.ofScott ν).val U) :=
  scott_isLSC (P := obj P) (SubprobValuation.evaluation_scottContinuous U)

theorem integral_map {P Q : DcpoCat.{u}} (f : P ⟶ Q) (μ : obj P)
    (g : WithScott Q → ℝ≥0∞) (hg : IsLSC g) :
    choquetIntegral (map f μ).val g = choquetIntegral μ.val
      (fun x => g (WithScott.toScott (f (WithScott.ofScott x)))) :=
  choquetIntegral_push μ.val _ _ g hg

/-- Multiplication is actual integration of valuation-valued evaluation. -/
noncomputable def mul (P : DcpoCat.{u}) : obj (obj P) ⟶ obj P :=
  ⟨fun μ => μ.bind (identityKernel P) (identityKernel_continuous P),
    SubprobValuation.bind_scottContinuous _ _⟩

@[simp] theorem mul_apply (P : DcpoCat.{u}) (μ : obj (obj P)) (U : ScottOpens P) :
    (mul P μ).val U = choquetIntegral μ.val
      (fun ν => (WithScott.ofScott ν).val U) := rfl

theorem mul_naturality {P Q : DcpoCat.{u}} (f : P ⟶ Q) :
    map (map f) ≫ mul Q = mul P ≫ map f := by
  apply DcpoCat.Hom.ext
  intro μ
  apply Subtype.ext
  apply Valuation.ext
  intro U
  change choquetIntegral
      (μ.val.push (fun ν => WithScott.toScott (map f (WithScott.ofScott ν)))
        ((scott_continuous_iff _).mp (map f).continuous))
      (fun ν => (WithScott.ofScott ν).val U) = _
  exact choquetIntegral_push μ.val
    (fun ν => WithScott.toScott (map f (WithScott.ofScott ν)))
    ((scott_continuous_iff _).mp (map f).continuous)
    (fun ν : WithScott (obj Q) => (WithScott.ofScott ν).val U) (evaluation_isLSC Q U)

noncomputable def mulNatTrans : functor ⋙ functor ⟶ functor where
  app := mul
  naturality {P Q} f := mul_naturality f

theorem left_unit (P : DcpoCat.{u}) : unit (obj P) ≫ mul P = 𝟙 (obj P) := by
  apply DcpoCat.Hom.ext
  intro μ
  exact SubprobValuation.bind_dirac (WithScott.toScott μ)
    (identityKernel P) (identityKernel_continuous P)

theorem right_unit (P : DcpoCat.{u}) : map (unit P) ≫ mul P = 𝟙 (obj P) := by
  apply DcpoCat.Hom.ext
  intro μ
  apply Subtype.ext
  apply Valuation.ext
  intro U
  change choquetIntegral
      (μ.val.push (fun x => WithScott.toScott (unit P (WithScott.ofScott x)))
        ((scott_continuous_iff _).mp (unit P).continuous))
      (fun ν => (WithScott.ofScott ν).val U) = μ.val U
  rw [choquetIntegral_push μ.val
    (fun x => WithScott.toScott (unit P (WithScott.ofScott x)))
    ((scott_continuous_iff _).mp (unit P).continuous)
    (fun ν : WithScott (obj P) => (WithScott.ofScott ν).val U) (evaluation_isLSC P U)]
  have hδ : Continuous (fun x : WithScott P =>
      WithScott.toScott (SubprobValuation.dirac x)) :=
    (scott_continuous_iff _).mp SubprobValuation.dirac_scottContinuous
  exact congrArg (fun ν : SubprobValuation (WithScott P) => ν.val U)
    (SubprobValuation.bind_unit μ hδ)

theorem associativity (P : DcpoCat.{u}) :
    map (mul P) ≫ mul P = mul (obj P) ≫ mul P := by
  apply DcpoCat.Hom.ext
  intro μ
  apply Subtype.ext
  apply Valuation.ext
  intro U
  change choquetIntegral
      (μ.val.push (fun ν => WithScott.toScott (mul P (WithScott.ofScott ν)))
        ((scott_continuous_iff _).mp (mul P).continuous))
      (fun ν => (WithScott.ofScott ν).val U) =
      choquetIntegral (SubprobValuation.bind μ (identityKernel (obj P))
        (identityKernel_continuous (obj P))).val
        (fun ν => (WithScott.ofScott ν).val U)
  rw [choquetIntegral_push μ.val
    (fun ν => WithScott.toScott (mul P (WithScott.ofScott ν)))
    ((scott_continuous_iff _).mp (mul P).continuous)
    (fun ν : WithScott (obj P) => (WithScott.ofScott ν).val U) (evaluation_isLSC P U)]
  exact (choquetIntegral_bind μ (identityKernel (obj P))
    (identityKernel_continuous (obj P)) _
    (evaluation_isLSC P U)).symm

/-- The actual category-theoretic continuous subprobability valuation monad. -/
noncomputable def monad : CategoryTheory.Monad DcpoCat.{u} where
  toFunctor := functor
  η := unitNatTrans
  μ := mulNatTrans
  assoc := associativity
  left_unit := left_unit
  right_unit := right_unit

end ZFCFubini.ValuationMonad
