import ZFCFubini.ValuationIntegral
import ZFCFubini.ValuationBindBasic

/-!
# Actual integration-defined Kleisli extension

The value on an open `U` is the existing Choquet integral of `x ↦ k x U`.
Strictness, modularity, and full directed continuity are proved from the
integral laws, never installed as fields of a kernel certificate.
-/

set_option autoImplicit false
open Set Topology TopologicalSpace MeasureTheory
open scoped ENNReal Classical
universe u v w

namespace ZFCFubini

namespace SubprobValuation

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

theorem kernel_isLSC (k : X → SubprobValuation Y)
    (hk : Continuous (fun x => WithScott.toScott (k x))) (U : Opens Y) :
    IsLSC (fun x => (k x).val U) :=
  (scott_isLSC (evaluation_scottContinuous U)).comp _ hk

/-- The actual bind of a continuous subprobability-valued kernel. -/
noncomputable def bind (μ : SubprobValuation X) (k : X → SubprobValuation Y)
    (hk : Continuous (fun x => WithScott.toScott (k x))) : SubprobValuation Y := by
  let v : Valuation Y := {
    mass := fun U => choquetIntegral μ.val (fun x => (k x).val U)
    strict := by
      have hzero : (fun x => (k x).val ⊥) = (fun _ => 0) := funext fun x => (k x).val.strict
      rw [hzero, choquetIntegral_const, zero_mul]
    modular := fun U V => by
      calc
        choquetIntegral μ.val (fun x => (k x).val U) +
            choquetIntegral μ.val (fun x => (k x).val V) =
            choquetIntegral μ.val ((fun x => (k x).val U) + (fun x => (k x).val V)) :=
          (choquetIntegral_add μ.val μ.property (kernel_isLSC k hk U)
            (kernel_isLSC k hk V)).symm
        _ = choquetIntegral μ.val
            ((fun x => (k x).val (U ⊔ V)) + (fun x => (k x).val (U ⊓ V))) := by
          congr 1
          exact funext fun x => (k x).val.modular U V
        _ = _ := choquetIntegral_add μ.val μ.property
          (kernel_isLSC k hk (U ⊔ V)) (kernel_isLSC k hk (U ⊓ V))
    continuous := choquetIntegral_scottContinuous_param μ.val
      (fun U x => (k x).val U) (kernel_isLSC k hk) (fun x => (k x).val.continuous) }
  exact ⟨v, choquetIntegral_le_one μ.val μ.property fun x => (k x).property⟩

@[simp] theorem bind_apply (μ : SubprobValuation X) (k : X → SubprobValuation Y)
    (hk : Continuous (fun x => WithScott.toScott (k x))) (U : Opens Y) :
    (bind μ k hk).val U = choquetIntegral μ.val (fun x => (k x).val U) := rfl

theorem bind_scottContinuous (k : X → SubprobValuation Y)
    (hk : Continuous (fun x => WithScott.toScott (k x))) :
    ScottContinuous (fun μ : SubprobValuation X => bind μ k hk) := by
  apply scottContinuous_of_evaluation
  intro U
  exact val_scottContinuous.comp
    (choquetIntegral_scottContinuous_valuation _ (kernel_isLSC k hk U))

theorem bind_scottContinuous_param {P : Type w} [Preorder P]
    (μ : SubprobValuation X) (k : P → X → SubprobValuation Y)
    (hk : ∀ p, Continuous (fun x => WithScott.toScott (k p x)))
    (hp : ∀ x, ScottContinuous (fun p => k p x)) :
    ScottContinuous (fun p => bind μ (k p) (hk p)) := by
  apply scottContinuous_of_evaluation
  intro U
  exact choquetIntegral_scottContinuous_param μ.val (fun p x => (k p x).val U)
    (fun p => kernel_isLSC (k p) (hk p) U)
    (fun x => (hp x).comp (evaluation_scottContinuous U))

theorem bind_scottContinuous_joint {P : Type w} [Preorder P]
    (μ : P → SubprobValuation X) (hμ : ScottContinuous μ)
    (k : P → X → SubprobValuation Y)
    (hk : ∀ p, Continuous (fun x => WithScott.toScott (k p x)))
    (hp : ∀ x, ScottContinuous (fun p => k p x)) :
    ScottContinuous (fun p => bind (μ p) (k p) (hk p)) := by
  apply scottContinuous_of_evaluation
  intro U
  exact choquetIntegral_scottContinuous_joint μ hμ (fun p x => (k p x).val U)
    (fun p => kernel_isLSC (k p) (hk p) U)
    (fun x => (hp x).comp (evaluation_scottContinuous U))

@[simp] theorem bind_dirac (x : X) (k : X → SubprobValuation Y)
    (hk : Continuous (fun x => WithScott.toScott (k x))) :
    bind (dirac x) k hk = k x := by
  apply Subtype.ext
  apply Valuation.ext
  intro U
  exact choquetIntegral_dirac x _ (kernel_isLSC k hk U)

@[simp] theorem bind_unit (μ : SubprobValuation X)
    (hδ : Continuous (fun x : X => WithScott.toScott (dirac x))) :
    bind μ dirac hδ = μ := by
  apply Subtype.ext
  apply Valuation.ext
  intro U
  change choquetIntegral μ.val (fun x => Valuation.dirac x U) = μ.val U
  have heq : (fun x => Valuation.dirac x U) = (U : Set X).indicator (fun _ => 1) := by
    funext x
    simp only [Valuation.dirac_apply, Set.indicator_apply]
    rfl
  rw [heq, choquetIntegral_indicator, one_mul]

theorem pushKernel_continuous {Z : Type w} [TopologicalSpace Z]
    (k : X → SubprobValuation Y) (hk : Continuous (fun x => WithScott.toScott (k x)))
    (g : Y → Z) (hg : Continuous g) :
    Continuous (fun x => WithScott.toScott ((k x).push g hg)) :=
  ((scott_continuous_iff _).mp (push_scottContinuous g hg)).comp hk

/-- Pushing the output of bind is the same actual open-preimage calculation. -/
theorem push_bind {Z : Type w} [TopologicalSpace Z]
    (μ : SubprobValuation X) (k : X → SubprobValuation Y)
    (hk : Continuous (fun x => WithScott.toScott (k x))) (g : Y → Z) (hg : Continuous g) :
    (bind μ k hk).push g hg =
      bind μ (fun x => (k x).push g hg) (pushKernel_continuous k hk g hg) := by
  apply Subtype.ext
  apply Valuation.ext
  intro U
  rfl

/-- Pushing the input of bind uses the actual Choquet change of variables. -/
theorem bind_push {Z : Type w} [TopologicalSpace Z]
    (μ : SubprobValuation X) (g : X → Y) (hg : Continuous g)
    (k : Y → SubprobValuation Z) (hk : Continuous (fun y => WithScott.toScott (k y))) :
    bind (μ.push g hg) k hk = bind μ (fun x => k (g x)) (hk.comp hg) := by
  apply Subtype.ext
  apply Valuation.ext
  intro U
  exact choquetIntegral_push μ.val g hg _ (kernel_isLSC k hk U)

theorem bindKernel_continuous {Z : Type w} [TopologicalSpace Z]
    (k : X → SubprobValuation Y) (hk : Continuous (fun x => WithScott.toScott (k x)))
    (l : Y → SubprobValuation Z) (hl : Continuous (fun y => WithScott.toScott (l y))) :
    Continuous (fun x => WithScott.toScott (bind (k x) l hl)) :=
  ((scott_continuous_iff _).mp (bind_scottContinuous l hl)).comp hk

end SubprobValuation
end ZFCFubini
