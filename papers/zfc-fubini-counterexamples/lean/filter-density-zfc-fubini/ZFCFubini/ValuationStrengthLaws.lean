import ZFCFubini.ValuationStrength
import ZFCFubini.ValuationMonadLaws

/-!
# The genuine strength of the continuous subprobability valuation monad

All five coherence laws refer to the actual categorical functor, unit and
integration-defined multiplication. The two double-strength arrows are then
computed on every actual Scott open, giving the two integration orders.
-/

set_option autoImplicit false
open Set Topology TopologicalSpace CategoryTheory
open CategoryTheory.MonoidalCategory
open scoped ENNReal Classical
universe u

namespace ZFCFubini.ValuationMonad

def pairLeft (P Q : DcpoCat.{u}) (p : P) : Q ⟶ P ⊗ Q :=
  ⟨fun q => (p, q), (ScottContinuous.const p).prodMk ScottContinuous.id⟩

def pairRight (P Q : DcpoCat.{u}) (q : Q) : P ⟶ P ⊗ Q :=
  ⟨fun p => (p, q), ScottContinuous.id.prodMk (ScottContinuous.const q)⟩

theorem strengthHom_eq_map (P Q : DcpoCat.{u}) (p : P) (ν : obj Q) :
    strengthHom P Q (p, ν) = map (pairLeft P Q p) ν := rfl

theorem strengthHom_mul (P Q : DcpoCat.{u}) :
    (𝟙 P ⊗ₘ mul Q) ≫ strengthHom P Q =
      strengthHom P (obj Q) ≫ map (strengthHom P Q) ≫ mul (P ⊗ Q) := by
  apply DcpoCat.Hom.ext
  intro z
  exact (congrArg (fun f : obj (obj Q) ⟶ obj (P ⊗ Q) => f z.2)
    (mul_naturality (pairLeft P Q z.1))).symm

/-- The actual strong monad, with every tensorial-strength diagram proved. -/
noncomputable def strength : CartesianMonadStrength monad where
  σ := strengthHom
  naturality := strengthHom_naturality
  left_unit := strengthHom_left_unit
  associator := strengthHom_associator
  unit := strengthHom_unit
  mul := strengthHom_mul

def rightOpenSection (P Q : DcpoCat.{u}) (U : ScottOpens (P × Q)) (q : Q) : ScottOpens P :=
  Opens.comap
    ⟨fun x => WithScott.toScott (WithScott.ofScott x, q),
      (scott_continuous_iff _).mp
        (ScottContinuous.id.prodMk (ScottContinuous.const q))⟩ U

@[simp] theorem mem_rightOpenSection (P Q : DcpoCat.{u}) (U : ScottOpens (P × Q))
    (p : P) (q : Q) :
    WithScott.toScott p ∈ rightOpenSection P Q U q ↔ WithScott.toScott (p, q) ∈ U := Iff.rfl

@[simp] theorem costrength_apply (P Q : DcpoCat.{u}) (μ : obj P) (q : Q)
    (U : ScottOpens (P × Q)) :
    (strength.costrength P Q (μ, q)).val U = μ.val (rightOpenSection P Q U q) := rfl

theorem costrength_eq_map (P Q : DcpoCat.{u}) (μ : obj P) (q : Q) :
    strength.costrength P Q (μ, q) = map (pairRight P Q q) μ := by
  apply Subtype.ext
  apply Valuation.ext
  intro U
  rfl

/-- The first double strength integrates first over `Q`, then over `P`. -/
theorem doubleStrength_apply (P Q : DcpoCat.{u}) (μ : obj P) (ν : obj Q)
    (U : ScottOpens (P × Q)) :
    (strength.doubleStrength P Q (μ, ν)).val U =
      choquetIntegral μ.val (fun p => choquetIntegral ν.val (fun q =>
        if WithScott.toScott (WithScott.ofScott p, WithScott.ofScott q) ∈ U then 1 else 0)) := by
  have he (p : WithScott P) :
      choquetIntegral ν.val (fun q =>
        if WithScott.toScott (WithScott.ofScott p, WithScott.ofScott q) ∈ U then 1 else 0) =
        ν.val (openSection P Q U (WithScott.ofScott p)) := by
    have heq : (fun q : WithScott Q =>
        if WithScott.toScott (WithScott.ofScott p, WithScott.ofScott q) ∈ U then
          (1 : ℝ≥0∞) else 0) =
        (openSection P Q U (WithScott.ofScott p) : Set (WithScott Q)).indicator (fun _ => 1) := by
      funext q
      simp only [Set.indicator_apply]
      rfl
    rw [heq, choquetIntegral_indicator, one_mul]
  simp_rw [he]
  change choquetIntegral (map (strengthHom P Q)
    (strength.costrength P (obj Q) (μ, ν))).val
      (fun ρ : WithScott (obj (P ⊗ Q)) => (WithScott.ofScott ρ).val U) = _
  rw [costrength_eq_map]
  rw [integral_map (strengthHom P Q) (map (pairRight P (obj Q) ν) μ)
    (fun ρ : WithScott (obj (P ⊗ Q)) => (WithScott.ofScott ρ).val U)
    (evaluation_isLSC (P ⊗ Q) U)]
  simp only [WithScott.ofScott_toScott]
  have hσ : IsLSC (fun w : WithScott (DcpoCat.prod P (obj Q)) =>
      (strengthHom P Q (WithScott.ofScott w)).val U) :=
    (evaluation_isLSC (P ⊗ Q) U).comp
      (fun w : WithScott (DcpoCat.prod P (obj Q)) =>
        WithScott.toScott (strengthHom P Q (WithScott.ofScott w)))
      ((scott_continuous_iff _).mp (strengthHom P Q).continuous)
  exact integral_map (pairRight P (obj Q) ν) μ
    (fun w : WithScott (DcpoCat.prod P (obj Q)) =>
      (strengthHom P Q (WithScott.ofScott w)).val U) hσ

/-- The second double strength integrates first over `P`, then over `Q`. -/
theorem doubleStrength'_apply (P Q : DcpoCat.{u}) (μ : obj P) (ν : obj Q)
    (U : ScottOpens (P × Q)) :
    (strength.doubleStrength' P Q (μ, ν)).val U =
      choquetIntegral ν.val (fun q => choquetIntegral μ.val (fun p =>
        if WithScott.toScott (WithScott.ofScott p, WithScott.ofScott q) ∈ U then 1 else 0)) := by
  have he (q : WithScott Q) :
      choquetIntegral μ.val (fun p =>
        if WithScott.toScott (WithScott.ofScott p, WithScott.ofScott q) ∈ U then 1 else 0) =
        μ.val (rightOpenSection P Q U (WithScott.ofScott q)) := by
    have heq : (fun p : WithScott P =>
        if WithScott.toScott (WithScott.ofScott p, WithScott.ofScott q) ∈ U then
          (1 : ℝ≥0∞) else 0) =
        (rightOpenSection P Q U (WithScott.ofScott q) : Set (WithScott P)).indicator (fun _ => 1) := by
      funext p
      simp only [Set.indicator_apply]
      rfl
    rw [heq, choquetIntegral_indicator, one_mul]
  simp_rw [he]
  change choquetIntegral (map (strength.costrength P Q)
    (strengthHom (obj P) Q (μ, ν))).val
      (fun ρ : WithScott (obj (P ⊗ Q)) => (WithScott.ofScott ρ).val U) = _
  rw [strengthHom_eq_map]
  rw [integral_map (strength.costrength P Q) (map (pairLeft (obj P) Q μ) ν)
    (fun ρ : WithScott (obj (P ⊗ Q)) => (WithScott.ofScott ρ).val U)
    (evaluation_isLSC (P ⊗ Q) U)]
  have hσ : IsLSC (fun w : WithScott (DcpoCat.prod (obj P) Q) =>
      (strength.costrength P Q (WithScott.ofScott w)).val U) :=
    (evaluation_isLSC (P ⊗ Q) U).comp
      (fun w : WithScott (DcpoCat.prod (obj P) Q) =>
        WithScott.toScott (strength.costrength P Q (WithScott.ofScott w)))
      ((scott_continuous_iff _).mp (strength.costrength P Q).continuous)
  exact integral_map (pairLeft (obj P) Q μ) ν
    (fun w : WithScott (DcpoCat.prod (obj P) Q) =>
      (strength.costrength P Q (WithScott.ofScott w)).val U) hσ

end ZFCFubini.ValuationMonad
