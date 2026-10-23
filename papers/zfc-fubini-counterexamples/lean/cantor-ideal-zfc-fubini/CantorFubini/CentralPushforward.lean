import CantorFubini.CentralFubini
import CantorFubini.ScottIntegralSections
import CantorFubini.SourceIteratedIntegral
import CantorFubini.SecondValuation

/-! Actual source centrality of compact zero-dimensional Radon pushforwards,
including every concrete stage etaStage M. The partner is an arbitrary dcpo
with an arbitrary continuous subprobability valuation; the conclusion uses
the source's ordinary-real SourceCentral predicate, with independent
universe levels for the valuation space and its partner. -/

set_option autoImplicit false
open Set Topology TopologicalSpace MeasureTheory
open scoped ENNReal
universe u v w
namespace CantorFubini

section CompactPushforward
variable {X : Type u} [TopologicalSpace X] [CompactSpace X] [T2Space X]
variable [TotallyDisconnectedSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
variable {D : Type v} [PartialOrder D]

/-- Every continuous pushforward of an actual subprobability Radon measure
on a compact Hausdorff totally disconnected space is central in exactly the
source's ordinary-real sense. -/
theorem compact_pushforward_sourceCentral (μ : Measure X)
    [Measure.InnerRegular μ] [SFinite μ]
    (hμ : (radonValuation μ).Subprobability)
    (f : X → WithScott D) (hf : Continuous f) :
    SourceCentral.{v, w} ((radonValuation μ).push f hf) := by
  have hpush : ((radonValuation μ).push f hf).Subprobability := hμ
  refine ⟨hpush, ?_⟩
  intro E _ _ ρ hρ h hh
  let α : SubprobValuation (WithScott D) := ⟨(radonValuation μ).push f hf, hpush⟩
  let β : SubprobValuation (WithScott E) := ⟨ρ, hρ⟩
  let H : WithScott D → WithScott E → ℝ :=
    fun d e => (h (WithScott.ofScott d, WithScott.ofScott e)).val
  have hH1 : ∀ d e, H d e ≤ 1 := fun d e =>
    (h (WithScott.ofScott d, WithScott.ofScott e)).property.2
  let K : WithScott D → WithScott E → ℝ≥0∞ :=
    fun d e => ENNReal.ofReal (H d e)
  have hinner : (fun e => vIntegral α.val (fun d => K d e)) =
      fun e => vIntegral (radonValuation μ) (fun x => K (f x) e) := by
    funext e
    exact vIntegral_push (radonValuation μ) f hf
      (unit_first_section_isVLSC h hh (WithScott.ofScott e))
  have houter : vIntegral α.val (fun d => vIntegral ρ (K d)) =
      vIntegral (radonValuation μ) (fun x => vIntegral ρ (K (f x))) :=
    vIntegral_push (radonValuation μ) f hf (unit_partial_vIntegral_isVLSC h hh ρ)
  have hjoint : IsVLSC (fun z : X × WithScott E => K (f z.1) z.2) :=
    isVLSC_ofReal (compact_parameter_joint_isRealLSC f hf h hh)
  have hF : vIntegral ρ (fun e => vIntegral α.val (fun d => K d e)) =
      vIntegral α.val (fun d => vIntegral ρ (K d)) := by
    rw [hinner, houter]
    exact compact_parameter_fubini μ ρ (fun x e => K (f x) e) hjoint
  change sourceIntegral β.val (fun e => sourceIntegral α.val (fun d => H d e)) =
    sourceIntegral α.val (fun d => sourceIntegral β.val (fun e => H d e))
  rw [sourceIntegral_iterated_eq_vIntegral α β H hH1,
    sourceIntegral_iterated_eq_vIntegral β α (fun e d => H d e) (fun e d => hH1 d e)]
  exact congrArg ENNReal.toReal hF

end CompactPushforward

/-- The centrality assertion about every actual eta stage in source Remark
6.5, with all partner-dcpo and subprobability-valuation quantifiers intact. -/
theorem etaStage_sourceCentral (M : NullIndex cantorMeasure) :
    SourceCentral.{0, w} (etaStage M) := by
  unfold etaStage
  exact compact_pushforward_sourceCentral parameterProbability
    (radonValuation_probability parameterProbability).subprobability
    (G cantorMeasure randomOpen M)
    (G_continuous cantorMeasure randomOpen randomOpen_continuous M)

/-- The noncentral limiting valuation is distinct from every continuous
pushforward stage appearing in source Remark 6.5. -/
theorem eta_ne_etaStage (M : NullIndex cantorMeasure) : eta ≠ etaStage M := by
  intro he
  have hc := etaStage_sourceCentral.{0} M
  rw [← he] at hc
  exact eta_noncentral hc

end CantorFubini
