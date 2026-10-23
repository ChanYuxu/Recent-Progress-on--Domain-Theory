import CantorFubini.Main

/-! Printed real-integral centrality for arbitrary subprobability partners,
with independent universe levels for the two dcpos. Companion modules prove
the actual categorical monad counterexample (`ValuationMonadCounterexample`)
and centrality of every compact-parameter stage (`CentralPushforward`). -/
set_option autoImplicit false
open Set Topology TopologicalSpace MeasureTheory
universe u v
namespace CantorFubini

/-- The source real strict-level formula, also for subprobability valuations. -/
noncomputable def sourceIntegral {X : Type u} [TopologicalSpace X]
    (μ : Valuation X) (f : X → ℝ) : ℝ :=
  ∫ a : ℝ in Icc (0 : ℝ) 1,
    (μ ⟨interior {x | a < f x}, isOpen_interior⟩).toReal

theorem sourceIntegral_probability {X : Type u} [TopologicalSpace X]
    (μ : ProbabilityValuation X) (f : X → ℝ) :
    sourceIntegral μ.val f = paperIntegral μ f := rfl

theorem sourceIntegral_eq_strictLevels {X : Type u} [TopologicalSpace X]
    (μ : Valuation X) (f : X → ℝ) (hf : IsRealLSC f) :
    sourceIntegral μ f = ∫ a : ℝ in Icc (0 : ℝ) 1,
      (μ ⟨{x | a < f x}, hf a⟩).toReal := by
  unfold sourceIntegral
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun a => congrArg
    (fun U : Opens X => (μ U).toReal) (Opens.ext (hf a).interior_eq))

def SourceCommute {D : Type u} {E : Type v} [PartialOrder D] [PartialOrder E]
    (μ : DValuation D) (ρ : DValuation E) : Prop :=
  ∀ h : D × E → UnitInterval, ScottContinuous h →
    sourceIntegral ρ (fun y => sourceIntegral μ (fun x =>
      (h (WithScott.ofScott x, WithScott.ofScott y)).val)) =
    sourceIntegral μ (fun x => sourceIntegral ρ (fun y =>
      (h (WithScott.ofScott x, WithScott.ofScott y)).val))

/-- Source centrality: the partner ranges over all dcpos and all continuous
subprobability valuations, on their full order Scott topologies. -/
def SourceCentral {D : Type u} [PartialOrder D] (μ : DValuation D) : Prop :=
  μ.Subprobability ∧ ∀ (E : Type v) [PartialOrder E], IsDcpo E →
    ∀ ρ : DValuation E, ρ.Subprobability → SourceCommute μ ρ

theorem nu_eta_do_not_commute : ¬ SourceCommute (nu cantorMeasure) eta := by
  intro h
  have he := h (incidence P) (incidence_scottContinuous P)
  change paperIntegral etaProbability (fun H : WithScott Q =>
    paperIntegral nuProbability (fun p : WithScott P =>
      (incidence P (WithScott.ofScott p, WithScott.ofScott H)).val)) =
    paperIntegral nuProbability (fun p : WithScott P =>
      paperIntegral etaProbability (fun H : WithScott Q =>
        (incidence P (WithScott.ofScott p, WithScott.ofScott H)).val)) at he
  rw [source_main.2.2.2.2.2.1, source_main.2.2.2.2.2.2.1] at he
  linarith [q_bounds.2]

theorem sourceCommute_symm {D : Type u} {E : Type v} [PartialOrder D] [PartialOrder E]
    {μ : DValuation D} {ρ : DValuation E} (h : SourceCommute ρ μ) : SourceCommute μ ρ := by
  intro f hf
  have hswap : ScottContinuous (fun z : E × D => f (z.2, z.1)) :=
    (ScottContinuous.snd.prodMk ScottContinuous.fst).comp hf
  exact (h (fun z => f (z.2, z.1)) hswap).symm

theorem nu_noncentral : ¬ SourceCentral.{0, 0} (nu cantorMeasure) := by
  intro h
  exact nu_eta_do_not_commute (h.2 Q Q_isDcpo eta eta_probability.subprobability)

theorem eta_noncentral : ¬ SourceCentral.{0, 0} eta := by
  intro h
  exact nu_eta_do_not_commute (sourceCommute_symm
    (h.2 P P_isDcpo (nu cantorMeasure) (nu_probability cantorMeasure).subprobability))

/-- The real-integral noncentrality assertions of Corollary 6.4. -/
theorem source_noncentral :
    ¬ SourceCentral.{0, 0} (nu cantorMeasure) ∧ ¬ SourceCentral.{0, 0} eta :=
  ⟨nu_noncentral, eta_noncentral⟩

end CantorFubini
