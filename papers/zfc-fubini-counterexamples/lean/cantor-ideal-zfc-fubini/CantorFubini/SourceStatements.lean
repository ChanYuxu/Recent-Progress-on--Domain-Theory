import CantorFubini.Corollaries
import CantorFubini.SourceScottStatements
import CantorFubini.KernelConsequences
import CantorFubini.ModelBridges
import CantorFubini.RealInfimum
import CantorFubini.Subprobability
import CantorFubini.SourceValuationEquivalence
import CantorFubini.SourceMeasureBridge
import CantorFubini.CentralPushforward
import CantorFubini.ValuationMonadCounterexample

/-! Public printed interfaces, including the actual categorical valuation
monad obstruction and centrality of every specified pushforward stage. -/
set_option autoImplicit false
open Set Topology TopologicalSpace MeasureTheory
universe u v w
namespace CantorFubini

/-- Source Proposition 2.2: the specified family is a topology, and the
completed fair-coin measure restricted to it is a continuous probability. -/
theorem source_tau :
    (∀ U : Set Cantor, (nullTopology cantorMeasure).IsOpen U ↔
      ∃ O : Set Cantor, IsOpen O ∧ ∃ M : Set Cantor,
        cantorMeasure.completion M = 0 ∧ U = O \ M) ∧
    (∃ μ : @Valuation Cantor (nullTopology cantorMeasure),
      @Valuation.Probability Cantor (nullTopology cantorMeasure) μ ∧
      ∀ U : @Opens Cantor (nullTopology cantorMeasure), μ U = cantorMeasure.completion (U : Set Cantor)) :=
  ⟨fun _ => Iff.rfl, nullValuation cantorMeasure, nullValuation_probability cantorMeasure,
    fun _ => rfl⟩

/-- Source Theorem 3.5 with the full Scott topology and completed measure. -/
theorem source_nu : (nu cantorMeasure).Probability ∧
    (∀ H : ScottOpens P, nu cantorMeasure H = cantorMeasure.completion (trace H : Set Cantor)) ∧
    ScottContinuous (nu cantorMeasure).mass :=
  ⟨nu_probability cantorMeasure, fun _ => rfl, (nu cantorMeasure).continuous⟩

/-- Both conclusions of source Lemma 4.1, with the specified B_(U_t). -/
theorem source_random_continuity :
    (∀ C : Set Cantor, IsCompact C → IsOpen {t : Omega | C ⊆ randomOpen t}) ∧
    (∀ H : Q, Continuous (fun t : Omega => WithScott.toScott (B cantorMeasure (randomOpen t) ⊔ H))) :=
  ⟨fun _ hC => randomOpen_compact_containment_isOpen hC,
    fun H => randomOpen_scott_sup_continuous (B cantorMeasure) (B_scottContinuous cantorMeasure) H⟩

/-- Source Theorem 5.5, on the entire intrinsic Scott-open lattice. -/
theorem source_eta : eta ⊥ = 0 ∧ eta ⊤ = 1 ∧ Monotone eta.mass ∧
    (∀ A₀ B₀ : ScottOpens Q, eta A₀ + eta B₀ = eta (A₀ ⊔ B₀) + eta (A₀ ⊓ B₀)) ∧
    ScottContinuous eta.mass :=
  ⟨eta.strict, eta_probability, eta.mono, eta.modular, eta.continuous⟩

/-- Source Lemma 6.1, using the order product, with all evaluation suprema. -/
theorem source_evaluation : ScottContinuous (incidence P) ∧
    (∀ p : P, IsOpen (evaluationOpen p : Set (WithScott Q))) ∧
    (∀ (D : Set P) (hn : D.Nonempty) (hd : DirectedOn (· ≤ ·) D) (p : P),
      IsLUB D p → evaluationOpen p = ⨆ d : D, evaluationOpen d.val) :=
  ⟨incidence_scottContinuous P, fun p => (evaluationOpen p).isOpen,
    fun _ hn hd _ hp => evaluationOpen_directed_sup hn hd hp⟩

/-- Source Lemma 6.2: the printed section, its continuity, exact product q,
and the sharper lower bound in that lemma. -/
theorem source_section_values :
    (∀ p : P, eta (evaluationOpen p) = parameterProbability {t : Omega | p.kernel ⊆ randomOpen t}) ∧
    ScottContinuous sectionValueUnit ∧
    (∀ x : Cantor, sectionValue (IdealPoint.e cantorMeasure x) = q) ∧
    q = 1 - ∏' n : ℕ, (1 - (2 : ℝ) ^ (-((n : ℤ) + 2))) ∧
    1 / 4 ≤ q ∧ q ≤ 1 / 2 :=
  ⟨eta_evaluation, sectionValueUnit_scottContinuous, sectionValue_maximal, q_source, q_bounds⟩

/-- The printed existential statement of source Theorem 6.3. The witness E
has a complete-lattice structure, strengthening the requested dcpo conclusion. -/
theorem source_main_exists :
    ∃ D E : Type, ∃ oD : PartialOrder D, ∃ oE : CompleteLattice E,
      letI : PartialOrder D := oD
      letI : CompleteLattice E := oE
      IsDcpo D ∧ IsDcpo E ∧
      ∃ μ : ProbabilityValuation (WithScott D), ∃ ρ : ProbabilityValuation (WithScott E),
      ∃ w : D × E → UnitInterval,
        ScottContinuous w ∧
        paperIntegral ρ (fun y : WithScott E => paperIntegral μ (fun x : WithScott D =>
          (w (WithScott.ofScott x, WithScott.ofScott y)).val)) = 1 ∧
        paperIntegral μ (fun x : WithScott D => paperIntegral ρ (fun y : WithScott E =>
          (w (WithScott.ofScott x, WithScott.ofScott y)).val)) = q ∧
        0 < q ∧ q ≤ 1 / 2 := by
  refine ⟨P, Q, inferInstance, inferInstance, P_isDcpo, Q_isDcpo,
    nuProbability, etaProbability, incidence P, incidence_scottContinuous P, ?_⟩
  exact source_main.2.2.2.2.2

/-- The decreasing-infimum assertions of Remark 6.5. The complete source
interface, including centrality, is `source_decreasing_central_infimum`. -/
theorem source_decreasing_infimum :
    (∀ M : NullIndex cantorMeasure, (etaStage M).Probability) ∧
    (∀ M N : NullIndex cantorMeasure, M ≤ N → ∀ A₀ : ScottOpens Q, etaStage N A₀ ≤ etaStage M A₀) ∧
    (∀ A₀ : ScottOpens Q, eta A₀ = ⨅ M : NullIndex cantorMeasure, etaStage M A₀) := by
  refine ⟨etaStage_probability, ?_, eta_eq_iInf_etaStage⟩
  intro M N hMN A₀
  apply measure_mono
  exact stageEvent_antitone (G cantorMeasure randomOpen) (G_antitone cantorMeasure randomOpen) A₀ hMN

/-- Complete printed Corollary 6.4: an existential noncentral continuous
probability valuation, and noncommutativity of the actual strong valuation
monad on the category of small dcpos. -/
theorem source_corollary_noncentral :
    (∃ D : Type, ∃ oD : PartialOrder D,
      letI : PartialOrder D := oD
      IsDcpo D ∧ ∃ μ : ProbabilityValuation (WithScott D),
        ¬ SourceCentral.{0, 0} μ.val) ∧
    ¬ DCPO.valuationMonadStrength.{0}.IsCommutative := by
  refine ⟨?_, source_monad_noncommutative⟩
  exact ⟨P, inferInstance, P_isDcpo, nuProbability, nu_noncentral⟩

/-- Complete printed Remark 6.5, retaining the actual specified maps and
ordinary-real infimum. Each stage commutes with partners in any universe;
the fixed small counterexample already witnesses eta's noncentrality. -/
theorem source_decreasing_central_infimum :
    CompactSpace Omega ∧ T2Space Omega ∧
    (∀ M : NullIndex cantorMeasure,
      Continuous (G cantorMeasure randomOpen M) ∧
      etaStage M = (radonValuation parameterProbability).push
        (G cantorMeasure randomOpen M)
        (G_continuous cantorMeasure randomOpen randomOpen_continuous M) ∧
      (etaStage M).Probability ∧ SourceCentral.{0, w} (etaStage M)) ∧
    (∀ M N : NullIndex cantorMeasure, M ≤ N → ∀ A₀ : ScottOpens Q,
      etaStage N A₀ ≤ etaStage M A₀) ∧
    (∀ A₀ : ScottOpens Q, eta A₀ = ⨅ M : NullIndex cantorMeasure, etaStage M A₀) ∧
    (∀ A₀ : ScottOpens Q,
      (eta A₀).toReal = ⨅ M : NullIndex cantorMeasure, (etaStage M A₀).toReal) ∧
    ¬ SourceCentral.{0, 0} eta ∧
    (∀ M : NullIndex cantorMeasure, eta ≠ etaStage M) := by
  refine ⟨inferInstance, inferInstance, ?_, source_decreasing_infimum.2.1,
    eta_eq_iInf_etaStage, eta_real_infimum, eta_noncentral, eta_ne_etaStage⟩
  intro M
  exact ⟨G_continuous cantorMeasure randomOpen randomOpen_continuous M,
    rfl, etaStage_probability M, etaStage_sourceCentral M⟩

end CantorFubini
