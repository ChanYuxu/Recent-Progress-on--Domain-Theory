import CHFubini

set_option pp.universes true
set_option autoImplicit false
open Set Topology TopologicalSpace MeasureTheory
open scoped ENNReal

#print CHFubini.PaperMainClaim
#print CHFubini.CounterexampleAt
#print CHFubini.counterexampleAt_of_CH
#print CHFubini.CH
#print CHFubini.choquetIntegral
#print CHFubini.Valuation
#print CHFubini.Central
#print CHFubini.singletonMap
#print CHFubini.completeLattice_scott_isWellFiltered
#print CHFubini.paper_product_topology_strict
#check CHFubini.paper_both_noncentral

#print axioms CHFubini.paper_main
#print axioms CHFubini.counterexampleAt_of_CH
#print axioms CHFubini.source_null_defect
#print axioms CHFubini.limitingValuation
#print axioms CHFubini.intervalFactors_multipliable
#print axioms CHFubini.pointHit_probability
#print axioms CHFubini.choquetIntegral_eq_layerCake
#print axioms CHFubini.source_first_iterated_integral
#print axioms CHFubini.source_second_iterated_integral
#print axioms CHFubini.paper_vietoris_scott
#print axioms CHFubini.paper_product_topology_strict

example (hCH : CHFubini.CH) : Nonempty (CHFubini.PaperSource hCH) :=
  ⟨CHFubini.pointAt (CHFubini.paperSequence hCH) CHFubini.zeroStage⟩

example (hCH : CHFubini.CH) : Nonempty (CHFubini.PaperP hCH) :=
  ⟨WithScott.ofScott (CHFubini.singletonMap
    (CHFubini.pointAt (CHFubini.paperSequence hCH) CHFubini.zeroStage))⟩

/- Raw source-facing re-expression: include the second dcpo assertion and
the actual inner-integral functions, not just aliases for section masses. -/
theorem independent_source_main :
    (Cardinal.continuum.{0} = Cardinal.aleph.{0} 1) →
    ∀ ε : ℝ, 0 < ε → ε < 1 →
    ∃ (P : Type) (orderP : PartialOrder P) (L : Type) (latticeL : CompleteLattice L),
      letI := orderP
      letI := latticeL
      CHFubini.IsDcpo P ∧ CHFubini.IsDcpo L ∧
      FirstCountableTopology (WithScott P) ∧ CHFubini.IsSober (WithScott P) ∧
      CHFubini.IsWellFiltered (WithScott P) ∧ CHFubini.IsWellFiltered (WithScott L) ∧
      ∃ (μ : CHFubini.DValuation P) (ρ : CHFubini.DValuation L)
        (W : CHFubini.ScottOpens (P × L)),
        μ.Probability ∧ ρ.Probability ∧
        CHFubini.choquetIntegral ρ
          (fun V => CHFubini.choquetIntegral μ
            (CHFubini.indicator (CHFubini.leftSection W (WithScott.ofScott V)))) = 1 ∧
        CHFubini.choquetIntegral μ
          (fun C => CHFubini.choquetIntegral ρ
            (CHFubini.indicator (CHFubini.rightSection W (WithScott.ofScott C)))) =
          ENNReal.ofReal (1 - ∏' n : ℕ, (1 - ε * (1 / 2 : ℝ) ^ (n + 1))) ∧
        0 < CHFubini.qEpsilon ε ∧ CHFubini.qEpsilon ε ≤ ε ∧ ε < 1 ∧
        ScottContinuous (fun V : L => CHFubini.choquetIntegral μ
          (CHFubini.indicator (CHFubini.leftSection W V))) ∧
        ScottContinuous (fun C : P => CHFubini.choquetIntegral ρ
          (CHFubini.indicator (CHFubini.rightSection W C))) := by
  intro hCH ε hε hε1
  obtain ⟨P, orderP, L, latticeL, hdcpo, hfirst, hsober, hwellP, hwellL,
    μ, ρ, W, hμ, hρ, hi, hj, hqpos, hqle, he1, hf, hg⟩ :=
    CHFubini.paper_main hCH ε hε hε1
  letI := orderP
  letI := latticeL
  refine ⟨P, orderP, L, latticeL, hdcpo, CHFubini.completeLattice_isDcpo L,
    hfirst, hsober, hwellP, hwellL, μ, ρ, W, hμ, hρ, hi, ?_, hqpos, hqle, he1, ?_, ?_⟩
  · exact hj
  · simpa only [CHFubini.choquetIntegral_indicator] using hf
  · simpa only [CHFubini.choquetIntegral_indicator] using hg

#print axioms independent_source_main
