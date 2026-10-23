import CHFubini.MainTheorems

/-! Noncentrality is proved for the manuscript's actual Fubini definition.
This module does not rename a Fubini predicate as a categorical monad.
-/

set_option autoImplicit false
open Set Topology TopologicalSpace MeasureTheory
open scoped ENNReal
universe u v
namespace CHFubini

theorem Commute.symm {P : Type u} {Q : Type v} [PartialOrder P] [PartialOrder Q]
    {μ : DValuation P} {ν : DValuation Q} (h : Commute μ ν) : Commute ν μ := by
  intro f hf hb
  have hs := h (fun z : P × Q => f z.swap)
    ((ScottContinuous.snd.prodMk ScottContinuous.fst).comp hf) (fun z => hb z.swap)
  exact hs.symm

theorem not_commute_of_indicator_integrals
    {P : Type u} {Q : Type v} [PartialOrder P] [PartialOrder Q]
    (μ : DValuation P) (ν : DValuation Q) (W : ScottOpens (P × Q))
    {a b : ℝ≥0∞}
    (hleft : choquetIntegral ν
      (fun y => choquetIntegral μ (indicator (leftSection W (WithScott.ofScott y)))) = a)
    (hright : choquetIntegral μ
      (fun x => choquetIntegral ν (indicator (rightSection W (WithScott.ofScott x)))) = b)
    (hne : b ≠ a) : ¬ Commute μ ν := by
  intro h
  have he := h (orderIndicator W) (orderIndicator_scottContinuous W) (orderIndicator_bounded W)
  change choquetIntegral μ
      (fun x => choquetIntegral ν (indicator (rightSection W (WithScott.ofScott x)))) =
    choquetIntegral ν
      (fun y => choquetIntegral μ (indicator (leftSection W (WithScott.ofScott y)))) at he
  rw [hright,hleft] at he
  exact hne he

theorem noncentral_pair_of_indicator_integrals
    {P : Type u} {Q : Type v} [PartialOrder P] [PartialOrder Q]
    (hP : IsDcpo P) (hQ : IsDcpo Q)
    (μ : DValuation P) (ν : DValuation Q)
    (hμ : μ.Subprobability) (hν : ν.Subprobability) (W : ScottOpens (P × Q))
    {a b : ℝ≥0∞}
    (hleft : choquetIntegral ν
      (fun y => choquetIntegral μ (indicator (leftSection W (WithScott.ofScott y)))) = a)
    (hright : choquetIntegral μ
      (fun x => choquetIntegral ν (indicator (rightSection W (WithScott.ofScott x)))) = b)
    (hne : b ≠ a) : ¬ Central.{u,v} μ ∧ ¬ Central.{v,u} ν := by
  have hn := not_commute_of_indicator_integrals μ ν W hleft hright hne
  exact ⟨fun h => hn (h.2 Q hQ ν hν),fun h => hn (h.2 P hP μ hμ).symm⟩

/-- Corollary 6.4: under CH a first-countable sober Scott dcpo carries a
noncentral continuous probability valuation. Its arbitrary partner here is
already a genuine complete lattice. -/
theorem exists_firstCountable_sober_noncentral (hCH : CH) :
    ∃ (P : Type) (orderP : PartialOrder P),
      letI := orderP
      IsDcpo P ∧ FirstCountableTopology (WithScott P) ∧ IsSober (WithScott P) ∧
      IsWellFiltered (WithScott P) ∧
      ∃ μ : DValuation P, μ.Probability ∧ ¬ Central.{0,0} μ := by
  obtain ⟨P,orderP,L,latticeL,hP,hfirst,hsober,hwell,_,μ,ρ,W,hμ,hρ,
      hleft,hright,_,hqle,_,_,_⟩ := counterexampleAt_of_CH hCH (1/2) (by norm_num) (by norm_num)
  letI := orderP
  letI := latticeL
  have hq1 : ENNReal.ofReal (qEpsilon (1/2)) < 1 := by
    rw [ENNReal.ofReal_lt_one]
    exact hqle.trans_lt (by norm_num)
  have hn := noncentral_pair_of_indicator_integrals hP (completeLattice_isDcpo L)
    μ ρ hμ.subprobability hρ.subprobability W hleft hright (ne_of_lt hq1)
  exact ⟨P,orderP,hP,hfirst,hsober,hwell,μ,hμ,hn.1⟩

/-- The source also states that rho, on the complete-lattice factor, is
noncentral. No commutativity theorem is assumed to derive this. -/
theorem exists_completeLattice_noncentral (hCH : CH) :
    ∃ (L : Type) (latticeL : CompleteLattice L),
      letI := latticeL
      IsWellFiltered (WithScott L) ∧
      ∃ ρ : DValuation L, ρ.Probability ∧ ¬ Central.{0,0} ρ := by
  obtain ⟨P,orderP,L,latticeL,hP,_,_,_,hwell,μ,ρ,W,hμ,hρ,
      hleft,hright,_,hqle,_,_,_⟩ := counterexampleAt_of_CH hCH (1/2) (by norm_num) (by norm_num)
  letI := orderP
  letI := latticeL
  have hq1 : ENNReal.ofReal (qEpsilon (1/2)) < 1 := by
    rw [ENNReal.ofReal_lt_one]
    exact hqle.trans_lt (by norm_num)
  have hn := noncentral_pair_of_indicator_integrals hP (completeLattice_isDcpo L)
    μ ρ hμ.subprobability hρ.subprobability W hleft hright (ne_of_lt hq1)
  exact ⟨L,latticeL,hwell,ρ,hρ,hn.2⟩

end CHFubini

#print axioms CHFubini.exists_firstCountable_sober_noncentral
#print axioms CHFubini.exists_completeLattice_noncentral
