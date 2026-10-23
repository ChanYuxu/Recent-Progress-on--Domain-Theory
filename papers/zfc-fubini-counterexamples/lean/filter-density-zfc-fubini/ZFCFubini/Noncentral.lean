import ZFCFubini.NNIntegralCalculations
import ZFCFubini.MainTheorem

/-!
Source `cor:noncentral`, its valuation-existence assertion: the ACTUAL source
nu and eta are noncentral under Foundations.Central, witnessed by the SAME
incidence function and the proved real/nonnegative integral encoding bridge.
No predicate named Central or Commute is replaced or redefined here.

Scope of this file: analytical noncentrality only. The actual categorical
monad/strength and its noncommutativity are supplied separately by
`CategoricalNoncommutativity`; positive centrality of every actual eta_M is
supplied by `StageCentrality`, with the full final remark in `StageConclusions`.
Those conclusions are not claimed to follow by renaming a scalar predicate.
This implementation is new; no older CH proof file is imported or reused.
-/

set_option autoImplicit false
open Set TopologicalSpace MeasureTheory Topology
open scoped ENNReal
universe u v

namespace ZFCFubini

/-- Symmetry is proved by the transposed integrand on the order product, as
in the source proof for eta; no ordinary product topology is used. -/
theorem commute_symm {P : Type u} {Q : Type v} [PartialOrder P] [PartialOrder Q]
    {μ : DValuation P} {ν : DValuation Q} (h : Commute μ ν) : Commute ν μ := by
  intro w hw hbound
  have hswap : ScottContinuous (fun z : P × Q => (z.2, z.1)) :=
    ScottContinuous.snd.prodMk ScottContinuous.fst
  have he := h (fun z => w (z.2, z.1)) (hswap.comp hw) (fun z => hbound (z.2, z.1))
  exact he.symm

theorem source_nn_section_inner_nu (H : SourceQ) :
    choquetIntegral sourceNu
      (fun p : WithScott SourceP => nnIncidence SourceP (WithScott.ofScott p, H)) =
      ENNReal.ofReal (realMass sourceNuProbability H) := by
  unfold nnIncidence
  change choquetIntegral sourceNuProbability.val
    (fun p : WithScott SourceP => ENNReal.ofReal (incidence SourceP (WithScott.ofScott p, H)).val) = _
  rw [choquetIntegral_ofReal_eq_paperIntegral sourceNuProbability
    (fun p : WithScott SourceP => (incidence SourceP (WithScott.ofScott p, H)).val)
    (fun p => (incidence SourceP (WithScott.ofScott p, H)).property.2), source_section_inner_nu]

theorem source_nn_section_inner_eta (p : SourceP) :
    choquetIntegral sourceEtaValuation
      (fun H : WithScott SourceQ => nnIncidence SourceP (p, WithScott.ofScott H)) =
      ENNReal.ofReal (sourceFReal p) := by
  unfold nnIncidence
  change choquetIntegral sourceEtaProbability.val
    (fun H : WithScott SourceQ => ENNReal.ofReal (incidence SourceP (p, WithScott.ofScott H)).val) = _
  rw [choquetIntegral_ofReal_eq_paperIntegral sourceEtaProbability
    (fun H : WithScott SourceQ => (incidence SourceP (p, WithScott.ofScott H)).val)
    (fun H => (incidence SourceP (p, WithScott.ofScott H)).property.2), source_section_inner_eta]

theorem source_nn_phi_scottContinuous :
    ScottContinuous (fun H : SourceQ => ENNReal.ofReal (realMass sourceNuProbability H)) :=
  (realMass_scottContinuous sourceNuProbability).comp ofReal_scottContinuous

theorem source_nn_f_scottContinuous :
    ScottContinuous (fun p : SourceP => ENNReal.ofReal (sourceFReal p)) :=
  sourceFReal_scottContinuous.comp ofReal_scottContinuous

/-- The source's first strict-level computation in the actual nonnegative
Choquet encoding, obtained through a proved bridge, not a new Fubini theorem. -/
theorem source_first_nn_iterated_integral :
    choquetIntegral sourceEtaValuation (fun H : WithScott SourceQ =>
      choquetIntegral sourceNu (fun p : WithScott SourceP =>
        nnIncidence SourceP (WithScott.ofScott p, WithScott.ofScott H))) = 1 := by
  simp_rw [source_nn_section_inner_nu]
  change choquetIntegral sourceEtaProbability.val
    (fun H : WithScott SourceQ => ENNReal.ofReal (realMass sourceNuProbability (WithScott.ofScott H))) = _
  rw [choquetIntegral_ofReal_eq_paperIntegral sourceEtaProbability
    (fun H : WithScott SourceQ => realMass sourceNuProbability (WithScott.ofScott H))
    (fun H => (realMass_mem_unit sourceNuProbability (WithScott.ofScott H)).2),
    source_first_integral, ENNReal.ofReal_one]

/-- The source's second strict-level computation for the same incidence. -/
theorem source_second_nn_iterated_integral :
    choquetIntegral sourceNu (fun p : WithScott SourceP =>
      choquetIntegral sourceEtaValuation (fun H : WithScott SourceQ =>
        nnIncidence SourceP (WithScott.ofScott p, WithScott.ofScott H))) = ENNReal.ofReal q := by
  simp_rw [source_nn_section_inner_eta]
  change choquetIntegral sourceNuProbability.val
    (fun p : WithScott SourceP => ENNReal.ofReal (sourceFReal (WithScott.ofScott p))) = _
  rw [choquetIntegral_ofReal_eq_paperIntegral sourceNuProbability
    (fun p : WithScott SourceP => sourceFReal (WithScott.ofScott p))
    (fun p => (realMass_mem_unit parameterProbability (kernelEvent (WithScott.ofScott p))).2),
    source_second_integral]

theorem source_nu_eta_not_commute : ¬ Commute sourceNu sourceEtaValuation := by
  intro h
  have he := h (nnIncidence SourceP) (nnIncidence_scottContinuous SourceP)
    (nnIncidence_le_one SourceP)
  rw [source_second_nn_iterated_integral, source_first_nn_iterated_integral] at he
  have hq : q < 1 := q_bounds.2.trans_lt (by norm_num)
  have hqnn : ENNReal.ofReal q < 1 := by
    simpa only [ENNReal.ofReal_one] using
      (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 1)).mpr hq
  exact ne_of_lt hqnn he

theorem source_eta_nu_not_commute : ¬ Commute sourceEtaValuation sourceNu :=
  fun h => source_nu_eta_not_commute (commute_symm h)

/-- The actual nu is noncentral in the universe of the source's set-sized
dcpos; eta on the actual full Scott-open lattice is its counterexample. -/
theorem sourceNu_not_central : ¬ Central.{0, 0} sourceNu := by
  intro h
  exact source_nu_eta_not_commute
    (h.2 SourceQ (completeLattice_isDcpo SourceQ) sourceEtaValuation sourceEta_probability.subprobability)

/-- The actual eta is noncentral, using the transposed incidence and nu. -/
theorem sourceEta_not_central : ¬ Central.{0, 0} sourceEtaValuation := by
  intro h
  exact source_eta_nu_not_commute
    (h.2 SourceP sourceP_isDcpo sourceNu sourceNu_probability.subprobability)

theorem source_noncentral_pair :
    (¬ Central.{0, 0} sourceNu) ∧ (¬ Central.{0, 0} sourceEtaValuation) :=
  ⟨sourceNu_not_central, sourceEta_not_central⟩

/-- Source `cor:noncentral`, first sentence. The categorical second sentence
is proved by the actual monad/strength in `CategoricalNoncommutativity`. -/
theorem exists_noncentral_probability_valuation :
    ∃ (P : Type) (orderP : PartialOrder P),
      letI := orderP
      IsDcpo P ∧ ∃ μ : DValuation P, μ.Probability ∧ ¬ Central.{0, 0} μ := by
  exact ⟨SourceP, inferInstance, sourceP_isDcpo, sourceNu, sourceNu_probability, sourceNu_not_central⟩

end ZFCFubini
