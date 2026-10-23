import CantorFubini.SourceModel
import CantorFubini.SecondValuation
import CantorFubini.Evaluation
import CantorFubini.PaperIntegralCalculations

/-! The actual construction and ordinary real strict-level-set integrals.
All source main-theorem inputs are constructed, with no mathematical premise. -/
set_option autoImplicit false
open Set Topology TopologicalSpace MeasureTheory
open scoped ENNReal
universe u v
namespace CantorFubini

abbrev P := IdealPoint cantorMeasure
abbrev Q := ScottOpens P

noncomputable def nuProbability : ProbabilityValuation (WithScott P) :=
  ⟨nu cantorMeasure, nu_probability cantorMeasure⟩
noncomputable def etaProbability : ProbabilityValuation (WithScott Q) := ⟨eta, eta_probability⟩

theorem P_isDcpo : IsDcpo P := IdealPoint.isDcpo cantorMeasure
theorem Q_isDcpo : IsDcpo Q := completeLattice_isDcpo Q

theorem evaluationOpen_scottContinuous {D : Type u} [PartialOrder D] :
    ScottContinuous (@evaluationOpen D _) := by
  intro S hn hd p hp
  constructor
  · rintro E ⟨d, hdS, rfl⟩ H hdH
    exact (IsScott.isUpperSet_of_isOpen (D := univ) (WithScott.ofScott H).isOpen)
      (hp.1 hdS) hdH
  · intro A hA H hpH
    have hacc := (scott_isOpen_iff
      (WithScott.toScott ⁻¹' ((WithScott.ofScott H : ScottOpens D) : Set (WithScott D)))).mp
      (WithScott.ofScott H).isOpen |>.2
    obtain ⟨d, hdS, hdH⟩ := hacc hn hd hp hpH
    exact hA (mem_image_of_mem _ hdS) hdH

theorem evaluationOpen_directed_sup {D : Type u} [PartialOrder D]
    {S : Set D} (hn : S.Nonempty) (hd : DirectedOn (· ≤ ·) S) {p : D}
    (hp : IsLUB S p) : evaluationOpen p = ⨆ d : S, evaluationOpen d.val :=
  (evaluationOpen_scottContinuous hn hd hp).unique (by
    simpa only [iSup_subtype, sSup_image] using isLUB_sSup (evaluationOpen '' S))

theorem paperPsi_evaluation (p : P) :
    (paperPsi (evaluationOpen p) : Set Omega) = {t | p.kernel ⊆ randomOpen t} := by
  ext t
  constructor
  · intro ht
    have h := (mem_paperPsi (evaluationOpen p) t).mp ht
    let M : NullIndex cantorMeasure := ⟨{p.label},
      cantorMeasure_countable (countable_singleton _)⟩
    have hp := h M
    change WithScott.toScott p ∈ B cantorMeasure (randomOpen t) ⊔
      A cantorMeasure M.val M.property at hp
    rcases hp with hp | hp
    · exact hp
    · have hd := (p.upper_bound hp).2
      exact False.elim (disjoint_left.mp hd (mem_singleton p.label) p.label_mem)
  · intro h
    apply (mem_paperPsi (evaluationOpen p) t).mpr
    intro M
    change WithScott.toScott p ∈ B cantorMeasure (randomOpen t) ⊔
      A cantorMeasure M.val M.property
    exact Or.inl h

theorem eta_evaluation (p : P) :
    eta (evaluationOpen p) = parameterProbability {t | p.kernel ⊆ randomOpen t} := by
  rw [eta_apply, paperPsi_evaluation]

noncomputable def sectionValue (p : P) : ℝ := realMass etaProbability (evaluationOpen p)
noncomputable def sectionValueUnit (p : P) : UnitInterval := realMassUnit etaProbability (evaluationOpen p)

theorem sectionValueUnit_scottContinuous : ScottContinuous sectionValueUnit :=
  evaluationOpen_scottContinuous.comp (realMassUnit_scottContinuous etaProbability)

theorem sectionValue_isRealLSC :
    IsRealLSC (fun p : WithScott P => sectionValue (WithScott.ofScott p)) :=
  unit_scott_isRealLSC sectionValueUnit_scottContinuous

theorem sectionValue_maximal (x : Cantor) : sectionValue (IdealPoint.e cantorMeasure x) = q := by
  unfold sectionValue realMass
  change (eta (evaluationOpen (IdealPoint.e cantorMeasure x))).toReal = q
  rw [eta_evaluation]
  have he : {t : Omega | (IdealPoint.e cantorMeasure x).kernel ⊆ randomOpen t} = pointHit x := by
    ext t; exact singleton_subset_iff
  rw [he, pointHit_probability, ENNReal.toReal_ofReal]
  exact (by linarith [q_bounds.1] : 0 ≤ q)

theorem nu_G_one (M : NullIndex cantorMeasure) (t : Omega) :
    nu cantorMeasure (WithScott.ofScott (G cantorMeasure randomOpen M t)) = 1 := by
  change nu cantorMeasure (B cantorMeasure (randomOpen t) ⊔ A cantorMeasure M.val M.property) = 1
  rw [nu_apply, trace_sup, trace_B, trace_A]
  have hm : cantorMeasure M.valᶜ = 1 := by
    have h := measure_add_measure_compl₀ (NullMeasurableSet.of_null M.property)
    simpa only [M.property, zero_add, measure_univ] using h
  apply le_antisymm
  · exact (measure_mono (subset_univ _)).trans_eq measure_univ
  · rw [← hm]
    exact measure_mono subset_union_right

theorem nuReal_isRealLSC :
    IsRealLSC (fun H : WithScott Q => realMass nuProbability (WithScott.ofScott H)) :=
  scott_isRealLSC (realMass_scottContinuous nuProbability)

theorem eta_nu_superlevel (a : ℝ) (ha : 0 ≤ a) :
    realMass etaProbability
      ⟨{H : WithScott Q | a < realMass nuProbability (WithScott.ofScott H)}, nuReal_isRealLSC a⟩ =
      if a < 1 then 1 else 0 := by
  classical
  let E : ScottOpens Q := ⟨{H | a < realMass nuProbability (WithScott.ofScott H)}, nuReal_isRealLSC a⟩
  change (eta E).toReal = if a < 1 then 1 else 0
  by_cases ha1 : a < 1
  · have hE : (paperPsi E : Set Omega) = univ := by
      apply eq_univ_of_forall
      intro t
      apply (mem_paperPsi E t).mpr
      intro M
      change a < (nu cantorMeasure (WithScott.ofScott (G cantorMeasure randomOpen M t))).toReal
      rw [nu_G_one, ENNReal.toReal_one]
      exact ha1
    rw [eta_apply, hE, measure_univ, ENNReal.toReal_one, if_pos ha1]
  · have hE : E = ⊥ := by
      ext H
      change (a < realMass nuProbability (WithScott.ofScott H)) ↔ False
      exact iff_false_intro (fun h => ha1 (h.trans_le (realMass_mem_unit nuProbability _).2))
    rw [hE, eta.strict, ENNReal.toReal_zero, if_neg ha1]

theorem first_integral_value :
    paperIntegral etaProbability
      (fun H : WithScott Q => realMass nuProbability (WithScott.ofScott H)) = 1 :=
  paperIntegral_eq_of_unit_superlevels etaProbability _ nuReal_isRealLSC 1 (by norm_num) le_rfl
    eta_nu_superlevel

theorem nu_section_superlevel (a : ℝ) (ha : 0 ≤ a) :
    realMass nuProbability
      ⟨{p : WithScott P | a < sectionValue (WithScott.ofScott p)}, sectionValue_isRealLSC a⟩ =
      if a < q then 1 else 0 := by
  classical
  let E : ScottOpens P := ⟨{p | a < sectionValue (WithScott.ofScott p)}, sectionValue_isRealLSC a⟩
  have htrace : trace E = if a < q then univ else ∅ := by
    ext x
    change (a < sectionValue (IdealPoint.e cantorMeasure x)) ↔ _
    rw [sectionValue_maximal]
    by_cases h : a < q <;> simp [h]
  change (nu cantorMeasure E).toReal = if a < q then 1 else 0
  rw [nu_apply, htrace]
  split_ifs <;> simp

theorem second_integral_value :
    paperIntegral nuProbability (fun p : WithScott P => sectionValue (WithScott.ofScott p)) = q :=
  paperIntegral_eq_of_unit_superlevels nuProbability _ sectionValue_isRealLSC q
    (by linarith [q_bounds.1]) (by linarith [q_bounds.2]) nu_section_superlevel

theorem incidence_inner_left (H : Q) :
    paperIntegral nuProbability
      (fun p : WithScott P => (incidence P (WithScott.ofScott p, H)).val) =
      realMass nuProbability H := by
  have he : (fun p : WithScott P => (incidence P (WithScott.ofScott p, H)).val) =
      realIndicator H := by
    funext p
    classical
    simp only [incidence_value, realIndicator]
    rfl
  rw [he, paperIntegral_realIndicator]

theorem incidence_inner_right (p : P) :
    paperIntegral etaProbability
      (fun H : WithScott Q => (incidence P (p, WithScott.ofScott H)).val) = sectionValue p := by
  have he : (fun H : WithScott Q => (incidence P (p, WithScott.ofScott H)).val) =
      realIndicator (evaluationOpen p) := by
    funext H
    classical
    simp only [incidence_value, realIndicator, evaluationOpen]
    rfl
  rw [he, paperIntegral_realIndicator]
  rfl

/-- Source Theorem 6.3 for the specified dcpos, valuations, and incidence map.
The interval has its order Scott topology through ScottContinuous. -/
theorem source_main :
    IsDcpo P ∧ IsDcpo Q ∧ (nu cantorMeasure).Probability ∧ eta.Probability ∧
    ScottContinuous (incidence P) ∧
    paperIntegral etaProbability (fun H : WithScott Q =>
      paperIntegral nuProbability (fun p : WithScott P =>
        (incidence P (WithScott.ofScott p, WithScott.ofScott H)).val)) = 1 ∧
    paperIntegral nuProbability (fun p : WithScott P =>
      paperIntegral etaProbability (fun H : WithScott Q =>
        (incidence P (WithScott.ofScott p, WithScott.ofScott H)).val)) = q ∧
    0 < q ∧ q ≤ 1 / 2 := by
  refine ⟨P_isDcpo, Q_isDcpo, nu_probability cantorMeasure, eta_probability,
    incidence_scottContinuous P, ?_, ?_, ?_, q_bounds.2⟩
  · simp_rw [incidence_inner_left]
    exact first_integral_value
  · simp_rw [incidence_inner_right]
    exact second_integral_value
  · linarith [q_bounds.1]

end CantorFubini
