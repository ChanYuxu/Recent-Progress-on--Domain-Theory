import ZFCFubini.SourceSections
import ZFCFubini.MainStatement

/-! The actual source witness and the two strict-level-set computations.
No Fubini theorem is invoked in either computation. -/

set_option autoImplicit false
open Set TopologicalSpace MeasureTheory Topology
open scoped ENNReal
namespace ZFCFubini
open FilterDcpo

theorem source_phi_isRealLSC :
    IsRealLSC (fun H : WithScott SourceQ => realMass sourceNuProbability (WithScott.ofScott H)) :=
  scott_isRealLSC (realMass_scottContinuous sourceNuProbability)

theorem source_f_isRealLSC :
    IsRealLSC (fun p : WithScott SourceP => sourceFReal (WithScott.ofScott p)) :=
  scott_isRealLSC sourceFReal_scottContinuous

theorem source_phi_level_mass (a : ℝ) (_ha0 : 0 ≤ a) :
    realMass sourceEtaProbability
      ⟨{H : WithScott SourceQ | a < realMass sourceNuProbability (WithScott.ofScott H)},
        source_phi_isRealLSC a⟩ = if a < 1 then 1 else 0 := by
  classical
  let A : ScottOpens SourceQ :=
    ⟨{H | a < realMass sourceNuProbability (WithScott.ofScott H)}, source_phi_isRealLSC a⟩
  change realMass sourceEtaProbability A = _
  by_cases ha : a < 1
  · have hψ : sourcePsi A = ⊤ := by
      apply Opens.ext
      ext t
      rw [sourcePsi_literal]
      simp only [mem_iInter, mem_setOf_eq, Opens.coe_top, mem_univ, iff_true]
      intro M
      change a < realMass sourceNuProbability (sourceG M t)
      simpa only [sourceG_realMass_nu_one] using ha
    change (sourceEtaValuation A).toReal = _
    rw [sourceEta_apply, hψ, Opens.coe_top, measure_univ, ENNReal.toReal_one, if_pos ha]
  · have hA : A = ⊥ := by
      apply Opens.ext
      ext H
      change (a < realMass sourceNuProbability (WithScott.ofScott H)) ↔ False
      exact iff_false_intro (not_lt_of_ge ((realMass_mem_unit sourceNuProbability
        (WithScott.ofScott H)).2.trans (le_of_not_gt ha)))
    rw [hA, realMass_empty, if_neg ha]

theorem source_f_level_mass (a : ℝ) (_ha0 : 0 ≤ a) :
    realMass sourceNuProbability
      ⟨{p : WithScott SourceP | a < sourceFReal (WithScott.ofScott p)}, source_f_isRealLSC a⟩ =
      if a < q then 1 else 0 := by
  classical
  let A : ScottOpens SourceP :=
    ⟨{p | a < sourceFReal (WithScott.ofScott p)}, source_f_isRealLSC a⟩
  have htr : trace A = if a < q then Set.univ else ∅ := by
    ext y
    change (a < sourceFReal (e circleModel y)) ↔ _
    rw [sourceFReal_maximal]
    by_cases ha : a < q <;> simp only [ha, if_true, if_false, mem_univ, mem_empty_iff_false]
  change (sourceNu A).toReal = _
  rw [sourceNu_apply, htr]
  by_cases ha : a < q <;> simp only [ha, if_true, if_false, measure_univ, measure_empty,
    ENNReal.toReal_one, ENNReal.toReal_zero]

theorem source_first_integral :
    paperIntegral sourceEtaProbability
      (fun H : WithScott SourceQ => realMass sourceNuProbability (WithScott.ofScott H)) = 1 :=
  paperIntegral_eq_of_unit_superlevels sourceEtaProbability _ source_phi_isRealLSC
    1 (by norm_num) le_rfl source_phi_level_mass

theorem source_second_integral :
    paperIntegral sourceNuProbability
      (fun p : WithScott SourceP => sourceFReal (WithScott.ofScott p)) = q :=
  paperIntegral_eq_of_unit_superlevels sourceNuProbability _ source_f_isRealLSC
    q q_bounds.1.le (by linarith [q_bounds.2]) source_f_level_mass

theorem source_first_iterated_integral :
    paperIntegral sourceEtaProbability (fun H => paperIntegral sourceNuProbability
      (fun p => (incidence SourceP (WithScott.ofScott p, WithScott.ofScott H)).val)) = 1 := by
  simp_rw [source_section_inner_nu]
  exact source_first_integral

theorem source_second_iterated_integral :
    paperIntegral sourceNuProbability (fun p => paperIntegral sourceEtaProbability
      (fun H => (incidence SourceP (WithScott.ofScott p, WithScott.ofScott H)).val)) = q := by
  simp_rw [source_section_inner_eta]
  exact source_second_integral

/-- Source `thm:main`, without extra premises. Q is the full complete lattice
of Scott opens of the actual source P, and w is the specified incidence. -/
theorem main_theorem : MainStatement := by
  refine ⟨SourceP, inferInstance, sourceP_isDcpo, sourceNuProbability,
    sourceEtaProbability, incidence_scottContinuous SourceP, source_first_iterated_integral,
    ?_, ?_, ?_, realMass_scottContinuous sourceNuProbability,
    sourceEta_evaluation_scottContinuous⟩
  · simpa only [← q_source, sourceQ] using source_second_iterated_integral
  · simpa only [sourceQ, ← q_source] using q_bounds.1
  · simpa only [sourceQ, ← q_source] using q_bounds.2

end ZFCFubini
