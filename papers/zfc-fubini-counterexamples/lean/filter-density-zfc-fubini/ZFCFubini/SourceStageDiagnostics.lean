import ZFCFubini.SourceSections

/-! Additional exact diagnostic identities for the specified stage family.
They do not stand in for the missing positive stage-centrality theorem.
In particular they independently rule out identifying the limit with one G_M
pushforward; no assumed centrality certificate is used in these identities. -/

set_option autoImplicit false
open Set TopologicalSpace MeasureTheory Topology
open scoped ENNReal
namespace ZFCFubini
open FilterDcpo

theorem sourceStageEta_maximal_conull (M : NullSet) (y : Circle) (hy : y ∉ M.val) :
    sourceStageEta M (evaluationOpen (e circleModel y)) = 1 := by
  rw [sourceStageEta_apply]
  have he : {t : Omega | WithScott.toScott (sourceG M t) ∈ evaluationOpen (e circleModel y)} =
      Set.univ := by
    ext t
    change (y ∈ trace (sourceG M t)) ↔ True
    rw [sourceG_trace]
    exact iff_true_intro (Or.inr hy)
  rw [he, measure_univ]

theorem sourceEta_maximal_evaluation (y : Circle) :
    sourceEtaValuation (evaluationOpen (e circleModel y)) = ENNReal.ofReal q := by
  rw [sourceEta_evaluation, kernel_e]
  have he : {t : Omega | ({y} : Set Circle) ⊆ randomOpen t} = pointHit y := by
    ext t
    exact Set.singleton_subset_iff
  rw [he, pointHit_probability]

/-- A diagnostic stronger than mere inequality of centrality predicates.
It is not used to bypass the original positive-centrality proof route. -/
theorem sourceEta_ne_stage (M : NullSet) : sourceEtaValuation ≠ sourceStageEta M := by
  have hcom : volume M.valᶜ = (1 : ℝ≥0∞) := by
    rw [prob_compl_eq_one_sub₀ M.property.1, M.property.2, tsub_zero]
  obtain ⟨y, hy⟩ := nonempty_of_measure_ne_zero (μ := (volume : Measure Circle))
    (s := M.valᶜ) (by rw [hcom]; exact one_ne_zero)
  intro he
  have hmass := congrArg (fun μ : DValuation SourceQ => μ (evaluationOpen (e circleModel y))) he
  change sourceEtaValuation (evaluationOpen (e circleModel y)) =
    sourceStageEta M (evaluationOpen (e circleModel y)) at hmass
  rw [sourceEta_maximal_evaluation, sourceStageEta_maximal_conull M y hy] at hmass
  have hq : ENNReal.ofReal q < 1 := by
    rw [ENNReal.ofReal_lt_one]
    exact q_bounds.2.trans_lt (by norm_num)
  exact ne_of_lt hq hmass

end ZFCFubini
