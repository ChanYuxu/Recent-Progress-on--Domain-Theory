import ZFCFubini.IndexComparison
import ZFCFubini.PaperIntegral

/-! The specified ψ, η and η_M, not abstract existence certificates.
The comparison premise of the generic helper is discharged by
`sourceCarrierIndexComparison`, whose proof uses the actual filter model. -/

set_option autoImplicit false
open Set TopologicalSpace MeasureTheory Topology
open scoped ENNReal
namespace ZFCFubini

noncomputable def sourcePsi (A : ScottOpens SourceQ) : Opens Omega :=
  stabilizedEvent nullSet_countablyBounded sourceFamily sourceFamily_antitone
    sourceFamily_continuous A

theorem sourcePsi_literal (A : ScottOpens SourceQ) :
    (sourcePsi A : Set Omega) = ⋂ M : NullSet, {t | WithScott.toScott (sourceG M t) ∈ A} := rfl

theorem sourcePsi_stabilization (A : ScottOpens SourceQ) :
    ∃ M0 : NullSet, ∀ M, M0 ≤ M →
      {t | WithScott.toScott (sourceG M t) ∈ A} = (sourcePsi A : Set Omega) :=
  stabilizedEvent_eventually_eq nullSet_countablyBounded sourceFamily
    sourceFamily_antitone sourceFamily_continuous A

theorem sourcePsi_mono : Monotone sourcePsi :=
  stabilizedEvent_mono nullSet_countablyBounded sourceFamily sourceFamily_antitone
    sourceFamily_continuous

@[simp] theorem sourcePsi_bot : sourcePsi ⊥ = ⊥ :=
  stabilizedEvent_bot nullSet_countablyBounded sourceFamily sourceFamily_antitone
    sourceFamily_continuous

@[simp] theorem sourcePsi_top : sourcePsi ⊤ = ⊤ :=
  stabilizedEvent_top nullSet_countablyBounded sourceFamily sourceFamily_antitone
    sourceFamily_continuous

theorem sourcePsi_inf (A B : ScottOpens SourceQ) :
    sourcePsi (A ⊓ B) = sourcePsi A ⊓ sourcePsi B :=
  stabilizedEvent_inf nullSet_countablyBounded sourceFamily sourceFamily_antitone
    sourceFamily_continuous A B

theorem sourcePsi_sup (A B : ScottOpens SourceQ) :
    sourcePsi (A ⊔ B) = sourcePsi A ⊔ sourcePsi B :=
  stabilizedEvent_sup nullSet_countablyBounded sourceFamily sourceFamily_antitone
    sourceFamily_continuous A B

theorem sourcePsi_iSup {I : Type*} [Countable I] (A : I → ScottOpens SourceQ) :
    sourcePsi (⨆ i, A i) = ⨆ i, sourcePsi (A i) :=
  stabilizedEvent_iSup nullSet_countablyBounded sourceFamily sourceFamily_antitone
    sourceFamily_continuous A

/-- Source `prop:arbitrary-unions`, with arbitrary, not merely countable I. -/
theorem source_arbitrary_unions {I : Type*} (A : I → ScottOpens SourceQ) :
    parameterMeasure ((sourcePsi (⨆ i, A i) : Set Omega) \
      ⋃ i, (sourcePsi (A i) : Set Omega)) = 0 :=
  stabilizedEvent_arbitrary_union_defect_null nullSet_countablyBounded sourceFamily
    sourceFamily_antitone sourceFamily_continuous parameterMeasure sourceCarrierIndexComparison A

noncomputable def sourceEtaValuation : DValuation SourceQ :=
  stabilizedValuation nullSet_countablyBounded sourceFamily sourceFamily_antitone
    sourceFamily_continuous parameterMeasure sourceCarrierIndexComparison

@[simp] theorem sourceEta_apply (A : ScottOpens SourceQ) :
    sourceEtaValuation A = parameterMeasure (sourcePsi A : Set Omega) := rfl

/-- Source `thm:eta-continuous`: full Scott continuity is part of the actual
constructed Valuation, not an extra premise on the main theorem. -/
theorem sourceEta_probability : sourceEtaValuation.Probability :=
  stabilizedValuation_probability nullSet_countablyBounded sourceFamily sourceFamily_antitone
    sourceFamily_continuous parameterMeasure sourceCarrierIndexComparison

noncomputable def sourceNuProbability : ProbabilityValuation (WithScott SourceP) :=
  ⟨sourceNu, sourceNu_probability⟩

noncomputable def sourceEtaProbability : ProbabilityValuation (WithScott SourceQ) :=
  ⟨sourceEtaValuation, sourceEta_probability⟩

noncomputable def parameterProbability : ProbabilityValuation Omega :=
  ⟨radonValuation parameterMeasure, radonValuation_probability parameterMeasure⟩

noncomputable def sourceStageEta (M : NullSet) : DValuation SourceQ :=
  (radonValuation parameterMeasure).push (sourceFamily M) (sourceFamily_continuous M)

@[simp] theorem sourceStageEta_apply (M : NullSet) (A : ScottOpens SourceQ) :
    sourceStageEta M A = parameterMeasure {t | WithScott.toScott (sourceG M t) ∈ A} := rfl

theorem sourceStageEta_probability (M : NullSet) : (sourceStageEta M).Probability := by
  change parameterMeasure (Set.univ : Set Omega) = 1
  exact measure_univ

theorem sourceEta_le_stage (M : NullSet) (A : ScottOpens SourceQ) :
    sourceEtaValuation A ≤ sourceStageEta M A := by
  apply measure_mono
  intro t ht
  exact Set.mem_iInter.mp ht M

theorem sourceEta_iInf_stage (A : ScottOpens SourceQ) :
    sourceEtaValuation A = ⨅ M : NullSet, sourceStageEta M A := by
  apply le_antisymm
  · exact le_iInf (fun M => sourceEta_le_stage M A)
  · obtain ⟨M0, hM0⟩ := sourcePsi_stabilization A
    have he : sourceStageEta M0 A = sourceEtaValuation A :=
      congrArg parameterMeasure (hM0 M0 le_rfl)
    exact (iInf_le (fun M => sourceStageEta M A) M0).trans he.le

theorem sourceG_nu_one (M : NullSet) (t : Omega) : sourceNu (sourceG M t) = 1 := by
  rw [sourceNu_apply, sourceG_trace]
  apply le_antisymm prob_le_one
  have hcom : volume M.valᶜ = (1 : ℝ≥0∞) := by
    rw [prob_compl_eq_one_sub₀ M.property.1, M.property.2, tsub_zero]
  rw [← hcom]
  exact measure_mono Set.subset_union_right

@[simp] theorem sourceG_realMass_nu_one (M : NullSet) (t : Omega) :
    realMass sourceNuProbability (sourceG M t) = 1 := by
  change (sourceNu (sourceG M t)).toReal = 1
  rw [sourceG_nu_one, ENNReal.toReal_one]

end ZFCFubini
