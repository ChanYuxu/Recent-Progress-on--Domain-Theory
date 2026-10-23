import ZFCFubini.SourceValuation
import ZFCFubini.Evaluation
import ZFCFubini.PaperIntegralCalculations

/-! Source `lem:sections`: the exact kernel event is obtained by intersecting
all null-set stages, including the singleton of the actual label. Its Scott
continuity is proved by the printed directed event-union/Radon argument. -/

set_option autoImplicit false
open Set TopologicalSpace MeasureTheory Topology
open scoped ENNReal
namespace ZFCFubini
open FilterDcpo

def kernelEvent (p : SourceP) : Opens Omega :=
  ⟨{t | p.kernel ⊆ randomOpen t}, randomOpen_compact_containment_isOpen p.kernel_compact⟩

theorem kernelEvent_mono : Monotone kernelEvent := by
  intro p q hpq t ht
  exact (Point.kernel_antitone hpq).trans ht

theorem kernelEvent_scottContinuous : ScottContinuous kernelEvent := by
  intro A hn hd p hp
  refine ⟨?_, ?_⟩
  · rintro b ⟨a, haA, rfl⟩
    exact kernelEvent_mono (hp.1 haA)
  · intro B hB t ht
    have hpH : WithScott.toScott p ∈ H_ordinary circleModel (randomOpen t) :=
      (mem_H_ordinary_iff_kernel_subset circleModel (randomOpen t) p).mpr ht
    have hacc := ((scott_isOpen_iff {a : SourceP |
      WithScott.toScott a ∈ H_ordinary circleModel (randomOpen t)}).mp
        (H_ordinary circleModel (randomOpen t)).isOpen).2
    obtain ⟨a, haA, haH⟩ := hacc hn hd hp hpH
    exact hB (mem_image_of_mem _ haA)
      ((mem_H_ordinary_iff_kernel_subset circleModel (randomOpen t) a).mp haH)

noncomputable def sourceFReal (p : SourceP) : ℝ := realMass parameterProbability (kernelEvent p)

theorem sourceFReal_formula (p : SourceP) :
    sourceFReal p = (parameterMeasure {t | p.kernel ⊆ randomOpen t}).toReal := rfl

theorem sourceFReal_scottContinuous : ScottContinuous sourceFReal :=
  kernelEvent_scottContinuous.comp (realMass_scottContinuous parameterProbability)

noncomputable def sourceFUnit (p : SourceP) : UnitInterval :=
  realMassUnit parameterProbability (kernelEvent p)

theorem sourceFUnit_scottContinuous : ScottContinuous sourceFUnit :=
  kernelEvent_scottContinuous.comp (realMassUnit_scottContinuous parameterProbability)

theorem sourcePsi_evaluation (p : SourceP) : sourcePsi (evaluationOpen p) = kernelEvent p := by
  apply Opens.ext
  ext t
  rw [sourcePsi_literal]
  simp only [mem_iInter, mem_setOf_eq]
  constructor
  · intro ht
    have ht0 := ht (nullSingleton p.label)
    change WithScott.toScott p ∈ H_ordinary circleModel (randomOpen t) ⊔
      L circleModel (conullOpen (nullSingleton p.label)) at ht0
    rcases ht0 with hpH | hpL
    · exact (mem_H_ordinary_iff_kernel_subset circleModel (randomOpen t) p).mp hpH
    · have hK := kernel_subset_of_mem_L circleModel (conullOpen (nullSingleton p.label)) hpL
      exact False.elim (hK p.label_mem (Set.mem_singleton p.label))
  · intro ht M
    change WithScott.toScott p ∈ H_ordinary circleModel (randomOpen t) ⊔ L circleModel (conullOpen M)
    exact Or.inl ((mem_H_ordinary_iff_kernel_subset circleModel (randomOpen t) p).mpr ht)

theorem sourceEta_evaluation (p : SourceP) :
    sourceEtaValuation (evaluationOpen p) = parameterMeasure {t | p.kernel ⊆ randomOpen t} := by
  rw [sourceEta_apply, sourcePsi_evaluation]
  rfl

theorem sourceEta_evaluation_real (p : SourceP) :
    realMass sourceEtaProbability (evaluationOpen p) = sourceFReal p :=
  congrArg ENNReal.toReal (sourceEta_evaluation p)

theorem sourceEta_evaluation_scottContinuous :
    ScottContinuous (fun p : SourceP => realMass sourceEtaProbability (evaluationOpen p)) := by
  simpa only [sourceEta_evaluation_real] using sourceFReal_scottContinuous

theorem sourceFReal_maximal (y : Circle) : sourceFReal (e circleModel y) = q := by
  rw [sourceFReal_formula, kernel_e]
  have he : {t : Omega | ({y} : Set Circle) ⊆ randomOpen t} = pointHit y := by
    ext t; exact Set.singleton_subset_iff
  rw [he, pointHit_probability, ENNReal.toReal_ofReal q_bounds.1.le]

theorem source_section_inner_nu (H : SourceQ) :
    paperIntegral sourceNuProbability
      (fun p => (incidence SourceP (WithScott.ofScott p, H)).val) =
      realMass sourceNuProbability H := by
  have he : (fun p : WithScott SourceP => (incidence SourceP (WithScott.ofScott p, H)).val) =
      realIndicator H := by
    funext p
    simp only [incidence_value, realIndicator]
    rfl
  rw [he, paperIntegral_realIndicator]

theorem source_section_inner_eta (p : SourceP) :
    paperIntegral sourceEtaProbability
      (fun H => (incidence SourceP (p, WithScott.ofScott H)).val) = sourceFReal p := by
  have he : (fun H : WithScott SourceQ => (incidence SourceP (p, WithScott.ofScott H)).val) =
      realIndicator (evaluationOpen p) := by
    funext H
    simp only [incidence_value, realIndicator]
    rfl
  rw [he, paperIntegral_realIndicator, sourceEta_evaluation_real]

end ZFCFubini
