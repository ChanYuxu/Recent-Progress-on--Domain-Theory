import CHFubini.Foundations
import Mathlib.MeasureTheory.Measure.Regular

/-! Source Lemma 2.1 and the actual ambient Radon-to-valuation bridge.
This is NOT an inner-regularity assumption about the refined source measure.
The directed-cover proof is adapted from the independent project's
`PointCentralFubini/CompactOrderedMeasure.lean`, without its AJK axiom.
-/

set_option autoImplicit false
open Set Topology TopologicalSpace MeasureTheory
open scoped ENNReal
universe u v
namespace CHFubini

theorem measureMass_scottContinuous {X : Type u}
    [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    (μ : Measure X) [Measure.InnerRegular μ] :
    ScottContinuous (fun U : Opens X => μ (U : Set X)) := by
  intro A hn hd p hp
  constructor
  · rintro z ⟨U,hU,rfl⟩
    exact measure_mono (hp.1 hU)
  · intro z hz
    change μ (p : Set X) ≤ z
    rw [p.isOpen.measurableSet.measure_eq_iSup_isCompact μ]
    apply iSup_le; intro K
    apply iSup_le; intro hKp
    apply iSup_le; intro hK
    letI : Nonempty A := hn.to_subtype
    let V : A → Set X := fun U => U.val
    have hdir : Directed (· ⊆ ·) V := by
      intro U W
      obtain ⟨Z,hZ,hUZ,hWZ⟩ := hd U.val U.property W.val W.property
      exact ⟨⟨Z,hZ⟩,hUZ,hWZ⟩
    have hcover : K ⊆ ⋃ U : A, V U := by
      intro x hx
      have hxp := hKp hx
      rw [hp.unique (isLUB_sSup A)] at hxp
      obtain ⟨U,hU,hxU⟩ := Opens.mem_sSup.mp hxp
      exact mem_iUnion.mpr ⟨⟨U,hU⟩,hxU⟩
    obtain ⟨U,hKU⟩ := hK.elim_directed_cover V (fun U => U.val.isOpen) hcover hdir
    exact (measure_mono hKU).trans (hz (mem_image_of_mem _ U.property))

def radonValuation {X : Type u}
    [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    (μ : Measure X) [Measure.InnerRegular μ] : Valuation X where
  mass U := μ (U : Set X)
  strict := measure_empty
  modular U V := (measure_union_add_inter (U : Set X) V.isOpen.measurableSet).symm
  continuous := measureMass_scottContinuous μ

@[simp] theorem radonValuation_apply {X : Type u}
    [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    (μ : Measure X) [Measure.InnerRegular μ] (U : Opens X) :
    radonValuation μ U = μ (U : Set X) := rfl

theorem radonValuation_probability {X : Type u}
    [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    (μ : Measure X) [Measure.InnerRegular μ] [IsProbabilityMeasure μ] :
    (radonValuation μ).Probability := measure_univ

/-- Source Lemma 2.1, finite-subunion formula for arbitrary indexed opens.
Finiteness and Hausdorffness are retained to expose the printed interface,
although the inner-regular proof gives the same equality more generally. -/
theorem finite_subunion_formula {X : Type u} {I : Type v}
    [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [OpensMeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] [Measure.InnerRegular μ]
    (G : I → Set X) (hG : ∀ i, IsOpen (G i)) :
    μ (⋃ i, G i) = ⨆ F : Finset I, μ (⋃ i ∈ F, G i) := by
  classical
  let O : I → Opens X := fun i => ⟨G i,hG i⟩
  let F : Finset I → Opens X := fun s => s.sup O
  have hF : Monotone F := fun s t hst => Finset.sup_mono hst
  have hsup : (⨆ s, F s) = ⨆ i, O i := by
    simp only [F,Finset.sup_eq_iSup,← iSup_eq_iSup_finset]
  have he := (radonValuation μ).map_iSup F hF.directed_le
  rw [hsup] at he
  simpa only [radonValuation_apply, Opens.coe_iSup, O,F,Finset.sup_eq_iSup] using he

/-- The directed form of the same source lemma uses no countable cofinality. -/
theorem directed_open_measure {X : Type u} {I : Type v} [Nonempty I]
    [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [OpensMeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] [Measure.InnerRegular μ]
    (G : I → Opens X) (hG : Directed (· ≤ ·) G) :
    μ ((⨆ i, G i : Opens X) : Set X) = ⨆ i, μ (G i : Set X) :=
  (radonValuation μ).map_iSup G hG

end CHFubini
