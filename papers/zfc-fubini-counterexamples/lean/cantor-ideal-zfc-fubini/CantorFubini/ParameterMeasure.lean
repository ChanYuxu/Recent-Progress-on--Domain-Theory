/- Adapted from ZFC_Fubini_Lean/ZFCFubini/ParameterMeasure.lean; original SHA256 f2ed6421f4d13f47d48bd2737a34cf64fe8f6cc3ac0849c6f4383a808baa5136. Current source is formalized-manuscript.tex. -/
import CantorFubini.Foundations
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Probability.ProductMeasure
import Mathlib.Topology.MetricSpace.PiNat

/-!
Ordinary parameter measure and source Lemma `lem:radon`.
The first assertion is adapted from CHFubini/RadonValuation.lean, SHA256
dae3546a8dafab890e6845a7c58cdc5bb122bea195452172d66c72f16b5a2d65.
The positive-carrier proof below is new and follows the manuscript's printed
countable-base deletion, not the legacy everywherePosSubset proof.
-/

set_option autoImplicit false
open Set Topology TopologicalSpace MeasureTheory Filter
open scoped ENNReal Topology
universe u v

namespace CantorFubini

theorem measureMass_scottContinuous {X : Type u}
    [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    (μ : Measure X) [Measure.InnerRegular μ] :
    ScottContinuous (fun U : Opens X => μ (U : Set X)) := by
  intro A hn hd p hp
  constructor
  · rintro z ⟨U, hU, rfl⟩
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
      obtain ⟨Z, hZ, hUZ, hWZ⟩ := hd U.val U.property W.val W.property
      exact ⟨⟨Z, hZ⟩, hUZ, hWZ⟩
    have hcover : K ⊆ ⋃ U : A, V U := by
      intro x hx
      have hxp := hKp hx
      rw [hp.unique (isLUB_sSup A)] at hxp
      obtain ⟨U, hU, hxU⟩ := Opens.mem_sSup.mp hxp
      exact mem_iUnion.mpr ⟨⟨U, hU⟩, hxU⟩
    obtain ⟨U, hKU⟩ := hK.elim_directed_cover V (fun U => U.val.isOpen) hcover hdir
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

theorem finite_subunion_formula {X : Type u} {I : Type v}
    [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [OpensMeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] [Measure.InnerRegular μ]
    (G : I → Set X) (hG : ∀ i, IsOpen (G i)) :
    μ (⋃ i, G i) = ⨆ F : Finset I, μ (⋃ i ∈ F, G i) := by
  classical
  let O : I → Opens X := fun i => ⟨G i, hG i⟩
  let F : Finset I → Opens X := fun s => s.sup O
  have hF : Monotone F := fun _ _ hst => Finset.sup_mono hst
  have hsup : (⨆ s, F s) = ⨆ i, O i := by
    simp only [F, Finset.sup_eq_iSup, ← iSup_eq_iSup_finset]
  have he := (radonValuation μ).map_iSup F hF.directed_le
  rw [hsup] at he
  simpa only [radonValuation_apply, Opens.coe_iSup, O, F, Finset.sup_eq_iSup] using he

/-- Source Lemma `lem:radon` (i), with genuinely arbitrary directed families. -/
theorem directed_open_measure {X : Type u} {I : Type v} [Nonempty I]
    [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [OpensMeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] [Measure.InnerRegular μ]
    (G : I → Opens X) (hG : Directed (· ≤ ·) G) :
    μ ((⨆ i, G i : Opens X) : Set X) = ⨆ i, μ (G i : Set X) :=
  (radonValuation μ).map_iSup G hG

/-- Exact ambient-mass condition (5.1), including positive mass of `D` itself. -/
def PositiveCarrier {X : Type u} [TopologicalSpace X] [MeasurableSpace X]
    (μ : Measure X) (D : Set X) : Prop :=
  0 < μ D ∧ IsCompact D ∧
    ∀ W : Set D, IsOpen W → W.Nonempty → 0 < μ (Subtype.val '' W)

theorem PositiveCarrier.nonempty {X : Type u}
    [TopologicalSpace X] [MeasurableSpace X] {μ : Measure X} {D : Set X}
    (hD : PositiveCarrier μ D) : D.Nonempty :=
  nonempty_of_measure_ne_zero hD.1.ne'

/-- Source Lemma `lem:radon` (ii). First take positive compact `C`, then delete
exactly the ordinary basis neighborhoods whose intersection with `C` is null. -/
theorem positive_compact_carrier {X : Type u}
    [TopologicalSpace X] [T2Space X] [SecondCountableTopology X]
    [MeasurableSpace X] [OpensMeasurableSpace X]
    (μ : Measure X) [μ.InnerRegular] {E : Set X}
    (hE : MeasurableSet E) (hpos : 0 < μ E) :
    ∃ D : Set X, D ⊆ E ∧ PositiveCarrier μ D := by
  classical
  obtain ⟨C, hCE, hCc, hCpos⟩ := hE.exists_lt_isCompact hpos
  let B := countableBasis X
  let deleted : B → Set X := fun b => if μ (C ∩ b.1) = 0 then b.1 else ∅
  let V : Set X := ⋃ b : B, deleted b
  let D : Set X := C \ V
  have hVo : IsOpen V := by
    apply isOpen_iUnion
    intro b
    dsimp [deleted]
    split_ifs
    · exact isOpen_of_mem_countableBasis b.2
    · exact isOpen_empty
  have hCV0 : μ (C ∩ V) = 0 := by
    rw [inter_iUnion]
    apply measure_iUnion_null
    intro b
    dsimp [deleted]
    split_ifs with hb
    · exact hb
    · simp
  have hDae : D =ᵐ[μ] C := diff_ae_eq_self.mpr hCV0
  have hDpos : 0 < μ D := by rw [hDae.measure_eq]; exact hCpos
  have hDc : IsCompact D := hCc.diff hVo
  refine ⟨D, diff_subset.trans hCE, hDpos, hDc, ?_⟩
  intro W hWo hWn
  obtain ⟨O, hOo, hOW⟩ := isOpen_induced_iff.mp hWo
  obtain ⟨x, hxW⟩ := hWn
  have hxO : x.1 ∈ O := by rw [← hOW] at hxW; exact hxW
  obtain ⟨b, hb, hxb, hbO⟩ :=
    (isBasis_countableBasis X).exists_subset_of_mem_open hxO hOo
  have hCbpos : 0 < μ (C ∩ b) := by
    apply pos_iff_ne_zero.mpr
    intro hCb0
    have hxV : x.1 ∈ V := mem_iUnion.mpr ⟨⟨b, hb⟩, by simpa [deleted, hCb0] using hxb⟩
    exact x.2.2 hxV
  have hDb : μ (D ∩ b) = μ (C ∩ b) :=
    (hDae.inter (ae_eq_refl b)).measure_eq
  have hsub : D ∩ b ⊆ Subtype.val '' W := by
    rintro y ⟨hyD, hyb⟩
    refine ⟨⟨y, hyD⟩, ?_, rfl⟩
    rw [← hOW]
    exact hbO hyb
  exact hCbpos.trans_le (hDb ▸ measure_mono hsub)

/-- Source `lem:radon`, both printed assertions on an actual compact metric
space with finite Radon Borel measure. -/
theorem radon_compact_metric {X : Type u} [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X)
    [IsFiniteMeasure μ] [μ.InnerRegular] :
    (∀ {I : Type v} [Nonempty I] (V : I → Opens X), Directed (· ≤ ·) V →
      μ ((⨆ i, V i : Opens X) : Set X) = ⨆ i, μ (V i : Set X)) ∧
    (∀ E : Set X, MeasurableSet E → 0 < μ E →
      ∃ D : Set X, D ⊆ E ∧ PositiveCarrier μ D) := by
  exact ⟨fun V hV => directed_open_measure μ V hV,
    fun _ hE hpos => positive_compact_carrier μ hE hpos⟩

end CantorFubini
