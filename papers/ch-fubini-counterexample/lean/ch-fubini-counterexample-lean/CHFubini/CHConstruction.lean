import CHFubini.OrdinalStages
import CHFubini.BorelCardinality
import CHFubini.Foundations
import Mathlib.MeasureTheory.Group.AddCircle
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.Typeclasses.NoAtoms

/-!
Candidate for the manuscript's genuine CH source construction, lines 287-334.
The stagewise choice lemma is proved from nullity and countability. It is not
an assumed existence field. The final wrapper instantiates CH-enumerated real
Borel-null and positive-compact families with the actual unit-circle volume.
-/

set_option autoImplicit false

open Set TopologicalSpace MeasureTheory Cardinal
open scoped Cardinal Ordinal ENNReal

namespace CHFubini

universe u

/-- A positive set still has a point after removing any null set. No
measurability of the removed set is needed for this outer-measure fact. -/
theorem exists_mem_diff_of_pos_of_null
    {X : Type u} [MeasurableSpace X] (μ : Measure X)
    {K B : Set X} (hK : 0 < μ K) (hB : μ B = 0) :
    (K \ B).Nonempty := by
  apply nonempty_of_measure_ne_zero
  rw [measure_diff_null hB]
  exact hK.ne'

section Selection

variable {X : Type u} [MeasurableSpace X] (μ : Measure X) [hAtom : NoAtoms μ]
    (N K : CHFubini.OmegaOneStage → Set X)
    (hN : ∀ ξ, μ (N ξ) = 0) (hK : ∀ ξ, 0 < μ (K ξ))

include hN hK hAtom in
/-- The actual feasibility proof at one recursion stage. All earlier null
sets and all previously selected points form a countable null obstruction. -/
theorem exists_fresh_point
    (γ : CHFubini.OmegaOneStage)
    (previous : ∀ ξ : CHFubini.OmegaOneStage, ξ < γ → X) :
    ∃ x : X, x ∈ K γ ∧ (∀ ξ, ξ ≤ γ → x ∉ N ξ) ∧
      ∀ ξ (hξ : ξ < γ), x ≠ previous ξ hξ := by
  classical
  letI : Countable (Iic γ) := (omegaOneStage_Iic_countable γ).to_subtype
  letI : Countable (Iio γ) := (omegaOneStage_Iio_countable γ).to_subtype
  let U : Set X := ⋃ ξ : Iic γ, N ξ.1
  let previousRange : Set X := range (fun ξ : Iio γ => previous ξ.1 ξ.2)
  have hU : μ U = 0 := measure_iUnion_null (fun ξ : Iic γ => hN ξ.1)
  have hR : μ previousRange = 0 := (countable_range _).measure_zero μ
  obtain ⟨x, hxK, hxB⟩ := exists_mem_diff_of_pos_of_null μ (hK γ)
    (measure_union_null hU hR)
  refine ⟨x, hxK, ?_, ?_⟩
  · intro ξ hξ hxN
    exact hxB (Or.inl (mem_iUnion.mpr ⟨⟨ξ, hξ⟩, hxN⟩))
  · intro ξ hξ heq
    apply hxB
    exact Or.inr ⟨⟨ξ, hξ⟩, heq.symm⟩

/-- The recursively selected point, using well-founded recursion on the
literal countable-ordinal stage order. -/
noncomputable def selectedPoint : CHFubini.OmegaOneStage → X :=
  wellFounded_lt.fix (fun γ previous =>
    Classical.choose (exists_fresh_point μ N K hN hK γ previous))

theorem selectedPoint_spec (γ : CHFubini.OmegaOneStage) :
    selectedPoint μ N K hN hK γ ∈ K γ ∧
      (∀ ξ, ξ ≤ γ → selectedPoint μ N K hN hK γ ∉ N ξ) ∧
      ∀ ξ, ξ < γ → selectedPoint μ N K hN hK γ ≠
        selectedPoint μ N K hN hK ξ := by
  unfold selectedPoint
  rw [WellFounded.fix_eq]
  exact Classical.choose_spec (exists_fresh_point μ N K hN hK γ _)

theorem selectedPoint_injective :
    Function.Injective (selectedPoint μ N K hN hK) := by
  intro ξ η h
  rcases lt_trichotomy ξ η with hξη | hξη | hηξ
  · exact False.elim ((selectedPoint_spec μ N K hN hK η).2.2 ξ hξη h.symm)
  · exact hξη
  · exact False.elim ((selectedPoint_spec μ N K hN hK ξ).2.2 η hηξ h)

end Selection

/-- The exact initial point segment of a selection sequence. -/
def initialSegment {X : Type u} (a : CHFubini.OmegaOneStage → X)
    (β : CHFubini.OmegaOneStage) : Set X := a '' Iio β

theorem initialSegment_countable {X : Type u}
    (a : CHFubini.OmegaOneStage → X) (β : CHFubini.OmegaOneStage) :
    (initialSegment a β).Countable :=
  (omegaOneStage_Iio_countable β).image a

section Properties

variable {X : Type u} [MeasurableSpace X]
    (μ : Measure X) [NoAtoms μ]
    (N K : CHFubini.OmegaOneStage → Set X)
    (hN : ∀ ξ, μ (N ξ) = 0) (hK : ∀ ξ, 0 < μ (K ξ))
    (hNsurj : ∀ B, MeasurableSet B → μ B = 0 → ∃ ξ, N ξ = B)

include hNsurj in
/-- Source A-properties (i), including the actual initial-segment bound. -/
theorem selectedPoint_null_trace
    {B : Set X} (hB : MeasurableSet B) (hB0 : μ B = 0) :
    ∃ β : CHFubini.OmegaOneStage,
      range (selectedPoint μ N K hN hK) ∩ B ⊆
        initialSegment (selectedPoint μ N K hN hK) β ∧
      (range (selectedPoint μ N K hN hK) ∩ B).Countable := by
  obtain ⟨β, hβ⟩ := hNsurj B hB hB0
  have hsub : range (selectedPoint μ N K hN hK) ∩ B ⊆
      initialSegment (selectedPoint μ N K hN hK) β := by
    rintro x ⟨⟨γ, rfl⟩, hxB⟩
    refine ⟨γ, ?_, rfl⟩
    by_contra hγ
    exact (selectedPoint_spec μ N K hN hK γ).2.1 β
      (not_lt.mp hγ) (by simpa only [hβ] using hxB)
  exact ⟨β, hsub, (initialSegment_countable _ β).mono hsub⟩

variable [TopologicalSpace X]
    (hKsurj : ∀ C, IsCompact C → 0 < μ C → ∃ ξ, K ξ = C)

include hKsurj in
/-- Source A-properties (ii): every genuinely positive compact is hit by the
point chosen at its own enumeration stage. -/
theorem selectedPoint_hits_compact
    {C : Set X} (hC : IsCompact C) (hCpos : 0 < μ C) :
    (range (selectedPoint μ N K hN hK) ∩ C).Nonempty := by
  obtain ⟨γ, hγ⟩ := hKsurj C hC hCpos
  refine ⟨selectedPoint μ N K hN hK γ, mem_range_self γ, ?_⟩
  simpa only [hγ] using (selectedPoint_spec μ N K hN hK γ).1

variable [Measure.InnerRegular μ]

include hKsurj in
/-- The compact-hitting property implies that every measurable set disjoint
from the selected range is null; inner regularity is used exactly here. -/
theorem selectedPoint_disjoint_measurable_null
    {E : Set X} (hE : MeasurableSet E)
    (hdisj : Disjoint E (range (selectedPoint μ N K hN hK))) :
    μ E = 0 := by
  by_contra hE0
  obtain ⟨C, hCE, hC, hCpos⟩ := hE.exists_lt_isCompact (pos_iff_ne_zero.mpr hE0)
  obtain ⟨x, hxA, hxC⟩ := selectedPoint_hits_compact μ N K hN hK hKsurj hC hCpos
  exact Set.disjoint_left.mp hdisj (hCE hxC) hxA

variable [MeasurableSingletonClass X]

include hKsurj in
/-- Source A-properties (iii): the trace being countable forces the entire
measurable ambient set to be null. -/
theorem selectedPoint_countable_trace_null
    {E : Set X} (hE : MeasurableSet E)
    (htrace : (range (selectedPoint μ N K hN hK) ∩ E).Countable) :
    μ E = 0 := by
  let C := range (selectedPoint μ N K hN hK) ∩ E
  have hCmeas : MeasurableSet C := htrace.measurableSet
  have hC0 : μ C = 0 := htrace.measure_zero μ
  have hdiff : μ (E \ C) = 0 := by
    apply selectedPoint_disjoint_measurable_null μ N K hN hK hKsurj
      (hE.diff hCmeas)
    apply Set.disjoint_left.mpr
    intro x hx hxA
    exact hx.2 ⟨hxA, hx.1⟩
  rwa [measure_diff_null hC0] at hdiff

end Properties

section CHApplication

variable {X : Type} [mX : MeasurableSpace X] [TopologicalSpace X]
    [SecondCountableTopology X] [T2Space X] [BorelSpace X]
    (μ : Measure X) [NoAtoms μ] [Measure.InnerRegular μ]

/-- Actual CH construction in a second-countable Hausdorff Borel measure
space. Nonatomicity and inner regularity are proved separately for the circle
in the concrete wrapper below. A positive compact is the only nontriviality
witness; no stage-feasibility or target A-property is assumed. -/
theorem exists_CH_selection
    (hCH : CHFubini.CH) (hne : ∃ C : Set X, IsCompact C ∧ 0 < μ C) :
    ∃ (N K : CHFubini.OmegaOneStage → Set X)
      (a : CHFubini.OmegaOneStage → X),
      (∀ β, MeasurableSet (N β) ∧ μ (N β) = 0) ∧
      (∀ B, MeasurableSet B → μ B = 0 → ∃ β, N β = B) ∧
      (∀ β, IsCompact (K β) ∧ 0 < μ (K β)) ∧
      (∀ C, IsCompact C → 0 < μ C → ∃ β, K β = C) ∧
      Function.Injective a ∧
      (∀ γ, a γ ∈ K γ ∧ (∀ ξ, ξ ≤ γ → a γ ∉ N ξ) ∧
        ∀ ξ, ξ < γ → a γ ≠ a ξ) ∧
      (∀ B, MeasurableSet B → μ B = 0 → ∃ β,
        range a ∩ B ⊆ initialSegment a β ∧ (range a ∩ B).Countable) ∧
      (∀ C, IsCompact C → 0 < μ C → (range a ∩ C).Nonempty) ∧
      (∀ E, MeasurableSet E → (range a ∩ E).Countable → μ E = 0) := by
  classical
  obtain ⟨N, hN, hNsurj⟩ := CHFubini.exists_borelFamily_enumeration hCH
    (fun B : Set X => MeasurableSet B ∧ μ B = 0)
    (fun B hB => by rw [← BorelSpace.measurable_eq]; exact hB.1)
    ⟨∅, MeasurableSet.empty, measure_empty⟩
  obtain ⟨K, hK, hKsurj⟩ := CHFubini.exists_borelFamily_enumeration hCH
    (fun C : Set X => IsCompact C ∧ 0 < μ C)
    (fun C hC => by
      rw [← BorelSpace.measurable_eq]
      exact hC.1.isClosed.measurableSet) hne
  let nnull : ∀ β, μ (N β) = 0 := fun β => (hN β).2
  let kpos : ∀ β, 0 < μ (K β) := fun β => (hK β).2
  let a := selectedPoint μ N K nnull kpos
  have hncover : ∀ B, MeasurableSet B → μ B = 0 → ∃ β, N β = B :=
    fun B hB hB0 => hNsurj B ⟨hB, hB0⟩
  have hkcover : ∀ C, IsCompact C → 0 < μ C → ∃ β, K β = C :=
    fun C hC hCpos => hKsurj C ⟨hC, hCpos⟩
  exact ⟨N, K, a, hN, hncover, hK, hkcover,
    selectedPoint_injective μ N K nnull kpos,
    selectedPoint_spec μ N K nnull kpos,
    fun B hB hB0 => selectedPoint_null_trace μ N K nnull kpos hncover hB hB0,
    fun C hC hCpos => selectedPoint_hits_compact μ N K nnull kpos hkcover hC hCpos,
    fun E hE ht => selectedPoint_countable_trace_null μ N K nnull kpos hkcover hE ht⟩

end CHApplication

/-- Actual circle instances, not abstract hypotheses about an unspecified
probability source. -/
theorem unitCircle_volume_noAtoms : NoAtoms (volume : Measure UnitAddCircle) := by
  refine ⟨fun x => ?_⟩
  simpa using (AddCircle.volume_closedBall (T := 1) (x := x) (0 : ℝ))

theorem unitCircle_volume_innerRegular :
    Measure.InnerRegular (volume : Measure UnitAddCircle) := by
  infer_instance

/-- CH implies the genuine source sequence on the circle, including the
exact recursive avoidance condition and all three source A-properties. -/
theorem exists_CH_circle_selection (hCH : CHFubini.CH) :
    ∃ (N K : CHFubini.OmegaOneStage → Set UnitAddCircle)
      (a : CHFubini.OmegaOneStage → UnitAddCircle),
      (∀ β, MeasurableSet (N β) ∧ volume (N β) = 0) ∧
      (∀ B, MeasurableSet B → volume B = 0 → ∃ β, N β = B) ∧
      (∀ β, IsCompact (K β) ∧ 0 < volume (K β)) ∧
      (∀ C, IsCompact C → 0 < volume C → ∃ β, K β = C) ∧
      Function.Injective a ∧
      (∀ γ, a γ ∈ K γ ∧ (∀ ξ, ξ ≤ γ → a γ ∉ N ξ) ∧
        ∀ ξ, ξ < γ → a γ ≠ a ξ) ∧
      (∀ B, MeasurableSet B → volume B = 0 → ∃ β,
        range a ∩ B ⊆ initialSegment a β ∧ (range a ∩ B).Countable) ∧
      (∀ C, IsCompact C → 0 < volume C → (range a ∩ C).Nonempty) ∧
      (∀ E, MeasurableSet E → (range a ∩ E).Countable → volume E = 0) := by
  letI := unitCircle_volume_noAtoms
  letI := unitCircle_volume_innerRegular
  apply exists_CH_selection (volume : Measure UnitAddCircle) hCH
  exact ⟨univ, isCompact_univ, by simp only [UnitAddCircle.measure_univ, zero_lt_one]⟩

/-- A source-facing sequence-only wrapper for the tail topology construction.
The enumeration and well-founded recursion are consumed through the theorem
above, rather than replaced by an abstract existence assumption. -/
theorem exists_CH_circle_points (hCH : CHFubini.CH) :
    ∃ a : CHFubini.OmegaOneStage → UnitAddCircle,
      Function.Injective a ∧
      (∀ B, MeasurableSet B → volume B = 0 → ∃ β,
        range a ∩ B ⊆ initialSegment a β ∧ (range a ∩ B).Countable) ∧
      (∀ C, IsCompact C → 0 < volume C → (range a ∩ C).Nonempty) ∧
      (∀ E, MeasurableSet E → (range a ∩ E).Countable → volume E = 0) := by
  obtain ⟨N, K, a, _, _, _, _, ha, _, hnull, hcompact, htrace⟩ :=
    exists_CH_circle_selection hCH
  exact ⟨a, ha, hnull, hcompact, htrace⟩

end CHFubini

-- Candidate-only actual axiom evidence; these commands add no assumptions.
#print axioms CHFubini.omegaOneStage_Iio_countable
#print axioms CHFubini.omegaOneStage_Iic_countable
#print axioms CHFubini.omegaOneStage_countable_strict_bound
#print axioms CHFubini.exists_mem_diff_of_pos_of_null
#print axioms CHFubini.exists_fresh_point
#print axioms CHFubini.selectedPoint
#print axioms CHFubini.selectedPoint_spec
#print axioms CHFubini.selectedPoint_injective
#print axioms CHFubini.initialSegment
#print axioms CHFubini.initialSegment_countable
#print axioms CHFubini.selectedPoint_null_trace
#print axioms CHFubini.selectedPoint_hits_compact
#print axioms CHFubini.selectedPoint_disjoint_measurable_null
#print axioms CHFubini.selectedPoint_countable_trace_null
#print axioms CHFubini.exists_CH_selection
#print axioms CHFubini.unitCircle_volume_noAtoms
#print axioms CHFubini.unitCircle_volume_innerRegular
#print axioms CHFubini.exists_CH_circle_selection
#print axioms CHFubini.exists_CH_circle_points

