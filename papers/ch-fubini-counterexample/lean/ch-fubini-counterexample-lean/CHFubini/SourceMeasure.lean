import CHFubini.SourceRepresentatives
import CHFubini.CHConstruction
import CHFubini.RadonValuation
import CHFubini.RandomOpenContinuity
import Mathlib.MeasureTheory.Measure.Typeclasses.NoAtoms
import Mathlib.Order.ScottContinuity.Complete

/-!
Candidate for source-measure and alpha-continuous on the actual generated
tail topology. The full-outer trace construction is adapted from
`PointCentralFubini_Lean/PointCentralFubini/OuterTrace.lean`, lines 10-109,
SHA-256 `1e21b179ca2f9b45b0d8d2c32c615a53fbae2feec0a6c54fff2603e479770ef8`.
The adaptation takes an arbitrary actual measure and a proved comap equality;
it does not import that project's TauMeasure structure or its extra laws.

The refined source measure has no Radon or inner-regularity hypothesis. Only
the ambient ordinary circle measure is inner regular.
-/

set_option autoImplicit false
open Set Topology TopologicalSpace MeasureTheory Function
open scoped ENNReal
universe u v

namespace CHFubini

section FullOuterTrace

variable {X : Type u} {Y : Type v} [mX : MeasurableSpace X] [mY : MeasurableSpace Y]

/-- Any measurable source set has an ambient representative when the source
sigma-algebra is exactly the pullback sigma-algebra. -/
private theorem comap_repr (f : Y → X) (hcomap : mY = mX.comap f)
    {S : Set Y} (hS : MeasurableSet S) :
    ∃ B : Set X, MeasurableSet B ∧ f ⁻¹' B = S := by
  rw [hcomap] at hS
  exact hS

omit mY in
theorem fullOuter_trace_mono (μ : Measure X) (f : Y → X)
    (hfull : ∀ B : Set X, MeasurableSet B → Disjoint B (range f) → μ B = 0)
    {B C : Set X} (hB : MeasurableSet B) (hC : MeasurableSet C)
    (htr : f ⁻¹' B ⊆ f ⁻¹' C) : μ B ≤ μ C := by
  have hnull : μ (B \ C) = 0 := by
    apply hfull _ (hB.diff hC)
    apply Set.disjoint_left.mpr
    rintro x ⟨hxB,hxC⟩ ⟨y,rfl⟩
    exact hxC (htr hxB)
  calc
    μ B ≤ μ (C ∪ (B \ C)) := measure_mono (by
      intro x hx; by_cases hxc : x ∈ C <;> simp [hx,hxc])
    _ ≤ μ C + μ (B \ C) := measure_union_le _ _
    _ = μ C := by rw [hnull,add_zero]

/-- Genuine countably additive trace measure, constructed from representatives
and disjointization. No smoothness or regularity field on the source is used. -/
theorem exists_fullOuter_trace_measure (μ : Measure X) (f : Y → X)
    (hcomap : mY = mX.comap f)
    (hfull : ∀ B : Set X, MeasurableSet B → Disjoint B (range f) → μ B = 0) :
    ∃ m : Measure Y, ∀ B : Set X, MeasurableSet B → m (f ⁻¹' B) = μ B := by
  classical
  have hwell : ∀ B C : Set X, MeasurableSet B → MeasurableSet C →
      f ⁻¹' B = f ⁻¹' C → μ B = μ C := by
    intro B C hB hC he
    exact le_antisymm (fullOuter_trace_mono μ f hfull hB hC he.le)
      (fullOuter_trace_mono μ f hfull hC hB he.ge)
  let rep : ∀ S : Set Y, MeasurableSet S → Set X :=
    fun S hS => (comap_repr f hcomap hS).choose
  have hrep : ∀ S hS, MeasurableSet (rep S hS) ∧ f ⁻¹' (rep S hS) = S :=
    fun S hS => (comap_repr f hcomap hS).choose_spec
  let mass : ∀ S : Set Y, MeasurableSet S → ℝ≥0∞ := fun S hS => μ (rep S hS)
  have hm : ∀ B : Set X, MeasurableSet B → ∀ (S : Set Y) (hS : MeasurableSet S),
      f ⁻¹' B = S → mass S hS = μ B := by
    intro B hB S hS he
    exact hwell _ _ (hrep S hS).1 hB ((hrep S hS).2.trans he.symm)
  have hm0 : mass ∅ MeasurableSet.empty = 0 := by
    rw [hm ∅ MeasurableSet.empty ∅ MeasurableSet.empty (by simp),measure_empty]
  have hmU : ∀ {S : ℕ → Set Y} (hs : ∀ n, MeasurableSet (S n)),
      Pairwise (Disjoint on S) → mass (⋃ n, S n) (.iUnion hs) = ∑' n, mass (S n) (hs n) := by
    intro S hs hd
    let B : ℕ → Set X := fun n => rep (S n) (hs n)
    have hB : ∀ n, MeasurableSet (B n) := fun n => (hrep (S n) (hs n)).1
    have htB : ∀ n, f ⁻¹' B n = S n := fun n => (hrep (S n) (hs n)).2
    have htC : ∀ n, f ⁻¹' disjointed B n = S n := by
      intro n
      rw [disjointed_eq_inter_compl]
      ext x
      simp only [mem_preimage,mem_inter_iff,mem_iInter,mem_compl_iff]
      constructor
      · intro hx
        have hx' : x ∈ f ⁻¹' B n := hx.1
        rw [htB n] at hx'; exact hx'
      · intro hx
        refine ⟨?_,?_⟩
        · change x ∈ f ⁻¹' B n
          rw [htB n]; exact hx
        · intro j hj hxj
          have hxj' : x ∈ f ⁻¹' B j := hxj
          rw [htB j] at hxj'
          exact Set.disjoint_left.mp (hd (ne_of_lt hj)) hxj' hx
    have htunion : f ⁻¹' (⋃ n, disjointed B n) = ⋃ n, S n := by
      simp_rw [preimage_iUnion,htC]
    rw [hm _ (.iUnion (MeasurableSet.disjointed hB)) _ (.iUnion hs) htunion,
      measure_iUnion (disjoint_disjointed B) (MeasurableSet.disjointed hB)]
    apply tsum_congr; intro n
    exact (hm _ (MeasurableSet.disjointed hB n) _ (hs n) (htC n)).symm
  let m : Measure Y := Measure.ofMeasurable mass hm0 (fun {g} hg hd => hmU hg hd)
  refine ⟨m,?_⟩
  intro B hB
  have htr : MeasurableSet (f ⁻¹' B) := by
    rw [hcomap]
    exact ⟨B,hB,rfl⟩
  rw [show m (f ⁻¹' B) = mass (f ⁻¹' B) htr from Measure.ofMeasurable_apply _ htr]
  exact hm B hB _ htr rfl

end FullOuterTrace

section SourceBorel

variable {X : Type u} [TopologicalSpace X]

noncomputable instance sourceMeasurableSpace (a : CHFubini.OmegaOneStage → X) :
    MeasurableSpace (CHFubini.SourcePoint a) := borel (CHFubini.SourcePoint a)

instance sourceBorelSpace (a : CHFubini.OmegaOneStage → X) :
    BorelSpace (CHFubini.SourcePoint a) := ⟨rfl⟩

/-- Exactly the manuscript's Borel trace sigma-algebra, despite the strictly
refined topology. No circle measurability of range(a) is assumed. -/
theorem source_borel_eq_comap [SecondCountableTopology X] [T2Space X]
    (a : CHFubini.OmegaOneStage → X) :
    borel (CHFubini.SourcePoint a) =
      (borel X).comap (@CHFubini.SourcePoint.val X a) := by
  letI : MeasurableSpace X := borel X
  letI : BorelSpace X := ⟨rfl⟩
  apply le_antisymm
  · apply MeasurableSpace.generateFrom_le
    intro U hU
    obtain ⟨O,C,hO,hC,_,hUC⟩ := CHFubini.source_countable_deletion a hU
    refine ⟨O \ (CHFubini.SourcePoint.val '' C),
      hO.measurableSet.diff (hC.image CHFubini.SourcePoint.val).measurableSet,?_⟩
    rw [preimage_diff,preimage_image_eq _ (CHFubini.SourcePoint.val_injective a)]
    exact hUC.symm
  · exact (CHFubini.source_val_continuous a).borel_measurable.comap_le

omit [TopologicalSpace X] in
theorem source_val_range (a : CHFubini.OmegaOneStage → X) :
    range (@CHFubini.SourcePoint.val X a) = range a := by
  ext x
  constructor
  · rintro ⟨y,rfl⟩; exact y.mem_range
  · intro hx; exact ⟨⟨x,hx⟩,rfl⟩

end SourceBorel

section SourceMeasure

variable {X : Type u} [TopologicalSpace X] [SecondCountableTopology X] [T2Space X]
    [mX : MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) (a : CHFubini.OmegaOneStage → X)

theorem exists_source_trace_measure
    (hfull : ∀ B : Set X, MeasurableSet B → Disjoint B (range a) → μ B = 0) :
    ∃ m : Measure (CHFubini.SourcePoint a),
      ∀ B : Set X, MeasurableSet B →
        m (CHFubini.SourcePoint.val ⁻¹' B) = μ B := by
  apply exists_fullOuter_trace_measure μ (@CHFubini.SourcePoint.val X a)
  · change borel (CHFubini.SourcePoint a) = mX.comap _
    rw [BorelSpace.measurable_eq (α := X)]
    exact source_borel_eq_comap a
  · intro B hB hd
    apply hfull B hB
    rwa [source_val_range] at hd

omit [TopologicalSpace X] [SecondCountableTopology X] [T2Space X] [BorelSpace X] in
/-- The exact null-trace interface needed by limitingValuation, derived from
the actual ambient A-property and the specified injective forgetful map. -/
theorem source_nullTrace_of_ambient_null_trace
    (hnull : ∀ N : Set X, MeasurableSet N → μ N = 0 → (range a ∩ N).Countable) :
    ∀ N : Set X, MeasurableSet N → μ N = 0 →
      {x : CHFubini.SourcePoint a | x.val ∈ N}.Countable := by
  intro N hN hN0
  apply ((hnull N hN hN0).preimage (CHFubini.SourcePoint.val_injective a)).mono
  intro x hx
  exact ⟨x.mem_range,hx⟩

variable (m : Measure (CHFubini.SourcePoint a))
    (hm : ∀ B : Set X, MeasurableSet B →
      m (CHFubini.SourcePoint.val ⁻¹' B) = μ B)

include hm in
omit [SecondCountableTopology X] [T2Space X] [BorelSpace X] in
theorem sourceMeasure_probability [IsProbabilityMeasure μ] : IsProbabilityMeasure m := by
  constructor
  have h := hm univ MeasurableSet.univ
  simpa only [preimage_univ,measure_univ] using h

include hm in
theorem sourceMeasure_noAtoms [NoAtoms μ] : NoAtoms m := by
  constructor
  intro x
  have he : CHFubini.SourcePoint.val ⁻¹' ({x.val} : Set X) = {x} := by
    ext y
    simp only [mem_preimage,mem_singleton_iff]
    exact ⟨fun h => CHFubini.SourcePoint.val_injective a h,fun h => congrArg _ h⟩
  rw [← he,hm _ (measurableSet_singleton _),measure_singleton]

include hm in
/-- Mass of any sandwich representative. This proves source equation
alpha-representative without assuming Radon regularity of m. -/
theorem sourceMeasure_representative_mass [NoAtoms μ]
    {U : Set (CHFubini.SourcePoint a)} {O : Set X} (hO : IsOpen O)
    (β : CHFubini.OmegaOneStage)
    (hlo : CHFubini.sourceBase a O β ⊆ U)
    (hup : U ⊆ CHFubini.SourcePoint.val ⁻¹' O) : m U = μ O := by
  letI : NoAtoms m := sourceMeasure_noAtoms μ a m hm
  let C : Set (CHFubini.SourcePoint a) := CHFubini.SourcePoint.val ⁻¹' O \ U
  have hCI : C ⊆ CHFubini.sourceInitial a β := by
    intro x hx
    change CHFubini.sourceIndex x < β
    apply lt_of_not_ge
    intro hβ
    exact hx.2 (hlo ⟨hx.1,hβ⟩)
  have hC0 : m C = 0 := ((CHFubini.sourceInitial_countable a β).mono hCI).measure_zero m
  have hUC : U = (CHFubini.SourcePoint.val ⁻¹' O) \ C := by
    ext x
    simp only [C,mem_diff]
    exact ⟨fun hx => ⟨hup hx,fun h => h.2 hx⟩,fun hx => by
      by_contra hxu; exact hx.2 ⟨hx.1,hxu⟩⟩
  rw [hUC,measure_diff_null hC0,hm O hO.measurableSet]

include hm in
theorem sourceMeasure_iUnion_representatives [NoAtoms μ]
    {I : Type v} (U : I → Set (CHFubini.SourcePoint a)) (O : I → Set X)
    (β : I → CHFubini.OmegaOneStage) (hO : ∀ i, IsOpen (O i))
    (hlo : ∀ i, CHFubini.sourceBase a (O i) (β i) ⊆ U i)
    (hup : ∀ i, U i ⊆ CHFubini.SourcePoint.val ⁻¹' O i) :
    m (⋃ i, U i) = μ (⋃ i, O i) := by
  obtain ⟨σ,hlo',hup'⟩ := CHFubini.ordinary_union_representative a U O β hO hlo hup
  exact sourceMeasure_representative_mass μ a m hm (isOpen_iUnion hO) σ hlo' hup'

private theorem directed_finset_upper {Z : Type v} [PartialOrder Z] {S : Set Z}
    (hn : S.Nonempty) (hd : DirectedOn (· ≤ ·) S) (F : Finset S) :
    ∃ U ∈ S, ∀ i ∈ F, i.val ≤ U := by
  classical
  induction F using Finset.induction_on with
  | empty => obtain ⟨U,hU⟩ := hn; exact ⟨U,hU,by simp⟩
  | @insert i F hi ih =>
    obtain ⟨U,hU,hFU⟩ := ih
    obtain ⟨V,hV,hiV,hUV⟩ := hd i i.property U hU
    refine ⟨V,hV,?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact hiV
    · exact (hFU j hj).trans hUV

include hm in
/-- Source Proposition alpha-continuous: arbitrary directed families, with
no regularity or countable-cofinality assumption on the refined source. -/
theorem sourceMeasure_mass_scottContinuous [NoAtoms μ] [IsFiniteMeasure μ]
    [Measure.InnerRegular μ] :
    ScottContinuous (fun U : Opens (CHFubini.SourcePoint a) => m (U : Set _)) := by
  classical
  choose O hO β hlo hup using
    (fun U : Opens (CHFubini.SourcePoint a) =>
      CHFubini.source_ordinary_representative a U.isOpen)
  apply ScottContinuous.of_map_sSup
  intro S hn hd
  have hSU : (⋃ U : S, (U.val : Set (CHFubini.SourcePoint a))) =
      ((sSup S : Opens (CHFubini.SourcePoint a)) : Set (CHFubini.SourcePoint a)) := by
    ext x
    constructor
    · intro hx
      obtain ⟨U,hxU⟩ := mem_iUnion.mp hx
      exact Opens.mem_sSup.mpr ⟨U.val,U.property,hxU⟩
    · intro hx
      obtain ⟨U,hU,hxU⟩ := Opens.mem_sSup.mp hx
      exact mem_iUnion.mpr ⟨⟨U,hU⟩,hxU⟩
  have hmass := sourceMeasure_iUnion_representatives μ a m hm
    (fun U : S => (U.val : Set (CHFubini.SourcePoint a)))
    (fun U : S => O U.val) (fun U : S => β U.val)
    (fun U => hO U.val) (fun U => hlo U.val) (fun U => hup U.val)
  rw [hSU] at hmass
  apply le_antisymm
  · change m ((sSup S : Opens (CHFubini.SourcePoint a)) : Set _) ≤ _
    rw [hmass,CHFubini.finite_subunion_formula μ (fun U : S => O U.val) (fun U => hO U.val)]
    apply iSup_le
    intro F
    obtain ⟨U,hU,hupper⟩ := directed_finset_upper hn hd F
    have hfmass : m (⋃ i ∈ F, (i.val : Set (CHFubini.SourcePoint a))) =
        μ (⋃ i ∈ F, O i.val) := by
      have hsrc : (⋃ i : F, (i.val.val : Set (CHFubini.SourcePoint a))) =
          ⋃ i ∈ F, (i.val : Set (CHFubini.SourcePoint a)) := by
        ext x
        simp only [mem_iUnion]
        exact ⟨fun ⟨i,hxi⟩ => ⟨i.val,i.property,hxi⟩,
          fun ⟨i,hi,hxi⟩ => ⟨⟨i,hi⟩,hxi⟩⟩
      have hamb : (⋃ i : F, O i.val.val) = ⋃ i ∈ F, O i.val := by
        ext x
        simp only [mem_iUnion]
        exact ⟨fun ⟨i,hxi⟩ => ⟨i.val,i.property,hxi⟩,
          fun ⟨i,hi,hxi⟩ => ⟨⟨i,hi⟩,hxi⟩⟩
      have h := sourceMeasure_iUnion_representatives μ a m hm
          (fun i : F => (i.val.val : Set (CHFubini.SourcePoint a)))
          (fun i : F => O i.val.val) (fun i : F => β i.val.val)
          (fun i => hO i.val.val) (fun i => hlo i.val.val) (fun i => hup i.val.val)
      rwa [hsrc,hamb] at h
    calc
      μ (⋃ i ∈ F, O i.val) = m (⋃ i ∈ F, (i.val : Set (CHFubini.SourcePoint a))) := hfmass.symm
      _ ≤ m (U : Set _) := measure_mono (iUnion₂_subset fun i hi => hupper i hi)
      _ ≤ sSup ((fun V : Opens (CHFubini.SourcePoint a) => m (V : Set _)) '' S) :=
        le_sSup (mem_image_of_mem _ hU)
  · apply sSup_le
    rintro z ⟨U,hU,rfl⟩
    have hle : U ≤ (sSup S : Opens (CHFubini.SourcePoint a)) := le_sSup hU
    exact measure_mono hle

noncomputable def sourceValuation [NoAtoms μ] [IsFiniteMeasure μ] [Measure.InnerRegular μ] :
    CHFubini.Valuation (CHFubini.SourcePoint a) where
  mass U := m (U : Set _)
  strict := measure_empty
  modular U V := (measure_union_add_inter (U : Set _) V.isOpen.measurableSet).symm
  continuous := sourceMeasure_mass_scottContinuous μ a m hm

@[simp] theorem sourceValuation_apply [NoAtoms μ] [IsFiniteMeasure μ]
    [Measure.InnerRegular μ] (U : Opens (CHFubini.SourcePoint a)) :
    sourceValuation μ a m hm U = m (U : Set _) := rfl

theorem sourceValuation_representative [NoAtoms μ] [IsFiniteMeasure μ]
    [Measure.InnerRegular μ] (U : Opens (CHFubini.SourcePoint a))
    {O : Set X} (hO : IsOpen O) (β : CHFubini.OmegaOneStage)
    (hlo : CHFubini.sourceBase a O β ⊆ (U : Set (CHFubini.SourcePoint a)))
    (hup : (U : Set (CHFubini.SourcePoint a)) ⊆
      (@CHFubini.SourcePoint.val X a) ⁻¹' O) :
    sourceValuation μ a m hm U = μ O :=
  sourceMeasure_representative_mass μ a m hm hO β hlo hup

include hm in
theorem sourceValuation_probability [NoAtoms μ] [IsProbabilityMeasure μ]
    [Measure.InnerRegular μ] : (sourceValuation μ a m hm).Probability := by
  letI : IsProbabilityMeasure m := sourceMeasure_probability μ a m hm
  exact measure_univ

include hm in
theorem sourceMeasure_tail_mass [NoAtoms μ] [IsProbabilityMeasure μ]
    (β : CHFubini.OmegaOneStage) : m (CHFubini.sourceTail a β) = 1 := by
  have h := sourceMeasure_representative_mass μ a m hm
    (U := CHFubini.sourceTail a β) isOpen_univ β
    (by simpa only [CHFubini.sourceBase,CHFubini.sourceTail,mem_univ,true_and] using
      (Subset.rfl : CHFubini.sourceTail a β ⊆ CHFubini.sourceTail a β))
    (subset_univ _)
  simpa only [measure_univ] using h

theorem sourceValuation_tail_mass [NoAtoms μ] [IsProbabilityMeasure μ]
    [Measure.InnerRegular μ] (β : CHFubini.OmegaOneStage) :
    sourceValuation μ a m hm
      ⟨CHFubini.sourceTail a β,CHFubini.sourceTail_isOpen a β⟩ = 1 :=
  sourceMeasure_tail_mass μ a m hm β

include hm in
theorem sourceMeasure_compact_zero [NoAtoms μ]
    {C : Set (CHFubini.SourcePoint a)} (hC : IsCompact C) : m C = 0 := by
  letI : NoAtoms m := sourceMeasure_noAtoms μ a m hm
  exact (CHFubini.source_compact_countable a hC).measure_zero m

include hm in
/-- Semantic regression guard: the actual source measure cannot be upgraded
to an inner-regular/Radon measure. Its total mass is one but all compacts null. -/
theorem sourceMeasure_not_innerRegular [NoAtoms μ] [IsProbabilityMeasure μ] :
    ¬ Measure.InnerRegular m := by
  intro hir
  letI := hir
  letI : IsProbabilityMeasure m := sourceMeasure_probability μ a m hm
  obtain ⟨C,_,hC,hCpos⟩ := (MeasurableSet.univ (α := CHFubini.SourcePoint a)).exists_lt_isCompact
    (show (0 : ℝ≥0∞) < m univ by rw [measure_univ]; exact zero_lt_one)
  rw [sourceMeasure_compact_zero μ a m hm hC] at hCpos
  exact lt_irrefl _ hCpos

/-- Construct the source probability and its actual valuation restriction
from the already proved A-property (iii), not from an alpha-continuity field. -/
theorem exists_source_measure_and_valuation [NoAtoms μ] [IsProbabilityMeasure μ]
    [Measure.InnerRegular μ]
    (htrace : ∀ E : Set X, MeasurableSet E → (range a ∩ E).Countable → μ E = 0) :
    ∃ m : Measure (CHFubini.SourcePoint a), IsProbabilityMeasure m ∧
      (∀ B : Set X, MeasurableSet B → m (CHFubini.SourcePoint.val ⁻¹' B) = μ B) ∧
      ∃ α : CHFubini.Valuation (CHFubini.SourcePoint a), α.Probability ∧
        ∀ U : Opens (CHFubini.SourcePoint a), α U = m (U : Set _) := by
  have hfull : ∀ B : Set X, MeasurableSet B → Disjoint B (range a) → μ B = 0 := by
    intro B hB hd
    apply htrace B hB
    rw [Set.disjoint_iff_inter_eq_empty.mp hd.symm]
    exact countable_empty
  obtain ⟨m,hm⟩ := exists_source_trace_measure μ a hfull
  exact ⟨m,sourceMeasure_probability μ a m hm,hm,sourceValuation μ a m hm,
    sourceValuation_probability μ a m hm,fun _ => rfl⟩

end SourceMeasure

section RandomMass

variable {T : Type u} [MetricSpace T] [SecondCountableTopology T]
    [MeasurableSpace T] [BorelSpace T]
    (μ : Measure T) [NoAtoms μ] [Measure.InnerRegular μ]
    (a : CHFubini.OmegaOneStage → T)
    (m : Measure (CHFubini.SourcePoint a))
    (hm : ∀ B : Set T, MeasurableSet B →
      m (CHFubini.SourcePoint.val ⁻¹' B) = μ B)

/-- Source random-small's exact mass identity, valid for every radius family.
Specializing to circleRadius epsilon gives alpha(R_s)=lambda(U_s). -/
theorem sourceValuation_randomOpen_mass [IsFiniteMeasure μ]
    (r : ℕ → ℝ) (s : ℕ → T) :
    sourceValuation μ a m hm
      (CHFubini.randomOpen CHFubini.SourcePoint.val (CHFubini.source_val_continuous a) r s) =
      μ (CHFubini.randomBallUnion r s) := by
  rw [sourceValuation_apply]
  exact hm _ (CHFubini.randomBallUnion_isOpen r s).measurableSet

/-- Source random-full, on the exact tailRandomOpen underlying sourceStage.
No independence, positivity of radii, or additional source regularity is used. -/
theorem sourceValuation_tailRandomOpen_mass [IsProbabilityMeasure μ]
    (r : ℕ → ℝ) (β : CHFubini.OmegaOneStage) (s : ℕ → T) :
    sourceValuation μ a m hm
      (CHFubini.tailRandomOpen
        ⟨CHFubini.sourceTail a β,CHFubini.sourceTail_isOpen a β⟩
        CHFubini.SourcePoint.val (CHFubini.source_val_continuous a) r s) = 1 := by
  apply le_antisymm
  · exact (sourceValuation_probability μ a m hm).subprobability.mass_le_one _
  · calc
      (1 : ℝ≥0∞) = sourceValuation μ a m hm
          ⟨CHFubini.sourceTail a β,CHFubini.sourceTail_isOpen a β⟩ :=
        (sourceValuation_tail_mass μ a m hm β).symm
      _ ≤ _ := (sourceValuation μ a m hm).mono le_sup_left

end RandomMass

/-- The concrete source probability and continuous valuation exist under CH
on the actual generated refined unit-circle source. Every additional property
of a is derived from the genuine CH recursion, not assumed here. -/
theorem exists_CH_circle_source_measure_and_valuation (hCH : CHFubini.CH) :
    ∃ a : CHFubini.OmegaOneStage → UnitAddCircle, Function.Injective a ∧
      (∀ B, MeasurableSet B → volume B = 0 → ∃ β,
        range a ∩ B ⊆ CHFubini.initialSegment a β ∧ (range a ∩ B).Countable) ∧
      (∀ C, IsCompact C → 0 < volume C → (range a ∩ C).Nonempty) ∧
      (∀ E, MeasurableSet E → (range a ∩ E).Countable → volume E = 0) ∧
      ∃ m : Measure (CHFubini.SourcePoint a), IsProbabilityMeasure m ∧
        (∀ B : Set UnitAddCircle, MeasurableSet B →
          m (CHFubini.SourcePoint.val ⁻¹' B) = volume B) ∧
        ∃ α : CHFubini.Valuation (CHFubini.SourcePoint a), α.Probability ∧
          ∀ U : Opens (CHFubini.SourcePoint a), α U = m (U : Set _) := by
  obtain ⟨a,ha,hnull,hcompact,htrace⟩ := CHFubini.exists_CH_circle_points hCH
  letI := CHFubini.unitCircle_volume_noAtoms
  letI := CHFubini.unitCircle_volume_innerRegular
  letI : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
    ⟨UnitAddCircle.measure_univ⟩
  exact ⟨a,ha,hnull,hcompact,htrace,
    exists_source_measure_and_valuation (volume : Measure UnitAddCircle) a htrace⟩

end CHFubini

-- Candidate-only actual axiom evidence; no new assumption is introduced.
#print axioms CHFubini.fullOuter_trace_mono
#print axioms CHFubini.exists_fullOuter_trace_measure
#print axioms CHFubini.sourceMeasurableSpace
#print axioms CHFubini.sourceBorelSpace
#print axioms CHFubini.source_borel_eq_comap
#print axioms CHFubini.source_val_range
#print axioms CHFubini.exists_source_trace_measure
#print axioms CHFubini.source_nullTrace_of_ambient_null_trace
#print axioms CHFubini.sourceMeasure_probability
#print axioms CHFubini.sourceMeasure_noAtoms
#print axioms CHFubini.sourceMeasure_representative_mass
#print axioms CHFubini.sourceMeasure_iUnion_representatives
#print axioms CHFubini.sourceMeasure_mass_scottContinuous
#print axioms CHFubini.sourceValuation
#print axioms CHFubini.sourceValuation_apply
#print axioms CHFubini.sourceValuation_representative
#print axioms CHFubini.sourceValuation_probability
#print axioms CHFubini.sourceMeasure_tail_mass
#print axioms CHFubini.sourceValuation_tail_mass
#print axioms CHFubini.sourceValuation_randomOpen_mass
#print axioms CHFubini.sourceValuation_tailRandomOpen_mass
#print axioms CHFubini.sourceMeasure_compact_zero
#print axioms CHFubini.sourceMeasure_not_innerRegular
#print axioms CHFubini.exists_source_measure_and_valuation
#print axioms CHFubini.exists_CH_circle_source_measure_and_valuation
