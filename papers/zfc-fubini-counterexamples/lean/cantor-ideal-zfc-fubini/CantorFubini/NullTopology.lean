import CantorFubini.ParameterMeasure
import Mathlib.MeasureTheory.Measure.NullMeasurable

/-! Source auxiliary topology: ordinary opens with arbitrary null sets removed.
Measures on arbitrary sets are outer measures; null-measurability below proves
agreement with the completed measure, without restricting the null indices. -/
set_option autoImplicit false
open Set Topology TopologicalSpace MeasureTheory
universe u v
namespace CantorFubini
variable {X : Type u} [TopologicalSpace X] [MeasurableSpace X]
variable (m : Measure X)

def NullRemovedOpen (U : Set X) : Prop :=
  ∃ O : Set X, IsOpen O ∧ ∃ N : Set X, m N = 0 ∧ U = O \ N

theorem nullRemovedOpen_inter {U V : Set X}
    (hU : NullRemovedOpen m U) (hV : NullRemovedOpen m V) :
    NullRemovedOpen m (U ∩ V) := by
  obtain ⟨O, hO, N, hN, rfl⟩ := hU
  obtain ⟨P, hP, L, hL, rfl⟩ := hV
  refine ⟨O ∩ P, hO.inter hP, N ∪ L, measure_union_null hN hL, ?_⟩
  ext x; simp only [mem_inter_iff, mem_diff, mem_union]; tauto

variable [SecondCountableTopology X]

theorem removed_union_null {I : Type v} (O N : I → Set X)
    (hO : ∀ i, IsOpen (O i)) (hN : ∀ i, m (N i) = 0) :
    m ((⋃ i, O i) \ ⋃ i, O i \ N i) = 0 := by
  obtain ⟨J, hJ, hcover⟩ := isOpen_iUnion_countable O hO
  apply measure_mono_null (t := ⋃ j ∈ J, N j) _
    ((measure_biUnion_null_iff hJ).mpr (fun j _ => hN j))
  rintro x ⟨hx, hxU⟩
  rw [← hcover] at hx
  obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp hx
  refine mem_iUnion₂.mpr ⟨j, hj, ?_⟩
  by_contra hxN
  exact hxU (mem_iUnion.mpr ⟨j, hxj, hxN⟩)

theorem nullRemovedOpen_iUnion {I : Type v} (U : I → Set X)
    (hU : ∀ i, NullRemovedOpen m (U i)) : NullRemovedOpen m (⋃ i, U i) := by
  classical
  choose O hO N hN he using hU
  refine ⟨⋃ i, O i, isOpen_iUnion hO, (⋃ i, O i) \ ⋃ i, U i, ?_, ?_⟩
  · simp_rw [he]
    exact removed_union_null m O N hO hN
  · have hsub : (⋃ i, U i) ⊆ ⋃ i, O i := iUnion_mono (fun i => by rw [he i]; exact diff_subset)
    exact (diff_diff_cancel_left hsub).symm

@[implicit_reducible] def nullTopology : TopologicalSpace X where
  IsOpen := NullRemovedOpen m
  isOpen_univ := ⟨univ, isOpen_univ, ∅, measure_empty, by simp⟩
  isOpen_inter := fun _ _ => nullRemovedOpen_inter m
  isOpen_sUnion S hS := by
    rw [sUnion_eq_iUnion]
    exact nullRemovedOpen_iUnion m (fun U : S => U.val) (fun U => hS U.val U.property)

theorem nullTopology_open_iff (U : Set X) : (nullTopology m).IsOpen U ↔
    NullRemovedOpen m U := Iff.rfl

theorem nullRemovedOpen_nullMeasurable [OpensMeasurableSpace X] {U : Set X}
    (hU : NullRemovedOpen m U) : NullMeasurableSet U m := by
  obtain ⟨O, hO, N, hN, rfl⟩ := hU
  exact hO.measurableSet.nullMeasurableSet.diff (NullMeasurableSet.of_null hN)

theorem measure_nullRemoved (O N : Set X) (hN : m N = 0) : m (O \ N) = m O :=
  measure_diff_null hN

/-- The completed probability in the source has exactly the same value on
every subset, not merely on Borel sets. Mathlib completion keeps outer measure. -/
theorem completed_mass (U : Set X) : m.completion U = m U :=
  Measure.completion_apply m U

theorem completed_null_family : {N : Set X | m.completion N = 0} =
    {N : Set X | m N = 0} := rfl

theorem measure_removed_iUnion {I : Type v} (O N : I → Set X)
    (hO : ∀ i, IsOpen (O i)) (hN : ∀ i, m (N i) = 0) :
    m (⋃ i, O i \ N i) = m (⋃ i, O i) := by
  have hsub : (⋃ i, O i \ N i) ⊆ ⋃ i, O i := iUnion_mono (fun _ => diff_subset)
  rw [← measure_diff_null (s := ⋃ i, O i) (removed_union_null m O N hO hN)]
  rw [diff_diff_cancel_left hsub]

theorem nullRemoved_directed_measure [T2Space X] [OpensMeasurableSpace X]
    [IsFiniteMeasure m] [m.InnerRegular]
    {I : Type v} [Nonempty I] (U : I → Set X)
    (hU : ∀ i, NullRemovedOpen m (U i)) (hd : Directed (· ⊆ ·) U) :
    m (⋃ i, U i) = ⨆ i, m (U i) := by
  classical
  choose O hO N hN he using hU
  apply le_antisymm
  · have hEqUnion : m (⋃ i, U i) = m (⋃ i, O i) := by
      simp_rw [he]; exact measure_removed_iUnion m O N hO hN
    rw [hEqUnion, finite_subunion_formula m O hO]
    apply iSup_le
    intro F
    have hbound : ∃ j, ∀ i ∈ F, U i ⊆ U j := by
      induction F using Finset.induction_on with
      | empty => exact ⟨Classical.choice inferInstance, by simp⟩
      | @insert i F hi ih =>
        obtain ⟨j, hj⟩ := ih
        obtain ⟨k, hik, hjk⟩ := hd i j
        exact ⟨k, fun l hl => (Finset.mem_insert.mp hl).elim
          (fun h => h ▸ hik) (fun h => (hj l h).trans hjk)⟩
    obtain ⟨j, hj⟩ := hbound
    have hEq : m (⋃ i ∈ F, O i) = m (⋃ i ∈ F, U i) := by
      simp_rw [he]
      simpa only [iUnion_subtype] using (measure_removed_iUnion m (fun i : F => O i)
        (fun i : F => N i) (fun i => hO i) (fun i => hN i)).symm
    rw [hEq]
    exact (measure_mono (iUnion₂_subset (fun i hi => hj i hi))).trans (le_iSup (fun i => m (U i)) j)
  · exact iSup_le (fun i => measure_mono (subset_iUnion U i))

def nullValuation [T2Space X] [OpensMeasurableSpace X]
    [IsFiniteMeasure m] [m.InnerRegular] : @Valuation X (nullTopology m) := by
  refine @Valuation.mk X (nullTopology m) (fun U => m U) measure_empty ?_ ?_
  · intro U V
    exact (measure_union_add_inter₀ (U : Set X)
      (nullRemovedOpen_nullMeasurable m (@Opens.isOpen X (nullTopology m) V))).symm
  ·
    intro D hn hd U hU
    have he : U = sSup D := hU.unique (isLUB_sSup D)
    letI : Nonempty D := hn.to_subtype
    have hm := nullRemoved_directed_measure m (fun V : D => (V.val : Set X))
      (fun V => @Opens.isOpen X (nullTopology m) V.val) (by
        intro V W
        obtain ⟨Z, hZ, hVZ, hWZ⟩ := hd V.val V.property W.val W.property
        exact ⟨⟨Z, hZ⟩, hVZ, hWZ⟩)
    constructor
    · rintro a ⟨V, hV, rfl⟩; exact measure_mono (hU.1 hV)
    · intro a ha
      change m (U : Set X) ≤ a
      rw [he, @Opens.coe_sSup X (nullTopology m) D]
      have heUnion : (⋃ V ∈ D, (V : Set X)) = ⋃ V : D, (V.val : Set X) := by
        ext x; simp only [mem_iUnion, Subtype.exists, exists_prop]
      rw [heUnion, hm]
      exact iSup_le (fun V => ha (mem_image_of_mem _ V.property))

theorem nullValuation_probability [T2Space X] [OpensMeasurableSpace X]
    [IsProbabilityMeasure m] [m.InnerRegular] :
    @Valuation.Probability X (nullTopology m) (nullValuation m) := measure_univ
end CantorFubini
