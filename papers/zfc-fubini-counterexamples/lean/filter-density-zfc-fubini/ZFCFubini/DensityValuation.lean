import ZFCFubini.DensityTopology

/-! Full arbitrary-directed continuity of completed Haar on the literal
density topology, source Lemma `lem:density`. -/

set_option autoImplicit false
open Set Filter MeasureTheory TopologicalSpace Topology
open scoped ENNReal Topology
universe u

namespace ZFCFubini

/-- The null-set family in the source, with completed rather than merely Borel
measurability. Subsets of null sets and countable unions are proved below. -/
abbrev NullSet :=
  {M : Set Circle // NullMeasurableSet M (volume : Measure Circle) ∧ volume M = 0}

def nullSetEmpty : NullSet := ⟨∅, MeasurableSet.empty.nullMeasurableSet, measure_empty⟩

def nullSetUnion (M N : NullSet) : NullSet :=
  ⟨M.1 ∪ N.1, M.2.1.union N.2.1, measure_union_null M.2.2 N.2.2⟩

def nullSetCountableUnion (M : ℕ → NullSet) : NullSet :=
  ⟨⋃ n, (M n).1, NullMeasurableSet.iUnion (fun n => (M n).2.1),
    measure_iUnion_null (fun n => (M n).2.2)⟩

theorem nullSet_subset {M A : Set Circle} (hAM : A ⊆ M) (hM : volume M = 0) :
    NullMeasurableSet A (volume : Measure Circle) ∧ volume A = 0 := by
  have hA : volume A = 0 := measure_mono_null hAM hM
  exact ⟨NullMeasurableSet.of_null hA, hA⟩

/-- Every density-open set is completed Haar measurable. -/
theorem density_isOpen_nullMeasurable {U : Set Circle}
    (hU : @IsOpen Circle densityTopology U) :
    NullMeasurableSet U (volume : Measure Circle) := hU.1

/-- Full directed-open union law, with no countable-cofinality assumption. -/
theorem density_directed_open_measure {I : Type u} [Nonempty I]
    (U : I → @Opens Circle densityTopology) (hU : Directed (· ≤ ·) U) :
    volume ((⨆ i, U i : @Opens Circle densityTopology) : Set Circle) =
      ⨆ i, volume (U i : Set Circle) := by
  classical
  letI : TopologicalSpace Circle := densityTopology
  rw [Opens.coe_iSup]
  rw [(densityOpen_iUnion_and_measure (fun i => (U i : Set Circle))
    (fun i => (U i).isOpen)).2]
  apply le_antisymm
  · apply iSup_le
    intro F
    obtain ⟨j, hj⟩ := hU.finset_le F
    apply (measure_mono (show (⋃ i ∈ F, (U i : Set Circle)) ⊆ U j from ?_)).trans
      (le_iSup (fun i => volume (U i : Set Circle)) j)
    rintro x hx
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hx
    exact hj i hi hxi
  · apply iSup_le
    intro i
    simpa using (le_iSup (fun F : Finset I => volume (⋃ i ∈ F, (U i : Set Circle))) {i})

/-- Completed normalized Haar restricted to the full density topology. -/
noncomputable def densityValuation : @Valuation Circle densityTopology := by
  letI : TopologicalSpace Circle := densityTopology
  refine
    { mass := fun U => volume (U : Set Circle)
      strict := measure_empty
      modular := fun U V => (measure_union_add_inter₀ (μ := (volume : Measure Circle))
        (U : Set Circle) (density_isOpen_nullMeasurable V.isOpen)).symm
      continuous := ?_ }
  intro A hn hd p hp
  letI : Nonempty A := hn.to_subtype
  let U : A → Opens Circle := fun U => U.val
  have hdir : Directed (· ≤ ·) U := by
    intro V W
    obtain ⟨Z, hZ, hVZ, hWZ⟩ := hd V.val V.property W.val W.property
    exact ⟨⟨Z, hZ⟩, hVZ, hWZ⟩
  have hpU : p = ⨆ i, U i := by
    rw [hp.unique (isLUB_sSup A)]
    simp only [sSup_eq_iSup, iSup_subtype, U]
  constructor
  · rintro z ⟨V, hV, rfl⟩
    exact measure_mono (hp.1 hV)
  · intro z hz
    change volume (p : Set Circle) ≤ z
    rw [hpU, density_directed_open_measure U hdir]
    exact iSup_le (fun V => hz (mem_image_of_mem _ V.property))

@[simp] theorem densityValuation_apply (U : @Opens Circle densityTopology) :
    densityValuation U = volume (U : Set Circle) := rfl

theorem densityValuation_probability :
    @Valuation.Probability Circle densityTopology densityValuation :=
  UnitAddCircle.measure_univ

/-- Source Lemma `lem:density`: the literal family is the topology and its
literal Haar restriction is a continuous probability valuation. Its
continuous-valuation structure is the constructed `densityValuation` itself. -/
theorem density_topology_and_valuation :
    (∀ U : Set Circle, @IsOpen Circle densityTopology U ↔ DensityOpen U) ∧
    (∀ U : @Opens Circle densityTopology, densityValuation U = volume (U : Set Circle)) ∧
    @Valuation.Probability Circle densityTopology densityValuation :=
  ⟨densityTopology_isOpen_iff, densityValuation_apply, densityValuation_probability⟩

end ZFCFubini
