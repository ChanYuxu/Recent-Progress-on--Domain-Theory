import ZFCFubini.DensityMeasure

/-! The literal circle density topology and the arbitrary-union proof from
source Lemma `lem:density`. Ordinary metric/topological instances on `Circle`
are never overwritten. -/

set_option autoImplicit false
open Set Filter Metric MeasureTheory TopologicalSpace Topology
open scoped ENNReal Topology
universe u

namespace ZFCFubini

theorem ordinary_isOpen_densityOpen {U : Set Circle} (hU : IsOpen U) : DensityOpen U := by
  refine ⟨hU.measurableSet.nullMeasurableSet, ?_⟩
  intro x hx
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU x hx
  have he : densityRatio U x =ᶠ[𝓝[>] (0 : ℝ)] fun _ => (1 : ℝ) := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hε : ∀ᶠ r in 𝓝 (0 : ℝ), r < ε).filter_mono nhdsWithin_le_nhds]
      with r hr0 hrε
    have hb : ball x r ⊆ U := (ball_subset_ball hrε.le).trans hεU
    unfold densityRatio
    rw [inter_eq_right.mpr hb, div_self]
    exact ne_of_gt (ENNReal.toReal_pos (circle_volume_ball_pos x hr0).ne' (measure_ne_top _ _))
  exact tendsto_const_nhds.congr' he.symm

theorem densityOpen_empty : DensityOpen (∅ : Set Circle) :=
  ⟨MeasurableSet.empty.nullMeasurableSet, empty_subset _⟩

theorem densityOpen_univ : DensityOpen (univ : Set Circle) :=
  ordinary_isOpen_densityOpen isOpen_univ

theorem densityOpen_null_compl {M : Set Circle} (hM : volume M = 0) : DensityOpen Mᶜ := by
  have he : Mᶜ =ᵐ[(volume : Measure Circle)] (univ : Set Circle) := by
    filter_upwards [show ∀ᵐ x ∂(volume : Measure Circle), x ∉ M from
      (ae_iff.mpr (by simpa only [not_not, setOf_mem_eq] using hM))] with x hx
    exact propext ⟨fun _ => mem_univ x, fun _ => hx⟩
  refine ⟨(NullMeasurableSet.of_null hM).compl, ?_⟩
  intro x _
  have hx := densityOpen_univ.2 (mem_univ x)
  exact (densityPoints_congr_ae he).symm ▸ hx

/-- The finite-intersection density deficit is bounded by the sum of the two
deficits, precisely the estimate used in the source. -/
theorem densityRatio_inter_lower {A B : Set Circle}
    (hB : NullMeasurableSet B (volume : Measure Circle)) (x : Circle) (r : ℝ) :
    densityRatio A x r + densityRatio B x r - 1 ≤ densityRatio (A ∩ B) x r := by
  by_cases hr : 0 < r
  · let C := ball x r
    have hm := measure_union_add_inter₀ (μ := (volume : Measure Circle)) (t := B ∩ C)
      (A ∩ C) (hB.inter (measurableSet_ball (x := x) (ε := r)).nullMeasurableSet)
    have hreal := congrArg ENNReal.toReal hm
    rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _),
      ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)] at hreal
    have hsub : (A ∩ C) ∪ (B ∩ C) ⊆ C := union_subset inter_subset_right inter_subset_right
    have hbound : (volume ((A ∩ C) ∪ (B ∩ C))).toReal ≤ (volume C).toReal :=
      ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub)
    have hint : (A ∩ C) ∩ (B ∩ C) = (A ∩ B) ∩ C := by ext y; simp; tauto
    rw [hint] at hreal
    have hle : (volume (A ∩ C)).toReal + (volume (B ∩ C)).toReal ≤
        (volume C).toReal + (volume ((A ∩ B) ∩ C)).toReal := by linarith
    have hd : 0 < (volume C).toReal :=
      ENNReal.toReal_pos (circle_volume_ball_pos x hr).ne' (measure_ne_top _ _)
    have hdiv := div_le_div_of_nonneg_right hle hd.le
    rw [add_div, add_div, div_self hd.ne'] at hdiv
    exact (by dsimp only [densityRatio, C] at *; linarith)
  · have hb : ball x r = ∅ := ball_eq_empty.mpr (le_of_not_gt hr)
    simp [densityRatio, hb]

theorem densityOpen_inter {A B : Set Circle} (hA : DensityOpen A) (hB : DensityOpen B) :
    DensityOpen (A ∩ B) := by
  refine ⟨hA.1.inter hB.1, ?_⟩
  rintro x ⟨hxA, hxB⟩
  have hl : Tendsto (fun r => densityRatio A x r + densityRatio B x r - 1)
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    convert ((hA.2 hxA).add (hB.2 hxB)).sub_const 1 using 1 <;> norm_num
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hl tendsto_const_nhds
    (densityRatio_inter_lower hB.1 x) (densityRatio_le_one (A ∩ B) x)

theorem densityOpen_union {A B : Set Circle} (hA : DensityOpen A) (hB : DensityOpen B) :
    DensityOpen (A ∪ B) := by
  refine ⟨hA.1.union hB.1, ?_⟩
  rintro x (hx | hx)
  · exact densityPoints_mono subset_union_left (hA.2 hx)
  · exact densityPoints_mono subset_union_right (hB.2 hx)

theorem densityOpen_finset_union {I : Type u} (U : I → Set Circle)
    (hU : ∀ i, DensityOpen (U i)) (F : Finset I) : DensityOpen (⋃ i ∈ F, U i) := by
  classical
  induction F using Finset.induction_on with
  | empty => simpa using densityOpen_empty
  | @insert i F hi ih => simpa using densityOpen_union (hU i) ih

/-- Source arbitrary-union argument: approximate the supremum of finite
subunion masses by increasing finite index sets, take their countable union,
and use the completed density theorem to sandwich the arbitrary union. -/
theorem densityOpen_iUnion_and_measure {I : Type u} (U : I → Set Circle)
    (hU : ∀ i, DensityOpen (U i)) :
    DensityOpen (⋃ i, U i) ∧
      volume (⋃ i, U i) = ⨆ F : Finset I, volume (⋃ i ∈ F, U i) := by
  classical
  let m : Finset I → ℝ≥0∞ := fun F => volume (⋃ i ∈ F, U i)
  let s : ℝ≥0∞ := sSup (range m)
  obtain ⟨v, _, hvs, hv⟩ := exists_seq_tendsto_sSup (range_nonempty m)
    (show BddAbove (range m) from ⟨1, by rintro _ ⟨F, rfl⟩; exact prob_le_one⟩)
  choose f hf using hv
  let F : ℕ → Finset I := fun n => (Finset.range (n + 1)).biUnion f
  have hFmono : Monotone F := by
    intro n k hnk i hi
    simp only [F, Finset.mem_biUnion, Finset.mem_range] at hi ⊢
    obtain ⟨j, hj, hij⟩ := hi
    exact ⟨j, lt_of_lt_of_le hj (Nat.add_le_add_right hnk 1), hij⟩
  have hfF (n : ℕ) : f n ⊆ F n := by
    intro i hi
    exact Finset.mem_biUnion.mpr ⟨n, Finset.mem_range.mpr (Nat.lt_succ_self n), hi⟩
  let A : ℕ → Set Circle := fun n => ⋃ i ∈ F n, U i
  have hAmono : Monotone A := by
    intro n k hnk x hx
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hx
    exact mem_iUnion₂.mpr ⟨i, hFmono hnk hi, hxi⟩
  let C : Set Circle := ⋃ n, A n
  have hCm : NullMeasurableSet C (volume : Measure Circle) :=
    NullMeasurableSet.iUnion (fun n => (densityOpen_finset_union U hU (F n)).1)
  have hm_le (T : Finset I) : m T ≤ s := le_sSup (mem_range_self T)
  have hv_le (n : ℕ) : v n ≤ volume (A n) := by
    rw [← hf n]
    apply measure_mono
    intro x hx
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hx
    exact mem_iUnion₂.mpr ⟨i, hfF n hi, hxi⟩
  have hCs : volume C = s := by
    apply le_antisymm
    · rw [hAmono.measure_iUnion]
      exact iSup_le (fun n => hm_le (F n))
    · exact le_of_tendsto hvs (Eventually.of_forall (fun n =>
        (hv_le n).trans (measure_mono (subset_iUnion A n))))
  have hCunion (i : I) : volume (C ∪ U i) = s := by
    apply le_antisymm
    · rw [show C ∪ U i = ⋃ n, A n ∪ U i from iUnion_union _ _]
      have hm : Monotone (fun n => A n ∪ U i) := fun _ _ h => union_subset_union (hAmono h) Subset.rfl
      rw [hm.measure_iUnion]
      apply iSup_le
      intro n
      have he : A n ∪ U i = ⋃ j ∈ insert i (F n), U j := by
        simp only [Finset.set_biUnion_insert, A]
        exact union_comm _ _
      rw [he]
      exact hm_le (insert i (F n))
    · rw [← hCs]
      exact measure_mono subset_union_left
  have hdiff (i : I) : volume (U i \ C) = 0 := by
    rw [measure_diff' _ hCm (measure_ne_top _ _), union_comm, hCunion i, hCs, tsub_self]
  have hCdensity (i : I) : U i ⊆ densityPoints C := by
    intro x hx
    have hle : U i ≤ᵐ[(volume : Measure Circle)] C := ae_le_set.mpr (hdiff i)
    have he : (U i ∩ C : Set Circle) =ᵐ[(volume : Measure Circle)] U i := by
      filter_upwards [hle] with y hy
      exact propext ⟨fun h => h.1, fun h => ⟨h, hy h⟩⟩
    have hxD := (hU i).2 hx
    have hxI : x ∈ densityPoints (U i ∩ C) := (densityPoints_congr_ae he).symm ▸ hxD
    exact densityPoints_mono inter_subset_right hxI
  have hCsub : C ⊆ ⋃ i, U i := by
    rintro x hx
    obtain ⟨n, hn⟩ := mem_iUnion.mp hx
    obtain ⟨i, _, hxi⟩ := mem_iUnion₂.mp hn
    exact mem_iUnion.mpr ⟨i, hxi⟩
  have hUsub : (⋃ i, U i) ⊆ densityPoints C := iUnion_subset hCdensity
  have hUC : (⋃ i, U i) =ᵐ[(volume : Measure Circle)] C := by
    filter_upwards [densityPoints_ae_eq C hCm] with x hx
    apply propext
    constructor
    · intro hxU
      exact Eq.mp hx (hUsub hxU)
    · intro hxC
      exact hCsub hxC
  refine ⟨⟨hCm.congr hUC.symm, ?_⟩, ?_⟩
  · rintro x hx
    obtain ⟨i, hxi⟩ := mem_iUnion.mp hx
    exact densityPoints_mono (subset_iUnion U i) ((hU i).2 hxi)
  · rw [hUC.measure_eq, hCs]
    exact sSup_range

theorem densityOpen_iUnion {I : Type u} (U : I → Set Circle)
    (hU : ∀ i, DensityOpen (U i)) : DensityOpen (⋃ i, U i) :=
  (densityOpen_iUnion_and_measure U hU).1

/-- Source tau on the actual circle carrier, with ordinary topology separate. -/
@[reducible] def densityTopology : TopologicalSpace Circle where
  IsOpen := DensityOpen
  isOpen_univ := densityOpen_univ
  isOpen_inter _ _ := densityOpen_inter
  isOpen_sUnion S hS := by
    rw [sUnion_eq_iUnion]
    exact densityOpen_iUnion _ (fun U => hS U.val U.property)

theorem densityTopology_isOpen_iff (U : Set Circle) :
    @IsOpen Circle densityTopology U ↔ DensityOpen U := Iff.rfl

theorem ordinary_isOpen_densityTopology {U : Set Circle} (hU : IsOpen U) :
    @IsOpen Circle densityTopology U := ordinary_isOpen_densityOpen hU

theorem circle_singleton_null (x : Circle) : volume ({x} : Set Circle) = 0 := by
  rw [← Metric.closedBall_zero, AddCircle.volume_closedBall]
  norm_num

theorem densityTopology_singleton_compl_open (x : Circle) :
    @IsOpen Circle densityTopology ({x} : Set Circle)ᶜ :=
  ordinary_isOpen_densityTopology isClosed_singleton.isOpen_compl

theorem densityTopology_t1 : @T1Space Circle densityTopology := by
  refine @T1Space.mk Circle densityTopology ?_
  intro x
  exact @IsClosed.mk Circle densityTopology ({x} : Set Circle)
    (densityTopology_singleton_compl_open x)

end ZFCFubini
