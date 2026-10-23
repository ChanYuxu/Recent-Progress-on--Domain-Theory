import CantorFubini.Trace
import CantorFubini.CantorProbability

/-! Exact source interfaces for the printed kernel condition, completed measure,
and the maximal-point subspace. These bridges do not assume their conclusions. -/
set_option autoImplicit false
open Set Topology TopologicalSpace MeasureTheory
universe u v
namespace CantorFubini

def CantorKernelCondition (K : Set Cantor) (x : Cantor) : Prop :=
  x ∈ K ∧ ∀ n : ℕ, (K \ (cylinder x (n + 1) : Set Cantor)).Finite

theorem kernel_condition_iff (K : Set Cantor) (x : Cantor) :
    CantorKernelCondition K x ↔ x ∈ K ∧
      ∀ V : Set Cantor, IsOpen V → x ∈ V → (K \ V).Finite := by
  constructor
  · rintro ⟨hx, hK⟩
    refine ⟨hx, fun V hV hxV => ?_⟩
    obtain ⟨n, hn⟩ := exists_cylinder_subset hV hxV
    exact (hK n).subset (fun y hy => ⟨hy.1, fun hyC => hy.2
      (hn ((cylinder_anti x (Nat.le_succ n)) hyC))⟩)
  · rintro ⟨hx, hK⟩
    exact ⟨hx, fun n => hK _ (cylinder x (n + 1)).isOpen (cylinder_mem_self x _)⟩

theorem kernel_condition_compact {K : Set Cantor} {x : Cantor}
    (hK : CantorKernelCondition K x) : IsCompact K :=
  kernel_compact_of_finite_outside hK.1 ((kernel_condition_iff K x).mp hK).2

theorem kernel_condition_countable {K : Set Cantor} {x : Cantor}
    (hK : CantorKernelCondition K x) : K.Countable := by
  have hc : (⋃ n : ℕ, K \ (cylinder x (n + 1) : Set Cantor)).Countable :=
    countable_iUnion (fun n => (hK.2 n).countable)
  apply (hc.insert x).mono
  intro y hy
  by_cases hyx : y = x
  · exact Or.inl hyx
  · apply Or.inr
    obtain ⟨j, hj⟩ : ∃ j, y j ≠ x j := by
      by_contra h; push Not at h; exact hyx (funext h)
    exact mem_iUnion.mpr ⟨j, hy, fun h => hj (h j (Nat.lt_succ_self j))⟩

def sourcePoint (K : Set Cantor) (x : Cantor) (hK : CantorKernelCondition K x)
    (I : NullIdeal cantorMeasure)
    (hlo : (lowerIdeal cantorMeasure K).sets ⊆ I.sets)
    (hhi : I.sets ⊆ (upperIdeal cantorMeasure K).sets) : IdealPoint cantorMeasure where
  kernel := K
  label := x
  label_mem := hK.1
  finite_outside := ((kernel_condition_iff K x).mp hK).2
  compact := kernel_condition_compact hK
  ideal := I
  lower_bound := hlo
  upper_bound := hhi

theorem point_source_condition (p : IdealPoint cantorMeasure) :
    CantorKernelCondition p.kernel p.label :=
  (kernel_condition_iff _ _).mpr ⟨p.label_mem, p.finite_outside⟩

theorem point_reconstruction (p : IdealPoint cantorMeasure) :
    sourcePoint p.kernel p.label (point_source_condition p) p.ideal p.lower_bound p.upper_bound = p :=
  IdealPoint.ext rfl rfl rfl

theorem completed_cantor_mass (U : Set Cantor) :
    cantorMeasure.completion U = cantorMeasure U := Measure.completion_apply _ _

abbrev MaximalPoint (m : Measure Cantor) :=
  {p : WithScott (IdealPoint m) // ∀ q : IdealPoint m, WithScott.ofScott p ≤ q →
    q = WithScott.ofScott p}

def maximalEquiv (m : Measure Cantor) : Cantor ≃ MaximalPoint m where
  toFun x := ⟨WithScott.toScott (IdealPoint.e m x),
    (IdealPoint.maximal_iff _).mpr ⟨x, rfl⟩⟩
  invFun p := (WithScott.ofScott p.val).label
  left_inv _ := rfl
  right_inv p := by
    apply Subtype.ext
    change IdealPoint.e m (WithScott.ofScott p.val).label = WithScott.ofScott p.val
    exact p.property _ (IdealPoint.le_e_label _)

theorem maximalEquiv_continuous (m : Measure Cantor) :
    @Continuous Cantor (MaximalPoint m) (nullTopology m) _ (maximalEquiv m) := by
  have hc := e_continuous m
  letI : TopologicalSpace Cantor := nullTopology m
  exact hc.subtype_mk _

theorem maximalEquiv_symm_continuous (m : Measure Cantor) :
    @Continuous (MaximalPoint m) Cantor _ (nullTopology m) (maximalEquiv m).symm := by
  rw [continuous_def]
  intro U hU
  obtain ⟨O, hO, M, hM, rfl⟩ := hU
  let H : ScottOpens (IdealPoint m) := B m ⟨O, hO⟩ ⊓ A m M hM
  have he : (maximalEquiv m).symm ⁻¹' (O \ M) = Subtype.val ⁻¹' (H : Set _) := by
    ext p
    have hp : WithScott.ofScott p.val = IdealPoint.e m (WithScott.ofScott p.val).label :=
      (p.property _ (IdealPoint.le_e_label _)).symm
    change ((WithScott.ofScott p.val).label ∈ O ∧ (WithScott.ofScott p.val).label ∉ M) ↔
      (WithScott.ofScott p.val).kernel ⊆ O ∧ M ∈ (WithScott.ofScott p.val).ideal.sets
    rw [hp]
    simp only [IdealPoint.label_e, IdealPoint.kernel_e, singleton_subset_iff]
    change (_ ∧ _) ↔ (_ ∧ m M = 0 ∧ Disjoint M {_})
    simp [hM]
  rw [he]
  exact H.isOpen.preimage continuous_subtype_val

def maximalHomeomorph (m : Measure Cantor) :
    @Homeomorph Cantor (MaximalPoint m) (nullTopology m) _ :=
  @Homeomorph.mk Cantor (MaximalPoint m) (nullTopology m) _
    (maximalEquiv m) (maximalEquiv_continuous m) (maximalEquiv_symm_continuous m)

/-- Source Proposition 3.4, all Scott-open traces and the actual maximal subspace. -/
theorem source_trace :
    (∀ H : ScottOpens (IdealPoint cantorMeasure),
      (nullTopology cantorMeasure).IsOpen (trace H)) ∧
    (∃ h : @Homeomorph Cantor (MaximalPoint cantorMeasure) (nullTopology cantorMeasure) _,
      ∀ x, (h x).val = WithScott.toScott (IdealPoint.e cantorMeasure x)) :=
  ⟨trace_isOpen cantorMeasure, maximalHomeomorph cantorMeasure, fun _ => rfl⟩

/-- Source Lemma 2.1 with no extra inner-regularity hypothesis. -/
theorem source_measure_facts {Y : Type u} [MetricSpace Y] [CompactSpace Y]
    [MeasurableSpace Y] [BorelSpace Y] (ρ : Measure Y) [IsFiniteMeasure ρ] :
    (∀ {I : Type v} [Nonempty I] (V : I → Opens Y), Directed (· ≤ ·) V →
      ρ ((⨆ i, V i : Opens Y) : Set Y) = ⨆ i, ρ (V i : Set Y)) ∧
    (∀ E : Set Y, MeasurableSet E → 0 < ρ E →
      ∃ D : Set Y, D ⊆ E ∧ PositiveCarrier ρ D) :=
  radon_compact_metric ρ

end CantorFubini
