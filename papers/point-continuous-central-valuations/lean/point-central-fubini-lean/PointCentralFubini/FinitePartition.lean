import PointCentralFubini.SimpleValuation

/-! Finite Borel partitions and simple-valuation quadrature for Proposition 4.2. -/
set_option autoImplicit false
open Set Topology TopologicalSpace MeasureTheory Filter Function
open scoped ENNReal BigOperators
universe u v
namespace PointCentralFubini

structure BorelPartition (X : Type u) [TopologicalSpace X] (I : Type v) where
  cell : I → Set X
  measurable : ∀ i, MeasurableSet[borel X] (cell i)
  disjoint : Pairwise (Disjoint on cell)
  cover : (⋃ i, cell i) = univ

namespace BorelPartition
variable {X : Type u} [TopologicalSpace X] {I : Type v} [Fintype I]

def Decides (π : BorelPartition X I) (U : Set X) : Prop :=
  ∀ i, π.cell i ⊆ U ∨ π.cell i ⊆ Uᶜ

theorem sum_mass (π : BorelPartition X I) (m : TauMeasure X) :
    (∑ i, m.measure (π.cell i)) = m.measure univ := by
  letI : MeasurableSpace X := borel X
  have h := measure_iUnion (μ := m.measure) π.disjoint π.measurable
  rw [π.cover,tsum_fintype] at h
  exact h.symm

theorem sum_integral (π : BorelPartition X I) (m : TauMeasure X) (g : X → ℝ≥0∞) :
    (∑ i, @lintegral X (borel X) (m.measure.restrict (π.cell i)) g) =
      @lintegral X (borel X) m.measure g := by
  letI : MeasurableSpace X := borel X
  have h := lintegral_iUnion (μ := m.measure) π.measurable π.disjoint g
  rw [π.cover,setLIntegral_univ,tsum_fintype] at h
  exact h.symm

omit [Fintype I] in
theorem exists_representatives [Nonempty X] (π : BorelPartition X I)
    (g : X → ℝ≥0∞) (hfinite : ∀ x, g x ≠ ⊤) (δ : ℝ≥0∞) (hδ : δ ≠ 0) :
    ∃ a : I → X, ∀ i, (π.cell i).Nonempty →
      a i ∈ π.cell i ∧ ∀ x ∈ π.cell i, g (a i) ≤ g x + δ := by
  classical
  have h : ∀ i, ∃ a : X, (π.cell i).Nonempty →
      a ∈ π.cell i ∧ ∀ x ∈ π.cell i, g a ≤ g x + δ := by
    intro i
    by_cases hn : (π.cell i).Nonempty
    · obtain ⟨z,hz⟩ := hn
      have ht : (⨅ x : π.cell i, g x) ≠ ⊤ :=
        ne_top_of_le_ne_top (hfinite z) (iInf_le (fun y : π.cell i => g y) ⟨z,hz⟩)
      obtain ⟨a,ha⟩ := iInf_lt_iff.mp (ENNReal.lt_add_right ht hδ)
      exact ⟨a.val,fun _ => ⟨a.property,fun x hx =>
        ha.le.trans (add_le_add (iInf_le (fun y : π.cell i => g y) ⟨x,hx⟩) le_rfl)⟩⟩
    · exact ⟨Classical.choice inferInstance,fun h => False.elim (hn h)⟩
  exact Classical.axiomOfChoice h

theorem simple_exact (π : BorelPartition X I) (m : TauMeasure X) (a : I → X)
    (ha : ∀ i, (π.cell i).Nonempty → a i ∈ π.cell i) (U : Opens X)
    (hU : π.Decides (U : Set X)) :
    Valuation.simple Finset.univ (fun i => m.measure (π.cell i)) a U = m.measure (U : Set X) := by
  classical
  letI : MeasurableSpace X := borel X
  letI : BorelSpace X := ⟨rfl⟩
  have he : (U : Set X) = ⋃ i, (U : Set X) ∩ π.cell i := by
    rw [← inter_iUnion,π.cover,inter_univ]
  have hd : Pairwise (Disjoint on (fun i => (U : Set X) ∩ π.cell i)) :=
    fun i j hij => (π.disjoint hij).mono inter_subset_right inter_subset_right
  rw [Valuation.simple_apply,he,measure_iUnion hd
    (fun i => U.isOpen.measurableSet.inter (π.measurable i)),tsum_fintype]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hn : (π.cell i).Nonempty
  · rcases hU i with hi | hi
    · have hai : a i ∈ U := hi (ha i hn)
      rw [Valuation.dirac_apply,if_pos hai,mul_one,inter_eq_right.mpr hi]
    · have hnot : a i ∉ U := hi (ha i hn)
      have hE : (U : Set X) ∩ π.cell i = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        rintro x ⟨hxU,hxi⟩; exact hi hxi hxU
      rw [Valuation.dirac_apply,if_neg hnot,mul_zero,hE,measure_empty]
  · have hi : π.cell i = ∅ := not_nonempty_iff_eq_empty.mp hn
    simp only [hi,measure_empty,zero_mul,inter_empty]

theorem simple_integral_bound (π : BorelPartition X I) (m : TauMeasure X)
    (η : DValuation (Opens X)) (a : I → X) (δ : ℝ≥0∞)
    (ha : ∀ i, (π.cell i).Nonempty →
      ∀ x ∈ π.cell i, η (pointOpen (a i)) ≤ η (pointOpen x) + δ)
    (hg : @Measurable X ℝ≥0∞ (borel X) (borel ℝ≥0∞) (fun x => η (pointOpen x))) :
    integral η (fun U => Valuation.simple Finset.univ (fun i => m.measure (π.cell i)) a
      (WithScott.ofScott U)) ≤
      @lintegral X (borel X) m.measure (fun x => η (pointOpen x)) + δ * m.measure univ := by
  letI : MeasurableSpace X := borel X
  rw [Valuation.integral_simple_evaluation]
  calc
    _ ≤ ∑ i, ((∫⁻ x in π.cell i, η (pointOpen x) ∂m.measure) + δ * m.measure (π.cell i)) := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hn : (π.cell i).Nonempty
      · calc
          m.measure (π.cell i) * η (pointOpen (a i)) =
              ∫⁻ _ in π.cell i, η (pointOpen (a i)) ∂m.measure := by
            rw [setLIntegral_const,mul_comm]
          _ ≤ ∫⁻ x in π.cell i, (η (pointOpen x) + δ) ∂m.measure :=
            setLIntegral_mono' (π.measurable i) (ha i hn)
          _ = _ := by rw [lintegral_add_left hg,setLIntegral_const]
      · have hi : π.cell i = ∅ := not_nonempty_iff_eq_empty.mp hn
        simp only [hi,measure_empty,zero_mul,setLIntegral_empty,mul_zero,add_zero,le_refl]
    _ = _ := by rw [Finset.sum_add_distrib,← Finset.mul_sum,π.sum_mass,π.sum_integral]

end BorelPartition

def membershipAtom {X : Type u} [TopologicalSpace X] {n : ℕ}
    (C : Fin n → Opens X) (σ : Fin n → Bool) : Set X :=
  ⋂ i, if σ i then (C i : Set X) else (C i : Set X)ᶜ

def membershipPartition {X : Type u} [TopologicalSpace X] {n : ℕ}
    (C : Fin n → Opens X) : BorelPartition X (Fin n → Bool) where
  cell := membershipAtom C
  measurable σ := by
    letI : MeasurableSpace X := borel X
    letI : BorelSpace X := ⟨rfl⟩
    apply MeasurableSet.iInter
    intro i
    cases σ i <;> simp only [Bool.false_eq_true,if_false,if_true]
    · exact (C i).isOpen.measurableSet.compl
    · exact (C i).isOpen.measurableSet
  disjoint := by
    intro σ τ hστ
    obtain ⟨i,hi⟩ := Function.ne_iff.mp hστ
    apply Set.disjoint_left.mpr
    intro x hxσ hxτ
    have hσ := mem_iInter.mp hxσ i
    have hτ := mem_iInter.mp hxτ i
    cases hσi : σ i <;> cases hτi : τ i <;> simp_all
  cover := by
    classical
    apply eq_univ_iff_forall.mpr
    intro x
    refine mem_iUnion.mpr ⟨fun i => decide (x ∈ C i),mem_iInter.mpr ?_⟩
    intro i
    by_cases hx : x ∈ C i <;> simp [hx]

theorem membershipPartition_decides {X : Type u} [TopologicalSpace X] {n : ℕ}
    (C : Fin n → Opens X) (i : Fin n) : (membershipPartition C).Decides (C i : Set X) := by
  intro σ
  cases h : σ i
  · right
    intro x hx
    simpa only [h,Bool.false_eq_true,if_false] using (mem_iInter.mp hx i)
  · left
    intro x hx
    simpa only [h,if_true] using (mem_iInter.mp hx i)

end PointCentralFubini
