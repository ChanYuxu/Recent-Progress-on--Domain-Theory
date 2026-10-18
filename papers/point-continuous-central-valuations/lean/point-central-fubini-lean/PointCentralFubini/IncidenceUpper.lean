import PointCentralFubini.FinitePartition

/-! The finite-partition inequality in source Proposition 4.2. Representatives
are chosen within δ of the infimum on each atom. This gives the required
one-sided integral error directly, without adding a Radon assumption. -/
set_option autoImplicit false
open Set Topology TopologicalSpace MeasureTheory Filter
open scoped ENNReal BigOperators
universe u
namespace PointCentralFubini

variable {X : Type u} [TopologicalSpace X] [FirstCountableTopology X]

theorem exists_finite_test_approximation [Nonempty X] (m : TauMeasure X)
    (η : DValuation (Opens X)) (hη : η.Finite) (D : ℕ → Opens X)
    (δ : ℝ≥0∞) (hδ : δ ≠ 0) (n : ℕ) :
    ∃ ν : Valuation X,
      (∀ i : Fin n, ν (D i.val) = m.measure (D i.val : Set X)) ∧
      integral η (fun U => ν (WithScott.ofScott U)) ≤
        @lintegral X (borel X) m.measure (fun x => η (pointOpen x)) + δ * m.measure univ := by
  classical
  let C : Fin n → Opens X := fun i => D i.val
  let π := membershipPartition C
  obtain ⟨a,ha⟩ := π.exists_representatives (fun x => η (pointOpen x))
    (incidence_evaluation_ne_top η hη) δ hδ
  let ν : Valuation X := Valuation.simple Finset.univ (fun i => m.measure (π.cell i)) a
  refine ⟨ν,?_,?_⟩
  · intro i
    exact π.simple_exact m a (fun j hj => (ha j hj).1) (C i) (membershipPartition_decides C i)
  · exact π.simple_integral_bound m η a δ (fun i hi => (ha i hi).2)
      (incidence_evaluation_borel_measurable η)

theorem incidence_integral_upper_error [Nonempty X] (m : TauMeasure X)
    (C : Set (Opens X)) (hC : InnerSkeleton m C)
    (η : DValuation (Opens X)) (hη : η.Finite) (δ : ℝ≥0∞) (hδ : δ ≠ 0) :
    integral η (fun U => m.measure ((WithScott.ofScott U : Opens X) : Set X)) ≤
      @lintegral X (borel X) m.measure (fun x => η (pointOpen x)) + δ * m.measure univ := by
  classical
  obtain ⟨D,hCD⟩ := Set.countable_iff_exists_subset_range.mp hC.1
  choose ν hν hJ using (exists_finite_test_approximation m η hη D δ hδ)
  have hlim : ∀ U : Opens X, m.toValuation U ≤ ⨆ N : ℕ, ⨅ n ≥ N, ν n U := by
    intro U
    change m.measure (U : Set X) ≤ _
    rw [hC.2 U]
    apply iSup_le; intro V
    apply iSup_le; intro hVC
    apply iSup_le; intro hVU
    obtain ⟨k,rfl⟩ := hCD hVC
    apply le_iSup_of_le (k+1)
    apply le_iInf; intro n
    apply le_iInf; intro hn
    have hkn : k < n := by omega
    calc
      m.measure (D k : Set X) = ν n (D k) := (hν n ⟨k,hkn⟩).symm
      _ ≤ ν n U := (ν n).mono hVU
  have h := scott_fatou (Opens X) (completeLattice_isDcpo _) η
    m.toValuation.mass (fun n => (ν n).mass)
    m.toValuation.continuous (fun n => (ν n).continuous) hlim
  apply h.trans
  apply iSup_le; intro N
  exact (iInf_le_of_le N (iInf_le _ le_rfl)).trans (hJ N)

/-- The forward inequality of Proposition 4.2 under its exact inner-skeleton
hypothesis. No directedness or domination of the simple approximants is used. -/
theorem incidence_integral_upper (m : TauMeasure X) (C : Set (Opens X))
    (hC : InnerSkeleton m C) (η : DValuation (Opens X)) (hη : η.Finite) :
    integral η (fun U => m.measure ((WithScott.ofScott U : Opens X) : Set X)) ≤
      @lintegral X (borel X) m.measure (fun x => η (pointOpen x)) := by
  classical
  by_cases hX : Nonempty X
  · letI : Nonempty X := hX
    apply ENNReal.le_of_forall_pos_le_add
    intro ε hε _
    obtain ⟨δ,hδ,hδε⟩ := ENNReal.exists_nnreal_pos_mul_lt m.finite
      (show (ε : ℝ≥0∞) ≠ 0 from ENNReal.coe_ne_zero.mpr hε.ne')
    exact (incidence_integral_upper_error m C hC η hη δ
      (ENNReal.coe_ne_zero.mpr hδ.ne')).trans (add_le_add le_rfl hδε.le)
  · letI : IsEmpty X := not_nonempty_iff.mp hX
    have he : (fun U : WithScott (Opens X) =>
        m.measure ((WithScott.ofScott U : Opens X) : Set X)) = fun _ => 0 := by
      funext U
      have hU : ((WithScott.ofScott U : Opens X) : Set X) = ∅ :=
        eq_empty_iff_forall_notMem.mpr (fun x _ => isEmptyElim x)
      rw [hU,measure_empty]
    rw [he,integral_zero]
    exact zero_le _

end PointCentralFubini
