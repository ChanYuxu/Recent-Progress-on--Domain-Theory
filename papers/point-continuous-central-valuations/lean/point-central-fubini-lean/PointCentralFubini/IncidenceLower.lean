import PointCentralFubini.IncidenceMeasure
import PointCentralFubini.ValuationLimits

/-! The Radon--Nikodym/support inequality in source Proposition 4.2. -/
set_option autoImplicit false
open Set Topology TopologicalSpace MeasureTheory Filter
open scoped ENNReal
universe u
namespace PointCentralFubini

variable {X : Type u} [TopologicalSpace X] [FirstCountableTopology X]
attribute [local instance] Classical.propDecidable

/-- Normalize restricted neighbourhood measures at a support point and apply
Scott--Fatou to the resulting probability valuations. -/
theorem incidence_evaluation_le_of_local_averages (m : TauMeasure X)
    (η : DValuation (Opens X)) (B : Set X) (hB : MeasurableSet[borel X] B)
    (a : ℝ≥0∞)
    (havg : ∀ V : Opens X, integral η (incidenceRestriction m (B ∩ V)) ≤
      a * m.measure (B ∩ V)) {x : X} (hx : x ∈ (m.restrict B hB).support) :
    η (pointOpen x) ≤ a := by
  letI : MeasurableSpace X := borel X
  letI : BorelSpace X := ⟨rfl⟩
  obtain ⟨W,hW,hbasis⟩ := (nhds_basis_opens x).exists_antitone_subbasis
  let V : ℕ → Opens X := fun n => ⟨W n,(hW n).2⟩
  have hxV : ∀ n, x ∈ V n := fun n => (hW n).1
  have hpos : ∀ n, 0 < m.measure (B ∩ V n) := by
    intro n
    have h := ((m.restrict B hB).mem_support_iff x).mp hx (V n) (hxV n)
    simpa only [TauMeasure.restrict_apply,inter_comm] using h
  have hfin : ∀ n, m.measure (B ∩ V n) ≠ ⊤ := fun n =>
    ne_top_of_le_ne_top m.finite (measure_mono (subset_univ _))
  let hBV : ∀ n, MeasurableSet (B ∩ V n) := fun n => hB.inter (V n).isOpen.measurableSet
  let ρ : ℕ → Valuation X := fun n =>
    (m.restrict (B ∩ V n) (hBV n)).toValuation.scale (m.measure (B ∩ V n))⁻¹
  have hlim : ∀ U : Opens X, Valuation.dirac x U ≤ ⨆ N : ℕ, ⨅ n ≥ N, ρ n U := by
    intro U
    by_cases hxU : x ∈ U
    · obtain ⟨N,hNU⟩ := hbasis.mem_iff.mp (U.isOpen.mem_nhds hxU)
      rw [Valuation.dirac_apply,if_pos hxU]
      apply le_iSup_of_le N
      apply le_iInf; intro n
      apply le_iInf; intro hn
      have hVnU : (V n : Set X) ⊆ U := (hbasis.2 hn).trans hNU
      change 1 ≤ (m.measure (B ∩ V n))⁻¹ *
        (m.restrict (B ∩ V n) (hBV n)).measure (U : Set X)
      rw [TauMeasure.restrict_apply,inter_eq_right.mpr (inter_subset_right.trans hVnU),
        ENNReal.inv_mul_cancel (hpos n).ne' (hfin n)]
    · simp only [Valuation.dirac_apply,if_neg hxU,zero_le]
  have hρ : ∀ n, integral η (fun U => ρ n (WithScott.ofScott U)) ≤ a := by
    intro n
    have he : (fun U : WithScott (Opens X) => ρ n (WithScott.ofScott U)) =
        fun U => (m.measure (B ∩ V n))⁻¹ * incidenceRestriction m (B ∩ V n) U := by
      funext U
      exact congrArg ((m.measure (B ∩ V n))⁻¹ * ·)
        (TauMeasure.restrict_apply m _ (hBV n) (WithScott.ofScott U))
    rw [he,fpr_integral_smul η _ _ (incidenceRestriction_isLSC m (hBV n))]
    calc
      _ ≤ (m.measure (B ∩ V n))⁻¹ * (a * m.measure (B ∩ V n)) := by
        gcongr
        exact havg (V n)
      _ = a := by rw [mul_left_comm,ENNReal.inv_mul_cancel (hpos n).ne' (hfin n),mul_one]
  have h := scott_fatou (Opens X) (completeLattice_isDcpo _) η
    (Valuation.dirac x).mass (fun n => (ρ n).mass)
    (Valuation.dirac x).continuous (fun n => (ρ n).continuous) hlim
  rw [Valuation.integral_dirac_evaluation] at h
  apply h.trans
  apply iSup_le; intro N
  exact (iInf_le_of_le N (iInf_le _ le_rfl)).trans (hρ N)

/-- The incidence evaluation is bounded by the RN density almost everywhere.
Rational level sets supply the countable exceptional union. -/
theorem incidence_evaluation_ae_le_rnDeriv (m : TauMeasure X)
    (η : DValuation (Opens X)) (hη : η.Finite) :
    ∀ᵐ x ∂m.measure, η (pointOpen x) ≤ (incidenceMeasure m η).rnDeriv m.measure x := by
  letI : MeasurableSpace X := borel X
  letI : BorelSpace X := ⟨rfl⟩
  let f := (incidenceMeasure m η).rnDeriv m.measure
  have hf : Measurable f := Measure.measurable_rnDeriv _ _
  have hq : ∀ q : ℚ, ∀ᵐ x ∂m.measure,
      f x < (Real.toNNReal q : ℝ≥0∞) → η (pointOpen x) ≤ (Real.toNNReal q : ℝ≥0∞) := by
    intro q
    let a : ℝ≥0∞ := Real.toNNReal q
    let B : Set X := {x | f x < a}
    have hB : MeasurableSet B := measurableSet_lt hf measurable_const
    have havg : ∀ V : Opens X, integral η (incidenceRestriction m (B ∩ V)) ≤
        a * m.measure (B ∩ V) := by
      intro V
      have hBV : MeasurableSet (B ∩ V) := hB.inter V.isOpen.measurableSet
      rw [← incidenceMeasure_rnDeriv m η hη _ hBV]
      change (∫⁻ x in B ∩ V, f x ∂m.measure) ≤ _
      calc
        _ ≤ ∫⁻ _ in B ∩ V, a ∂m.measure :=
          setLIntegral_mono' hBV (fun x hx => hx.1.le)
        _ = a * m.measure (B ∩ V) := setLIntegral_const _ _
    have hs : ∀ᵐ x ∂(m.restrict B hB).measure, x ∈ (m.restrict B hB).support :=
      mem_ae_iff.mpr (m.restrict B hB).support_compl_null
    have hg : ∀ᵐ x ∂m.measure.restrict B, η (pointOpen x) ≤ a :=
      hs.mono (fun _ hx => incidence_evaluation_le_of_local_averages m η B hB a havg hx)
    exact (ae_restrict_iff' hB).mp hg
  filter_upwards [ae_all_iff.mpr hq] with x hx
  by_contra hle
  obtain ⟨q,_,hfq,hqg⟩ := ENNReal.lt_iff_exists_rat_btwn.mp (lt_of_not_ge hle)
  exact not_le_of_gt hqg (hx q hfq)

/-- The reverse inequality of source Proposition 4.2. The countable inner
skeleton is needed only for the other inequality. -/
theorem incidence_integral_lower (m : TauMeasure X) (η : DValuation (Opens X))
    (hη : η.Finite) :
    @lintegral X (borel X) m.measure (fun x => η (pointOpen x)) ≤
      integral η (fun U => m.measure ((WithScott.ofScott U : Opens X) : Set X)) := by
  letI : MeasurableSpace X := borel X
  letI : IsFiniteMeasure m.measure := ⟨m.finite.lt_top⟩
  letI : IsFiniteMeasure (incidenceMeasure m η) := ⟨(incidenceMeasure_finite m η hη).lt_top⟩
  calc
    _ ≤ ∫⁻ x, (incidenceMeasure m η).rnDeriv m.measure x ∂m.measure :=
      lintegral_mono_ae (incidence_evaluation_ae_le_rnDeriv m η hη)
    _ = incidenceMeasure m η univ :=
      Measure.lintegral_rnDeriv (incidenceMeasure_absolutelyContinuous m η)
    _ = integral η (incidenceRestriction m univ) :=
      incidenceMeasure_apply m η MeasurableSet.univ
    _ = _ := by apply integral_congr η; intro U; simp [incidenceRestriction]

end PointCentralFubini
