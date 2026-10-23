import CHFubini.RandomOpenContinuity
import CHFubini.MainStatement
import Mathlib.MeasureTheory.Group.AddCircle
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
Candidate numerical and fixed-point probability computations for source
`lem:rho-values`. The circle is the actual metric quotient `UnitAddCircle`,
its normalized Haar law is `volume`, and the sample law is `productLaw`.
-/

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal BigOperators

namespace CHFubini

theorem intervalLength_pos {ε : ℝ} (hε : 0 < ε) (n : ℕ) :
    0 < intervalLength ε n := by
  unfold intervalLength
  positivity

theorem intervalLength_nonneg {ε : ℝ} (hε : 0 ≤ ε) (n : ℕ) :
    0 ≤ intervalLength ε n := by
  unfold intervalLength
  positivity

theorem intervalLength_le_epsilon {ε : ℝ} (hε : 0 ≤ ε) (n : ℕ) :
    intervalLength ε n ≤ ε := by
  unfold intervalLength
  exact mul_le_of_le_one_right hε (pow_le_one₀ (by norm_num) (by norm_num))

theorem intervalLength_lt_one {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε < 1) (n : ℕ) :
    intervalLength ε n < 1 := (intervalLength_le_epsilon hε n).trans_lt hε1

theorem hasSum_intervalLength (ε : ℝ) : HasSum (intervalLength ε) ε := by
  convert hasSum_geometric_two.mul_left (ε / 2) using 1
  · funext n
    unfold intervalLength
    rw [pow_succ]
    ring
  · ring

theorem intervalFactors_multipliable (ε : ℝ) :
    Multipliable (fun n : ℕ => 1 - intervalLength ε n) := by
  have h := Real.multipliable_one_add_of_summable (hasSum_intervalLength ε).summable.neg
  exact h.congr (fun _ => by ring)

/-- Elementary union bound, proved for every finite product. -/
theorem one_sub_prod_one_sub_le_sum {ι : Type*} (f : ι → ℝ)
    (hf0 : ∀ i, 0 ≤ f i) (hf1 : ∀ i, f i ≤ 1) (s : Finset ι) :
    1 - ∏ i ∈ s, (1 - f i) ≤ ∑ i ∈ s, f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha]
      have hprod : ∏ i ∈ s, (1 - f i) ≤ 1 :=
        Finset.prod_le_one (fun i _ => sub_nonneg.mpr (hf1 i))
          (fun i _ => by linarith [hf0 i])
      have hmul := mul_le_of_le_one_right (hf0 a) hprod
      nlinarith

theorem intervalFactors_tprod_nonneg {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε < 1) :
    0 ≤ ∏' n : ℕ, (1 - intervalLength ε n) := by
  apply le_hasProd_of_le_prod (intervalFactors_multipliable ε).hasProd
  intro s
  exact Finset.prod_nonneg (fun n _ => (sub_pos.mpr (intervalLength_lt_one hε hε1 n)).le)

theorem intervalFactors_tprod_lower {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε < 1) :
    1 - ε ≤ ∏' n : ℕ, (1 - intervalLength ε n) := by
  apply le_hasProd_of_le_prod (intervalFactors_multipliable ε).hasProd
  intro s
  have hsum : ∑ n ∈ s, intervalLength ε n ≤ ε := by
    simpa only [(hasSum_intervalLength ε).tsum_eq] using
      (hasSum_intervalLength ε).summable.sum_le_tsum s
        (fun n _ => intervalLength_nonneg hε n)
  have hfinite := one_sub_prod_one_sub_le_sum (intervalLength ε)
    (intervalLength_nonneg hε) (fun n => (intervalLength_lt_one hε hε1 n).le) s
  linarith

theorem intervalFactors_tprod_upper {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε < 1) :
    (∏' n : ℕ, (1 - intervalLength ε n)) ≤ 1 - intervalLength ε 0 := by
  have he : ∀ᶠ s : Finset ℕ in atTop,
      (∏ n ∈ s, (1 - intervalLength ε n)) ≤ 1 - intervalLength ε 0 := by
    refine eventually_atTop.mpr ⟨{0}, fun s hs => ?_⟩
    have h := Finset.prod_le_prod_of_subset_of_le_one hs
      (fun n _ => (sub_pos.mpr (intervalLength_lt_one hε hε1 n)).le)
      (fun n _ _ => by linarith [intervalLength_nonneg hε n])
    simpa using h
  exact le_of_tendsto (intervalFactors_multipliable ε).hasProd he

/-- All exact numerical inequalities in the manuscript, including the
positive first-coordinate lower bound. -/
theorem qEpsilon_bounds {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    intervalLength ε 0 ≤ qEpsilon ε ∧ 0 < qEpsilon ε ∧ qEpsilon ε ≤ ε ∧
      qEpsilon ε < 1 := by
  have hlow := intervalFactors_tprod_lower hε.le hε1
  have hupp := intervalFactors_tprod_upper hε.le hε1
  have hfirst := intervalLength_pos hε 0
  unfold qEpsilon
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

/-- `ofReal` preserves this infinite product, justified from the actual
multipliability proof and nonnegative factors. -/
theorem intervalFactors_hasProd_ofReal {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε < 1) :
    HasProd (fun n : ℕ => ENNReal.ofReal (1 - intervalLength ε n))
      (ENNReal.ofReal (∏' n : ℕ, (1 - intervalLength ε n))) := by
  have h := ENNReal.tendsto_ofReal (intervalFactors_multipliable ε).hasProd
  unfold HasProd
  convert h using 1
  funext s
  exact (ENNReal.ofReal_prod_of_nonneg
    (fun n _ => (sub_pos.mpr (intervalLength_lt_one hε hε1 n)).le)).symm

instance circleVolume_probability : IsProbabilityMeasure (volume : Measure UnitAddCircle) where
  measure_univ := UnitAddCircle.measure_univ

/-- The paper's radii `ell_n/2`, with positive-integer indexing shifted. -/
noncomputable def circleRadius (ε : ℝ) (n : ℕ) : ℝ := intervalLength ε n / 2

theorem circleRadius_pos {ε : ℝ} (hε : 0 < ε) (n : ℕ) : 0 < circleRadius ε n :=
  div_pos (intervalLength_pos hε n) (by norm_num)

theorem volume_circle_ball {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε < 1)
    (t : UnitAddCircle) (n : ℕ) :
    volume (Metric.ball t (circleRadius ε n)) = ENNReal.ofReal (intervalLength ε n) := by
  rw [← (AddCircle.closedBall_ae_eq_ball (x := t) (ε := circleRadius ε n)).measure_eq,
    AddCircle.volume_closedBall]
  have hlen := intervalLength_lt_one hε hε1 n
  have hrad : 2 * circleRadius ε n = intervalLength ε n := by unfold circleRadius; ring
  rw [hrad, min_eq_right hlen.le]

def pointHit (ε : ℝ) (t : UnitAddCircle) : Set (ℕ → UnitAddCircle) :=
  {s | t ∈ randomBallUnion (circleRadius ε) s}

theorem pointHit_isOpen (ε : ℝ) (t : UnitAddCircle) : IsOpen (pointHit ε t) :=
  randomBallUnion_incidence_isOpen (circleRadius ε) t

theorem pointHit_compl_eq_pi (ε : ℝ) (t : UnitAddCircle) :
    (pointHit ε t)ᶜ = Set.pi univ (fun n => (Metric.ball t (circleRadius ε n))ᶜ) := by
  ext s
  simp [pointHit, randomBallUnion, Set.mem_pi, Metric.mem_ball, dist_comm]

/-- Exact fixed-point coverage probability under the actual iid circle law.
No conditional independence on a carrier is used anywhere in this proof. -/
theorem pointHit_probability {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) (t : UnitAddCircle) :
    productLaw (volume : Measure UnitAddCircle) (pointHit ε t) =
      ENNReal.ofReal (qEpsilon ε) := by
  have hmiss : productLaw (volume : Measure UnitAddCircle) (pointHit ε t)ᶜ =
      ENNReal.ofReal (∏' n : ℕ, (1 - intervalLength ε n)) := by
    rw [pointHit_compl_eq_pi, productLaw,
      Measure.infinitePi_pi_univ (fun _ : ℕ => (volume : Measure UnitAddCircle))
        (fun _ => measurableSet_ball.compl)]
    calc
      (∏' n : ℕ, volume (Metric.ball t (circleRadius ε n))ᶜ) =
          ∏' n : ℕ, ENNReal.ofReal (1 - intervalLength ε n) := by
        apply tprod_congr
        intro n
        rw [prob_compl_eq_one_sub measurableSet_ball, volume_circle_ball hε.le hε1]
        simpa using (ENNReal.ofReal_sub 1 (intervalLength_nonneg hε.le n)).symm
      _ = ENNReal.ofReal (∏' n : ℕ, (1 - intervalLength ε n)) :=
        (intervalFactors_hasProd_ofReal hε.le hε1).tprod_eq
  calc
    productLaw (volume : Measure UnitAddCircle) (pointHit ε t) =
        1 - productLaw (volume : Measure UnitAddCircle) (pointHit ε t)ᶜ := by
      simpa only [compl_compl] using
        prob_compl_eq_one_sub (μ := productLaw (volume : Measure UnitAddCircle))
          (pointHit_isOpen ε t).measurableSet.compl
    _ = 1 - ENNReal.ofReal (∏' n : ℕ, (1 - intervalLength ε n)) := by rw [hmiss]
    _ = ENNReal.ofReal (qEpsilon ε) := by
      unfold qEpsilon
      simpa using
        (ENNReal.ofReal_sub 1 (intervalFactors_tprod_nonneg hε.le hε1)).symm

theorem randomBallUnion_volume_le_epsilon {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε < 1)
    (s : ℕ → UnitAddCircle) :
    volume (randomBallUnion (circleRadius ε) s) ≤ ENNReal.ofReal ε := by
  calc
    volume (randomBallUnion (circleRadius ε) s) ≤
        ∑' n : ℕ, volume (Metric.ball (s n) (circleRadius ε n)) := measure_iUnion_le _
    _ = ∑' n : ℕ, ENNReal.ofReal (intervalLength ε n) := by
      apply tsum_congr
      intro n
      exact volume_circle_ball hε hε1 (s n) n
    _ = ENNReal.ofReal (∑' n : ℕ, intervalLength ε n) :=
      (ENNReal.ofReal_tsum_of_nonneg (intervalLength_nonneg hε)
        (hasSum_intervalLength ε).summable).symm
    _ = ENNReal.ofReal ε := by rw [(hasSum_intervalLength ε).tsum_eq]

end CHFubini

#print axioms CHFubini.qEpsilon_bounds
#print axioms CHFubini.pointHit_probability
#print axioms CHFubini.randomBallUnion_volume_le_epsilon

