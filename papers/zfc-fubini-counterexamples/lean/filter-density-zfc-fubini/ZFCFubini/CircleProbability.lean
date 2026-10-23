import ZFCFubini.RandomOpen
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Analysis.SpecificLimits.Basic

/-!
Circle ball lengths, union bound and exact fixed-point coverage probability.
Adapted elementary proofs from CHFubini/CircleProbability.lean, SHA256
5254cd3a8eef09f043589c15c9699d983d8ee1fafe15da9e84a23603b615bead.
Actual source radii and epsilon are instantiated below; no CH result is used.
-/

set_option autoImplicit false
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal BigOperators

namespace ZFCFubini

noncomputable def intervalLength (ε : ℝ) (n : ℕ) : ℝ := ε * (1 / 2 : ℝ) ^ (n + 1)
noncomputable def qEpsilon (ε : ℝ) : ℝ := 1 - ∏' n : ℕ, (1 - intervalLength ε n)

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

def ballPointHit (ε : ℝ) (t : UnitAddCircle) : Set (ℕ → UnitAddCircle) :=
  {s | t ∈ randomBallUnion (circleRadius ε) s}

theorem ballPointHit_isOpen (ε : ℝ) (t : UnitAddCircle) : IsOpen (ballPointHit ε t) :=
  randomBallUnion_incidence_isOpen (circleRadius ε) t

theorem ballPointHit_compl_eq_pi (ε : ℝ) (t : UnitAddCircle) :
    (ballPointHit ε t)ᶜ = Set.pi univ (fun n => (Metric.ball t (circleRadius ε n))ᶜ) := by
  ext s
  simp [ballPointHit, randomBallUnion, Set.mem_pi, Metric.mem_ball, dist_comm]

/-- Exact fixed-point coverage probability under the actual iid circle law.
No conditional independence on a carrier is used anywhere in this proof. -/
theorem ballPointHit_probability {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) (t : UnitAddCircle) :
    parameterMeasure (ballPointHit ε t) =
      ENNReal.ofReal (qEpsilon ε) := by
  have hmiss : parameterMeasure (ballPointHit ε t)ᶜ =
      ENNReal.ofReal (∏' n : ℕ, (1 - intervalLength ε n)) := by
    rw [ballPointHit_compl_eq_pi, parameterMeasure,
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
    parameterMeasure (ballPointHit ε t) =
        1 - parameterMeasure (ballPointHit ε t)ᶜ := by
      simpa only [compl_compl] using
        prob_compl_eq_one_sub (μ := parameterMeasure)
          (ballPointHit_isOpen ε t).measurableSet.compl
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


/-- The exact source mass bound. -/
noncomputable def epsilon : ℝ := 1 / 64

theorem epsilon_pos : 0 < epsilon := by norm_num [epsilon]
theorem epsilon_lt_one : epsilon < 1 := by norm_num [epsilon]

theorem twice_radius_eq_intervalLength (n : ℕ) :
    2 * radius n = intervalLength epsilon n := by
  have he : n + 8 = (n + 1) + 7 := by omega
  unfold radius intervalLength epsilon
  rw [he, pow_add]
  norm_num
  ring

theorem circleRadius_epsilon_eq_radius (n : ℕ) : circleRadius epsilon n = radius n := by
  unfold circleRadius
  rw [← twice_radius_eq_intervalLength]
  ring

theorem hasSum_twice_radius : HasSum (fun n => 2 * radius n) epsilon := by
  simpa only [twice_radius_eq_intervalLength] using hasSum_intervalLength epsilon

theorem volume_radius_ball (y : Circle) (n : ℕ) :
    volume (Metric.ball y (radius n)) = ENNReal.ofReal (2 * radius n) := by
  rw [twice_radius_eq_intervalLength, ← circleRadius_epsilon_eq_radius]
  exact volume_circle_ball epsilon_pos.le epsilon_lt_one y n

theorem randomOpen_volume_le_epsilon (t : Omega) :
    volume (randomOpen t : Set Circle) ≤ ENNReal.ofReal epsilon := by
  have he : circleRadius epsilon = radius := funext circleRadius_epsilon_eq_radius
  change volume (randomBallUnion radius t) ≤ _
  rw [← he]
  exact randomBallUnion_volume_le_epsilon epsilon_pos.le epsilon_lt_one t

def pointHit (y : Circle) : Set Omega := {t | y ∈ randomOpen t}

theorem pointHit_isOpen (y : Circle) : IsOpen (pointHit y) :=
  randomOpen_incidence_isOpen y

noncomputable def q : ℝ := qEpsilon epsilon

theorem q_source : q = 1 - ∏' n : ℕ, (1 - 2 * radius n) := by
  unfold q qEpsilon
  simp only [twice_radius_eq_intervalLength]

theorem q_bounds : 0 < q ∧ q ≤ 1 / 64 := by
  have h := qEpsilon_bounds epsilon_pos epsilon_lt_one
  exact ⟨h.2.1, h.2.2.1⟩

theorem pointHit_probability (y : Circle) :
    parameterMeasure (pointHit y) = ENNReal.ofReal q := by
  have he : circleRadius epsilon = radius := funext circleRadius_epsilon_eq_radius
  have h := ballPointHit_probability epsilon_pos epsilon_lt_one y
  simpa only [ballPointHit, pointHit, he, randomOpen, randomOpenPullback, id_eq,
    preimage_id, q] using h

/-- Finite-coordinate independence forces the forbidden ordinary closed set
outside a positive sample union to be Haar null. Adapted from the elementary
part of CHFubini/DenseIncidence.lean, SHA256
9390c441bcaaef7a404b1287de4050ab5cbe4c56afff1b1d2346659e0db7e53b.
No independence on a compact carrier is asserted or used. -/
theorem randomOpen_forbidden_union_null {W : Set Omega}
    (hW : 0 < parameterMeasure W) :
    volume ((⋃ t ∈ W, (randomOpen t : Set Circle))ᶜ) = 0 := by
  let N : Set Circle := (⋃ t ∈ W, (randomOpen t : Set Circle))ᶜ
  have hNm : MeasurableSet N :=
    (isOpen_iUnion (fun t => isOpen_iUnion (fun _ => (randomOpen t).isOpen))).isClosed_compl.measurableSet
  change volume N = 0
  by_contra hN
  have hcomp : volume Nᶜ < 1 :=
    lt_of_le_of_ne prob_le_one (fun h => hN ((prob_compl_eq_one_iff hNm).mp h))
  have hbound (k : ℕ) : parameterMeasure W ≤ (volume Nᶜ) ^ k := by
    have hsub : W ⊆ Set.pi (Finset.range k : Set ℕ) (fun _ => Nᶜ) := by
      intro t ht n _
      change t n ∉ N
      intro hn
      exact hn (mem_iUnion.mpr ⟨t, mem_iUnion.mpr ⟨ht, randomOpen_contains_coordinate t n⟩⟩)
    calc
      parameterMeasure W ≤ parameterMeasure (Set.pi (Finset.range k : Set ℕ) (fun _ => Nᶜ)) :=
        measure_mono hsub
      _ = (volume Nᶜ) ^ k := by
        rw [parameterMeasure, Measure.infinitePi_pi (fun _ : ℕ => (volume : Measure Circle))
          (fun _ _ => hNm.compl)]
        simp
  exact (not_le_of_gt hW)
    (ge_of_tendsto' (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hcomp) hbound)

/-- Source `lem:hitting`, with the ordinary relative topology and ambient
product Haar measure. The exceptional set is the printed countable union of
closed forbidden sets associated with a countable base of `D`. -/
theorem hitting_lemma {D : Set Omega} (hD : PositiveCarrier parameterMeasure D) :
    ∃ N : Set Circle, MeasurableSet N ∧ volume N = 0 ∧ ∀ y ∉ N,
      IsOpen {t : D | y ∈ randomOpen t.1} ∧ Dense {t : D | y ∈ randomOpen t.1} := by
  classical
  let B := countableBasis D
  let forbidden (b : B) : Set Circle :=
    (⋃ t ∈ Subtype.val '' b.1, (randomOpen t : Set Circle))ᶜ
  have hfm (b : B) : MeasurableSet (forbidden b) :=
    (isOpen_iUnion (fun t => isOpen_iUnion (fun _ => (randomOpen t).isOpen))).isClosed_compl.measurableSet
  have hf0 (b : B) : volume (forbidden b) = 0 := by
    apply randomOpen_forbidden_union_null
    exact hD.2.2 b.1 (isOpen_of_mem_countableBasis b.2)
      (nonempty_of_mem_countableBasis b.2)
  let N : Set Circle := ⋃ b : B, forbidden b
  refine ⟨N, MeasurableSet.iUnion hfm, measure_iUnion_null hf0, fun y hy => ?_⟩
  refine ⟨(randomOpen_incidence_isOpen y).preimage continuous_subtype_val, ?_⟩
  apply (isBasis_countableBasis D).dense_iff.mpr
  intro W hW _
  have hyf : y ∉ forbidden ⟨W, hW⟩ :=
    fun h => hy (mem_iUnion.mpr ⟨⟨W, hW⟩, h⟩)
  have hyunion : y ∈ ⋃ t ∈ Subtype.val '' W, (randomOpen t : Set Circle) := by
    simpa only [forbidden, mem_compl_iff, not_not] using hyf
  obtain ⟨t, htW, hyt⟩ := mem_iUnion₂.mp hyunion
  obtain ⟨d, hdW, rfl⟩ := htW
  exact ⟨d, hdW, hyt⟩

/-- The last assertion of source `lem:hitting` uses only a finite intersection
of dense relatively open hitting sets; no Baire theorem is needed. -/
theorem hitting_finite {D : Set Omega} {N : Set Circle}
    (hgood : ∀ y ∉ N, IsOpen {t : D | y ∈ randomOpen t.1} ∧
      Dense {t : D | y ∈ randomOpen t.1})
    {F : Set Circle} (hF : F.Finite) (hFN : Disjoint F N)
    {W : Set D} (hWo : IsOpen W) (hWn : W.Nonempty) :
    ∃ t ∈ W, F ⊆ randomOpen t.1 := by
  classical
  have hfinite : ∀ S : Finset Circle, (↑S : Set Circle) ⊆ F →
      IsOpen {t : D | ∀ y ∈ S, y ∈ randomOpen t.1} ∧
      Dense {t : D | ∀ y ∈ S, y ∈ randomOpen t.1} := by
    intro S
    induction S using Finset.induction_on with
    | empty => intro _; simp only [Finset.notMem_empty, IsEmpty.forall_iff, implies_true,
        setOf_true]; exact ⟨isOpen_univ, dense_univ⟩
    | @insert a S ha ih =>
      intro hSF
      have haF : a ∈ F := hSF (by simp)
      have haN : a ∉ N := fun haN => (disjoint_left.mp hFN) haF haN
      have hS := ih (fun y hy => hSF (by simp [hy]))
      have he : {t : D | ∀ y ∈ insert a S, y ∈ randomOpen t.1} =
          {t : D | a ∈ randomOpen t.1} ∩ {t : D | ∀ y ∈ S, y ∈ randomOpen t.1} := by
        ext t; simp
      rw [he]
      exact ⟨(hgood a haN).1.inter hS.1,
        (hgood a haN).2.inter_of_isOpen_left hS.2 (hgood a haN).1⟩
  have hAll := hfinite hF.toFinset (by simp)
  obtain ⟨t, htW, htAll⟩ := hAll.2.inter_open_nonempty W hWo hWn
  exact ⟨t, htW, fun y hy => htAll y (by simpa using hy)⟩

end ZFCFubini

