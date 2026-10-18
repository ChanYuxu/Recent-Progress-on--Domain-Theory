import Practice.DomainTheory.Papers.LipschitzYonedaFinalTopology.QuasiMetric

/-!
# A non-Yoneda-complete space with property D

This module formalizes the order-quasi-metric example from source lines
1057--1095.  On `ℕ`, distance is zero in the order direction and infinity
otherwise.  The identity sequence is Cauchy but has no `d`-limit.  For every
positive finite constant, the Lipschitz condition is exactly monotonicity, so
all positive layers coincide and property D is tautological.
-/

set_option autoImplicit false
set_option linter.unnecessarySimpa false

open Set Function
open scoped NNReal ENNReal

namespace LipschitzYonedaFinalTopology
namespace QuasiMetric

/-- The order quasi-metric on the natural numbers. -/
def natOrder : QuasiMetric ℕ where
  edist m n := if m ≤ n then 0 else ∞
  edist_self n := by simp
  edist_triangle m n k := by
    by_cases hmk : m ≤ k
    · simp [hmk]
    · by_cases hmn : m ≤ n
      · have hnk : ¬n ≤ k := fun h ↦ hmk (hmn.trans h)
        simp [hmk, hmn, hnk]
      · simp [hmk, hmn]
  eq_of_edist_zero := by
    intro m n hmn hnm
    have hmn_le : m ≤ n := by
      by_contra h
      simp [h] at hmn
    have hnm_le : n ≤ m := by
      by_contra h
      simp [h] at hnm
    exact Nat.le_antisymm hmn_le hnm_le

@[simp]
theorem natOrder_edist_eq_zero_iff (m n : ℕ) :
    natOrder.edist m n = 0 ↔ m ≤ n := by
  simp [natOrder]

@[simp]
theorem natOrder_edist_eq_top_iff (m n : ℕ) :
    natOrder.edist m n = ∞ ↔ ¬m ≤ n := by
  simp [natOrder]

/-- The increasing identity sequence is Cauchy for the order quasi-metric. -/
theorem natOrder_id_isCauchyNet :
    natOrder.IsCauchyNet (fun n : ℕ ↦ n) := by
  intro ε hε
  refine ⟨0, ?_⟩
  intro i j _hi hij
  simp [natOrder, hij, ENNReal.coe_pos.mpr hε]

/-- At every proposed limit `x`, the limsup of the distances from the identity
sequence to `x` is infinity. -/
theorem natOrder_id_netLimsup (x : ℕ) :
    netLimsup (fun n : ℕ ↦ natOrder.edist n x) = ∞ := by
  apply top_unique
  apply le_iInf
  intro i
  let j : ℕ := max i (x + 1)
  have hij : i ≤ j := le_max_left _ _
  have hxj : x < j :=
    (Nat.lt_succ_self x).trans_le (le_max_right i (x + 1))
  calc
    ∞ = natOrder.edist j x := by
      simp [natOrder, Nat.not_le.mpr hxj]
    _ ≤ ⨆ (_h : i ≤ j), natOrder.edist j x :=
      le_iSup (fun _h : i ≤ j ↦ natOrder.edist j x) hij
    _ ≤ ⨆ k : ℕ, ⨆ (_h : i ≤ k), natOrder.edist k x :=
      le_iSup (fun k : ℕ ↦ ⨆ (_h : i ≤ k), natOrder.edist k x) j

/-- The Cauchy identity sequence has no `d`-limit. -/
theorem natOrder_id_has_no_dLimit :
    ¬∃ x : ℕ, natOrder.IsDLimit (fun n : ℕ ↦ n) x := by
  rintro ⟨x, hx⟩
  have h := hx x
  rw [natOrder.edist_self, natOrder_id_netLimsup] at h
  exact ENNReal.zero_ne_top h

/-- The order quasi-metric on `ℕ` is not Yoneda-complete. -/
theorem natOrder_not_yonedaComplete : ¬natOrder.IsYonedaComplete := by
  intro hcomplete
  obtain ⟨x, hx⟩ := hcomplete ℕ (fun n : ℕ ↦ n)
    ⟨inferInstance, fun i j ↦ ⟨max i j, le_max_left _ _, le_max_right _ _⟩⟩
    natOrder_id_isCauchyNet
  exact natOrder_id_has_no_dLimit ⟨x, hx⟩

/-- For every positive finite constant, the Lipschitz condition is exactly
monotonicity. -/
theorem natOrder_isLipschitz_iff_monotone
    {α : ℝ≥0} (hα : 0 < α) (f : ℕ → ℝ≥0∞) :
    natOrder.IsLipschitz α f ↔ Monotone f := by
  constructor
  · intro hf m n hmn
    have h := hf m n
    change f m - f n ≤ (α : ℝ≥0∞) * natOrder.edist m n at h
    rw [(natOrder_edist_eq_zero_iff m n).mpr hmn, mul_zero] at h
    exact tsub_eq_zero_iff_le.mp (le_antisymm h (zero_le _))
  · intro hf m n
    change f m - f n ≤ (α : ℝ≥0∞) * natOrder.edist m n
    by_cases hmn : m ≤ n
    · rw [(natOrder_edist_eq_zero_iff m n).mpr hmn, mul_zero]
      exact (tsub_eq_zero_iff_le.mpr (hf hmn)).le
    · rw [(natOrder_edist_eq_top_iff m n).mpr hmn]
      simp [ENNReal.coe_ne_zero.mpr hα.ne']

/-- Membership in any two positive layers is identical. -/
theorem natOrder_inLayer_iff_inLayer
    {α β : ℝ≥0} (hα : 0 < α) (hβ : 0 < β)
    (f : natOrder.LSpace) :
    natOrder.InLayer α f ↔ natOrder.InLayer β f := by
  constructor
  · intro hf
    exact ⟨(natOrder_isLipschitz_iff_monotone hβ f).mpr
      ((natOrder_isLipschitz_iff_monotone hα f).mp hf.1), hf.2⟩
  · intro hf
    exact ⟨(natOrder_isLipschitz_iff_monotone hα f).mpr
      ((natOrder_isLipschitz_iff_monotone hβ f).mp hf.1), hf.2⟩

/-- Every integer layer is already all of `ℒ∞`. -/
theorem natOrder_integerLayer_eq_univ (n : ℕ) :
    natOrder.integerLayer n = Set.univ := by
  apply Set.eq_univ_of_forall
  intro f
  obtain ⟨α, hα, hf⟩ := f.2
  exact (natOrder_inLayer_iff_inLayer hα (by positivity) f.1).mp hf

/-- The non-Yoneda-complete order quasi-metric nevertheless has property D. -/
theorem natOrder_propertyD : natOrder.layerSystem.PropertyD :=
  natOrder.layerSystem.propertyD_of_layer_eq_univ 0
    (natOrder_integerLayer_eq_univ 0)

/-- Proposition `prop:not-necessary`: Yoneda completeness is not necessary for
property D in the full quasi-metric category. -/
theorem yonedaCompleteness_not_necessary_for_propertyD :
    ∃ d : QuasiMetric ℕ, d.layerSystem.PropertyD ∧ ¬d.IsYonedaComplete :=
  ⟨natOrder, natOrder_propertyD, natOrder_not_yonedaComplete⟩

end QuasiMetric
end LipschitzYonedaFinalTopology
