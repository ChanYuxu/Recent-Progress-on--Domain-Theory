import Mathlib.Topology.Instances.ENNReal.Lemmas
import Practice.DomainTheory.Papers.LipschitzYonedaFinalTopology.CenterPoints

/-!
# Zero-radius suprema of formal-ball chains

The cone-forest proof only needs a sharply bounded part of the general
formal-ball dcpo theorem: an increasing sequence of formal balls whose
radii tend to zero has a least upper bound of the form `(x, 0)` in every
Yoneda-complete quasi-metric space.  This file proves that statement
directly from the source definitions, rather than postulating a dcpo
interface.
-/

set_option autoImplicit false
set_option linter.unnecessarySimpa false

open Set Filter Topology
open scoped NNReal ENNReal Topology

noncomputable section

universe u

namespace LipschitzYonedaFinalTopology
namespace QuasiMetric

variable {X : Type u} (d : QuasiMetric X)

/-- A natural-number indexed preorder is directed in the exact sense used
by `IsYonedaComplete`. -/
theorem nat_isDirectedIndex : IsDirectedIndex ℕ := by
  constructor
  · infer_instance
  · intro i j
    exact ⟨max i j, le_max_left _ _, le_max_right _ _⟩

/-- If an `ENNReal` sequence is bounded by finite radii tending to zero,
then its explicit net limsup is zero. -/
theorem netLimsup_eq_zero_of_le_radius_eventually_lt
    {ι : Type u} [Preorder ι]
    (a : ι → ℝ≥0∞) (r : ι → ℝ≥0)
    (har : ∀ n, a n ≤ (r n : ℝ≥0∞))
    (hr : ∀ ε : ℝ≥0, 0 < ε → ∃ i : ι, ∀ j, i ≤ j → r j < ε) :
    netLimsup a = 0 := by
  apply le_antisymm
  · apply ENNReal.le_of_forall_pos_le_add
    intro ε hε _hzeroFinite
    obtain ⟨k, hk⟩ := hr ε hε
    simp only [zero_add]
    refine (iInf_le
      (fun i : ι ↦ ⨆ j : ι, ⨆ (_h : i ≤ j), a j) k).trans ?_
    apply iSup_le
    intro j
    apply iSup_le
    intro hkj
    exact (har j).trans (ENNReal.coe_le_coe.mpr (le_of_lt (hk j hkj)))
  · exact zero_le _

/-- The natural-number version of the preceding order lemma. -/
theorem netLimsup_eq_zero_of_le_radius_tendsto_zero
    (a : ℕ → ℝ≥0∞) (r : ℕ → ℝ≥0)
    (har : ∀ n, a n ≤ (r n : ℝ≥0∞))
    (hr : Tendsto r atTop (𝓝 0)) :
    netLimsup a = 0 := by
  apply netLimsup_eq_zero_of_le_radius_eventually_lt a r har
  intro ε hε
  exact eventually_atTop.1 ((tendsto_order.1 hr).2 ε hε)

/-- If the explicit net limsup is zero, then after any prescribed index
there is a later value below every positive finite threshold. -/
theorem exists_ge_lt_of_netLimsup_eq_zero
    {ι : Type u} [Preorder ι] (hdir : IsDirectedIndex ι)
    (a : ι → ℝ≥0∞) (ha : netLimsup a = 0)
    (i : ι) (ε : ℝ≥0) (hε : 0 < ε) :
    ∃ j ≥ i, a j < (ε : ℝ≥0∞) := by
  have hinf : netLimsup a < (ε : ℝ≥0∞) := by
    rw [ha]
    exact ENNReal.coe_pos.mpr hε
  unfold netLimsup at hinf
  obtain ⟨k, hk⟩ := iInf_lt_iff.mp hinf
  obtain ⟨j, hij, hkj⟩ := hdir.2 i k
  refine ⟨j, hij, ?_⟩
  have hinner : a j ≤ ⨆ (_h : k ≤ j), a j :=
    le_iSup (fun _h : k ≤ j ↦ a j) hkj
  exact (le_iSup_of_le j hinner).trans_lt hk

/-- The centers of an increasing formal-ball sequence with vanishing radii
form a Cauchy sequence. -/
theorem centers_isCauchyNet_of_monotone_radius_tendsto_zero
    (p : ℕ → d.FormalBall) (hp : Monotone p)
    (hr : Tendsto (fun n ↦ (p n).radius) atTop (𝓝 0)) :
    d.IsCauchyNet (fun n ↦ (p n).center) := by
  intro ε hε
  have hevent : ∀ᶠ n in atTop, (p n).radius < ε :=
    (tendsto_order.1 hr).2 ε hε
  obtain ⟨i₀, hi₀⟩ := eventually_atTop.1 hevent
  refine ⟨i₀, ?_⟩
  intro i j hi₀i hij
  have hijBall := hp hij
  have hi₀iBall := hp hi₀i
  have hdist : d.edist (p i).center (p j).center ≤
      ((p i).radius : ℝ≥0∞) :=
    (le_add_right le_rfl).trans
      ((FormalBall.le_def d).mp hijBall)
  have hri : (p i).radius ≤ (p i₀).radius := by
    exact_mod_cast (show ((p i).radius : ℝ≥0∞) ≤ (p i₀).radius from
      (le_add_left le_rfl).trans
        ((FormalBall.le_def d).mp hi₀iBall))
  exact hdist.trans_lt
    (ENNReal.coe_lt_coe.mpr (hri.trans_lt (hi₀ i₀ le_rfl)))

/-- The source-bounded formal-ball theorem used by the infinite branches:
Yoneda completeness supplies a zero-radius least upper bound for every
increasing sequence whose radii tend to zero. -/
theorem exists_zeroRadius_isLUB_of_monotone
    (hcomplete : d.IsYonedaComplete)
    (p : ℕ → d.FormalBall) (hp : Monotone p)
    (hr : Tendsto (fun n ↦ (p n).radius) atTop (𝓝 0)) :
    ∃ x : X, IsLUB (Set.range p) (⟨x, 0⟩ : d.FormalBall) := by
  have hcauchy : d.IsCauchyNet (fun n ↦ (p n).center) :=
    d.centers_isCauchyNet_of_monotone_radius_tendsto_zero p hp hr
  have hdirLift : IsDirectedIndex (ULift.{u} ℕ) := by
    constructor
    · infer_instance
    · intro i j
      exact ⟨ULift.up (max i.down j.down),
        le_max_left _ _, le_max_right _ _⟩
  have hcauchyLift :
      d.IsCauchyNet (fun n : ULift.{u} ℕ ↦ (p n.down).center) := by
    intro ε hε
    obtain ⟨i₀, hi₀⟩ := hcauchy ε hε
    refine ⟨ULift.up i₀, ?_⟩
    intro i j hi₀i hij
    exact hi₀ i.down j.down hi₀i hij
  obtain ⟨x, hx⟩ := hcomplete (ULift.{u} ℕ)
    (fun n ↦ (p n.down).center) hdirLift hcauchyLift
  have hselfLimsup :
      netLimsup (fun n : ULift.{u} ℕ ↦
        d.edist (p n.down).center x) = 0 := by
    simpa [d.edist_self] using (hx x).symm
  have hupper : ∀ n, p n ≤ (⟨x, 0⟩ : d.FormalBall) := by
    intro i
    rw [FormalBall.le_def]
    simp only [ENNReal.coe_zero, add_zero]
    apply ENNReal.le_of_forall_pos_le_add
    intro ε hε _hradiusFinite
    obtain ⟨j, hij, hjx⟩ :=
      exists_ge_lt_of_netLimsup_eq_zero
        hdirLift (fun n : ULift.{u} ℕ ↦
          d.edist (p n.down).center x)
        hselfLimsup (ULift.up i) ε hε
    have hijDown : i ≤ j.down := hij
    have hijBall := hp hijDown
    calc
      d.edist (p i).center x
          ≤ d.edist (p i).center (p j.down).center +
              d.edist (p j.down).center x := d.edist_triangle _ _ _
      _ ≤ ((p i).radius : ℝ≥0∞) + (ε : ℝ≥0∞) := by
        apply add_le_add
        · exact (le_add_right le_rfl).trans
            ((FormalBall.le_def d).mp hijBall)
        · exact le_of_lt hjx
  refine ⟨x, ⟨?_, ?_⟩⟩
  · intro q hq
    obtain ⟨n, rfl⟩ := hq
    exact hupper n
  · intro q hq
    have hqRadiusLe (n : ℕ) : q.radius ≤ (p n).radius := by
      exact_mod_cast (show (q.radius : ℝ≥0∞) ≤ (p n).radius from
        (le_add_left le_rfl).trans
          ((FormalBall.le_def d).mp (hq ⟨n, rfl⟩)))
    have hqRadius : q.radius = 0 := by
      apply le_antisymm _ (zero_le _)
      by_contra hnot
      have hpos : 0 < q.radius := lt_of_not_ge hnot
      have hevent : ∀ᶠ n in atTop, (p n).radius < q.radius :=
        (tendsto_order.1 hr).2 q.radius hpos
      obtain ⟨n, hn⟩ := hevent.exists
      exact (not_lt_of_ge (hqRadiusLe n)) hn
    have hdistLeRadius (n : ℕ) :
        d.edist (p n).center q.center ≤ ((p n).radius : ℝ≥0∞) := by
      have hn := (FormalBall.le_def d).mp (hq ⟨n, rfl⟩)
      rw [hqRadius] at hn
      simpa using hn
    have hdistZero : d.edist x q.center = 0 := by
      rw [hx q.center]
      apply netLimsup_eq_zero_of_le_radius_eventually_lt
        (fun n : ULift.{u} ℕ ↦
          d.edist (p n.down).center q.center)
        (fun n : ULift.{u} ℕ ↦ (p n.down).radius)
        (fun n ↦ hdistLeRadius n.down)
      intro ε hε
      obtain ⟨k, hk⟩ := eventually_atTop.1
        ((tendsto_order.1 hr).2 ε hε)
      refine ⟨ULift.up k, ?_⟩
      intro j hkj
      exact hk j.down hkj
    rw [FormalBall.le_def, hqRadius, hdistZero]
    simp

end QuasiMetric
end LipschitzYonedaFinalTopology
