import Practice.DomainTheory.Papers.LipschitzYonedaFinalTopology.DomainStructure
import Practice.DomainTheory.Papers.LipschitzYonedaFinalTopology.FormalBallChains

/-!
# Consequences of standardness for formal balls

This file begins the internal proof of the established formal-ball facts
used by the manuscript.  In particular it proves Proposition 2.4(1): the
radius of a directed supremum is the infimum of the radii.  No completeness
assumption is used here.
-/

set_option autoImplicit false
set_option linter.unnecessarySimpa false

open Set Function Topology
open scoped NNReal ENNReal Topology

noncomputable section

universe u

namespace LipschitzYonedaFinalTopology
namespace QuasiMetric

variable {X : Type u} (d : QuasiMetric X)

namespace FormalBall

/-- Formal-ball order reverses radii. -/
theorem radius_le_of_le {p q : d.FormalBall} (hpq : p ≤ q) :
    q.radius ≤ p.radius := by
  apply ENNReal.coe_le_coe.mp
  exact (le_add_left le_rfl).trans hpq

/-- Adding the same finite amount to both radii preserves and reflects the
formal-ball order. -/
theorem shift_le_shift_iff (t : ℝ≥0) (p q : d.FormalBall) :
    FormalBall.shift d t p ≤ FormalBall.shift d t q ↔ p ≤ q := by
  rw [FormalBall.le_def, FormalBall.le_def]
  change d.edist p.center q.center + ((q.radius + t : ℝ≥0) : ℝ≥0∞) ≤
      ((p.radius + t : ℝ≥0) : ℝ≥0∞) ↔
    d.edist p.center q.center + (q.radius : ℝ≥0∞) ≤
      (p.radius : ℝ≥0∞)
  rw [ENNReal.coe_add, ENNReal.coe_add, ← add_assoc]
  exact ENNReal.add_le_add_iff_right ENNReal.coe_ne_top

/-- Removing a common amount from a radius. -/
def unshift (t : ℝ≥0) (p : d.FormalBall) : d.FormalBall :=
  ⟨p.center, p.radius - t⟩

@[simp]
theorem shift_unshift {t : ℝ≥0} {p : d.FormalBall}
    (ht : t ≤ p.radius) :
    FormalBall.shift d t (FormalBall.unshift d t p) = p := by
  cases p
  simp [shift, unshift, tsub_add_cancel_of_le ht]

end FormalBall

/-- Proposition 2.4(1): in a standard quasi-metric space, the radius of a
directed supremum is the infimum of the radii. -/
theorem IsStandard.radius_eq_iInf
    (hstandard : d.IsStandard)
    {ι : Type u} [Preorder ι]
    (p : ι → d.FormalBall)
    (hdir : IsDirectedIndex ι)
    (hmono : Monotone p)
    {q : d.FormalBall}
    (hq : IsLUB (Set.range p) q) :
    q.radius = sInf (Set.range fun i ↦ (p i).radius) := by
  let i0 : ι := Classical.choice hdir.1
  have hrange_nonempty : (Set.range fun i ↦ (p i).radius).Nonempty :=
    ⟨(p i0).radius, ⟨i0, rfl⟩⟩
  have hrange_bdd : BddBelow (Set.range fun i ↦ (p i).radius) :=
    ⟨0, by intro r _hr; exact zero_le r⟩
  let R : ℝ≥0 := sInf (Set.range fun i ↦ (p i).radius)
  have hRle (i : ι) : R ≤ (p i).radius :=
    csInf_le hrange_bdd ⟨i, rfl⟩
  have hqR : q.radius ≤ R := by
    apply le_csInf hrange_nonempty
    intro r hr
    obtain ⟨i, rfl⟩ := hr
    exact FormalBall.radius_le_of_le d (hq.1 ⟨i, rfl⟩)
  let p0 : ι → d.FormalBall := fun i ↦ FormalBall.unshift d R (p i)
  have hshift_p0 (i : ι) : FormalBall.shift d R (p0 i) = p i := by
    exact FormalBall.shift_unshift d (hRle i)
  have hmono0 : Monotone p0 := by
    intro i j hij
    apply (FormalBall.shift_le_shift_iff d R (p0 i) (p0 j)).mp
    simpa [hshift_p0] using hmono hij
  have hshiftLUB : IsLUB
      (Set.range (fun i ↦ FormalBall.shift d R (p0 i))) q := by
    simpa [hshift_p0] using hq
  obtain ⟨q0, hq0⟩ :=
    (hstandard ι p0 hdir hmono0 R).mpr ⟨q, hshiftLUB⟩
  have hq0radius : q0.radius = 0 := by
    apply le_antisymm _ (zero_le _)
    by_contra hnot
    have hpos : 0 < q0.radius := lt_of_not_ge hnot
    have hRlt : R < R + q0.radius := lt_add_of_pos_right R hpos
    obtain ⟨ri, ⟨i, rfl⟩, hi⟩ :=
      exists_lt_of_csInf_lt hrange_nonempty hRlt
    have hq0le : q0.radius ≤ (p0 i).radius :=
      FormalBall.radius_le_of_le d (hq0.1 ⟨i, rfl⟩)
    have hadd : R + q0.radius ≤ (p i).radius := by
      calc
        R + q0.radius = q0.radius + R := add_comm _ _
        _ ≤ ((p i).radius - R) + R := by
          simpa [add_comm] using add_le_add_right hq0le R
        _ = (p i).radius := tsub_add_cancel_of_le (hRle i)
    exact (not_lt_of_ge hadd) hi
  have hshiftUpper :
      FormalBall.shift d R q0 ∈ upperBounds (Set.range p) := by
    intro b hb
    obtain ⟨i, rfl⟩ := hb
    have hp0q0 : p0 i ≤ q0 := hq0.1 ⟨i, rfl⟩
    have hshift :=
      (FormalBall.shift_le_shift_iff d R (p0 i) q0).2 hp0q0
    simpa [hshift_p0] using hshift
  have hR_q : R ≤ q.radius := by
    have hqshift : q ≤ FormalBall.shift d R q0 := hq.2 hshiftUpper
    have hradius := FormalBall.radius_le_of_le d hqshift
    simpa [FormalBall.shift, hq0radius] using hradius
  exact le_antisymm hqR hR_q

/-- Proposition 2.4(2), for nonnegative shifts: shifting every radius in a
directed family shifts its supremum by the same amount. -/
theorem IsStandard.shift_isLUB
    (hstandard : d.IsStandard)
    {ι : Type u} [Preorder ι]
    (p : ι → d.FormalBall)
    (hdir : IsDirectedIndex ι)
    (hmono : Monotone p)
    {q : d.FormalBall}
    (hq : IsLUB (Set.range p) q)
    (t : ℝ≥0) :
    IsLUB (Set.range (fun i ↦ FormalBall.shift d t (p i)))
      (FormalBall.shift d t q) := by
  have hshiftMono : Monotone (fun i ↦ FormalBall.shift d t (p i)) := by
    intro i j hij
    exact (FormalBall.shift_le_shift_iff d t (p i) (p j)).2 (hmono hij)
  obtain ⟨q', hq'⟩ :=
    (hstandard ι p hdir hmono t).mp ⟨q, hq⟩
  have hq'_le : q' ≤ FormalBall.shift d t q := by
    apply hq'.2
    intro b hb
    obtain ⟨i, rfl⟩ := hb
    exact (FormalBall.shift_le_shift_iff d t (p i) q).2
      (hq.1 ⟨i, rfl⟩)
  have hshiftRangeNonempty :
      (Set.range fun i ↦ (FormalBall.shift d t (p i)).radius).Nonempty := by
    let i0 : ι := Classical.choice hdir.1
    exact ⟨(FormalBall.shift d t (p i0)).radius, ⟨i0, rfl⟩⟩
  have htq' : t ≤ q'.radius := by
    rw [IsStandard.radius_eq_iInf d hstandard
      (fun i ↦ FormalBall.shift d t (p i)) hdir hshiftMono hq']
    apply le_csInf hshiftRangeNonempty
    intro r hr
    obtain ⟨i, rfl⟩ := hr
    simp [FormalBall.shift]
  let q0 := FormalBall.unshift d t q'
  have hq0Upper : q0 ∈ upperBounds (Set.range p) := by
    intro b hb
    obtain ⟨i, rfl⟩ := hb
    apply (FormalBall.shift_le_shift_iff d t (p i) q0).mp
    rw [FormalBall.shift_unshift d htq']
    exact hq'.1 ⟨i, rfl⟩
  have hq_q0 : q ≤ q0 := hq.2 hq0Upper
  have hshift_le : FormalBall.shift d t q ≤ q' := by
    have := (FormalBall.shift_le_shift_iff d t q q0).2 hq_q0
    simpa [q0, FormalBall.shift_unshift d htq'] using this
  have heq : q' = FormalBall.shift d t q :=
    le_antisymm hq'_le hshift_le
  simpa [heq] using hq'

/-- Conversely, removing a common finite amount from all radii removes it
from the supremum.  The side condition is exactly what makes every
subtraction an actual inverse to `shift`. -/
theorem IsStandard.unshift_isLUB
    (hstandard : d.IsStandard)
    {ι : Type u} [Preorder ι]
    (p : ι → d.FormalBall)
    (hdir : IsDirectedIndex ι)
    (hmono : Monotone p)
    {q : d.FormalBall}
    (hq : IsLUB (Set.range p) q)
    {t : ℝ≥0}
    (ht : t ≤ q.radius) :
    IsLUB (Set.range (fun i ↦ FormalBall.unshift d t (p i)))
      (FormalBall.unshift d t q) := by
  have htpi (i : ι) : t ≤ (p i).radius :=
    ht.trans (FormalBall.radius_le_of_le d (hq.1 ⟨i, rfl⟩))
  let p0 : ι → d.FormalBall :=
    fun i ↦ FormalBall.unshift d t (p i)
  have hshift_p0 (i : ι) : FormalBall.shift d t (p0 i) = p i :=
    FormalBall.shift_unshift d (htpi i)
  have hmono0 : Monotone p0 := by
    intro i j hij
    apply (FormalBall.shift_le_shift_iff d t (p0 i) (p0 j)).mp
    simpa only [hshift_p0] using hmono hij
  have hshiftLUB : IsLUB
      (Set.range (fun i ↦ FormalBall.shift d t (p0 i))) q := by
    simpa only [hshift_p0] using hq
  obtain ⟨q0, hq0⟩ :=
    (hstandard ι p0 hdir hmono0 t).mpr ⟨q, hshiftLUB⟩
  have hq0shift :=
    IsStandard.shift_isLUB d hstandard p0 hdir hmono0 hq0 t
  have hshiftEq : FormalBall.shift d t q0 = q :=
    hq0shift.unique hshiftLUB
  have htargetShift :
      FormalBall.shift d t (FormalBall.unshift d t q) = q :=
    FormalBall.shift_unshift d ht
  have hq0Eq : q0 = FormalBall.unshift d t q := by
    apply le_antisymm
    · apply (FormalBall.shift_le_shift_iff d t q0
        (FormalBall.unshift d t q)).mp
      exact (hshiftEq.trans htargetShift.symm).le
    · apply (FormalBall.shift_le_shift_iff d t
        (FormalBall.unshift d t q) q0).mp
      exact (htargetShift.trans hshiftEq.symm).le
  simpa only [p0, hq0Eq] using hq0

/-- Radii in a monotone formal-ball net with zero-radius supremum become
arbitrarily small, uniformly on a tail. -/
theorem IsStandard.radius_eventually_lt_of_zeroRadius_isLUB
    (hstandard : d.IsStandard)
    {ι : Type u} [Preorder ι]
    (p : ι → d.FormalBall)
    (hdir : IsDirectedIndex ι)
    (hmono : Monotone p)
    (x : X)
    (hq : IsLUB (Set.range p) (⟨x, 0⟩ : d.FormalBall)) :
    ∀ ε : ℝ≥0, 0 < ε →
      ∃ i : ι, ∀ j : ι, i ≤ j → (p j).radius < ε := by
  have hradius :
      sInf (Set.range fun i ↦ (p i).radius) = 0 := by
    simpa using (IsStandard.radius_eq_iInf d hstandard p hdir hmono hq).symm
  let i0 : ι := Classical.choice hdir.1
  have hrange_nonempty : (Set.range fun i ↦ (p i).radius).Nonempty :=
    ⟨(p i0).radius, ⟨i0, rfl⟩⟩
  intro ε hε
  have hinf_lt : sInf (Set.range fun i ↦ (p i).radius) < ε := by
    simpa [hradius] using hε
  obtain ⟨r, ⟨i, rfl⟩, hi⟩ :=
    exists_lt_of_csInf_lt hrange_nonempty hinf_lt
  refine ⟨i, fun j hij ↦ ?_⟩
  exact (FormalBall.radius_le_of_le d (hmono hij)).trans_lt hi

/-- Centers of a monotone formal-ball net with zero-radius supremum form a
Cauchy net. -/
theorem IsStandard.centers_isCauchyNet_of_zeroRadius_isLUB
    (hstandard : d.IsStandard)
    {ι : Type u} [Preorder ι]
    (p : ι → d.FormalBall)
    (hdir : IsDirectedIndex ι)
    (hmono : Monotone p)
    (x : X)
    (hq : IsLUB (Set.range p) (⟨x, 0⟩ : d.FormalBall)) :
    d.IsCauchyNet (fun i ↦ (p i).center) := by
  intro ε hε
  obtain ⟨i0, hi0⟩ :=
    IsStandard.radius_eventually_lt_of_zeroRadius_isLUB
      d hstandard p hdir hmono x hq ε hε
  refine ⟨i0, ?_⟩
  intro i j hi hj
  have hpij := hmono hj
  have hdist : d.edist (p i).center (p j).center ≤ (p i).radius :=
    (le_add_right le_rfl).trans hpij
  exact hdist.trans_lt (ENNReal.coe_lt_coe.mpr (hi0 i hi))

/-- The formal-ball form of Lemma 5.15, in the direction needed below: if a
monotone weighted net has zero-radius supremum `(x,0)`, then `x` is the
`d`-limit of its centers. -/
theorem IsStandard.center_isDLimit_of_zeroRadius_isLUB
    (hstandard : d.IsStandard)
    {ι : Type u} [Preorder ι]
    (p : ι → d.FormalBall)
    (hdir : IsDirectedIndex ι)
    (hmono : Monotone p)
    (x : X)
    (hq : IsLUB (Set.range p) (⟨x, 0⟩ : d.FormalBall)) :
    d.IsDLimit (fun i ↦ (p i).center) x := by
  intro y
  apply le_antisymm
  · by_contra hnot
    have hlt : netLimsup (fun i ↦ d.edist (p i).center y) <
        d.edist x y := lt_of_not_ge hnot
    obtain ⟨R, hlimR, hRxy⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hlt
    obtain ⟨i, hi⟩ := iInf_lt_iff.mp hlimR
    have htail (j : ι) (hij : i ≤ j) :
        d.edist (p j).center y < (R : ℝ≥0∞) := by
      have hjle : d.edist (p j).center y ≤
          ⨆ (_h : i ≤ j), d.edist (p j).center y :=
        le_iSup_of_le hij le_rfl
      exact hjle.trans_lt <| (le_iSup (fun k : ι ↦
        ⨆ (_h : i ≤ k), d.edist (p k).center y) j).trans_lt hi
    let Tail := {j : ι // i ≤ j}
    let pTail : Tail → d.FormalBall := fun j ↦ p j.1
    have hdirTail : IsDirectedIndex Tail := by
      constructor
      · exact ⟨⟨i, le_rfl⟩⟩
      · intro j k
        obtain ⟨l, hjl, hkl⟩ := hdir.2 j.1 k.1
        exact ⟨⟨l, j.2.trans hjl⟩, hjl, hkl⟩
    have hmonoTail : Monotone pTail := fun _ _ hjk ↦ hmono hjk
    have hqTail : IsLUB (Set.range pTail) (⟨x, 0⟩ : d.FormalBall) := by
      constructor
      · intro b hb
        obtain ⟨j, rfl⟩ := hb
        exact hq.1 ⟨j.1, rfl⟩
      · intro z hz
        apply hq.2
        intro b hb
        obtain ⟨k, rfl⟩ := hb
        obtain ⟨l, hkl, hil⟩ := hdir.2 k i
        exact (hmono hkl).trans (hz ⟨⟨l, hil⟩, rfl⟩)
    have hshiftTail := IsStandard.shift_isLUB d hstandard pTail
      hdirTail hmonoTail hqTail R
    have hyUpper : (⟨y, 0⟩ : d.FormalBall) ∈
        upperBounds (Set.range fun j ↦ FormalBall.shift d R (pTail j)) := by
      intro b hb
      obtain ⟨j, rfl⟩ := hb
      change d.edist (p j.1).center y + (0 : ℝ≥0∞) ≤
        (((p j.1).radius + R : ℝ≥0) : ℝ≥0∞)
      rw [add_zero, ENNReal.coe_add]
      exact (htail j.1 j.2).le.trans (le_add_left le_rfl)
    have hxyR : d.edist x y ≤ (R : ℝ≥0∞) := by
      have hball : FormalBall.shift d R (⟨x, 0⟩ : d.FormalBall) ≤
          (⟨y, 0⟩ : d.FormalBall) := hshiftTail.2 hyUpper
      simpa [FormalBall.shift, FormalBall.le_def] using hball
    exact (not_lt_of_ge hxyR) hRxy
  · apply ENNReal.le_of_forall_pos_le_add
    intro ε hε _hfinite
    obtain ⟨i, hi⟩ :=
      IsStandard.radius_eventually_lt_of_zeroRadius_isLUB
        d hstandard p hdir hmono x hq ε hε
    refine (iInf_le (fun k : ι ↦
      ⨆ j : ι, ⨆ (_h : k ≤ j), d.edist (p j).center y) i).trans ?_
    apply iSup_le
    intro j
    apply iSup_le
    intro hij
    have hpjx := hq.1 ⟨j, rfl⟩
    have hjx : d.edist (p j).center x ≤ (p j).radius := by
      simpa using (le_add_right le_rfl).trans hpjx
    calc
      d.edist (p j).center y
          ≤ d.edist (p j).center x + d.edist x y :=
        d.edist_triangle _ _ _
      _ ≤ ((p j).radius : ℝ≥0∞) + d.edist x y :=
        add_le_add hjx le_rfl
      _ ≤ (ε : ℝ≥0∞) + d.edist x y :=
        add_le_add (ENNReal.coe_le_coe.mpr (hi j hij).le) le_rfl
      _ = d.edist x y + (ε : ℝ≥0∞) := add_comm _ _

/-- The converse formal-ball direction of Lemma 5.15.  A monotone weighted
net whose radii tend to zero has `(x,0)` as its least upper bound as soon as
`x` is the `d`-limit of the centers.  Notice that this direction does not
need standardness or completeness. -/
theorem zeroRadius_isLUB_of_center_isDLimit
    {ι : Type u} [Preorder ι]
    (p : ι → d.FormalBall)
    (hdir : IsDirectedIndex ι)
    (hmono : Monotone p)
    (hradius : ∀ ε : ℝ≥0, 0 < ε →
      ∃ i : ι, ∀ j : ι, i ≤ j → (p j).radius < ε)
    (x : X)
    (hx : d.IsDLimit (fun i ↦ (p i).center) x) :
    IsLUB (Set.range p) (⟨x, 0⟩ : d.FormalBall) := by
  have hselfLimsup :
      netLimsup (fun i ↦ d.edist (p i).center x) = 0 := by
    simpa [d.edist_self] using (hx x).symm
  have hupper (i : ι) : p i ≤ (⟨x, 0⟩ : d.FormalBall) := by
    rw [FormalBall.le_def]
    simp only [ENNReal.coe_zero, add_zero]
    apply ENNReal.le_of_forall_pos_le_add
    intro ε hε _hfinite
    obtain ⟨j, hij, hjx⟩ :=
      exists_ge_lt_of_netLimsup_eq_zero hdir
        (fun k ↦ d.edist (p k).center x) hselfLimsup i ε hε
    calc
      d.edist (p i).center x
          ≤ d.edist (p i).center (p j).center +
              d.edist (p j).center x := d.edist_triangle _ _ _
      _ ≤ ((p i).radius : ℝ≥0∞) + (ε : ℝ≥0∞) := by
        apply add_le_add
        · exact (le_add_right le_rfl).trans (hmono hij)
        · exact hjx.le
  constructor
  · intro b hb
    obtain ⟨i, rfl⟩ := hb
    exact hupper i
  · intro q hq
    have hqRadiusLe (i : ι) : q.radius ≤ (p i).radius :=
      FormalBall.radius_le_of_le d (hq ⟨i, rfl⟩)
    have hqRadius : q.radius = 0 := by
      apply le_antisymm _ (zero_le _)
      by_contra hnot
      have hpos : 0 < q.radius := lt_of_not_ge hnot
      obtain ⟨i, hi⟩ := hradius q.radius hpos
      exact (not_lt_of_ge (hqRadiusLe i)) (hi i le_rfl)
    have hdistLeRadius (i : ι) :
        d.edist (p i).center q.center ≤ ((p i).radius : ℝ≥0∞) := by
      have hi := (FormalBall.le_def d).mp (hq ⟨i, rfl⟩)
      rw [hqRadius] at hi
      simpa using hi
    have hdistZero : d.edist x q.center = 0 := by
      rw [hx q.center]
      exact netLimsup_eq_zero_of_le_radius_eventually_lt
        (fun i ↦ d.edist (p i).center q.center)
        (fun i ↦ (p i).radius) hdistLeRadius hradius
    rw [FormalBall.le_def, hqRadius, hdistZero]
    simp

end QuasiMetric
end LipschitzYonedaFinalTopology
