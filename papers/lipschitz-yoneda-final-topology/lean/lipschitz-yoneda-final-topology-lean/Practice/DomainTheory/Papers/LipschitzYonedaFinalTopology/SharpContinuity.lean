import Mathlib.Data.ENNReal.Inv
import Practice.DomainTheory.Papers.LipschitzYonedaFinalTopology.StandardConsequences

/-!
# Scott continuity of the sharp transform

This file proves the formal-ball criterion used in the manuscript.  In a
standard quasi-metric space, an `α`-Lipschitz Yoneda-continuous map `q`
induces the Scott-continuous map

`(x,r) ↦ q x - α r`.

The proof is internal.  It uses standardness to normalize an arbitrary
directed formal-ball supremum to radius zero, identifies the center as a
Yoneda limit, and then applies Yoneda continuity of `q`.
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

/-- A finite scaling of a tail-small family is again tail-small. -/
theorem eventually_mul_lt_of_eventually_lt
    {ι : Type u} [Preorder ι] (hne : Nonempty ι)
    (r : ι → ℝ≥0)
    (hr : ∀ ε : ℝ≥0, 0 < ε →
      ∃ i : ι, ∀ j : ι, i ≤ j → r j < ε)
    (α : ℝ≥0) :
    ∀ ε : ℝ≥0, 0 < ε →
      ∃ i : ι, ∀ j : ι, i ≤ j → α * r j < ε := by
  intro ε hε
  by_cases hα : α = 0
  · let i : ι := Classical.choice hne
    refine ⟨i, ?_⟩
    intro j _hij
    simpa [hα] using hε
  · have hαpos : 0 < α := pos_iff_ne_zero.mpr hα
    obtain ⟨i, hi⟩ := hr (ε / α) (div_pos hε hαpos)
    refine ⟨i, ?_⟩
    intro j hij
    calc
      α * r j < α * (ε / α) :=
        mul_lt_mul_of_pos_left (hi j hij) hαpos
      _ = ε := by
        rw [mul_comm, div_mul_cancel₀ ε hα]

/-- Algebraic form of monotonicity for the truncated difference coordinate
of a formal ball over `[0,+∞]`.  The radii are finite, which is precisely
what permits cancellation. -/
theorem ennreal_sub_radius_mono
    {u v : ℝ≥0∞} {r s : ℝ≥0}
    (h : (u - v) + (s : ℝ≥0∞) ≤ (r : ℝ≥0∞)) :
    u - (r : ℝ≥0∞) ≤ v - (s : ℝ≥0∞) := by
  have hsr : (s : ℝ≥0∞) ≤ (r : ℝ≥0∞) :=
    (le_add_left le_rfl).trans h
  have huv : u - v ≤ (r : ℝ≥0∞) - (s : ℝ≥0∞) :=
    ENNReal.le_sub_of_add_le_right ENNReal.coe_ne_top h
  rw [tsub_le_iff_right]
  calc
    u ≤ v + (u - v) := le_add_tsub
    _ ≤ v + ((r : ℝ≥0∞) - (s : ℝ≥0∞)) :=
      by simpa [add_comm] using add_le_add_left huv v
    _ = v + (r : ℝ≥0∞) - (s : ℝ≥0∞) := by
      rw [add_comm v, ENNReal.sub_add_eq_add_sub hsr ENNReal.coe_ne_top]
      ac_rfl
    _ ≤ (v - (s : ℝ≥0∞)) + (r : ℝ≥0∞) :=
      add_tsub_le_tsub_add

/-- Lipschitzness makes the sharp transform monotone on formal balls. -/
theorem sharp_monotone
    {α : ℝ≥0} {q : X → ℝ≥0∞}
    (hq : d.IsLipschitz α q) :
    Monotone (d.sharp α q) := by
  intro p p' hpp'
  apply ennreal_sub_radius_mono
  calc
    (q p.center - q p'.center) +
          (((α * p'.radius : ℝ≥0)) : ℝ≥0∞)
        ≤ (α : ℝ≥0∞) * d.edist p.center p'.center +
            (α : ℝ≥0∞) * (p'.radius : ℝ≥0∞) := by
          simpa only [ENNReal.coe_mul] using
            add_le_add (hq p.center p'.center) le_rfl
    _ = (α : ℝ≥0∞) *
          (d.edist p.center p'.center + (p'.radius : ℝ≥0∞)) := by
          rw [mul_add]
    _ ≤ (α : ℝ≥0∞) * (p.radius : ℝ≥0∞) :=
      mul_le_mul_left' ((FormalBall.le_def d).mp hpp') _
    _ = (((α * p.radius : ℝ≥0)) : ℝ≥0∞) := by
      rw [ENNReal.coe_mul]

/-- The indexed form of the formal-ball criterion: `sharp` preserves every
directed supremum represented by a monotone directed net. -/
theorem IsStandard.sharp_isLUB
    (hstandard : d.IsStandard)
    {ι : Type u} [Preorder ι]
    (p : ι → d.FormalBall)
    (hdir : IsDirectedIndex ι)
    (hmono : Monotone p)
    {a : d.FormalBall}
    (ha : IsLUB (Set.range p) a)
    {α : ℝ≥0} {q : X → ℝ≥0∞}
    (hqLip : d.IsLipschitz α q)
    (hqYoneda : d.IsYonedaContinuous q) :
    IsLUB (Set.range (fun i ↦ d.sharp α q (p i)))
      (d.sharp α q a) := by
  let p0 : ι → d.FormalBall :=
    fun i ↦ FormalBall.unshift d a.radius (p i)
  have hapi (i : ι) : a.radius ≤ (p i).radius :=
    FormalBall.radius_le_of_le d (ha.1 ⟨i, rfl⟩)
  have hmono0 : Monotone p0 := by
    intro i j hij
    apply (FormalBall.shift_le_shift_iff d a.radius (p0 i) (p0 j)).mp
    simpa [p0, FormalBall.shift_unshift d (hapi i),
      FormalBall.shift_unshift d (hapi j)] using hmono hij
  have ha0raw := IsStandard.unshift_isLUB d hstandard p hdir hmono ha
    (t := a.radius) le_rfl
  have ha0 : IsLUB (Set.range p0)
      (⟨a.center, 0⟩ : d.FormalBall) := by
    simpa [p0, FormalBall.unshift] using ha0raw
  have hradius0 :=
    IsStandard.radius_eventually_lt_of_zeroRadius_isLUB
      d hstandard p0 hdir hmono0 a.center ha0
  have hcauchy0 :=
    IsStandard.centers_isCauchyNet_of_zeroRadius_isLUB
      d hstandard p0 hdir hmono0 a.center ha0
  have hdlimit0 :=
    IsStandard.center_isDLimit_of_zeroRadius_isLUB
      d hstandard p0 hdir hmono0 a.center ha0
  have hqLimit : QuasiMetric.ennreal.IsDLimit
      (fun i ↦ q (p i).center) (q a.center) := by
    simpa [p0, FormalBall.unshift] using
      hqYoneda.maps_dLimit ι (fun i ↦ (p0 i).center) a.center
        hdir hcauchy0 hdlimit0
  have hsharpMono := d.sharp_monotone hqLip
  constructor
  · intro b hb
    obtain ⟨i, rfl⟩ := hb
    exact hsharpMono (ha.1 ⟨i, rfl⟩)
  · intro b hb
    let c : ℝ≥0∞ :=
      (α : ℝ≥0∞) * (a.radius : ℝ≥0∞)
    have hbound (i : ι) :
        q (p i).center - (b + c) ≤
          (((α * (p0 i).radius : ℝ≥0)) : ℝ≥0∞) := by
      have hsharp : d.sharp α q (p i) ≤ b := hb ⟨i, rfl⟩
      have hqpi : q (p i).center ≤
          b + (α : ℝ≥0∞) * ((p i).radius : ℝ≥0∞) := by
        simpa [sharp] using (tsub_le_iff_right.mp hsharp)
      have hsplitNN :
          α * (p i).radius = α * a.radius + α * (p0 i).radius := by
        change α * (p i).radius =
          α * a.radius + α * ((p i).radius - a.radius)
        calc
          α * (p i).radius =
              α * ((p i).radius - a.radius + a.radius) :=
            congrArg (α * ·) (tsub_add_cancel_of_le (hapi i)).symm
          _ = α * ((p i).radius - a.radius) + α * a.radius := by
            rw [mul_add]
          _ = α * a.radius + α * ((p i).radius - a.radius) :=
            add_comm _ _
      have hsplitENN :
          (α : ℝ≥0∞) * ((p i).radius : ℝ≥0∞) =
            c + (((α * (p0 i).radius : ℝ≥0)) : ℝ≥0∞) := by
        rw [← ENNReal.coe_mul, hsplitNN, ENNReal.coe_add]
        simp only [c, ENNReal.coe_mul]
      apply tsub_le_iff_right.mpr
      calc
        q (p i).center
            ≤ b + (α : ℝ≥0∞) * ((p i).radius : ℝ≥0∞) := hqpi
        _ = b +
              (c + (((α * (p0 i).radius : ℝ≥0)) : ℝ≥0∞)) := by
          rw [hsplitENN]
        _ = (((α * (p0 i).radius : ℝ≥0)) : ℝ≥0∞) +
              (b + c) := by ac_rfl
    have hscaled : ∀ ε : ℝ≥0, 0 < ε →
        ∃ i : ι, ∀ j : ι, i ≤ j → α * (p0 j).radius < ε :=
      eventually_mul_lt_of_eventually_lt hdir.1
        (fun i ↦ (p0 i).radius) hradius0 α
    have hlimZero :
        netLimsup (fun i ↦ q (p i).center - (b + c)) = 0 :=
      netLimsup_eq_zero_of_le_radius_eventually_lt
        (fun i ↦ q (p i).center - (b + c))
        (fun i ↦ α * (p0 i).radius) hbound hscaled
    have hqa : q a.center - (b + c) = 0 := by
      exact (hqLimit (b + c)).trans hlimZero
    have hqa_le : q a.center ≤ b + c :=
      tsub_eq_zero_iff_le.mp hqa
    unfold sharp
    exact tsub_le_iff_right.mpr hqa_le

/-- The source formal-ball criterion, now discharged: every Lipschitz
Yoneda-continuous map has Scott-continuous truncated sharp transform. -/
theorem IsStandard.hasScottContinuousSharp
    (hstandard : d.IsStandard)
    {α : ℝ≥0} {q : X → ℝ≥0∞}
    (hqLip : d.IsLipschitz α q)
    (hqYoneda : d.IsYonedaContinuous q) :
    d.HasScottContinuousSharp α q := by
  have hscott : ScottContinuous (d.sharp α q) := by
    intro S hSnonempty hSdirected a ha
    let p : S → d.FormalBall := fun s ↦ s.1
    have hdir : IsDirectedIndex S := by
      constructor
      · exact Set.nonempty_coe_sort.mpr hSnonempty
      · intro i j
        obtain ⟨k, hkS, hik, hjk⟩ :=
          hSdirected i.1 i.2 j.1 j.2
        exact ⟨⟨k, hkS⟩, hik, hjk⟩
    have hmono : Monotone p := fun _ _ hij ↦ hij
    have hpLUB : IsLUB (Set.range p) a := by
      simpa only [p, Subtype.range_val] using ha
    have hindexed := IsStandard.sharp_isLUB d hstandard p hdir hmono
      hpLUB hqLip hqYoneda
    simpa only [p, ← Set.image_eq_range] using hindexed
  unfold HasScottContinuousSharp
  apply (Topology.IsScott.scottContinuousOn_iff_continuous
    (D := Set.univ) (by simp)).mp
  simpa only [scottContinuousOn_univ] using hscott

end QuasiMetric
end LipschitzYonedaFinalTopology
