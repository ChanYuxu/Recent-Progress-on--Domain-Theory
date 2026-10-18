import Practice.DomainTheory.Papers.LipschitzYonedaFinalTopology.CauchyWeightedSubnet
import Practice.DomainTheory.Papers.LipschitzYonedaFinalTopology.SharpContinuity

/-!
# Converse formal-ball criterion

This file formalizes the converse direction of the formal-ball criterion.
The key step is not skipped: an arbitrary Cauchy net is replaced by the
cofinal Cauchy-weighted subnet constructed in `CauchyWeightedSubnet.lean`.
-/

set_option autoImplicit false
set_option linter.unnecessarySimpa false

open Set Function Filter Topology
open scoped NNReal ENNReal Topology

noncomputable section

universe u

namespace LipschitzYonedaFinalTopology
namespace QuasiMetric

variable {X : Type u} (d : QuasiMetric X)

/-- The Cauchy clause in Yoneda continuity follows from a finite Lipschitz
bound. -/
theorem IsLipschitz.maps_cauchy
    {α : ℝ≥0} {q : X → ℝ≥0∞}
    (hq : d.IsLipschitz α q)
    {ι : Type u} [Preorder ι]
    (x : ι → X) (hdir : IsDirectedIndex ι)
    (hx : d.IsCauchyNet x) :
    QuasiMetric.ennreal.IsCauchyNet (fun i ↦ q (x i)) := by
  intro ε hε
  by_cases hα : α = 0
  · let i₀ : ι := Classical.choice hdir.1
    refine ⟨i₀, ?_⟩
    intro i j _hi _hij
    have hzero : QuasiMetric.ennreal.edist (q (x i)) (q (x j)) = 0 := by
      apply le_antisymm _ (zero_le _)
      simpa [hα] using hq (x i) (x j)
    simpa [hzero] using ENNReal.coe_pos.mpr hε
  · have hαpos : 0 < α := pos_iff_ne_zero.mpr hα
    obtain ⟨i₀, hi₀⟩ := hx (ε / α) (div_pos hε hαpos)
    refine ⟨i₀, ?_⟩
    intro i j hi hij
    calc
      QuasiMetric.ennreal.edist (q (x i)) (q (x j))
          ≤ (α : ℝ≥0∞) * d.edist (x i) (x j) := hq _ _
      _ < (α : ℝ≥0∞) * ((ε / α : ℝ≥0) : ℝ≥0∞) :=
        ENNReal.mul_lt_mul_right (ENNReal.coe_ne_zero.mpr hα)
          ENNReal.coe_ne_top (hi₀ i j hi hij)
      _ = (ε : ℝ≥0∞) := by
        rw [← ENNReal.coe_mul, mul_comm, div_mul_cancel₀ ε hα]

/-- For a weighted scalar net, a least-upper-bound statement for the
truncated sharp coordinates is exactly the `d_R`-limit equation. -/
theorem ennreal_isDLimit_of_weighted_sharp_isLUB
    {κ : Type u} [Preorder κ]
    (hdir : IsDirectedIndex κ)
    (z : κ → ℝ≥0∞) (r : κ → ℝ≥0)
    (hsharpMono : Monotone (fun k ↦ z k - (r k : ℝ≥0∞)))
    (hradius : ∀ ε : ℝ≥0, 0 < ε →
      ∃ k : κ, ∀ l : κ, k ≤ l → r l < ε)
    (z₀ : ℝ≥0∞)
    (hsharp : IsLUB
      (Set.range (fun k ↦ z k - (r k : ℝ≥0∞))) z₀) :
    QuasiMetric.ennreal.IsDLimit z z₀ := by
  have hzsup : (⨆ k : κ, z k - (r k : ℝ≥0∞)) = z₀ := by
    apply le_antisymm
    · apply iSup_le
      intro k
      exact hsharp.1 ⟨k, rfl⟩
    · apply hsharp.2
      intro b hb
      obtain ⟨k, rfl⟩ := hb
      exact le_iSup (fun l : κ ↦ z l - (r l : ℝ≥0∞)) k
  intro y
  change z₀ - y = netLimsup (fun i ↦ z i - y)
  apply le_antisymm
  · rw [← hzsup, ENNReal.iSup_sub]
    apply iSup_le
    intro k
    apply le_iInf
    intro j
    obtain ⟨l, hkl, hjl⟩ := hdir.2 k j
    calc
      (z k - (r k : ℝ≥0∞)) - y
          ≤ (z l - (r l : ℝ≥0∞)) - y :=
        tsub_le_tsub_right (hsharpMono hkl) y
      _ ≤ z l - y :=
        tsub_le_tsub_right (tsub_le_self :
          z l - (r l : ℝ≥0∞) ≤ z l) y
      _ ≤ ⨆ m : κ, ⨆ (_h : j ≤ m), z m - y :=
        le_iSup_of_le l (le_iSup_of_le hjl le_rfl)
  · apply ENNReal.le_of_forall_pos_le_add
    intro ε hε _hfinite
    obtain ⟨k, hk⟩ := hradius ε hε
    refine (iInf_le (fun j : κ ↦
      ⨆ l : κ, ⨆ (_h : j ≤ l), z l - y) k).trans ?_
    apply iSup_le
    intro l
    apply iSup_le
    intro hkl
    have hzsplit : z l ≤
        (z l - (r l : ℝ≥0∞)) + (r l : ℝ≥0∞) := by
      simpa [add_comm] using
        (le_add_tsub : z l ≤ (r l : ℝ≥0∞) +
          (z l - (r l : ℝ≥0∞)))
    calc
      z l - y
          ≤ ((z l - (r l : ℝ≥0∞)) + (r l : ℝ≥0∞)) - y :=
        tsub_le_tsub_right hzsplit y
      _ ≤ (z l - (r l : ℝ≥0∞) - y) + (r l : ℝ≥0∞) :=
        add_tsub_le_tsub_add
      _ ≤ (z₀ - y) + (ε : ℝ≥0∞) := by
        apply add_le_add
        · exact tsub_le_tsub_right (hsharp.1 ⟨l, rfl⟩) y
        · exact ENNReal.coe_le_coe.mpr (hk l hkl).le

/-- Convert topological continuity of `sharp` back to order-theoretic Scott
continuity. -/
theorem HasScottContinuousSharp.scottContinuous
    {α : ℝ≥0} {q : X → ℝ≥0∞}
    (hq : d.HasScottContinuousSharp α q) :
    ScottContinuous (d.sharp α q) := by
  change Continuous (fun p : WithScott d.FormalBall ↦
    WithScott.toScott (d.sharp α q (WithScott.ofScott p))) at hq
  have hs : ScottContinuous (fun p : WithScott d.FormalBall ↦
      WithScott.toScott (d.sharp α q (WithScott.ofScott p))) := by
    rw [← scottContinuousOn_univ]
    apply (Topology.IsScott.scottContinuousOn_iff_continuous
      (D := Set.univ) (by simp)).mpr
    exact hq
  exact hs

/-- The converse formal-ball criterion with the Cauchy-weighted subnet step
made explicit. -/
theorem IsStandard.isYonedaContinuous_of_hasScottContinuousSharp
    (_hstandard : d.IsStandard)
    {α : ℝ≥0} {q : X → ℝ≥0∞}
    (hqLip : d.IsLipschitz α q)
    (hqSharp : d.HasScottContinuousSharp α q) :
    d.IsYonedaContinuous q where
  maps_cauchy := by
    intro ι _ x hdir hx
    exact hqLip.maps_cauchy d x hdir hx
  maps_dLimit := by
    intro ι _ x x₀ hdir hxCauchy hxLimit
    let W : d.CauchyWeightedSubnet x :=
      CauchyWeightedSubnet.ofCauchy d x hdir hxCauchy
    let p : W.Index → d.FormalBall := fun k ↦
      ⟨x (W.map k), W.radius k⟩
    have hpLUB : IsLUB (Set.range p)
        (⟨x₀, 0⟩ : d.FormalBall) := by
      simpa only [p] using
        CauchyWeightedSubnet.formalBall_isLUB d W hxCauchy hxLimit
    have hpRangeNonempty : (Set.range p).Nonempty := by
      let k : W.Index := Classical.choice W.directed.1
      exact ⟨p k, ⟨k, rfl⟩⟩
    have hpRangeDirected : DirectedOn (· ≤ ·) (Set.range p) := by
      intro a ha b hb
      obtain ⟨i, rfl⟩ := ha
      obtain ⟨j, rfl⟩ := hb
      obtain ⟨k, hik, hjk⟩ := W.directed.2 i j
      exact ⟨p k, ⟨k, rfl⟩,
        W.formalBall_monotone hik,
        W.formalBall_monotone hjk⟩
    have hsharpImage := hqSharp.scottContinuous d
      hpRangeNonempty hpRangeDirected hpLUB
    have hsharpRange :
        (d.sharp α q) '' Set.range p =
          Set.range (fun k : W.Index ↦
            q (x (W.map k)) -
              (((α * W.radius k : ℝ≥0)) : ℝ≥0∞)) := by
      ext v
      constructor
      · rintro ⟨b, ⟨k, rfl⟩, rfl⟩
        exact ⟨k, by simp [p, sharp]⟩
      · rintro ⟨k, rfl⟩
        exact ⟨p k, ⟨k, rfl⟩, by simp [p, sharp]⟩
    have hsharpLUB : IsLUB
        (Set.range (fun k : W.Index ↦
          q (x (W.map k)) -
            (((α * W.radius k : ℝ≥0)) : ℝ≥0∞)))
        (q x₀) := by
      rw [hsharpRange] at hsharpImage
      simpa [p, sharp] using hsharpImage
    have hsharpMono : Monotone (fun k : W.Index ↦
        q (x (W.map k)) -
          (((α * W.radius k : ℝ≥0)) : ℝ≥0∞)) := by
      intro i j hij
      simpa [p, sharp] using
        d.sharp_monotone hqLip (W.formalBall_monotone hij)
    have hscaled : ∀ ε : ℝ≥0, 0 < ε →
        ∃ k : W.Index, ∀ l : W.Index, k ≤ l →
          α * W.radius l < ε :=
      eventually_mul_lt_of_eventually_lt W.directed.1
        W.radius W.radius_eventually_lt α
    have hsubLimit : QuasiMetric.ennreal.IsDLimit
        (fun k : W.Index ↦ q (x (W.map k))) (q x₀) :=
      ennreal_isDLimit_of_weighted_sharp_isLUB W.directed
        (fun k ↦ q (x (W.map k)))
        (fun k ↦ α * W.radius k) hsharpMono hscaled (q x₀)
        hsharpLUB
    have himageCauchy : QuasiMetric.ennreal.IsCauchyNet
        (fun i ↦ q (x i)) :=
      hqLip.maps_cauchy d x hdir hxCauchy
    intro y
    calc
      QuasiMetric.ennreal.edist (q x₀) y
          = netLimsup (fun k : W.Index ↦
              QuasiMetric.ennreal.edist (q (x (W.map k))) y) :=
        hsubLimit y
      _ = netLimsup (fun i : ι ↦
              QuasiMetric.ennreal.edist (q (x i)) y) :=
        netLimsup_edist_comp_eq QuasiMetric.ennreal
          (fun i ↦ q (x i)) W.directed himageCauchy W.map
          W.map_monotone W.map_cofinal y

/-- Scott continuity of `sharp` restricts at radius zero to lower
semicontinuity on the original quasi-metric space. -/
theorem HasScottContinuousSharp.isLowerSemicontinuous
    {α : ℝ≥0} {q : X → ℝ≥0∞}
    (hq : d.HasScottContinuousSharp α q) :
    d.IsLowerSemicontinuous q := by
  unfold IsLowerSemicontinuous
  have hembed : Continuous (fun x : d.DScott ↦
      WithScott.toScott (⟨x, 0⟩ : d.FormalBall)) :=
    continuous_induced_dom
  apply (hq.comp hembed).congr
  intro x
  simp [Function.comp_def, sharp]

end QuasiMetric
end LipschitzYonedaFinalTopology
