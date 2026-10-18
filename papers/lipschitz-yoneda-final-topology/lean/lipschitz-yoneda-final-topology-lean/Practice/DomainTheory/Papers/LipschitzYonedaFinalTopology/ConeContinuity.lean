import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Practice.DomainTheory.Papers.LipschitzYonedaFinalTopology.SharpConverse
import Practice.DomainTheory.Papers.LipschitzYonedaFinalTopology.Interpolation

/-!
# Continuity of finite center-cone envelopes

The source's cone fact is proved here from the definition of a center point.
For a finite height `a`, strict superlevels of the sharp transform of
`y ↦ a - α d(x,y)` are either empty or one of the defining Scott-open
formal-ball balls centered at `(x,0)`.
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

/-- Arbitrary pointwise suprema of continuous maps into Scott `[0,+∞]`
are continuous. -/
theorem continuous_withScott_iSup
    {A : Type u} [TopologicalSpace A]
    {ι : Type u} (f : ι → A → ℝ≥0∞)
    (hf : ∀ i, Continuous (fun x ↦ WithScott.toScott (f i x))) :
    Continuous (fun x ↦ WithScott.toScott (⨆ i, f i x)) := by
  letI : CompleteLinearOrder (WithScott ℝ≥0∞) :=
    inferInstanceAs (CompleteLinearOrder ℝ≥0∞)
  rw [continuous_def]
  intro U hU
  rcases (Topology.IsScott.isOpen_iff_Iic_compl_or_univ U).mp hU with
    rfl | ⟨a, rfl⟩
  · simp
  · have hpreimage :
        (fun x ↦ WithScott.toScott (⨆ i, f i x)) ⁻¹' (Set.Iic a)ᶜ =
          ⋃ i, (fun x ↦ WithScott.toScott (f i x)) ⁻¹' (Set.Iic a)ᶜ := by
      ext x
      simp only [mem_preimage, mem_compl_iff, mem_Iic, mem_iUnion]
      simpa only [not_le] using
        (lt_iSup_iff :
          WithScott.ofScott a < (⨆ i, f i x) ↔
            ∃ i, WithScott.ofScott a < f i x)
    rw [hpreimage]
    exact isOpen_iUnion fun i ↦ ((hf i).isOpen_preimage _
      isClosed_Iic.isOpen_compl)

/-- The sharp transform of a finite-height cone centered at a center point
is Scott-continuous. -/
theorem cone_hasScottContinuousSharp
    {x : X} (hx : d.IsCenterPoint x)
    (α a : ℝ≥0) :
    d.HasScottContinuousSharp α (d.cone α x (a : ℝ≥0∞)) := by
  unfold HasScottContinuousSharp
  rw [continuous_def]
  intro U hU
  letI : CompleteLinearOrder (WithScott ℝ≥0∞) :=
    inferInstanceAs (CompleteLinearOrder ℝ≥0∞)
  rcases (Topology.IsScott.isOpen_iff_Iic_compl_or_univ U).mp hU with
    rfl | ⟨b, rfl⟩
  · simp
  · let b₀ : ℝ≥0∞ := WithScott.ofScott b
    by_cases hα : α = 0
    · by_cases hba : b₀ < (a : ℝ≥0∞)
      · have hpreimage :
            (fun p : WithScott d.FormalBall ↦
              WithScott.toScott
                (d.sharp α (d.cone α x (a : ℝ≥0∞))
                  (WithScott.ofScott p))) ⁻¹' (Set.Iic b)ᶜ = Set.univ := by
          ext p
          simp only [mem_preimage, mem_compl_iff, mem_Iic, mem_univ,
            iff_true, not_le]
          change b₀ < d.sharp α (d.cone α x (a : ℝ≥0∞))
            (WithScott.ofScott p)
          simpa [sharp, cone, hα] using hba
        rw [hpreimage]
        exact isOpen_univ
      · have hpreimage :
            (fun p : WithScott d.FormalBall ↦
              WithScott.toScott
                (d.sharp α (d.cone α x (a : ℝ≥0∞))
                  (WithScott.ofScott p))) ⁻¹' (Set.Iic b)ᶜ = ∅ := by
          ext p
          simp only [mem_preimage, mem_compl_iff, mem_Iic,
            mem_empty_iff_false, iff_false]
          intro hp
          apply hp
          change d.sharp α (d.cone α x (a : ℝ≥0∞))
            (WithScott.ofScott p) ≤ b₀
          simpa [sharp, cone, hα] using (le_of_not_gt hba)
        rw [hpreimage]
        exact isOpen_empty
    · have hαpos : 0 < α := pos_iff_ne_zero.mpr hα
      by_cases hba : b₀ < (a : ℝ≥0∞)
      · let gap : ℝ≥0 := ((a : ℝ≥0∞) - b₀).toNNReal
        have hgapTop : (a : ℝ≥0∞) - b₀ ≠ ∞ :=
          ne_top_of_le_ne_top ENNReal.coe_ne_top tsub_le_self
        have hgapCoe : (gap : ℝ≥0∞) = (a : ℝ≥0∞) - b₀ :=
          ENNReal.coe_toNNReal hgapTop
        have hgapPos : 0 < gap := by
          apply ENNReal.coe_pos.mp
          rw [hgapCoe]
          exact tsub_pos_iff_lt.mpr hba
        let ε : ℝ≥0 := gap / α
        have hεpos : 0 < ε := div_pos hgapPos hαpos
        have hαε :
            (α : ℝ≥0∞) * (ε : ℝ≥0∞) =
              (a : ℝ≥0∞) - b₀ := by
          rw [← hgapCoe, ← ENNReal.coe_mul]
          change ((α * (gap / α) : ℝ≥0) : ℝ≥0∞) = gap
          rw [mul_comm, div_mul_cancel₀ gap hα]
        have hthreshold (p : d.FormalBall) :
            b₀ < d.sharp α (d.cone α x (a : ℝ≥0∞)) p ↔
              d.edist x p.center + (p.radius : ℝ≥0∞) <
                (ε : ℝ≥0∞) := by
          rw [sharp, cone, tsub_tsub, ← mul_add]
          rw [lt_tsub_iff_left]
          have hgapForm :
              (α : ℝ≥0∞) *
                    (d.edist x p.center + (p.radius : ℝ≥0∞)) <
                  (a : ℝ≥0∞) - b₀ ↔
                (α : ℝ≥0∞) *
                    (d.edist x p.center + (p.radius : ℝ≥0∞)) + b₀ <
                  (a : ℝ≥0∞) :=
            lt_tsub_iff_right
          rw [← hgapForm, ← hαε]
          constructor
          · intro hmul
            by_contra hnot
            have hle : (ε : ℝ≥0∞) ≤
                d.edist x p.center + (p.radius : ℝ≥0∞) :=
              le_of_not_gt hnot
            exact (not_lt_of_ge (mul_le_mul_left' hle
              (α : ℝ≥0∞))) hmul
          · exact ENNReal.mul_lt_mul_right
              (ENNReal.coe_ne_zero.mpr hα) ENNReal.coe_ne_top
        have hpreimage :
            (fun p : WithScott d.FormalBall ↦
              WithScott.toScott
                (d.sharp α (d.cone α x (a : ℝ≥0∞))
                  (WithScott.ofScott p))) ⁻¹' (Set.Iic b)ᶜ =
              d.formalBallOpenBall x ε := by
          ext p
          simp only [mem_preimage, mem_compl_iff, mem_Iic,
            formalBallOpenBall, mem_setOf_eq]
          change (¬d.sharp α (d.cone α x (a : ℝ≥0∞))
              (WithScott.ofScott p) ≤ b₀) ↔
            d.formalBallEdist (⟨x, 0⟩ : d.FormalBall)
              (WithScott.ofScott p) < (ε : ℝ≥0∞)
          rw [not_le, hthreshold]
          simp [formalBallEdist]
        rw [hpreimage]
        exact hx ε hεpos
      · have hsharpLe (p : d.FormalBall) :
            d.sharp α (d.cone α x (a : ℝ≥0∞)) p ≤
              (a : ℝ≥0∞) :=
          (tsub_le_self.trans tsub_le_self)
        have hpreimage :
            (fun p : WithScott d.FormalBall ↦
              WithScott.toScott
                (d.sharp α (d.cone α x (a : ℝ≥0∞))
                  (WithScott.ofScott p))) ⁻¹' (Set.Iic b)ᶜ = ∅ := by
          ext p
          simp only [mem_preimage, mem_compl_iff, mem_Iic,
            mem_empty_iff_false, iff_false]
          intro hp
          have hp' : b₀ < d.sharp α
              (d.cone α x (a : ℝ≥0∞)) (WithScott.ofScott p) := by
            simpa only [not_le] using hp
          exact hba (hp'.trans_le (hsharpLe _))
        rw [hpreimage]
        exact isOpen_empty

/-- A finite-height center cone is lower semicontinuous. -/
theorem cone_isLowerSemicontinuous
    {x : X} (hx : d.IsCenterPoint x)
    (α a : ℝ≥0) :
    d.IsLowerSemicontinuous (d.cone α x (a : ℝ≥0∞)) :=
  (d.cone_hasScottContinuousSharp hx α a).isLowerSemicontinuous

/-- On a standard space, a finite-height center cone is Yoneda-continuous. -/
theorem IsStandard.cone_isYonedaContinuous
    (hstandard : d.IsStandard)
    {x : X} (hx : d.IsCenterPoint x)
    (α a : ℝ≥0) :
    d.IsYonedaContinuous (d.cone α x (a : ℝ≥0∞)) :=
  hstandard.isYonedaContinuous_of_hasScottContinuousSharp d
    (d.cone_isLipschitz α x (a : ℝ≥0∞))
    (d.cone_hasScottContinuousSharp hx α a)

/-- The sharp transform of a finite maximum of finite center cones is
Scott-continuous. -/
theorem finiteConeEnvelope_hasScottContinuousSharp
    {ι : Type u} [Fintype ι] [Nonempty ι]
    (α : ℝ≥0) (center : ι → X) (height : ι → ℝ≥0)
    (hcenter : ∀ i, d.IsCenterPoint (center i)) :
    d.HasScottContinuousSharp α
      (d.finiteConeEnvelope α center
        (fun i ↦ (height i : ℝ≥0∞))) := by
  have hcone (i : ι) :=
    d.cone_hasScottContinuousSharp (hcenter i) α (height i)
  have hsup := continuous_withScott_iSup
    (fun i (p : WithScott d.FormalBall) ↦
      d.sharp α (d.cone α (center i) (height i : ℝ≥0∞))
        (WithScott.ofScott p))
    (fun i ↦ hcone i)
  unfold HasScottContinuousSharp
  apply hsup.congr
  intro p
  congr 1
  unfold sharp finiteConeEnvelope finiteConeFamilyMax
  rw [Finset.sup'_univ_eq_ciSup, ENNReal.iSup_sub]

/-- A finite center-cone envelope is lower semicontinuous. -/
theorem finiteConeEnvelope_isLowerSemicontinuous
    {ι : Type u} [Fintype ι] [Nonempty ι]
    (α : ℝ≥0) (center : ι → X) (height : ι → ℝ≥0)
    (hcenter : ∀ i, d.IsCenterPoint (center i)) :
    d.IsLowerSemicontinuous
      (d.finiteConeEnvelope α center
        (fun i ↦ (height i : ℝ≥0∞))) :=
  (d.finiteConeEnvelope_hasScottContinuousSharp
    α center height hcenter).isLowerSemicontinuous

/-- On a standard space, a finite center-cone envelope is
Yoneda-continuous. -/
theorem IsStandard.finiteConeEnvelope_isYonedaContinuous
    (hstandard : d.IsStandard)
    {ι : Type u} [Fintype ι] [Nonempty ι]
    (α : ℝ≥0) (center : ι → X) (height : ι → ℝ≥0)
    (hcenter : ∀ i, d.IsCenterPoint (center i)) :
    d.IsYonedaContinuous
      (d.finiteConeEnvelope α center
        (fun i ↦ (height i : ℝ≥0∞))) :=
  hstandard.isYonedaContinuous_of_hasScottContinuousSharp d
    (d.finiteConeEnvelope_isLipschitz α center
      (fun i ↦ (height i : ℝ≥0∞)))
    (d.finiteConeEnvelope_hasScottContinuousSharp
      α center height hcenter)

end QuasiMetric
end LipschitzYonedaFinalTopology
