import Practice.DomainTheory.Papers.LipschitzYonedaFinalTopology.CenterPoints

/-!
# Finite cone interpolation

This module formalizes the constructive order-theoretic core of
`lem:interpolation` (source lines 375--421).  Its hypotheses expose exactly
the two formal-ball inputs used by the paper proof:

* center-point balls form a Scott basis;
* the sharp transform `q♯(x,r) = q(x) - αr` is Scott-continuous.

The result chooses a center and a positive finite height for every constraint,
and proves all displayed strict inequalities and the global envelope bound.
The additional literature fact that these finite cone envelopes are
Yoneda-continuous is intentionally not assumed here.
-/

set_option autoImplicit false
set_option linter.unnecessarySimpa false

open Set Topology
open scoped NNReal ENNReal

noncomputable section

universe u v

namespace LipschitzYonedaFinalTopology
namespace QuasiMetric

variable {X : Type u} (d : QuasiMetric X)

/-- The maximum of a nonempty finite family of labelled cones. -/
def finiteConeEnvelope
    {ι : Type v} [Fintype ι] [Nonempty ι]
    (α : ℝ≥0) (center : ι → X) (height : ι → ℝ≥0∞) :
    X → ℝ≥0∞ :=
  d.finiteConeFamilyMax α Finset.univ Finset.univ_nonempty center height

/-- The finite envelope is `α`-Lipschitz. -/
theorem finiteConeEnvelope_isLipschitz
    {ι : Type v} [Fintype ι] [Nonempty ι]
    (α : ℝ≥0) (center : ι → X) (height : ι → ℝ≥0∞) :
    d.IsLipschitz α (d.finiteConeEnvelope α center height) :=
  d.finiteConeFamilyMax_isLipschitz
    α Finset.univ Finset.univ_nonempty center height

/-- Output of finite cone interpolation for a nonempty finite family of
point-value constraints. -/
structure FiniteConeInterpolation
    {ι : Type v} [Fintype ι] [Nonempty ι]
    (α : ℝ≥0) (q : X → ℝ≥0∞)
    (sample : ι → X) (threshold : ι → ℝ≥0) where
  /-- Center point selected for each constraint. -/
  center : ι → X
  /-- Positive finite cone height selected for each constraint. -/
  height : ι → ℝ≥0
  center_isCenter : ∀ i, d.IsCenterPoint (center i)
  height_pos : ∀ i, 0 < height i
  height_lt_target : ∀ i, (height i : ℝ≥0∞) < q (center i)
  envelope_le :
    d.finiteConeEnvelope α center (fun i ↦ (height i : ℝ≥0∞)) ≤ q
  exceeds_threshold : ∀ i,
    (threshold i : ℝ≥0∞) <
      d.finiteConeEnvelope α center
        (fun j ↦ (height j : ℝ≥0∞)) (sample i)

namespace FiniteConeInterpolation

variable {d}

/-- The interpolating envelope supplied by the result. -/
def envelope
    {ι : Type v} [Fintype ι] [Nonempty ι]
    {α : ℝ≥0} {q : X → ℝ≥0∞}
    {sample : ι → X} {threshold : ι → ℝ≥0}
    (R : d.FiniteConeInterpolation α q sample threshold) :
    X → ℝ≥0∞ :=
  d.finiteConeEnvelope α R.center (fun i ↦ (R.height i : ℝ≥0∞))

/-- The resulting envelope is `α`-Lipschitz, independently of the analytic
continuity input used to construct it. -/
theorem envelope_isLipschitz
    {ι : Type v} [Fintype ι] [Nonempty ι]
    {α : ℝ≥0} {q : X → ℝ≥0∞}
    {sample : ι → X} {threshold : ι → ℝ≥0}
    (R : d.FiniteConeInterpolation α q sample threshold) :
    d.IsLipschitz α R.envelope :=
  d.finiteConeEnvelope_isLipschitz α R.center
    (fun i ↦ (R.height i : ℝ≥0∞))

end FiniteConeInterpolation

/-- Source lemma `lem:interpolation`, order-theoretic core.

For every finite nonempty family of strict point constraints below an
`α`-Lipschitz target, enough center points and Scott continuity of `q♯`
produce a finite cone envelope below `q` which satisfies all constraints and
whose finite positive heights remain strictly below `q` at their centers. -/
noncomputable def finiteConeInterpolation
    {ι : Type v} [Fintype ι] [Nonempty ι]
    {α : ℝ≥0} (hα : 0 < α)
    {q : X → ℝ≥0∞} (hqLip : d.IsLipschitz α q)
    (hqSharp : d.HasScottContinuousSharp α q)
    (hcenters : d.HasEnoughCenterPoints)
    (sample : ι → X) (threshold : ι → ℝ≥0)
    (hthreshold : ∀ i,
      (threshold i : ℝ≥0∞) < q (sample i)) :
    d.FiniteConeInterpolation α q sample threshold := by
  let U : ι → Set (WithScott d.FormalBall) := fun i ↦
    {p | (threshold i : ℝ≥0∞) <
      d.sharp α q (WithScott.ofScott p)}
  have hUopen : ∀ i, IsOpen (U i) := by
    intro i
    exact hqSharp.isOpen_superlevel (d := d) (threshold i)
  have hsampleU : ∀ i,
      WithScott.toScott (⟨sample i, 0⟩ : d.FormalBall) ∈ U i := by
    intro i
    simpa [U] using hthreshold i
  have hselection : ∀ i, ∃ x : X, ∃ t : ℝ≥0,
      d.IsCenterPoint x ∧ 0 < t ∧
      d.edist x (sample i) < (t : ℝ≥0∞) ∧
      WithScott.toScott (⟨x, t⟩ : d.FormalBall) ∈ U i := by
    intro i
    exact HasEnoughCenterPoints.exists_center_radius_mem
      (d := d) hcenters (hUopen i) (hsampleU i)
  choose center radius hcenter hradius hdistance hmem using hselection
  let height : ι → ℝ≥0 := fun i ↦ threshold i + α * radius i
  have hheight_pos : ∀ i, 0 < height i := by
    intro i
    dsimp [height]
    calc
      0 < α * radius i := mul_pos hα (hradius i)
      _ ≤ threshold i + α * radius i := le_add_left le_rfl
  have hsharp_lt : ∀ i,
      (threshold i : ℝ≥0∞) <
        q (center i) -
          (α : ℝ≥0∞) * (radius i : ℝ≥0∞) := by
    intro i
    simpa [U, sharp] using hmem i
  have hheight_lt : ∀ i,
      (height i : ℝ≥0∞) < q (center i) := by
    intro i
    have hi := lt_tsub_iff_right.mp (hsharp_lt i)
    simpa [height, ENNReal.coe_add, ENNReal.coe_mul] using hi
  refine
    { center := center
      height := height
      center_isCenter := hcenter
      height_pos := hheight_pos
      height_lt_target := hheight_lt
      envelope_le := ?_
      exceeds_threshold := ?_ }
  · apply d.finiteConeFamilyMax_le_of_isLipschitz
      Finset.univ_nonempty hqLip
    intro i _hi
    exact (hheight_lt i).le
  · intro i
    have hαcoe : (α : ℝ≥0∞) ≠ 0 := by
      exact ENNReal.coe_ne_zero.mpr hα.ne'
    have hmul :
        (α : ℝ≥0∞) * d.edist (center i) (sample i) <
          (α : ℝ≥0∞) * (radius i : ℝ≥0∞) :=
      ENNReal.mul_lt_mul_right hαcoe ENNReal.coe_ne_top (hdistance i)
    have hcone :
        (threshold i : ℝ≥0∞) <
          d.cone α (center i) (height i) (sample i) := by
      rw [cone]
      apply lt_tsub_iff_right.mpr
      simpa [height, ENNReal.coe_add, ENNReal.coe_mul] using
        ENNReal.add_lt_add_left
          (a := (threshold i : ℝ≥0∞)) ENNReal.coe_ne_top hmul
    exact hcone.trans_le <|
      Finset.le_sup'
        (fun j ↦ d.cone α (center j) (height j) (sample i))
        (Finset.mem_univ i)

end QuasiMetric
end LipschitzYonedaFinalTopology
