import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.Fintype.Sum
import Practice.DomainTheory.Papers.LipschitzYonedaFinalTopology.DomainStructure
import Practice.DomainTheory.Papers.LipschitzYonedaFinalTopology.Interpolation
import Practice.DomainTheory.Papers.LipschitzYonedaFinalTopology.LowerMapSuprema

/-!
# Directed finite-cone approximation

This file replaces the manuscript's appeal to the pointwise topology on a
fixed layer by an equivalent Scott argument.  All nonempty finite envelopes
below a target form a directed family, and finite cone interpolation proves
that their pointwise supremum is the target.  Consequently, any relatively
open layer neighborhood of the target contains one such envelope.

The two established analytic facts from the cited literature are kept in the
explicit `StandardConeFacts` interface below.  They will be proved from the
source definition of standardness in a later module; until then, no headline
theorem is stated using this interface.
-/

set_option autoImplicit false
set_option linter.unnecessarySimpa false

open Set Function Topology
open scoped NNReal ENNReal Topology

noncomputable section

universe u

namespace LipschitzYonedaFinalTopology
namespace QuasiMetric

variable {X : Type u} {d : QuasiMetric X}

/-- The two analytic consequences of standardness used by cone
interpolation: the sharp criterion, and lower/Yoneda continuity of finite
envelopes based at center points.  This is a proof interface for intermediate
modules, not an added hypothesis in the final theorem. -/
structure StandardConeFacts (d : QuasiMetric X) (hstandard : d.IsStandard) : Prop where
  sharp_of_inLayer : ∀ (α : ℝ≥0) (q : d.LSpace),
    d.InLayer α q → d.HasScottContinuousSharp α q
  finiteEnvelope_lower :
    ∀ {ι : Type u} [Fintype ι] [Nonempty ι]
      (α : ℝ≥0) (center : ι → X) (height : ι → ℝ≥0),
      (∀ i, d.IsCenterPoint (center i)) →
      d.IsLowerSemicontinuous
        (d.finiteConeEnvelope α center
          (fun i ↦ (height i : ℝ≥0∞)))
  finiteEnvelope_yoneda :
    ∀ {ι : Type u} [Fintype ι] [Nonempty ι]
      (α : ℝ≥0) (center : ι → X) (height : ι → ℝ≥0),
      (∀ i, d.IsCenterPoint (center i)) →
      d.IsYonedaContinuous
        (d.finiteConeEnvelope α center
          (fun i ↦ (height i : ℝ≥0∞)))

/-- A nonempty labelled finite family of positive center cones lying
strictly below a target.  Keeping the finite label type as data preserves
duplicate centers exactly as in the manuscript. -/
structure FiniteConeApproximation
    (d : QuasiMetric X) (α : ℝ≥0) (q : X → ℝ≥0∞) where
  Node : Type u
  [nodeFintype : Fintype Node]
  [nodeNonempty : Nonempty Node]
  center : Node → X
  height : Node → ℝ≥0
  center_isCenter : ∀ i, d.IsCenterPoint (center i)
  height_pos : ∀ i, 0 < height i
  height_lt_target : ∀ i, (height i : ℝ≥0∞) < q (center i)

namespace FiniteConeApproximation

attribute [instance] nodeFintype nodeNonempty

variable {α : ℝ≥0} {q : X → ℝ≥0∞}

/-- The raw finite cone envelope represented by an approximation. -/
def envelope (A : FiniteConeApproximation d α q) : X → ℝ≥0∞ :=
  d.finiteConeEnvelope α A.center
    (fun i ↦ (A.height i : ℝ≥0∞))

/-- Every approximation envelope has the displayed Lipschitz constant. -/
theorem envelope_isLipschitz
    (A : FiniteConeApproximation d α q) :
    d.IsLipschitz α A.envelope :=
  d.finiteConeEnvelope_isLipschitz α A.center
    (fun i ↦ (A.height i : ℝ≥0∞))

/-- An approximation lies below its Lipschitz target. -/
theorem envelope_le_target
    (A : FiniteConeApproximation d α q)
    (hq : d.IsLipschitz α q) :
    A.envelope ≤ q := by
  exact d.finiteConeFamilyMax_le_of_isLipschitz
    Finset.univ_nonempty hq
    (fun i _hi ↦ (A.height_lt_target i).le)

/-- The envelope attains at least the prescribed height at each labelled
center. -/
theorem height_le_envelope_at_center
    (A : FiniteConeApproximation d α q) (i : A.Node) :
    (A.height i : ℝ≥0∞) ≤ A.envelope (A.center i) := by
  have hcone :
      d.cone α (A.center i) (A.height i) (A.center i) ≤
        A.envelope (A.center i) := by
    unfold envelope QuasiMetric.finiteConeEnvelope
      QuasiMetric.finiteConeFamilyMax
    exact Finset.le_sup'
      (fun j ↦ d.cone α (A.center j) (A.height j) (A.center i))
      (Finset.mem_univ i)
  simpa [cone_at_center] using hcone

/-- Package a finite envelope as an element of `𝓛∞`, using the two analytic
standard-space facts. -/
def toLInf
    {hstandard : d.IsStandard}
    (facts : d.StandardConeFacts hstandard)
    (hα : 0 < α)
    (A : FiniteConeApproximation d α q) : d.LInf := by
  let lower : d.LowerMap :=
    ⟨A.envelope,
      facts.finiteEnvelope_lower α A.center A.height A.center_isCenter⟩
  refine ⟨WithScott.toScott lower, ⟨α, hα, ?_, ?_⟩⟩
  · exact A.envelope_isLipschitz
  · exact facts.finiteEnvelope_yoneda α A.center A.height A.center_isCenter

@[simp]
theorem toLInf_apply
    {hstandard : d.IsStandard}
    (facts : d.StandardConeFacts hstandard)
    (hα : 0 < α)
    (A : FiniteConeApproximation d α q) (x : X) :
    A.toLInf facts hα x = A.envelope x :=
  rfl

/-- A packaged approximation belongs to its fixed Lipschitz layer. -/
theorem toLInf_inLayer
    {hstandard : d.IsStandard}
    (facts : d.StandardConeFacts hstandard)
    (hα : 0 < α)
    (A : FiniteConeApproximation d α q) :
    d.InLayer α (A.toLInf facts hα).1 :=
  ⟨A.envelope_isLipschitz,
    facts.finiteEnvelope_yoneda α A.center A.height A.center_isCenter⟩

/-- Positive prescribed heights ensure that a packaged finite envelope is
not the zero function. -/
theorem toLInf_ne_zero
    {hstandard : d.IsStandard}
    (facts : d.StandardConeFacts hstandard)
    (hα : 0 < α)
    (A : FiniteConeApproximation d α q) :
    A.toLInf facts hα ≠ d.zeroLInf := by
  intro hzero
  let i : A.Node := Classical.choice inferInstance
  have hvalue : A.toLInf facts hα (A.center i) = 0 := by
    simpa using congrArg (fun g : d.LInf ↦ g (A.center i)) hzero
  have hpos : (0 : ℝ≥0∞) < A.envelope (A.center i) :=
    (ENNReal.coe_pos.mpr (A.height_pos i)).trans_le
      (A.height_le_envelope_at_center i)
  change A.envelope (A.center i) = 0 at hvalue
  rw [hvalue] at hpos
  exact lt_irrefl 0 hpos

/-- Disjoint union combines two labelled finite approximations. -/
def combine
    (A B : FiniteConeApproximation d α q) :
    FiniteConeApproximation d α q where
  Node := Sum A.Node B.Node
  center := Sum.elim A.center B.center
  height := Sum.elim A.height B.height
  center_isCenter
    | Sum.inl i => A.center_isCenter i
    | Sum.inr i => B.center_isCenter i
  height_pos
    | Sum.inl i => A.height_pos i
    | Sum.inr i => B.height_pos i
  height_lt_target
    | Sum.inl i => A.height_lt_target i
    | Sum.inr i => B.height_lt_target i

/-- Every cone in the left family lies below the combined envelope. -/
theorem envelope_le_combine_left
    (A B : FiniteConeApproximation d α q) :
    A.envelope ≤ (A.combine B).envelope := by
  apply d.finiteConeFamilyMax_le_of_isLipschitz
    Finset.univ_nonempty (A.combine B).envelope_isLipschitz
  intro i _hi
  change (A.height i : ℝ≥0∞) ≤ (A.combine B).envelope (A.center i)
  have hcone :
      d.cone α (A.center i) (A.height i) (A.center i) ≤
        (A.combine B).envelope (A.center i) := by
    unfold envelope combine QuasiMetric.finiteConeEnvelope
      QuasiMetric.finiteConeFamilyMax
    simpa using Finset.le_sup'
      (fun z : Sum A.Node B.Node ↦
        d.cone α (Sum.elim A.center B.center z)
          (Sum.elim (fun i ↦ (A.height i : ℝ≥0∞))
            (fun i ↦ (B.height i : ℝ≥0∞)) z) (A.center i))
      (Finset.mem_univ (Sum.inl i))
  simpa [cone_at_center] using hcone

/-- Every cone in the right family lies below the combined envelope. -/
theorem envelope_le_combine_right
    (A B : FiniteConeApproximation d α q) :
    B.envelope ≤ (A.combine B).envelope := by
  apply d.finiteConeFamilyMax_le_of_isLipschitz
    Finset.univ_nonempty (A.combine B).envelope_isLipschitz
  intro i _hi
  change (B.height i : ℝ≥0∞) ≤ (A.combine B).envelope (B.center i)
  have hcone :
      d.cone α (B.center i) (B.height i) (B.center i) ≤
        (A.combine B).envelope (B.center i) := by
    unfold envelope combine QuasiMetric.finiteConeEnvelope
      QuasiMetric.finiteConeFamilyMax
    simpa using Finset.le_sup'
      (fun z : Sum A.Node B.Node ↦
        d.cone α (Sum.elim A.center B.center z)
          (Sum.elim (fun i ↦ (A.height i : ℝ≥0∞))
            (fun i ↦ (B.height i : ℝ≥0∞)) z) (B.center i))
      (Finset.mem_univ (Sum.inr i))
  simpa [cone_at_center] using hcone

end FiniteConeApproximation

namespace FiniteConeInterpolation

/-- Forget an interpolation problem's samples while retaining its concrete
finite approximation below the target. -/
def toApproximation
    {ι : Type u} [Fintype ι] [Nonempty ι]
    {α : ℝ≥0} {q : X → ℝ≥0∞}
    {sample : ι → X} {threshold : ι → ℝ≥0}
    (R : d.FiniteConeInterpolation α q sample threshold) :
    d.FiniteConeApproximation α q where
  Node := ι
  center := R.center
  height := R.height
  center_isCenter := R.center_isCenter
  height_pos := R.height_pos
  height_lt_target := R.height_lt_target

@[simp]
theorem toApproximation_envelope
    {ι : Type u} [Fintype ι] [Nonempty ι]
    {α : ℝ≥0} {q : X → ℝ≥0∞}
    {sample : ι → X} {threshold : ι → ℝ≥0}
    (R : d.FiniteConeInterpolation α q sample threshold) :
    R.toApproximation.envelope = R.envelope :=
  rfl

end FiniteConeInterpolation

/-- The ambient family of all nonempty finite center-cone approximations
below `q`. -/
def finiteConeApproximationFamily
    {hstandard : d.IsStandard}
    (facts : d.StandardConeFacts hstandard)
    {α : ℝ≥0} (hα : 0 < α)
    (q : d.LInf) : Set d.LSpace :=
  Set.range (fun A : d.FiniteConeApproximation α q ↦
    (A.toLInf facts hα).1)

/-- The finite approximation family is directed, by disjoint union of
labels. -/
theorem finiteConeApproximationFamily_directed
    {hstandard : d.IsStandard}
    (facts : d.StandardConeFacts hstandard)
    {α : ℝ≥0} (hα : 0 < α)
    (q : d.LInf) :
    DirectedOn (· ≤ ·) (d.finiteConeApproximationFamily facts hα q) := by
  intro f hf g hg
  obtain ⟨A, rfl⟩ := hf
  obtain ⟨B, rfl⟩ := hg
  refine ⟨((A.combine B).toLInf facts hα).1, ⟨A.combine B, rfl⟩, ?_, ?_⟩
  · intro x
    exact A.envelope_le_combine_left B x
  · intro x
    exact A.envelope_le_combine_right B x

/-- A nonzero nonnegative function has a strictly positive value. -/
theorem exists_pos_apply_of_ne_zeroLInf
    (q : d.LInf) (hq : q ≠ d.zeroLInf) :
    ∃ x : X, 0 < q x := by
  by_contra h
  push_neg at h
  apply hq
  apply Subtype.ext
  apply WithScott.ofScott.injective
  apply Subtype.ext
  funext x
  exact le_antisymm (h x) (zero_le _)

/-- If the target is nonzero, its finite approximation family is nonempty. -/
theorem finiteConeApproximationFamily_nonempty
    {hstandard : d.IsStandard}
    (facts : d.StandardConeFacts hstandard)
    (hcenters : d.HasEnoughCenterPoints)
    {α : ℝ≥0} (hα : 0 < α)
    (q : d.LInf) (hqLayer : d.InLayer α q.1)
    (hqne : q ≠ d.zeroLInf) :
    (d.finiteConeApproximationFamily facts hα q).Nonempty := by
  obtain ⟨x, hx⟩ := exists_pos_apply_of_ne_zeroLInf q hqne
  let sample : PUnit → X := fun _ ↦ x
  let threshold : PUnit → ℝ≥0 := fun _ ↦ 0
  let R := d.finiteConeInterpolation hα hqLayer.1
    (facts.sharp_of_inLayer α q.1 hqLayer) hcenters
    sample threshold (fun _ ↦ hx)
  let A := R.toApproximation
  exact ⟨(A.toLInf facts hα).1, ⟨A, rfl⟩⟩

/-- Finite cone interpolation proves that the target is the least upper
bound of all its finite center-cone approximations. -/
theorem finiteConeApproximationFamily_isLUB
    {hstandard : d.IsStandard}
    (facts : d.StandardConeFacts hstandard)
    {α : ℝ≥0} (hα : 0 < α)
    (hcenters : d.HasEnoughCenterPoints)
    (q : d.LInf) (hq : d.InLayer α q.1) :
    IsLUB (d.finiteConeApproximationFamily facts hα q) q.1 := by
  constructor
  · intro f hf
    obtain ⟨A, rfl⟩ := hf
    intro x
    exact A.envelope_le_target hq.1 x
  · intro g hg
    intro x
    apply ENNReal.le_of_forall_nnreal_lt
    intro b hb
    let sample : PUnit → X := fun _ ↦ x
    let threshold : PUnit → ℝ≥0 := fun _ ↦ b
    let R := d.finiteConeInterpolation hα hq.1
      (facts.sharp_of_inLayer α q.1 hq)
      hcenters
      sample threshold (fun _ ↦ hb)
    let A := R.toApproximation
    have hAfamily : (A.toLInf facts hα).1 ∈
        d.finiteConeApproximationFamily facts hα q :=
      ⟨A, rfl⟩
    exact (R.exceeds_threshold PUnit.unit).le.trans
      (hg hAfamily x)

/-- A relatively open neighborhood in one integer layer contains a concrete
finite cone approximation of every nonzero target in that layer.  The proof
uses the ambient Scott topology twice (first through `𝓛∞`, then through the
fixed layer) and the directed-supremum theorem above. -/
theorem exists_finiteConeApproximation_mem_layerOpen
    {hstandard : d.IsStandard}
    (facts : d.StandardConeFacts hstandard)
    (hcenters : d.HasEnoughCenterPoints)
    (n : ℕ) {U : Set d.LInf}
    (hU : IsOpen ((↑) ⁻¹' U : Set (d.integerLayer n)))
    (q : d.LInf) (hqU : q ∈ U)
    (hqLayer : q ∈ d.integerLayer n)
    (hqne : q ≠ d.zeroLInf) :
    ∃ A : d.FiniteConeApproximation
        (((n + 1 : ℕ) : ℝ≥0)) q,
      A.toLInf facts (by positivity) ∈ U := by
  let α : ℝ≥0 := ((n + 1 : ℕ) : ℝ≥0)
  have hα : 0 < α := by simp [α]
  obtain ⟨O, hO, hOeq⟩ := isOpen_induced_iff.mp hU
  obtain ⟨V, hV, hVeq⟩ := isOpen_induced_iff.mp hO
  have hqO : q ∈ O := by
    have hqpre : (⟨q, hqLayer⟩ : d.integerLayer n) ∈
        ((↑) ⁻¹' O : Set (d.integerLayer n)) := by
      rw [hOeq]
      exact hqU
    exact hqpre
  have hqV : q.1 ∈ V := by
    have hqpre : q ∈ ((↑) ⁻¹' V : Set d.LInf) := by
      rw [hVeq]
      exact hqO
    exact hqpre
  let S := d.finiteConeApproximationFamily facts hα q
  have hSne : S.Nonempty :=
    d.finiteConeApproximationFamily_nonempty facts hcenters hα q hqLayer hqne
  have hSdir : DirectedOn (· ≤ ·) S :=
    d.finiteConeApproximationFamily_directed facts hα q
  have hSLUB : IsLUB S q.1 :=
    d.finiteConeApproximationFamily_isLUB facts hα hcenters q hqLayer
  have hVinacc :=
    (Topology.IsScott.isOpen_iff_isUpperSet_and_dirSupInaccOn
      (D := Set.univ)).mp hV |>.2
  obtain ⟨g, hgS, hgV⟩ :=
    hVinacc (by trivial) hSne hSdir hSLUB hqV
  obtain ⟨A, rfl⟩ := hgS
  refine ⟨A, ?_⟩
  have hAO : A.toLInf facts hα ∈ O := by
    have hApre : A.toLInf facts hα ∈
        ((↑) ⁻¹' V : Set d.LInf) := hgV
    rw [hVeq] at hApre
    exact hApre
  have hAlayer : A.toLInf facts hα ∈ d.integerLayer n := by
    simpa [integerLayer, α] using A.toLInf_inLayer facts hα
  have hApre : (⟨A.toLInf facts hα, hAlayer⟩ : d.integerLayer n) ∈
      ((↑) ⁻¹' O : Set (d.integerLayer n)) := hAO
  rw [hOeq] at hApre
  simpa [α] using hApre

end QuasiMetric
end LipschitzYonedaFinalTopology
