import Mathlib.Data.Finset.Order
import Mathlib.Topology.Compactness.Compact
import Practice.DomainTheory.Papers.LipschitzYonedaFinalTopology.Retract

/-!
# Directed suprema of lower-semicontinuous maps

The ambient function dcpo in the manuscript consists of maps from a
`d`-Scott space to `ℝ≥0∞`, ordered pointwise.  This file proves directly
that arbitrary pointwise suprema remain lower semicontinuous and then uses
that concrete supremum to show that precomposition preserves directed
suprema.  No dcpo or continuity property is assumed as an interface.
-/

set_option autoImplicit false
set_option linter.unnecessarySimpa false

open Function Set Topology
open scoped NNReal ENNReal Topology

noncomputable section

universe u

namespace LipschitzYonedaFinalTopology
namespace QuasiMetric

variable {X Y : Type u} (dX : QuasiMetric X) (dY : QuasiMetric Y)

/-- An arbitrary pointwise supremum of lower-semicontinuous maps is lower
semicontinuous for the Scott topology on `ℝ≥0∞`. -/
theorem isLowerSemicontinuous_iSup
    {ι : Type u} (f : ι → X → ℝ≥0∞)
    (hf : ∀ i, dX.IsLowerSemicontinuous (f i)) :
    dX.IsLowerSemicontinuous (fun x ↦ ⨆ i, f i x) := by
  letI : CompleteLinearOrder (WithScott ℝ≥0∞) :=
    inferInstanceAs (CompleteLinearOrder ℝ≥0∞)
  unfold IsLowerSemicontinuous
  rw [continuous_def]
  intro U hU
  rcases (Topology.IsScott.isOpen_iff_Iic_compl_or_univ U).mp hU with
    rfl | ⟨a, rfl⟩
  · simp
  · have hpreimage :
        (fun x : dX.DScott ↦
            WithScott.toScott (⨆ i, f i x)) ⁻¹' (Set.Iic a)ᶜ =
          ⋃ i, (fun x : dX.DScott ↦ WithScott.toScott (f i x)) ⁻¹'
            (Set.Iic a)ᶜ := by
      ext x
      simp only [mem_preimage, mem_compl_iff, mem_Iic, mem_iUnion]
      simpa only [not_le] using
        (lt_iSup_iff :
          WithScott.ofScott a < (⨆ i, f i x) ↔
            ∃ i, WithScott.ofScott a < f i x)
    rw [hpreimage]
    exact isOpen_iUnion fun i ↦
      isClosed_Iic.isOpen_compl.preimage (hf i)

namespace LowerMap

/-- The pointwise supremum of a family of lower-semicontinuous maps. -/
def pointwiseSup (S : Set dX.LowerMap) : dX.LowerMap :=
  ⟨fun x ↦ ⨆ f : S, (f.1 : dX.LowerMap) x,
    dX.isLowerSemicontinuous_iSup
      (fun f : S ↦ (f.1 : dX.LowerMap))
      (fun f ↦ f.1.2)⟩

@[simp]
theorem pointwiseSup_apply (S : Set dX.LowerMap) (x : X) :
    LowerMap.pointwiseSup dX S x = ⨆ f : S, (f.1 : dX.LowerMap) x :=
  rfl

/-- The concrete pointwise supremum is a least upper bound in the ambient
poset of lower-semicontinuous maps. -/
theorem pointwiseSup_isLUB (S : Set dX.LowerMap) :
    IsLUB S (LowerMap.pointwiseSup dX S) := by
  constructor
  · intro f hf x
    exact le_iSup_of_le ⟨f, hf⟩ le_rfl
  · intro g hg x
    apply iSup_le
    intro f
    exact hg f.2 x

/-- Every family of lower-semicontinuous maps has a pointwise least upper
bound.  The manuscript only needs the directed case. -/
theorem exists_isLUB (S : Set dX.LowerMap) :
    ∃ f : dX.LowerMap, IsLUB S f :=
  ⟨LowerMap.pointwiseSup dX S, LowerMap.pointwiseSup_isLUB dX S⟩

end LowerMap

namespace LSpace

/-- The pointwise supremum of a family in the Scott space of lower maps. -/
def pointwiseSup (S : Set dX.LSpace) : dX.LSpace :=
  WithScott.toScott
    ⟨fun x ↦ ⨆ f : S, (f.1 : dX.LSpace) x,
      dX.isLowerSemicontinuous_iSup
        (fun f : S ↦ (f.1 : dX.LSpace))
        (fun f ↦ (WithScott.ofScott f.1).2)⟩

@[simp]
theorem pointwiseSup_apply (S : Set dX.LSpace) (x : X) :
    LSpace.pointwiseSup dX S x = ⨆ f : S, (f.1 : dX.LSpace) x :=
  rfl

/-- The concrete pointwise supremum is the least upper bound of the
original family in `LSpace`. -/
theorem pointwiseSup_isLUB (S : Set dX.LSpace) :
    IsLUB S (LSpace.pointwiseSup dX S) := by
  constructor
  · intro f hf x
    exact le_iSup_of_le ⟨f, hf⟩ le_rfl
  · intro g hg x
    apply iSup_le
    intro f
    exact hg f.2 x

end LSpace

/-- The compact-open subbasic condition used at source equation `eq:N`.
The compact set lives in the induced `d`-Scott space. -/
def compactStrictSuperlevel
    (K : Set dX.DScott) (b : ℝ≥0∞) : Set dX.LSpace :=
  {f | ∀ x ∈ K, b < f x}

/-- A compact strict-superlevel condition is Scott-open in the ambient
space of lower-semicontinuous maps.  The proof uses compactness to reduce
the pointwise witnesses from a directed family to finitely many, then
directedness supplies one common upper bound. -/
theorem isOpen_compactStrictSuperlevel
    (K : Set dX.DScott) (hK : IsCompact K) (b : ℝ≥0∞) :
    IsOpen (dX.compactStrictSuperlevel K b) := by
  rw [Topology.IsScott.isOpen_iff_isUpperSet_and_dirSupInaccOn
    (D := Set.univ)]
  constructor
  · intro f g hfg hf x hx
    exact (hf x hx).trans_le (hfg x)
  · intro S _hSuniv hSnonempty hSdirected a ha haK
    have haPointwise : a = LSpace.pointwiseSup dX S := by
      apply WithScott.ofScott.injective
      apply @le_antisymm dX.LowerMap _
      · intro x
        exact ha.2 (LSpace.pointwiseSup_isLUB dX S).1 x
      · intro x
        exact (LSpace.pointwiseSup_isLUB dX S).2 ha.1 x
    let U : S → Set dX.DScott := fun f ↦
      {x | b < (f.1 : dX.LSpace) x}
    have hUopen (f : S) : IsOpen (U f) := by
      letI : CompleteLinearOrder (WithScott ℝ≥0∞) :=
        inferInstanceAs (CompleteLinearOrder ℝ≥0∞)
      have hopen :
          IsOpen (Set.Ioi (WithScott.toScott b) : Set (WithScott ℝ≥0∞)) :=
        isOpen_Ioi
      simpa [U, Set.preimage] using
        hopen.preimage (WithScott.ofScott f.1).2
    have hcover : K ⊆ ⋃ f, U f := by
      intro x hx
      have hlt : b < ⨆ f : S, (f.1 : dX.LSpace) x := by
        simpa [haPointwise] using haK x hx
      obtain ⟨f, hf⟩ := (lt_iSup_iff).mp hlt
      exact Set.mem_iUnion.mpr ⟨f, hf⟩
    obtain ⟨t, ht⟩ := hK.elim_finite_subcover U hUopen hcover
    letI : Nonempty S := hSnonempty.to_subtype
    have hdirected : Directed (· ≤ ·) (fun f : S ↦ (f.1 : dX.LSpace)) := by
      intro f g
      obtain ⟨h, hhS, hfh, hgh⟩ :=
        hSdirected f.1 f.2 g.1 g.2
      exact ⟨⟨h, hhS⟩, hfh, hgh⟩
    obtain ⟨g, hg⟩ := hdirected.finset_le t
    refine ⟨g.1, g.2, ?_⟩
    intro x hx
    obtain ⟨f, hft, hxf⟩ := Set.mem_iUnion₂.mp (ht hx)
    exact hxf.trans_le (hg f hft x)

/-- Precomposition on lower maps preserves every existing directed
supremum, hence is Scott-continuous. -/
theorem precomposeLowerMap_scottContinuous
    (e : X → Y) (he : dX.IsDScottContinuous dY e) :
    ScottContinuous (dX.precomposeLowerMap dY e he) := by
  intro S _hSnonempty _hSdirected a ha
  have haPointwise : a = LowerMap.pointwiseSup dY S :=
    ha.unique (LowerMap.pointwiseSup_isLUB dY S)
  constructor
  · rintro _ ⟨f, hf, rfl⟩ x
    exact ha.1 hf (e x)
  · intro g hg x
    rw [haPointwise]
    change (⨆ f : S, (f.1 : dY.LowerMap) (e x)) ≤ g x
    apply iSup_le
    intro f
    exact hg ⟨f.1, f.2, rfl⟩ x

/-- The Scott-continuity calculation above is exactly topological continuity
between the corresponding `WithScott` spaces. -/
theorem continuous_precomposeLSpace
    (e : X → Y) (he : dX.IsDScottContinuous dY e) :
    Continuous (dX.precomposeLSpace dY e he) := by
  rw [← Topology.IsScott.scottContinuousOn_iff_continuous
    (D := Set.univ) (fun _ _ _ ↦ Set.mem_univ _)]
  exact (dX.precomposeLowerMap_scottContinuous dY e he).scottContinuousOn

/-- The source retraction data after removing the two now-proved ambient
precomposition-continuity fields. -/
structure YonedaDScottRetract where
  embedding : X → Y
  projection : Y → X
  embedding_nonexpansive : dX.IsNonexpansive dY embedding
  projection_nonexpansive : dY.IsNonexpansive dX projection
  embedding_yoneda : dX.IsYonedaContinuousMap dY embedding
  projection_yoneda : dY.IsYonedaContinuousMap dX projection
  embedding_dScott : dX.IsDScottContinuous dY embedding
  projection_dScott : dY.IsDScottContinuous dX projection
  leftInverse : Function.LeftInverse projection embedding

namespace YonedaDScottRetract

/-- Directed pointwise suprema discharge both ambient continuity obligations
in the older `FunctionSpaceRetract` interface. -/
def toFunctionSpaceRetract
    (R : dX.YonedaDScottRetract dY) : dX.FunctionSpaceRetract dY where
  embedding := R.embedding
  projection := R.projection
  embedding_nonexpansive := R.embedding_nonexpansive
  projection_nonexpansive := R.projection_nonexpansive
  embedding_yoneda := R.embedding_yoneda
  projection_yoneda := R.projection_yoneda
  embedding_dScott := R.embedding_dScott
  projection_dScott := R.projection_dScott
  leftInverse := R.leftInverse
  continuous_precompose_embedding :=
    dX.continuous_precomposeLSpace dY R.embedding R.embedding_dScott
  continuous_precompose_projection :=
    dY.continuous_precomposeLSpace dX R.projection R.projection_dScott

/-- Source lemma `lem:retract` with no ambient continuity premise. -/
theorem propertyD
    (R : dX.YonedaDScottRetract dY)
    (hY : dY.PropertyD) : dX.PropertyD :=
  FunctionSpaceRetract.propertyD dX dY R.toFunctionSpaceRetract hY

end YonedaDScottRetract

end QuasiMetric
end LipschitzYonedaFinalTopology
