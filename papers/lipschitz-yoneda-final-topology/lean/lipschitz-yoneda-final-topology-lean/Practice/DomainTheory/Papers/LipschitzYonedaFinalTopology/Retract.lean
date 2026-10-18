import Practice.DomainTheory.Papers.LipschitzYonedaFinalTopology.QuasiMetric

/-!
# Quasi-metric retract transfer

This module instantiates the abstract layer-system retraction from
`LayeredTopology.lean` with the precomposition maps of source lines 668--697.
The Lipschitz, Yoneda-continuity, lower-semicontinuity, layer-preservation,
and retraction calculations are proved here.

The source derives continuity of precomposition on the ambient Scott function
spaces from standardness and pointwise directed suprema.  Since those dcpo
interfaces are not yet present in this project, that exact continuity is a
named field of `FunctionSpaceRetract`; it is not silently assumed as an axiom.
-/

set_option autoImplicit false
set_option linter.unnecessarySimpa false

open Function Set Topology
open scoped NNReal ENNReal Topology

universe u

namespace LipschitzYonedaFinalTopology
namespace QuasiMetric

variable {X Y : Type u} (dX : QuasiMetric X) (dY : QuasiMetric Y)

/-- A map does not increase the extended asymmetric distance. -/
def IsNonexpansive (e : X → Y) : Prop :=
  ∀ x x' : X, dY.edist (e x) (e x') ≤ dX.edist x x'

/-- Yoneda continuity for maps between two quasi-metric spaces, expressed by
preservation of the source's Cauchy nets and their `d`-limits. -/
structure IsYonedaContinuousMap (e : X → Y) : Prop where
  maps_cauchy :
    ∀ (ι : Type u) [Preorder ι] (x : ι → X),
      IsDirectedIndex ι → dX.IsCauchyNet x →
        dY.IsCauchyNet (fun i ↦ e (x i))
  maps_dLimit :
    ∀ (ι : Type u) [Preorder ι] (x : ι → X) (x₀ : X),
      IsDirectedIndex ι → dX.IsCauchyNet x → dX.IsDLimit x x₀ →
        dY.IsDLimit (fun i ↦ e (x i)) (e x₀)

/-- A map regarded as a function between the two induced `d`-Scott spaces. -/
def dScottMap (dX : QuasiMetric X) (dY : QuasiMetric Y) (e : X → Y) :
    dX.DScott → dY.DScott :=
  e

/-- Continuity between the two induced `d`-Scott spaces. -/
def IsDScottContinuous
    (dX : QuasiMetric X) (dY : QuasiMetric Y) (e : X → Y) : Prop :=
  Continuous (dScottMap dX dY e)

/-- Precomposition by a nonexpansive map preserves every Lipschitz constant.
-/
theorem IsLipschitz.comp_nonexpansive
    {e : X → Y} (he : dX.IsNonexpansive dY e)
    {α : ℝ≥0} {f : Y → ℝ≥0∞} (hf : dY.IsLipschitz α f) :
    dX.IsLipschitz α (fun x ↦ f (e x)) := by
  intro x x'
  exact (hf (e x) (e x')).trans
    (by simpa [mul_comm] using
      mul_le_mul_left (he x x') (α : ℝ≥0∞))

/-- Precomposition by a Yoneda-continuous map preserves Yoneda continuity of
extended nonnegative-real-valued functions. -/
theorem IsYonedaContinuous.comp_map
    {e : X → Y} (he : dX.IsYonedaContinuousMap dY e)
    {f : Y → ℝ≥0∞} (hf : dY.IsYonedaContinuous f) :
    dX.IsYonedaContinuous (fun x ↦ f (e x)) where
  maps_cauchy := by
    intro ι _ x hdir hx
    exact hf.maps_cauchy ι (fun i ↦ e (x i)) hdir
      (he.maps_cauchy ι x hdir hx)
  maps_dLimit := by
    intro ι _ x x₀ hdir hx hlim
    exact hf.maps_dLimit ι (fun i ↦ e (x i)) (e x₀) hdir
      (he.maps_cauchy ι x hdir hx)
      (he.maps_dLimit ι x x₀ hdir hx hlim)

/-- Precomposition by a `d`-Scott-continuous map preserves lower
semicontinuity. -/
theorem IsLowerSemicontinuous.comp_dScottContinuous
    {e : X → Y} (he : dX.IsDScottContinuous dY e)
    {f : Y → ℝ≥0∞} (hf : dY.IsLowerSemicontinuous f) :
    dX.IsLowerSemicontinuous (fun x ↦ f (e x)) :=
  hf.comp he

/-- Precomposition on lower-semicontinuous maps. -/
def precomposeLowerMap
    (e : X → Y) (he : dX.IsDScottContinuous dY e)
    (f : dY.LowerMap) : dX.LowerMap :=
  ⟨fun x ↦ f (e x),
    f.2.comp_dScottContinuous dX dY he⟩

@[simp]
theorem precomposeLowerMap_apply
    (e : X → Y) (he : dX.IsDScottContinuous dY e)
    (f : dY.LowerMap) (x : X) :
    dX.precomposeLowerMap dY e he f x = f (e x) :=
  rfl

/-- Precomposition on the Scott spaces of lower-semicontinuous maps. -/
def precomposeLSpace
    (e : X → Y) (he : dX.IsDScottContinuous dY e)
    (f : dY.LSpace) : dX.LSpace :=
  WithScott.toScott
    (dX.precomposeLowerMap dY e he (WithScott.ofScott f))

@[simp]
theorem precomposeLSpace_apply
    (e : X → Y) (he : dX.IsDScottContinuous dY e)
    (f : dY.LSpace) (x : X) :
    dX.precomposeLSpace dY e he f x = f (e x) :=
  rfl

/-- The exact ambient Scott-continuity input for precomposition used in the
source proof of retract transfer. -/
def HasContinuousPrecomposition
    (e : X → Y) (he : dX.IsDScottContinuous dY e) : Prop :=
  Continuous (dX.precomposeLSpace dY e he)

/-- Precomposition preserves membership in a fixed Lipschitz/Yoneda layer. -/
theorem precomposeLSpace_inLayer
    {e : X → Y} (hnonexp : dX.IsNonexpansive dY e)
    (hyoneda : dX.IsYonedaContinuousMap dY e)
    (hdScott : dX.IsDScottContinuous dY e)
    {α : ℝ≥0} {f : dY.LSpace} (hf : dY.InLayer α f) :
    dX.InLayer α (dX.precomposeLSpace dY e hdScott f) := by
  constructor
  · change dX.IsLipschitz α (fun x ↦ f (e x))
    exact hf.1.comp_nonexpansive dX dY hnonexp
  · change dX.IsYonedaContinuous (fun x ↦ f (e x))
    exact hf.2.comp_map dX dY hyoneda

/-- Precomposition restricted to the union of all positive finite layers. -/
def precomposeLInf
    (e : X → Y) (hnonexp : dX.IsNonexpansive dY e)
    (hyoneda : dX.IsYonedaContinuousMap dY e)
    (hdScott : dX.IsDScottContinuous dY e)
    (f : dY.LInf) : dX.LInf :=
  ⟨dX.precomposeLSpace dY e hdScott f.1, by
    obtain ⟨α, hα, hf⟩ := f.2
    exact ⟨α, hα,
      dX.precomposeLSpace_inLayer dY hnonexp hyoneda hdScott hf⟩⟩

@[simp]
theorem precomposeLInf_apply
    (e : X → Y) (hnonexp : dX.IsNonexpansive dY e)
    (hyoneda : dX.IsYonedaContinuousMap dY e)
    (hdScott : dX.IsDScottContinuous dY e)
    (f : dY.LInf) (x : X) :
    dX.precomposeLInf dY e hnonexp hyoneda hdScott f x = f (e x) :=
  rfl

/-- The restricted precomposition map preserves every integer layer. -/
theorem precomposeLInf_maps_integerLayer
    {e : X → Y} (hnonexp : dX.IsNonexpansive dY e)
    (hyoneda : dX.IsYonedaContinuousMap dY e)
    (hdScott : dX.IsDScottContinuous dY e) (n : ℕ) :
    MapsTo (dX.precomposeLInf dY e hnonexp hyoneda hdScott)
      (dY.integerLayer n) (dX.integerLayer n) := by
  intro f hf
  exact dX.precomposeLSpace_inLayer dY hnonexp hyoneda hdScott hf

/-- Ambient continuity of precomposition restricts to continuity on
`ℒ∞`. -/
theorem continuous_precomposeLInf
    {e : X → Y} (hnonexp : dX.IsNonexpansive dY e)
    (hyoneda : dX.IsYonedaContinuousMap dY e)
    (hdScott : dX.IsDScottContinuous dY e)
    (hcontinuous : dX.HasContinuousPrecomposition dY e hdScott) :
    Continuous (dX.precomposeLInf dY e hnonexp hyoneda hdScott) := by
  exact (hcontinuous.comp continuous_subtype_val).subtype_mk _

/-- Source-facing quasi-metric retract data, including the one still-explicit
ambient precomposition-continuity premise in each direction. -/
structure FunctionSpaceRetract where
  embedding : X → Y
  projection : Y → X
  embedding_nonexpansive : dX.IsNonexpansive dY embedding
  projection_nonexpansive : dY.IsNonexpansive dX projection
  embedding_yoneda : dX.IsYonedaContinuousMap dY embedding
  projection_yoneda : dY.IsYonedaContinuousMap dX projection
  embedding_dScott : dX.IsDScottContinuous dY embedding
  projection_dScott : dY.IsDScottContinuous dX projection
  leftInverse : Function.LeftInverse projection embedding
  continuous_precompose_embedding :
    dX.HasContinuousPrecomposition dY embedding embedding_dScott
  continuous_precompose_projection :
    dY.HasContinuousPrecomposition dX projection projection_dScott

namespace FunctionSpaceRetract

/-- The induced retraction between the two increasing layer systems. -/
def toLayerRetraction (R : dX.FunctionSpaceRetract dY) :
    dX.layerSystem.Retraction dY.layerSystem where
  embedding :=
    dY.precomposeLInf dX R.projection R.projection_nonexpansive
      R.projection_yoneda R.projection_dScott
  projection :=
    dX.precomposeLInf dY R.embedding R.embedding_nonexpansive
      R.embedding_yoneda R.embedding_dScott
  continuous_embedding :=
    dY.continuous_precomposeLInf dX R.projection_nonexpansive
      R.projection_yoneda R.projection_dScott
      R.continuous_precompose_projection
  continuous_projection :=
    dX.continuous_precomposeLInf dY R.embedding_nonexpansive
      R.embedding_yoneda R.embedding_dScott
      R.continuous_precompose_embedding
  leftInverse := by
    intro f
    apply Subtype.ext
    apply WithScott.ofScott.injective
    apply Subtype.ext
    funext x
    exact congrArg (fun z ↦ f z) (R.leftInverse x)
  embedding_maps_layer :=
    dY.precomposeLInf_maps_integerLayer dX R.projection_nonexpansive
      R.projection_yoneda R.projection_dScott
  projection_maps_layer :=
    dX.precomposeLInf_maps_integerLayer dY R.embedding_nonexpansive
      R.embedding_yoneda R.embedding_dScott

/-- Lemma `lem:retract`, with the ambient precomposition-continuity step kept
as explicit data in `FunctionSpaceRetract`. -/
theorem propertyD
    (R : dX.FunctionSpaceRetract dY)
    (hY : dY.layerSystem.PropertyD) :
    dX.layerSystem.PropertyD :=
  dX.layerSystem.propertyD_of_retraction dY.layerSystem
    R.toLayerRetraction hY

end FunctionSpaceRetract

end QuasiMetric
end LipschitzYonedaFinalTopology
