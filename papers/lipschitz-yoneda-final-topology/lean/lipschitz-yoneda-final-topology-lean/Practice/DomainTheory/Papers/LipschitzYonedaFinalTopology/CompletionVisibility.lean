import Practice.DomainTheory.Papers.LipschitzYonedaFinalTopology.QuasiMetric

/-!
# Abstract completion-visibility theorem

This file isolates the topological engine of `thm:completion-visibility`.
The source-specific extension formula is separate mathematical input: once an
extension map is continuous on each layer, has a continuous layer-preserving
left inverse, and the completion-side union has property `D`, global
continuity of extension is equivalent to property `D` on the original union.
-/

set_option autoImplicit false
set_option linter.unnecessarySimpa false

open Set Function
open scoped NNReal ENNReal

universe u v

namespace LipschitzYonedaFinalTopology

namespace CompletionFormula

variable {I : Type u} {A : Type v}

/-- The pointwise supremum occurring in the completion-extension formula.

The intended coordinates are `value i f - penalty i`, where `i` ranges over
the formal balls in a rounded ideal. -/
noncomputable def correctedSupremum
    (value : I → A → ℝ≥0∞) (penalty : I → ℝ≥0) (f : A) : ℝ≥0∞ :=
  ⨆ i, value i f - (penalty i : ℝ≥0∞)

/-- A strict inequality against a finite correction can be moved across
truncated subtraction in `ℝ≥0∞`.  Finiteness of the correction is essential:
it is supplied here by taking penalties in `ℝ≥0`. -/
theorem lt_correctedCoordinate_iff
    (value : I → A → ℝ≥0∞) (penalty : I → ℝ≥0)
    (i : I) (f : A) (a : ℝ≥0∞) :
    a < value i f - (penalty i : ℝ≥0∞) ↔
      a + (penalty i : ℝ≥0∞) < value i f := by
  exact (ENNReal.cancel_of_ne (by simp)).lt_tsub_iff_right

/-- The strict superlevel set of the completion formula is the union of the
strict superlevel sets of its corrected coordinates.  This is the exact
set-theoretic calculation used in the proof of layerwise continuity. -/
theorem strictSuperlevel_correctedSupremum
    (value : I → A → ℝ≥0∞) (penalty : I → ℝ≥0) (a : ℝ≥0∞) :
    {f | a < correctedSupremum value penalty f} =
      ⋃ i, {f | a + (penalty i : ℝ≥0∞) < value i f} := by
  ext f
  simp only [correctedSupremum, mem_setOf_eq, mem_iUnion, lt_iSup_iff]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i, (lt_correctedCoordinate_iff value penalty i f a).mp hi⟩
  · rintro ⟨i, hi⟩
    exact ⟨i, (lt_correctedCoordinate_iff value penalty i f a).mpr hi⟩

/-- Point-evaluation strict superlevels being open implies that every strict
superlevel of the corrected supremum is open.  Applying this with
`value (x,r) f = f x` and `penalty (x,r) = α r` supplies the topological
calculation in `lem:Ext-layerwise`, once the source-specific extension
formula has been constructed. -/
theorem isOpen_strictSuperlevel_correctedSupremum
    [TopologicalSpace A]
    (value : I → A → ℝ≥0∞) (penalty : I → ℝ≥0)
    (hvalue : ∀ i b, IsOpen {f | b < value i f}) (a : ℝ≥0∞) :
    IsOpen {f | a < correctedSupremum value penalty f} := by
  rw [strictSuperlevel_correctedSupremum value penalty a]
  exact isOpen_iUnion fun i ↦ hvalue i _

end CompletionFormula

namespace LayerSystem

variable {X : Type u} {Y : Type v}
  [TopologicalSpace X] [TopologicalSpace Y]
  (L : LayerSystem X) (M : LayerSystem Y)

/-- The exact topological data supplied in the manuscript by simultaneous
extension to the formal-ball completion and recovery along the way-below
section. -/
structure LayerwiseExtension where
  extension : X → Y
  recovery : Y → X
  continuous_recovery : Continuous recovery
  recovery_extension : Function.LeftInverse recovery extension
  extension_maps_layer : ∀ n, MapsTo extension (L.layer n) (M.layer n)
  recovery_maps_layer : ∀ n, MapsTo recovery (M.layer n) (L.layer n)
  continuous_extension_on_layer :
    ∀ n, Continuous (fun x : L.layer n ↦
      (⟨extension x, extension_maps_layer n x.2⟩ : M.layer n))

/-- The abstract content of `thm:completion-visibility`: if the target union
has property `D`, then the source union has property `D` exactly when the
simultaneous extension map is continuous. -/
theorem propertyD_iff_continuous_extension
    (E : L.LayerwiseExtension M) (hM : M.PropertyD) :
    L.PropertyD ↔ Continuous E.extension := by
  constructor
  · intro hL
    apply (L.propertyD_iff_universal_continuity.mp hL Y E.extension).2
    intro n
    have hsub := continuous_subtype_val.comp
      (E.continuous_extension_on_layer n)
    simpa [Function.comp_def] using hsub
  · intro hExt
    let R : L.Retraction M :=
      { embedding := E.extension
        projection := E.recovery
        continuous_embedding := hExt
        continuous_projection := E.continuous_recovery
        leftInverse := E.recovery_extension
        embedding_maps_layer := E.extension_maps_layer
        projection_maps_layer := E.recovery_maps_layer }
    exact L.propertyD_of_retraction M R hM

end LayerSystem
end LipschitzYonedaFinalTopology
