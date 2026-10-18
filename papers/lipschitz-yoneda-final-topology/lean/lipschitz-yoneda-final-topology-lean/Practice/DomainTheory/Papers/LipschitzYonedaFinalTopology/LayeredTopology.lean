import Mathlib.Topology.Coherent
import Mathlib.Topology.Constructions
import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.Order

/-!
# Final topologies of increasing layers

This module formalizes the purely topological part of
`lipschitz_yoneda_final_topology_paper_fifth_audit.tex`:

* property `D` for a countable increasing union of subspaces;
* the coproduct quotient-map characterization;
* the universal continuity, Sierpiński, and closed-set characterizations;
* descent of property `D` along a layer-preserving retraction.

The index `n : ℕ` represents the manuscript's positive integer layer
`n + 1`.
-/

set_option autoImplicit false
set_option linter.unnecessarySimpa false

open Set Function
open Topology

universe u v

namespace LipschitzYonedaFinalTopology

/-- An increasing countable cover of a topological space by subspaces. -/
structure LayerSystem (X : Type u) [TopologicalSpace X] where
  /-- The `n`-th layer; index `n` represents the source layer `n + 1`. -/
  layer : ℕ → Set X
  /-- Every point occurs in an integer layer. -/
  cover : ∀ x : X, ∃ n : ℕ, x ∈ layer n
  /-- The layers are increasing. -/
  monotone_layer : Monotone layer

namespace LayerSystem

variable {X : Type u} [TopologicalSpace X] (L : LayerSystem X)

/-- The family of subsets underlying a layer system. -/
def family : Set (Set X) := Set.range L.layer

/-- Property `D`: a set open on every layer is open globally.

This is exactly mathlib's `Topology.IsCoherentWith` predicate specialized to
the family of integer layers. -/
def PropertyD : Prop := Topology.IsCoherentWith L.family

/-- The topological coproduct of all layers. -/
abbrev LayerSum := Σ n : ℕ, L.layer n

/-- The natural map from the coproduct of the layers to the union. -/
def collapse : L.LayerSum → X := fun p ↦ p.2.1

@[simp]
theorem collapse_mk (n : ℕ) (x : L.layer n) :
    L.collapse ⟨n, x⟩ = x := rfl

theorem collapse_continuous : Continuous L.collapse := by
  apply continuous_sigma
  intro n
  exact continuous_subtype_val

theorem collapse_surjective : Function.Surjective L.collapse := by
  intro x
  obtain ⟨n, hx⟩ := L.cover x
  exact ⟨⟨n, ⟨x, hx⟩⟩, rfl⟩

/-- The source definition of property `D`, unfolded to the integer layers. -/
theorem propertyD_iff_layerwise_open :
    L.PropertyD ↔
      ∀ U : Set X,
        (∀ n : ℕ, IsOpen ((↑) ⁻¹' U : Set (L.layer n))) → IsOpen U := by
  constructor
  · intro h U hU
    apply h.isOpen_iff.2
    intro s hs
    obtain ⟨n, rfl⟩ := hs
    exact hU n
  · intro h
    refine ⟨?_⟩
    intro U hU
    apply h U
    intro n
    exact hU (L.layer n) ⟨n, rfl⟩

/-- If one layer is already the entire space, property `D` is tautological. -/
theorem propertyD_of_layer_eq_univ (n : ℕ) (hn : L.layer n = Set.univ) :
    L.PropertyD := by
  apply L.propertyD_iff_layerwise_open.mpr
  intro U hU
  have hpre := hU n
  rw [hn] at hpre
  have himage :
      IsOpen (((↑) : ↑(Set.univ : Set X) → X) ''
        ((↑) ⁻¹' U : Set ↑(Set.univ : Set X))) :=
    isOpen_univ.isOpenMap_subtype_val _ hpre
  simpa using himage

/-- Proposition `prop:formal-iff`, clauses (i) and (ii): property `D` is
equivalent to the natural coproduct map being a quotient map. -/
theorem propertyD_iff_isQuotientMap :
    L.PropertyD ↔ Topology.IsQuotientMap L.collapse := by
  constructor
  · intro hD
    refine ⟨Topology.IsCoinducing.of_isOpen_preimage_iff_isOpen ?_,
      L.collapse_surjective⟩
    intro U
    constructor
    · intro hpre
      apply (L.propertyD_iff_layerwise_open.mp hD) U
      intro n
      have hn := isOpen_sigma_iff.mp hpre n
      simpa [LayerSystem.collapse] using hn
    · intro hU
      exact hU.preimage L.collapse_continuous
  · intro hq
    apply L.propertyD_iff_layerwise_open.mpr
    intro U hU
    apply hq.isCoinducing.isOpen_preimage.mp
    rw [isOpen_sigma_iff]
    intro n
    simpa [LayerSystem.collapse] using hU n

/-- Proposition `prop:formal-iff`, clause (iii): the universal continuity
criterion for maps out of the union of the layers. -/
theorem propertyD_iff_universal_continuity :
    L.PropertyD ↔
      ∀ (Z : Type v) [TopologicalSpace Z] (F : X → Z),
        Continuous F ↔
          ∀ n : ℕ, Continuous (fun x : L.layer n ↦ F x) := by
  constructor
  · intro hD Z _ F
    have hq : Topology.IsQuotientMap L.collapse :=
      L.propertyD_iff_isQuotientMap.mp hD
    rw [hq.continuous_iff, continuous_sigma_iff]
    rfl
  · intro h
    apply L.propertyD_iff_layerwise_open.mpr
    intro U hU
    let F : X → ULift.{v} Prop := fun x ↦ ULift.up (x ∈ U)
    have hF : Continuous F := by
      apply (h (ULift.{v} Prop) F).2
      intro n
      exact continuous_uliftUp.comp (continuous_Prop.mpr (by
        simpa only [Set.setOf_mem_eq] using hU n))
    have hmem : Continuous (fun x : X ↦ x ∈ U) :=
      continuous_uliftDown.comp hF
    exact continuous_Prop.mp hmem

/-- Proposition `prop:formal-iff`, clause (iv): it is enough to test the
universal criterion against the Sierpiński space `Prop`. -/
theorem propertyD_iff_sierpinski :
    L.PropertyD ↔
      ∀ F : X → Prop,
        (∀ n : ℕ, Continuous (fun x : L.layer n ↦ F x)) →
          Continuous F := by
  constructor
  · intro hD F hF
    rw [continuous_Prop]
    apply (L.propertyD_iff_layerwise_open.mp hD)
    intro n
    simpa only [Set.setOf_mem_eq] using continuous_Prop.mp (hF n)
  · intro h
    apply L.propertyD_iff_layerwise_open.mpr
    intro U hU
    have hmem : Continuous (fun x : X ↦ x ∈ U) := by
      apply h
      intro n
      rw [continuous_Prop]
      simpa only [Set.setOf_mem_eq] using hU n
    exact continuous_Prop.mp hmem

/-- Proposition `prop:formal-iff`, clause (v): the closed-set criterion. -/
theorem propertyD_iff_layerwise_closed :
    L.PropertyD ↔
      ∀ C : Set X,
        IsClosed C ↔
          ∀ n : ℕ, IsClosed ((↑) ⁻¹' C : Set (L.layer n)) := by
  constructor
  · intro hD C
    constructor
    · intro hC n
      exact hC.preimage continuous_subtype_val
    · intro hC
      apply hD.isClosed_iff.2
      intro s hs
      obtain ⟨n, rfl⟩ := hs
      exact hC n
  · intro h
    apply Topology.IsCoherentWith.of_isClosed
    intro C hC
    apply (h C).2
    intro n
    exact hC (L.layer n) ⟨n, rfl⟩

/-- Data for a retraction that preserves every layer in both directions. -/
structure Retraction
    {Y : Type v} [TopologicalSpace Y]
    (M : LayerSystem Y) where
  embedding : X → Y
  projection : Y → X
  continuous_embedding : Continuous embedding
  continuous_projection : Continuous projection
  leftInverse : Function.LeftInverse projection embedding
  embedding_maps_layer : ∀ n, MapsTo embedding (L.layer n) (M.layer n)
  projection_maps_layer : ∀ n, MapsTo projection (M.layer n) (L.layer n)

/-- Lemma `lem:abstract-retract`: property `D` descends along a continuous,
layer-preserving retraction. -/
theorem propertyD_of_retraction
    {Y : Type v} [TopologicalSpace Y]
    (M : LayerSystem Y) (R : L.Retraction M)
    (hM : M.PropertyD) :
    L.PropertyD := by
  apply L.propertyD_iff_layerwise_open.mpr
  intro U hU
  have hopen_projection_preimage : IsOpen (R.projection ⁻¹' U) := by
    apply (M.propertyD_iff_layerwise_open.mp hM)
    intro n
    let rn : M.layer n → L.layer n := fun y ↦
      ⟨R.projection y, R.projection_maps_layer n y.2⟩
    have hrn : Continuous rn :=
      (R.continuous_projection.comp continuous_subtype_val).subtype_mk _
    have hopen := (hU n).preimage hrn
    simpa [rn, Set.preimage] using hopen
  have hopen_twice := hopen_projection_preimage.preimage R.continuous_embedding
  convert hopen_twice using 1
  ext x
  simp [R.leftInverse x]

end LayerSystem

end LipschitzYonedaFinalTopology
