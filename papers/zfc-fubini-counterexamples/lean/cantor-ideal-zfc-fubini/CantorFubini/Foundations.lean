/- Adapted from ZFC_Fubini_Lean/ZFCFubini/Foundations.lean; original SHA256 9faed1d8e3885692d4a467735f086856c71167fb57c2644ff1f1b27a825a707b. Current source is formalized-manuscript.tex. -/
import Mathlib.Topology.Order.ScottTopology
import Mathlib.Topology.Sets.Opens
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic

/-!
Order and continuous valuation infrastructure, adapted from
CH_Fubini_Counterexample_Lean/CHFubini/Foundations.lean, SHA256
69e84fe08aa95a236840580435bb251f6aee1c37d5959d70e36dc6b33f4d3536.
No CH construction or theorem is imported. Source-facing bounded-real integrals
and proved unit-interval bridges are in PaperIntegral and Corollaries.
-/

set_option autoImplicit false
open Set Topology TopologicalSpace MeasureTheory
open scoped ENNReal
universe u v w

namespace CantorFubini

instance scottPartialOrder (P : Type u) [PartialOrder P] : PartialOrder (WithScott P) :=
  inferInstanceAs (PartialOrder P)

instance scottCompleteLattice (P : Type u) [CompleteLattice P] :
    CompleteLattice (WithScott P) := inferInstanceAs (CompleteLattice P)

/-- All directed sets in the manuscript are nonempty; no bottom is required. -/
def IsDcpo (P : Type u) [PartialOrder P] : Prop :=
  ∀ A : Set P, A.Nonempty → DirectedOn (· ≤ ·) A → ∃ p, IsLUB A p

theorem completeLattice_isDcpo (P : Type u) [CompleteLattice P] : IsDcpo P :=
  fun A _ _ => ⟨sSup A, isLUB_sSup A⟩

/-- Strict, modular and Scott-continuous mass on the complete lattice of opens.
Monotonicity follows from Scott continuity and is exposed below. -/
structure Valuation (X : Type u) [TopologicalSpace X] where
  mass : Opens X → ℝ≥0∞
  strict : mass ⊥ = 0
  modular : ∀ U V, mass U + mass V = mass (U ⊔ V) + mass (U ⊓ V)
  continuous : ScottContinuous mass

namespace Valuation
variable {X : Type u} [TopologicalSpace X]

instance : CoeFun (Valuation X) (fun _ => Opens X → ℝ≥0∞) := ⟨Valuation.mass⟩

@[ext] theorem ext {μ ν : Valuation X} (h : ∀ U, μ U = ν U) : μ = ν := by
  cases μ; cases ν; congr; exact funext h

theorem mono (μ : Valuation X) : Monotone μ.mass := μ.continuous.monotone

def Subprobability (μ : Valuation X) : Prop := μ ⊤ ≤ 1
def Probability (μ : Valuation X) : Prop := μ ⊤ = 1

theorem Probability.subprobability {μ : Valuation X} (hμ : μ.Probability) :
    μ.Subprobability := hμ.le

theorem Subprobability.mass_le_one {μ : Valuation X} (hμ : μ.Subprobability)
    (U : Opens X) : μ U ≤ 1 := (μ.mono le_top).trans hμ

theorem map_sSup (μ : Valuation X) {A : Set (Opens X)}
    (hn : A.Nonempty) (hd : DirectedOn (· ≤ ·) A) :
    μ (sSup A) = ⨆ U ∈ A, μ U := by
  have h := μ.continuous hn hd (isLUB_sSup A)
  exact h.unique <| by
    convert isLUB_sSup (μ.mass '' A) using 1
    exact sSup_image.symm

theorem map_iSup (μ : Valuation X) {ι : Type v} [Nonempty ι]
    (U : ι → Opens X) (hd : Directed (· ≤ ·) U) :
    μ (⨆ i, U i) = ⨆ i, μ (U i) := by
  simpa only [sSup_range, iSup_range] using
    μ.map_sSup (Set.range_nonempty U) hd.directedOn_range

/-- The manuscript's pushforward, on the actual specified continuous map. -/
def push {Y : Type v} [TopologicalSpace Y] (μ : Valuation X)
    (f : X → Y) (hf : Continuous f) : Valuation Y where
  mass U := μ (Opens.comap ⟨f, hf⟩ U)
  strict := μ.strict
  modular U V := μ.modular _ _
  continuous := by
    intro A hn hd p hp
    have he : IsLUB ((Opens.comap ⟨f, hf⟩) '' A)
        (Opens.comap ⟨f, hf⟩ p) := by
      have ep : p = sSup A := hp.unique (isLUB_sSup A)
      subst p
      simpa using isLUB_sSup ((Opens.comap ⟨f, hf⟩) '' A)
    simpa [Set.image_image, Function.comp_def] using
      μ.continuous (hn.image _)
        ((directedOn_image.mpr (hd.mono (fun _ _ h _ hx => h hx)))) he

@[simp] theorem push_apply {Y : Type v} [TopologicalSpace Y]
    (μ : Valuation X) (f : X → Y) (hf : Continuous f) (U : Opens Y) :
    μ.push f hf U = μ (Opens.comap ⟨f, hf⟩ U) := rfl

@[simp] theorem push_univ {Y : Type v} [TopologicalSpace Y]
    (μ : Valuation X) (f : X → Y) (hf : Continuous f) : μ.push f hf ⊤ = μ ⊤ := rfl

theorem Probability.push {Y : Type v} [TopologicalSpace Y]
    {μ : Valuation X} (hμ : μ.Probability) (f : X → Y) (hf : Continuous f) :
    (μ.push f hf).Probability := hμ

end Valuation

/-- Source `Val(X)` has values in [0,1], rather than arbitrary mass. -/
abbrev SubprobValuation (X : Type u) [TopologicalSpace X] :=
  {μ : Valuation X // μ.Subprobability}

abbrev ScottOpens (P : Type u) [Preorder P] := Opens (WithScott P)
abbrev DValuation (P : Type u) [Preorder P] := Valuation (WithScott P)

/-- Bridge between order-theoretic continuity and the full intrinsic Scott
topologies, not any point-generated or ordinary product topology. -/
theorem scott_continuous_iff {P : Type u} {Q : Type v} [Preorder P] [Preorder Q]
    (f : P → Q) : ScottContinuous f ↔
    Continuous (fun x : WithScott P => WithScott.toScott (f (WithScott.ofScott x))) := by
  change ScottContinuous (fun x : WithScott P => WithScott.toScott (f (WithScott.ofScott x))) ↔ _
  rw [← scottContinuousOn_univ]
  exact Topology.IsScott.scottContinuousOn_iff_continuous (fun _ _ _ => mem_univ _)

end CantorFubini
