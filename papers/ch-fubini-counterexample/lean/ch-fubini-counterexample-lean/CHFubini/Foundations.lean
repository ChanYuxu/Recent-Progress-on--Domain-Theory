import Mathlib.Topology.Order.ScottTopology
import Mathlib.Topology.Sets.Opens
import Mathlib.Topology.Sober
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.SetTheory.Cardinal.Continuum
import Mathlib.Tactic

/-!
Exact conventions from Section 2 of the source-bound CH Fubini manuscript.
The unbounded `Valuation` is reusable infrastructure. The source's
subprobability and probability valuations are explicit predicates on it.
No completeness, countability, or continuity conclusion is assumed implicitly.

Provenance: valuation/order and layer-cake interfaces adapted from
`PointCentralFubini_Lean/PointCentralFubini/Basic.lean` and `Scott.lean`.
Only the copied definitions and proved elementary lemmas are used, not that
project's literature axioms. All imports below are from mathlib.
-/

set_option autoImplicit false
open Set Topology TopologicalSpace MeasureTheory
open scoped ENNReal Cardinal
universe u v w

namespace CHFubini

instance scottPartialOrder (P : Type u) [PartialOrder P] : PartialOrder (WithScott P) :=
  inferInstanceAs (PartialOrder P)

instance scottCompleteLattice (P : Type u) [CompleteLattice P] :
    CompleteLattice (WithScott P) := inferInstanceAs (CompleteLattice P)

/-- CH is an explicit mathematical hypothesis, not a project axiom. -/
def CH : Prop := Cardinal.continuum.{0} = Cardinal.aleph.{0} 1

/-- All directed sets in the manuscript are nonempty; no bottom is required. -/
def IsDcpo (P : Type u) [PartialOrder P] : Prop :=
  ∀ A : Set P, A.Nonempty → DirectedOn (· ≤ ·) A → ∃ p, IsLUB A p

theorem completeLattice_isDcpo (P : Type u) [CompleteLattice P] : IsDcpo P :=
  fun A _ _ => ⟨sSup A, isLUB_sSup A⟩

/-- Saturated means the intersection of all open supersets. -/
def IsSaturated {X : Type u} [TopologicalSpace X] (K : Set X) : Prop :=
  K = ⋂₀ {U : Set X | IsOpen U ∧ K ⊆ U}

/-- The paper's T0 well-filteredness, for arbitrary nonempty filtered families. -/
def IsWellFiltered (X : Type u) [TopologicalSpace X] : Prop :=
  T0Space X ∧ ∀ K : Set (Set X), K.Nonempty →
    (∀ C ∈ K, C.Nonempty ∧ IsCompact C ∧ IsSaturated C) →
    DirectedOn (fun C D : Set X => D ⊆ C) K →
    ∀ U : Set X, IsOpen U → ⋂₀ K ⊆ U → ∃ C ∈ K, C ⊆ U

/-- Mathlib separates existence of generic points from the T0 uniqueness law. -/
def IsSober (X : Type u) [TopologicalSpace X] : Prop := T0Space X ∧ QuasiSober X

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

/-- Strict-superlevel formulation of nonnegative lower semicontinuity. -/
def IsLSC {X : Type u} [TopologicalSpace X] (f : X → ℝ≥0∞) : Prop :=
  ∀ r : ℝ≥0∞, IsOpen {x | r < f x}

/-- Source equation (2.1), the Choquet layer-cake integral. For LSC functions,
the interior is exactly the strict superlevel (proved below). The interior
only makes the notation a total function on non-LSC inputs, on which no source
claim is made. The integration variable is the ordinary nonnegative real axis. -/
noncomputable def choquetIntegral {X : Type u} [TopologicalSpace X]
    (μ : Valuation X) (f : X → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ t : ℝ in Ici (0 : ℝ),
    μ ⟨interior {x | ENNReal.ofReal t < f x}, isOpen_interior⟩

theorem choquetIntegral_eq_layerCake {X : Type u} [TopologicalSpace X]
    (μ : Valuation X) (f : X → ℝ≥0∞) (hf : IsLSC f) :
    choquetIntegral μ f =
      ∫⁻ t : ℝ in Ici (0 : ℝ), μ ⟨{x | ENNReal.ofReal t < f x}, hf _⟩ := by
  unfold choquetIntegral
  apply lintegral_congr
  intro t
  congr 1
  exact Opens.ext ((hf _).interior_eq)

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

theorem scott_Ioi_open (r : ℝ≥0∞) :
    IsOpen {a : WithScott ℝ≥0∞ | r < WithScott.ofScott a} := by
  have hc : IsClosed (Iic (WithScott.toScott r)) := isClosed_Iic
  convert hc.isOpen_compl using 1
  ext a
  change (r < WithScott.ofScott a) ↔ ¬ WithScott.ofScott a ≤ r
  exact lt_iff_not_ge

theorem scott_isLSC {P : Type u} [Preorder P] {f : P → ℝ≥0∞}
    (hf : ScottContinuous f) : IsLSC (fun x : WithScott P => f (WithScott.ofScott x)) :=
  fun r => (scott_Ioi_open r).preimage ((scott_continuous_iff f).mp hf)

/-- Subprobability centrality: the partner is an arbitrary dcpo, and the
integrand is Scott-continuous on the ORDER product with values in [0,1]. -/
def Commute {P : Type u} {Q : Type v} [PartialOrder P] [PartialOrder Q]
    (μ : DValuation P) (ν : DValuation Q) : Prop :=
  ∀ h : P × Q → ℝ≥0∞, ScottContinuous h → (∀ z, h z ≤ 1) →
    choquetIntegral μ
        (fun x => choquetIntegral ν (fun y => h (WithScott.ofScott x, WithScott.ofScott y))) =
    choquetIntegral ν
        (fun y => choquetIntegral μ (fun x => h (WithScott.ofScott x, WithScott.ofScott y)))

def Central {P : Type u} [PartialOrder P] (μ : DValuation P) : Prop :=
  μ.Subprobability ∧ ∀ (Q : Type v) [PartialOrder Q], IsDcpo Q →
    ∀ ν : DValuation Q, ν.Subprobability → Commute μ ν

end CHFubini
