import Mathlib.Topology.Order.ScottTopology
import Mathlib.Topology.Sets.Opens
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
Source: `source/manuscript.tex`, Sections 2--5. The appendix is excluded.
All products in centrality use the Scott topology of the ORDER product.
`WithScott` keeps this distinct from the topological product.
-/

set_option autoImplicit false
open Set Topology TopologicalSpace MeasureTheory
open scoped ENNReal
universe u v w

namespace PointCentralFubini

instance scottPartialOrder (P : Type u) [PartialOrder P] : PartialOrder (WithScott P) :=
  inferInstanceAs (PartialOrder P)
instance scottCompleteLattice (P : Type u) [CompleteLattice P] : CompleteLattice (WithScott P) :=
  inferInstanceAs (CompleteLattice P)
instance scottCompleteLinearOrder (P : Type u) [CompleteLinearOrder P] :
    CompleteLinearOrder (WithScott P) := inferInstanceAs (CompleteLinearOrder P)

/-- A dcpo has suprema of all NONEMPTY directed subsets. -/
def IsDcpo (P : Type u) [PartialOrder P] : Prop :=
  ∀ A : Set P, A.Nonempty → DirectedOn (· ≤ ·) A → ∃ p, IsLUB A p

theorem completeLattice_isDcpo (P : Type u) [CompleteLattice P] : IsDcpo P :=
  fun A _ _ => ⟨sSup A, isLUB_sSup A⟩

/-- Section 2.1: strict, monotone, modular and directed-continuous mass on opens. -/
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
instance : PartialOrder (Valuation X) where
  le μ ν := ∀ U, μ U ≤ ν U
  le_refl _ _ := le_rfl
  le_trans _ _ _ h k U := (h U).trans (k U)
  le_antisymm _ _ h k := ext fun U => le_antisymm (h U) (k U)

theorem mono (μ : Valuation X) : Monotone μ.mass := μ.continuous.monotone

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
  have hn : (Set.range U).Nonempty := Set.range_nonempty U
  have hd' : DirectedOn (· ≤ ·) (Set.range U) := hd.directedOn_range
  simpa only [sSup_range, iSup_range] using μ.map_sSup hn hd'

def Finite (μ : Valuation X) : Prop := μ ⊤ ≠ ⊤
def Subprobability (μ : Valuation X) : Prop := μ ⊤ ≤ 1

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
      μ.continuous (hn.image _) ((directedOn_image.mpr (hd.mono (fun _ _ h _ hx => h hx)))) he

@[simp] theorem push_apply {Y : Type v} [TopologicalSpace Y]
    (μ : Valuation X) (f : X → Y) (hf : Continuous f) (U : Opens Y) :
    μ.push f hf U = μ (Opens.comap ⟨f, hf⟩ U) := rfl

@[simp] theorem push_univ {Y : Type v} [TopologicalSpace Y]
    (μ : Valuation X) (f : X → Y) (hf : Continuous f) :
    μ.push f hf ⊤ = μ ⊤ := rfl

theorem finite_push {Y : Type v} [TopologicalSpace Y]
    {μ : Valuation X} (h : μ.Finite) (f : X → Y) (hf : Continuous f) :
    (μ.push f hf).Finite := h
end Valuation

/-- Strict-superlevel definition, with the Scott topology on `[0,∞]`. -/
def IsLSC {X : Type u} [TopologicalSpace X] (f : X → ℝ≥0∞) : Prop :=
  ∀ r : ℝ≥0∞, IsOpen {x | r < f x}

/-- For an LSC map the interior is the strict superlevel itself. The interior
also defines a total extension to arbitrary maps; theorems use LSC maps. -/
noncomputable def integral {X : Type u} [TopologicalSpace X]
    (μ : Valuation X) (f : X → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ t : ℝ in Ici (0 : ℝ),
    μ ⟨interior {x | ENNReal.ofReal t < f x}, isOpen_interior⟩

/-- Source definition 2.6; finite-witness basics define the point topology. -/
@[implicit_reducible] def pointTopology (X : Type u) [TopologicalSpace X] : TopologicalSpace (Opens X) where
  IsOpen H := ∀ U ∈ H, ∃ F : Finset X,
    (↑F : Set X) ⊆ U ∧ ∀ V : Opens X, (↑F : Set X) ⊆ V → V ∈ H
  isOpen_univ := by
    intro U _; exact ⟨∅, by simp, by simp⟩
  isOpen_inter := by
    intro H K hH hK U hU
    obtain ⟨F, hF, hFH⟩ := hH U hU.1
    obtain ⟨G, hG, hGK⟩ := hK U hU.2
    classical
    refine ⟨F ∪ G, ?_, ?_⟩
    · simpa using union_subset hF hG
    · intro V hV
      exact ⟨hFH V (fun _ hx => hV (by simp [hx])),
        hGK V (fun _ hx => hV (by simp [hx]))⟩
  isOpen_sUnion := by
    intro S hS U hU
    obtain ⟨H, hHS, hUH⟩ := hU
    obtain ⟨F, hF, hFH⟩ := hS H hHS U hUH
    exact ⟨F, hF, fun V hV => ⟨H, hHS, hFH V hV⟩⟩

/-- The definition uses actual continuity for the point topology. -/
def PointContinuous {X : Type u} [TopologicalSpace X] (μ : Valuation X) : Prop :=
  @Continuous (Opens X) (WithScott ℝ≥0∞) (pointTopology X) inferInstance
    (fun U => WithScott.toScott (μ U))

theorem scott_Ioi_open (r : ℝ≥0∞) :
    IsOpen {a : WithScott ℝ≥0∞ | r < WithScott.ofScott a} := by
  have hc : IsClosed (Iic (WithScott.toScott r)) := isClosed_Iic
  convert hc.isOpen_compl using 1
  ext a
  change (r < WithScott.ofScott a) ↔ ¬ WithScott.ofScott a ≤ r
  exact lt_iff_not_ge

/-- Source contract: `prop:heckmann` (proposition 2.3).
Version: SHA-256 `134da69fa816824e5fefcb93a4e77a8cd5158c8aaab5ffd288ece2372e55d4e6`.
Locator: `source/manuscript.tex`, lines 154--157; no PDF was supplied.
Formalization status: `proved`; human review is pending.

Strict source TeX:
```latex
\begin{proposition}\label{prop:heckmann}
\cite[Section~2.1]{GLJ2021}
A continuous valuation $\nu$ on $X$ is point-continuous if and only if, for every $U\in\OO(X)$ and $0\leq r<\nu(U)$, some finite $F\subseteq U$ satisfies $\nu(V)>r$ whenever $F\subseteq V\in\OO(X)$.
\end{proposition}
```
-/
theorem pointContinuous_iff {X : Type u} [TopologicalSpace X] (μ : Valuation X) :
    PointContinuous μ ↔ ∀ (U : Opens X) (r : ℝ≥0∞), r < μ U →
      ∃ F : Finset X, (↑F : Set X) ⊆ U ∧
        ∀ V : Opens X, (↑F : Set X) ⊆ V → r < μ V := by
  letI : TopologicalSpace (Opens X) := pointTopology X
  constructor
  · intro h U r hr
    have ho := scott_Ioi_open r
    exact h.isOpen_preimage _ ho U hr
  · intro h
    apply continuous_def.mpr
    intro S hs
    rcases Topology.IsScott.isOpen_iff_Iic_compl_or_univ S |>.mp hs with rfl | ⟨a, rfl⟩
    · exact (pointTopology X).isOpen_univ
    · intro U hu
      simpa only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_Iic, not_le] using
        h U (WithScott.ofScott a) (lt_of_not_ge hu)

abbrev ScottOpens (P : Type u) [Preorder P] := Opens (WithScott P)
abbrev DValuation (P : Type u) [Preorder P] := Valuation (WithScott P)

/-- Section 2.2: extended centrality, for arbitrary mass and integrands.
The partner universe is explicit; theorem wrappers are polymorphic in it. -/
def Commute {P : Type u} {Q : Type v} [PartialOrder P] [PartialOrder Q]
    (μ : DValuation P) (ν : DValuation Q) : Prop :=
  ∀ h : P × Q → ℝ≥0∞, ScottContinuous h →
    integral μ (fun x => integral ν (fun y => h (WithScott.ofScott x, WithScott.ofScott y))) =
    integral ν (fun y => integral μ (fun x => h (WithScott.ofScott x, WithScott.ofScott y)))

def Central {P : Type u} [PartialOrder P] (μ : DValuation P) : Prop :=
  ∀ (Q : Type v) [PartialOrder Q], IsDcpo Q → ∀ ν : DValuation Q, Commute μ ν

/-- Source contract: `def:fubini-object` (definition 2.6).
Version: SHA-256 `134da69fa816824e5fefcb93a4e77a8cd5158c8aaab5ffd288ece2372e55d4e6`.
Locator: `source/manuscript.tex`, lines 177--179; no PDF was supplied.
Formalization status: `definition`; human review is pending.

Strict source TeX:
```latex
\begin{definition}\label{def:fubini-object}
A dcpo $P$ is a \emph{Fubini object} if $\Val(P)=\Central(P)$. Write $\Fub$ for this class.
\end{definition}
```
-/
def FubiniObject (P : Type u) [PartialOrder P] : Prop :=
  ∀ μ : DValuation P, Central.{u,v} μ

end PointCentralFubini
