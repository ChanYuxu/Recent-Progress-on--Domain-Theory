import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.Order.Field.Pi
import Mathlib.Data.ENNReal.Inv
import Mathlib.Topology.Compactness.NhdsKer
import Practice.DomainTheory.Papers.LipschitzYonedaFinalTopology.Forest
import Practice.DomainTheory.Papers.LipschitzYonedaFinalTopology.FormalBallChains
import Practice.DomainTheory.Papers.LipschitzYonedaFinalTopology.Interpolation

/-!
# Cone-forest parent selection and formal-ball chains

This module formalizes the numerical core of the cone-forest construction in
source lines 506--548.  A child cone whose height is strictly below the
previous finite cone envelope has a parent cone witnessing the strict
inequality from equation `eq:parent`.  For positive increasing slopes, that
inequality makes the corresponding finite-radius formal balls comparable.

Existence of suprema of the resulting infinite chains, and identification of
their radii using standardness, remain separate domain-theoretic inputs.
-/

set_option autoImplicit false
set_option linter.unnecessarySimpa false

open Set Filter
open scoped NNReal ENNReal Topology

noncomputable section

universe u v w

namespace LipschitzYonedaFinalTopology
namespace QuasiMetric

variable {X : Type u} (d : QuasiMetric X)

/-- A simultaneous choice of a parent cone for each node in the next level.
The stored strict cone inequality is exactly source line 508. -/
structure ConeParentSelection
    {Parent : Type v} {Child : Type w}
    [Fintype Parent] [Nonempty Parent]
    (slope : ℝ≥0)
    (parentCenter : Parent → X) (parentHeight : Parent → ℝ≥0)
    (childCenter : Child → X) (childHeight : Child → ℝ≥0) where
  parent : Child → Parent
  cone_lt : ∀ t,
    (childHeight t : ℝ≥0∞) <
      d.cone slope (parentCenter (parent t))
        (parentHeight (parent t)) (childCenter t)

namespace ConeParentSelection

variable {d}

/-- The selected parent satisfies source equation `eq:parent`. -/
theorem scaled_edist_lt
    {Parent : Type v} {Child : Type w}
    [Fintype Parent] [Nonempty Parent]
    {slope : ℝ≥0}
    {parentCenter : Parent → X} {parentHeight : Parent → ℝ≥0}
    {childCenter : Child → X} {childHeight : Child → ℝ≥0}
    (R : d.ConeParentSelection slope parentCenter parentHeight
      childCenter childHeight) (t : Child) :
    (childHeight t : ℝ≥0∞) +
        (slope : ℝ≥0∞) *
          d.edist (parentCenter (R.parent t)) (childCenter t) <
      (parentHeight (R.parent t) : ℝ≥0∞) := by
  exact lt_tsub_iff_right.mp (by simpa [cone] using R.cone_lt t)

/-- Heights strictly decrease from a parent to each child. -/
theorem height_lt
    {Parent : Type v} {Child : Type w}
    [Fintype Parent] [Nonempty Parent]
    {slope : ℝ≥0}
    {parentCenter : Parent → X} {parentHeight : Parent → ℝ≥0}
    {childCenter : Child → X} {childHeight : Child → ℝ≥0}
    (R : d.ConeParentSelection slope parentCenter parentHeight
      childCenter childHeight) (t : Child) :
    childHeight t < parentHeight (R.parent t) := by
  apply ENNReal.coe_lt_coe.mp
  exact (le_add_right le_rfl).trans_lt (R.scaled_edist_lt t)

end ConeParentSelection

/-- Select all parent nodes from the strict comparison with the preceding
finite envelope.  This is the finite maximum argument of source lines
506--514. -/
noncomputable def selectConeParents
    {Parent : Type v} {Child : Type w}
    [Fintype Parent] [Nonempty Parent]
    (slope : ℝ≥0)
    (parentCenter : Parent → X) (parentHeight : Parent → ℝ≥0)
    (childCenter : Child → X) (childHeight : Child → ℝ≥0)
    (hbelow : ∀ t,
      (childHeight t : ℝ≥0∞) <
        d.finiteConeEnvelope slope parentCenter
          (fun s ↦ (parentHeight s : ℝ≥0∞)) (childCenter t)) :
    d.ConeParentSelection slope parentCenter parentHeight
      childCenter childHeight := by
  classical
  have hexists : ∀ t : Child, ∃ s : Parent,
      (childHeight t : ℝ≥0∞) <
        d.cone slope (parentCenter s) (parentHeight s) (childCenter t) := by
    intro t
    obtain ⟨s, _hs, hcone⟩ :=
      d.exists_index_cone_gt_of_lt_finiteConeFamilyMax
        Finset.univ_nonempty (hbelow t)
    exact ⟨s, hcone⟩
  choose parent hparent using hexists
  exact ⟨parent, hparent⟩

/-- A scaled strict center-distance inequality implies comparability of the
formal balls with radii `a / slope` and `b / nextSlope`. -/
theorem formalBall_le_of_scaled_edist_lt
    {slope nextSlope : ℝ≥0} (hslope : 0 < slope)
    (hslopes : slope ≤ nextSlope)
    {x y : X} {a b : ℝ≥0}
    (hscaled :
      (b : ℝ≥0∞) + (slope : ℝ≥0∞) * d.edist x y <
        (a : ℝ≥0∞)) :
    (⟨x, a / slope⟩ : d.FormalBall) ≤
      (⟨y, b / nextSlope⟩ : d.FormalBall) := by
  rw [FormalBall.le_def]
  have hdist : d.edist x y ≠ ∞ := by
    intro htop
    have hslope_ne : (slope : ℝ≥0∞) ≠ 0 :=
      ENNReal.coe_ne_zero.mpr hslope.ne'
    have hbad := hscaled
    simp [htop, hslope_ne] at hbad
  have hlhs_ne :
      (b : ℝ≥0∞) + (slope : ℝ≥0∞) * d.edist x y ≠ ∞ := by
    finiteness
  have hnn :
      b + slope * (d.edist x y).toNNReal < a := by
    have hto :=
      (ENNReal.toNNReal_lt_toNNReal hlhs_ne ENNReal.coe_ne_top).mpr hscaled
    rw [ENNReal.toNNReal_add (by finiteness) (by finiteness),
      ENNReal.toNNReal_mul] at hto
    simpa using hto
  have hnextSlope : 0 < nextSlope := hslope.trans_le hslopes
  have hradius_nn :
      (d.edist x y).toNNReal + b / nextSlope ≤ a / slope := by
    calc
      (d.edist x y).toNNReal + b / nextSlope
          ≤ (d.edist x y).toNNReal + b / slope := by
            exact add_le_add_right
              (div_le_div_of_nonneg_left (zero_le b) hslope hslopes) _
      _ = (slope * (d.edist x y).toNNReal + b) / slope := by
            field_simp
      _ ≤ a / slope := by
            exact (div_le_div_iff_of_pos_right hslope).mpr
              (by simpa [add_comm] using hnn.le)
  rw [← ENNReal.coe_toNNReal hdist]
  exact_mod_cast hradius_nn

/-- If a sequence of formal balls has a least upper bound and its radii tend
to zero, then the least upper bound has radius zero.  This is the
order/topology part of the branch-supremum calculation and does not require
standardness once the least upper bound is supplied. -/
theorem FormalBall.radius_eq_zero_of_isLUB
    (p : ℕ → d.FormalBall) (q : d.FormalBall)
    (hq : IsLUB (Set.range p) q)
    (hradius : Tendsto (fun n ↦ (p n).radius) atTop (𝓝 0)) :
    q.radius = 0 := by
  apply le_antisymm _ (zero_le _)
  by_contra hnot
  have hqpos : 0 < q.radius := lt_of_not_ge hnot
  have hevent : ∀ᶠ n : ℕ in atTop, (p n).radius < q.radius :=
    (tendsto_order.1 hradius).2 q.radius hqpos
  obtain ⟨n, hn⟩ := Filter.Eventually.exists hevent
  have hpq : p n ≤ q := hq.1 ⟨n, rfl⟩
  have hrle : q.radius ≤ (p n).radius := by
    apply ENNReal.coe_le_coe.mp
    exact (show (q.radius : ℝ≥0∞) ≤
        d.edist (p n).center q.center + (q.radius : ℝ≥0∞) from
          le_add_left le_rfl).trans hpq
  exact (not_lt_of_ge hrle) hn

/-- Parent selection supplies the formal-ball step used along every branch.
The slopes may be any positive increasing pair; the manuscript specializes
them to `n` and `n+1`. -/
theorem ConeParentSelection.formalBall_le_child
    {Parent : Type v} {Child : Type w}
    [Fintype Parent] [Nonempty Parent]
    {slope nextSlope : ℝ≥0} (hslope : 0 < slope)
    (hslopes : slope ≤ nextSlope)
    {parentCenter : Parent → X} {parentHeight : Parent → ℝ≥0}
    {childCenter : Child → X} {childHeight : Child → ℝ≥0}
    (R : d.ConeParentSelection slope parentCenter parentHeight
      childCenter childHeight) (t : Child) :
    (⟨parentCenter (R.parent t), parentHeight (R.parent t) / slope⟩ :
        d.FormalBall) ≤
      (⟨childCenter t, childHeight t / nextSlope⟩ : d.FormalBall) :=
  d.formalBall_le_of_scaled_edist_lt hslope hslopes
    (R.scaled_edist_lt t)

/-- A finite nonempty root family with strict height bounds admits one common
positive finite margin.  This is source equation `eq:root-margin`. -/
theorem exists_uniform_root_margin
    {Root : Type v} [Finite Root] [Nonempty Root]
    (center : Root → X) (height : Root → ℝ≥0) (f : X → ℝ≥0∞)
    (hroot : ∀ s, (height s : ℝ≥0∞) < f (center s)) :
    ∃ δ : ℝ≥0, 0 < δ ∧
      ∀ s, ((height s + δ : ℝ≥0) : ℝ≥0∞) ≤ f (center s) := by
  choose cap hheight_cap hcap_f using fun s ↦
    ENNReal.lt_iff_exists_nnreal_btwn.mp (hroot s)
  have hheight_cap_nn : ∀ s, height s < cap s := by
    intro s
    exact_mod_cast hheight_cap s
  obtain ⟨δ, hδ, hmargin⟩ :=
    Pi.exists_forall_pos_add_lt hheight_cap_nn
  refine ⟨δ, hδ, fun s ↦ ?_⟩
  exact (ENNReal.coe_lt_coe.mpr (hmargin s)).le.trans (hcap_f s).le

/-- The common root margin propagates strictly to every positive height below
the root cone envelope.  This is the finite-descendant estimate in source
lines 589--603. -/
theorem finiteConeEnvelope_margin
    {Root : Type v} [Fintype Root] [Nonempty Root]
    {slope : ℝ≥0}
    {center : Root → X} {height : Root → ℝ≥0}
    {f : X → ℝ≥0∞} (hf : d.IsLipschitz slope f)
    {δ : ℝ≥0}
    (hrootMargin : ∀ s,
      ((height s + δ : ℝ≥0) : ℝ≥0∞) ≤ f (center s))
    {y : X} {b : ℝ≥0}
    (hbelow : (b : ℝ≥0∞) <
      d.finiteConeEnvelope slope center
        (fun s ↦ (height s : ℝ≥0∞)) y) :
    (b : ℝ≥0∞) + (δ : ℝ≥0∞) < f y := by
  obtain ⟨s, _hs, hcone⟩ :=
    d.exists_index_cone_gt_of_lt_finiteConeFamilyMax
      Finset.univ_nonempty hbelow
  have hscaled :
      (b : ℝ≥0∞) +
          (slope : ℝ≥0∞) * d.edist (center s) y <
        (height s : ℝ≥0∞) :=
    lt_tsub_iff_right.mp (by simpa [cone] using hcone)
  have hproduct_lt :
      (slope : ℝ≥0∞) * d.edist (center s) y <
        (height s : ℝ≥0∞) :=
    (le_add_left le_rfl).trans_lt hscaled
  have hproduct_ne :
      (slope : ℝ≥0∞) * d.edist (center s) y ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.coe_ne_top hproduct_lt.le
  have hfx :
      f (center s) ≤
        (slope : ℝ≥0∞) * d.edist (center s) y + f y := by
    simpa [add_comm] using tsub_le_iff_left.mp (hf (center s) y)
  have hadd := ENNReal.add_lt_add_right
    (a := (δ : ℝ≥0∞)) ENNReal.coe_ne_top hscaled
  have hsum :
      (slope : ℝ≥0∞) * d.edist (center s) y +
          ((b : ℝ≥0∞) + (δ : ℝ≥0∞)) <
        (slope : ℝ≥0∞) * d.edist (center s) y + f y := by
    calc
      (slope : ℝ≥0∞) * d.edist (center s) y +
            ((b : ℝ≥0∞) + (δ : ℝ≥0∞)) =
          ((b : ℝ≥0∞) +
            (slope : ℝ≥0∞) * d.edist (center s) y) + δ := by
              ac_rfl
      _ < (height s : ℝ≥0∞) + δ := hadd
      _ = ((height s + δ : ℝ≥0) : ℝ≥0∞) := by
            rw [ENNReal.coe_add]
      _ ≤ f (center s) := hrootMargin s
      _ ≤ (slope : ℝ≥0∞) * d.edist (center s) y + f y := hfx
  exact (ENNReal.add_lt_add_iff_left hproduct_ne).mp hsum

/-- A single strict root-cone inequality propagates a root margin to its
target point.  This is the pointwise calculation inside
`finiteConeEnvelope_margin`, exposed for the path endpoint argument. -/
theorem margin_of_scaled_edist_lt
    {slope : ℝ≥0} {root y : X} {rootHeight b δ : ℝ≥0}
    {f : X → ℝ≥0∞} (hf : d.IsLipschitz slope f)
    (hscaled :
      (b : ℝ≥0∞) + (slope : ℝ≥0∞) * d.edist root y <
        (rootHeight : ℝ≥0∞))
    (hrootMargin :
      ((rootHeight + δ : ℝ≥0) : ℝ≥0∞) ≤ f root) :
    (b : ℝ≥0∞) + (δ : ℝ≥0∞) < f y := by
  have hproduct_lt :
      (slope : ℝ≥0∞) * d.edist root y < (rootHeight : ℝ≥0∞) :=
    (le_add_left le_rfl).trans_lt hscaled
  have hproduct_ne :
      (slope : ℝ≥0∞) * d.edist root y ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.coe_ne_top hproduct_lt.le
  have hfy :
      f root ≤ (slope : ℝ≥0∞) * d.edist root y + f y := by
    simpa [add_comm] using tsub_le_iff_left.mp (hf root y)
  have hadd := ENNReal.add_lt_add_right
    (a := (δ : ℝ≥0∞)) ENNReal.coe_ne_top hscaled
  have hsum :
      (slope : ℝ≥0∞) * d.edist root y +
          ((b : ℝ≥0∞) + (δ : ℝ≥0∞)) <
        (slope : ℝ≥0∞) * d.edist root y + f y := by
    calc
      (slope : ℝ≥0∞) * d.edist root y +
            ((b : ℝ≥0∞) + (δ : ℝ≥0∞)) =
          ((b : ℝ≥0∞) +
            (slope : ℝ≥0∞) * d.edist root y) + δ := by
              ac_rfl
      _ < (rootHeight : ℝ≥0∞) + δ := hadd
      _ = ((rootHeight + δ : ℝ≥0) : ℝ≥0∞) := by
            rw [ENNReal.coe_add]
      _ ≤ f root := hrootMargin
      _ ≤ (slope : ℝ≥0∞) * d.edist root y + f y := hfy
  exact (ENNReal.add_lt_add_iff_left hproduct_ne).mp hsum

/-- A finite-level forest equipped with the cone centers, finite heights, and
increasing positive slopes used in the manuscript's recursive construction.
The last field is source equation `eq:parent` at every edge. -/
structure FiniteConeForestData (d : QuasiMetric X) where
  forest : FiniteLevelForest.{u}
  /-- A chosen enumeration of every finite level.  Keeping this data avoids
  changing a labelled finite cone envelope when the forest's `Finite`
  instance is converted back to a `Fintype`. -/
  nodeFintype : ∀ n, Fintype (forest.Node n)
  node_nonempty : ∀ n, Nonempty (forest.Node n)
  center : ∀ n, forest.Node n → X
  height : ∀ n, forest.Node n → ℝ≥0
  slope : ℕ → ℝ≥0
  slope_pos : ∀ n, 0 < slope n
  slope_mono : Monotone slope
  parent_scaled_edist_lt : ∀ n (t : forest.Node (n + 1)),
    (height (n + 1) t : ℝ≥0∞) +
        (slope n : ℝ≥0∞) *
          d.edist (center n (forest.parent n t)) (center (n + 1) t) <
      (height n (forest.parent n t) : ℝ≥0∞)
  /-- Every non-root node lies strictly below one cone from the root
  envelope.  The recursive source construction obtains this from
  `h_n ≤ h_{n₀}` and `a_t < h_{n-1}(x_t)`. -/
  root_scaled_edist_lt : ∀ n (s : forest.Node n), n ≠ 0 →
    ∃ r : forest.Node 0,
      (height n s : ℝ≥0∞) +
          (slope 0 : ℝ≥0∞) *
            d.edist (center 0 r) (center n s) <
        (height 0 r : ℝ≥0∞)

namespace FiniteConeForestData

variable {d}

/-- The finite cone envelope represented by one level of the forest. -/
noncomputable def levelEnvelope
    (C : d.FiniteConeForestData) (n : ℕ) : X → ℝ≥0∞ := by
  letI : Fintype (C.forest.Node n) := C.nodeFintype n
  letI : Nonempty (C.forest.Node n) := C.node_nonempty n
  exact d.finiteConeEnvelope (C.slope n) (C.center n)
    (fun s ↦ (C.height n s : ℝ≥0∞))

/-- A level envelope has the displayed slope. -/
theorem levelEnvelope_isLipschitz
    (C : d.FiniteConeForestData) (n : ℕ) :
    d.IsLipschitz (C.slope n) (C.levelEnvelope n) := by
  letI : Fintype (C.forest.Node n) := C.nodeFintype n
  letI : Nonempty (C.forest.Node n) := C.node_nonempty n
  exact d.finiteConeEnvelope_isLipschitz (C.slope n) (C.center n)
    (fun s ↦ (C.height n s : ℝ≥0∞))

/-- Minimality of a finite level envelope. -/
theorem levelEnvelope_le_of_height_le
    (C : d.FiniteConeForestData) (n : ℕ)
    {g : X → ℝ≥0∞} (hg : d.IsLipschitz (C.slope n) g)
    (hheight : ∀ s : C.forest.Node n,
      (C.height n s : ℝ≥0∞) ≤ g (C.center n s)) :
    C.levelEnvelope n ≤ g := by
  letI : Fintype (C.forest.Node n) := C.nodeFintype n
  letI : Nonempty (C.forest.Node n) := C.node_nonempty n
  exact d.finiteConeFamilyMax_le_of_isLipschitz
    Finset.univ_nonempty hg (fun s _hs ↦ hheight s)

/-- An infinite compatible branch through every level of the cone forest. -/
structure InfiniteBranch (C : d.FiniteConeForestData) where
  node : ∀ n, C.forest.Node n
  parent_eq : ∀ n, C.forest.parent n (node (n + 1)) = node n

/-- Regard an infinite branch as a point of the compact path space. -/
def InfiniteBranch.toPath
    {C : d.FiniteConeForestData} (branch : C.InfiniteBranch) :
    C.forest.Path :=
  ⟨fun n ↦ some (branch.node n), by
    constructor
    · simp
    · intro n
      simp [FiniteLevelForest.StepOK, branch.parent_eq n]⟩

/-- The formal ball associated with a node of a cone forest. -/
def formalBall (C : d.FiniteConeForestData)
    (n : ℕ) (s : C.forest.Node n) : d.FormalBall :=
  ⟨C.center n s, C.height n s / C.slope n⟩

/-- Heights strictly decrease across every parent edge. -/
theorem edge_height_lt
    (C : d.FiniteConeForestData) (n : ℕ)
    (t : C.forest.Node (n + 1)) :
    C.height (n + 1) t < C.height n (C.forest.parent n t) := by
  apply ENNReal.coe_lt_coe.mp
  exact (le_add_right le_rfl).trans_lt (C.parent_scaled_edist_lt n t)

/-- Heights strictly decrease at every edge of an infinite branch. -/
theorem branch_height_step_lt
    (C : d.FiniteConeForestData) (branch : C.InfiniteBranch) (n : ℕ) :
    C.height (n + 1) (branch.node (n + 1)) <
      C.height n (branch.node n) := by
  simpa [branch.parent_eq n] using
    C.edge_height_lt n (branch.node (n + 1))

/-- The node heights along a branch form an antitone sequence. -/
theorem branch_height_antitone
    (C : d.FiniteConeForestData) (branch : C.InfiniteBranch) :
    Antitone (fun n ↦ C.height n (branch.node n)) :=
  antitone_nat_of_succ_le fun n ↦ (C.branch_height_step_lt branch n).le

/-- Every descendant height is bounded by the height of its root. -/
theorem branch_height_le_root
    (C : d.FiniteConeForestData) (branch : C.InfiniteBranch) (n : ℕ) :
    C.height n (branch.node n) ≤ C.height 0 (branch.node 0) :=
  C.branch_height_antitone branch (Nat.zero_le n)

/-- Consecutive nodes on a branch determine comparable formal balls. -/
theorem branch_formalBall_step
    (C : d.FiniteConeForestData) (branch : C.InfiniteBranch) (n : ℕ) :
    C.formalBall n (branch.node n) ≤
      C.formalBall (n + 1) (branch.node (n + 1)) := by
  apply d.formalBall_le_of_scaled_edist_lt
    (C.slope_pos n) (C.slope_mono (Nat.le_succ n))
  simpa [branch.parent_eq n] using
    C.parent_scaled_edist_lt n (branch.node (n + 1))

/-- The formal balls along an infinite cone-forest branch form an increasing
chain. -/
theorem branch_formalBall_monotone
    (C : d.FiniteConeForestData) (branch : C.InfiniteBranch) :
    Monotone (fun n ↦ C.formalBall n (branch.node n)) :=
  monotone_nat_of_le_succ fun n ↦ C.branch_formalBall_step branch n

/-- For source slopes `base+n+1` after reindexing an arbitrary initial
integer layer, the radii along every infinite branch tend to zero.  This
proves the bounded-height estimate from source lines 537--540 before any
dcpo supremum is invoked. -/
theorem branch_radius_tendsto_zero_from_base
    (C : d.FiniteConeForestData)
    (base : ℕ)
    (hslope : ∀ n,
      C.slope n = ((base + n + 1 : ℕ) : ℝ≥0))
    (branch : C.InfiniteBranch) :
    Tendsto
      (fun n ↦ C.height n (branch.node n) / C.slope n)
      atTop (𝓝 0) := by
  have hupper :
      Tendsto
        (fun n : ℕ ↦ C.height 0 (branch.node 0) /
          ((base + n + 1 : ℕ) : ℝ≥0))
        atTop (𝓝 0) := by
    convert
      (tendsto_const_div_atTop_nhds_zero_nat
        (C.height 0 (branch.node 0))).comp
          (tendsto_add_atTop_nat (base + 1)) using 1
    · funext n
      simp only [Function.comp_apply]
      congr 1
      simp [Nat.add_assoc, Nat.add_left_comm]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hupper
  · exact Eventually.of_forall fun _ ↦ zero_le _
  · exact Eventually.of_forall fun n ↦ by
      rw [hslope n]
      exact div_le_div_of_nonneg_right
        (C.branch_height_le_root branch n) (zero_le _)

/-- The center of the zero-radius least upper bound of an infinite branch.
The existence proof is no longer an interface: it follows directly from
Yoneda completeness and the vanishing-radius estimate. -/
def branchEndpoint
    (C : d.FiniteConeForestData)
    (hcomplete : d.IsYonedaComplete)
    (base : ℕ)
    (hslope : ∀ n,
      C.slope n = ((base + n + 1 : ℕ) : ℝ≥0))
    (branch : C.InfiniteBranch) : X :=
  Classical.choose <|
    d.exists_zeroRadius_isLUB_of_monotone
      hcomplete
      (fun n ↦ C.formalBall n (branch.node n))
      (C.branch_formalBall_monotone branch)
      (C.branch_radius_tendsto_zero_from_base base hslope branch)

/-- Source equation `eq:branch-sup`: the formal balls along an infinite
branch have supremum `(branchEndpoint, 0)`. -/
theorem branchEndpoint_isLUB
    (C : d.FiniteConeForestData)
    (hcomplete : d.IsYonedaComplete)
    (base : ℕ)
    (hslope : ∀ n,
      C.slope n = ((base + n + 1 : ℕ) : ℝ≥0))
    (branch : C.InfiniteBranch) :
    IsLUB
      (Set.range (fun n ↦ C.formalBall n (branch.node n)))
      (⟨C.branchEndpoint hcomplete base hslope branch, 0⟩ :
        d.FormalBall) :=
  Classical.choose_spec <|
    d.exists_zeroRadius_isLUB_of_monotone
      hcomplete
      (fun n ↦ C.formalBall n (branch.node n))
      (C.branch_formalBall_monotone branch)
      (C.branch_radius_tendsto_zero_from_base base hslope branch)

/-- Every branch formal ball lies below its zero-radius endpoint. -/
theorem branch_formalBall_le_endpoint
    (C : d.FiniteConeForestData)
    (hcomplete : d.IsYonedaComplete)
    (base : ℕ)
    (hslope : ∀ n,
      C.slope n = ((base + n + 1 : ℕ) : ℝ≥0))
    (branch : C.InfiniteBranch) (n : ℕ) :
    C.formalBall n (branch.node n) ≤
      (⟨C.branchEndpoint hcomplete base hslope branch, 0⟩ :
        d.FormalBall) :=
  (C.branchEndpoint_isLUB hcomplete base hslope branch).1 ⟨n, rfl⟩

/-- The zero-based specialization retained for the existing cone-forest
API. -/
theorem branch_radius_tendsto_zero
    (C : d.FiniteConeForestData)
    (hslope : ∀ n, C.slope n = ((n + 1 : ℕ) : ℝ≥0))
    (branch : C.InfiniteBranch) :
    Tendsto
      (fun n ↦ C.height n (branch.node n) / C.slope n)
      atTop (𝓝 0) := by
  apply C.branch_radius_tendsto_zero_from_base 0
  intro n
  simpa using hslope n

/-- The height of a finite or infinite compactified path is the infimum of
the heights of all its nonterminal nodes.  Along a finite path this is its
last (hence smallest) node height; along an infinite path it is the decreasing
limit used at source lines 568--573. -/
def pathHeight (C : d.FiniteConeForestData) (p : C.forest.Path) : ℝ≥0∞ :=
  ⨅ n : ℕ, ⨅ s : C.forest.Node n,
    ⨅ (_hs : p.1 n = some s), (C.height n s : ℝ≥0∞)

/-- Any node on a path bounds the path's infimum height from above. -/
theorem pathHeight_le_node
    (C : d.FiniteConeForestData) (p : C.forest.Path)
    {n : ℕ} {s : C.forest.Node n} (hs : p.1 n = some s) :
    C.pathHeight p ≤ (C.height n s : ℝ≥0∞) :=
  iInf_le_of_le n <| iInf_le_of_le s <| iInf_le_of_le hs le_rfl

/-- A later nonterminal node on a valid path has height at most that of every
earlier node. -/
theorem path_node_height_antitone
    (C : d.FiniteConeForestData) (p : C.forest.Path)
    {m n : ℕ} (hmn : m ≤ n)
    {s : C.forest.Node m} {t : C.forest.Node n}
    (hs : p.1 m = some s) (ht : p.1 n = some t) :
    C.height n t ≤ C.height m s := by
  revert t
  induction n, hmn using Nat.le_induction with
  | base =>
      intro t ht
      have hst : s = t := Option.some.inj (hs.symm.trans ht)
      subst t
      exact le_rfl
  | succ n hmn ih =>
      intro t ht
      have hparent : p.1 n = some (C.forest.parent n t) := by
        have hstep := p.2.2 n
        rw [ht] at hstep
        exact hstep
      exact (C.edge_height_lt n t).le.trans (ih hparent)

/-- If a valid path terminates immediately after node `s`, its infimum path
height is exactly the height of `s`. -/
theorem pathHeight_eq_height_of_terminal
    (C : d.FiniteConeForestData) (p : C.forest.Path)
    {n : ℕ} {s : C.forest.Node n}
    (hs : p.1 n = some s) (hterminal : p.1 (n + 1) = none) :
    C.pathHeight p = (C.height n s : ℝ≥0∞) := by
  apply le_antisymm (C.pathHeight_le_node p hs)
  apply le_iInf
  intro m
  apply le_iInf
  intro t
  apply le_iInf
  intro ht
  have hmn : m ≤ n := by
    by_contra hnot
    have hnm : n + 1 ≤ m := Nat.succ_le_of_lt (Nat.lt_of_not_ge hnot)
    have hmnone := C.forest.terminal_of_le p.2 hterminal hnm
    rw [ht] at hmnone
    contradiction
  exact_mod_cast C.path_node_height_antitone p hmn ht hs

/-- A strict bound above the infimum path height is already witnessed at a
finite node of the path. -/
theorem exists_node_height_lt_of_pathHeight_lt
    (C : d.FiniteConeForestData) (p : C.forest.Path) {c : ℝ≥0∞}
    (hp : C.pathHeight p < c) :
    ∃ n : ℕ, ∃ s : C.forest.Node n,
      p.1 n = some s ∧ (C.height n s : ℝ≥0∞) < c := by
  by_contra hnone
  have hc : c ≤ C.pathHeight p := by
    apply le_iInf
    intro n
    apply le_iInf
    intro s
    apply le_iInf
    intro hs
    exact le_of_not_gt fun hlt ↦ hnone ⟨n, s, hs, hlt⟩
  exact (not_lt_of_ge hc) hp

/-- Strict sublevel sets of the compactified path height are open.  This is
the upper-semicontinuity argument of source lines 568--576: once a node has
height below `c`, its finite-prefix cylinder stays below `c`. -/
theorem isOpen_pathHeight_sublevel
    (C : d.FiniteConeForestData) (c : ℝ≥0∞) :
    IsOpen {p : C.forest.Path | C.pathHeight p < c} := by
  apply isOpen_iff_forall_mem_open.mpr
  intro p hp
  obtain ⟨n, s, hs, hheight⟩ :=
    C.exists_node_height_lt_of_pathHeight_lt p hp
  refine ⟨C.forest.PrefixCylinder p n, ?_,
    C.forest.isOpen_prefixCylinder p n, ?_⟩
  · intro q hq
    apply (C.pathHeight_le_node q ?_).trans_lt hheight
    exact (hq n le_rfl).trans hs
  · intro k _hk
    rfl

/-- Superlevel sets of the upper-semicontinuous path height are closed. -/
theorem isClosed_pathHeight_superlevel
    (C : d.FiniteConeForestData) (c : ℝ≥0∞) :
    IsClosed {p : C.forest.Path | c ≤ C.pathHeight p} := by
  rw [← isOpen_compl_iff]
  simpa only [compl_setOf, not_le] using C.isOpen_pathHeight_sublevel c

/-- Every path-height superlevel is compact in the compactified path space. -/
theorem isCompact_pathHeight_superlevel
    (C : d.FiniteConeForestData) (c : ℝ≥0∞) :
    IsCompact {p : C.forest.Path | c ≤ C.pathHeight p} :=
  (C.isClosed_pathHeight_superlevel c).isCompact

/-- The topological saturation used by the manuscript is mathlib's
neighborhood kernel: the intersection of all open sets containing a set. -/
def compactSaturation
    {Y : Type*} [TopologicalSpace Y]
    (C : d.FiniteConeForestData) (c : ℝ≥0∞)
    (mapPath : C.forest.Path → Y) : Set Y :=
  nhdsKer (mapPath '' {p : C.forest.Path | c ≤ C.pathHeight p})

/-- The saturation of the compact image of a height superlevel is compact in
an arbitrary target topological space. -/
theorem isCompact_compactSaturation
    {Y : Type*} [TopologicalSpace Y]
    (C : d.FiniteConeForestData) (c : ℝ≥0∞)
    {mapPath : C.forest.Path → Y} (hmap : Continuous mapPath) :
    IsCompact (C.compactSaturation c mapPath) := by
  apply IsCompact.nhdsKer
  exact (C.isCompact_pathHeight_superlevel c).image hmap

/-- Every open set containing the compact superlevel image also contains its
saturation.  This packages the containment argument at source lines 636--640.
-/
theorem compactSaturation_subset_open
    {Y : Type*} [TopologicalSpace Y]
    (C : d.FiniteConeForestData) (c : ℝ≥0∞)
    {mapPath : C.forest.Path → Y} {U : Set Y}
    (hUopen : IsOpen U)
    (himage : mapPath '' {p : C.forest.Path | c ≤ C.pathHeight p} ⊆ U) :
    C.compactSaturation c mapPath ⊆ U :=
  nhdsKer_minimal himage hUopen

end FiniteConeForestData

end QuasiMetric
end LipschitzYonedaFinalTopology
