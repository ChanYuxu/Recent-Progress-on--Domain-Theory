import Mathlib.Algebra.Order.Floor.Semifield
import Practice.DomainTheory.Papers.LipschitzYonedaFinalTopology.LowerMapSuprema
import Practice.DomainTheory.Papers.LipschitzYonedaFinalTopology.PathEndpoint
import Practice.DomainTheory.Papers.LipschitzYonedaFinalTopology.Upperness

/-!
# The compact cone-forest neighborhood

This file formalizes the compact-neighborhood argument in the proof of the
algebraic case.  It starts from the concrete output of the recursive finite
cone interpolation: a finite-level cone forest, its functions `h_n`, a
uniform height bound, and the strict root inequalities.  It then constructs
the finite intersection `N` from source equation `eq:N` and proves
`f ∈ N ⊆ U`.

The separate task of constructing this data from algebraicity and the
relative openness of `U` remains outside this file; it is not hidden in the
statement proved here.
-/

set_option autoImplicit false
set_option linter.unnecessarySimpa false

open Set Function Topology
open scoped NNReal ENNReal Topology

universe u

namespace LipschitzYonedaFinalTopology
namespace QuasiMetric

variable {X : Type u} {d : QuasiMetric X}

/-- The left endpoint of the height bin containing `a`. -/
theorem floor_mul_le
    (a ε : ℝ≥0) (hε : 0 < ε) :
    ((Nat.floor ((a : ℝ) / (ε : ℝ)) : ℕ) : ℝ≥0) * ε ≤ a := by
  have h := Nat.floor_le (show 0 ≤ (a : ℝ) / (ε : ℝ) by positivity)
  apply NNReal.coe_le_coe.mp
  push_cast
  exact (le_div_iff₀ (NNReal.coe_pos.mpr hε)).mp h

/-- A height is strictly below the right endpoint of its floor bin. -/
theorem lt_floor_add_one_mul
    (a ε : ℝ≥0) (hε : 0 < ε) :
    a < ((Nat.floor ((a : ℝ) / (ε : ℝ)) + 1 : ℕ) : ℝ≥0) * ε := by
  have h := Nat.lt_floor_add_one ((a : ℝ) / (ε : ℝ))
  apply NNReal.coe_lt_coe.mp
  push_cast
  exact (div_lt_iff₀ (NNReal.coe_pos.mpr hε)).mp h

/-- Taking floor after division by a positive number is monotone. -/
theorem floor_div_mono
    (a A ε : ℝ≥0) (hε : 0 < ε) (ha : a ≤ A) :
    Nat.floor ((a : ℝ) / (ε : ℝ)) ≤
      Nat.floor ((A : ℝ) / (ε : ℝ)) := by
  apply Nat.floor_mono
  exact (div_le_div_iff_of_pos_right (NNReal.coe_pos.mpr hε)).mpr
    (NNReal.coe_le_coe.mpr ha)

/-- The source output needed after the recursive cone construction has been
performed.  Every field corresponds to an explicit assertion in the proof:
the slope indexing, membership of the root target, the represented functions
`h_n ∈ U`, a common height bound, and the strict root inequalities.

This is an intermediate data structure, not an assumption of the final
algebraic theorem. -/
structure ConeForestNeighborhoodData
    (d : QuasiMetric X) (f : d.LInf) (U : Set d.LInf) where
  base : ℕ
  C : d.FiniteConeForestData
  slope_eq : ∀ n,
    C.slope n = ((base + n + 1 : ℕ) : ℝ≥0)
  f_mem_base : f ∈ d.integerLayer base
  level : ℕ → d.LInf
  level_eq_envelope : ∀ n x,
    level n x = C.levelEnvelope n x
  level_mem : ∀ n, level n ∈ U
  heightBound : ℝ≥0
  height_le_bound : ∀ n (s : C.forest.Node n),
    C.height n s ≤ heightBound
  root_height_lt : ∀ s : C.forest.Node 0,
    (C.height 0 s : ℝ≥0∞) < f (C.center 0 s)

namespace FiniteConeForestData

/-- The `k`-th closed path-height superlevel set. -/
def pathHeightSuperlevel
    (C : d.FiniteConeForestData) (ε : ℝ≥0) (k : ℕ) :
    Set C.forest.Path :=
  {p | ((((k : ℕ) : ℝ≥0) * ε : ℝ≥0) : ℝ≥0∞) ≤ C.pathHeight p}

/-- The compact endpoint set `K_k = φ(C_k)` from the manuscript. -/
def endpointCompact
    (C : d.FiniteConeForestData)
    (hcomplete : d.IsYonedaComplete)
    (base : ℕ)
    (hslope : ∀ n,
      C.slope n = ((base + n + 1 : ℕ) : ℝ≥0))
    (ε : ℝ≥0) (k : ℕ) : Set d.DScott :=
  C.pathEndpointDScott hcomplete base hslope ''
    C.pathHeightSuperlevel ε k

/-- `K_k` is compact: its source is a closed subset of the compact path
space and the endpoint map is continuous. -/
theorem isCompact_endpointCompact
    (C : d.FiniteConeForestData)
    (hcomplete : d.IsYonedaComplete)
    (base : ℕ)
    (hslope : ∀ n,
      C.slope n = ((base + n + 1 : ℕ) : ℝ≥0))
    (ε : ℝ≥0) (k : ℕ) :
    IsCompact (C.endpointCompact hcomplete base hslope ε k) := by
  exact (C.isCompact_pathHeight_superlevel
      (((((k : ℕ) : ℝ≥0) * ε : ℝ≥0) : ℝ≥0∞))).image
    (C.continuous_pathEndpoint hcomplete base hslope)

end FiniteConeForestData

namespace ConeForestNeighborhoodData

/-- The number `M = floor(A / ε)` of relevant height bins. -/
noncomputable def maxBin
    {f : d.LInf} {U : Set d.LInf}
    (D : ConeForestNeighborhoodData d f U) (ε : ℝ≥0) : ℕ :=
  Nat.floor ((D.heightBound : ℝ) / (ε : ℝ))

/-- The ambient Scott-open finite intersection from source equation `eq:N`.
We use `K_k` itself; saturation is unnecessary because every lower map has
open strict superlevel sets and hence has the same condition on `K_k` and on
its saturation. -/
noncomputable def ambientNeighborhood
    {f : d.LInf} {U : Set d.LInf}
    (D : ConeForestNeighborhoodData d f U)
    (hcomplete : d.IsYonedaComplete)
    (ε : ℝ≥0) : Set d.LSpace :=
  ⋂ k : Fin (D.maxBin ε + 1),
    d.compactStrictSuperlevel
      (D.C.endpointCompact hcomplete D.base D.slope_eq ε k.1)
      (((((k.1 + 1 : ℕ) : ℝ≥0) * ε : ℝ≥0) : ℝ≥0∞))

/-- The neighborhood in `𝓛∞`, obtained by restriction of the ambient
Scott-open finite intersection. -/
noncomputable def neighborhood
    {f : d.LInf} {U : Set d.LInf}
    (D : ConeForestNeighborhoodData d f U)
    (hcomplete : d.IsYonedaComplete)
    (ε : ℝ≥0) : Set d.LInf :=
  ((↑) : d.LInf → d.LSpace) ⁻¹'
    D.ambientNeighborhood hcomplete ε

/-- The cone-forest neighborhood is open in the inherited topology of
`𝓛∞`. -/
theorem isOpen_neighborhood
    {f : d.LInf} {U : Set d.LInf}
    (D : ConeForestNeighborhoodData d f U)
    (hcomplete : d.IsYonedaComplete)
    (ε : ℝ≥0) :
    IsOpen (D.neighborhood hcomplete ε) := by
  have hopen : IsOpen (D.ambientNeighborhood hcomplete ε) := by
    apply isOpen_iInter_of_finite
    intro k
    exact d.isOpen_compactStrictSuperlevel
      (D.C.endpointCompact hcomplete D.base D.slope_eq ε k.1)
      (D.C.isCompact_endpointCompact hcomplete D.base D.slope_eq ε k.1)
      (((((k.1 + 1 : ℕ) : ℝ≥0) * ε : ℝ≥0) : ℝ≥0∞))
  exact hopen.preimage continuous_subtype_val

/-- The root margin makes the target function belong to the compact
cone-forest neighborhood.  This is the use of source equation
`eq:uniform-margin` in the construction of `eq:N`. -/
theorem mem_neighborhood_of_root_margin
    {f : d.LInf} {U : Set d.LInf}
    (D : ConeForestNeighborhoodData d f U)
    (hcomplete : d.IsYonedaComplete)
    {δ ε : ℝ≥0}
    (hε : 0 < ε) (hεδ : ε < δ)
    (hrootMargin : ∀ r : D.C.forest.Node 0,
      ((D.C.height 0 r + δ : ℝ≥0) : ℝ≥0∞) ≤
        f (D.C.center 0 r)) :
    f ∈ D.neighborhood hcomplete ε := by
  have hfLip : d.IsLipschitz (D.C.slope 0) f := by
    rw [D.slope_eq 0]
    simpa using D.f_mem_base.1
  change f.1 ∈ D.ambientNeighborhood hcomplete ε
  rw [ambientNeighborhood]
  refine Set.mem_iInter.mpr ?_
  intro k
  intro x hx
  obtain ⟨p, hp, rfl⟩ := hx
  have hmargin := D.C.pathHeight_add_margin_le_endpoint
    hcomplete D.base D.slope_eq hfLip hrootMargin p
  have hbin :
      (((((k.1 + 1 : ℕ) : ℝ≥0) * ε : ℝ≥0) : ℝ≥0∞)) =
        (((((k.1 : ℕ) : ℝ≥0) * ε : ℝ≥0) : ℝ≥0∞)) +
          (ε : ℝ≥0∞) := by
    norm_num [Nat.cast_add, add_mul, ENNReal.coe_add, ENNReal.coe_mul]
  let r := D.C.pathRootNode p
  have hr : p.1 0 = some r := D.C.pathRootNode_spec p
  have hheightFinite : D.C.pathHeight p ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.coe_ne_top
      (D.C.pathHeight_le_node p hr)
  have hstrict :
      D.C.pathHeight p + (ε : ℝ≥0∞) <
        D.C.pathHeight p + (δ : ℝ≥0∞) :=
    ENNReal.add_lt_add_left hheightFinite (ENNReal.coe_lt_coe.mpr hεδ)
  rw [hbin]
  exact ((add_le_add hp le_rfl).trans_lt hstrict).trans_le hmargin

/-- Every function in the compact cone-forest neighborhood lies in `U`.
For each node, its height is placed in a floor bin; the corresponding
compact condition forces the represented level envelope below the function.
Upperness of `U` then finishes the argument. -/
theorem neighborhood_subset
    {f : d.LInf} {U : Set d.LInf}
    (D : ConeForestNeighborhoodData d f U)
    (hcomplete : d.IsYonedaComplete)
    {ε : ℝ≥0} (hε : 0 < ε)
    (hUpper : IsUpperSet U) :
    D.neighborhood hcomplete ε ⊆ U := by
  intro g hg
  change g.1 ∈ D.ambientNeighborhood hcomplete ε at hg
  obtain ⟨j, hgj⟩ := d.integerLayer_cover g
  have hj : j ≤ D.base + j := by omega
  have hgLayer : g ∈ d.integerLayer (D.base + j) :=
    d.integerLayer_mono hj hgj
  have hgLip : d.IsLipschitz (D.C.slope j) g := by
    rw [D.slope_eq j]
    simpa [Nat.add_assoc] using hgLayer.1
  have hheight : ∀ s : D.C.forest.Node j,
      (D.C.height j s : ℝ≥0∞) ≤ g (D.C.center j s) := by
    intro s
    let k := Nat.floor
      (((D.C.height j s : ℝ≥0) : ℝ) / (ε : ℝ))
    have hkM : k ≤ D.maxBin ε := by
      exact floor_div_mono (D.C.height j s) D.heightBound ε hε
        (D.height_le_bound j s)
    let kfin : Fin (D.maxBin ε + 1) :=
      ⟨k, Nat.lt_succ_iff.mpr hkM⟩
    have hpHeight : D.C.forest.nodePath j s ∈
        D.C.pathHeightSuperlevel ε k := by
      change (((((k : ℕ) : ℝ≥0) * ε : ℝ≥0) : ℝ≥0∞)) ≤
        D.C.pathHeight (D.C.forest.nodePath j s)
      rw [D.C.pathHeight_nodePath]
      exact ENNReal.coe_le_coe.mpr (floor_mul_le (D.C.height j s) ε hε)
    have hxK : (D.C.center j s : d.DScott) ∈
        D.C.endpointCompact hcomplete D.base D.slope_eq ε k := by
      refine ⟨D.C.forest.nodePath j s, hpHeight, ?_⟩
      simpa [FiniteConeForestData.pathEndpointDScott] using
        D.C.pathEndpoint_nodePath hcomplete D.base D.slope_eq j s
    have hgCondition := Set.mem_iInter.mp hg kfin
    have hgThreshold :
        (((((k + 1 : ℕ) : ℝ≥0) * ε : ℝ≥0) : ℝ≥0∞)) <
          g (D.C.center j s) := by
      exact hgCondition (D.C.center j s) (by simpa [kfin] using hxK)
    have hheightBin :
        (D.C.height j s : ℝ≥0∞) <
          (((((k + 1 : ℕ) : ℝ≥0) * ε : ℝ≥0) : ℝ≥0∞)) :=
      ENNReal.coe_lt_coe.mpr
        (lt_floor_add_one_mul (D.C.height j s) ε hε)
    exact (hheightBin.trans hgThreshold).le
  have henvelope : D.C.levelEnvelope j ≤ g :=
    D.C.levelEnvelope_le_of_height_le j hgLip hheight
  have hlevel : D.level j ≤ g := by
    intro x
    change D.level j x ≤ g x
    rw [D.level_eq_envelope j x]
    exact henvelope x
  exact hUpper hlevel (D.level_mem j)

/-- A completed cone-forest construction supplies an actual open
neighborhood of `f` contained in `U`. -/
theorem exists_open_neighborhood
    {f : d.LInf} {U : Set d.LInf}
    (D : ConeForestNeighborhoodData d f U)
    (hcomplete : d.IsYonedaComplete)
    (hUpper : IsUpperSet U) :
    ∃ N : Set d.LInf, IsOpen N ∧ f ∈ N ∧ N ⊆ U := by
  letI : Nonempty (D.C.forest.Node 0) := D.C.node_nonempty 0
  obtain ⟨δ, hδ, hrootMargin⟩ :=
    exists_uniform_root_margin
      (D.C.center 0) (D.C.height 0) f D.root_height_lt
  obtain ⟨ε, hε, hεδ⟩ := exists_between hδ
  refine ⟨D.neighborhood hcomplete ε,
    D.isOpen_neighborhood hcomplete ε,
    D.mem_neighborhood_of_root_margin hcomplete hε hεδ hrootMargin,
    D.neighborhood_subset hcomplete hε hUpper⟩

end ConeForestNeighborhoodData

/-- Reduction of the algebraic theorem to the recursive finite-cone
construction.  The hypothesis asks for the concrete data structure above
only at nonzero points of layerwise-open sets; the zero case follows from
upperness.  A later theorem will discharge this hypothesis from
algebraicity. -/
theorem propertyD_of_coneForestNeighborhoodData
    (d : QuasiMetric X)
    (hcomplete : d.IsYonedaComplete)
    (hconstruct : ∀ (U : Set d.LInf),
      (∀ n : ℕ, IsOpen ((↑) ⁻¹' U : Set (d.integerLayer n))) →
      ∀ f ∈ U, f ≠ d.zeroLInf →
        Nonempty (ConeForestNeighborhoodData d f U)) :
    d.PropertyD := by
  apply d.layerSystem.propertyD_iff_layerwise_open.mpr
  intro U hU
  have hUpper : IsUpperSet U := d.layerwiseOpen_isUpper hU
  by_cases hzero : d.zeroLInf ∈ U
  · have hUuniv : U = Set.univ := by
      apply Set.eq_univ_of_forall
      intro g
      have hzero_le : d.zeroLInf ≤ g := by
        intro x
        change (0 : ℝ≥0∞) ≤ g x
        exact zero_le _
      exact hUpper hzero_le hzero
    rw [hUuniv]
    exact isOpen_univ
  · rw [isOpen_iff_mem_nhds]
    intro f hf
    have hfne : f ≠ d.zeroLInf := by
      intro h
      apply hzero
      simpa [h] using hf
    let D := Classical.choice (hconstruct U hU f hf hfne)
    obtain ⟨N, hNopen, hfN, hNU⟩ :=
      D.exists_open_neighborhood hcomplete hUpper
    exact Filter.mem_of_superset (hNopen.mem_nhds hfN) hNU

end QuasiMetric
end LipschitzYonedaFinalTopology
