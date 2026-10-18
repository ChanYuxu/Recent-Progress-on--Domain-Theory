import Practice.DomainTheory.Papers.LipschitzYonedaFinalTopology.AlgebraicCore
import Practice.DomainTheory.Papers.LipschitzYonedaFinalTopology.ConeApproximation

/-!
# Recursive construction of the cone forest

Starting from a nonzero point `f` of a set that is open on every integer
layer, this module recursively chooses a nonempty finite center-cone
approximation in each successive layer.  The target of stage `n+1` is the
envelope chosen at stage `n`, so the represented functions form the
decreasing sequence used in the manuscript.
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

/-- The slope at level `n`, with level zero corresponding to the integer
layer indexed by `base`. -/
def forestSlope (base n : ℕ) : ℝ≥0 :=
  ((base + n + 1 : ℕ) : ℝ≥0)

theorem forestSlope_pos (base n : ℕ) : 0 < forestSlope base n := by
  simp [forestSlope]

theorem forestSlope_mono (base : ℕ) : Monotone (forestSlope base) := by
  intro n m hnm
  simp only [forestSlope]
  exact_mod_cast Nat.add_le_add_right (Nat.add_le_add_left hnm base) 1

/-- One recursive stage: a nonzero target already in `U` and in the correct
layer, together with a finite cone approximation selected in the same open
set. -/
structure ConeConstructionStage
    (d : QuasiMetric X)
    {hstandard : d.IsStandard}
    (facts : d.StandardConeFacts hstandard)
    (U : Set d.LInf) (base n : ℕ) where
  target : d.LInf
  target_mem_U : target ∈ U
  target_mem_layer : target ∈ d.integerLayer (base + n)
  target_ne_zero : target ≠ d.zeroLInf
  approximation : d.FiniteConeApproximation
    (forestSlope base n) target
  approximation_mem_U :
    approximation.toLInf facts (forestSlope_pos base n) ∈ U

namespace ConeConstructionStage

variable {hstandard : d.IsStandard}
variable {facts : d.StandardConeFacts hstandard}
variable {U : Set d.LInf} {base n : ℕ}

/-- The represented function at this level. -/
def level (S : d.ConeConstructionStage facts U base n) : d.LInf :=
  S.approximation.toLInf facts (forestSlope_pos base n)

@[simp]
theorem level_apply
    (S : d.ConeConstructionStage facts U base n) (x : X) :
    S.level x = S.approximation.envelope x :=
  rfl

theorem level_mem_U
    (S : d.ConeConstructionStage facts U base n) :
    S.level ∈ U :=
  S.approximation_mem_U

theorem level_ne_zero
    (S : d.ConeConstructionStage facts U base n) :
    S.level ≠ d.zeroLInf :=
  S.approximation.toLInf_ne_zero facts (forestSlope_pos base n)

theorem level_mem_layer
    (S : d.ConeConstructionStage facts U base n) :
    S.level ∈ d.integerLayer (base + n) := by
  simpa [integerLayer, forestSlope, Nat.add_assoc] using
    S.approximation.toLInf_inLayer facts (forestSlope_pos base n)

theorem level_le_target
    (S : d.ConeConstructionStage facts U base n) :
    S.level ≤ S.target := by
  have htarget : d.IsLipschitz (forestSlope base n) S.target := by
    simpa [integerLayer, forestSlope, Nat.add_assoc] using
      S.target_mem_layer.1
  intro x
  exact S.approximation.envelope_le_target htarget x

end ConeConstructionStage

/-- The recursively selected stages of the cone construction. -/
noncomputable def coneConstructionStages
    {hstandard : d.IsStandard}
    (facts : d.StandardConeFacts hstandard)
    (hcenters : d.HasEnoughCenterPoints)
    (U : Set d.LInf)
    (hU : ∀ n : ℕ,
      IsOpen ((↑) ⁻¹' U : Set (d.integerLayer n)))
    (f : d.LInf) (hfU : f ∈ U) (hfne : f ≠ d.zeroLInf)
    (base : ℕ) (hfbase : f ∈ d.integerLayer base) :
    (n : ℕ) → d.ConeConstructionStage facts U base n
  | 0 => by
      have hex : ∃ A : d.FiniteConeApproximation
          (forestSlope base 0) f,
          A.toLInf facts (forestSlope_pos base 0) ∈ U := by
        simpa [forestSlope] using
          d.exists_finiteConeApproximation_mem_layerOpen
            facts hcenters base (hU base) f hfU hfbase hfne
      let A := Classical.choose hex
      exact
        { target := f
          target_mem_U := hfU
          target_mem_layer := by simpa using hfbase
          target_ne_zero := hfne
          approximation := A
          approximation_mem_U := Classical.choose_spec hex }
  | n + 1 => by
      let P := coneConstructionStages facts hcenters U hU f hfU hfne
        base hfbase n
      let q := P.level
      have hqCurrent : q ∈ d.integerLayer (base + n) := P.level_mem_layer
      have hqNext : q ∈ d.integerLayer (base + (n + 1)) := by
        have hmono := d.integerLayer_mono
          (show base + n ≤ base + (n + 1) by omega) hqCurrent
        simpa using hmono
      have hex : ∃ A : d.FiniteConeApproximation
          (forestSlope base (n + 1)) q,
          A.toLInf facts (forestSlope_pos base (n + 1)) ∈ U := by
        simpa [forestSlope, Nat.add_assoc] using
          d.exists_finiteConeApproximation_mem_layerOpen
            facts hcenters (base + (n + 1)) (hU (base + (n + 1)))
              q P.level_mem_U hqNext P.level_ne_zero
      let A := Classical.choose hex
      exact
        { target := q
          target_mem_U := P.level_mem_U
          target_mem_layer := hqNext
          target_ne_zero := P.level_ne_zero
          approximation := A
          approximation_mem_U := Classical.choose_spec hex }

namespace ConeConstruction

variable {hstandard : d.IsStandard}
variable (facts : d.StandardConeFacts hstandard)
variable (hcenters : d.HasEnoughCenterPoints)
variable (U : Set d.LInf)
variable (hU : ∀ n : ℕ,
  IsOpen ((↑) ⁻¹' U : Set (d.integerLayer n)))
variable (f : d.LInf) (hfU : f ∈ U) (hfne : f ≠ d.zeroLInf)
variable (base : ℕ) (hfbase : f ∈ d.integerLayer base)

/-- Short name for the recursively selected stage. -/
def stage (n : ℕ) : d.ConeConstructionStage facts U base n :=
  coneConstructionStages facts hcenters U hU f hfU hfne base hfbase n

/-- The decreasing finite cone envelope at level `n`. -/
def level (n : ℕ) : d.LInf :=
  (stage facts hcenters U hU f hfU hfne base hfbase n).level

theorem level_mem_U (n : ℕ) :
    level facts hcenters U hU f hfU hfne base hfbase n ∈ U :=
  (stage facts hcenters U hU f hfU hfne base hfbase n).level_mem_U

theorem level_mem_layer (n : ℕ) :
    level facts hcenters U hU f hfU hfne base hfbase n ∈
      d.integerLayer (base + n) :=
  (stage facts hcenters U hU f hfU hfne base hfbase n).level_mem_layer

theorem level_ne_zero (n : ℕ) :
    level facts hcenters U hU f hfU hfne base hfbase n ≠ d.zeroLInf :=
  (stage facts hcenters U hU f hfU hfne base hfbase n).level_ne_zero

@[simp]
theorem stage_zero_target :
    (stage facts hcenters U hU f hfU hfne base hfbase 0).target = f := by
  simp [stage, coneConstructionStages]

@[simp]
theorem stage_succ_target (n : ℕ) :
    (stage facts hcenters U hU f hfU hfne base hfbase (n + 1)).target =
      level facts hcenters U hU f hfU hfne base hfbase n := by
  simp [stage, level, coneConstructionStages]

theorem level_zero_le_target :
    level facts hcenters U hU f hfU hfne base hfbase 0 ≤ f := by
  simpa [stage_zero_target] using
    (stage facts hcenters U hU f hfU hfne base hfbase 0).level_le_target

theorem level_succ_le (n : ℕ) :
    level facts hcenters U hU f hfU hfne base hfbase (n + 1) ≤
      level facts hcenters U hU f hfU hfne base hfbase n := by
  simpa [stage_succ_target] using
    (stage facts hcenters U hU f hfU hfne base hfbase (n + 1)).level_le_target

theorem level_antitone :
    Antitone (level facts hcenters U hU f hfU hfne base hfbase) := by
  exact antitone_nat_of_succ_le
    (level_succ_le facts hcenters U hU f hfU hfne base hfbase)

/-- The labelled finite approximation selected at level `n`. -/
def approximation (n : ℕ) :=
  (stage facts hcenters U hU f hfU hfne base hfbase n).approximation

/-- Every next-level height is strictly below the preceding envelope at its
center. -/
theorem child_height_lt_parent_envelope
    (n : ℕ)
    (t : (approximation facts hcenters U hU f hfU hfne base hfbase
      (n + 1)).Node) :
    ((approximation facts hcenters U hU f hfU hfne base hfbase
        (n + 1)).height t : ℝ≥0∞) <
      (approximation facts hcenters U hU f hfU hfne base hfbase n).envelope
        ((approximation facts hcenters U hU f hfU hfne base hfbase
          (n + 1)).center t) := by
  let Snext := stage facts hcenters U hU f hfU hfne base hfbase (n + 1)
  let Sprev := stage facts hcenters U hU f hfU hfne base hfbase n
  have hlt := Snext.approximation.height_lt_target t
  have htarget : Snext.target = Sprev.level :=
    stage_succ_target facts hcenters U hU f hfU hfne base hfbase n
  calc
    (Snext.approximation.height t : ℝ≥0∞)
        < Snext.target (Snext.approximation.center t) := hlt
    _ = Sprev.level (Snext.approximation.center t) :=
      congrArg (fun g : d.LInf ↦ g (Snext.approximation.center t)) htarget
    _ = Sprev.approximation.envelope
        (Snext.approximation.center t) := rfl

/-- Parent selection for the edge from level `n+1` to level `n`. -/
def parentSelection (n : ℕ) :=
  d.selectConeParents
    (forestSlope base n)
    (approximation facts hcenters U hU f hfU hfne base hfbase n).center
    (approximation facts hcenters U hU f hfU hfne base hfbase n).height
    (approximation facts hcenters U hU f hfU hfne base hfbase (n + 1)).center
    (approximation facts hcenters U hU f hfU hfne base hfbase (n + 1)).height
    (child_height_lt_parent_envelope facts hcenters U hU f hfU hfne
      base hfbase n)

/-- The finite-level forest underlying the recursive construction. -/
def forest : FiniteLevelForest where
  Node n :=
    (approximation facts hcenters U hU f hfU hfne base hfbase n).Node
  finite_node n := Finite.of_fintype _
  parent n :=
    (parentSelection facts hcenters U hU f hfU hfne base hfbase n).parent

/-- Every non-root node lies strictly below the root envelope. -/
theorem node_height_lt_root_envelope
    {n : ℕ} (hn : n ≠ 0)
    (s : (approximation facts hcenters U hU f hfU hfne base hfbase n).Node) :
    ((approximation facts hcenters U hU f hfU hfne base hfbase n).height s :
        ℝ≥0∞) <
      (approximation facts hcenters U hU f hfU hfne base hfbase 0).envelope
        ((approximation facts hcenters U hU f hfU hfne base hfbase n).center s) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  let Snext := stage facts hcenters U hU f hfU hfne base hfbase (k + 1)
  let Szero := stage facts hcenters U hU f hfU hfne base hfbase 0
  have hlt := Snext.approximation.height_lt_target s
  have htarget : Snext.target =
      level facts hcenters U hU f hfU hfne base hfbase k :=
    stage_succ_target facts hcenters U hU f hfU hfne base hfbase k
  have hdecrease :
      level facts hcenters U hU f hfU hfne base hfbase k ≤
        level facts hcenters U hU f hfU hfne base hfbase 0 :=
    level_antitone facts hcenters U hU f hfU hfne base hfbase
      (Nat.zero_le k)
  calc
    (Snext.approximation.height s : ℝ≥0∞)
        < Snext.target (Snext.approximation.center s) := hlt
    _ = level facts hcenters U hU f hfU hfne base hfbase k
        (Snext.approximation.center s) :=
      congrArg (fun g : d.LInf ↦ g (Snext.approximation.center s)) htarget
    _ ≤ level facts hcenters U hU f hfU hfne base hfbase 0
        (Snext.approximation.center s) :=
      hdecrease (Snext.approximation.center s)
    _ = Szero.approximation.envelope
        (Snext.approximation.center s) := rfl

/-- The concrete finite cone forest data extracted from the recursively
selected levels. -/
def coneForestData : d.FiniteConeForestData where
  forest := forest facts hcenters U hU f hfU hfne base hfbase
  nodeFintype n :=
    (approximation facts hcenters U hU f hfU hfne base hfbase n).nodeFintype
  node_nonempty n := by
    change Nonempty
      (approximation facts hcenters U hU f hfU hfne base hfbase n).Node
    infer_instance
  center n :=
    (approximation facts hcenters U hU f hfU hfne base hfbase n).center
  height n :=
    (approximation facts hcenters U hU f hfU hfne base hfbase n).height
  slope := forestSlope base
  slope_pos := forestSlope_pos base
  slope_mono := forestSlope_mono base
  parent_scaled_edist_lt n t :=
    (parentSelection facts hcenters U hU f hfU hfne base hfbase n).scaled_edist_lt t
  root_scaled_edist_lt n s hn := by
    have hbelow := node_height_lt_root_envelope
      facts hcenters U hU f hfU hfne base hfbase hn s
    obtain ⟨r, _hr, hcone⟩ :=
      d.exists_index_cone_gt_of_lt_finiteConeFamilyMax
        Finset.univ_nonempty hbelow
    refine ⟨r, ?_⟩
    exact lt_tsub_iff_right.mp (by simpa [cone] using hcone)

/-- The maximum root height. -/
def rootHeightBound : ℝ≥0 :=
  Finset.univ.sup' Finset.univ_nonempty
    (approximation facts hcenters U hU f hfU hfne base hfbase 0).height

theorem root_height_le_bound
    (r : (approximation facts hcenters U hU f hfU hfne base hfbase 0).Node) :
    (approximation facts hcenters U hU f hfU hfne base hfbase 0).height r ≤
      rootHeightBound facts hcenters U hU f hfU hfne base hfbase := by
  exact Finset.le_sup'
    (approximation facts hcenters U hU f hfU hfne base hfbase 0).height
    (Finset.mem_univ r)

theorem all_heights_le_bound
    (n : ℕ)
    (s : (coneForestData facts hcenters U hU f hfU hfne base hfbase).forest.Node n) :
    (coneForestData facts hcenters U hU f hfU hfne base hfbase).height n s ≤
      rootHeightBound facts hcenters U hU f hfU hfne base hfbase := by
  let C := coneForestData facts hcenters U hU f hfU hfne base hfbase
  by_cases hn : n = 0
  · subst n
    exact root_height_le_bound facts hcenters U hU f hfU hfne base hfbase s
  · obtain ⟨r, hr⟩ := C.root_scaled_edist_lt n s hn
    have hheight : C.height n s < C.height 0 r := by
      apply ENNReal.coe_lt_coe.mp
      exact (le_add_right le_rfl).trans_lt hr
    exact hheight.le.trans
      (root_height_le_bound facts hcenters U hU f hfU hfne base hfbase r)

/-- The full data structure consumed by the compact cone-forest
neighborhood theorem. -/
def neighborhoodData : ConeForestNeighborhoodData d f U where
  base := base
  C := coneForestData facts hcenters U hU f hfU hfne base hfbase
  slope_eq n := by rfl
  f_mem_base := hfbase
  level := level facts hcenters U hU f hfU hfne base hfbase
  level_eq_envelope n x := by
    simp [level, ConeConstructionStage.level,
      FiniteConeForestData.levelEnvelope, coneForestData, forest,
      approximation, FiniteConeApproximation.envelope]
  level_mem := level_mem_U facts hcenters U hU f hfU hfne base hfbase
  heightBound := rootHeightBound facts hcenters U hU f hfU hfne base hfbase
  height_le_bound :=
    all_heights_le_bound facts hcenters U hU f hfU hfne base hfbase
  root_height_lt r := by
    let Szero := stage facts hcenters U hU f hfU hfne base hfbase 0
    have hlt := Szero.approximation.height_lt_target r
    have htarget : Szero.target = f :=
      stage_zero_target facts hcenters U hU f hfU hfne base hfbase
    exact hlt.trans_eq
      (congrArg (fun g : d.LInf ↦ g (Szero.approximation.center r)) htarget)

end ConeConstruction

/-- Algebraic-case theorem after discharging the two standard cone facts.
All cone-forest recursion, compactness, and neighborhood arguments are
proved internally; only `StandardConeFacts` remains to be derived from
standardness. -/
theorem propertyD_of_standardConeFacts
    (d : QuasiMetric X)
    (hstandard : d.IsStandard)
    (facts : d.StandardConeFacts hstandard)
    (hcenters : d.HasEnoughCenterPoints)
    (hcomplete : d.IsYonedaComplete) :
    d.PropertyD := by
  apply propertyD_of_coneForestNeighborhoodData d hcomplete
  intro U hU f hfU hfne
  obtain ⟨base, hfbase⟩ := d.integerLayer_cover f
  exact ⟨ConeConstruction.neighborhoodData facts hcenters U hU
    f hfU hfne base hfbase⟩

end QuasiMetric
end LipschitzYonedaFinalTopology
