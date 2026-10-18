import Practice.DomainTheory.Papers.LipschitzYonedaFinalTopology.CauchyWeightedSubnet
import Practice.DomainTheory.Papers.LipschitzYonedaFinalTopology.LowerMapSuprema

/-!
# The formal-ball functor and Yoneda-continuous maps

For a map `f : X → Y`, `formalBallMap f` sends `(x,r)` to `(f x,r)`.
This file proves directly the formal-ball criterion used in Section 7 of
Goubault-Larrecq--Ng: Scott continuity of this map, together with
standardness of the target, yields nonexpansiveness, Yoneda continuity, and
continuity for the induced `d`-Scott topologies.

The proof is kept in the source-facing net language of this development.
In particular, preservation of `d`-limits is obtained from the canonical
Cauchy-weighted cofinal subnet, not postulated as an interface.
-/

set_option autoImplicit false
set_option linter.unnecessarySimpa false

open Set Function Topology
open scoped NNReal ENNReal Topology

noncomputable section

universe u

namespace LipschitzYonedaFinalTopology
namespace QuasiMetric

variable {X Y : Type u} (dX : QuasiMetric X) (dY : QuasiMetric Y)

/-- The order map on formal balls induced by a map of centers. -/
def formalBallMap (f : X → Y) (p : dX.FormalBall) : dY.FormalBall :=
  ⟨f p.center, p.radius⟩

@[simp]
theorem formalBallMap_center (f : X → Y) (p : dX.FormalBall) :
    (dX.formalBallMap dY f p).center = f p.center :=
  rfl

@[simp]
theorem formalBallMap_radius (f : X → Y) (p : dX.FormalBall) :
    (dX.formalBallMap dY f p).radius = p.radius :=
  rfl

/-- A nonexpansive map induces a monotone formal-ball map. -/
theorem formalBallMap_monotone_of_nonexpansive
    {f : X → Y} (hf : dX.IsNonexpansive dY f) :
    Monotone (dX.formalBallMap dY f) := by
  intro p q hpq
  rw [FormalBall.le_def] at hpq ⊢
  exact (add_le_add (hf p.center q.center) le_rfl).trans hpq

/-- Conversely, monotonicity on all finite-radius formal balls detects the
full extended nonexpansive inequality, including the case of infinite
distance. -/
theorem nonexpansive_of_formalBallMap_monotone
    {f : X → Y} (hf : Monotone (dX.formalBallMap dY f)) :
    dX.IsNonexpansive dY f := by
  intro x y
  by_contra hnot
  have hlt : dX.edist x y < dY.edist (f x) (f y) := lt_of_not_ge hnot
  obtain ⟨r, hxr, hry⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hlt
  have hball : (⟨x, r⟩ : dX.FormalBall) ≤ ⟨y, 0⟩ := by
    rw [FormalBall.le_def]
    simpa using hxr.le
  have himage := hf hball
  rw [FormalBall.le_def] at himage
  exact (not_le_of_gt hry) (by simpa using himage)

/-- The formal-ball map between the two Scott spaces. -/
def formalBallScottMap (f : X → Y) :
    WithScott dX.FormalBall → WithScott dY.FormalBall :=
  fun p ↦ WithScott.toScott
    (dX.formalBallMap dY f (WithScott.ofScott p))

/-- Order-theoretic Scott continuity is topological continuity on the
corresponding `WithScott` spaces. -/
theorem continuous_formalBallScottMap
    {f : X → Y}
    (hf : ScottContinuous (dX.formalBallMap dY f)) :
    Continuous (dX.formalBallScottMap dY f) := by
  rw [← Topology.IsScott.scottContinuousOn_iff_continuous
    (D := Set.univ) (fun _ _ _ ↦ Set.mem_univ _)]
  exact hf.scottContinuousOn

/-- Restricting a Scott-continuous formal-ball map to radius zero gives a
continuous map of the induced `d`-Scott spaces. -/
theorem isDScottContinuous_of_formalBallMap_scottContinuous
    {f : X → Y}
    (hf : ScottContinuous (dX.formalBallMap dY f)) :
    dX.IsDScottContinuous dY f := by
  unfold IsDScottContinuous dScottMap
  apply continuous_induced_rng.mpr
  have hzero : Continuous (fun x : dX.DScott ↦
      WithScott.toScott (⟨x, 0⟩ : dX.FormalBall)) :=
    continuous_induced_dom
  have hcomp := (dX.continuous_formalBallScottMap dY hf).comp hzero
  simpa [formalBallScottMap, formalBallMap, Function.comp_def] using hcomp

/-- Nonexpansive maps preserve the manuscript's one-sided Cauchy nets. -/
theorem IsNonexpansive.maps_cauchy
    {f : X → Y} (hf : dX.IsNonexpansive dY f)
    {ι : Type u} [Preorder ι] (x : ι → X)
    (hx : dX.IsCauchyNet x) :
    dY.IsCauchyNet (fun i ↦ f (x i)) := by
  intro ε hε
  obtain ⟨i₀, hi₀⟩ := hx ε hε
  refine ⟨i₀, ?_⟩
  intro i j hi hj
  exact (hf (x i) (x j)).trans_lt (hi₀ i j hi hj)

/-- The formal-ball criterion for Yoneda continuity.  This is the exact
direction needed for both arrows of the completion retract. -/
theorem yonedaContinuousMap_of_formalBallMap_scottContinuous
    (hstandardY : dY.IsStandard)
    {f : X → Y}
    (hf : ScottContinuous (dX.formalBallMap dY f)) :
    dX.IsYonedaContinuousMap dY f := by
  have hmono : Monotone (dX.formalBallMap dY f) :=
    hf.monotone
  have hnonexp : dX.IsNonexpansive dY f :=
    dX.nonexpansive_of_formalBallMap_monotone dY hmono
  constructor
  · intro ι _ x _hdir hx
    exact hnonexp.maps_cauchy dX dY x hx
  · intro ι _ x x₀ hdir hxCauchy hxLimit
    let W : dX.CauchyWeightedSubnet x :=
      CauchyWeightedSubnet.ofCauchy dX x hdir hxCauchy
    let p : W.Index → dX.FormalBall := fun k ↦
      ⟨x (W.map k), W.radius k⟩
    have hpLUB : IsLUB (Set.range p)
        (⟨x₀, 0⟩ : dX.FormalBall) := by
      simpa only [p] using
        CauchyWeightedSubnet.formalBall_isLUB dX W hxCauchy hxLimit
    have hpRangeNonempty : (Set.range p).Nonempty := by
      let k : W.Index := Classical.choice W.directed.1
      exact ⟨p k, ⟨k, rfl⟩⟩
    have hpRangeDirected : DirectedOn (· ≤ ·) (Set.range p) := by
      intro a ha b hb
      obtain ⟨i, rfl⟩ := ha
      obtain ⟨j, rfl⟩ := hb
      obtain ⟨k, hik, hjk⟩ := W.directed.2 i j
      exact ⟨p k, ⟨k, rfl⟩,
        W.formalBall_monotone hik,
        W.formalBall_monotone hjk⟩
    have himageLUB := hf hpRangeNonempty hpRangeDirected hpLUB
    have himageRange :
        (dX.formalBallMap dY f) '' Set.range p =
          Set.range (fun k : W.Index ↦
            (⟨f (x (W.map k)), W.radius k⟩ : dY.FormalBall)) := by
      ext q
      constructor
      · rintro ⟨_, ⟨k, rfl⟩, rfl⟩
        exact ⟨k, rfl⟩
      · rintro ⟨k, rfl⟩
        exact ⟨p k, ⟨k, rfl⟩, rfl⟩
    have hsubLUB : IsLUB
        (Set.range (fun k : W.Index ↦
          (⟨f (x (W.map k)), W.radius k⟩ : dY.FormalBall)))
        (⟨f x₀, 0⟩ : dY.FormalBall) := by
      rw [← himageRange]
      simpa [formalBallMap] using himageLUB
    have hsubLimit : dY.IsDLimit
        (fun k : W.Index ↦ f (x (W.map k))) (f x₀) :=
      IsStandard.center_isDLimit_of_zeroRadius_isLUB dY hstandardY
        (fun k : W.Index ↦
          (⟨f (x (W.map k)), W.radius k⟩ : dY.FormalBall))
        W.directed
        (fun _ _ h ↦ hmono (W.formalBall_monotone h))
        (f x₀) hsubLUB
    have himageCauchy : dY.IsCauchyNet (fun i ↦ f (x i)) :=
      hnonexp.maps_cauchy dX dY x hxCauchy
    intro y
    calc
      dY.edist (f x₀) y =
          netLimsup (fun k : W.Index ↦
            dY.edist (f (x (W.map k))) y) := hsubLimit y
      _ = netLimsup (fun i : ι ↦ dY.edist (f (x i)) y) :=
        netLimsup_edist_comp_eq dY (fun i ↦ f (x i)) W.directed
          himageCauchy W.map W.map_monotone W.map_cofinal y

end QuasiMetric
end LipschitzYonedaFinalTopology
