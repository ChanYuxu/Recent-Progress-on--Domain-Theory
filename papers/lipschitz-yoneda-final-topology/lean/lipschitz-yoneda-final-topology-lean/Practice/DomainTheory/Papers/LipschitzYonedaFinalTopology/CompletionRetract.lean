import Practice.DomainTheory.Papers.LipschitzYonedaFinalTopology.FormalBallWayBelow
import Practice.DomainTheory.Papers.LipschitzYonedaFinalTopology.AlgebraicTheorem

/-!
# The continuous-space retract from the formal-ball completion

This file formalizes Lemmas 7.5--7.7 and Proposition 7.8 of
Goubault-Larrecq--Ng.  For a continuous Yoneda-complete quasi-metric space
`X`, the section sends `x` to the rounded ideal `↓↓(x,0)`, while the
projection sends an aperture-zero ideal to the center of its formal-ball
supremum.  Both maps are proved nonexpansive, Yoneda-continuous, and
continuous for the induced `d`-Scott topologies.

No completion universal property is assumed: the ideal supremum and all
map-continuity claims are constructed from the definitions in this paper.
-/

set_option autoImplicit false
set_option linter.unnecessarySimpa false

open Set Function Filter Topology
open scoped NNReal ENNReal Topology

noncomputable section

universe u

namespace LipschitzYonedaFinalTopology
namespace QuasiMetric

variable {X : Type u} (d : QuasiMetric X)

namespace RoundedIdeal

/-- A rounded ideal, ordered by the formal-ball order, is a directed index
type. -/
theorem subtype_isDirectedIndex (A : d.RoundedIdeal) :
    IsDirectedIndex {p // p ∈ A} := by
  constructor
  · exact (RoundedIdeal.nonempty d A).to_subtype
  · intro p q
    rcases RoundedIdeal.directed d A p.2 q.2 with
      ⟨r, hrA, hpr, hqr⟩
    exact ⟨⟨r, hrA⟩,
      FormalBall.le_of_strictBelow d hpr,
      FormalBall.le_of_strictBelow d hqr⟩

/-- After removing the aperture, radii in a rounded ideal become
arbitrarily small on a tail. -/
theorem unshift_aperture_radius_eventually_lt
    (A : d.RoundedIdeal) :
    let R := apertureRadius d A
    let I := {p // p ∈ A}
    ∀ ε : ℝ≥0, 0 < ε →
      ∃ i : I, ∀ j : I, i ≤ j →
        (FormalBall.unshift d R j.1).radius < ε := by
  intro R I ε hε
  have hapLt : aperture d A < ((R + ε : ℝ≥0) : ℝ≥0∞) := by
    rw [← coe_apertureRadius d A, ENNReal.coe_lt_coe]
    exact lt_add_of_pos_right R hε
  unfold aperture at hapLt
  rcases iInf_lt_iff.mp hapLt with ⟨i, hi⟩
  have hiNN : i.1.radius < R + ε := ENNReal.coe_lt_coe.mp hi
  have hRi : R ≤ i.1.radius := apertureRadius_le_radius d A i.2
  have hsmall : i.1.radius - R < ε :=
    (tsub_lt_iff_left hRi).2 (by simpa [add_comm] using hiNN)
  refine ⟨i, ?_⟩
  intro j hij
  have hrad : j.1.radius ≤ i.1.radius :=
    FormalBall.radius_le_of_le d hij
  exact (tsub_le_tsub_right hrad R).trans_lt hsmall

/-- Centers of an aperture-normalized rounded ideal form a Cauchy net. -/
theorem unshift_aperture_centers_isCauchy
    (A : d.RoundedIdeal) :
    let R := apertureRadius d A
    let I := {p // p ∈ A}
    d.IsCauchyNet (fun i : I ↦
      (FormalBall.unshift d R i.1).center) := by
  intro R I ε hε
  obtain ⟨i₀, hi₀⟩ :=
    unshift_aperture_radius_eventually_lt d A ε hε
  refine ⟨i₀, ?_⟩
  intro i j hi₀i hij
  have hRi : R ≤ i.1.radius := apertureRadius_le_radius d A i.2
  have hRj : R ≤ j.1.radius := apertureRadius_le_radius d A j.2
  have hijUnshift : FormalBall.unshift d R i.1 ≤
      FormalBall.unshift d R j.1 := by
    apply (FormalBall.shift_le_shift_iff d R _ _).1
    simpa [FormalBall.shift_unshift d hRi,
      FormalBall.shift_unshift d hRj] using hij
  have hdist : d.edist i.1.center j.1.center ≤
      ((FormalBall.unshift d R i.1).radius : ℝ≥0∞) :=
    (le_add_right le_rfl).trans hijUnshift
  exact hdist.trans_lt
    (ENNReal.coe_lt_coe.mpr (hi₀ i hi₀i))

/-- Every rounded ideal has a formal-ball supremum whose radius is exactly
its aperture. -/
theorem exists_center_isLUB
    (hstandard : d.IsStandard)
    (hcomplete : d.IsYonedaComplete)
    (A : d.RoundedIdeal) :
    ∃ x : X, IsLUB (A : Set d.FormalBall)
      (⟨x, apertureRadius d A⟩ : d.FormalBall) := by
  let R := apertureRadius d A
  let I := {p // p ∈ A}
  let b : I → d.FormalBall := fun i ↦ i.1
  let b0 : I → d.FormalBall := fun i ↦ FormalBall.unshift d R i.1
  have hIdir : IsDirectedIndex I := subtype_isDirectedIndex d A
  have hbmono : Monotone b := fun _ _ hij ↦ hij
  have hb0mono : Monotone b0 := by
    intro i j hij
    have hRi : R ≤ i.1.radius := apertureRadius_le_radius d A i.2
    have hRj : R ≤ j.1.radius := apertureRadius_le_radius d A j.2
    apply (FormalBall.shift_le_shift_iff d R _ _).1
    simpa [b0, FormalBall.shift_unshift d hRi,
      FormalBall.shift_unshift d hRj] using hij
  have hb0small : ∀ ε : ℝ≥0, 0 < ε →
      ∃ i : I, ∀ j : I, i ≤ j → (b0 j).radius < ε := by
    simpa [b0, R, I] using
      unshift_aperture_radius_eventually_lt d A
  have hb0Cauchy : d.IsCauchyNet (fun i : I ↦ (b0 i).center) := by
    simpa [b0, R, I] using unshift_aperture_centers_isCauchy d A
  obtain ⟨x, hxLimit⟩ := hcomplete I
    (fun i ↦ (b0 i).center) hIdir hb0Cauchy
  have hb0LUB : IsLUB (Set.range b0)
      (⟨x, 0⟩ : d.FormalBall) :=
    zeroRadius_isLUB_of_center_isDLimit d b0 hIdir hb0mono
      hb0small x hxLimit
  have hshiftLUB := IsStandard.shift_isLUB d hstandard b0 hIdir
    hb0mono hb0LUB R
  have hshiftRange :
      Set.range (fun i : I ↦ FormalBall.shift d R (b0 i)) =
        (A : Set d.FormalBall) := by
    ext p
    constructor
    · rintro ⟨i, rfl⟩
      have hRi : R ≤ i.1.radius := apertureRadius_le_radius d A i.2
      simpa [b0, FormalBall.shift_unshift d hRi] using i.2
    · intro hp
      let i : I := ⟨p, hp⟩
      have hRi : R ≤ p.radius := apertureRadius_le_radius d A hp
      exact ⟨i, by simp [i, b0, FormalBall.shift_unshift d hRi]⟩
  refine ⟨x, ?_⟩
  rw [← hshiftRange]
  simpa [FormalBall.shift] using hshiftLUB

/-- The selected center of the supremum of a rounded ideal. -/
def supCenter
    (hstandard : d.IsStandard)
    (hcomplete : d.IsYonedaComplete)
    (A : d.RoundedIdeal) : X :=
  Classical.choose (exists_center_isLUB d hstandard hcomplete A)

/-- The selected formal-ball supremum. -/
def formalBallSup
    (hstandard : d.IsStandard)
    (hcomplete : d.IsYonedaComplete)
    (A : d.RoundedIdeal) : d.FormalBall :=
  ⟨supCenter d hstandard hcomplete A, apertureRadius d A⟩

theorem formalBallSup_isLUB
    (hstandard : d.IsStandard)
    (hcomplete : d.IsYonedaComplete)
    (A : d.RoundedIdeal) :
    IsLUB (A : Set d.FormalBall)
      (formalBallSup d hstandard hcomplete A) :=
  Classical.choose_spec (exists_center_isLUB d hstandard hcomplete A)

/-- Inclusion of ideals is sent to the formal-ball order. -/
theorem formalBallSup_mono_direct
    (hstandard : d.IsStandard)
    (hcomplete : d.IsYonedaComplete)
    {A B : d.RoundedIdeal} (hAB : A ≤ B) :
    formalBallSup d hstandard hcomplete A ≤
      formalBallSup d hstandard hcomplete B := by
  apply (formalBallSup_isLUB d hstandard hcomplete A).2
  intro p hpA
  exact (formalBallSup_isLUB d hstandard hcomplete B).1 (hAB hpA)

/-- Taking the formal-ball supremum commutes with translation. -/
theorem formalBallSup_shift
    (hstandard : d.IsStandard)
    (hcomplete : d.IsYonedaComplete)
    (t : ℝ≥0) (A : d.RoundedIdeal) :
    formalBallSup d hstandard hcomplete (shift d t A) =
      FormalBall.shift d t (formalBallSup d hstandard hcomplete A) := by
  let I := {p // p ∈ A}
  let b : I → d.FormalBall := fun i ↦ i.1
  have hIdir : IsDirectedIndex I := subtype_isDirectedIndex d A
  have hbmono : Monotone b := fun _ _ hij ↦ hij
  have hbLUB : IsLUB (Set.range b)
      (formalBallSup d hstandard hcomplete A) := by
    simpa [I, b] using formalBallSup_isLUB d hstandard hcomplete A
  have hshiftLUB := IsStandard.shift_isLUB d hstandard b hIdir
    hbmono hbLUB t
  have hshiftRange :
      Set.range (fun i : I ↦ FormalBall.shift d t (b i)) =
        (shift d t A : Set d.FormalBall) := by
    ext p
    constructor
    · rintro ⟨i, rfl⟩
      exact shift_mem_shift d t A i.2
    · intro hp
      let i : I := ⟨FormalBall.unshift d t p, hp.2⟩
      exact ⟨i, by simpa [i, b, FormalBall.shift_unshift d hp.1]⟩
  have htarget : IsLUB (shift d t A : Set d.FormalBall)
      (FormalBall.shift d t (formalBallSup d hstandard hcomplete A)) := by
    rw [← hshiftRange]
    exact hshiftLUB
  exact (formalBallSup_isLUB d hstandard hcomplete
    (shift d t A)).unique htarget

/-- Supremum of rounded ideals is Scott-continuous. -/
theorem formalBallSup_scottContinuous
    (hstandard : d.IsStandard)
    (hcomplete : d.IsYonedaComplete) :
    ScottContinuous (formalBallSup d hstandard hcomplete) := by
  intro S hSne hSdir A hSA
  have hU := directedUnion_isLUB d S hSne hSdir
  have hAU : A = directedUnion d S hSne hSdir := hSA.unique hU
  constructor
  · rintro _ ⟨B, hBS, rfl⟩
    exact formalBallSup_mono_direct d hstandard hcomplete (hSA.1 hBS)
  · intro q hq
    apply (formalBallSup_isLUB d hstandard hcomplete A).2
    intro p hpA
    rw [hAU] at hpA
    rcases hpA with ⟨B, hBS, hpB⟩
    exact ((formalBallSup_isLUB d hstandard hcomplete B).1 hpB).trans
      (hq ⟨B, hBS, rfl⟩)

end RoundedIdeal

namespace Completion

variable (hcontinuous : d.FormalBallPosetContinuous)

/-- The way-below section `η⁰_S(x)=↓↓(x,0)`. -/
def wayBelowPoint (hstandard : d.IsStandard) (x : X) : d.Completion :=
  ⟨RoundedIdeal.wayBelowIdeal d hcontinuous
      (⟨x, 0⟩ : d.FormalBall),
    RoundedIdeal.aperture_wayBelowIdeal_zero d hstandard hcontinuous x⟩

/-- The `d-lim` projection from the completion. -/
def dLimitProjection
    (hstandard : d.IsStandard)
    (hcomplete : d.IsYonedaComplete) : d.Completion → X :=
  fun A ↦ RoundedIdeal.supCenter d hstandard hcomplete A.1

theorem apertureRadius_completion (A : d.Completion) :
    RoundedIdeal.apertureRadius d A.1 = 0 := by
  apply ENNReal.coe_injective
  rw [RoundedIdeal.coe_apertureRadius, A.2]
  rfl

/-- Under `σ`, the formal-ball map of the section is exactly
`q ↦ ↓↓q`. -/
theorem sigma_formalBallMap_wayBelowPoint
    (hstandard : d.IsStandard) (p : d.FormalBall) :
    sigma d (d.formalBallMap (quasiMetric d)
      (wayBelowPoint d hcontinuous hstandard) p) =
      RoundedIdeal.wayBelowIdeal d hcontinuous p := by
  cases p with
  | mk x r =>
      change RoundedIdeal.shift d r
          (RoundedIdeal.wayBelowIdeal d hcontinuous
            (⟨x, 0⟩ : d.FormalBall)) =
        RoundedIdeal.wayBelowIdeal d hcontinuous
          (⟨x, r⟩ : d.FormalBall)
      simpa [FormalBall.shift] using
        RoundedIdeal.shift_wayBelowIdeal d hstandard hcontinuous r
          (⟨x, 0⟩ : d.FormalBall)

private theorem sigmaInv_scottContinuous :
    ScottContinuous (sigmaInv d) := by
  intro S hSne hSdir A hSA
  change IsLUB ((sigmaOrderIso d).symm '' S)
    ((sigmaOrderIso d).symm A)
  constructor
  · intro p hp
    rcases hp with ⟨B, hBS, rfl⟩
    exact (sigmaOrderIso d).symm.monotone (hSA.1 hBS)
  · intro p hp
    have hAEp : A ≤ (sigmaOrderIso d) p := by
      apply hSA.2
      intro B hBS
      have hpre : (sigmaOrderIso d).symm B ≤ p := hp ⟨B, hBS, rfl⟩
      simpa using (sigmaOrderIso d).monotone hpre
    simpa using (sigmaOrderIso d).symm.monotone hAEp

/-- The section's formal-ball map is Scott-continuous. -/
theorem wayBelowPoint_formalBallMap_scottContinuous
    (hstandard : d.IsStandard) :
    ScottContinuous (d.formalBallMap (quasiMetric d)
      (wayBelowPoint d hcontinuous hstandard)) := by
  have hcomp :=
    (RoundedIdeal.wayBelowIdeal_scottContinuous d hcontinuous).comp
      (sigmaInv_scottContinuous d)
  have heq : d.formalBallMap (quasiMetric d)
        (wayBelowPoint d hcontinuous hstandard) =
      sigmaInv d ∘ RoundedIdeal.wayBelowIdeal d hcontinuous := by
    funext p
    apply (sigmaOrderIso d).injective
    change sigma d (d.formalBallMap (quasiMetric d)
        (wayBelowPoint d hcontinuous hstandard) p) =
      sigma d (sigmaInv d
        (RoundedIdeal.wayBelowIdeal d hcontinuous p))
    rw [sigma_sigmaInv]
    exact sigma_formalBallMap_wayBelowPoint d hcontinuous hstandard p
  rw [heq]
  exact hcomp

/-- The formal-ball map of `d-lim`, after `σ`, is the ideal-supremum map. -/
theorem formalBallMap_dLimitProjection_eq_formalBallSup_sigma
    (hstandard : d.IsStandard)
    (hcomplete : d.IsYonedaComplete)
    (p : Ball d) :
    (quasiMetric d).formalBallMap d
        (dLimitProjection d hstandard hcomplete) p =
      RoundedIdeal.formalBallSup d hstandard hcomplete (sigma d p) := by
  rcases p with ⟨A, r⟩
  have hbase : RoundedIdeal.formalBallSup d hstandard hcomplete A.1 =
      (⟨dLimitProjection d hstandard hcomplete A, 0⟩ : d.FormalBall) := by
    rw [FormalBall.mk.injEq]
    exact ⟨rfl, apertureRadius_completion d A⟩
  change (⟨dLimitProjection d hstandard hcomplete A, r⟩ : d.FormalBall) =
    RoundedIdeal.formalBallSup d hstandard hcomplete
      (RoundedIdeal.shift d r A.1)
  rw [RoundedIdeal.formalBallSup_shift d hstandard hcomplete r A.1,
    hbase]
  simp [FormalBall.shift]

private theorem sigma_scottContinuous : ScottContinuous (sigma d) := by
  intro S hSne hSdir p hp
  change IsLUB ((sigmaOrderIso d) '' S) ((sigmaOrderIso d) p)
  constructor
  · intro A hA
    rcases hA with ⟨q, hqS, rfl⟩
    exact (sigmaOrderIso d).monotone (hp.1 hqS)
  · intro A hA
    rw [← (sigmaOrderIso d).apply_symm_apply A]
    apply (sigmaOrderIso d).monotone
    apply hp.2
    intro q hqS
    have hq := (sigmaOrderIso d).symm.monotone (hA ⟨q, hqS, rfl⟩)
    rw [(sigmaOrderIso d).symm_apply_apply] at hq
    exact hq

/-- The projection's formal-ball map is Scott-continuous. -/
theorem dLimitProjection_formalBallMap_scottContinuous
    (hstandard : d.IsStandard)
    (hcomplete : d.IsYonedaComplete) :
    ScottContinuous ((quasiMetric d).formalBallMap d
      (dLimitProjection d hstandard hcomplete)) := by
  have hcomp :=
    (sigma_scottContinuous d).comp
      (RoundedIdeal.formalBallSup_scottContinuous d hstandard hcomplete)
  have heq : (quasiMetric d).formalBallMap d
        (dLimitProjection d hstandard hcomplete) =
      RoundedIdeal.formalBallSup d hstandard hcomplete ∘ sigma d := by
    funext p
    exact formalBallMap_dLimitProjection_eq_formalBallSup_sigma d
      hstandard hcomplete p
  rw [heq]
  exact hcomp

/-- The projection is a left inverse of the way-below section. -/
theorem dLimitProjection_wayBelowPoint
    (hstandard : d.IsStandard)
    (hcomplete : d.IsYonedaComplete)
    (x : X) :
    dLimitProjection d hstandard hcomplete
      (wayBelowPoint d hcontinuous hstandard x) = x := by
  let A := RoundedIdeal.wayBelowIdeal d hcontinuous
    (⟨x, 0⟩ : d.FormalBall)
  have hsupA := RoundedIdeal.formalBallSup_isLUB d hstandard hcomplete A
  have hsupX : IsLUB (A : Set d.FormalBall)
      (⟨x, 0⟩ : d.FormalBall) := by
    simpa [A, RoundedIdeal.wayBelowIdeal] using
      (hcontinuous (⟨x, 0⟩ : d.FormalBall)).2.2
  have heq := hsupA.unique hsupX
  exact congrArg FormalBall.center heq

/-- Proposition 7.8: every continuous Yoneda-complete quasi-metric space
is a Yoneda- and `d`-Scott-continuous retract of its algebraic completion.
-/
def yonedaDScottRetract
    (hcontinuousSpace : d.IsContinuous)
    (hcomplete : d.IsYonedaComplete) :
    d.YonedaDScottRetract (quasiMetric d) := by
  let hs := hcontinuousSpace.1
  let hc := hcontinuousSpace.2
  let e := wayBelowPoint d hc hs
  let r := dLimitProjection d hs hcomplete
  have heScott : ScottContinuous
      (d.formalBallMap (quasiMetric d) e) :=
    wayBelowPoint_formalBallMap_scottContinuous d hc hs
  have hrScott : ScottContinuous
      ((quasiMetric d).formalBallMap d r) :=
    dLimitProjection_formalBallMap_scottContinuous d hs hcomplete
  exact
    { embedding := e
      projection := r
      embedding_nonexpansive :=
        d.nonexpansive_of_formalBallMap_monotone (quasiMetric d)
          heScott.monotone
      projection_nonexpansive :=
        (quasiMetric d).nonexpansive_of_formalBallMap_monotone d
          hrScott.monotone
      embedding_yoneda :=
        d.yonedaContinuousMap_of_formalBallMap_scottContinuous
          (quasiMetric d) (Completion.isStandard d) heScott
      projection_yoneda :=
        (quasiMetric d).yonedaContinuousMap_of_formalBallMap_scottContinuous
          d hs hrScott
      embedding_dScott :=
        d.isDScottContinuous_of_formalBallMap_scottContinuous
          (quasiMetric d) heScott
      projection_dScott :=
        (quasiMetric d).isDScottContinuous_of_formalBallMap_scottContinuous
          d hrScott
      leftInverse := fun x ↦ dLimitProjection_wayBelowPoint d hc hs hcomplete x }

end Completion
end QuasiMetric
end LipschitzYonedaFinalTopology
