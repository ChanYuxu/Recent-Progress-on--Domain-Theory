import Practice.DomainTheory.Papers.LipschitzYonedaFinalTopology.RoundedIdealDomain

/-!
# Center points of the formal-ball completion

The zero-radius principal ideals `⇓(x,0)` are proved to be center points of
`S(X,d)`, and their formal-ball neighborhoods form a Scott basis.  This is
the remaining analytic content of algebraicity of the completion.
-/

set_option autoImplicit false
set_option linter.unnecessarySimpa false

open Set Function Topology
open scoped NNReal ENNReal Topology

noncomputable section

universe u

namespace LipschitzYonedaFinalTopology
namespace QuasiMetric

variable {X : Type u} (d : QuasiMetric X)

namespace RoundedIdeal

/-- Principal ideals at zero-radius balls have aperture zero. -/
theorem aperture_principal_zero (x : X) :
    aperture d (principal d (⟨x, 0⟩ : d.FormalBall)) = 0 := by
  apply le_antisymm
  · apply ENNReal.le_of_forall_pos_le_add
    intro ε hε _hfinite
    let p : d.FormalBall := ⟨x, ε⟩
    have hp : p ∈ principal d (⟨x, 0⟩ : d.FormalBall) := by
      change d.edist x x + (0 : ℝ≥0∞) < (ε : ℝ≥0∞)
      simpa [d.edist_self] using ENNReal.coe_pos.2 hε
    simpa [p] using aperture_le_radius d
      (principal d (⟨x, 0⟩ : d.FormalBall)) hp
  · exact zero_le _

/-- Translation commutes with principal rounded ideals. -/
theorem shift_principal (t : ℝ≥0) (q : d.FormalBall) :
    shift d t (principal d q) =
      principal d (FormalBall.shift d t q) := by
  apply RoundedIdeal.ext
  intro p
  constructor
  · intro hp
    have hbase : FormalBall.StrictBelow d
        (FormalBall.unshift d t p) q := hp.2
    have hshift := (FormalBall.strictBelow_shift_iff d t
      (FormalBall.unshift d t p) q).2 hbase
    simpa [FormalBall.shift_unshift d hp.1] using hshift
  · intro hp
    have hp_le : p ≤ FormalBall.shift d t q :=
      FormalBall.le_of_strictBelow d hp
    have htp : t ≤ p.radius := by
      have hrad := FormalBall.radius_le_of_le d hp_le
      exact (le_add_left le_rfl).trans hrad
    refine ⟨htp, ?_⟩
    apply (FormalBall.strictBelow_shift_iff d t
      (FormalBall.unshift d t p) q).mp
    simpa [FormalBall.shift_unshift d htp] using hp

end RoundedIdeal

namespace Completion

/-- The completion point corresponding to `x`. -/
def principalPoint (x : X) : d.Completion :=
  ⟨RoundedIdeal.principal d (⟨x, 0⟩ : d.FormalBall),
    RoundedIdeal.aperture_principal_zero d x⟩

/-- Scott-space form of `sigma`. -/
def sigmaScott (p : WithScott (Ball d)) : WithScott d.RoundedIdeal :=
  WithScott.toScott (sigma d (WithScott.ofScott p))

/-- Scott-space form of the inverse of `sigma`. -/
def sigmaInvScott (A : WithScott d.RoundedIdeal) : WithScott (Ball d) :=
  WithScott.toScott (sigmaInv d (WithScott.ofScott A))

@[simp]
theorem sigmaInvScott_sigmaScott (p : WithScott (Ball d)) :
    sigmaInvScott d (sigmaScott d p) = p := by
  apply WithScott.ofScott.injective
  exact sigmaInv_sigma d (WithScott.ofScott p)

@[simp]
theorem sigmaScott_sigmaInvScott (A : WithScott d.RoundedIdeal) :
    sigmaScott d (sigmaInvScott d A) = A := by
  apply WithScott.ofScott.injective
  exact sigma_sigmaInv d (WithScott.ofScott A)

theorem continuous_sigmaScott : Continuous (sigmaScott d) := by
  rw [← Topology.IsScott.scottContinuousOn_iff_continuous
    (D := Set.univ) (by simp)]
  rw [scottContinuousOn_univ]
  intro S hne hdir p hp
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
    have hq := (sigmaOrderIso d).symm.monotone
      (hA ⟨q, hqS, rfl⟩)
    rw [(sigmaOrderIso d).symm_apply_apply] at hq
    exact hq

theorem continuous_sigmaInvScott : Continuous (sigmaInvScott d) := by
  rw [← Topology.IsScott.scottContinuousOn_iff_continuous
    (D := Set.univ) (by simp)]
  rw [scottContinuousOn_univ]
  intro S hne hdir A hA
  change IsLUB ((sigmaOrderIso d).symm '' S)
    ((sigmaOrderIso d).symm A)
  constructor
  · intro p hp
    rcases hp with ⟨B, hBS, rfl⟩
    exact (sigmaOrderIso d).symm.monotone (hA.1 hBS)
  · intro p hp
    have hAEp : A ≤ (sigmaOrderIso d) p := by
      apply hA.2
      intro B hBS
      have hpre : (sigmaOrderIso d).symm B ≤ p :=
        hp ⟨B, hBS, rfl⟩
      simpa using (sigmaOrderIso d).monotone hpre
    simpa using (sigmaOrderIso d).symm.monotone hAEp

/-- The basic Scott-open set of ideals containing a fixed formal ball. -/
def contains (p : d.FormalBall) : Set (WithScott d.RoundedIdeal) :=
  {A | p ∈ (WithScott.ofScott A : d.RoundedIdeal)}

theorem isOpen_contains (p : d.FormalBall) : IsOpen (contains d p) := by
  rw [Topology.IsScott.isOpen_iff_isUpperSet_and_dirSupInaccOn
    (D := Set.univ)]
  constructor
  · intro A B hAB hp
    exact hAB hp
  · intro S _hSuniv hSne hSdir A hSA hpA
    let U := RoundedIdeal.directedUnion d S hSne hSdir
    have hU : IsLUB S U :=
      RoundedIdeal.directedUnion_isLUB d S hSne hSdir
    have hAleU : A ≤ U := hSA.2 hU.1
    have hpU : p ∈ U := hAleU hpA
    rcases hpU with ⟨I, hIS, hpI⟩
    exact ⟨I, hIS, hpI⟩

/-- Formal-ball quasi-distance from a member of `⇓(x,0)` is bounded by
the distance from `(x,0)`. -/
theorem formalBallEdist_le_from_principal
    (x : X) {p q : d.FormalBall}
    (hp : p ∈ RoundedIdeal.principal d (⟨x, 0⟩ : d.FormalBall)) :
    d.formalBallEdist p q ≤
      d.formalBallEdist (⟨x, 0⟩ : d.FormalBall) q := by
  have hpx : p ≤ (⟨x, 0⟩ : d.FormalBall) :=
    FormalBall.le_of_strictBelow d hp
  have hzero : d.formalBallEdist p (⟨x, 0⟩ : d.FormalBall) = 0 :=
    (formalBallEdist_eq_zero_iff d _ _).2 hpx
  exact (FormalBall.formalBallEdist_triangle d p
    (⟨x, 0⟩ : d.FormalBall) q).trans_eq (by simp [hzero])

/-- The metric open-ball condition at a principal completion point is
exactly membership of one formal ball in the translated ideal. -/
theorem formalBallOpen_iff_contains
    (x : X) (A : d.Completion) (r ε : ℝ≥0) :
    (quasiMetric d).formalBallEdist
        (⟨principalPoint d x, 0⟩ : Ball d) ⟨A, r⟩ <
          (ε : ℝ≥0∞) ↔
      (⟨x, ε⟩ : d.FormalBall) ∈ RoundedIdeal.shift d r A.1 := by
  unfold formalBallEdist
  change (RoundedIdeal.hausdorffEdist d
      (RoundedIdeal.principal d (⟨x, 0⟩ : d.FormalBall)) A.1 +
        (r : ℝ≥0∞)) - 0 < (ε : ℝ≥0∞) ↔ _
  rw [tsub_zero]
  constructor
  · intro hdist
    have hrεE : (r : ℝ≥0∞) < (ε : ℝ≥0∞) :=
      (le_add_left le_rfl).trans_lt hdist
    have hrε : r ≤ ε := (ENNReal.coe_lt_coe.mp hrεE).le
    have hHtarget :
        RoundedIdeal.hausdorffEdist d
            (RoundedIdeal.principal d (⟨x, 0⟩ : d.FormalBall)) A.1 <
          ((ε - r : ℝ≥0) : ℝ≥0∞) := by
      have hsub := AddLECancellable.lt_tsub_of_add_lt_right
        (ENNReal.cancel_of_ne ENNReal.coe_ne_top) hdist
      simpa using hsub
    obtain ⟨γ, hγpos, hHγ⟩ :=
      ENNReal.lt_iff_exists_add_pos_lt.mp hHtarget
    let δ : ℝ≥0 := γ / 2
    have hδpos : 0 < δ := half_pos hγpos
    let p : d.FormalBall := ⟨x, δ⟩
    have hpPrincipal :
        p ∈ RoundedIdeal.principal d (⟨x, 0⟩ : d.FormalBall) := by
      change d.edist x x + (0 : ℝ≥0∞) < (δ : ℝ≥0∞)
      simpa [d.edist_self] using ENNReal.coe_pos.2 hδpos
    let pP : (RoundedIdeal.principal d
        (⟨x, 0⟩ : d.FormalBall) : Set d.FormalBall) :=
      ⟨p, hpPrincipal⟩
    have hpoint :
        (⨅ q : (A.1 : Set d.FormalBall),
          d.formalBallEdist p q.1) ≤
        RoundedIdeal.hausdorffEdist d
          (RoundedIdeal.principal d (⟨x, 0⟩ : d.FormalBall)) A.1 :=
      le_iSup (fun a : (RoundedIdeal.principal d
        (⟨x, 0⟩ : d.FormalBall) : Set d.FormalBall) ↦
          ⨅ q : (A.1 : Set d.FormalBall),
            d.formalBallEdist a.1 q.1) pP
    have hHfinite : RoundedIdeal.hausdorffEdist d
        (RoundedIdeal.principal d (⟨x, 0⟩ : d.FormalBall)) A.1 ≠ ∞ :=
      ne_top_of_lt hHtarget
    have hHlt : RoundedIdeal.hausdorffEdist d
          (RoundedIdeal.principal d (⟨x, 0⟩ : d.FormalBall)) A.1 <
        RoundedIdeal.hausdorffEdist d
            (RoundedIdeal.principal d (⟨x, 0⟩ : d.FormalBall)) A.1 +
          (δ : ℝ≥0∞) := by
      have h := (ENNReal.add_lt_add_iff_left hHfinite).2
        (ENNReal.coe_pos.2 hδpos)
      simpa using h
    have hinfLt :
        (⨅ q : (A.1 : Set d.FormalBall),
          d.formalBallEdist p q.1) <
        RoundedIdeal.hausdorffEdist d
            (RoundedIdeal.principal d (⟨x, 0⟩ : d.FormalBall)) A.1 +
          (δ : ℝ≥0∞) := hpoint.trans_lt hHlt
    rcases iInf_lt_iff.mp hinfLt with ⟨q, hq⟩
    have hraw : d.edist x q.1.center + (q.1.radius : ℝ≥0∞) <
        (δ : ℝ≥0∞) +
          (RoundedIdeal.hausdorffEdist d
              (RoundedIdeal.principal d
                (⟨x, 0⟩ : d.FormalBall)) A.1 + (δ : ℝ≥0∞)) := by
      exact AddLECancellable.lt_add_of_tsub_lt_left
        (ENNReal.cancel_of_ne ENNReal.coe_ne_top) (by
          simpa [p, formalBallEdist] using hq)
    have hrawTarget :
        d.edist x q.1.center + (q.1.radius : ℝ≥0∞) <
          ((ε - r : ℝ≥0) : ℝ≥0∞) := by
      calc
        d.edist x q.1.center + (q.1.radius : ℝ≥0∞)
            < (δ : ℝ≥0∞) +
                (RoundedIdeal.hausdorffEdist d
                  (RoundedIdeal.principal d
                    (⟨x, 0⟩ : d.FormalBall)) A.1 + (δ : ℝ≥0∞)) := hraw
        _ = RoundedIdeal.hausdorffEdist d
              (RoundedIdeal.principal d
                (⟨x, 0⟩ : d.FormalBall)) A.1 + (γ : ℝ≥0∞) := by
              have hhalf : (δ : ℝ≥0∞) + (δ : ℝ≥0∞) =
                  (γ : ℝ≥0∞) := by
                exact_mod_cast add_halves γ
              rw [show (δ : ℝ≥0∞) +
                    (RoundedIdeal.hausdorffEdist d
                      (RoundedIdeal.principal d
                        (⟨x, 0⟩ : d.FormalBall)) A.1 + (δ : ℝ≥0∞)) =
                  RoundedIdeal.hausdorffEdist d
                    (RoundedIdeal.principal d
                      (⟨x, 0⟩ : d.FormalBall)) A.1 +
                    ((δ : ℝ≥0∞) + (δ : ℝ≥0∞)) by ac_rfl,
                hhalf]
        _ < ((ε - r : ℝ≥0) : ℝ≥0∞) := hHγ
    have htargetA : (⟨x, ε - r⟩ : d.FormalBall) ∈ A.1 :=
      RoundedIdeal.lower d A.1 q.2 hrawTarget
    refine ⟨hrε, ?_⟩
    change (⟨x, ε - r⟩ : d.FormalBall) ∈ A.1
    simpa [FormalBall.unshift] using htargetA
  · intro hmem
    have hrε : r ≤ ε := hmem.1
    let z : d.FormalBall := ⟨x, ε - r⟩
    have hzA : z ∈ A.1 := by
      simpa [z, FormalBall.unshift] using hmem.2
    rcases RoundedIdeal.directed d A.1 hzA hzA with
      ⟨q, hqA, hzq, _⟩
    have hHlt : RoundedIdeal.hausdorffEdist d
        (RoundedIdeal.principal d (⟨x, 0⟩ : d.FormalBall)) A.1 <
        ((ε - r : ℝ≥0) : ℝ≥0∞) := by
      apply (iSup_le (fun p ↦ ?_)).trans_lt hzq
      exact (iInf_le
        (fun q' : (A.1 : Set d.FormalBall) ↦
          d.formalBallEdist p.1 q'.1) ⟨q, hqA⟩).trans
            (by
              simpa [z, formalBallEdist] using
                (formalBallEdist_le_from_principal d x
                  (q := q) p.2))
    have hadd : RoundedIdeal.hausdorffEdist d
          (RoundedIdeal.principal d (⟨x, 0⟩ : d.FormalBall)) A.1 +
            (r : ℝ≥0∞) <
        ((ε - r : ℝ≥0) : ℝ≥0∞) + (r : ℝ≥0∞) :=
      (ENNReal.add_lt_add_iff_right
      (a := (r : ℝ≥0∞))
      (b := RoundedIdeal.hausdorffEdist d
        (RoundedIdeal.principal d (⟨x, 0⟩ : d.FormalBall)) A.1)
      (c := ((ε - r : ℝ≥0) : ℝ≥0∞)) ENNReal.coe_ne_top).2 hHlt
    calc
      RoundedIdeal.hausdorffEdist d
            (RoundedIdeal.principal d (⟨x, 0⟩ : d.FormalBall)) A.1 +
          (r : ℝ≥0∞)
          < ((ε - r : ℝ≥0) : ℝ≥0∞) + (r : ℝ≥0∞) := hadd
      _ = (ε : ℝ≥0∞) := by
        rw [← ENNReal.coe_add, tsub_add_cancel_of_le hrε]

/-- Principal completion points are center points. -/
theorem principalPoint_isCenterPoint (x : X) :
    (quasiMetric d).IsCenterPoint (principalPoint d x) := by
  intro ε hε
  have hset : (quasiMetric d).formalBallOpenBall (principalPoint d x) ε =
      sigmaScott d ⁻¹' contains d (⟨x, ε⟩ : d.FormalBall) := by
    ext p
    change (quasiMetric d).formalBallEdist
        (⟨principalPoint d x, 0⟩ : Ball d) (WithScott.ofScott p) <
          (ε : ℝ≥0∞) ↔
      (⟨x, ε⟩ : d.FormalBall) ∈ sigma d (WithScott.ofScott p)
    rcases WithScott.ofScott p with ⟨A, r⟩
    exact formalBallOpen_iff_contains d x A r ε
  rw [hset]
  exact (isOpen_contains d (⟨x, ε⟩ : d.FormalBall)).preimage
    (continuous_sigmaScott d)

/-- The principal completion points provide enough center points. -/
theorem hasEnoughCenterPoints :
    (quasiMetric d).HasEnoughCenterPoints := by
  intro U hU p hpU
  let V : Set (WithScott d.RoundedIdeal) :=
    sigmaInvScott d ⁻¹' U
  have hV : IsOpen V := hU.preimage (continuous_sigmaInvScott d)
  have hsigmaV : sigmaScott d (WithScott.toScott p) ∈ V := by
    simpa [V]
  have hVchar := (Topology.IsScott.isOpen_iff_isUpperSet_and_dirSupInaccOn
    (D := Set.univ)).mp hV
  let A := sigma d p
  let PF := RoundedIdeal.principalFamily d A
  have hPFne := RoundedIdeal.principalFamily_nonempty d A
  have hPFdir := RoundedIdeal.principalFamily_directed d A
  have hPFsup := RoundedIdeal.principalFamily_isLUB d A
  have hAinV : WithScott.toScott A ∈ V := by simpa [A] using hsigmaV
  rcases hVchar.2 (Set.mem_univ PF) hPFne hPFdir hPFsup hAinV with
    ⟨I, hIPF, hIV⟩
  rcases hIPF with ⟨q, hqA, rfl⟩
  have hqpos : 0 < q.radius := by
    rcases RoundedIdeal.directed d A hqA hqA with ⟨q', hq'A, hqq', _⟩
    have : (q'.radius : ℝ≥0∞) < (q.radius : ℝ≥0∞) :=
      (le_add_left le_rfl).trans_lt hqq'
    exact lt_of_le_of_lt (zero_le q'.radius) (ENNReal.coe_lt_coe.mp this)
  refine ⟨principalPoint d q.center, q.radius,
    principalPoint_isCenterPoint d q.center, hqpos, ?_, ?_⟩
  · change (quasiMetric d).formalBallEdist
        (⟨principalPoint d q.center, 0⟩ : Ball d) p <
      (q.radius : ℝ≥0∞)
    exact (formalBallOpen_iff_contains d q.center p.center p.radius q.radius).2
      hqA
  · intro z hz
    have hqSigma : q ∈ sigma d (WithScott.ofScott z) :=
      (formalBallOpen_iff_contains d q.center
        (WithScott.ofScott z).center (WithScott.ofScott z).radius q.radius).1 hz
    have hprincipal_le : RoundedIdeal.principal d q ≤
        sigma d (WithScott.ofScott z) := by
      intro a haq
      exact RoundedIdeal.lower d (sigma d (WithScott.ofScott z)) hqSigma haq
    have hzV : sigmaScott d z ∈ V :=
      hVchar.1 hprincipal_le hIV
    simpa [V] using hzV

/-- The formal-ball completion is algebraic in the source-facing
characterization. -/
theorem isAlgebraic : (quasiMetric d).IsAlgebraic :=
  ⟨isStandard d, hasEnoughCenterPoints d⟩

end Completion
end QuasiMetric
end LipschitzYonedaFinalTopology
