import Practice.DomainTheory.Papers.LipschitzYonedaFinalTopology.FormalBallRoundedIdeal

/-!
# The asymmetric Hausdorff distance on rounded ideals

This module proves, rather than postulates, that the source's formula

`dᴴ⁺(D,E) = sup_{p ∈ D} inf_{q ∈ E} d⁺(p,q)`

is a `T₀` extended quasi-metric on rounded ideals.  The proof that zero
distance is inclusion uses roundedness essentially.
-/

set_option autoImplicit false
set_option linter.unnecessarySimpa false

open Set Function
open scoped NNReal ENNReal

noncomputable section

universe u

namespace LipschitzYonedaFinalTopology
namespace QuasiMetric

variable {X : Type u} (d : QuasiMetric X)

namespace FormalBall

/-- The formal-ball quasi-distance satisfies the triangle inequality. -/
theorem formalBallEdist_triangle (p q r : d.FormalBall) :
    d.formalBallEdist p r ≤
      d.formalBallEdist p q + d.formalBallEdist q r := by
  let a := d.edist p.center q.center
  let b := d.edist q.center r.center
  let rp : ℝ≥0∞ := p.radius
  let rq : ℝ≥0∞ := q.radius
  let rr : ℝ≥0∞ := r.radius
  have hcenter : d.edist p.center r.center + rr ≤ a + b + rr :=
    add_le_add (d.edist_triangle _ _ _) le_rfl
  have hsub :
      (a + b + rr) - rp ≤
        (a + rq - rp) + (b + rr - rq) := by
    have h := add_tsub_add_le_tsub_add_tsub
      (a := a + rq) (b := b + rr) (c := rp) (d := rq)
    have hleft :
        (a + rq) + (b + rr) - (rp + rq) =
          (a + b + rr) - rp := by
      calc
        (a + rq) + (b + rr) - (rp + rq)
            = (a + b + rr) + rq - (rp + rq) := by
                congr 1 <;> ac_rfl
        _ = (a + b + rr) - rp :=
          ENNReal.add_sub_add_eq_sub_right ENNReal.coe_ne_top
    rw [hleft] at h
    exact h
  exact (tsub_le_tsub_right hcenter rp).trans (by
    simpa [formalBallEdist, a, b, rp, rq, rr, add_assoc] using hsub)

end FormalBall

namespace RoundedIdeal

/-- The one-sided Hausdorff quasi-distance between rounded ideals. -/
def hausdorffEdist (A B : d.RoundedIdeal) : ℝ≥0∞ :=
  ⨆ p : (A : Set d.FormalBall),
    ⨅ q : (B : Set d.FormalBall), d.formalBallEdist p.1 q.1

theorem hausdorffEdist_self (A : d.RoundedIdeal) :
    hausdorffEdist d A A = 0 := by
  apply le_antisymm
  · apply iSup_le
    intro p
    exact (iInf_le
      (fun q : (A : Set d.FormalBall) ↦ d.formalBallEdist p.1 q.1)
      p).trans (by simp [formalBallEdist, d.edist_self])
  · exact zero_le _

theorem hausdorffEdist_triangle (A B C : d.RoundedIdeal) :
    hausdorffEdist d A C ≤
      hausdorffEdist d A B + hausdorffEdist d B C := by
  apply iSup_le
  intro p
  let left : ℝ≥0∞ :=
    ⨅ r : (C : Set d.FormalBall), d.formalBallEdist p.1 r.1
  let middle : ℝ≥0∞ :=
    ⨅ q : (B : Set d.FormalBall), d.formalBallEdist p.1 q.1
  have hq (q : (B : Set d.FormalBall)) :
      left ≤ d.formalBallEdist p.1 q.1 + hausdorffEdist d B C := by
    have htoInf :
        left ≤ d.formalBallEdist p.1 q.1 +
          (⨅ r : (C : Set d.FormalBall),
            d.formalBallEdist q.1 r.1) := by
      rw [ENNReal.add_iInf]
      apply le_iInf
      intro r
      exact (iInf_le
        (fun s : (C : Set d.FormalBall) ↦
          d.formalBallEdist p.1 s.1) r).trans
            (FormalBall.formalBallEdist_triangle d p.1 q.1 r.1)
    exact htoInf.trans (add_le_add_right
      (le_iSup (fun q' : (B : Set d.FormalBall) ↦
        ⨅ r : (C : Set d.FormalBall),
          d.formalBallEdist q'.1 r.1) q) _)
  have hmiddle :
      left ≤ middle + hausdorffEdist d B C := by
    rw [ENNReal.iInf_add]
    exact le_iInf hq
  exact hmiddle.trans (add_le_add_left
    (le_iSup (fun p' : (A : Set d.FormalBall) ↦
      ⨅ q : (B : Set d.FormalBall),
        d.formalBallEdist p'.1 q.1) p) _)

/-- Zero one-sided Hausdorff distance is exactly inclusion of rounded
ideals. -/
theorem hausdorffEdist_eq_zero_iff_le (A B : d.RoundedIdeal) :
    hausdorffEdist d A B = 0 ↔ A ≤ B := by
  constructor
  · intro hzero p hp
    rcases RoundedIdeal.directed d A hp hp with ⟨p', hp'A, hpp', _⟩
    obtain ⟨ε, hεpos, hgap⟩ :=
      ENNReal.lt_iff_exists_add_pos_lt.mp hpp'
    let pA : (A : Set d.FormalBall) := ⟨p', hp'A⟩
    have hpoint :
        (⨅ q : (B : Set d.FormalBall),
          d.formalBallEdist p' q.1) = 0 := by
      apply le_antisymm
      · exact (le_iSup
          (fun a : (A : Set d.FormalBall) ↦
            ⨅ q : (B : Set d.FormalBall),
              d.formalBallEdist a.1 q.1) pA).trans_eq hzero
      · exact zero_le _
    have hlt :
        (⨅ q : (B : Set d.FormalBall),
          d.formalBallEdist p' q.1) < (ε : ℝ≥0∞) := by
      rw [hpoint]
      exact ENNReal.coe_pos.2 hεpos
    rcases iInf_lt_iff.mp hlt with ⟨q, hq⟩
    have hpqRaw :
        d.edist p'.center q.1.center + (q.1.radius : ℝ≥0∞) <
          (p'.radius : ℝ≥0∞) + (ε : ℝ≥0∞) := by
      exact (ENNReal.cancel_of_ne ENNReal.coe_ne_top).lt_add_of_tsub_lt_left
        (by simpa [formalBallEdist] using hq)
    have hfinite : d.edist p.center p'.center ≠ ∞ := by
      intro htop
      rw [FormalBall.StrictBelow, htop] at hpp'
      simp at hpp'
    have hpq : FormalBall.StrictBelow d p q.1 := by
      calc
        d.edist p.center q.1.center + (q.1.radius : ℝ≥0∞)
            ≤ (d.edist p.center p'.center + d.edist p'.center q.1.center) +
                (q.1.radius : ℝ≥0∞) :=
              add_le_add (d.edist_triangle _ _ _) le_rfl
        _ = d.edist p.center p'.center +
              (d.edist p'.center q.1.center + (q.1.radius : ℝ≥0∞)) := by
                ac_rfl
        _ < d.edist p.center p'.center +
              ((p'.radius : ℝ≥0∞) + (ε : ℝ≥0∞)) :=
              (ENNReal.add_lt_add_iff_left hfinite).2 hpqRaw
        _ = (d.edist p.center p'.center + (p'.radius : ℝ≥0∞)) +
              (ε : ℝ≥0∞) := by ac_rfl
        _ < (p.radius : ℝ≥0∞) := hgap
    exact RoundedIdeal.lower d B q.2 hpq
  · intro hAB
    apply le_antisymm
    · apply iSup_le
      intro p
      let q : (B : Set d.FormalBall) := ⟨p.1, hAB p.2⟩
      have hself : d.formalBallEdist p.1 q.1 = 0 :=
        (formalBallEdist_eq_zero_iff d p.1 q.1).2 (by
          change p.1 ≤ p.1
          exact le_rfl)
      exact (iInf_le
        (fun q' : (B : Set d.FormalBall) ↦
          d.formalBallEdist p.1 q'.1) q).trans_eq hself
    · exact zero_le _

/-- The Hausdorff formula equips rounded ideals with a `T₀` extended
quasi-metric. -/
def hausdorffQuasiMetric : QuasiMetric d.RoundedIdeal where
  edist := hausdorffEdist d
  edist_self := hausdorffEdist_self d
  edist_triangle := hausdorffEdist_triangle d
  eq_of_edist_zero := by
    intro A B hAB hBA
    exact le_antisymm
      ((hausdorffEdist_eq_zero_iff_le d A B).mp hAB)
      ((hausdorffEdist_eq_zero_iff_le d B A).mp hBA)

end RoundedIdeal
end QuasiMetric
end LipschitzYonedaFinalTopology
