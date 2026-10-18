import Practice.DomainTheory.Papers.LipschitzYonedaFinalTopology.FormalBallHausdorff

/-!
# Zero-aperture formal-ball completion

This module defines ideal translation, aperture, and the carrier
`S(X,d)` of zero-aperture rounded ideals.  The Hausdorff quasi-metric is
restricted to that carrier.
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

/-- Translating both radii by the same finite amount preserves and reflects
the strict basis relation. -/
theorem strictBelow_shift_iff (t : ℝ≥0) (p q : d.FormalBall) :
    StrictBelow d (shift d t p) (shift d t q) ↔ StrictBelow d p q := by
  change d.edist p.center q.center + ((q.radius + t : ℝ≥0) : ℝ≥0∞) <
      ((p.radius + t : ℝ≥0) : ℝ≥0∞) ↔
    d.edist p.center q.center + (q.radius : ℝ≥0∞) <
      (p.radius : ℝ≥0∞)
  rw [ENNReal.coe_add, ENNReal.coe_add, ← add_assoc]
  exact ENNReal.add_lt_add_iff_right ENNReal.coe_ne_top

end FormalBall

namespace RoundedIdeal

/-- Translation of a rounded ideal by adding `t` to every radius.  The
membership presentation makes the inverse translation explicit. -/
def shift (t : ℝ≥0) (A : d.RoundedIdeal) : d.RoundedIdeal where
  val := {p | t ≤ p.radius ∧ FormalBall.unshift d t p ∈ A}
  property := by
    constructor
    · intro p q hq hpq
      have hp_le_q : p ≤ q := FormalBall.le_of_strictBelow d hpq
      have htq : t ≤ q.radius := hq.1
      have htp : t ≤ p.radius :=
        htq.trans (FormalBall.radius_le_of_le d hp_le_q)
      refine ⟨htp, RoundedIdeal.lower d A hq.2 ?_⟩
      apply (FormalBall.strictBelow_shift_iff d t
        (FormalBall.unshift d t p) (FormalBall.unshift d t q)).mp
      simpa [FormalBall.shift_unshift d htp,
        FormalBall.shift_unshift d htq] using hpq
    · constructor
      · rcases RoundedIdeal.nonempty d A with ⟨p, hp⟩
        refine ⟨FormalBall.shift d t p, ?_⟩
        change t ≤ p.radius + t ∧
          FormalBall.unshift d t (FormalBall.shift d t p) ∈ A
        constructor
        · exact le_add_left le_rfl
        · simpa [FormalBall.shift, FormalBall.unshift] using hp
      · intro p hp q hq
        rcases RoundedIdeal.directed d A hp.2 hq.2 with
          ⟨r, hr, hpr, hqr⟩
        refine ⟨FormalBall.shift d t r, ?_, ?_, ?_⟩
        · simp [FormalBall.shift, FormalBall.unshift, hr]
        · have h := (FormalBall.strictBelow_shift_iff d t
            (FormalBall.unshift d t p) r).2 hpr
          rw [FormalBall.shift_unshift d hp.1] at h
          exact h
        · have h := (FormalBall.strictBelow_shift_iff d t
            (FormalBall.unshift d t q) r).2 hqr
          rw [FormalBall.shift_unshift d hq.1] at h
          exact h

@[simp]
theorem mem_shift_iff {t : ℝ≥0} {A : d.RoundedIdeal} {p : d.FormalBall} :
    p ∈ shift d t A ↔
      t ≤ p.radius ∧ FormalBall.unshift d t p ∈ A :=
  Iff.rfl

@[simp]
theorem shift_mem_shift (t : ℝ≥0) (A : d.RoundedIdeal)
    {p : d.FormalBall} (hp : p ∈ A) :
    FormalBall.shift d t p ∈ shift d t A := by
  change t ≤ p.radius + t ∧
    FormalBall.unshift d t (FormalBall.shift d t p) ∈ A
  constructor
  · exact le_add_left le_rfl
  · simpa [FormalBall.shift, FormalBall.unshift] using hp

/-- Members of a translated ideal are uniquely obtained by translating
their explicit inverse. -/
theorem shift_unshift_member (t : ℝ≥0) (A : d.RoundedIdeal)
    (p : (shift d t A : Set d.FormalBall)) :
    FormalBall.shift d t (FormalBall.unshift d t p.1) = p.1 :=
  FormalBall.shift_unshift d p.2.1

/-- Translation induces an equivalence between the members of an ideal and
the members of its translate. -/
def shiftEquiv (t : ℝ≥0) (A : d.RoundedIdeal) :
    (A : Set d.FormalBall) ≃ (shift d t A : Set d.FormalBall) where
  toFun p := ⟨FormalBall.shift d t p.1, shift_mem_shift d t A p.2⟩
  invFun p := ⟨FormalBall.unshift d t p.1, p.2.2⟩
  left_inv p := by
    apply Subtype.ext
    simp [FormalBall.shift, FormalBall.unshift]
  right_inv p := by
    apply Subtype.ext
    exact shift_unshift_member d t A p

/-- The aperture is the infimum of all radii in the ideal.  It is first
recorded in `ℝ≥0∞`; nonemptiness makes it finite. -/
def aperture (A : d.RoundedIdeal) : ℝ≥0∞ :=
  ⨅ p : (A : Set d.FormalBall), (p.1.radius : ℝ≥0∞)

theorem aperture_le_radius (A : d.RoundedIdeal) {p : d.FormalBall}
    (hp : p ∈ A) : aperture d A ≤ (p.radius : ℝ≥0∞) :=
  iInf_le (fun q : (A : Set d.FormalBall) ↦
    (q.1.radius : ℝ≥0∞)) ⟨p, hp⟩

theorem aperture_ne_top (A : d.RoundedIdeal) : aperture d A ≠ ∞ := by
  rcases RoundedIdeal.nonempty d A with ⟨p, hp⟩
  exact ne_top_of_le_ne_top ENNReal.coe_ne_top (aperture_le_radius d A hp)

/-- Aperture is additive under ideal translation. -/
@[simp]
theorem aperture_shift (t : ℝ≥0) (A : d.RoundedIdeal) :
    aperture d (shift d t A) = aperture d A + (t : ℝ≥0∞) := by
  unfold aperture
  rw [← (shiftEquiv d t A).surjective.iInf_comp]
  change (⨅ p : (A : Set d.FormalBall),
      (((FormalBall.shift d t p.1).radius : ℝ≥0) : ℝ≥0∞)) = _
  simp only [FormalBall.shift, ENNReal.coe_add]
  exact ENNReal.iInf_add.symm

end RoundedIdeal

/-- The formal-ball completion `S(X,d)`: rounded ideals of aperture zero. -/
def Completion :=
  {A : d.RoundedIdeal // RoundedIdeal.aperture d A = 0}

namespace Completion

instance : Coe d.Completion d.RoundedIdeal := ⟨Subtype.val⟩

instance : SetLike d.Completion d.FormalBall where
  coe A := (A.1 : Set d.FormalBall)
  coe_injective' A B h := by
    apply Subtype.ext
    apply SetLike.ext
    exact Set.ext_iff.mp h

@[ext]
theorem ext {A B : d.Completion} (h : ∀ p, p ∈ A ↔ p ∈ B) : A = B := by
  apply SetLike.ext
  exact h

theorem aperture_eq_zero (A : d.Completion) :
    RoundedIdeal.aperture d A.1 = 0 :=
  A.2

/-- The Hausdorff quasi-metric restricted to zero-aperture ideals. -/
def quasiMetric : QuasiMetric d.Completion where
  edist A B := RoundedIdeal.hausdorffEdist d A.1 B.1
  edist_self A := RoundedIdeal.hausdorffEdist_self d A.1
  edist_triangle A B C :=
    RoundedIdeal.hausdorffEdist_triangle d A.1 B.1 C.1
  eq_of_edist_zero := by
    intro A B hAB hBA
    apply Subtype.ext
    exact (RoundedIdeal.hausdorffQuasiMetric d).eq_of_edist_zero hAB hBA

end Completion
end QuasiMetric
end LipschitzYonedaFinalTopology
