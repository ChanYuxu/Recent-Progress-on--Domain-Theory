import Practice.DomainTheory.Papers.LipschitzYonedaFinalTopology.FormalBallCompletion

/-!
# Normalization of rounded ideals

Every rounded ideal is uniquely a zero-aperture ideal translated by its
aperture.  This is the set-theoretic half of the source isomorphism
`B(S(X,d)) ≅ RI(B(X,d),≺)`.
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

namespace RoundedIdeal

/-- Aperture as a finite formal-ball radius. -/
def apertureRadius (A : d.RoundedIdeal) : ℝ≥0 :=
  (aperture d A).toNNReal

@[simp]
theorem coe_apertureRadius (A : d.RoundedIdeal) :
    (apertureRadius d A : ℝ≥0∞) = aperture d A := by
  exact ENNReal.coe_toNNReal (aperture_ne_top d A)

theorem apertureRadius_le_radius (A : d.RoundedIdeal)
    {p : d.FormalBall} (hp : p ∈ A) :
    apertureRadius d A ≤ p.radius := by
  apply ENNReal.coe_le_coe.mp
  rw [coe_apertureRadius d A]
  exact aperture_le_radius d A hp

/-- Remove the aperture from every member of an ideal. -/
def normalize (A : d.RoundedIdeal) : d.RoundedIdeal where
  val := {p | FormalBall.shift d (apertureRadius d A) p ∈ A}
  property := by
    let a := apertureRadius d A
    constructor
    · intro p q hq hpq
      exact RoundedIdeal.lower d A hq
        ((FormalBall.strictBelow_shift_iff d a p q).2 hpq)
    · constructor
      · rcases RoundedIdeal.nonempty d A with ⟨p, hp⟩
        have hap : a ≤ p.radius := apertureRadius_le_radius d A hp
        refine ⟨FormalBall.unshift d a p, ?_⟩
        simpa [a, FormalBall.shift_unshift d hap] using hp
      · intro p hp q hq
        rcases RoundedIdeal.directed d A hp hq with ⟨r, hr, hpr, hqr⟩
        have har : a ≤ r.radius := apertureRadius_le_radius d A hr
        let r0 := FormalBall.unshift d a r
        refine ⟨r0, ?_, ?_, ?_⟩
        · simpa [a, r0, FormalBall.shift_unshift d har] using hr
        · apply (FormalBall.strictBelow_shift_iff d a p r0).mp
          simpa [r0, FormalBall.shift_unshift d har] using hpr
        · apply (FormalBall.strictBelow_shift_iff d a q r0).mp
          simpa [r0, FormalBall.shift_unshift d har] using hqr

@[simp]
theorem mem_normalize_iff {A : d.RoundedIdeal} {p : d.FormalBall} :
    p ∈ normalize d A ↔
      FormalBall.shift d (apertureRadius d A) p ∈ A :=
  Iff.rfl

/-- Translating the normalization back by the aperture recovers the
original ideal. -/
theorem shift_normalize (A : d.RoundedIdeal) :
    shift d (apertureRadius d A) (normalize d A) = A := by
  apply RoundedIdeal.ext
  intro p
  constructor
  · intro hp
    change apertureRadius d A ≤ p.radius ∧
      FormalBall.unshift d (apertureRadius d A) p ∈ normalize d A at hp
    rcases hp with ⟨hap, hp⟩
    change FormalBall.shift d (apertureRadius d A)
      (FormalBall.unshift d (apertureRadius d A) p) ∈ A at hp
    simpa [FormalBall.shift_unshift d hap] using hp
  · intro hp
    have hap : apertureRadius d A ≤ p.radius :=
      apertureRadius_le_radius d A hp
    refine ⟨hap, ?_⟩
    change FormalBall.shift d (apertureRadius d A)
      (FormalBall.unshift d (apertureRadius d A) p) ∈ A
    simpa [FormalBall.shift_unshift d hap] using hp

/-- Translation by a fixed radius is injective on rounded ideals. -/
theorem shift_injective (t : ℝ≥0) :
    Function.Injective (shift d t) := by
  intro A B hAB
  apply RoundedIdeal.ext
  intro p
  constructor
  · intro hp
    have hs : FormalBall.shift d t p ∈ shift d t A :=
      shift_mem_shift d t A hp
    rw [hAB] at hs
    simpa [FormalBall.shift, FormalBall.unshift] using hs.2
  · intro hp
    have hs : FormalBall.shift d t p ∈ shift d t B :=
      shift_mem_shift d t B hp
    rw [← hAB] at hs
    simpa [FormalBall.shift, FormalBall.unshift] using hs.2

/-- Normalization has aperture zero. -/
theorem aperture_normalize (A : d.RoundedIdeal) :
    aperture d (normalize d A) = 0 := by
  have hshift := aperture_shift d (apertureRadius d A) (normalize d A)
  rw [shift_normalize d A, coe_apertureRadius d A] at hshift
  have hcancel :
      aperture d (normalize d A) + aperture d A =
        0 + aperture d A := by
    simpa using hshift.symm
  exact (ENNReal.add_left_inj (aperture_ne_top d A)).mp hcancel

/-- The zero-aperture ideal underlying the normalization. -/
def normalizeCompletion (A : d.RoundedIdeal) : d.Completion :=
  ⟨normalize d A, aperture_normalize d A⟩

/-- Normalizing an already zero-aperture ideal does nothing. -/
theorem normalize_eq_self_of_aperture_zero (A : d.RoundedIdeal)
    (hA : aperture d A = 0) : normalize d A = A := by
  apply RoundedIdeal.ext
  intro p
  change FormalBall.shift d (apertureRadius d A) p ∈ A ↔ p ∈ A
  simp [apertureRadius, hA, FormalBall.shift]

end RoundedIdeal
end QuasiMetric
end LipschitzYonedaFinalTopology
