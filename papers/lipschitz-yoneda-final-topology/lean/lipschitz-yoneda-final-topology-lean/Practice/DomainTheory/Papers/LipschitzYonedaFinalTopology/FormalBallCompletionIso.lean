import Practice.DomainTheory.Papers.LipschitzYonedaFinalTopology.FormalBallNormalization

/-!
# Formal balls of the completion as rounded ideals

This module proves the source isomorphism

`σ : B(S(X,d),dᴴ⁺) ≃o RI(B(X,d),≺)`,  `σ(D,r)=D+r`.

Both bijectivity and the order characterization are proved from the
Hausdorff formula and roundedness.
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

/-- Aperture reverses inclusion. -/
theorem aperture_antitone {A B : d.RoundedIdeal} (hAB : A ≤ B) :
    aperture d B ≤ aperture d A := by
  apply le_iInf
  intro p
  exact aperture_le_radius d B (hAB p.2)

/-- A translated zero-aperture ideal has translation radius as aperture. -/
theorem apertureRadius_shift_completion (t : ℝ≥0) (A : d.Completion) :
    apertureRadius d (shift d t A.1) = t := by
  apply ENNReal.coe_injective
  rw [coe_apertureRadius, aperture_shift, A.2]
  simp

/-- Normalizing a translated zero-aperture ideal recovers its center. -/
theorem normalize_shift_completion (t : ℝ≥0) (A : d.Completion) :
    normalize d (shift d t A.1) = A.1 := by
  have hrad := apertureRadius_shift_completion d t A
  have hnorm := shift_normalize d (shift d t A.1)
  rw [hrad] at hnorm
  exact shift_injective d t hnorm

end RoundedIdeal

namespace Completion

abbrev Ball := (quasiMetric d).FormalBall

/-- The source map `σ(D,r)=D+r`. -/
def sigma (p : Ball d) : d.RoundedIdeal :=
  RoundedIdeal.shift d p.radius p.center.1

/-- Inverse of `σ`: normalize and retain the aperture as radius. -/
def sigmaInv (A : d.RoundedIdeal) : Ball d :=
  ⟨RoundedIdeal.normalizeCompletion d A, RoundedIdeal.apertureRadius d A⟩

theorem sigma_sigmaInv (A : d.RoundedIdeal) :
    sigma d (sigmaInv d A) = A :=
  RoundedIdeal.shift_normalize d A

theorem sigmaInv_sigma (p : Ball d) :
    sigmaInv d (sigma d p) = p := by
  have hc : RoundedIdeal.normalizeCompletion d (sigma d p) = p.center := by
    apply Subtype.ext
    exact RoundedIdeal.normalize_shift_completion d p.radius p.center
  have hr : RoundedIdeal.apertureRadius d (sigma d p) = p.radius :=
    RoundedIdeal.apertureRadius_shift_completion d p.radius p.center
  cases p with
  | mk center radius =>
      simp only at hc hr ⊢
      rw [FormalBall.mk.injEq]
      exact ⟨hc, hr⟩

/-- Set-theoretic equivalence underlying the order isomorphism. -/
def sigmaEquiv : Ball d ≃ d.RoundedIdeal where
  toFun := sigma d
  invFun := sigmaInv d
  left_inv := sigmaInv_sigma d
  right_inv := sigma_sigmaInv d

/-- Inclusion forces the corresponding aperture inequality. -/
theorem radius_le_of_sigma_le {A B : d.Completion} {r s : ℝ≥0}
    (h : RoundedIdeal.shift d r A.1 ≤ RoundedIdeal.shift d s B.1) :
    s ≤ r := by
  have hap := RoundedIdeal.aperture_antitone d h
  rw [RoundedIdeal.aperture_shift, RoundedIdeal.aperture_shift,
    A.2, B.2] at hap
  apply ENNReal.coe_le_coe.mp
  simpa using hap

/-- Inclusion of translated zero-aperture ideals bounds their Hausdorff
distance. -/
theorem hausdorff_add_le_of_shift_le
    {A B : d.Completion} {r s : ℝ≥0}
    (h : RoundedIdeal.shift d r A.1 ≤ RoundedIdeal.shift d s B.1) :
    RoundedIdeal.hausdorffEdist d A.1 B.1 + (s : ℝ≥0∞) ≤
      (r : ℝ≥0∞) := by
  have hsr : s ≤ r := radius_le_of_sigma_le d h
  let δ : ℝ≥0 := r - s
  have hdist : RoundedIdeal.hausdorffEdist d A.1 B.1 ≤
      (δ : ℝ≥0∞) := by
    apply iSup_le
    intro p
    let q0 : d.FormalBall := FormalBall.shift d δ p.1
    have hshiftR : FormalBall.shift d r p.1 ∈
        RoundedIdeal.shift d r A.1 :=
      RoundedIdeal.shift_mem_shift d r A.1 p.2
    have hshiftS := h hshiftR
    have hqB : q0 ∈ B.1 := by
      have hu := hshiftS.2
      change FormalBall.unshift d s (FormalBall.shift d r p.1) ∈ B.1 at hu
      simpa [q0, δ, FormalBall.shift, FormalBall.unshift,
        add_tsub_assoc_of_le hsr] using hu
    let q : (B.1 : Set d.FormalBall) := ⟨q0, hqB⟩
    have hpq : d.formalBallEdist p.1 q.1 = (δ : ℝ≥0∞) := by
      simp [q, q0, formalBallEdist, FormalBall.shift, d.edist_self,
        ENNReal.coe_add, δ]
    exact (iInf_le
      (fun q' : (B.1 : Set d.FormalBall) ↦
        d.formalBallEdist p.1 q'.1) q).trans_eq hpq
  calc
    RoundedIdeal.hausdorffEdist d A.1 B.1 + (s : ℝ≥0∞)
        ≤ (δ : ℝ≥0∞) + (s : ℝ≥0∞) := add_le_add_left hdist _
    _ = (r : ℝ≥0∞) := by
      exact_mod_cast tsub_add_cancel_of_le hsr

/-- The Hausdorff formal-ball inequality yields inclusion after translating
the two zero-aperture ideals.  The proof uses a strict interpolant in the
source ideal, then an approximate minimizer in the target ideal. -/
theorem shift_le_of_hausdorff_add_le
    {A B : d.Completion} {r s : ℝ≥0}
    (h : RoundedIdeal.hausdorffEdist d A.1 B.1 + (s : ℝ≥0∞) ≤
      (r : ℝ≥0∞)) :
    RoundedIdeal.shift d r A.1 ≤ RoundedIdeal.shift d s B.1 := by
  have hsrE : (s : ℝ≥0∞) ≤ (r : ℝ≥0∞) :=
    (le_add_left le_rfl).trans h
  have hsr : s ≤ r := ENNReal.coe_le_coe.mp hsrE
  let δ : ℝ≥0 := r - s
  have hHδ : RoundedIdeal.hausdorffEdist d A.1 B.1 ≤
      (δ : ℝ≥0∞) := by
    have hsub := ENNReal.le_sub_of_add_le_right ENNReal.coe_ne_top h
    simpa [δ] using hsub
  have hdelta (p : d.FormalBall) (hp : p ∈ A.1) :
      FormalBall.shift d δ p ∈ B.1 := by
    rcases RoundedIdeal.directed d A.1 hp hp with
      ⟨p', hp'A, hpp', _⟩
    obtain ⟨ε, hεpos, hgap⟩ :=
      ENNReal.lt_iff_exists_add_pos_lt.mp hpp'
    let pA : (A.1 : Set d.FormalBall) := ⟨p', hp'A⟩
    have hpoint :
        (⨅ q : (B.1 : Set d.FormalBall),
          d.formalBallEdist p' q.1) ≤ (δ : ℝ≥0∞) :=
      (le_iSup
        (fun a : (A.1 : Set d.FormalBall) ↦
          ⨅ q : (B.1 : Set d.FormalBall),
            d.formalBallEdist a.1 q.1) pA).trans hHδ
    have hδlt : (δ : ℝ≥0∞) < (δ : ℝ≥0∞) + (ε : ℝ≥0∞) := by
      have hpos : (0 : ℝ≥0∞) < (ε : ℝ≥0∞) :=
        ENNReal.coe_pos.2 hεpos
      have hadd := (ENNReal.add_lt_add_iff_left
        (a := (δ : ℝ≥0∞)) (b := 0) (c := (ε : ℝ≥0∞))
        ENNReal.coe_ne_top).2 hpos
      simpa using hadd
    have hinfLt :
        (⨅ q : (B.1 : Set d.FormalBall),
          d.formalBallEdist p' q.1) <
            (δ : ℝ≥0∞) + (ε : ℝ≥0∞) :=
      hpoint.trans_lt hδlt
    rcases iInf_lt_iff.mp hinfLt with ⟨q, hq⟩
    have hpqRaw :
        d.edist p'.center q.1.center + (q.1.radius : ℝ≥0∞) <
          (p'.radius : ℝ≥0∞) +
            ((δ : ℝ≥0∞) + (ε : ℝ≥0∞)) := by
      exact (ENNReal.cancel_of_ne ENNReal.coe_ne_top).lt_add_of_tsub_lt_left
        (by simpa [formalBallEdist, add_assoc] using hq)
    have hfinite : d.edist p.center p'.center ≠ ∞ := by
      intro htop
      rw [FormalBall.StrictBelow, htop] at hpp'
      simp at hpp'
    apply RoundedIdeal.lower d B.1 q.2
    calc
      d.edist (FormalBall.shift d δ p).center q.1.center +
          (q.1.radius : ℝ≥0∞)
          ≤ (d.edist p.center p'.center + d.edist p'.center q.1.center) +
              (q.1.radius : ℝ≥0∞) :=
            add_le_add (d.edist_triangle _ _ _) le_rfl
      _ = d.edist p.center p'.center +
            (d.edist p'.center q.1.center + (q.1.radius : ℝ≥0∞)) := by
              ac_rfl
      _ < d.edist p.center p'.center +
            ((p'.radius : ℝ≥0∞) +
              ((δ : ℝ≥0∞) + (ε : ℝ≥0∞))) :=
            (ENNReal.add_lt_add_iff_left hfinite).2 hpqRaw
      _ = ((d.edist p.center p'.center + (p'.radius : ℝ≥0∞)) +
            (ε : ℝ≥0∞)) + (δ : ℝ≥0∞) := by ac_rfl
      _ < (p.radius : ℝ≥0∞) + (δ : ℝ≥0∞) :=
            (ENNReal.add_lt_add_iff_right ENNReal.coe_ne_top).2 hgap
      _ = ((FormalBall.shift d δ p).radius : ℝ≥0∞) := by
            simp [FormalBall.shift, ENNReal.coe_add]
  intro P hP
  have hsp : s ≤ P.radius := hsr.trans hP.1
  refine ⟨hsp, ?_⟩
  let p := FormalBall.unshift d r P
  have hpA : p ∈ A.1 := hP.2
  have hδp := hdelta p hpA
  have hP_eq : FormalBall.shift d r p = P :=
    FormalBall.shift_unshift d hP.1
  change FormalBall.unshift d s P ∈ B.1
  rw [← hP_eq]
  simpa [p, δ, FormalBall.shift, FormalBall.unshift,
    add_tsub_assoc_of_le hsr] using hδp

/-- Exact order characterization of the source map `σ`. -/
theorem sigma_le_sigma_iff (p q : Ball d) :
    sigma d p ≤ sigma d q ↔ p ≤ q := by
  change RoundedIdeal.shift d p.radius p.center.1 ≤
      RoundedIdeal.shift d q.radius q.center.1 ↔
    (quasiMetric d).edist p.center q.center +
        (q.radius : ℝ≥0∞) ≤ (p.radius : ℝ≥0∞)
  change RoundedIdeal.shift d p.radius p.center.1 ≤
      RoundedIdeal.shift d q.radius q.center.1 ↔
    RoundedIdeal.hausdorffEdist d p.center.1 q.center.1 +
        (q.radius : ℝ≥0∞) ≤ (p.radius : ℝ≥0∞)
  exact ⟨hausdorff_add_le_of_shift_le d,
    shift_le_of_hausdorff_add_le d⟩

/-- Proposition 7.5.4 in the source: formal balls of the completion are
order-isomorphic to the rounded-ideal completion. -/
def sigmaOrderIso : Ball d ≃o d.RoundedIdeal where
  toEquiv := sigmaEquiv d
  map_rel_iff' := fun {p q} ↦ sigma_le_sigma_iff d p q

end Completion
end QuasiMetric
end LipschitzYonedaFinalTopology
