import Practice.DomainTheory.Papers.LipschitzYonedaFinalTopology.StandardConsequences

/-!
# Rounded ideals of formal balls

This module develops the concrete abstract basis used by the formal-ball
completion.  It is intentionally local to the paper formalization: no theorem
from the debt-bearing monolithic Chapter 2 file is imported.

The relation is the source's strict formal-ball relation

`(x,r) ≺ (y,s)  ↔  d(x,y) + s < r`.
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

/-- The strict relation on formal balls used for the rounded-ideal
completion. -/
def StrictBelow (p q : d.FormalBall) : Prop :=
  d.edist p.center q.center + (q.radius : ℝ≥0∞) <
    (p.radius : ℝ≥0∞)

theorem strictBelow_def {p q : d.FormalBall} :
    StrictBelow d p q ↔
      d.edist p.center q.center + (q.radius : ℝ≥0∞) <
        (p.radius : ℝ≥0∞) :=
  Iff.rfl

/-- Strict comparison implies formal-ball order comparison. -/
theorem le_of_strictBelow {p q : d.FormalBall}
    (hpq : StrictBelow d p q) :
    p ≤ q :=
  (FormalBall.le_def d).2 hpq.le

/-- The strict formal-ball relation is transitive. -/
theorem strictBelow_trans {p q r : d.FormalBall}
    (hpq : StrictBelow d p q) (hqr : StrictBelow d q r) :
    StrictBelow d p r := by
  have hfinite : d.edist p.center q.center ≠ ∞ := by
    intro htop
    rw [StrictBelow, htop] at hpq
    simp at hpq
  calc
    d.edist p.center r.center + (r.radius : ℝ≥0∞)
        ≤ (d.edist p.center q.center + d.edist q.center r.center) +
            (r.radius : ℝ≥0∞) :=
      add_le_add (d.edist_triangle _ _ _) le_rfl
    _ = d.edist p.center q.center +
          (d.edist q.center r.center + (r.radius : ℝ≥0∞)) := by
      ac_rfl
    _ < d.edist p.center q.center + (q.radius : ℝ≥0∞) :=
      (ENNReal.add_lt_add_iff_left hfinite).2 hqr
    _ < (p.radius : ℝ≥0∞) := hpq

/-- A finite family strictly below one formal ball admits a common strict
interpolant.  This is the concrete abstract-basis interpolation property. -/
theorem strictBelow_finite_interpolation
    (q : d.FormalBall) (M : Set d.FormalBall) (hM : M.Finite)
    (hMq : ∀ m ∈ M, StrictBelow d m q) :
    ∃ y : d.FormalBall,
      (∀ m ∈ M, StrictBelow d m y) ∧ StrictBelow d y q := by
  classical
  by_cases hMempty : M = ∅
  · let y : d.FormalBall := ⟨q.center, q.radius + 1⟩
    refine ⟨y, ?_, ?_⟩
    · intro m hm
      simp [hMempty] at hm
    · dsimp [y, StrictBelow]
      rw [d.edist_self, zero_add]
      change (q.radius : ℝ≥0∞) < (q.radius : ℝ≥0∞) + 1
      have h := (ENNReal.add_lt_add_iff_left
        (a := (q.radius : ℝ≥0∞)) (b := 0) (c := 1)
        ENNReal.coe_ne_top).2 (by norm_num : (0 : ℝ≥0∞) < 1)
      simpa using h
  · have hMne : M.Nonempty := Set.nonempty_iff_ne_empty.2 hMempty
    letI : Fintype M := hM.fintype
    have hgap (m : M) :
        ∃ ε : ℝ≥0, 0 < ε ∧
          (d.edist m.1.center q.center + (q.radius : ℝ≥0∞)) +
              (ε : ℝ≥0∞) < (m.1.radius : ℝ≥0∞) :=
      ENNReal.lt_iff_exists_add_pos_lt.mp (hMq m.1 m.2)
    let gap : M → ℝ≥0 := fun m ↦ Classical.choose (hgap m)
    have gap_pos (m : M) : 0 < gap m :=
      (Classical.choose_spec (hgap m)).1
    have gap_lt (m : M) :
        (d.edist m.1.center q.center + (q.radius : ℝ≥0∞)) +
            (gap m : ℝ≥0∞) < (m.1.radius : ℝ≥0∞) :=
      (Classical.choose_spec (hgap m)).2
    let gaps : Finset ℝ≥0 := Finset.univ.image gap
    have hgaps : gaps.Nonempty := by
      rcases hMne with ⟨m, hm⟩
      exact ⟨gap ⟨m, hm⟩, by simp [gaps]⟩
    let ε : ℝ≥0 := gaps.min' hgaps
    have hεmem : ε ∈ gaps := Finset.min'_mem gaps hgaps
    have hεpos : 0 < ε := by
      rcases Finset.mem_image.mp hεmem with ⟨m, _hm, hmε⟩
      simpa [ε, hmε] using gap_pos m
    have hεle (m : M) : ε ≤ gap m := by
      exact Finset.min'_le gaps (gap m) (by simp [gaps])
    let y : d.FormalBall := ⟨q.center, q.radius + ε⟩
    refine ⟨y, ?_, ?_⟩
    · intro m hm
      let mM : M := ⟨m, hm⟩
      have hcoe : (ε : ℝ≥0∞) ≤ (gap mM : ℝ≥0∞) := by
        exact_mod_cast hεle mM
      calc
        d.edist m.center y.center + (y.radius : ℝ≥0∞)
            = (d.edist m.center q.center + (q.radius : ℝ≥0∞)) +
                (ε : ℝ≥0∞) := by
              simp [y, ENNReal.coe_add, add_assoc]
        _ ≤ (d.edist m.center q.center + (q.radius : ℝ≥0∞)) +
                (gap mM : ℝ≥0∞) := add_le_add_right hcoe _
        _ < (m.radius : ℝ≥0∞) := gap_lt mM
    · dsimp [y, StrictBelow]
      rw [d.edist_self, zero_add]
      change (q.radius : ℝ≥0∞) <
        (q.radius : ℝ≥0∞) + (ε : ℝ≥0∞)
      have h := (ENNReal.add_lt_add_iff_left
        (a := (q.radius : ℝ≥0∞)) (b := 0) (c := (ε : ℝ≥0∞))
        ENNReal.coe_ne_top).2 (ENNReal.coe_pos.2 hεpos)
      simpa using h

end FormalBall

/-- A rounded ideal is nonempty, strict-downward-closed, and directed with
respect to the strict formal-ball relation. -/
def IsRoundedIdeal (A : Set d.FormalBall) : Prop :=
  (∀ ⦃p q : d.FormalBall⦄, q ∈ A →
      FormalBall.StrictBelow d p q → p ∈ A) ∧
  A.Nonempty ∧
  ∀ ⦃p : d.FormalBall⦄, p ∈ A →
    ∀ ⦃q : d.FormalBall⦄, q ∈ A →
      ∃ r ∈ A, FormalBall.StrictBelow d p r ∧
        FormalBall.StrictBelow d q r

/-- The rounded-ideal completion of the strict formal-ball basis. -/
def RoundedIdeal :=
  {A : Set d.FormalBall // d.IsRoundedIdeal A}

namespace RoundedIdeal

instance : SetLike d.RoundedIdeal d.FormalBall where
  coe A := A.1
  coe_injective' A B h := Subtype.ext h

@[ext]
theorem ext {A B : d.RoundedIdeal} (h : ∀ p, p ∈ A ↔ p ∈ B) : A = B := by
  apply SetLike.ext
  exact h

instance : PartialOrder d.RoundedIdeal where
  le A B := (A : Set d.FormalBall) ⊆ B
  le_refl _ := fun _ hp ↦ hp
  le_trans _ _ _ hAB hBC := hAB.trans hBC
  le_antisymm A B hAB hBA := by
    apply SetLike.ext
    intro p
    change p ∈ (A : Set d.FormalBall) ↔ p ∈ (B : Set d.FormalBall)
    constructor
    · intro hp
      exact hAB hp
    · intro hp
      exact hBA hp

theorem lower (A : d.RoundedIdeal) {p q : d.FormalBall}
    (hq : q ∈ A) (hpq : FormalBall.StrictBelow d p q) : p ∈ A :=
  A.2.1 hq hpq

theorem nonempty (A : d.RoundedIdeal) : (A : Set d.FormalBall).Nonempty :=
  A.2.2.1

theorem directed (A : d.RoundedIdeal) {p q : d.FormalBall}
    (hp : p ∈ A) (hq : q ∈ A) :
    ∃ r ∈ A, FormalBall.StrictBelow d p r ∧
      FormalBall.StrictBelow d q r :=
  A.2.2.2 hp hq

/-- The principal rounded ideal `⇓q`. -/
def principal (q : d.FormalBall) : d.RoundedIdeal where
  val := {p | FormalBall.StrictBelow d p q}
  property := by
    constructor
    · intro p r hr hpr
      exact FormalBall.strictBelow_trans d hpr hr
    · constructor
      · rcases FormalBall.strictBelow_finite_interpolation d q ∅ Set.finite_empty
            (by simp) with ⟨y, _hy, hyq⟩
        exact ⟨y, hyq⟩
      · intro p hp r hr
        rcases FormalBall.strictBelow_finite_interpolation d q
            ({p, r} : Set d.FormalBall)
            (Set.finite_singleton r |>.insert p) (by
              intro z hz
              simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
              rcases hz with rfl | rfl
              · exact hp
              · exact hr) with ⟨y, hy, hyq⟩
        exact ⟨y, hyq, hy p (by simp), hy r (by simp)⟩

@[simp]
theorem mem_principal_iff {p q : d.FormalBall} :
    p ∈ principal d q ↔ FormalBall.StrictBelow d p q :=
  Iff.rfl

end RoundedIdeal
end QuasiMetric
end LipschitzYonedaFinalTopology
