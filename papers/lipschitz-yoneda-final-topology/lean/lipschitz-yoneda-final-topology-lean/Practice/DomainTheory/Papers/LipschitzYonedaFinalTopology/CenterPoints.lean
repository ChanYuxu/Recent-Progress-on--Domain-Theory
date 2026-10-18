import Practice.DomainTheory.Papers.LipschitzYonedaFinalTopology.Cones

/-!
# Center points and Scott-continuous sharp maps

This module records the formal-ball interfaces used in Facts (F3)--(F4) and
in `lem:interpolation` of
`lipschitz_yoneda_final_topology_paper_fifth_audit.tex`.

The definitions of center point and enough center points are literal
topological definitions.  The final predicate isolates the cited formal-ball
criterion for the map `q♯(x,r) = q(x) - αr`; no external theorem is silently
assumed in this file.
-/

set_option autoImplicit false
set_option linter.unnecessarySimpa false

open Set Topology
open scoped NNReal ENNReal Topology

noncomputable section

universe u

namespace LipschitzYonedaFinalTopology
namespace QuasiMetric

variable {X : Type u} (d : QuasiMetric X)

/-- The formal-ball quasi-distance
`d⁺((x,r),(y,s)) = max (d(x,y) - r + s) 0`, written with truncated
subtraction in `ℝ≥0∞`. -/
def formalBallEdist (p q : d.FormalBall) : ℝ≥0∞ :=
  (d.edist p.center q.center + (q.radius : ℝ≥0∞)) -
    (p.radius : ℝ≥0∞)

/-- The specialization order of the formal-ball quasi-distance is exactly
the formal-ball order.  This is also a regression check that subtraction is
performed after adding the target radius. -/
@[simp]
theorem formalBallEdist_eq_zero_iff (p q : d.FormalBall) :
    d.formalBallEdist p q = 0 ↔ p ≤ q := by
  rw [formalBallEdist, tsub_eq_zero_iff_le]
  exact (FormalBall.le_def d (p := p) (q := q)).symm

@[simp]
theorem formalBallEdist_zero_radii (x y : X) :
    d.formalBallEdist (⟨x, 0⟩ : d.FormalBall) ⟨y, 0⟩ =
      d.edist x y := by
  simp [formalBallEdist]

@[simp]
theorem formalBallEdist_center_radius (x : X) (r : ℝ≥0) :
    d.formalBallEdist (⟨x, 0⟩ : d.FormalBall) ⟨x, r⟩ =
      (r : ℝ≥0∞) := by
  simp [formalBallEdist, d.edist_self]

/-- The open `d⁺`-ball of finite radius `ε`, centred at the zero-radius
formal ball `(x,0)`, regarded as a subset of the Scott space of formal
balls. -/
def formalBallOpenBall (x : X) (ε : ℝ≥0) :
    Set (WithScott d.FormalBall) :=
  {p | d.formalBallEdist ⟨x, 0⟩ (WithScott.ofScott p) <
    (ε : ℝ≥0∞)}

theorem mem_formalBallOpenBall_iff
    {x : X} {ε : ℝ≥0} {p : d.FormalBall} :
    WithScott.toScott p ∈ d.formalBallOpenBall x ε ↔
      d.formalBallEdist ⟨x, 0⟩ p < (ε : ℝ≥0∞) :=
  Iff.rfl

/-- Source definition: `x` is a center point when every positive formal-ball
open ball centred at `(x,0)` is Scott-open. -/
def IsCenterPoint (x : X) : Prop :=
  ∀ ε : ℝ≥0, 0 < ε → IsOpen (d.formalBallOpenBall x ε)

/-- Source definition: formal-ball open balls centred at center points form a
basis for the Scott topology on formal balls. -/
def HasEnoughCenterPoints : Prop :=
  ∀ (U : Set (WithScott d.FormalBall)), IsOpen U →
    ∀ p : d.FormalBall, WithScott.toScott p ∈ U →
      ∃ x : X, ∃ ε : ℝ≥0,
        d.IsCenterPoint x ∧ 0 < ε ∧
        WithScott.toScott p ∈ d.formalBallOpenBall x ε ∧
        d.formalBallOpenBall x ε ⊆ U

/-- The concrete consequence of enough center points used by finite cone
interpolation: from an open neighborhood of `(y,0)`, choose a center `x` and
a positive finite radius `t` strictly above `d(x,y)` such that `(x,t)` still
belongs to the neighborhood. -/
theorem HasEnoughCenterPoints.exists_center_radius_mem
    (hcenters : d.HasEnoughCenterPoints)
    {U : Set (WithScott d.FormalBall)} (hU : IsOpen U)
    {y : X} (hy : WithScott.toScott (⟨y, 0⟩ : d.FormalBall) ∈ U) :
    ∃ x : X, ∃ t : ℝ≥0,
      d.IsCenterPoint x ∧ 0 < t ∧
      d.edist x y < (t : ℝ≥0∞) ∧
      WithScott.toScott (⟨x, t⟩ : d.FormalBall) ∈ U := by
  obtain ⟨x, ε, hx, hε, hyball, hballU⟩ :=
    hcenters U hU ⟨y, 0⟩ hy
  have hxyε : d.edist x y < (ε : ℝ≥0∞) := by
    simpa [formalBallOpenBall] using hyball
  obtain ⟨t, hxyt, htε⟩ :=
    ENNReal.lt_iff_exists_nnreal_btwn.mp hxyε
  have ht : 0 < t := by
    exact ENNReal.coe_pos.mp ((zero_le (d.edist x y)).trans_lt hxyt)
  refine ⟨x, t, hx, ht, hxyt, hballU ?_⟩
  change d.formalBallEdist ⟨x, 0⟩ ⟨x, t⟩ < (ε : ℝ≥0∞)
  simpa using htε

/-- The truncated real-valued transform used in the formal-ball criterion:
`q♯(x,r) = q(x) - αr`. -/
def sharp (α : ℝ≥0) (q : X → ℝ≥0∞) (p : d.FormalBall) : ℝ≥0∞ :=
  q p.center - (α : ℝ≥0∞) * (p.radius : ℝ≥0∞)

@[simp]
theorem sharp_zero_radius (α : ℝ≥0) (q : X → ℝ≥0∞) (x : X) :
    d.sharp α q (⟨x, 0⟩ : d.FormalBall) = q x := by
  simp [sharp]

/-- The exact Scott-continuity premise about `q♯` used in the source proof of
finite cone interpolation.  The cited formal-ball criterion is expected to
supply this predicate from standardness and Yoneda continuity. -/
def HasScottContinuousSharp (α : ℝ≥0) (q : X → ℝ≥0∞) : Prop :=
  Continuous (fun p : WithScott d.FormalBall ↦
    WithScott.toScott (d.sharp α q (WithScott.ofScott p)))

/-- Every strict finite superlevel of a Scott-continuous sharp map is open. -/
theorem HasScottContinuousSharp.isOpen_superlevel
    {α : ℝ≥0} {q : X → ℝ≥0∞}
    (hq : d.HasScottContinuousSharp α q) (b : ℝ≥0∞) :
    IsOpen {p : WithScott d.FormalBall |
      b < d.sharp α q (WithScott.ofScott p)} := by
  letI : LinearOrder (WithScott ℝ≥0∞) :=
    inferInstanceAs (LinearOrder ℝ≥0∞)
  have hopen :
      IsOpen (Set.Ioi (WithScott.toScott b) : Set (WithScott ℝ≥0∞)) :=
    isOpen_Ioi
  simpa [Set.preimage] using hopen.preimage hq

end QuasiMetric
end LipschitzYonedaFinalTopology
