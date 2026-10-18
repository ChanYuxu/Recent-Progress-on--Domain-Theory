import Practice.DomainTheory.Papers.LipschitzYonedaFinalTopology.CenterPoints

/-!
# Standard, continuous, and algebraic quasi-metric spaces

These are the source-facing predicates used by the headline theorem.  In
particular, continuity includes standardness because the manuscript defines
a continuous quasi-metric space only after imposing standardness; algebraic
spaces use the equivalent enough-center-points characterization explicitly
selected in the manuscript.
-/

set_option autoImplicit false
set_option linter.unnecessarySimpa false

open Set
open scoped NNReal ENNReal Topology

universe u

namespace LipschitzYonedaFinalTopology
namespace QuasiMetric

variable {X : Type u} (d : QuasiMetric X)

/-- Source Definition 2.1: shifting every radius in a directed family by a
fixed finite amount preserves and reflects existence of a supremum. -/
def IsStandard : Prop :=
  ∀ (ι : Type u) [Preorder ι] (p : ι → d.FormalBall),
    IsDirectedIndex ι → Monotone p → ∀ t : ℝ≥0,
      (∃ q : d.FormalBall, IsLUB (Set.range p) q) ↔
      ∃ q : d.FormalBall,
        IsLUB (Set.range (fun i ↦ FormalBall.shift d t (p i))) q

/-- The way-below relation on formal balls, stated directly so this paper
module does not inherit any proof debt or large API surface from the
textbook development. -/
def FormalBallWayBelow (p q : d.FormalBall) : Prop :=
  ∀ {S : Set d.FormalBall}, S.Nonempty → DirectedOn (· ≤ ·) S →
    ∀ {a : d.FormalBall}, IsLUB S a → q ≤ a →
      ∃ s ∈ S, p ≤ s

/-- A poset is continuous when every element is the directed supremum of
the elements way below it, specialized here to the formal-ball poset. -/
def FormalBallPosetContinuous : Prop :=
  ∀ q : d.FormalBall,
    let A := {p : d.FormalBall | d.FormalBallWayBelow p q}
    A.Nonempty ∧ DirectedOn (· ≤ ·) A ∧ IsLUB A q

/-- A continuous quasi-metric space in the manuscript's sense: it is
standard and its formal-ball poset is a continuous poset. -/
def IsContinuous : Prop :=
  d.IsStandard ∧ d.FormalBallPosetContinuous

/-- The algebraic characterization used by the manuscript: standardness
together with enough center points. -/
def IsAlgebraic : Prop :=
  d.IsStandard ∧ d.HasEnoughCenterPoints

theorem IsContinuous.isStandard (h : d.IsContinuous) : d.IsStandard :=
  h.1

theorem IsContinuous.formalBall_continuous
    (h : d.IsContinuous) :
    d.FormalBallPosetContinuous :=
  h.2

theorem IsAlgebraic.isStandard (h : d.IsAlgebraic) : d.IsStandard :=
  h.1

theorem IsAlgebraic.hasEnoughCenterPoints
    (h : d.IsAlgebraic) : d.HasEnoughCenterPoints :=
  h.2

end QuasiMetric
end LipschitzYonedaFinalTopology
