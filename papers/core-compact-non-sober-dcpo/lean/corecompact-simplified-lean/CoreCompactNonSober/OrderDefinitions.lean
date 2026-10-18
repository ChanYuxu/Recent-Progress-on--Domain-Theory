import Mathlib.Topology.Order.ScottTopology
import Mathlib.Topology.Sets.Opens

/-!
# Order definitions from Section 2

These background definitions are adapted from the legacy project and are
being rechecked against this project's `source/manuscript.tex`, SHA-256
`9bba1776d112ff696b933960a63eefc627bb65f41f3cc4013025daeab82337bc`.
This comment does not assert completion of the current source audit.

These definitions quantify over all nonempty directed sets, of arbitrary
cardinality. Suprema are expressed by `IsLUB`, without assuming binary meets
or a complete-lattice structure on the retained dcpo.
-/

set_option autoImplicit false

universe u

namespace CoreCompactNonSober

open Set

variable {P : Type u} [PartialOrder P]

/-- ID `def-directed`: directed sets in the manuscript are nonempty. -/
def NonemptyDirected (E : Set P) : Prop :=
  E.Nonempty ∧ DirectedOn (· ≤ ·) E

/-- ID `prelim-cofinal`: `E'` is a subset of `E`, and every member of `E`
lies below a member of `E'`. -/
def CofinalIn (E' E : Set P) : Prop :=
  E' ⊆ E ∧ ∀ e ∈ E, ∃ e' ∈ E', e ≤ e'

/-- ID `def-dcpo`: every nonempty directed subset has a least upper bound. -/
def IsDcpo (P : Type u) [PartialOrder P] : Prop :=
  ∀ E : Set P, NonemptyDirected E → ∃ p : P, IsLUB E p

/-- Element way-below from the current manuscript: `a ≪ b` means that
whenever a nonempty directed set has a supremum above `b`, one of its
members is above `a`. Suprema are still expressed by `IsLUB`, so this
does not silently assume a complete lattice. -/
def ElementWayBelow (a b : P) : Prop :=
  ∀ E : Set P, NonemptyDirected E →
    ∀ p : P, IsLUB E p → b ≤ p → ∃ e ∈ E, a ≤ e

/-- A continuous dcpo in the element-level sense stated in Section 2:
the way-below elements of every `b` form a nonempty directed set with
supremum `b`. Directed completeness itself is included explicitly. -/
def IsContinuousDcpo (P : Type u) [PartialOrder P] : Prop :=
  IsDcpo P ∧ ∀ b : P,
    NonemptyDirected {a : P | ElementWayBelow a b} ∧
      IsLUB {a : P | ElementWayBelow a b} b

/-- ID `def-lower-hull`: the lower hull `↓ A` from Section 2. -/
def lowerHull (A : Set P) : Set P :=
  {x | ∃ a ∈ A, x ≤ a}

/-- ID `def-upper-hull`: the upper hull `↑ A` from Section 2. -/
def upperHull (A : Set P) : Set P :=
  {x | ∃ a ∈ A, a ≤ x}

/-- ID `def-scott-topology`: intrinsic Scott topology, determined by the
order on `P`. `Set.univ` selects all nonempty directed subsets, not just
countable chains. This definition does not use any pre-existing topology. -/
abbrev scottTopology (P : Type u) [PartialOrder P] : TopologicalSpace P :=
  Topology.scott P Set.univ

/-- ID `def-scott-open`: the manuscript's explicit upper-set and
directed-inaccessibility definition. -/
def IsScottOpen (U : Set P) : Prop :=
  IsUpperSet U ∧
    ∀ E : Set P, NonemptyDirected E →
      ∀ p : P, IsLUB E p → p ∈ U → ∃ e ∈ E, e ∈ U

/-- ID `def-scott-closed`: lower sets closed under all nonempty directed
suprema. -/
def IsScottClosed (C : Set P) : Prop :=
  IsLowerSet C ∧
    ∀ E : Set P, E ⊆ C → NonemptyDirected E →
      ∀ p : P, IsLUB E p → p ∈ C

/-- The open-set lattice `𝒪(P)` uses the intrinsic Scott topology. In
particular `ScottOpens S` for a subtype `S` uses its inherited order, not the
subspace topology inherited from the ambient Scott space. -/
abbrev ScottOpens (P : Type u) [PartialOrder P] :=
  @TopologicalSpace.Opens P (scottTopology P)

/-- ID `def-sub-dcpo`: a subset is closed under directed suprema computed in
the ambient order. Existence of ambient suprema is supplied by the dcpo or
complete-lattice hypothesis where this predicate is used. -/
def IsSubDcpo (S : Set P) : Prop :=
  ∀ E : Set P, E ⊆ S → NonemptyDirected E →
    ∀ p : P, IsLUB E p → p ∈ S

/-- ID `def-proper-sub-dcpo`: strict inclusion and closure under ambient
directed suprema. No bottom element is required to belong to `S`. -/
def IsProperSubDcpo (S : Set P) : Prop :=
  S ⊂ Set.univ ∧ IsSubDcpo S

/-- ID `def-no-greatest`: absence of a greatest element. This does not
assert the stronger condition that there are no maximal elements. -/
def NoGreatestElement (P : Type u) [PartialOrder P] : Prop :=
  ¬ ∃ p : P, ∀ q : P, q ≤ p

/-- ID `def-meet-continuous`, equation `eq:meet-continuity`:
for every nonempty directed `E`, every supremum `p` of `E`, and `q ≤ p`,
`q` belongs to the intrinsic Scott closure of `↓q ∩ ↓E`.

Only a partial order is required; there is no binary-meet assumption. The
main statement supplies directed completeness separately. -/
def MeetContinuous (P : Type u) [PartialOrder P] : Prop :=
  ∀ E : Set P, NonemptyDirected E →
    ∀ p : P, IsLUB E p →
      ∀ q : P, q ≤ p →
        q ∈ @closure P (scottTopology P) (Set.Iic q ∩ lowerHull E)

end CoreCompactNonSober
