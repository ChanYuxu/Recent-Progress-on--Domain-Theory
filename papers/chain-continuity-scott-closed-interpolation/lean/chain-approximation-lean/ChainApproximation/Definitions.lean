import Mathlib.Order.Bounds.Basic
import Mathlib.Order.Preorder.Chain
import Mathlib.Topology.Order.ScottTopology
import Mathlib.SetTheory.Cardinal.Cofinality

/-!
# Source definitions, Sections 2 and 3

Source SHA-256: fb98ea2b95418ee17dcebaee23c905a089a32ceb56a7a8d2217ec3806d80f8d1.
All chains and directed sets are nonempty. The canonical approximation
relations are the cut-based relations on arbitrary partial orders; their
existing-supremum forms are proved equivalent on dcpos in `Basic`.
-/

set_option autoImplicit false

universe u

namespace ChainApproximation

open Set

variable {P : Type u} [PartialOrder P]

def NonemptyChain (C : Set P) : Prop := C.Nonempty ∧ IsChain (· ≤ ·) C

def NonemptyDirected (D : Set P) : Prop := D.Nonempty ∧ DirectedOn (· ≤ ·) D

def lowerHull (A : Set P) : Set P := {x | ∃ a ∈ A, x ≤ a}

/-- The literal source cut `(Aᵘ)ˡ`, with no supremum chosen. -/
def cut (A : Set P) : Set P := lowerBounds (upperBounds A)

def IsDcpo (P : Type u) [PartialOrder P] : Prop :=
  ∀ D : Set P, NonemptyDirected D → ∃ p, IsLUB D p

def IsChainComplete (P : Type u) [PartialOrder P] : Prop :=
  ∀ C : Set P, NonemptyChain C → ∃ p, IsLUB C p

def ChainBelow (x y : P) : Prop :=
  ∀ C : Set P, NonemptyChain C → y ∈ cut C → x ∈ lowerHull C

def DirectedBelow (x y : P) : Prop :=
  ∀ D : Set P, NonemptyDirected D → y ∈ cut D → x ∈ lowerHull D

def ChainBelowSup (x y : P) : Prop :=
  ∀ C : Set P, NonemptyChain C → ∀ s : P, IsLUB C s → y ≤ s → x ∈ lowerHull C

def WayBelow (x y : P) : Prop :=
  ∀ D : Set P, NonemptyDirected D → ∀ s : P, IsLUB D s → y ≤ s → x ∈ lowerHull D

def chainSection (y : P) : Set P := {x | ChainBelow x y}

def chainSupSection (y : P) : Set P := {x | ChainBelowSup x y}

def directedSection (y : P) : Set P := {x | DirectedBelow x y}

def waySection (y : P) : Set P := {x | WayBelow x y}

def IsChainGeneratedIdeal (I : Set P) : Prop :=
  ∃ C : Set P, NonemptyChain C ∧ I = lowerHull C

/-- Source chain-precontinuity: chain-generated lower sections approximate
every point; directed completeness is a separate main-theorem hypothesis. -/
def IsChainContinuous (P : Type u) [PartialOrder P] : Prop :=
  ∀ y : P, IsChainGeneratedIdeal (chainSection y) ∧ IsLUB (chainSection y) y

/-- Existing-supremum chain precontinuity on a possibly incomplete poset. -/
def IsChainContinuousSup (P : Type u) [PartialOrder P] : Prop :=
  ∀ y : P, IsChainGeneratedIdeal (chainSupSection y) ∧ IsLUB (chainSupSection y) y

def IsDirectedIdeal (I : Set P) : Prop := IsLowerSet I ∧ NonemptyDirected I

/-- Cut-based directed predistributivity on a possibly incomplete poset. -/
def IsDirectedPredistributive (P : Type u) [PartialOrder P] : Prop :=
  ∀ y : P, IsLUB (directedSection y) y

/-- Existing-supremum directed predistributivity on a possibly incomplete poset. -/
def IsDirectedPredistributiveSup (P : Type u) [PartialOrder P] : Prop :=
  ∀ y : P, IsLUB (waySection y) y

def IsDirectedPrecontinuous (P : Type u) [PartialOrder P] : Prop :=
  IsDirectedPredistributive P ∧ ∀ y : P, IsDirectedIdeal (directedSection y)

def IsDirectedPrecontinuousSup (P : Type u) [PartialOrder P] : Prop :=
  IsDirectedPredistributiveSup P ∧ ∀ y : P, IsDirectedIdeal (waySection y)

def IsContinuous (P : Type u) [PartialOrder P] : Prop :=
  IsDcpo P ∧ ∀ y : P, NonemptyDirected (waySection y) ∧ IsLUB (waySection y) y

def RelComp (S T : P → P → Prop) (a b : P) : Prop := ∃ c, S a c ∧ T c b

def RelPower (T : P → P → Prop) : ℕ → P → P → Prop
  | 0 => Eq
  | n + 1 => RelComp (RelPower T n) T

def Interpolates (T : P → P → Prop) : Prop :=
  ∀ a b, T a b → ∃ c, T a c ∧ T c b

def IsStrongChainContinuous (P : Type u) [PartialOrder P] : Prop :=
  IsChainContinuous P ∧ Interpolates (ChainBelow (P := P))

def IsStrongChainContinuousSup (P : Type u) [PartialOrder P] : Prop :=
  IsChainContinuousSup P ∧ Interpolates (ChainBelowSup (P := P))

def IsAuxiliary (T : P → P → Prop) : Prop :=
  (∀ a b, T a b → a ≤ b) ∧
    ∀ a' a b b', a' ≤ a → T a b → b ≤ b' → T a' b'

def IsScottClosed (F : Set P) : Prop :=
  IsLowerSet F ∧ ∀ D : Set P, D ⊆ F → NonemptyDirected D →
    ∀ s, IsLUB D s → s ∈ F

abbrev scottTopology (P : Type u) [PartialOrder P] : TopologicalSpace P :=
  Topology.scott P Set.univ

/-- The source cofinality, as the actual minimum cofinal cardinal. -/
noncomputable def kappa (p : P) : Cardinal := Order.cof (chainSection p)

end ChainApproximation
