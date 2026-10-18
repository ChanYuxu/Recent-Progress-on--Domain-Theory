import CoreCompactNonSober.OrderDefinitions
import Mathlib.Topology.Sober
import Mathlib.Topology.Bases
import Mathlib.Topology.Compactness.Compact

/-!
# Topological definitions from Section 2

The neighborhood form of local compactness is kept exactly as in the
manuscript, including a compact *saturated* intermediate set. No Hausdorff
assumption is introduced. Sobriety explicitly includes uniqueness.
-/

set_option autoImplicit false

universe u

namespace CoreCompactNonSober

open Set TopologicalSpace

section Topological

variable {X : Type u} [TopologicalSpace X]

/-- ID `def-specialization`: the source convention `x ≤ₓ y` means
`x ∈ closure {y}`. -/
def SpecializationLE (x y : X) : Prop :=
  x ∈ closure ({y} : Set X)

/-- ID `def-saturated`: intersection of all open neighborhoods of the set.
This definition does not use an assumed order/topology correspondence. -/
def IsSaturated (K : Set X) : Prop :=
  K = ⋂₀ {U : Set X | IsOpen U ∧ K ⊆ U}

/-- ID `def-sober`: every nonempty irreducible closed set has exactly one
generic point. Mathlib's `IsIrreducible` already includes nonemptiness. -/
def IsSober (X : Type u) [TopologicalSpace X] : Prop :=
  ∀ C : Set X, IsClosed C → IsIrreducible C →
    ∃! x : X, closure ({x} : Set X) = C

/-- ID `def-open-way-below`: `V ≪ U` for opens means that every nonempty
inclusion-directed family whose union contains `U` has a member containing
`V`. In `Opens X`, `≤` is inclusion and `sSup` is union. -/
def OpenWayBelow (V U : Opens X) : Prop :=
  ∀ D : Set (Opens X), D.Nonempty → DirectedOn (· ≤ ·) D →
    U ≤ sSup D → ∃ W ∈ D, V ≤ W

/-- ID `def-core-compact`: every point of an open `U` lies in an open
`V ≪ U`. This is the source's neighborhood definition, without an added
sobriety, well-filteredness, countability, or separation condition. -/
def IsCoreCompact (X : Type u) [TopologicalSpace X] : Prop :=
  ∀ (U : Opens X) (x : X), x ∈ U →
    ∃ V : Opens X, x ∈ V ∧ OpenWayBelow V U

/-- ID `def-locally-compact`: for `x ∈ U` open, there are an open `V` and
a compact saturated `K` with `x ∈ V ⊆ K ⊆ U`. -/
def IsLocallyCompact (X : Type u) [TopologicalSpace X] : Prop :=
  ∀ (U : Opens X) (x : X), x ∈ U →
    ∃ (V : Opens X) (K : Set X),
      x ∈ V ∧ (V : Set X) ⊆ K ∧ K ⊆ (U : Set X) ∧
        IsCompact K ∧ IsSaturated K

end Topological

/-- Compactness of the intrinsic Scott space, in the open-cover sense. -/
def ScottCompact (P : Type u) [PartialOrder P] : Prop :=
  @CompactSpace P (scottTopology P)

/-- A countable basis for the intrinsic Scott topology. The carrier itself
is not assumed countable. -/
def ScottSecondCountable (P : Type u) [PartialOrder P] : Prop :=
  @SecondCountableTopology P (scottTopology P)

def ScottLocallyCompact (P : Type u) [PartialOrder P] : Prop :=
  @IsLocallyCompact P (scottTopology P)

def ScottCoreCompact (P : Type u) [PartialOrder P] : Prop :=
  @IsCoreCompact P (scottTopology P)

def ScottSober (P : Type u) [PartialOrder P] : Prop :=
  @IsSober P (scottTopology P)

end CoreCompactNonSober
