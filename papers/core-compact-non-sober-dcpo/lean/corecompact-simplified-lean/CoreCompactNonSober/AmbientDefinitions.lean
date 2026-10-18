import CoreCompactNonSober.OrderDefinitions
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Sets

/-!
# Concrete ambient carrier from Section 3.1

This file defines the actual capacity-constrained carrier and coordinatewise
partial order. Complete-lattice operations and their laws will be constructed
and proved in the proof stage; no complete-lattice instance is assumed here.

`Fin D` labels the manuscript's alphabet `{1, ..., D}` by `0, ..., D-1`.
`alphabetLabelEquiv` proves the precise relabeling equivalence.
-/

set_option autoImplicit false

namespace CoreCompactNonSober

namespace Ambient

/-- ID `def-coordinate`: exactly the integer coordinates `j ≥ 2`. -/
abbrev Coordinate := {j : ℕ // 2 ≤ j}

/-- ID `def-alphabet-size`: `D_j = 2^(2^j)`. -/
def alphabetSize (j : Coordinate) : ℕ :=
  2 ^ (2 ^ j.val)

/-- A finite coordinate alphabet, with zero-based internal labels. -/
abbrev Alphabet (j : Coordinate) := Fin (alphabetSize j)

/-- The manuscript's original one-based alphabet. -/
abbrev PaperAlphabet (j : Coordinate) :=
  {k : ℕ // 1 ≤ k ∧ k ≤ alphabetSize j}

/-- Explicit equivalence `k ↦ k+1` between the internal and source labels. -/
def alphabetLabelEquiv (j : Coordinate) : Alphabet j ≃ PaperAlphabet j where
  toFun k := ⟨k.val + 1, by omega⟩
  invFun k := ⟨k.val - 1, by have := k.property; omega⟩
  left_inv k := by ext; simp
  right_inv k := by
    apply Subtype.ext
    change k.val - 1 + 1 = k.val
    have := k.property
    omega

/-- ID `def-configuration`: one arbitrary subset of the finite alphabet
at each coordinate. `Finset` represents every subset because the alphabet
is finite. -/
abbrev Configuration := (j : Coordinate) → Finset (Alphabet j)

/-- Every subset of a finite alphabet is represented; using `Finset` does
not restrict the configurations to a smaller collection. -/
noncomputable def finiteSubsetEquiv (j : Coordinate) :
    Finset (Alphabet j) ≃ Set (Alphabet j) :=
  Fintype.finsetEquivSet

/-- The equivalence uses the literal underlying subset. -/
theorem finiteSubsetEquiv_apply (j : Coordinate) (A : Finset (Alphabet j)) :
    finiteSubsetEquiv j A = (A : Set (Alphabet j)) :=
  rfl

/-- The number of holes `|N_j \ A|`. -/
def holeCount (j : Coordinate) (A : Finset (Alphabet j)) : ℕ :=
  (Finset.univ \ A).card

/-- ID `def-capacity`, equation `eq:capacity`:
`max 0 (1 - (1/j) * log₂(1 + |N_j \ A|))`. -/
noncomputable def capacity (j : Coordinate) (A : Finset (Alphabet j)) : ℝ :=
  max 0 (1 - (1 / (j.val : ℝ)) * Real.logb 2 (1 + (holeCount j A : ℝ)))

/-- The usual closed real unit interval. -/
abbrev Height := Set.Icc (0 : ℝ) 1

/-- ID `def-ambient-carrier`, equation `eq:ambient`:
the capacity-constrained pairs in `[0,1] × ∏_j 𝒫(N_j)`. -/
def Carrier :=
  {p : Height × Configuration // ∀ j, (p.1 : ℝ) ≤ capacity j (p.2 j)}

/-- ID `def-ambient-order`: inherited coordinatewise order on height and
configurations. The order on finite sets is inclusion. -/
instance : PartialOrder Carrier :=
  inferInstanceAs (PartialOrder
    {p : Height × Configuration // ∀ j, (p.1 : ℝ) ≤ capacity j (p.2 j)})

def height (p : Carrier) : ℝ := p.val.1.val

def configuration (p : Carrier) : Configuration := p.val.2

def Positive (p : Carrier) : Prop := 0 < height p

/-- A retained positive configuration is not the full configuration.
This auxiliary predicate records a deletion from the insertion construction. -/
def HasHole (p : Carrier) : Prop :=
  ∃ j : Coordinate, ∃ z : Alphabet j, z ∉ configuration p j

/-- ID `def-zero-layer`: precisely the height-zero layer of `L`. -/
def zeroLayer : Set Carrier := {p | height p = 0}

/-- Verification that the inherited order is exactly the manuscript's
coordinatewise comparison. -/
theorem le_iff (p q : Carrier) :
    p ≤ q ↔ height p ≤ height q ∧
      ∀ j, configuration p j ⊆ configuration q j :=
  Iff.rfl

end Ambient

end CoreCompactNonSober
