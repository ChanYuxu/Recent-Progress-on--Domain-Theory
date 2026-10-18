import CoreCompactNonSober.AmbientLattice
import CoreCompactNonSober.CountableProductCardinality
import Mathlib.Analysis.Real.Cardinality

/-!
# The zero-height layer and cardinality of the ambient lattice

Source: the last paragraph of `prop:ambient-properties`.
The lower bound is an explicit injection of all subsets of the naturals,
not an assumption that every uncountable set has cardinality continuum.
-/

set_option autoImplicit false

namespace CoreCompactNonSober.Ambient

open Set Cardinal

def zeroAt (A : Configuration) : Carrier :=
  ⟨(⟨0, by norm_num⟩, A), fun j ↦ capacity_nonneg j (A j)⟩

@[simp] theorem height_zeroAt (A : Configuration) : height (zeroAt A) = 0 := rfl

@[simp] theorem configuration_zeroAt (A : Configuration) : configuration (zeroAt A) = A := rfl

def zeroLayerEquiv : zeroLayer ≃ Configuration where
  toFun p := configuration p.val
  invFun A := ⟨zeroAt A, rfl⟩
  left_inv p := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      exact p.property.symm
    · rfl
  right_inv _ := rfl

theorem zeroLayer_isSubDcpo : IsSubDcpo zeroLayer := by
  intro E hEZ _ p hp
  have hub : fullAt ⟨0, by norm_num⟩ ∈ upperBounds E := by
    intro q hq
    apply (le_iff _ _).mpr
    constructor
    · simpa only [height_fullAt] using le_of_eq (hEZ hq)
    · intro j
      simp only [configuration_fullAt]
      exact Finset.subset_univ _
  have hpzero : height p ≤ 0 := by
    simpa only [height_fullAt] using ((le_iff _ _).mp (hp.2 hub)).1
  exact le_antisymm hpzero p.val.1.property.1

def distinguishedLetter (j : Coordinate) : Alphabet j :=
  ⟨0, by unfold alphabetSize; positivity⟩

instance alphabetNonempty (j : Coordinate) : Nonempty (Alphabet j) :=
  ⟨distinguishedLetter j⟩

noncomputable def binaryConfiguration (A : Set ℕ) : Configuration := by
  classical
  exact fun j ↦ if j.val - 2 ∈ A then {distinguishedLetter j} else ∅

theorem binaryConfiguration_injective : Function.Injective binaryConfiguration := by
  intro A B h
  apply Set.ext
  intro n
  let j : Coordinate := ⟨n + 2, by omega⟩
  have hp := congrArg (fun C : Configuration ↦ distinguishedLetter j ∈ C j) h
  by_cases ha : n ∈ A <;> by_cases hb : n ∈ B
  all_goals simp [binaryConfiguration, j, ha, hb] at hp ⊢

theorem configuration_cardinality : Cardinal.mk Configuration = Cardinal.continuum := by
  apply le_antisymm (mk_countable_pi_le_continuum (fun j ↦ Finset (Alphabet j)))
  rw [← Cardinal.mk_set_nat]
  exact Cardinal.mk_le_of_injective binaryConfiguration_injective

theorem zeroLayer_cardinality : Cardinal.mk zeroLayer = Cardinal.continuum :=
  (Cardinal.mk_congr zeroLayerEquiv).trans configuration_cardinality

theorem carrier_cardinality_le : Cardinal.mk Carrier ≤ Cardinal.continuum := by
  calc
    Cardinal.mk Carrier ≤ Cardinal.mk (Height × Configuration) := Cardinal.mk_subtype_le _
    _ = Cardinal.continuum * Cardinal.continuum := by
      rw [Cardinal.mk_prod, Cardinal.mk_Icc_real (by norm_num : (0 : ℝ) < 1),
        configuration_cardinality]
      simp
    _ = Cardinal.continuum := Cardinal.continuum_mul_self

theorem carrier_cardinality : Cardinal.mk Carrier = Cardinal.continuum := by
  apply le_antisymm carrier_cardinality_le
  rw [← zeroLayer_cardinality]
  exact Cardinal.mk_set_le zeroLayer

end CoreCompactNonSober.Ambient
