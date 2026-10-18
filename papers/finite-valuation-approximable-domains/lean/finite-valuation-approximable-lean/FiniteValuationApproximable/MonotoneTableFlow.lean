import FiniteValuationApproximable.FiniteValuation.ErosionFS
import FiniteValuationApproximable.Polytope

/-!
# Pointwise erosion on finite monotone tables

This module formalizes equation `eq:Psi-definition` (source lines 1730--1772)
from `main (17).tex`.  For finite posets `A` and `P`, the manuscript's space
`M(A,P)` is represented by `MonotoneTable A P`, and the finite-valuation flow
is lifted pointwise:

`Psi t x = exactPhi t ∘ x`.

The definition below is unconditional.  For nonpositive time `exactPhi` is
the identity, while for positive time its already proved stochastic-order
monotonicity makes the composite a monotone table.  The pointwise equation,
order monotonicity, time antitonicity, semigroup law, and the source's
two-sided upper-set estimate are all proved without a local axiom or proof
placeholder.

Source version: SHA-256
`4b2e65f0f96347bea4df7571e8993ad6e888c0ff7181c1305c5056880365ac94`.
-/

set_option autoImplicit false

universe u v

namespace FiniteValuationApproximable

open scoped Classical

namespace Erosion

variable {P : Type v} [Fintype P] [PartialOrder P]

/-- The exact erosion flow is monotone at every real time.  The existing
positive-time theorem supplies the substantive case; at nonpositive time the
flow is definitionally the identity. -/
theorem exactPhi_mono_all {p q : SubprobabilityVector P} (hpq : p <= q)
    (t : Real) : exactPhi t p <= exactPhi t q := by
  by_cases ht : t <= 0
  · rw [exactPhi_of_nonpos p ht, exactPhi_of_nonpos q ht]
    exact hpq
  · exact exactPhi_mono hpq (le_of_lt (lt_of_not_ge ht))

end Erosion

section Psi

variable {A : Type u} {P : Type v}
variable [Preorder A] [Fintype P] [PartialOrder P]

open Erosion

/-- Equation `eq:Psi-definition`: lift the finite-poset erosion flow pointwise
to the monotone-table space `M(A,P)`.

All structure fields are mathematical: the carrier function is exactly
`exactPhi t ∘ x`, and well-definedness follows from stochastic-order
monotonicity of `exactPhi`. -/
noncomputable def Psi (t : Real) (x : MonotoneTable A P) : MonotoneTable A P where
  toFun := fun a => exactPhi t (x a)
  monotone' := by
    intro a b hab
    exact exactPhi_mono_all ((MonotoneTable.monotone A P x) hab) t

/-- Pointwise form of equation `eq:Psi-definition`. -/
@[simp]
theorem Psi_apply (t : Real) (x : MonotoneTable A P) (a : A) :
    Psi t x a = exactPhi t (x a) :=
  rfl

/-- Function-level form of the source equation
`Psi_t(x) = Phi_t^P ∘ x`. -/
theorem eq_Psi_definition (t : Real) (x : MonotoneTable A P) :
    ((Psi t x : MonotoneTable A P) : A -> SubprobabilityVector P) =
      (fun p => exactPhi t p) ∘ x :=
  rfl

/-- For fixed time, pointwise erosion is monotone on `M(A,P)`. -/
theorem Psi_mono (t : Real) : Monotone (Psi t : MonotoneTable A P -> MonotoneTable A P) := by
  intro x y hxy a
  exact exactPhi_mono_all (hxy a) t

/-- Pointwise erosion remains below the original monotone table. -/
theorem Psi_le (t : Real) (x : MonotoneTable A P) : Psi t x <= x := by
  intro a
  exact exactPhi_le t (x a)

/-- The pointwise flow is the identity at time zero. -/
@[simp]
theorem Psi_zero (x : MonotoneTable A P) : Psi 0 x = x := by
  apply MonotoneTable.ext_apply
  intro a
  exact exactPhi_time_zero (x a)

/-- The pointwise lift inherits the exact semigroup law. -/
theorem Psi_add (x : MonotoneTable A P) {s t : Real}
    (hs0 : 0 <= s) (ht0 : 0 <= t) :
    Psi (s + t) x = Psi s (Psi t x) := by
  apply MonotoneTable.ext_apply
  intro a
  exact exactPhi_add (x a) hs0 ht0

/-- Increasing the erosion time decreases the pointwise lift. -/
theorem Psi_antitone_time (x : MonotoneTable A P) {s t : Real}
    (ht0 : 0 <= t) (hts : t <= s) : Psi s x <= Psi t x := by
  intro a
  exact exactPhi_antitone_time (x a) ht0 hts

/-- The source functional `lambda_{a,U}` after applying `Psi` is exactly the
upper-set mass of the pointwise-eroded valuation. -/
theorem Psi_upperCoordinate (t : Real) (x : MonotoneTable A P)
    (a : A) (U : UpperSet P) :
    (Psi t x).upperCoordinate a U = upperMass (exactPhi t (x a)) U :=
  rfl

/-- Equation `eq:Psi-estimate`, with the positive-part notation represented
by `max _ 0`.  As in the source, the estimate is for nonnegative time; the
formal proof is valid for every upper set, so no nonemptiness premise is
needed. -/
theorem Psi_two_sided (x : MonotoneTable A P) (a : A) (U : UpperSet P)
    {t : Real} (ht0 : 0 <= t) :
    max (x.upperCoordinate a U - erosionConstant (P := P) * t) 0 <=
        (Psi t x).upperCoordinate a U ∧
      (Psi t x).upperCoordinate a U <=
        max (x.upperCoordinate a U - t) 0 := by
  simpa [MonotoneTable.upperCoordinate] using
    (exactPhi_two_sided (x a) U ht0)

end Psi

end FiniteValuationApproximable
