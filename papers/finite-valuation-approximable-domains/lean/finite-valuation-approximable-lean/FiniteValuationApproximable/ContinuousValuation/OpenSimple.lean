import FiniteValuationApproximable.ContinuousValuation.FiniteSignature

/-!
# Finite Scott-open simple functions

This file proves the finite positivity principle behind the Jones lower
integral.  A formal finite linear combination of Scott-open indicators is
evaluated against a valuation by the corresponding finite linear combination
of open masses.  If two such expressions use the same finite family of opens
and are pointwise ordered, their valuation values are ordered as well.

The proof pushes the valuation to the finite Boolean membership cube and then
uses its internally proved atomic vector representation.  Thus no external
content-extension or measure theorem is assumed.
-/

set_option autoImplicit false
set_option linter.unnecessarySimpa false

universe u v

namespace FiniteValuationApproximable
namespace ContinuousValuation

open Set
open scoped BigOperators ENNReal

/-- Value of a finite real coefficient family at a Boolean membership
pattern. -/
noncomputable def patternStepValue
    {ι : Type v} [Fintype ι]
    (a : ι → ℝ) (p : MembershipPattern ι) : ℝ := by
  classical
  exact ∑ i, a i * if p i = true then 1 else 0

/-- Pointwise value of a finite linear combination of Scott-open
indicators. -/
noncomputable def openStepValue
    {D : Type u} [Preorder D] {ι : Type v} [Fintype ι]
    (a : ι → ℝ) (O : ι → ScottOpen D) (x : D) : ℝ := by
  classical
  exact ∑ i, if x ∈ O i then a i else 0

/-- The corresponding finite real linear combination of valuation values. -/
noncomputable def valuationStepValue
    {D : Type u} [Preorder D] {ι : Type v} [Fintype ι]
    (mu : VSub D) (a : ι → ℝ) (O : ι → ScottOpen D) : ℝ :=
  ∑ i, a i * (mu (O i)).toReal

theorem openStepValue_eq_patternStepValue_signature
    {D : Type u} [Preorder D] {ι : Type v}
    [Fintype ι] [DecidableEq ι]
    (a : ι → ℝ) (O : ι → ScottOpen D) (x : D) :
    openStepValue a O x =
      patternStepValue a (membershipSignature O x) := by
  classical
  unfold openStepValue patternStepValue
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hxi : x ∈ O i
  · simp [membershipSignature, hxi]
  · simp [membershipSignature, hxi]

/-- Finite Boolean dissection formula.  The formal valuation value of an open
step expression equals the ordinary weighted sum of its values on Boolean
cells. -/
theorem valuationStepValue_eq_weightedSignature
    {D : Type u} [Preorder D] {ι : Type v}
    [Fintype ι] [DecidableEq ι]
    (mu : VSub D) (a : ι → ℝ) (O : ι → ScottOpen D) :
    valuationStepValue mu a O =
      weightedSum (signatureVector mu O)
        (patternStepValue a) := by
  classical
  symm
  unfold weightedSum patternStepValue
  calc
    (∑ p : MembershipPattern ι,
        signatureVector mu O p *
          ∑ i, a i * if p i = true then 1 else 0) =
        ∑ p : MembershipPattern ι,
          ∑ i, signatureVector mu O p *
            (a i * if p i = true then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.mul_sum]
    _ = ∑ i, ∑ p : MembershipPattern ι,
          signatureVector mu O p *
            (a i * if p i = true then 1 else 0) :=
      Finset.sum_comm
    _ = ∑ i, a i * (mu (O i)).toReal := by
      apply Finset.sum_congr rfl
      intro i hi
      calc
        (∑ p : MembershipPattern ι,
            signatureVector mu O p *
              (a i * if p i = true then 1 else 0)) =
            ∑ p : MembershipPattern ι,
              a i * (if p i = true then signatureVector mu O p else 0) := by
          apply Finset.sum_congr rfl
          intro p hp
          by_cases hpi : p i = true <;> simp [hpi, mul_assoc, mul_comm, mul_left_comm]
        _ = a i * ∑ p : MembershipPattern ι,
              if p i = true then signatureVector mu O p else 0 := by
          rw [Finset.mul_sum]
        _ = a i *
            (signatureVector mu O).mass
              (coordinateUpperSet i : Set (MembershipPattern ι)) := by
          congr 1
          unfold SubprobabilityVector.mass
          apply Finset.sum_congr rfl
          intro p hp
          simp [coordinateUpperSet]
        _ = a i * (mu (O i)).toReal := by
          rw [signatureVector_coordinateMass_real]
    _ = valuationStepValue mu a O := rfl

/-- Positivity for finite Scott-open step expressions using one common open
family.  Coefficients may be signed; only pointwise order is required. -/
theorem valuationStepValue_mono_same
    {D : Type u} [Preorder D] {ι : Type v}
    [Fintype ι] [DecidableEq ι]
    (mu : VSub D) (O : ι → ScottOpen D)
    (a b : ι → ℝ)
    (hab : ∀ x : D, openStepValue a O x ≤ openStepValue b O x) :
    valuationStepValue mu a O ≤ valuationStepValue mu b O := by
  classical
  rw [valuationStepValue_eq_weightedSignature,
    valuationStepValue_eq_weightedSignature]
  unfold weightedSum
  apply Finset.sum_le_sum
  intro p hp
  by_cases hp0 : signatureVector mu O p = 0
  · simp [hp0]
  · have hppos : 0 < signatureVector mu O p :=
      lt_of_le_of_ne ((signatureVector mu O).coeff_nonneg p) (Ne.symm hp0)
    rcases exists_of_signatureVector_pos mu O p hppos with ⟨x, hx⟩
    apply mul_le_mul_of_nonneg_left _
      ((signatureVector mu O).coeff_nonneg p)
    calc
      patternStepValue a p = openStepValue a O x := by
        rw [openStepValue_eq_patternStepValue_signature, hx]
      _ ≤ openStepValue b O x := hab x
      _ = patternStepValue b p := by
        rw [openStepValue_eq_patternStepValue_signature, hx]

end ContinuousValuation
end FiniteValuationApproximable
