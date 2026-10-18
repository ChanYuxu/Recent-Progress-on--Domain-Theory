import FiniteValuationApproximable.ContinuousValuation.JonesCrescent

/-!
# Boolean cells for finite families of Scott opens

The finite Boolean signature turns a family of Scott opens into disjoint
cells.  Here each cell is represented as a crescent between the preimages of
the principal and punctured-principal opens of its Boolean pattern.  Its real
mass is exactly the corresponding coefficient of `signatureVector`.
-/

set_option autoImplicit false
set_option linter.unnecessarySimpa false

universe u v

namespace FiniteValuationApproximable
namespace ContinuousValuation

open Set
open AbramskyJung.Chapter2
open scoped ENNReal BigOperators

/-- Principal-open preimage associated with a Boolean membership pattern. -/
noncomputable def signatureCellPrincipal
    {D : Type u} [Preorder D] {I : Type v}
    [Fintype I] [DecidableEq I]
    (O : I → ScottOpen D) (p : MembershipPattern I) : ScottOpen D :=
  ScottOpen.preimage (membershipSignatureMap O)
    (membershipSignatureMap O).continuous (principalScottOpen p)

/-- Punctured-principal-open preimage associated with a Boolean pattern. -/
noncomputable def signatureCellPunctured
    {D : Type u} [Preorder D] {I : Type v}
    [Fintype I] [DecidableEq I]
    (O : I → ScottOpen D) (p : MembershipPattern I) : ScottOpen D :=
  ScottOpen.preimage (membershipSignatureMap O)
    (membershipSignatureMap O).continuous (puncturedPrincipalScottOpen p)

theorem signatureCellPunctured_le_principal
    {D : Type u} [Preorder D] {I : Type v}
    [Fintype I] [DecidableEq I]
    (O : I → ScottOpen D) (p : MembershipPattern I) :
    signatureCellPunctured O p ≤ signatureCellPrincipal O p := by
  intro x hx
  exact hx.1

@[simp]
theorem mem_signatureCellPrincipal_iff
    {D : Type u} [Preorder D] {I : Type v}
    [Fintype I] [DecidableEq I]
    (O : I → ScottOpen D) (p : MembershipPattern I) (x : D) :
    x ∈ signatureCellPrincipal O p ↔
      p ≤ membershipSignature O x :=
  Iff.rfl

@[simp]
theorem mem_signatureCellPunctured_iff
    {D : Type u} [Preorder D] {I : Type v}
    [Fintype I] [DecidableEq I]
    (O : I → ScottOpen D) (p : MembershipPattern I) (x : D) :
    x ∈ signatureCellPunctured O p ↔
      p ≤ membershipSignature O x ∧ membershipSignature O x ≠ p :=
  Iff.rfl

/-- The crescent between the principal and punctured-principal preimages is
exactly one Boolean membership cell. -/
theorem mem_signatureCell_crescent_iff
    {D : Type u} [Preorder D] {I : Type v}
    [Fintype I] [DecidableEq I]
    (O : I → ScottOpen D) (p : MembershipPattern I) (x : D) :
    x ∈ signatureCellPrincipal O p ∧
        x ∉ signatureCellPunctured O p ↔
      membershipSignature O x = p := by
  change (p ≤ membershipSignature O x ∧
      ¬ (p ≤ membershipSignature O x ∧ membershipSignature O x ≠ p)) ↔
    membershipSignature O x = p
  constructor
  · rintro ⟨hp, hnot⟩
    by_contra hne
    exact hnot ⟨hp, hne⟩
  · intro h
    subst h
    exact ⟨le_rfl, by simp⟩

/-- A signature coefficient is the ENNReal difference between the principal
and punctured cell values, converted to a real number. -/
theorem signatureVector_eq_cellDifference
    {D : Type u} [Preorder D] {I : Type v}
    [Fintype I] [DecidableEq I]
    (mu : VSub D) (O : I → ScottOpen D) (p : MembershipPattern I) :
    signatureVector mu O p =
      (mu (signatureCellPrincipal O p) -
        mu (signatureCellPunctured O p)).toReal := by
  rfl

/-- Real subtraction form of the cell coefficient. -/
theorem signatureVector_eq_cellRealSub
    {D : Type u} [Preorder D] {I : Type v}
    [Fintype I] [DecidableEq I]
    (mu : VSub D) (O : I → ScottOpen D) (p : MembershipPattern I) :
    signatureVector mu O p =
      (mu (signatureCellPrincipal O p)).toReal -
        (mu (signatureCellPunctured O p)).toReal := by
  rw [signatureVector_eq_cellDifference,
    ENNReal.toReal_sub_of_le
      (mu.monotone (signatureCellPunctured_le_principal O p))
      (ne_top_of_le_ne_top ENNReal.one_ne_top
        (mu.value_le_one (signatureCellPrincipal O p)))]

/-- Boolean patterns in which at least one coordinate from `s` is true. -/
def someTrueUpper
    {I : Type v} (s : Finset I) : UpperSet (MembershipPattern I) where
  carrier := {p | ∃ i ∈ s, p i = true}
  upper' := by
    intro p q hpq hp
    rcases hp with ⟨i, hi, hpi⟩
    exact ⟨i, hi, Bool.eq_true_of_true_le (hpi ▸ hpq i)⟩

@[simp]
theorem mem_someTrueUpper_iff
    {I : Type v} (s : Finset I) (p : MembershipPattern I) :
    p ∈ someTrueUpper s ↔ ∃ i ∈ s, p i = true :=
  Iff.rfl

/-- Pulling back `someTrueUpper` gives the finite union of the corresponding
source opens. -/
theorem someTrueUpper_preimage
    {D : Type u} [Preorder D] {I : Type v}
    [Fintype I] [DecidableEq I]
    (O : I → ScottOpen D) (s : Finset I) :
    ScottOpen.preimage (membershipSignatureMap O)
        (membershipSignatureMap O).continuous
        (upperSetToScottOpen (someTrueUpper s)) =
      finiteUnion O s := by
  classical
  apply ScottOpen.ext
  ext x
  change (∃ i ∈ s, membershipSignature O x i = true) ↔
    x ∈ finiteUnion O s
  rw [mem_finiteUnion_iff]
  constructor
  · rintro ⟨i, hi, hxi⟩
    exact ⟨i, hi, (membershipSignature_apply_eq_true O x i).mp hxi⟩
  · rintro ⟨i, hi, hxi⟩
    exact ⟨i, hi, (membershipSignature_apply_eq_true O x i).mpr hxi⟩

/-- The total signature coefficient of patterns meeting a finite coordinate
set is exactly the source valuation of the corresponding finite union. -/
theorem signatureVector_someTrueMass_real
    {D : Type u} [Preorder D] {I : Type v}
    [Fintype I] [DecidableEq I]
    (mu : VSub D) (O : I → ScottOpen D) (s : Finset I) :
    (signatureVector mu O).mass
        (someTrueUpper s : Set (MembershipPattern I)) =
      (mu (finiteUnion O s)).toReal := by
  rw [signatureVector_upperMass_real mu O (someTrueUpper s),
    someTrueUpper_preimage]

end ContinuousValuation
end FiniteValuationApproximable
