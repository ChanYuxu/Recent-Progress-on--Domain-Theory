import FiniteValuationApproximable.ContinuousValuation.JonesApproximationTarget

/-!
# Certified finite atomic Jones approximations

This module records exactly the finite-subfamily estimate needed in Jones's
proof.  A certificate contains a finite atomic subprobability valuation and a
uniform factor `rate < 1`; no order-theoretic conclusion is built into the
structure.  Domination, genuine way-below-ness, directedness, and cofinality
are proved from these fields in subsequent modules.
-/

set_option autoImplicit false
set_option linter.unnecessarySimpa false

universe u

namespace FiniteValuationApproximable
namespace ContinuousValuation

open Set
open AbramskyJung.Chapter2
open scoped ENNReal BigOperators

/-- A finite atomic valuation together with Jones's uniform strict-factor
bound on every finite subfamily of atoms. -/
structure JonesCertificate
    {D : Type u} [Preorder D]
    (hD : AbramskyJung.Chapter2.IsContinuousDomain D) (mu : VSub D) where
  index : Type u
  fintypeIndex : Fintype index
  point : index → D
  weight : index → ℝ
  weight_nonneg : ∀ q, 0 ≤ weight q
  total_le_one : (@Finset.univ index fintypeIndex).sum weight ≤ 1
  rate : ℝ
  rate_nonneg : 0 ≤ rate
  rate_lt_one : rate < 1
  subset_bound : ∀ K : Finset index,
    (∑ q ∈ K, weight q) ≤
      rate * (mu (finiteUnion
        (fun q ↦ wayAboveOpen hD (point q)) K)).toReal

namespace JonesCertificate

variable {D : Type u} [Preorder D]
variable (hD : AbramskyJung.Chapter2.IsContinuousDomain D) (mu : VSub D)

/-- The Scott-open attached to one certified atom. -/
def atomOpen (a : JonesCertificate hD mu) (q : a.index) : ScottOpen D :=
  wayAboveOpen hD (a.point q)

/-- The genuine subprobability valuation represented by a certificate. -/
noncomputable def toVSub (a : JonesCertificate hD mu) : VSub D := by
  letI : Fintype a.index := a.fintypeIndex
  exact finiteAtomicVSub a.point a.weight a.weight_nonneg (by
    simpa only using a.total_le_one)

@[simp]
theorem toVSub_apply (a : JonesCertificate hD mu) (U : ScottOpen D) :
    letI : Fintype a.index := a.fintypeIndex
    a.toVSub hD mu U =
      ENNReal.ofReal (finiteAtomicRealMass a.point a.weight U) := by
  letI : Fintype a.index := a.fintypeIndex
  exact finiteAtomicVSub_apply
    a.point a.weight a.weight_nonneg (by
      simpa only using a.total_le_one) U

theorem toVSub_apply_toReal (a : JonesCertificate hD mu) (U : ScottOpen D) :
    letI : Fintype a.index := a.fintypeIndex
    (a.toVSub hD mu U).toReal =
      finiteAtomicRealMass a.point a.weight U := by
  letI : Fintype a.index := a.fintypeIndex
  exact finiteAtomicVSub_apply_toReal
    a.point a.weight a.weight_nonneg (by
      simpa only using a.total_le_one) U

/-- The set of all certified Jones approximants to `mu`. -/
def approximantSet : Set (VSub D) :=
  {nu | ∃ a : JonesCertificate hD mu, a.toVSub hD mu = nu}

/-- A vacuous certificate, used only to witness nonemptiness. -/
noncomputable def empty : JonesCertificate hD mu where
  index := PEmpty
  fintypeIndex := inferInstance
  point := PEmpty.elim
  weight := PEmpty.elim
  weight_nonneg := by intro q; exact PEmpty.elim q
  total_le_one := by simp
  rate := 0
  rate_nonneg := le_rfl
  rate_lt_one := zero_lt_one
  subset_bound := by
    intro K
    have hK : K = ∅ := by ext q; exact PEmpty.elim q
    subst K
    simp

theorem approximantSet_nonempty : (approximantSet hD mu).Nonempty := by
  exact ⟨(empty hD mu).toVSub hD mu, empty hD mu, rfl⟩

/-- The refined Boolean dissection, packaged with its finite-subfamily
certificate at a prescribed factor `t < 1`. -/
noncomputable def refined
    [Nonempty D]
    {I : Type u} [Fintype I] [DecidableEq I]
    (O : I → ScottOpen D) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    JonesCertificate hD mu := by
  classical
  letI : Fintype (JonesSupport hD mu O t ht0 ht1) := Fintype.ofFinite _
  letI : DecidableEq (JonesSupport hD mu O t ht0 ht1) := Classical.decEq _
  exact
    { index := MembershipPattern (I ⊕ JonesSupport hD mu O t ht0 ht1)
      fintypeIndex := inferInstance
      point := refinedAtomicPoint hD mu O t ht0 ht1
      weight := refinedAtomicWeight hD mu O t ht0 ht1
      weight_nonneg := refinedAtomicWeight_nonneg hD mu O t ht0 ht1
      total_le_one := refinedAtomicWeight_total_le_one hD mu O t ht0 ht1
      rate := t
      rate_nonneg := ht0
      rate_lt_one := ht1
      subset_bound := refinedAtomic_subset_bound hD mu O t ht0 ht1 }

theorem refined_toVSub
    [Nonempty D]
    {I : Type u} [Fintype I] [DecidableEq I]
    (O : I → ScottOpen D) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    (refined hD mu O t ht0 ht1).toVSub hD mu =
      refinedAtomicVSub hD mu O t ht0 ht1 := by
  rfl

/-- The packaged refined certificate has Jones's corrected positive-target
estimate. -/
theorem refined_target_gt
    [Nonempty D]
    {I : Type u} [Fintype I] [DecidableEq I]
    (O : I → ScottOpen D)
    (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (T : Finset I) (hpos : 0 < (mu (finiteUnion O T)).toReal) :
    r * (mu (finiteUnion O T)).toReal <
      ((refined hD mu O (jonesMid r)
        (jonesMid_nonneg hr0) (jonesMid_lt_one hr1)).toVSub
          hD mu (finiteUnion O T)).toReal := by
  rw [refined_toVSub]
  exact refinedAtomicVSub_target_gt hD mu O r hr0 hr1 T hpos

end JonesCertificate
end ContinuousValuation
end FiniteValuationApproximable
