import FiniteValuationApproximable.ContinuousValuation.JonesCertificate

/-!
# Order bounds for certified Jones approximations

The finite-subfamily certificate implies that its atomic valuation is below
the source valuation on every Scott open.  This is proved pointwise and does
not use the target-open cofinality estimate.
-/

set_option autoImplicit false
set_option linter.unnecessarySimpa false

universe u

namespace FiniteValuationApproximable
namespace ContinuousValuation

open Set
open AbramskyJung.Chapter2
open scoped ENNReal BigOperators

namespace VSub

theorem value_ne_top {D : Type u} [Preorder D]
    (mu : VSub D) (U : ScottOpen D) : mu U ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (mu.value_le_one U)

end VSub

namespace JonesCertificate

variable {D : Type u} [Preorder D]
variable (hD : AbramskyJung.Chapter2.IsContinuousDomain D) (mu : VSub D)

/-- Indices of the certified atoms lying in a given Scott open. -/
noncomputable def activeIndices
    (a : JonesCertificate hD mu) (U : ScottOpen D) : Finset a.index := by
  classical
  letI : Fintype a.index := a.fintypeIndex
  exact Finset.univ.filter (fun q ↦ a.point q ∈ U)

@[simp]
theorem mem_activeIndices_iff
    (a : JonesCertificate hD mu) (U : ScottOpen D) (q : a.index) :
    q ∈ activeIndices hD mu a U ↔ a.point q ∈ U := by
  classical
  letI : Fintype a.index := a.fintypeIndex
  simp [activeIndices]

theorem finiteAtomicRealMass_eq_sum_active
    (a : JonesCertificate hD mu) (U : ScottOpen D) :
    letI : Fintype a.index := a.fintypeIndex
    finiteAtomicRealMass a.point a.weight U =
      ∑ q ∈ activeIndices hD mu a U, a.weight q := by
  classical
  letI : Fintype a.index := a.fintypeIndex
  unfold finiteAtomicRealMass activeIndices
  rw [Finset.sum_filter]

/-- The finite union of way-above opens belonging to atoms already inside
`U` is itself contained in `U`. -/
theorem activeAtomUnion_le
    (a : JonesCertificate hD mu) (U : ScottOpen D) :
    finiteUnion (fun q ↦ wayAboveOpen hD (a.point q))
        (activeIndices hD mu a U) ≤ U := by
  intro x hx
  rcases (mem_finiteUnion_iff
    (fun q ↦ wayAboveOpen hD (a.point q))
    (activeIndices hD mu a U) x).mp hx with ⟨q, hq, hxq⟩
  exact wayAboveOpen_le_of_mem hD
    ((mem_activeIndices_iff hD mu a U q).mp hq) hxq

/-- Every certified Jones approximant is pointwise below its source
valuation. -/
theorem toVSub_le
    (a : JonesCertificate hD mu) : a.toVSub hD mu ≤ mu := by
  intro U
  letI : Fintype a.index := a.fintypeIndex
  apply (ENNReal.toReal_le_toReal
    (VSub.value_ne_top (a.toVSub hD mu) U)
    (VSub.value_ne_top mu U)).mp
  rw [toVSub_apply_toReal, finiteAtomicRealMass_eq_sum_active]
  calc
    (∑ q ∈ activeIndices hD mu a U, a.weight q) ≤
        a.rate * (mu (finiteUnion
          (fun q ↦ wayAboveOpen hD (a.point q))
          (activeIndices hD mu a U))).toReal :=
      a.subset_bound (activeIndices hD mu a U)
    _ ≤ (mu (finiteUnion
          (fun q ↦ wayAboveOpen hD (a.point q))
          (activeIndices hD mu a U))).toReal :=
      mul_le_of_le_one_left ENNReal.toReal_nonneg a.rate_lt_one.le
    _ ≤ (mu U).toReal :=
      ENNReal.toReal_mono (VSub.value_ne_top mu U)
        (mu.monotone (activeAtomUnion_le hD mu a U))

theorem approximantSet_le_source
    {nu : VSub D} (hnu : nu ∈ approximantSet hD mu) : nu ≤ mu := by
  rcases hnu with ⟨a, rfl⟩
  exact toVSub_le hD mu a

end JonesCertificate
end ContinuousValuation
end FiniteValuationApproximable
