import FiniteValuationApproximable.ContinuousValuation.JonesCertificateDirected

/-!
# Supremum of the certified Jones approximants

The certified approximants are all below the source valuation.  Conversely,
an upper bound that were strictly smaller on one Scott open would be defeated
by a one-coordinate refined approximation with a factor sufficiently close
to `1`.  Hence their supremum is exactly the source valuation.
-/

set_option autoImplicit false
set_option linter.unnecessarySimpa false

universe u

namespace FiniteValuationApproximable
namespace ContinuousValuation

open Set
open AbramskyJung.Chapter2
open scoped ENNReal BigOperators

namespace JonesCertificate

variable {D : Type u} [Preorder D]
variable (hD : AbramskyJung.Chapter2.IsContinuousDomain D) (mu : VSub D)

/-- A universe-correct singleton target index. -/
abbrev SingletonIndex : Type u := ULift.{u, 0} Unit

def singletonIndex : SingletonIndex := ULift.up ()

def singletonOpen (U : ScottOpen D) : SingletonIndex → ScottOpen D :=
  fun _ ↦ U

def singletonTarget : Finset SingletonIndex := {singletonIndex}

@[simp]
theorem finiteUnion_singletonOpen (U : ScottOpen D) :
    finiteUnion (singletonOpen U) singletonTarget = U := by
  apply ScottOpen.ext
  ext x
  constructor
  · intro hx
    rcases (mem_finiteUnion_iff
      (singletonOpen U) singletonTarget x).mp hx with ⟨i, hi, hxi⟩
    exact hxi
  · intro hx
    apply (mem_finiteUnion_iff
      (singletonOpen U) singletonTarget x).mpr
    exact ⟨singletonIndex, by simp [singletonTarget], hx⟩

/-- The source valuation is the least upper bound of all its certified Jones
approximants. -/
theorem approximantSet_isSup [Nonempty D] :
    IsSup (approximantSet hD mu) mu := by
  constructor
  · intro nu hnu
    exact approximantSet_le_source hD mu hnu
  · intro nu hnu U
    apply (ENNReal.toReal_le_toReal
      (VSub.value_ne_top mu U) (VSub.value_ne_top nu U)).mp
    by_contra hnot
    have hlt : (nu U).toReal < (mu U).toReal := lt_of_not_ge hnot
    have hnuNonneg : 0 ≤ (nu U).toReal := ENNReal.toReal_nonneg
    have hmuPos : 0 < (mu U).toReal :=
      lt_of_le_of_lt hnuNonneg hlt
    let q := (nu U).toReal / (mu U).toReal
    have hq0 : 0 ≤ q := by
      exact div_nonneg hnuNonneg hmuPos.le
    have hq1 : q < 1 := by
      dsimp [q]
      exact (div_lt_one hmuPos).2 hlt
    let r := (q + 1) / 2
    have hr0 : 0 ≤ r := by
      dsimp [r]
      linarith
    have hr1 : r < 1 := by
      dsimp [r]
      linarith
    have hqr : q < r := by
      dsimp [r]
      linarith
    have hnur : (nu U).toReal < r * (mu U).toReal := by
      apply (div_lt_iff₀ hmuPos).mp
      simpa only [q] using hqr
    let O := singletonOpen U
    let T := singletonTarget
    have htargetPos : 0 < (mu (finiteUnion O T)).toReal := by
      simpa only [O, T, finiteUnion_singletonOpen] using hmuPos
    let c := refined hD mu O (jonesMid r)
      (jonesMid_nonneg hr0) (jonesMid_lt_one hr1)
    have htarget := refined_target_gt hD mu O r hr0 hr1 T htargetPos
    have htarget' : r * (mu U).toReal < (c.toVSub hD mu U).toReal := by
      simpa only [c, O, T, finiteUnion_singletonOpen] using htarget
    have hc_mem : c.toVSub hD mu ∈ approximantSet hD mu := ⟨c, rfl⟩
    have hc_le : c.toVSub hD mu ≤ nu := hnu hc_mem
    have hcReal_le : (c.toVSub hD mu U).toReal ≤ (nu U).toReal :=
      ENNReal.toReal_mono (VSub.value_ne_top nu U) (hc_le U)
    exact (not_lt_of_ge hcReal_le) (hnur.trans htarget')

end JonesCertificate
end ContinuousValuation
end FiniteValuationApproximable
