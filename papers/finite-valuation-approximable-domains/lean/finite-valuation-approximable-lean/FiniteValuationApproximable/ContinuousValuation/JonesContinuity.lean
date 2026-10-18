import FiniteValuationApproximable.ContinuousValuation.JonesCertificateSup

/-!
# Jones's continuity theorem for subprobability valuations

The preceding modules provide, for every source valuation on a nonempty
continuous domain, a directed family of genuine way-below approximants with
that source as supremum.  This is an `IsBasisRaw Set.univ` witness.  The empty
carrier case is handled separately: its valuation space is a subsingleton and
hence continuous directly from the definition.
-/

set_option autoImplicit false
set_option linter.unnecessarySimpa false

universe u

namespace FiniteValuationApproximable
namespace ContinuousValuation

open Set
open AbramskyJung.Chapter2

/-- Every subsingleton preorder is a continuous domain: each point is compact
and its singleton is a directed approximating family. -/
theorem isContinuousDomain_of_subsingleton
    (A : Type u) [Preorder A] [Subsingleton A] :
    AbramskyJung.Chapter2.IsContinuousDomain A := by
  refine ⟨Set.univ, ?_⟩
  intro x
  refine ⟨{x}, ?_, directed_singleton x, isSup_singleton x⟩
  intro y hy
  have hyx : y = x := Set.mem_singleton_iff.mp hy
  subst y
  refine ⟨Set.mem_univ x, ?_⟩
  intro B s hB _ _
  rcases hB.1 with ⟨b, hbB⟩
  exact ⟨b, hbB, le_of_eq (Subsingleton.elim x b)⟩

/-- On an empty carrier every Scott open is empty, so every continuous
subprobability valuation is the zero valuation. -/
theorem vSub_subsingleton_of_isEmpty
    {D : Type u} [Preorder D] [IsEmpty D] : Subsingleton (VSub D) where
  allEq mu nu := by
    apply VSub.ext
    intro U
    have hU : U = (ScottOpen.empty : ScottOpen D) := by
      apply ScottOpen.ext
      ext x
      exact isEmptyElim x
    rw [hU, mu.1.strict, nu.1.strict]

namespace JonesCertificate

variable {D : Type u} [Preorder D]

/-- The certified Jones family witnesses a raw basis on a nonempty
continuous domain. -/
theorem vSub_isContinuousDomain_of_nonempty [Nonempty D]
    (hD : AbramskyJung.Chapter2.IsContinuousDomain D) :
    AbramskyJung.Chapter2.IsContinuousDomain (VSub D) := by
  refine ⟨Set.univ, ?_⟩
  intro mu
  refine ⟨approximantSet hD mu, ?_,
    approximantSet_directed hD mu, approximantSet_isSup hD mu⟩
  intro nu hnu
  exact ⟨Set.mem_univ nu, approximantSet_wayBelow hD mu hnu⟩

/-- Jones (1990), Corollary 5.4, proved internally: continuous
subprobability valuations over a continuous domain again form a continuous
domain. -/
theorem vSub_isContinuousDomain
    (hD : AbramskyJung.Chapter2.IsContinuousDomain D) :
    AbramskyJung.Chapter2.IsContinuousDomain (VSub D) := by
  classical
  by_cases hnonempty : Nonempty D
  · letI : Nonempty D := hnonempty
    exact vSub_isContinuousDomain_of_nonempty hD
  · letI : IsEmpty D := not_nonempty_iff.mp hnonempty
    letI : Subsingleton (VSub D) := vSub_subsingleton_of_isEmpty
    exact isContinuousDomain_of_subsingleton (VSub D)

end JonesCertificate
end ContinuousValuation
end FiniteValuationApproximable
