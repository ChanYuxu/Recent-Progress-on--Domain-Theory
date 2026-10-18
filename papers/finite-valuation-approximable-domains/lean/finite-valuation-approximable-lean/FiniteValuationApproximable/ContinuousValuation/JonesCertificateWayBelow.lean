import FiniteValuationApproximable.ContinuousValuation.JonesCertificateOrder

/-!
# Genuine way-below-ness of certified Jones approximations

For a directed family of valuations whose supremum lies above the source,
each finite subset of atoms gives one strict open-set constraint.  There are
only finitely many such subsets.  Directedness therefore supplies a single
family member satisfying all constraints simultaneously, which dominates
the entire finite atomic valuation.  This proves the order-theoretic
`WayBelow` definition for arbitrary directed sets, not merely sequences.
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

/-- Total real weight of an arbitrary finite subfamily of certified atoms. -/
noncomputable def subsetWeight
    (a : JonesCertificate hD mu) (K : Finset a.index) : ℝ :=
  ∑ q ∈ K, a.weight q

/-- Union of the way-above opens attached to a finite subfamily. -/
def atomUnion
    (a : JonesCertificate hD mu) (K : Finset a.index) : ScottOpen D :=
  finiteUnion (fun q ↦ wayAboveOpen hD (a.point q)) K

theorem subsetWeight_nonneg
    (a : JonesCertificate hD mu) (K : Finset a.index) :
    0 ≤ subsetWeight hD mu a K := by
  unfold subsetWeight
  exact Finset.sum_nonneg fun q _ ↦ a.weight_nonneg q

theorem subsetWeight_bound
    (a : JonesCertificate hD mu) (K : Finset a.index) :
    subsetWeight hD mu a K ≤
      a.rate * (mu (atomUnion hD mu a K)).toReal := by
  exact a.subset_bound K

/-- One finite subfamily constraint is met by some member of any directed
family whose supremum lies above the source valuation. -/
theorem exists_member_ge_subset
    (a : JonesCertificate hD mu)
    {A : Set (VSub D)} {s : VSub D}
    (hA : DirectedSet A) (hs : IsSup A s) (hmus : mu ≤ s)
    (K : Finset a.index) :
    ∃ rho ∈ A,
      ENNReal.ofReal (subsetWeight hD mu a K) ≤
        rho (atomUnion hD mu a K) := by
  classical
  by_cases hpos : 0 < subsetWeight hD mu a K
  · have hbound := subsetWeight_bound hD mu a K
    have hmuNonneg : 0 ≤ (mu (atomUnion hD mu a K)).toReal :=
      ENNReal.toReal_nonneg
    have hmuPos : 0 < (mu (atomUnion hD mu a K)).toReal := by
      nlinarith [subsetWeight_nonneg hD mu a K,
        a.rate_nonneg, hmuNonneg]
    have hscaled :
        a.rate * (mu (atomUnion hD mu a K)).toReal <
          (mu (atomUnion hD mu a K)).toReal := by
      have h := mul_lt_mul_of_pos_right a.rate_lt_one hmuPos
      simpa using h
    have hreal : subsetWeight hD mu a K <
        (mu (atomUnion hD mu a K)).toReal :=
      hbound.trans_lt hscaled
    have hsource :
        ENNReal.ofReal (subsetWeight hD mu a K) <
          mu (atomUnion hD mu a K) :=
      (ENNReal.ofReal_lt_iff_lt_toReal
        (subsetWeight_nonneg hD mu a K)
        (VSub.value_ne_top mu (atomUnion hD mu a K))).2 hreal
    have hsup :
        ENNReal.ofReal (subsetWeight hD mu a K) <
          s (atomUnion hD mu a K) :=
      hsource.trans_le (hmus (atomUnion hD mu a K))
    by_contra hnone
    have hub : ∀ y ∈
        ((fun rho : VSub D ↦ rho (atomUnion hD mu a K)) '' A),
        y ≤ ENNReal.ofReal (subsetWeight hD mu a K) := by
      rintro y ⟨rho, hrhoA, rfl⟩
      apply le_of_not_gt
      intro hgt
      exact hnone ⟨rho, hrhoA, hgt.le⟩
    have hsle : s (atomUnion hD mu a K) ≤
        ENNReal.ofReal (subsetWeight hD mu a K) :=
      (VSub.eval_isSup hA hs (atomUnion hD mu a K)).2 _ hub
    exact (not_le_of_gt hsup) hsle
  · rcases hA.1 with ⟨rho, hrhoA⟩
    refine ⟨rho, hrhoA, ?_⟩
    have hzero : subsetWeight hD mu a K = 0 :=
      le_antisymm (le_of_not_gt hpos) (subsetWeight_nonneg hD mu a K)
    simp [hzero]

/-- A certified finite atomic valuation is genuinely way below its source. -/
theorem toVSub_wayBelow
    (a : JonesCertificate hD mu) : a.toVSub hD mu ≪ mu := by
  classical
  intro A s hA hs hmus
  letI : Fintype a.index := a.fintypeIndex
  have hexists : ∀ K : Finset a.index,
      ∃ rho ∈ A,
        ENNReal.ofReal (subsetWeight hD mu a K) ≤
          rho (atomUnion hD mu a K) :=
    fun K ↦ exists_member_ge_subset hD mu a hA hs hmus K
  let pick : Finset a.index → VSub D :=
    fun K ↦ Classical.choose (hexists K)
  have hpick_mem : ∀ K, pick K ∈ A :=
    fun K ↦ (Classical.choose_spec (hexists K)).1
  have hpick_bound : ∀ K,
      ENNReal.ofReal (subsetWeight hD mu a K) ≤
        pick K (atomUnion hD mu a K) :=
    fun K ↦ (Classical.choose_spec (hexists K)).2
  have hrangeFinite : (Set.range pick).Finite := Set.finite_range pick
  have hrangeSub : Set.range pick ⊆ A := by
    rintro rho ⟨K, rfl⟩
    exact hpick_mem K
  rcases hA.exists_upper_finite hrangeFinite hrangeSub with
    ⟨rho, hrhoA, hrho⟩
  refine ⟨rho, hrhoA, ?_⟩
  intro U
  let K := activeIndices hD mu a U
  calc
    a.toVSub hD mu U =
        ENNReal.ofReal (subsetWeight hD mu a K) := by
      rw [toVSub_apply, finiteAtomicRealMass_eq_sum_active]
      rfl
    _ ≤ pick K (atomUnion hD mu a K) := hpick_bound K
    _ ≤ rho (atomUnion hD mu a K) :=
      (hrho (pick K) ⟨K, rfl⟩) (atomUnion hD mu a K)
    _ ≤ rho U := by
      apply rho.monotone
      simpa only [atomUnion, K] using activeAtomUnion_le hD mu a U

theorem approximantSet_wayBelow
    {nu : VSub D} (hnu : nu ∈ approximantSet hD mu) : nu ≪ mu := by
  rcases hnu with ⟨a, rfl⟩
  exact toVSub_wayBelow hD mu a

end JonesCertificate
end ContinuousValuation
end FiniteValuationApproximable
