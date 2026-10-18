import FiniteValuationApproximable.ContinuousValuation.JonesCertificateWayBelow

/-!
# Directedness of the certified Jones approximants

Two certificates are jointly dominated by applying the refined Jones
construction to the disjoint union of their atom-open families.  A factor
strictly between both old rates and `1` supplies the strict room needed on
every positive finite subfamily.
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

def sumInlEmbedding (A B : Type u) : A ↪ A ⊕ B where
  toFun := Sum.inl
  inj' := by
    intro x y h
    cases h
    rfl

def sumInrEmbedding (A B : Type u) : B ↪ A ⊕ B where
  toFun := Sum.inr
  inj' := by
    intro x y h
    cases h
    rfl

/-- Mapping a finite atom subfamily into a target family preserves its union
when the target coordinates are the corresponding atom opens. -/
theorem finiteUnion_map_atomOpen
    (a : JonesCertificate hD mu)
    {J : Type u} (e : a.index ↪ J) (O : J → ScottOpen D)
    (hO : ∀ q, O (e q) = wayAboveOpen hD (a.point q))
    (K : Finset a.index) :
    finiteUnion O (K.map e) = atomUnion hD mu a K := by
  apply ScottOpen.ext
  ext x
  constructor
  · intro hx
    rcases (mem_finiteUnion_iff O (K.map e) x).mp hx with ⟨j, hj, hxj⟩
    rcases Finset.mem_map.mp hj with ⟨q, hqK, rfl⟩
    apply (mem_finiteUnion_iff
      (fun q ↦ wayAboveOpen hD (a.point q)) K x).mpr
    exact ⟨q, hqK, by simpa only [hO q] using hxj⟩
  · intro hx
    rcases (mem_finiteUnion_iff
      (fun q ↦ wayAboveOpen hD (a.point q)) K x).mp hx with
      ⟨q, hqK, hxq⟩
    apply (mem_finiteUnion_iff O (K.map e) x).mpr
    refine ⟨e q, Finset.mem_map.mpr ⟨q, hqK, rfl⟩, ?_⟩
    simpa only [hO q] using hxq

/-- If the refined target factor is strictly larger than an old
certificate's factor, the refined valuation dominates the old one. -/
theorem toVSub_le_refined
    [Nonempty D]
    (a : JonesCertificate hD mu)
    {J : Type u} [Fintype J] [DecidableEq J]
    (e : a.index ↪ J) (O : J → ScottOpen D)
    (hO : ∀ q, O (e q) = wayAboveOpen hD (a.point q))
    (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) (har : a.rate < r) :
    a.toVSub hD mu ≤
      (refined hD mu O (jonesMid r)
        (jonesMid_nonneg hr0) (jonesMid_lt_one hr1)).toVSub hD mu := by
  classical
  intro U
  let K := activeIndices hD mu a U
  let T := K.map e
  have hopen : finiteUnion O T = atomUnion hD mu a K := by
    exact finiteUnion_map_atomOpen hD mu a e O hO K
  by_cases hpos : 0 < subsetWeight hD mu a K
  · have hbound := subsetWeight_bound hD mu a K
    have hmuNonneg : 0 ≤ (mu (atomUnion hD mu a K)).toReal :=
      ENNReal.toReal_nonneg
    have hmuPos : 0 < (mu (atomUnion hD mu a K)).toReal := by
      nlinarith [subsetWeight_nonneg hD mu a K,
        a.rate_nonneg, hmuNonneg]
    have hrate :
        a.rate * (mu (atomUnion hD mu a K)).toReal <
          r * (mu (atomUnion hD mu a K)).toReal :=
      mul_lt_mul_of_pos_right har hmuPos
    have hold : subsetWeight hD mu a K <
        r * (mu (atomUnion hD mu a K)).toReal :=
      hbound.trans_lt hrate
    have htarget := refined_target_gt hD mu O r hr0 hr1 T (by
      rw [hopen]
      exact hmuPos)
    have htarget' :
        r * (mu (atomUnion hD mu a K)).toReal <
          ((refined hD mu O (jonesMid r)
            (jonesMid_nonneg hr0) (jonesMid_lt_one hr1)).toVSub
              hD mu (atomUnion hD mu a K)).toReal := by
      simpa only [hopen] using htarget
    have hreal : subsetWeight hD mu a K <
        ((refined hD mu O (jonesMid r)
          (jonesMid_nonneg hr0) (jonesMid_lt_one hr1)).toVSub
            hD mu (atomUnion hD mu a K)).toReal :=
      hold.trans htarget'
    have henn : ENNReal.ofReal (subsetWeight hD mu a K) <
        (refined hD mu O (jonesMid r)
          (jonesMid_nonneg hr0) (jonesMid_lt_one hr1)).toVSub
            hD mu (atomUnion hD mu a K) :=
      (ENNReal.ofReal_lt_iff_lt_toReal
        (subsetWeight_nonneg hD mu a K)
        (VSub.value_ne_top
          ((refined hD mu O (jonesMid r)
            (jonesMid_nonneg hr0) (jonesMid_lt_one hr1)).toVSub hD mu)
          (atomUnion hD mu a K))).2 hreal
    calc
      a.toVSub hD mu U =
          ENNReal.ofReal (subsetWeight hD mu a K) := by
        rw [toVSub_apply, finiteAtomicRealMass_eq_sum_active]
        rfl
      _ ≤ (refined hD mu O (jonesMid r)
            (jonesMid_nonneg hr0) (jonesMid_lt_one hr1)).toVSub
              hD mu (atomUnion hD mu a K) := henn.le
      _ ≤ (refined hD mu O (jonesMid r)
            (jonesMid_nonneg hr0) (jonesMid_lt_one hr1)).toVSub
              hD mu U := by
        apply VSub.monotone
        simpa only [atomUnion, K] using activeAtomUnion_le hD mu a U
  · have hzero : subsetWeight hD mu a K = 0 :=
      le_antisymm (le_of_not_gt hpos) (subsetWeight_nonneg hD mu a K)
    calc
      a.toVSub hD mu U =
          ENNReal.ofReal (subsetWeight hD mu a K) := by
        rw [toVSub_apply, finiteAtomicRealMass_eq_sum_active]
        rfl
      _ = 0 := by simp [hzero]
      _ ≤ (refined hD mu O (jonesMid r)
            (jonesMid_nonneg hr0) (jonesMid_lt_one hr1)).toVSub
              hD mu U := bot_le

/-- The disjoint union of the atom-open families of two certificates. -/
def combinedAtomOpen
    (a b : JonesCertificate hD mu) : a.index ⊕ b.index → ScottOpen D
  | Sum.inl q => wayAboveOpen hD (a.point q)
  | Sum.inr q => wayAboveOpen hD (b.point q)

/-- Certified Jones approximants form a directed set. -/
theorem approximantSet_directed [Nonempty D] :
    DirectedSet (approximantSet hD mu) := by
  classical
  constructor
  · exact approximantSet_nonempty hD mu
  · intro nu hnu eta heta
    rcases hnu with ⟨a, rfl⟩
    rcases heta with ⟨b, rfl⟩
    letI : Fintype a.index := a.fintypeIndex
    letI : Fintype b.index := b.fintypeIndex
    let O := combinedAtomOpen hD mu a b
    let r := (max a.rate b.rate + 1) / 2
    have hmax : max a.rate b.rate < 1 := max_lt a.rate_lt_one b.rate_lt_one
    have hmax0 : 0 ≤ max a.rate b.rate :=
      a.rate_nonneg.trans (le_max_left _ _)
    have hr0 : 0 ≤ r := by
      dsimp [r]
      linarith
    have hr1 : r < 1 := by
      dsimp [r]
      linarith
    have har : a.rate < r := by
      dsimp [r]
      have ha := le_max_left a.rate b.rate
      linarith
    have hbr : b.rate < r := by
      dsimp [r]
      have hb := le_max_right a.rate b.rate
      linarith
    let c := refined hD mu O (jonesMid r)
      (jonesMid_nonneg hr0) (jonesMid_lt_one hr1)
    refine ⟨c.toVSub hD mu, ⟨c, rfl⟩, ?_, ?_⟩
    · simpa only [c, O] using
        (toVSub_le_refined hD mu a
          (sumInlEmbedding a.index b.index) O (by
            intro q
            simp [O, combinedAtomOpen, sumInlEmbedding])
          r hr0 hr1 har)
    · simpa only [c, O] using
        (toVSub_le_refined hD mu b
          (sumInrEmbedding a.index b.index) O (by
            intro q
            simp [O, combinedAtomOpen, sumInrEmbedding])
          r hr0 hr1 hbr)

end JonesCertificate
end ContinuousValuation
end FiniteValuationApproximable
