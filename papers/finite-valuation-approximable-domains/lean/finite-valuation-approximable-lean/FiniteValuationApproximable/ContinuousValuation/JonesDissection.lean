import FiniteValuationApproximable.ContinuousValuation.JonesCellCover

/-!
# Jones finite dissections

This file combines the cellwise covers into one finite Boolean refinement.
Every refined Boolean pattern carrying selected mass is assigned to one basic
open which covers it; the corresponding atom is placed at the generator of
that basic open.  Patterns not covered receive weight zero.  This realizes
Jones's finite dissection without extending a valuation to a field of sets.
-/

set_option autoImplicit false
set_option linter.unnecessarySimpa false

universe u

namespace FiniteValuationApproximable
namespace ContinuousValuation

open Set
open AbramskyJung.Chapter2
open scoped ENNReal BigOperators

/-- Midpoint scale used twice in the dissection. -/
noncomputable def jonesMid (r : ℝ) : ℝ := (r + 1) / 2

theorem jonesMid_nonneg {r : ℝ} (hr0 : 0 ≤ r) : 0 ≤ jonesMid r := by
  unfold jonesMid
  linarith

theorem jonesMid_pos {r : ℝ} (hr0 : 0 ≤ r) : 0 < jonesMid r := by
  unfold jonesMid
  linarith

theorem jonesMid_lt_one {r : ℝ} (hr1 : r < 1) : jonesMid r < 1 := by
  unfold jonesMid
  linarith

theorem lt_jonesMid_sq {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    r < jonesMid r * jonesMid r := by
  unfold jonesMid
  nlinarith [sq_pos_of_pos (sub_pos.mpr hr1)]

/-- A chosen finite way-above cover for each positive signature cell.  A
zero-mass cell receives the empty cover. -/
noncomputable def chosenCellCover
    {D : Type u} [Preorder D]
    (hD : AbramskyJung.Chapter2.IsContinuousDomain D)
    {I : Type u} [Fintype I] [DecidableEq I]
    (mu : VSub D) (O : I → ScottOpen D)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1)
    (p : MembershipPattern I) : Finset D := by
  classical
  by_cases hp : 0 < signatureVector mu O p
  · exact Classical.choose
      (exists_signatureCell_cover hD mu O p t ht0 ht1 hp)
  · exact ∅

theorem chosenCellCover_mem_pattern
    {D : Type u} [Preorder D]
    (hD : AbramskyJung.Chapter2.IsContinuousDomain D)
    {I : Type u} [Fintype I] [DecidableEq I]
    (mu : VSub D) (O : I → ScottOpen D)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1)
    (p : MembershipPattern I) {b : D}
    (hb : b ∈ chosenCellCover hD mu O t ht0 ht1 p) :
    membershipSignature O b = p := by
  classical
  by_cases hp : 0 < signatureVector mu O p
  · have hspec := Classical.choose_spec
      (exists_signatureCell_cover hD mu O p t ht0 ht1 hp)
    exact hspec.1 b (by simpa [chosenCellCover, hp] using hb)
  · simp [chosenCellCover, hp] at hb

theorem chosenCellCover_capture
    {D : Type u} [Preorder D]
    (hD : AbramskyJung.Chapter2.IsContinuousDomain D)
    {I : Type u} [Fintype I] [DecidableEq I]
    (mu : VSub D) (O : I → ScottOpen D)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1)
    (p : MembershipPattern I)
    (hp : 0 < signatureVector mu O p) :
    t * signatureVector mu O p <
      (mu (crescentCoverOpen hD (signatureCellPunctured O p)
        (chosenCellCover hD mu O t ht0 ht1 p))).toReal -
        (mu (signatureCellPunctured O p)).toReal := by
  classical
  have hspec := Classical.choose_spec
    (exists_signatureCell_cover hD mu O p t ht0 ht1 hp)
  simpa [chosenCellCover, hp] using hspec.2

/-- Indices of all selected cell-cover generators. -/
abbrev JonesSupport
    {D : Type u} [Preorder D]
    (hD : AbramskyJung.Chapter2.IsContinuousDomain D)
    {I : Type u} [Fintype I] [DecidableEq I]
    (mu : VSub D) (O : I → ScottOpen D)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1) :=
  Σ p : MembershipPattern I,
    ↑(chosenCellCover hD mu O t ht0 ht1 p)

noncomputable def jonesSupportPoint
    {D : Type u} [Preorder D]
    (hD : AbramskyJung.Chapter2.IsContinuousDomain D)
    {I : Type u} [Fintype I] [DecidableEq I]
    (mu : VSub D) (O : I → ScottOpen D)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    JonesSupport hD mu O t ht0 ht1 → D :=
  fun j => j.2.1

noncomputable def jonesSupportOpen
    {D : Type u} [Preorder D]
    (hD : AbramskyJung.Chapter2.IsContinuousDomain D)
    {I : Type u} [Fintype I] [DecidableEq I]
    (mu : VSub D) (O : I → ScottOpen D)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    JonesSupport hD mu O t ht0 ht1 → ScottOpen D :=
  fun j => wayAboveOpen hD (jonesSupportPoint hD mu O t ht0 ht1 j)

/-- The common refinement consists of the original opens followed by all
selected way-above cover opens. -/
noncomputable def refinedOpenFamily
    {D : Type u} [Preorder D]
    (hD : AbramskyJung.Chapter2.IsContinuousDomain D)
    {I : Type u} [Fintype I] [DecidableEq I]
    (mu : VSub D) (O : I → ScottOpen D)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    I ⊕ JonesSupport hD mu O t ht0 ht1 → ScottOpen D
  | Sum.inl i => O i
  | Sum.inr j => jonesSupportOpen hD mu O t ht0 ht1 j

/-- Restriction of a refined Boolean pattern to the original family. -/
def refinedOriginalPattern
    {I J : Type u} (q : MembershipPattern (I ⊕ J)) : MembershipPattern I :=
  fun i => q (Sum.inl i)

/-- A refined pattern is selected when it belongs to the exact original cell
of some chosen support and also lies in that support's basic open. -/
def IsChosenRefinedPattern
    {D : Type u} [Preorder D]
    (hD : AbramskyJung.Chapter2.IsContinuousDomain D)
    {I : Type u} [Fintype I] [DecidableEq I]
    (mu : VSub D) (O : I → ScottOpen D)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1)
    (q : MembershipPattern
      (I ⊕ JonesSupport hD mu O t ht0 ht1)) : Prop :=
  ∃ j : JonesSupport hD mu O t ht0 ht1,
    j.1 = refinedOriginalPattern q ∧ q (Sum.inr j) = true

/-- Chosen atomic point for a refined pattern.  The fallback point is used
only when the pattern receives weight zero. -/
noncomputable def refinedAtomicPoint
    {D : Type u} [Preorder D] [Nonempty D]
    (hD : AbramskyJung.Chapter2.IsContinuousDomain D)
    {I : Type u} [Fintype I] [DecidableEq I]
    (mu : VSub D) (O : I → ScottOpen D)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1)
    (q : MembershipPattern
      (I ⊕ JonesSupport hD mu O t ht0 ht1)) : D := by
  classical
  by_cases hq : IsChosenRefinedPattern hD mu O t ht0 ht1 q
  · exact jonesSupportPoint hD mu O t ht0 ht1 (Classical.choose hq)
  · exact Classical.choice inferInstance

/-- Scaled coefficient assigned to a refined Boolean pattern. -/
noncomputable def refinedAtomicWeight
    {D : Type u} [Preorder D]
    (hD : AbramskyJung.Chapter2.IsContinuousDomain D)
    {I : Type u} [Fintype I] [DecidableEq I]
    (mu : VSub D) (O : I → ScottOpen D)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1)
    (q : MembershipPattern
      (I ⊕ JonesSupport hD mu O t ht0 ht1)) : ℝ := by
  classical
  letI : Fintype (JonesSupport hD mu O t ht0 ht1) := Fintype.ofFinite _
  exact if IsChosenRefinedPattern hD mu O t ht0 ht1 q then
    t * signatureVector mu
      (refinedOpenFamily hD mu O t ht0 ht1) q
  else 0

theorem refinedAtomicWeight_nonneg
    {D : Type u} [Preorder D]
    (hD : AbramskyJung.Chapter2.IsContinuousDomain D)
    {I : Type u} [Fintype I] [DecidableEq I]
    (mu : VSub D) (O : I → ScottOpen D)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1)
    (q : MembershipPattern
      (I ⊕ JonesSupport hD mu O t ht0 ht1)) :
    0 ≤ refinedAtomicWeight hD mu O t ht0 ht1 q := by
  classical
  letI : Fintype (JonesSupport hD mu O t ht0 ht1) := Fintype.ofFinite _
  unfold refinedAtomicWeight
  split_ifs
  · have hqnonneg : 0 ≤ signatureVector mu
        (refinedOpenFamily hD mu O t ht0 ht1) q :=
      (signatureVector mu
        (refinedOpenFamily hD mu O t ht0 ht1)).coeff_nonneg q
    exact mul_nonneg ht0 hqnonneg
  · exact le_rfl

end ContinuousValuation
end FiniteValuationApproximable
