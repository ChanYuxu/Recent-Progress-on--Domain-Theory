import FiniteValuationApproximable.ContinuousValuation.JonesAtomic

/-!
# Finite way-above covers of crescents

This is the valuation-only replacement for the Pettis-extension step in
Jones's Lemma 5.1.  If `B ≤ A`, the opens obtained by adjoining to `B` a
finite union of basic opens `\{x | b \ll x\}`, with `b ∈ A \ B`, form a
directed family with supremum `A`.  Scott continuity of a valuation therefore
lets one approximate `mu A` by one such finite cover.
-/

set_option autoImplicit false
set_option linter.unnecessarySimpa false

universe u

namespace FiniteValuationApproximable
namespace ContinuousValuation

open Set
open AbramskyJung.Chapter2
open scoped ENNReal

/-- Adjoin a finite union of way-above basic opens to the excluded open `B`. -/
def crescentCoverOpen
    {D : Type u} [Preorder D]
    (hD : AbramskyJung.Chapter2.IsContinuousDomain D)
    (B : ScottOpen D) (s : Finset D) : ScottOpen D :=
  ScottOpen.union B (finiteUnion (wayAboveOpen hD) s)

@[simp]
theorem mem_crescentCoverOpen_iff
    {D : Type u} [Preorder D]
    (hD : AbramskyJung.Chapter2.IsContinuousDomain D)
    (B : ScottOpen D) (s : Finset D) (x : D) :
    x ∈ crescentCoverOpen hD B s ↔
      x ∈ B ∨ ∃ b ∈ s, b ≪ x := by
  simp [crescentCoverOpen, mem_finiteUnion_iff]

/-- The directed family of finite crescent covers. -/
def crescentCoverFamily
    {D : Type u} [Preorder D]
    (hD : AbramskyJung.Chapter2.IsContinuousDomain D)
    (A B : ScottOpen D) : Set (ScottOpen D) :=
  {W | ∃ s : Finset D,
    (∀ b ∈ s, b ∈ A ∧ b ∉ B) ∧ W = crescentCoverOpen hD B s}

theorem crescentCoverFamily_directed
    {D : Type u} [Preorder D]
    (hD : AbramskyJung.Chapter2.IsContinuousDomain D)
    (A B : ScottOpen D) :
    DirectedSet (crescentCoverFamily hD A B) := by
  classical
  constructor
  · refine ⟨crescentCoverOpen hD B ∅, ∅, ?_, rfl⟩
    intro b hb
    simp at hb
  · rintro W ⟨s, hs, rfl⟩ Z ⟨t, ht, rfl⟩
    refine ⟨crescentCoverOpen hD B (s ∪ t), ⟨s ∪ t, ?_, rfl⟩, ?_, ?_⟩
    · intro b hb
      rcases Finset.mem_union.mp hb with hbs | hbt
      · exact hs b hbs
      · exact ht b hbt
    · intro x hx
      rcases (mem_crescentCoverOpen_iff hD B s x).mp hx with hxB | ⟨b, hb, hbx⟩
      · exact (mem_crescentCoverOpen_iff hD B (s ∪ t) x).mpr (Or.inl hxB)
      · exact (mem_crescentCoverOpen_iff hD B (s ∪ t) x).mpr
          (Or.inr ⟨b, Finset.mem_union_left t hb, hbx⟩)
    · intro x hx
      rcases (mem_crescentCoverOpen_iff hD B t x).mp hx with hxB | ⟨b, hb, hbx⟩
      · exact (mem_crescentCoverOpen_iff hD B (s ∪ t) x).mpr (Or.inl hxB)
      · exact (mem_crescentCoverOpen_iff hD B (s ∪ t) x).mpr
          (Or.inr ⟨b, Finset.mem_union_right s hb, hbx⟩)

/-- When `B ≤ A`, finite crescent covers have supremum `A`. -/
theorem crescentCoverFamily_isSup
    {D : Type u} [Preorder D]
    (hD : AbramskyJung.Chapter2.IsContinuousDomain D)
    {A B : ScottOpen D} (hBA : B ≤ A) :
    IsSup (crescentCoverFamily hD A B) A := by
  classical
  constructor
  · rintro W ⟨s, hs, rfl⟩ x hx
    rcases (mem_crescentCoverOpen_iff hD B s x).mp hx with hxB | ⟨b, hb, hbx⟩
    · exact hBA hxB
    · exact wayAboveOpen_le_of_mem hD (hs b hb).1 hbx
  · intro Z hZ x hxA
    by_cases hxB : x ∈ B
    · have hmem : crescentCoverOpen hD B ∅ ∈
          crescentCoverFamily hD A B := by
        exact ⟨∅, by simp, rfl⟩
      exact hZ hmem ((mem_crescentCoverOpen_iff hD B ∅ x).mpr (Or.inl hxB))
    · rcases exists_wayAboveOpen_mem hD A hxA with ⟨b, hbA, hbx⟩
      have hbB : b ∉ B := by
        intro hb
        exact hxB (B.upper (prop_2_2_2_1 hbx) hb)
      have hmem : crescentCoverOpen hD B {b} ∈
          crescentCoverFamily hD A B := by
        refine ⟨{b}, ?_, rfl⟩
        intro c hc
        have hcb : c = b := by simpa using hc
        subst c
        exact ⟨hbA, hbB⟩
      exact hZ hmem ((mem_crescentCoverOpen_iff hD B {b} x).mpr
        (Or.inr ⟨b, by simp, hbx⟩))

/-- The values of a continuous valuation on the finite crescent covers have
supremum its value on `A`. -/
theorem crescentCoverValues_isSup
    {D : Type u} [Preorder D]
    (hD : AbramskyJung.Chapter2.IsContinuousDomain D)
    (mu : VSub D) {A B : ScottOpen D} (hBA : B ≤ A) :
    IsSup ((fun W : ScottOpen D => mu W) ''
        crescentCoverFamily hD A B) (mu A) :=
  mu.1.continuous.maps_isSup
    (crescentCoverFamily_directed hD A B)
    (crescentCoverFamily_isSup hD hBA)

/-- Any strict lower bound of `mu A` is beaten by one finite crescent cover. -/
theorem exists_crescentCover_value_gt
    {D : Type u} [Preorder D]
    (hD : AbramskyJung.Chapter2.IsContinuousDomain D)
    (mu : VSub D) {A B : ScottOpen D} (hBA : B ≤ A)
    {c : ℝ≥0∞} (hc : c < mu A) :
    ∃ s : Finset D,
      (∀ b ∈ s, b ∈ A ∧ b ∉ B) ∧
      c < mu (crescentCoverOpen hD B s) := by
  classical
  have hsup := crescentCoverValues_isSup hD mu hBA
  by_contra hnone
  push_neg at hnone
  have hcUpper : IsUpperBound
      ((fun W : ScottOpen D => mu W) '' crescentCoverFamily hD A B) c := by
    rintro _ ⟨W, ⟨s, hs, rfl⟩, rfl⟩
    exact hnone s hs
  exact (not_le_of_gt hc) (hsup.2 c hcUpper)

end ContinuousValuation
end FiniteValuationApproximable
