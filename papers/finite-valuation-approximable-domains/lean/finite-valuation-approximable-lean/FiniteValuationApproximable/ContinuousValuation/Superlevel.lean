import FiniteValuationApproximable.ContinuousValuation.Basic

/-!
# Strict superlevel Scott opens

This module records the order-topological part of the Jones integral.  A
strict superlevel of a bounded Scott-continuous `ENNReal`-valued function is
Scott open, and strict superlevels commute with arbitrary directed pointwise
suprema.  The latter fact is the source of directed monotone convergence for
the lower integral constructed in the subsequent modules.
-/

set_option autoImplicit false

universe u

namespace FiniteValuationApproximable
namespace ContinuousValuation

open Set
open AbramskyJung.Chapter2
open scoped ENNReal

namespace BoundedScottFunction

/-- The strict superlevel `{x | t < f x}` as a Scott open. -/
def superlevel {D : Type u} [Preorder D]
    (f : BoundedScottFunction D) (t : ℝ≥0∞) : ScottOpen D where
  carrier := {x | t < f x}
  isScottOpen := by
    constructor
    · intro x y hxy hx
      exact hx.trans_le (f.continuous.monotone hxy)
    · intro A s hA hs hts
      have hfs : IsSup (f '' A) (f s) :=
        f.continuous.maps_isSup hA hs
      by_contra hnone
      push_neg at hnone
      have htUpper : IsUpperBound (f '' A) t := by
        rintro _ ⟨x, hxA, rfl⟩
        exact not_lt.mp (hnone x hxA)
      exact (not_le_of_gt hts) (hfs.2 t htUpper)

@[simp] theorem mem_superlevel_iff {D : Type u} [Preorder D]
    (f : BoundedScottFunction D) (t : ℝ≥0∞) (x : D) :
    x ∈ superlevel f t ↔ t < f x :=
  Iff.rfl

theorem superlevel_mono {D : Type u} [Preorder D]
    {f g : BoundedScottFunction D} (hfg : f ≤ g) (t : ℝ≥0∞) :
    superlevel f t ≤ superlevel g t := by
  intro x hx
  exact hx.trans_le (hfg x)

theorem superlevel_indicator_mem_iff {D : Type u} [Preorder D]
    (U : ScottOpen D) (t : ℝ≥0∞) (x : D) :
    x ∈ superlevel (indicator U) t ↔ x ∈ U ∧ t < 1 := by
  classical
  by_cases hx : x ∈ U
  · change t < openIndicator U x ↔ x ∈ U ∧ t < 1
    rw [openIndicator_of_mem hx]
    simp [hx]
  · change t < openIndicator U x ↔ x ∈ U ∧ t < 1
    rw [openIndicator_of_not_mem hx]
    simp [hx]

/-- Strict superlevels commute with an arbitrary directed pointwise
supremum.  No countability assumption is present. -/
theorem superlevel_isSup {D : Type u} [Preorder D]
    {A : Set (BoundedScottFunction D)} (hA : DirectedSet A)
    (f : BoundedScottFunction D)
    (hf : ∀ x : D,
      IsSup ((fun g : BoundedScottFunction D => g x) '' A) (f x))
    (t : ℝ≥0∞) :
    IsSup ((fun g : BoundedScottFunction D => superlevel g t) '' A)
      (superlevel f t) := by
  constructor
  · rintro _ ⟨g, hgA, rfl⟩
    apply superlevel_mono (t := t)
    intro x
    exact (hf x).1 ⟨g, hgA, rfl⟩
  · intro V hV x hx
    have hex : ∃ g ∈ A, t < g x := by
      by_contra hnone
      push_neg at hnone
      have htUpper : IsUpperBound
          ((fun g : BoundedScottFunction D => g x) '' A) t := by
        rintro _ ⟨g, hgA, rfl⟩
        exact hnone g hgA
      exact (not_le_of_gt hx) ((hf x).2 t htUpper)
    rcases hex with ⟨g, hgA, hxg⟩
    exact hV ⟨g, hgA, rfl⟩ hxg

theorem superlevel_directed {D : Type u} [Preorder D]
    {A : Set (BoundedScottFunction D)} (hA : DirectedSet A)
    (t : ℝ≥0∞) :
    DirectedSet ((fun g : BoundedScottFunction D => superlevel g t) '' A) :=
  hA.image (fun _ _ hfg => superlevel_mono hfg t)

theorem superlevel_eq_sUnion {D : Type u} [Preorder D]
    {A : Set (BoundedScottFunction D)} (hA : DirectedSet A)
    (f : BoundedScottFunction D)
    (hf : ∀ x : D,
      IsSup ((fun g : BoundedScottFunction D => g x) '' A) (f x))
    (t : ℝ≥0∞) :
    superlevel f t =
      ScottOpen.sUnion
        ((fun g : BoundedScottFunction D => superlevel g t) '' A) :=
  IsSup.unique (superlevel_isSup hA f hf t)
    (ScottOpen.sUnion_isSup _)

theorem valuation_superlevel_isSup {D : Type u} [Preorder D]
    {A : Set (BoundedScottFunction D)} (hA : DirectedSet A)
    (f : BoundedScottFunction D)
    (hf : ∀ x : D,
      IsSup ((fun g : BoundedScottFunction D => g x) '' A) (f x))
    (mu : VSub D) (t : ℝ≥0∞) :
    IsSup
      ((fun g : BoundedScottFunction D => mu (superlevel g t)) '' A)
      (mu (superlevel f t)) := by
  simpa only [Set.image_image, Function.comp_apply] using
    mu.1.continuous.maps_isSup (superlevel_directed hA t)
      (superlevel_isSup hA f hf t)

end BoundedScottFunction

/-- Convert the set-image form of `IsSup` into an indexed `iSup` over the
membership subtype. -/
theorem isSup_image_eq_iSup_subtype {α : Type*} {A : Set α}
    (p : α → ℝ≥0∞) (s : ℝ≥0∞) (hs : IsSup (p '' A) s) :
    s = ⨆ a : A, p a.1 := by
  apply le_antisymm
  · apply hs.2
    rintro _ ⟨a, haA, rfl⟩
    exact le_iSup (fun z : A => p z.1) ⟨a, haA⟩
  · exact iSup_le fun a => hs.1 ⟨a.1, a.2, rfl⟩

end ContinuousValuation
end FiniteValuationApproximable
