import ChainApproximation.Main
import Mathlib.Order.UpperLower.Closure

/-!
# Approximation by Scott-closed test sets

Source Section 4, equation (closed-test) and `lem:empty-convention`.
Both test conventions retain the actual universal quantification over
Scott-closed sets; the finite-upper characterization is proved separately.
-/

set_option autoImplicit false

universe u

namespace ChainApproximation

open Set

variable {M : Type u} [CompleteLattice M]

def ClosedBelow (a b : M) : Prop :=
  ∀ H : Set M, IsScottClosed H → b ≤ sSup H → a ∈ H

def ClosedBelowPlus (a b : M) : Prop :=
  ∀ H : Set M, H.Nonempty → IsScottClosed H → b ≤ sSup H → a ∈ H

def IsClosedContinuous (M : Type u) [CompleteLattice M] : Prop :=
  ∀ b : M, sSup {a | ClosedBelow a b} = b

def IsClosedContinuousPlus (M : Type u) [CompleteLattice M] : Prop :=
  ∀ b : M, sSup {a | ClosedBelowPlus a b} = b

theorem completeLattice_dcpo : IsDcpo M := fun D _ ↦ ⟨sSup D, isLUB_sSup D⟩

theorem scottClosed_empty {P : Type u} [PartialOrder P] : IsScottClosed (∅ : Set P) := by
  refine ⟨isLowerSet_empty, ?_⟩
  intro D hD hne _ _
  exact False.elim (Set.not_nonempty_empty (hne.1.mono hD))

theorem scottClosed_Iic (b : M) : IsScottClosed (Set.Iic b) :=
  ⟨isLowerSet_Iic b, fun _ hD _ _ hs ↦ hs.2 hD⟩

theorem ClosedBelow.le {a b : M} (hab : ClosedBelow a b) : a ≤ b :=
  hab (Set.Iic b) (scottClosed_Iic b) (le_sSup le_rfl)

theorem ClosedBelowPlus.le {a b : M} (hab : ClosedBelowPlus a b) : a ≤ b :=
  hab (Set.Iic b) Set.nonempty_Iic (scottClosed_Iic b) (le_sSup le_rfl)

theorem ClosedBelow.mono {a' a b b' : M} (haa : a' ≤ a) (hab : ClosedBelow a b)
    (hbb : b ≤ b') : ClosedBelow a' b' :=
  fun H hH hb'H ↦ hH.1 haa (hab H hH (hbb.trans hb'H))

theorem ClosedBelowPlus.mono {a' a b b' : M} (haa : a' ≤ a) (hab : ClosedBelowPlus a b)
    (hbb : b ≤ b') : ClosedBelowPlus a' b' :=
  fun H hne hH hb'H ↦ hH.1 haa (hab H hne hH (hbb.trans hb'H))

theorem closedBelow_not_bot (a : M) : ¬ ClosedBelow a ⊥ := by
  intro ha
  exact ha ∅ scottClosed_empty (by simp)

/-- Source `lem:empty-convention`, the exact relation equality. -/
theorem closedBelowPlus_iff (a b : M) :
    ClosedBelowPlus a b ↔ ClosedBelow a b ∨ (a = ⊥ ∧ b = ⊥) := by
  classical
  constructor
  · intro hab
    by_cases hb : b = ⊥
    · exact Or.inr ⟨le_bot_iff.mp (hb ▸ hab.le), hb⟩
    · left
      intro H hH hbH
      have hne : H.Nonempty := by
        by_contra hn
        have hHe : H = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
        rw [hHe, sSup_empty] at hbH
        exact hb (le_bot_iff.mp hbH)
      exact hab H hne hH hbH
  · rintro (hab | ⟨rfl, rfl⟩)
    · exact fun H _ hH hbH ↦ hab H hH hbH
    · intro H hne hH _
      obtain ⟨x, hx⟩ := hne
      exact hH.1 bot_le hx

theorem closedBelowPlus_iff_of_ne_bot_left {a b : M} (ha : a ≠ ⊥) :
    ClosedBelowPlus a b ↔ ClosedBelow a b := by
  rw [closedBelowPlus_iff]
  simp [ha]

theorem closedBelowPlus_iff_of_ne_bot_right {a b : M} (hb : b ≠ ⊥) :
    ClosedBelowPlus a b ↔ ClosedBelow a b := by
  rw [closedBelowPlus_iff]
  simp [hb]

theorem closedContinuous_iff_plus : IsClosedContinuous M ↔ IsClosedContinuousPlus M := by
  have hzero : sSup {a : M | ClosedBelow a ⊥} = ⊥ := by
    have heq : {a : M | ClosedBelow a ⊥} = ∅ := by ext a; simp [closedBelow_not_bot]
    rw [heq, sSup_empty]
  have hzeroPlus : sSup {a : M | ClosedBelowPlus a ⊥} = ⊥ := by
    apply le_antisymm
    · apply sSup_le
      intro a ha
      exact ha.le
    · exact bot_le
  constructor
  · intro h b
    by_cases hb : b = ⊥
    · subst b
      exact hzeroPlus
    · have heq : {a : M | ClosedBelowPlus a b} = {a | ClosedBelow a b} := by
        ext a
        exact closedBelowPlus_iff_of_ne_bot_right hb
      rw [heq]
      exact h b
  · intro h b
    by_cases hb : b = ⊥
    · subst b
      exact hzero
    · have heq : {a : M | ClosedBelow a b} = {a | ClosedBelowPlus a b} := by
        ext a
        exact (closedBelowPlus_iff_of_ne_bot_right hb).symm
      rw [heq]
      exact h b

theorem closed_intermediate_iff_plus {a b : M} (ha : a ≠ ⊥) :
    RelComp ClosedBelow ClosedBelow a b ↔ RelComp ClosedBelowPlus ClosedBelowPlus a b := by
  constructor
  · rintro ⟨c, hac, hcb⟩
    exact ⟨c, (closedBelowPlus_iff a c).mpr (Or.inl hac),
      (closedBelowPlus_iff c b).mpr (Or.inl hcb)⟩
  · rintro ⟨c, hac, hcb⟩
    have hc : c ≠ ⊥ := fun hc ↦ ha (le_bot_iff.mp (hc ▸ hac.le))
    exact ⟨c, (closedBelowPlus_iff_of_ne_bot_left ha).mp hac,
      (closedBelowPlus_iff_of_ne_bot_left hc).mp hcb⟩

theorem closed_noninterpolating_iff_plus {a b : M} (ha : a ≠ ⊥) :
    (ClosedBelow a b ∧ ¬ RelComp ClosedBelow ClosedBelow a b) ↔
      (ClosedBelowPlus a b ∧ ¬ RelComp ClosedBelowPlus ClosedBelowPlus a b) := by
  rw [closedBelowPlus_iff_of_ne_bot_left ha, ← closed_intermediate_iff_plus ha]

end ChainApproximation
