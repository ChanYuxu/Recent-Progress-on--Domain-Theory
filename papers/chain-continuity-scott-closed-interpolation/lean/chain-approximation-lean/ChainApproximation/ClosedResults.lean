import ChainApproximation.HeightProperties

/-!
# Source-facing closed-approximation results

This facade packages the Scott-closed selection's predistributivity,
precontinuity and completeness separately. In a complete lattice the
precontinuity condition follows because the lower section is Scott closed.
-/

set_option autoImplicit false

universe u v

namespace ChainApproximation

open Set

def IsClosedPrecontinuous (M : Type u) [CompleteLattice M] : Prop :=
  ∀ b : M, IsScottClosed {a | ClosedBelow a b} ∧ IsLUB {a | ClosedBelow a b} b

def IsClosedDistributive (M : Type u) [CompleteLattice M] : Prop :=
  (∀ b : M, IsLUB {a | ClosedBelow a b} b) ∧
    ∀ H : Set M, IsScottClosed H → ∃ s, IsLUB H s

theorem closedPrecontinuous_of_continuous {M : Type u} [CompleteLattice M]
    (hM : IsClosedContinuous M) : IsClosedPrecontinuous M := by
  intro b
  refine ⟨closedBelow_section_scottClosed b, ?_⟩
  simpa only [hM b] using (isLUB_sSup {a : M | ClosedBelow a b})

theorem closedDistributive_of_continuous {M : Type u} [CompleteLattice M]
    (hM : IsClosedContinuous M) : IsClosedDistributive M :=
  ⟨fun b ↦ (closedPrecontinuous_of_continuous hM b).2,
    fun H _ ↦ ⟨sSup H, isLUB_sSup H⟩⟩

/-- Source `cor:closed-cont`, all selection and test-convention assertions. -/
theorem lowerSet_closed_cont {Q : Type u} [PartialOrder Q] :
    IsClosedContinuous (LowerSet Q) ∧ IsClosedPrecontinuous (LowerSet Q) ∧
      IsClosedDistributive (LowerSet Q) ∧ IsClosedContinuousPlus (LowerSet Q) :=
  ⟨lowerSet_closedContinuous, closedPrecontinuous_of_continuous lowerSet_closedContinuous,
    closedDistributive_of_continuous lowerSet_closedContinuous, lowerSet_closedContinuousPlus⟩

/-- The O-invariance used in the source's answer to Erne: isotone images
of nonempty directed sets remain nonempty and directed. -/
theorem NonemptyDirected.monotone_image {P : Type u} {Q : Type v}
    [PartialOrder P] [PartialOrder Q] {D : Set P} (hD : NonemptyDirected D)
    (f : P → Q) (hf : Monotone f) : NonemptyDirected (f '' D) :=
  ⟨hD.1.image f, hD.2.mono_comp (fun _ _ hab ↦ hf hab)⟩

namespace HeightTwo

theorem twoB_ne_bot : twoB ≠ ⊥ := by
  intro hF
  have h : b 0 ∈ (⊥ : LowerSet HeightTwo) := hF ▸ (show b 0 ∈ twoB from Set.mem_insert _ _)
  exact h

theorem relations_incomparablePlus :
    (∃ A E : LowerSet HeightTwo, ClosedBelowPlus A E ∧ ¬ WayBelow A E) ∧
      ∃ A E : LowerSet HeightTwo, WayBelow A E ∧ ¬ ClosedBelowPlus A E :=
  ⟨⟨B, ⊤, (closedBelowPlus_iff B ⊤).mpr (Or.inl B_closedBelow_top), B_not_wayBelow_top⟩,
    ⟨twoB, twoB, twoB_wayBelow_self, fun h ↦ twoB_not_closedBelow_self
      ((closedBelowPlus_iff_of_ne_bot_left twoB_ne_bot).mp h)⟩⟩

/-- Source `thm:closed-counter`, including the D-vee-distributive assertion. -/
theorem closed_counter_full :
    IsCountablyBased (LowerSet HeightTwo) ∧ IsCompletelyDistributive (LowerSet HeightTwo) ∧
      IsAlgebraic (LowerSet HeightTwo) ∧ IsClosedPrecontinuous (LowerSet HeightTwo) ∧
      IsClosedDistributive (LowerSet HeightTwo) ∧
      ClosedBelow B (⊤ : LowerSet HeightTwo) ∧
      ¬ RelComp ClosedBelow ClosedBelow B (⊤ : LowerSet HeightTwo) :=
  ⟨lowerSet_countablyBased, lowerSet_completelyDistributive, lowerSet_algebraic,
    closedPrecontinuous_of_continuous lowerSet_closedContinuous,
    closedDistributive_of_continuous lowerSet_closedContinuous, B_closedBelow_top, B_no_closed_intermediate⟩

/-- Source `cor:two-questions`: the same complete lattice satisfies both
continuity conventions but fails ordinary interpolation under both. -/
theorem two_questions_counterexample :
    IsCountablyBased (LowerSet HeightTwo) ∧ IsCompletelyDistributive (LowerSet HeightTwo) ∧
      IsAlgebraic (LowerSet HeightTwo) ∧ IsClosedDistributive (LowerSet HeightTwo) ∧
      IsClosedContinuousPlus (LowerSet HeightTwo) ∧ B ≠ ⊥ ∧
      ¬ Interpolates (ClosedBelow (M := LowerSet HeightTwo)) ∧
      ¬ Interpolates (ClosedBelowPlus (M := LowerSet HeightTwo)) :=
  ⟨lowerSet_countablyBased, lowerSet_completelyDistributive, lowerSet_algebraic,
    closedDistributive_of_continuous lowerSet_closedContinuous, lowerSet_closedContinuousPlus,
    B_ne_bot, closedBelow_does_not_interpolate, closedBelowPlus_does_not_interpolate⟩

end HeightTwo
end ChainApproximation
