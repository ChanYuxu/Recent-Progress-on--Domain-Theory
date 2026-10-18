import Practice.DomainTheory.Papers.UnitIntervalRetracts.SourceFamilies
import Practice.DomainTheory.Papers.UnitIntervalRetracts.Noncontinuity
import Practice.DomainTheory.Papers.UnitIntervalRetracts.Counterexample
import Practice.DomainTheory.Papers.UnitIntervalRetracts.Splitting

/-!
# Main theorem for the sparse unit-interval counterexample

This is the public entry point for
`unit_interval_retracts_quasicontinuous_domains_style_matched_副本.tex`.
-/

set_option autoImplicit false
set_option linter.unnecessarySimpa false

namespace UnitIntervalRetracts

open Set
open AbramskyJung.Chapter2

noncomputable section

theorem P_isDcpoOrder : IsDcpoOrder P := by
  constructor
  · intro A _hA
    exact ⟨sSup A, isLUB_sSup A⟩
  · intro A B hAB hBA
    exact le_antisymm hAB hBA

/-- The complete list of properties asserted by `thm:main-counterexample`.
The `CompleteLattice P` structure is the global instance constructed in
`Lattice.lean`. -/
structure MainCounterexampleProperties : Prop where
  dcpo : IsDcpoOrder P
  quasicontinuous : IsQuasicontinuous P
  notContinuous : ¬ IsContinuousDomain P
  notQuasialgebraic : ¬ IsQuasialgebraic P
  chainsCountable : ∀ ⦃C : Set P⦄, IsChainSet C → C.Countable
  quotientScottContinuous :
    AbramskyJung.Chapter2.ScottContinuous q
  quotientSurjective : Function.Surjective q
  noIntervalOrderEmbedding : ¬ Nonempty (X ↪o P)
  noIntervalRetract :
    ¬ ∃ (r : P → X) (s : X → P),
        AbramskyJung.Chapter2.ScottContinuous r ∧
        AbramskyJung.Chapter2.ScottContinuous s ∧
        Function.LeftInverse r s

/-- Theorem `thm:main-counterexample`. -/
theorem mainCounterexample : MainCounterexampleProperties where
  dcpo := P_isDcpoOrder
  quasicontinuous := isQuasicontinuous_P
  notContinuous := not_isContinuousDomain_P
  notQuasialgebraic := not_isQuasialgebraic_P
  chainsCountable := fun {_C} hC => chain_countable hC
  quotientScottContinuous := q_scottContinuous_surjective.1
  quotientSurjective := q_scottContinuous_surjective.2
  noIntervalOrderEmbedding := no_orderEmbedding_X_to_P
  noIntervalRetract := no_scottContinuous_retract_X_of_P

/-- Corollary `cor:negative-answers`: both interval inclusion/splitting
requirements fail for the constructed quasicontinuous complete lattice. -/
theorem negativeAnswers :
    (¬ Nonempty (X ↪o P)) ∧
      ¬ ∃ (r : P → X) (s : X → P),
        AbramskyJung.Chapter2.ScottContinuous r ∧
        AbramskyJung.Chapter2.ScottContinuous s ∧
        Function.LeftInverse r s :=
  ⟨mainCounterexample.noIntervalOrderEmbedding,
    mainCounterexample.noIntervalRetract⟩

end

end UnitIntervalRetracts
