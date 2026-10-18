import FiniteValuationApproximable.External.Gierz
import FiniteValuationApproximable.FiniteValuation.Consequences

/-!
# Unconditional local clauses of the main theorem

This module collects the parts of source theorem `thm:main` that no longer
depend on randomized rounding or on the arbitrary-dcpo valuation monad:

* every FVA object is pointed, countably based, and an FS-domain;
* every finite subprobability generator is FVA;
* the empty finite generator is a genuine terminal object for the local
  Scott-continuous-map interface; and
* FVA is closed under Scott-continuous retracts.
-/

set_option autoImplicit false

universe u v

namespace FiniteValuationApproximable

/-- The empty finite poset whose subprobability simplex is the one-point
terminal dcpo used by the manuscript. -/
def emptyFinitePoset : FinitePoset.{u} where
  carrier := PEmpty.{u + 1}
  fintype := inferInstance
  partialOrder := inferInstance

/-- There is exactly one finite subprobability vector on the empty carrier. -/
theorem emptyFiniteStage_subsingleton :
    Subsingleton emptyFinitePoset.VSub := by
  constructor
  intro mu nu
  apply SubprobabilityVector.ext
  intro x
  exact x.elim

/-- Canonical point of the empty finite stage. -/
def emptyFiniteStagePoint : emptyFinitePoset.VSub :=
  zeroVector PEmpty

/-- The unique Scott-continuous map into the empty finite stage. -/
def terminalMap (D : Type v) [Preorder D] :
    AbramskyJung.Chapter3.ContFun D emptyFinitePoset.VSub where
  toFun := fun _ => emptyFiniteStagePoint
  continuous := AbramskyJung.Chapter2.const_scottContinuous
    emptyFiniteStagePoint

/-- Universal uniqueness of the terminal map. -/
theorem terminalMap_unique
    (D : Type v) [Preorder D]
    (f : AbramskyJung.Chapter3.ContFun D emptyFinitePoset.VSub) :
    f = terminalMap D := by
  apply AbramskyJung.Chapter3.ContFun.ext_apply
  intro x
  exact emptyFiniteStage_subsingleton.elim _ _

/-- The terminal dcpo belongs to FVA. -/
theorem terminal_isFVA : IsFVA.{u, u} emptyFinitePoset.VSub :=
  finiteStage_isFVA_unconditional emptyFinitePoset

/-- Every inhabited subsingleton partial order is a continuous retract of
the terminal finite valuation stage.  This is the uniform endpoint used for
the empty-source or empty-target cases of the finite-polytope theorem. -/
noncomputable def subsingletonTerminalRetraction
    (D : Type u) [PartialOrder D] [Subsingleton D] [Nonempty D] :
    AbramskyJung.Chapter3.ContinuousSectionRetractionPair
      D emptyFinitePoset.VSub where
  s := fun _ => emptyFiniteStagePoint
  r := fun _ => Classical.arbitrary D
  monotone_s := by
    intro x y hxy
    exact le_rfl
  monotone_r := by
    intro x y hxy
    exact le_of_eq (Subsingleton.elim _ _)
  retract := by
    intro x
    exact Subsingleton.elim _ _
  continuous_s := AbramskyJung.Chapter2.const_scottContinuous
    emptyFiniteStagePoint
  continuous_r := AbramskyJung.Chapter2.const_scottContinuous
    (Classical.arbitrary D)

/-- An inhabited subsingleton partial order is FVA, with no domain-theoretic
or finite-stage premise left to the caller. -/
theorem subsingleton_isFVA
    (D : Type u) [PartialOrder D] [Subsingleton D] [Nonempty D] :
    IsFVA.{u, u} D :=
  IsFVA.retract (subsingletonTerminalRetraction D) terminal_isFVA

/-- Exact objectwise content of clause (i) of source theorem `thm:main`. -/
theorem fva_pointed_countablyBased_fs
    {D : Type u} [PartialOrder D] (hD : IsFVA.{u, u} D) :
    AbramskyJung.Chapter3.HasLeastElement D ∧
      AbramskyJung.Chapter2.IsOmegaContinuousDcpo D ∧
      IsFSDomain D :=
  ⟨hD.hasLeastElement,
    hD.isOmegaContinuousDcpo_unconditional,
    hD.isFSDomain_unconditional⟩

/-- Local package used verbatim by the final main-theorem assembly. -/
theorem thm_main_local_clauses :
    (∀ P : FinitePoset.{u}, IsFVA.{u, u} P.VSub) ∧
      IsFVA.{u, u} emptyFinitePoset.VSub ∧
      (∀ {D E : Type u} [PartialOrder D] [PartialOrder E],
        AbramskyJung.Chapter3.ContinuousSectionRetractionPair D E →
        IsFVA.{u, u} E → IsFVA.{u, u} D) := by
  refine ⟨finiteStage_isFVA_unconditional, terminal_isFVA, ?_⟩
  intro D E _ _ sr hE
  exact IsFVA.retract sr hE

end FiniteValuationApproximable
