import Practice.DomainTheory.Papers.RBFunctionSpace.Target

/-!
# The RB function-space characterization

This file formalizes `thm:universal-target` and
`thm:rb-characterization`.  It intentionally stops before the manuscript's
countably based uniform test and before every FS-domain result.
-/

set_option autoImplicit false
set_option linter.unnecessarySimpa false

universe u v

namespace RBFunctionSpace

open Set
open AbramskyJung.Chapter2

variable {X : Type u} [PartialOrder X]

/-- `thm:universal-target`: continuity of `[X → A_X]` already forces `X`
to be an RB-domain. -/
theorem universalTarget
    (hX : IsDomain X)
    (hFunAX : HasContinuousFunctionSpace X (AX X)) :
    IsRBDomain X := by
  classical
  have hFunEX : HasContinuousFunctionSpace X (EX X) :=
    AbramskyJung.Chapter3.theorem_3_1_4_retract_continuous_domain
      (AX.functionSpaceRetract (X := X)) hFunAX
  have hCompact : IsScottCompact X := by
    rcases
        continuous_functionSpace_compact_or_pointedComponents
          hX AX.isDomain hFunAX with
      hCompact | hPointedComponents
    · exact hCompact
    · exact False.elim
        (AX.not_disjointUnionOfPointedDomains hPointedComponents)
  let openCover : Set (Set X) :=
    {U | ∃ p : X × X,
      p.1 ≪ p.2 ∧ U = wayBelowUpper p.2}
  have hOpenCover :
      ∀ U ∈ openCover, ScottOpen U := by
    intro U hU
    rcases hU with ⟨p, _, rfl⟩
    exact scottOpen_wayBelowUpper hX.2.2 p.2
  have hOpenCoverCovers :
      Set.univ ⊆ ⋃₀ openCover := by
    intro x _
    rcases
        (continuous_twoStepApproximants_directed hX.2.2 x).1 with
      ⟨u, v, huv, hvx⟩
    exact
      Set.mem_sUnion_of_mem hvx
        ⟨(u, v), huv, rfl⟩
  rcases hCompact openCover hOpenCover hOpenCoverCovers with
    ⟨finiteCover, hFiniteSub, hFinite, hFiniteCovers⟩
  have hOpenWitness :
      ∀ U ∈ finiteCover,
        ∃ p : X × X,
          p.1 ≪ p.2 ∧ U = wayBelowUpper p.2 := by
    intro U hU
    exact hFiniteSub hU
  let selectedPair :
      {U : Set X // U ∈ finiteCover} → X × X :=
    fun U => Classical.choose (hOpenWitness U.1 U.2)
  have selectedPair_wayBelow :
      ∀ U : {U : Set X // U ∈ finiteCover},
        (selectedPair U).1 ≪ (selectedPair U).2 := by
    intro U
    exact
      (Classical.choose_spec (hOpenWitness U.1 U.2)).1
  have selectedOpen_eq :
      ∀ U : {U : Set X // U ∈ finiteCover},
        U.1 = wayBelowUpper (selectedPair U).2 := by
    intro U
    exact
      (Classical.choose_spec (hOpenWitness U.1 U.2)).2
  let pairSet : Set (X × X) :=
    Set.range selectedPair
  letI : Finite {U : Set X // U ∈ finiteCover} :=
    Set.finite_coe_iff.mp hFinite
  have hPairSetFinite : pairSet.Finite :=
    Set.finite_range selectedPair
  let requirementCover : FiniteRequirementCover hX :=
    { pairs := pairSet
      finite_pairs := hPairSetFinite
      wayBelow_pairs := by
        intro p hp
        rcases hp with ⟨U, rfl⟩
        exact selectedPair_wayBelow U
      covers := by
        intro x
        have hxUnion :
            x ∈ ⋃₀ finiteCover :=
          hFiniteCovers (Set.mem_univ x)
        rcases Set.mem_sUnion.mp hxUnion with
          ⟨U, hUFinite, hxU⟩
        let U' : {W : Set X // W ∈ finiteCover} :=
          ⟨U, hUFinite⟩
        refine
          ⟨selectedPair U', ⟨U', rfl⟩, ?_⟩
        have hxSelected :
            x ∈ wayBelowUpper (selectedPair U').2 := by
          rw [← selectedOpen_eq U']
          exact hxU
        exact hxSelected }
  exact finiteCoverExtraction hX hFunEX requirementCover

/-- The forward implication of `thm:rb-characterization`, universe
polymorphic in the target domain. -/
theorem rb_implies_continuous_functionSpace
    (hX : IsDomain X) (hRB : IsRBDomain X)
    {E : Type v} [PartialOrder E] (hE : IsDomain E) :
    HasContinuousFunctionSpace X E :=
  rb_functionSpace_continuous hX hE hRB

/-- `thm:rb-characterization`.  The internal quantifier ranges over target
domains in the same universe as `X`; the preceding theorem supplies the
fully universe-polymorphic forward direction. -/
theorem rbCharacterization
    (hX : IsDomain X) :
    IsRBDomain X ↔
      ∀ (E : Type u) [PartialOrder E],
        IsDomain E → HasContinuousFunctionSpace X E := by
  constructor
  · intro hRB E _ hE
    exact rb_implies_continuous_functionSpace hX hRB hE
  · intro hAll
    have hFunAX :
        HasContinuousFunctionSpace X (AX X) :=
      hAll (AX X) AX.isDomain
    exact universalTarget hX hFunAX

/-- The “moreover” clause of `thm:rb-characterization`. -/
theorem singleTargetCharacterization
    (hX : IsDomain X) :
    HasContinuousFunctionSpace X (AX X) → IsRBDomain X :=
  universalTarget hX

end RBFunctionSpace
