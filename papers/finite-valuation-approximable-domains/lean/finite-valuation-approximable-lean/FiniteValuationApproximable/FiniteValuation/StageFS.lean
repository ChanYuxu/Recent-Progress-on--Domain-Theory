import FiniteValuationApproximable.FiniteValuation.DirectedSup
import FiniteValuationApproximable.Abstract.FSDomain

/-!
# FS approximate identities on every finite valuation stage

This module transports the unconditional erosion construction into the
manuscript's self-contained Abramsky--Jung-compatible order API.  It thereby
discharges `FiniteStagesHaveFSApproximateIdentities` without adding any
semantic premise.
-/

set_option autoImplicit false
set_option linter.unnecessarySimpa false

universe u w

namespace FiniteValuationApproximable

open scoped Classical
open Set
open AbstractApproximation

namespace Erosion

variable {P : Type u} [Fintype P] [PartialOrder P]

/-- Convert Mathlib's `IsLUB` predicate into the local source-facing
`Chapter2.IsSup` predicate. -/
theorem chapter2IsSup_of_isLUB {D : Type u} [Preorder D]
    {A : Set D} {x : D} (h : IsLUB A x) :
    AbramskyJung.Chapter2.IsSup A x := by
  constructor
  · intro a ha
    exact h.1 ha
  · intro y hy
    exact h.2 hy

/-- Convert the local source-facing `Chapter2.IsSup` predicate into
Mathlib's `IsLUB` predicate. -/
theorem isLUB_of_chapter2IsSup {D : Type u} [Preorder D]
    {A : Set D} {x : D} (h : AbramskyJung.Chapter2.IsSup A x) :
    IsLUB A x := by
  constructor
  · intro a ha
    exact h.1 ha
  · intro y hy
    exact h.2 y hy

/-- Mathlib Scott continuity implies Scott continuity in the local
Abramsky--Jung-compatible API. -/
theorem chapter2ScottContinuous_of_scottContinuous
    {D : Type u} {E : Type u} [Preorder D] [Preorder E]
    {f : D → E} (hf : _root_.ScottContinuous f) :
    AbramskyJung.Chapter2.ScottContinuous f := by
  constructor
  · exact hf.monotone
  · intro A x hA hx
    have hm : IsLUB A x := isLUB_of_chapter2IsSup hx
    have hi : IsLUB (f '' A) (f x) := hf hA.1 hA.2 hm
    exact chapter2IsSup_of_isLUB hi

/-- The erosion time sequence is antitone. -/
theorem erosionTime_antitone : Antitone erosionTime :=
  antitone_nat_of_succ_le erosionTime_succ_le

/-- The exact erosion maps, at times `1/(n+1)`, form an FS approximate
identity in the manuscript's local abstract interface. -/
noncomputable def finiteSubprobabilityFSApproximateIdentity :
    FSApproximateIdentity (SubprobabilityVector P) where
  map n := {
    toFun := fun p => exactPhi (erosionTime n) p
    continuous := chapter2ScottContinuous_of_scottContinuous
      (exactPhi_scott (P := P) (le_of_lt (erosionTime_pos n)))
  }
  monotone := by
    intro n m hnm p
    exact exactPhi_antitone_time p
      (le_of_lt (erosionTime_pos m)) (erosionTime_antitone hnm)
  below_id := by
    intro n p
    exact exactPhi_le (erosionTime n) p
  pointwise_sup := by
    intro p
    exact chapter2IsSup_of_isLUB (erosionTime_range_isLUB p)
  finitelySeparated := by
    intro n
    simpa only [AbstractApproximation.IsFinitelySeparated,
      FinitelySeparatedFromId] using
      (exactPhi_finitelySeparated (P := P) (erosionTime_pos n))

/-- The finite stochastic simplex is a dcpo order.  Existence is the compact
finite-dimensional directed-supremum theorem; antisymmetry is the already
proved stochastic partial order. -/
theorem finiteSubprobability_isDcpoOrder :
    AbramskyJung.Chapter2.IsDcpoOrder (SubprobabilityVector P) := by
  constructor
  · intro D hD
    rcases finiteSubprobability_exists_isLUB D hD.1 hD.2 with ⟨p, hp⟩
    exact ⟨p, chapter2IsSup_of_isLUB hp⟩
  · intro p q hpq hqp
    exact le_antisymm hpq hqp

/-- Every finite stochastic simplex is an omega-continuous dcpo, derived from
its explicit FS approximate identity and directed completeness. -/
theorem finiteSubprobability_isOmegaContinuousDcpo :
    AbramskyJung.Chapter2.IsOmegaContinuousDcpo (SubprobabilityVector P) :=
  finiteSubprobabilityFSApproximateIdentity.omegaContinuousDcpo
    finiteSubprobability_isDcpoOrder

/-- In particular, every finite stochastic simplex is a continuous dcpo. -/
theorem finiteSubprobability_isContinuousDcpo :
    AbramskyJung.Chapter2.IsContinuousDcpo (SubprobabilityVector P) :=
  ⟨finiteSubprobability_isDcpoOrder,
    finiteSubprobabilityFSApproximateIdentity.continuousDomain⟩

end Erosion

/-- The finite-stage premise used by saturation is now a theorem. -/
theorem finiteStagesHaveFSApproximateIdentities :
    FiniteStagesHaveFSApproximateIdentities.{u} := by
  intro P
  exact ⟨Erosion.finiteSubprobabilityFSApproximateIdentity (P := P)⟩

/-- Unconditional form of source item `thm:saturation(i)`: the only premise
of the earlier theorem is discharged by finite-stage erosion. -/
theorem FVApproximateIdentity.saturate_unconditional
    {D : Type u} [PartialOrder D]
    (hD : AbramskyJung.Chapter2.IsContinuousDomain D)
    (A : FVApproximateIdentity.{u, w} D) :
    Nonempty (SaturatedFVApproximateIdentity.{u, w} D) :=
  A.saturate finiteStagesHaveFSApproximateIdentities hD

/-- Unconditional source-facing saturation consequence for FVA domains. -/
theorem IsFVA.saturated_unconditional
    {D : Type u} [PartialOrder D] (hD : IsFVA.{u, w} D) :
    Nonempty (SaturatedFVApproximateIdentity.{u, w} D) :=
  hD.saturated finiteStagesHaveFSApproximateIdentities

end FiniteValuationApproximable
