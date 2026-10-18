import FiniteValuationApproximable.FiniteBC
import FiniteValuationApproximable.FiniteValuation.Consequences

/-!
# Unconditional finite bounded-complete FVA theorem

This module discharges the two semantic premises left explicit in
`FiniteBC.lean`.  A finite bounded-complete order has a least element.  The
order isomorphism

`ProbabilityVector B ≃o SubprobabilityVector (WithoutPoint bot)`

then transports directed suprema to the finite stochastic simplex, where
`directedUpperMassApproximation` proves that every upper-set mass coordinate
attains the correct directed supremum.  Consequently the threshold
retraction in the manuscript is genuinely Scott-continuous, and every
finite bc-domain is FVA without an extra premise.
-/

set_option autoImplicit false
set_option linter.unnecessarySimpa false

universe u

namespace FiniteValuationApproximable

open Set
open SubprobabilityVector

section ProbabilityCoordinates

variable {B : Type u} [Fintype B] [PartialOrder B]

/-- Upper-set masses on normalized probabilities over a finite poset with a
least element preserve all directed suprema. -/
theorem probabilityUpperMassPreservesDirectedSuprema_of_least
    (bot : B) (hbot : ∀ x : B, bot ≤ x) :
    ProbabilityUpperMassPreservesDirectedSuprema B := by
  intro A p hA hp U
  by_cases hbotU : bot ∈ U
  · have hU : (U : Set B) = Set.univ := by
      apply Set.eq_univ_of_forall
      intro x
      exact U.upper (hbot x) hbotU
    have hmass (q : ProbabilityVector B) : upperMass q.1 U = 1 := by
      rw [show U = ⟨Set.univ, isUpperSet_univ⟩ from UpperSet.ext hU]
      simpa [upperMass] using ProbabilityVector.totalMass_eq_one q
    have himage :
        ((fun q : ProbabilityVector B => upperMass q.1 U) '' A) =
          ({1} : Set Real) := by
      ext z
      constructor
      · rintro ⟨q, hqA, rfl⟩
        simp [hmass q]
      · intro hz
        have hz1 : z = 1 := by simpa using hz
        rcases hA.1 with ⟨q, hqA⟩
        exact ⟨q, hqA, by simpa [hz1] using hmass q⟩
    rw [himage, hmass p]
    exact AbramskyJung.Chapter2.isSup_singleton 1
  · classical
    letI withoutPointFintype : Fintype (WithoutPoint bot) :=
      Subtype.fintype fun x : B => x ≠ bot
    let e := probabilityOrderIso bot hbot
    let U' : UpperSet (WithoutPoint bot) := restrictUpperToWithout bot U
    have heA : LocalDirectedSet (e '' A) :=
      AbramskyJung.Chapter2.DirectedSet.image e.monotone hA
    have hep : LocalIsSup (e '' A) (e p) :=
      (orderIso_scottContinuous e).maps_isSup hA hp
    have hLUB : IsLUB (e '' A) (e p) :=
      Erosion.isLUB_of_chapter2IsSup hep
    have happrox := Erosion.directedUpperMassApproximation
      (P := WithoutPoint bot) (e '' A) (e p) heA.1 heA.2 hLUB
    have hmass (q : ProbabilityVector B) :
        upperMass (e q) U' = upperMass q.1 U := by
      change upperMass (restrictProbability bot q) U' = upperMass q.1 U
      rw [← upperMass_addMissingMass_of_bot_notMem bot
        (restrictProbability bot q) U hbotU]
      simp
    constructor
    · rintro _ ⟨q, hqA, rfl⟩
      exact hp.1 hqA U
    · intro c hc
      by_contra hnot
      have hcp : c < upperMass p.1 U := lt_of_not_ge hnot
      let eps : Real := (upperMass p.1 U - c) / 2
      have heps : 0 < eps := by
        dsimp only [eps]
        linarith
      rcases happrox eps heps with ⟨q, hqA, hq⟩
      rcases hqA with ⟨r, hrA, rfl⟩
      have hclose := hq U'
      rw [hmass p, hmass r] at hclose
      have hrc : upperMass r.1 U ≤ c := hc ⟨r, hrA, rfl⟩
      dsimp only [eps] at hclose
      linarith

end ProbabilityCoordinates

section FiniteBc

variable {B : Type u} [Fintype B] [PartialOrder B] [Nonempty B]

/-- Source lemma `lem:finite-bc-fva`: every finite bounded-complete domain
belongs to `FVA`.  All directed-supremum and finite-stage inputs are proved
inside this standalone development. -/
theorem finite_bc_isFVA (hBC : IsBoundedCompleteOrder B) :
    IsFVA.{u, u} B := by
  let bot : B := boundedCompleteLeast hBC
  have hbot : ∀ x : B, bot ≤ x := boundedCompleteLeast_isLeast hBC
  exact finite_bc_isFVA_conditional
    finiteStagesAreContinuousDcpos bot hbot hBC
    (probabilityUpperMassPreservesDirectedSuprema_of_least bot hbot)

end FiniteBc

end FiniteValuationApproximable
