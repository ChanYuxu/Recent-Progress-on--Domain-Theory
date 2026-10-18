import CoreCompactSimplified.AmbientSource
import CoreCompactSimplified.Transfer
import CoreCompactSimplified.AppendixSource
import CoreCompactSimplified.ConstructionBridge
import CoreCompactSimplified.ExternalStatements
import CoreCompactSimplified.HeZhangProof

/-!
The new manuscript's actual construction and transfer proof.

`main_core` retains the earlier core-only interface. `main_of_heZhang` is the
conditional assembly helper. The source-facing `main_theorem` below supplies
the now-proved He–Zhang theorem and proves the full printed conclusion with
no extra premise, including the non-local-compactness clause.
-/

set_option autoImplicit false
universe u

namespace CoreCompactSimplified

open Set CoreCompactNonSober CoreCompactNonSober.Ambient

/-- Everything in the printed main conclusion except non-local-compactness,
with all transfer assertions and the actual sub-dcpo made explicit. -/
structure MainCoreConclusion {L : Type u} [CompleteLattice L] (D : Set L) : Prop
    extends TransferConclusion D where
  proper : D ⊂ Set.univ
  subdcpo : IsSubDcpo D
  ambient_compact : ScottCompact L
  ambient_secondCountable : ScottSecondCountable L
  ambient_locallyCompact : ScottLocallyCompact L
  ambient_coreCompact : ScottCoreCompact L
  ambient_sober : ScottSober L

/-- The generic transfer theorem is instantiated with the literal
zero-layer/recursive-packet union, whose two properties are proved rather
than assumed. -/
theorem construction_transfer : TransferConclusion recursiveSubset :=
  transfer carrier_isDcpo Ambient.scottSecondCountable Ambient.scottCoreCompact
    recursive_subset_isSubDcpo recursive_bottom_mem recursive_top_not_mem
    recursive_lowerNeighborhoodApproximation recursive_commonLowerWitness

theorem construction_main_core : MainCoreConclusion recursiveSubset where
  toTransferConclusion := construction_transfer
  proper := recursive_proper
  subdcpo := recursive_subset_isSubDcpo
  ambient_compact := Ambient.scottCompact
  ambient_secondCountable := Ambient.scottSecondCountable
  ambient_locallyCompact := Ambient.scottLocallyCompact
  ambient_coreCompact := Ambient.scottCoreCompact
  ambient_sober := ambient_sober

/-- The earlier unconditional core existence theorem. Its intentionally
smaller conclusion remains separate from the full `MainStatement`. -/
theorem main_core :
    ∃ (L : Type) (lattice : CompleteLattice L),
      letI := lattice
      ∃ D : Set L, MainCoreConclusion D :=
  ⟨Carrier, inferInstance, recursiveSubset, construction_main_core⟩

/-- The source corollary's conditional assembly argument, retained as a
helper. The unconditional source wrapper below supplies the proved theorem. -/
theorem transfer_not_locallyCompact_of_heZhang
    {L : Type u} [PartialOrder L] {D : Set L}
    (hHeZhang : SecondCountableLocallyCompactDcpoSobriety.{u})
    (h : TransferConclusion D) : ¬ ScottLocallyCompact D := by
  intro hlc
  exact h.not_sober (hHeZhang D inferInstance h.dcpo h.secondCountable hlc)

/-- The earlier conditional interface, retained for compatibility and to
make the assembly dependency explicit. -/
theorem corollary_not_locallyCompact_of_heZhang
    {L : Type u} [PartialOrder L] [OrderBot L] [OrderTop L] {D : Set L}
    (hHeZhang : SecondCountableLocallyCompactDcpoSobriety.{u})
    (hL : IsDcpo L) (hsecond : ScottSecondCountable L) (hcore : ScottCoreCompact L)
    (hD : IsSubDcpo D) (hbot : (⊥ : L) ∈ D) (htop : (⊤ : L) ∉ D)
    (happrox : LowerNeighborhoodApproximation D) (hcommon : CommonLowerWitness D) :
    ¬ ScottLocallyCompact D :=
  transfer_not_locallyCompact_of_heZhang hHeZhang
    (transfer hL hsecond hcore hD hbot htop happrox hcommon)

/-- The exact source corollary, with no additional background assumption.
He–Zhang Theorem 4.13 is supplied by its actual Lean proof. -/
theorem corollary_not_locallyCompact
    {L : Type u} [PartialOrder L] [OrderBot L] [OrderTop L] {D : Set L}
    (hL : IsDcpo L) (hsecond : ScottSecondCountable L) (hcore : ScottCoreCompact L)
    (hD : IsSubDcpo D) (hbot : (⊥ : L) ∈ D) (htop : (⊤ : L) ∉ D)
    (happrox : LowerNeighborhoodApproximation D) (hcommon : CommonLowerWitness D) :
    ¬ ScottLocallyCompact D :=
  corollary_not_locallyCompact_of_heZhang
    HeZhang.secondCountableLocallyCompactDcpoSobriety
    hL hsecond hcore hD hbot htop happrox hcommon

/-- Conditional assembly of the full conclusion. It is applied below to the
proved background theorem, not left as a premise of the final result. -/
theorem construction_main_of_heZhang
    (hHeZhang : SecondCountableLocallyCompactDcpoSobriety.{0}) :
    MainConclusion recursiveSubset where
  proper := recursive_proper
  subdcpo := recursive_subset_isSubDcpo
  dcpo := construction_transfer.dcpo
  ambient_compact := Ambient.scottCompact
  ambient_secondCountable := Ambient.scottSecondCountable
  ambient_locallyCompact := Ambient.scottLocallyCompact
  ambient_coreCompact := Ambient.scottCoreCompact
  ambient_sober := ambient_sober
  retained_meetContinuous := construction_transfer.meetContinuous
  retained_compact := construction_transfer.compact
  retained_secondCountable := construction_transfer.secondCountable
  retained_coreCompact := construction_transfer.coreCompact
  retained_not_sober := construction_transfer.not_sober
  retained_not_locallyCompact := transfer_not_locallyCompact_of_heZhang hHeZhang construction_transfer
  restriction := construction_transfer.restriction
  closed_restriction := construction_transfer.closed_restriction
  not_orderIso := construction_transfer.not_orderIso

/-- The earlier conditional main assembly helper, retained for compatibility. -/
theorem main_of_heZhang (hHeZhang : SecondCountableLocallyCompactDcpoSobriety.{0}) :
    MainStatement :=
  ⟨Carrier, inferInstance, recursiveSubset, construction_main_of_heZhang hHeZhang⟩

/-- The full printed conclusion for the actual recursive subset. No external
proposition or background theorem is assumed. -/
theorem construction_main : MainConclusion recursiveSubset :=
  construction_main_of_heZhang HeZhang.secondCountableLocallyCompactDcpoSobriety

/-- The complete source main theorem, with its non-local-compactness clause
and with no extra premise. All witnesses and mathematical dependencies are
given by actual Lean definitions and proofs. -/
theorem main_theorem : MainStatement :=
  ⟨Carrier, inferInstance, recursiveSubset, construction_main⟩

/-- Explicit witness to the source's `C_sigma` non-uniqueness consequence.
No ambiguous universe-wide uniqueness definition is substituted. -/
theorem locallyCompact_sober_closedLattice_counterexample :
    ∃ (L : Type) (order : PartialOrder L),
      letI := order
      IsDcpo L ∧ ScottLocallyCompact L ∧ ScottSober L ∧
      ∃ (D : Type) (orderD : PartialOrder D),
        letI := orderD
        IsDcpo D ∧ Nonempty (ScottCloseds L ≃o ScottCloseds D) ∧
          ¬ Nonempty (L ≃o D) := by
  refine ⟨Carrier, inferInstance, carrier_isDcpo, Ambient.scottLocallyCompact,
    ambient_sober, recursiveSubset, inferInstance, construction_transfer.dcpo, ?_,
    construction_transfer.not_orderIso⟩
  obtain ⟨e, _⟩ := construction_transfer.closed_restriction
  exact ⟨e⟩

end CoreCompactSimplified
