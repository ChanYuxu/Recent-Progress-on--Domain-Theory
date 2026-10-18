import CoreCompactSimplified.MainTheorems
import CoreCompactSimplified.OrderTransport

set_option autoImplicit false
universe u v

namespace CoreCompactSimplified

open Set CoreCompactNonSober CoreCompactNonSober.Ambient

/-- The introduction's definition, with an independently quantified target
universe. The negative result below supplies a witness in every universe. -/
def CSigmaUnique (P : Type u) [PartialOrder P] : Prop :=
  ∀ (Q : Type v) (order : PartialOrder Q),
    letI := order
    IsDcpo Q → Nonempty (ScottCloseds P ≃o ScottCloseds Q) → Nonempty (P ≃o Q)

/-- First unnumbered consequence of `thm:main`; no external sobriety
theorem is needed for the negative answer to Jia's question. -/
theorem coreCompact_meetContinuous_not_sober :
    ∃ (D : Type) (order : PartialOrder D),
      letI := order
      IsDcpo D ∧ MeetContinuous D ∧ ScottCompact D ∧ ScottSecondCountable D ∧
        ScottCoreCompact D ∧ ¬ ScottSober D :=
  ⟨recursiveSubset, inferInstance, construction_transfer.dcpo,
    construction_transfer.meetContinuous, construction_transfer.compact,
    construction_transfer.secondCountable, construction_transfer.coreCompact,
    construction_transfer.not_sober⟩

/-- The exact negative `C_sigma`-uniqueness assertion. `ULift` ensures this
is not merely failure against dcpos in the small universe of the example. -/
theorem ambient_not_CsigmaUnique : ¬ CSigmaUnique.{0, v} Carrier := by
  intro hUnique
  let Q : Type v := ULift.{v} recursiveSubset
  let e : recursiveSubset ≃o Q := ULift.orderIso.symm
  have hQ : IsDcpo Q := orderIso_isDcpo e construction_transfer.dcpo
  obtain ⟨c, _⟩ := construction_transfer.closed_restriction
  obtain ⟨hiso⟩ := hUnique Q inferInstance hQ ⟨c.trans (closedOrderIso e)⟩
  exact construction_transfer.not_orderIso ⟨hiso.trans e.symm⟩

/-- Second unnumbered consequence of `thm:main`, uniformly in the target
universe appearing in the source's "every dcpo Q" definition. -/
theorem locallyCompact_sober_not_CsigmaUnique :
    ∃ (L : Type) (order : PartialOrder L),
      letI := order
      IsDcpo L ∧ ScottLocallyCompact L ∧ ScottSober L ∧ ¬ CSigmaUnique.{0, v} L :=
  ⟨Carrier, inferInstance, carrier_isDcpo, Ambient.scottLocallyCompact, ambient_sober,
    ambient_not_CsigmaUnique⟩

end CoreCompactSimplified
