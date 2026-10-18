import CoreCompactNonSober.TopologicalDefinitions

/-! Literal frame restriction, extracted from the legacy statement interface.
This background definition carries no counterexample or main-theorem claim. -/

set_option autoImplicit false
universe u

namespace CoreCompactNonSober

def RestrictionFrameIsomorphism {L : Type u} [PartialOrder L] (S : Set L) : Prop :=
  ∃ ρ : FrameHom (ScottOpens L) (ScottOpens S),
    Function.Bijective ρ ∧
      ∀ (U : ScottOpens L) (s : S), s ∈ ρ U ↔ (s : L) ∈ U

end CoreCompactNonSober
