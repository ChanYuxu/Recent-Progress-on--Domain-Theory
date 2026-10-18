import CoreCompactSimplified.SourceDefinitions

/-!
Exact statement of the He–Zhang background dependency. A `def ... : Prop`
records a proposition and is not by itself a proof. The actual proof is
`HeZhang.secondCountableLocallyCompactDcpoSobriety` in `HeZhangProof`.
-/

set_option autoImplicit false
universe u

namespace CoreCompactSimplified

open CoreCompactNonSober

/-- He–Zhang, arXiv:2610.17759v1, Theorem 4.13. Local compactness here
is exactly the compact-saturated sandwich definition, for the intrinsic
Scott topology. This definition does not assert the theorem is proved. -/
def SecondCountableLocallyCompactDcpoSobriety : Prop :=
  ∀ (P : Type u) (order : PartialOrder P),
    letI := order
    IsDcpo P → ScottSecondCountable P → ScottLocallyCompact P → ScottSober P

end CoreCompactSimplified
