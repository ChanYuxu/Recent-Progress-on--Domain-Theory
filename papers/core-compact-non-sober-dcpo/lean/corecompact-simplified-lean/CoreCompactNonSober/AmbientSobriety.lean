import CoreCompactNonSober.AmbientBasis
import CoreCompactNonSober.ScottSobriety

/-!
# Sobriety of the ambient Scott space

Binary joins pull a positive basic constraint back to the union of the
same constraint on the two projections. Thus joins are jointly continuous
for the ordinary product of Scott spaces. No general identification of
product Scott topologies is assumed.
-/

set_option autoImplicit false

namespace CoreCompactNonSober.Ambient

open Set TopologicalSpace

theorem height_sup_real (p q : Carrier) :
    height (p ⊔ q) = max (height p) (height q) := by
  change ((p ⊔ q).val.1 : ℝ) = max (p.val.1 : ℝ) (q.val.1 : ℝ)
  rw [height_sup_interval]
  rfl

theorem sup_preimage_constraint (c : Constraint) :
    (fun p : Carrier × Carrier ↦ p.1 ⊔ p.2) ⁻¹' constraintSet c =
      Prod.fst ⁻¹' constraintSet c ∪ Prod.snd ⁻¹' constraintSet c := by
  cases c with
  | inl e =>
    ext p
    simp only [Set.mem_preimage, Set.mem_union, constraintSet, entrySet,
      Set.mem_setOf_eq, configuration_sup, Finset.mem_union]
  | inr q =>
    ext p
    simp only [Set.mem_preimage, Set.mem_union, constraintSet, heightAbove,
      Set.mem_setOf_eq, height_sup_real, lt_max_iff]

theorem scottContinuousSup :
    @Continuous (Carrier × Carrier) Carrier
      (@instTopologicalSpaceProd Carrier Carrier
        (scottTopology Carrier) (scottTopology Carrier)) (scottTopology Carrier)
      (fun p ↦ p.1 ⊔ p.2) := by
  letI : TopologicalSpace Carrier := scottTopology Carrier
  apply basic_isTopologicalBasis.continuous_iff.mpr
  rintro _ ⟨F, rfl⟩
  simp only [basicSet, Set.preimage_iInter]
  apply isOpen_biInter_finset
  intro c _
  rw [sup_preimage_constraint]
  exact ((constraintSet_isOpen_scott c).preimage continuous_fst).union
    ((constraintSet_isOpen_scott c).preimage continuous_snd)

theorem scottSober : ScottSober Carrier :=
  scottSober_of_continuous_sup scottContinuousSup

end CoreCompactNonSober.Ambient
