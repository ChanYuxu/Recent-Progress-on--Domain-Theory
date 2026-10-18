import CoreCompactNonSober.DefinitionChecks
import Mathlib.Topology.Constructions.SumProd

/-!
# Sobriety from joint Scott continuity of binary joins

This is the irreducible-closed-set argument used in
`prop:ambient-properties`. The continuity hypothesis uses the ordinary
product of the two Scott topologies, not the Scott topology of the product
order. These need not agree in general.
-/

set_option autoImplicit false

universe u

namespace CoreCompactNonSober

open Set TopologicalSpace
open scoped Topology

theorem scottSober_of_continuous_sup {P : Type u} [CompleteLattice P]
    (hjoin : @Continuous (P × P) P
      (@instTopologicalSpaceProd P P (scottTopology P) (scottTopology P))
      (scottTopology P)
      (fun p ↦ p.1 ⊔ p.2)) : ScottSober P := by
  letI : TopologicalSpace P := scottTopology P
  intro C hC hirr
  have hjoinC : ∀ a ∈ C, ∀ b ∈ C, a ⊔ b ∈ C := by
    intro a ha b hb
    apply hC.closure_eq ▸ (show a ⊔ b ∈ closure C from ?_)
    apply mem_closure_iff.mpr
    intro U hU hab
    have hpre : (fun p : P × P ↦ p.1 ⊔ p.2) ⁻¹' U ∈ 𝓝 (a, b) :=
      (hU.preimage hjoin).mem_nhds hab
    obtain ⟨V, W, hV, haV, hW, hbW, hVW⟩ := mem_nhds_prod_iff'.mp hpre
    obtain ⟨c, hcC, hcV, hcW⟩ := hirr.2 V W hV hW ⟨a, ha, haV⟩ ⟨b, hb, hbW⟩
    have hcU : c ∈ U := by
      simpa only [Set.mem_preimage, sup_idem] using
        hVW (show (c, c) ∈ V ×ˢ W from ⟨hcV, hcW⟩)
    exact ⟨c, hcU, hcC⟩
  have hdir : NonemptyDirected C := ⟨hirr.1, by
    intro a ha b hb
    exact ⟨a ⊔ b, hjoinC a ha b hb, le_sup_left, le_sup_right⟩⟩
  have hsc : IsScottClosed C := (isClosed_scott_iff C).mp hC
  have hsupC : sSup C ∈ C := hsc.2 C Set.Subset.rfl hdir (sSup C) (isLUB_sSup C)
  have hgeneric : closure ({sSup C} : Set P) = C := by
    rw [scott_closure_singleton]
    apply Set.Subset.antisymm
    · intro p hp
      exact hsc.1 hp hsupC
    · intro p hp
      exact le_sSup hp
  refine ⟨sSup C, hgeneric, ?_⟩
  intro p hp
  have heq : Set.Iic p = Set.Iic (sSup C) := by
    simpa only [scott_closure_singleton] using hp.trans hgeneric.symm
  apply le_antisymm
  · show p ∈ Set.Iic (sSup C)
    rw [← heq]
    exact le_rfl
  · show sSup C ∈ Set.Iic p
    rw [heq]
    exact le_rfl

end CoreCompactNonSober
