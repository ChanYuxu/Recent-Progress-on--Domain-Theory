import CoreCompactSimplified.SourceDefinitions
import Mathlib.Order.Bounds.OrderIso

set_option autoImplicit false
universe u v

namespace CoreCompactSimplified

open Set TopologicalSpace CoreCompactNonSober

variable {P : Type u} {Q : Type v} [PartialOrder P] [PartialOrder Q]

local instance transportedScottTopologyP : TopologicalSpace P := scottTopology P
local instance transportedScottTopologyQ : TopologicalSpace Q := scottTopology Q

theorem orderIso_directed_image (e : P ≃o Q) {E : Set P} (hE : NonemptyDirected E) :
    NonemptyDirected (e '' E) := by
  refine ⟨hE.1.image e, ?_⟩
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  obtain ⟨z, hz, hxz, hyz⟩ := hE.2 x hx y hy
  exact ⟨e z, ⟨z, hz, rfl⟩, e.monotone hxz, e.monotone hyz⟩

theorem orderIso_isDcpo (e : P ≃o Q) (hP : IsDcpo P) : IsDcpo Q := by
  intro E hE
  obtain ⟨p, hp⟩ := hP (e.symm '' E) (orderIso_directed_image e.symm hE)
  refine ⟨e p, ?_⟩
  have h := e.isLUB_image'.mpr hp
  simpa only [Set.image_image, e.apply_symm_apply, Set.image_id'] using h

def closedPreimage (e : P ≃o Q) (C : ScottCloseds Q) : ScottCloseds P := by
  letI : TopologicalSpace P := scottTopology P
  letI : TopologicalSpace Q := scottTopology Q
  have hC := (isClosed_scott_iff (C : Set Q)).mp C.isClosed
  refine ⟨e ⁻¹' (C : Set Q), (isClosed_scott_iff _).mpr ⟨?_, ?_⟩⟩
  · intro a b hab hb
    exact hC.1 (e.monotone hab) hb
  · intro E hEC hE p hp
    apply hC.2 (e '' E) ?_ (orderIso_directed_image e hE) (e p) (e.isLUB_image'.mpr hp)
    rintro _ ⟨x, hx, rfl⟩
    exact hEC hx

def closedOrderIso (e : P ≃o Q) : ScottCloseds P ≃o ScottCloseds Q where
  toFun := closedPreimage e.symm
  invFun := closedPreimage e
  left_inv C := by
    apply Closeds.ext
    ext p
    change e.symm (e p) ∈ C ↔ p ∈ C
    rw [e.symm_apply_apply]
  right_inv C := by
    apply Closeds.ext
    ext q
    change e (e.symm q) ∈ C ↔ q ∈ C
    rw [e.apply_symm_apply]
  map_rel_iff' := by
    intro A B
    constructor
    · intro h p hp
      have hp' : e p ∈ closedPreimage e.symm A := by
        change e.symm (e p) ∈ A
        simpa only [e.symm_apply_apply] using hp
      have hb : e p ∈ closedPreimage e.symm B := h hp'
      change e.symm (e p) ∈ B at hb
      simpa only [e.symm_apply_apply] using hb
    · intro h q hq
      exact h hq

end CoreCompactSimplified
