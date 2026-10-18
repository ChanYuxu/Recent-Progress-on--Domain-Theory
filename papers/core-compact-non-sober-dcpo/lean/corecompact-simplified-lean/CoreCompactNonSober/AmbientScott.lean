import CoreCompactNonSober.AmbientMeetContinuity
import CoreCompactNonSober.CompactSemilattice
import Mathlib.Topology.Metrizable.Uniformity

/-!
# Identification of the intrinsic Scott topology

Source: `lem:scott-ambient`. The auxiliary metric is chosen with exactly
the already defined product/subtype topology. The conclusions below are
about the intrinsic order-determined Scott topology.
-/

set_option autoImplicit false

namespace CoreCompactNonSober.Ambient

open Set Filter TopologicalSpace
open scoped Topology

theorem isScottClosed_iff_auxClosed_lower (F : Set Carrier) :
    IsScottClosed F ↔ IsClosed F ∧ IsLowerSet F := by
  letI : MetricSpace Carrier := TopologicalSpace.metrizableSpaceMetric Carrier
  exact CompactSemilattice.isScottClosed_iff_closed_lower F

/-- Exact open-set identification of `lem:scott-ambient`. -/
theorem isOpen_scott_iff_aux_open_upper (U : Set Carrier) :
    @IsOpen Carrier (scottTopology Carrier) U ↔ IsOpen U ∧ IsUpperSet U := by
  constructor
  · intro hU
    have hclosedSC : @IsClosed Carrier (scottTopology Carrier) Uᶜ :=
      @IsOpen.isClosed_compl Carrier (scottTopology Carrier) U hU
    have hC : IsScottClosed Uᶜ :=
      (isClosed_scott_iff Uᶜ).mp hclosedSC
    have haux : IsClosed Uᶜ := (isScottClosed_iff_auxClosed_lower Uᶜ).mp hC |>.1
    refine ⟨?_, ((isOpen_scott_iff U).mp hU).1⟩
    simpa only [compl_compl] using haux.isOpen_compl
  · rintro ⟨hU, hupper⟩
    have hC : IsScottClosed Uᶜ :=
      (isScottClosed_iff_auxClosed_lower Uᶜ).mpr ⟨hU.isClosed_compl, hupper.compl⟩
    have hclosed : @IsClosed Carrier (scottTopology Carrier) Uᶜ :=
      (isClosed_scott_iff Uᶜ).mpr hC
    simpa only [compl_compl] using
      (@IsClosed.isOpen_compl Carrier (scottTopology Carrier) Uᶜ hclosed)

/-- The auxiliary topology is finer than the intrinsic Scott topology. -/
theorem auxiliary_le_scott : auxiliaryTopology ≤ scottTopology Carrier := by
  intro U hU
  exact ((isOpen_scott_iff_aux_open_upper U).mp hU).1

/-- Compactness passes from the auxiliary topology to the coarser Scott
topology. Both topology arguments are explicit in the continuous-image step. -/
theorem isCompact_scott_of_aux {K : Set Carrier}
    (hK : @IsCompact Carrier auxiliaryTopology K) :
    @IsCompact Carrier (scottTopology Carrier) K := by
  have hi : @Continuous Carrier Carrier auxiliaryTopology (scottTopology Carrier) id :=
    (@continuous_def Carrier Carrier auxiliaryTopology (scottTopology Carrier) id).mpr
      (fun U hU ↦ ((isOpen_scott_iff_aux_open_upper U).mp hU).1)
  have himage := @IsCompact.image Carrier Carrier auxiliaryTopology
    (scottTopology Carrier) K id hK hi
  simpa only [Set.image_id] using himage

/-- The second clause of `lem:scott-ambient`, proved by the net argument
from the source rather than assumed as a lattice-distributivity property. -/
theorem scottContinuous_meet_left (x : Carrier) :
    ScottContinuous (fun y : Carrier ↦ x ⊓ y) := by
  intro E hne hdir p hp
  haveI : Nonempty E := hne.to_subtype
  haveI : IsDirectedOrder E := ⟨fun a b ↦ by
    obtain ⟨c, hc, hac, hbc⟩ := hdir a a.property b b.property
    exact ⟨⟨c, hc⟩, hac, hbc⟩⟩
  have ht : Tendsto (Subtype.val : E → Carrier) atTop (𝓝 p) :=
    SupConvergenceClass.tendsto_coe_atTop_isLUB p E hp
  have hmap : Tendsto (fun e : E ↦ x ⊓ (e : Carrier)) atTop (𝓝 (x ⊓ p)) :=
    ((continuous_const.inf continuous_id).tendsto p).comp ht
  have hm : Monotone (fun e : E ↦ x ⊓ (e : Carrier)) :=
    fun _ _ hab ↦ inf_le_inf_left x hab
  have hrange : Set.range (fun e : E ↦ x ⊓ (e : Carrier)) =
      (fun y : Carrier ↦ x ⊓ y) '' E := by
    ext z
    constructor
    · rintro ⟨e, rfl⟩
      exact ⟨e, e.property, rfl⟩
    · rintro ⟨e, he, rfl⟩
      exact ⟨⟨e, he⟩, rfl⟩
  rw [← hrange]
  exact isLUB_of_tendsto_atTop hm hmap

theorem inf_sSup (x : Carrier) (E : Set Carrier) (hE : NonemptyDirected E) :
    x ⊓ sSup E = sSup ((fun y : Carrier ↦ x ⊓ y) '' E) :=
  (scottContinuous_meet_left x hE.1 hE.2 (isLUB_sSup E)).unique (isLUB_sSup _)

/-- The finite required-entry conditions used in the Scott basis. -/
def entrySet (j : Coordinate) (z : Alphabet j) : Set Carrier :=
  {p | z ∈ configuration p j}

theorem entrySet_isScottOpen (j : Coordinate) (z : Alphabet j) :
    IsScottOpen (entrySet j z) := by
  constructor
  · intro p q hpq hp
    exact ((le_iff p q).mp hpq).2 j hp
  · intro E hE p hp hz
    have heq : sSup E = p := (isLUB_sSup E).unique hp
    have hzs : z ∈ configuration (sSup E) j := by simpa only [heq] using hz
    exact (mem_configuration_sSup E j z).mp hzs

theorem entrySet_isClosed_aux (j : Coordinate) (z : Alphabet j) :
    IsClosed (entrySet j z) :=
  (isClosed_discrete {A : Finset (Alphabet j) | z ∈ A}).preimage (continuous_configuration j)

def heightAbove (r : ℝ) : Set Carrier := {p | r < height p}

theorem heightAbove_isScottOpen (r : ℝ) : IsScottOpen (heightAbove r) := by
  classical
  constructor
  · intro p q hpq hp
    exact hp.trans_le ((le_iff p q).mp hpq).1
  · intro E hE p hp hpr
    by_contra hnone
    have hbound : ∀ q ∈ E, height q ≤ r := by
      intro q hq
      exact le_of_not_gt (fun hrq ↦ hnone ⟨q, hq, hrq⟩)
    have hsup : height (sSup E) ≤ r := by
      rw [height_sSup E hE.1]
      apply csSup_le (hE.1.image height)
      rintro _ ⟨q, hq, rfl⟩
      exact hbound q hq
    have heq : sSup E = p := (isLUB_sSup E).unique hp
    rw [heq] at hsup
    exact not_le_of_gt hpr hsup

end CoreCompactNonSober.Ambient
