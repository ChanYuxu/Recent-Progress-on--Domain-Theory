import CoreCompactNonSober.AmbientBasis
import CoreCompactNonSober.TopologicalConsequences

/-!
# Local compactness and core-compactness of the ambient Scott space

Source: `eq:compact-neighbourhood` and `prop:ambient-properties`.
The printed two-form basis is used literally. If there is a height threshold,
one rational threshold is chosen between it and the height of the point.
The corresponding non-strict relaxation is auxiliary-closed and upper.
-/

set_option autoImplicit false

namespace CoreCompactNonSober.Ambient

open Set TopologicalSpace

private theorem printed_compact_refinement (x : Carrier) (B : PrintedBasic)
    (hx : x ∈ printedBasicSet B) :
    ∃ (V : ScottOpens Carrier) (K : Set Carrier),
      x ∈ V ∧ (V : Set Carrier) ⊆ K ∧ K ⊆ printedBasicSet B ∧
        @IsClosed Carrier auxiliaryTopology K ∧ IsUpperSet K := by
  letI : TopologicalSpace Carrier := scottTopology Carrier
  let E : Set Carrier := ⋂ e ∈ B.entries, entrySet e.1 e.2
  have hEclosed : @IsClosed Carrier auxiliaryTopology E := by
    letI : TopologicalSpace Carrier := auxiliaryTopology
    exact isClosed_biInter (fun e _ ↦ entrySet_isClosed_aux e.1 e.2)
  have hEupper : IsUpperSet E := by
    intro p z hpz hp
    apply Set.mem_iInter.mpr
    intro e
    apply Set.mem_iInter.mpr
    intro he
    exact ((le_iff p z).mp hpz).2 e.1
      (Set.mem_iInter.mp (Set.mem_iInter.mp hp e) he)
  cases hthreshold : B.threshold with
  | none =>
    have hBE : printedBasicSet B = E := by simp [printedBasicSet, hthreshold, E]
    refine ⟨⟨printedBasicSet B, printedBasicSet_isOpen_scott B⟩,
      printedBasicSet B, hx, Set.Subset.rfl, Set.Subset.rfl, ?_, ?_⟩
    · simpa only [hBE] using hEclosed
    · simpa only [hBE] using hEupper
  | some q =>
    have hxE : x ∈ E := hx.1
    have hqx : ((q : ℚ) : ℝ) < height x := by
      simpa only [printedBasicSet, hthreshold, Set.mem_inter_iff] using hx.2
    obtain ⟨r, hqr, hrx⟩ := exists_rat_btwn hqx
    have hr0 : (0 : ℚ) ≤ r := by
      have hq0 : (0 : ℝ) ≤ (q : ℚ) := by exact_mod_cast q.property.1
      exact_mod_cast (hq0.trans hqr.le)
    have hr1 : r < (1 : ℚ) := by exact_mod_cast hrx.trans_le x.val.1.property.2
    let B' : PrintedBasic := ⟨B.entries, some ⟨r, hr0, hr1⟩⟩
    let V : ScottOpens Carrier := ⟨printedBasicSet B', printedBasicSet_isOpen_scott B'⟩
    let K : Set Carrier := E ∩ {p | (r : ℝ) ≤ height p}
    refine ⟨V, K, ⟨hxE, hrx⟩, ?_, ?_, ?_, ?_⟩
    · intro p hp
      have hpr : (r : ℝ) < height p := hp.2
      exact ⟨hp.1, hpr.le⟩
    · intro p hp
      refine ⟨hp.1, ?_⟩
      change p ∈ match B.threshold with
        | none => Set.univ
        | some q => heightAbove (q : ℚ)
      rw [hthreshold]
      exact hqr.trans_le hp.2
    · letI : TopologicalSpace Carrier := auxiliaryTopology
      exact hEclosed.inter (isClosed_le continuous_const continuous_height)
    · intro p z hpz hp
      exact ⟨hEupper hpz hp.1, hp.2.trans ((le_iff p z).mp hpz).1⟩

/-- The source's neighborhood definition of local compactness, including
compactness and saturation in the intrinsic Scott topology. -/
theorem scottLocallyCompact : ScottLocallyCompact Carrier := by
  classical
  letI : TopologicalSpace Carrier := scottTopology Carrier
  intro U x hx
  obtain ⟨F, hxF, hFU⟩ := exists_basic_subset x U hx U.isOpen
  obtain ⟨B, hxB, hBF⟩ := exists_printedBasic_subset_basicSet x F hxF
  obtain ⟨V, K, hxV, hVK, hKB, hKclosed, hKupper⟩ := printed_compact_refinement x B hxB
  have hKcompact_aux : @IsCompact Carrier auxiliaryTopology K := by
    letI : TopologicalSpace Carrier := auxiliaryTopology
    exact hKclosed.isCompact
  exact ⟨V, K, hxV, hVK, hKB.trans (hBF.trans hFU),
    isCompact_scott_of_aux hKcompact_aux,
    isSaturated_of_isUpperSet_scott hKupper⟩

theorem scottCoreCompact : ScottCoreCompact Carrier := by
  letI : TopologicalSpace Carrier := scottTopology Carrier
  exact IsLocallyCompact.isCoreCompact scottLocallyCompact

theorem scottCompact : ScottCompact Carrier :=
  scottCompact_of_least (⊥ : Carrier) (fun _ ↦ bot_le)

end CoreCompactNonSober.Ambient
