import CoreCompactNonSober.AmbientBasis

/-! The literal finite-coordinate/height basic neighborhood used by
singleton insertion and the appendix reference-family approximation. -/

set_option autoImplicit false

namespace CoreCompactNonSober.Ambient

open Set TopologicalSpace
open scoped Topology

theorem auxiliary_finite_neighborhood (p : Carrier) (U : Set Carrier)
    (hU : @IsOpen Carrier auxiliaryTopology U) (hp : p ∈ U) :
    ∃ (I : Set ℝ) (J : Finset Coordinate), IsOpen I ∧ height p ∈ I ∧
      ∀ q : Carrier, height q ∈ I →
        (∀ j ∈ J, configuration q j = configuration p j) → q ∈ U := by
  classical
  obtain ⟨O, hO, rfl⟩ := isOpen_induced_iff.mp hU
  have hpO : p.val ∈ O := hp
  obtain ⟨IH, C, hIH, hpIH, hC, hpC, hIC⟩ :=
    mem_nhds_prod_iff'.mp (hO.mem_nhds hpO)
  obtain ⟨I, hI, rfl⟩ := isOpen_induced_iff.mp hIH
  obtain ⟨J, W, hW, hWC⟩ := isOpen_pi_iff.mp hC (configuration p) hpC
  refine ⟨I, J, hI, hpIH, ?_⟩
  intro q hqI hqJ
  apply hIC
  refine ⟨hqI, hWC ?_⟩
  intro j hj
  change configuration q j ∈ W j
  rw [hqJ j hj]
  exact (hW j hj).2

theorem lower_height_in_open {t : ℝ} (ht : 0 < t) {I : Set ℝ}
    (hI : IsOpen I) (htI : t ∈ I) :
    ∃ u : ℝ, 0 < u ∧ u < t ∧ u ∈ I := by
  obtain ⟨a, b, ⟨hat, htb⟩, hab⟩ :=
    mem_nhds_iff_exists_Ioo_subset.mp (hI.mem_nhds htI)
  let u : ℝ := (max a 0 + t) / 2
  have hmax : max a 0 < t := max_lt hat ht
  have humax : max a 0 < u := by dsimp [u]; linarith
  have hut : u < t := by dsimp [u]; linarith
  exact ⟨u, (le_max_right a 0).trans_lt humax, hut,
    hab ⟨(le_max_left a 0).trans_lt humax, hut.trans htb⟩⟩

/-- Literal interval version of the unnumbered source neighborhood step.
Intersecting this real interval with `[0,1]` gives the printed relative
interval. All configuration coordinates outside the finite set are free. -/
theorem auxiliary_interval_finite_neighborhood (p : Carrier) (U : Set Carrier)
    (hU : @IsOpen Carrier auxiliaryTopology U) (hp : p ∈ U) :
    ∃ (a b : ℝ) (J : Finset Coordinate), a < height p ∧ height p < b ∧
      ∀ q : Carrier, height q ∈ Set.Ioo a b →
        (∀ j ∈ J, configuration q j = configuration p j) → q ∈ U := by
  obtain ⟨I, J, hI, hpI, hneigh⟩ := auxiliary_finite_neighborhood p U hU hp
  obtain ⟨a, b, ⟨hap, hpb⟩, hab⟩ :=
    mem_nhds_iff_exists_Ioo_subset.mp (hI.mem_nhds hpI)
  exact ⟨a, b, J, hap, hpb, fun q hq hconfig ↦ hneigh q (hab hq) hconfig⟩

end CoreCompactNonSober.Ambient
