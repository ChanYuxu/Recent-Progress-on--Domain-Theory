import CoreCompactNonSober.SubDcpoTopology

/-!
# Core-compactness and irreducibility consequences

Source: the local-compactness implication in Section 2 and the transfer
arguments in `thm:main`. Restriction is used as an actual frame map with
its specified membership equation.
-/

set_option autoImplicit false

universe u v

namespace CoreCompactNonSober

open Set TopologicalSpace

theorem isSaturated_of_isUpperSet_scott
    {P : Type u} [PartialOrder P] {K : Set P} (hK : IsUpperSet K) :
    @IsSaturated P (scottTopology P) K := by
  letI : TopologicalSpace P := scottTopology P
  letI : Topology.IsScott P Set.univ := ⟨rfl⟩
  change K = ⋂₀ {U : Set P | IsOpen U ∧ K ⊆ U}
  apply Set.Subset.antisymm
  · intro x hx
    exact Set.mem_sInter.mpr (fun U hU ↦ hU.2 hx)
  · intro x hx
    by_contra hxK
    have hU : IsOpen (Set.Iic x)ᶜ := isClosed_Iic.isOpen_compl
    have hKU : K ⊆ (Set.Iic x)ᶜ := by
      intro y hy hyx
      exact hxK (hK hyx hy)
    exact (Set.mem_sInter.mp hx (Set.Iic x)ᶜ ⟨hU, hKU⟩) le_rfl

theorem IsLocallyCompact.isCoreCompact
    {X : Type u} [TopologicalSpace X] (hX : IsLocallyCompact X) : IsCoreCompact X := by
  intro U x hx
  obtain ⟨V, K, hxV, hVK, hKU, hK, _⟩ := hX U x hx
  refine ⟨V, hxV, ?_⟩
  intro D hne hdir hcover
  haveI : Nonempty D := hne.to_subtype
  have hKcover : K ⊆ ⋃ W : D, ((W : Opens X) : Set X) := by
    intro y hy
    obtain ⟨W, hWD, hyW⟩ := Opens.mem_sSup.mp (hcover (hKU hy))
    exact Set.mem_iUnion.mpr ⟨⟨W, hWD⟩, hyW⟩
  have hD : Directed (· ⊆ ·) (fun W : D ↦ ((W : Opens X) : Set X)) := by
    intro A B
    obtain ⟨C, hC, hAC, hBC⟩ := hdir A A.property B B.property
    exact ⟨⟨C, hC⟩, hAC, hBC⟩
  obtain ⟨W, hKW⟩ := hK.elim_directed_cover
    (fun W : D ↦ ((W : Opens X) : Set X)) (fun W ↦ W.val.isOpen) hKcover hD
  exact ⟨W.val, W.property, hVK.trans hKW⟩

/-- A bijective frame map determines an order isomorphism. The proof
explicitly derives order reflection from preservation of binary meets. -/
noncomputable def orderIsoOfBijectiveFrameHom
    {A : Type u} {B : Type v} [CompleteLattice A] [CompleteLattice B]
    (ρ : FrameHom A B) (hρ : Function.Bijective ρ) : A ≃o B where
  toEquiv := Equiv.ofBijective ρ hρ
  map_rel_iff' := by
    intro a b
    change ρ a ≤ ρ b ↔ a ≤ b
    constructor
    · intro h
      have heq : ρ (a ⊓ b) = ρ a := by rw [map_inf, inf_eq_left.mpr h]
      exact inf_eq_left.mp (hρ.1 heq)
    · intro h
      apply inf_eq_left.mp
      rw [← map_inf, inf_eq_left.mpr h]

theorem OpenWayBelow.map_orderIso
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (e : Opens X ≃o Opens Y) {V U : Opens X} (h : OpenWayBelow V U) :
    OpenWayBelow (e V) (e U) := by
  intro D hne hdir hcover
  let D' : Set (Opens X) := e.symm '' D
  have hne' : D'.Nonempty := hne.image e.symm
  have hdir' : DirectedOn (· ≤ ·) D' := by
    rintro _ ⟨A, hA, rfl⟩ _ ⟨B, hB, rfl⟩
    obtain ⟨C, hC, hAC, hBC⟩ := hdir A hA B hB
    exact ⟨e.symm C, ⟨C, hC, rfl⟩, e.symm.monotone hAC, e.symm.monotone hBC⟩
  have hcover' : U ≤ sSup D' := by
    have ht := e.symm.monotone hcover
    simpa only [OrderIso.symm_apply_apply, map_sSup] using ht
  obtain ⟨W, ⟨Z, hZD, rfl⟩, hVW⟩ := h D' hne' hdir' hcover'
  refine ⟨Z, hZD, ?_⟩
  simpa only [OrderIso.apply_symm_apply] using e.monotone hVW

/-- Core-compactness transfer in `thm:main`, using the actual restriction
isomorphism and the finite-neighborhood definition of core-compactness. -/
theorem scottCoreCompact_of_restriction
    {L : Type u} [PartialOrder L] (S : Set L)
    (hL : ScottCoreCompact L) (hρ : RestrictionFrameIsomorphism S) :
    ScottCoreCompact S := by
  letI : TopologicalSpace L := scottTopology L
  letI : TopologicalSpace S := scottTopology S
  obtain ⟨ρ, hbij, htrace⟩ := hρ
  let e : ScottOpens L ≃o ScottOpens S := orderIsoOfBijectiveFrameHom ρ hbij
  intro U s hsU
  obtain ⟨UL, hUL⟩ := hbij.2 U
  have hsUL : (s : L) ∈ UL := (htrace UL s).mp (by simpa only [hUL] using hsU)
  obtain ⟨V, hsV, hVU⟩ := hL UL s.val hsUL
  refine ⟨ρ V, (htrace V s).mpr hsV, ?_⟩
  have ht := hVU.map_orderIso e
  change OpenWayBelow (ρ V) (ρ UL) at ht
  simpa only [hUL] using ht

/-- Irreducibility of the retained whole Scott space in the main proof. -/
theorem irreducible_univ_of_restriction
    {L : Type u} [CompleteLattice L] (S : Set L)
    (happ : LowerApproximation S) (hρ : RestrictionFrameIsomorphism S) :
    @IsIrreducible S (scottTopology S) Set.univ := by
  letI : TopologicalSpace L := scottTopology L
  letI : TopologicalSpace S := scottTopology S
  obtain ⟨ρ, hbij, htrace⟩ := hρ
  constructor
  · obtain ⟨s, _, _⟩ := happ (⊤ : L) (⊤ : ScottOpens L) (by trivial)
    exact ⟨s, trivial⟩
  · intro U V hU hV hmeetU hmeetV
    let Uopen : ScottOpens S := ⟨U, hU⟩
    let Vopen : ScottOpens S := ⟨V, hV⟩
    obtain ⟨UL, hUL⟩ := hbij.2 Uopen
    obtain ⟨VL, hVL⟩ := hbij.2 Vopen
    obtain ⟨a, _, ha⟩ := hmeetU
    obtain ⟨b, _, hb⟩ := hmeetV
    have haUL : (a : L) ∈ UL := (htrace UL a).mp (by simpa only [hUL] using ha)
    have hbVL : (b : L) ∈ VL := (htrace VL b).mp (by simpa only [hVL] using hb)
    have htopU : (⊤ : L) ∈ UL := ((isOpen_scott_iff _).mp UL.isOpen).1 le_top haUL
    have htopV : (⊤ : L) ∈ VL := ((isOpen_scott_iff _).mp VL.isOpen).1 le_top hbVL
    obtain ⟨s, _, hs⟩ := happ (⊤ : L) (UL ⊓ VL) ⟨htopU, htopV⟩
    have hsU : s ∈ U := by
      have ht := (htrace UL s).mpr hs.1
      simpa only [hUL] using ht
    have hsV : s ∈ V := by
      have ht := (htrace VL s).mpr hs.2
      simpa only [hVL] using ht
    exact ⟨s, trivial, hsU, hsV⟩

end CoreCompactNonSober
