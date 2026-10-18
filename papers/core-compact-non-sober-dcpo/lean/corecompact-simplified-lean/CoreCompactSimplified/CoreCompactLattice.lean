import CoreCompactSimplified.SourceDefinitions
import CoreCompactNonSober.ScottSobriety

/-!
The exact sobriety implication cited in `prop:ambient-properties`:
a complete lattice with core-compact Scott topology is sober.

The paper cites this background theorem, rather than specifying its proof.
Here its proof is supplied: continuity of the open-set lattice gives
interpolation; this makes binary join jointly Scott-topology continuous;
irreducible Scott-closed sets are then directed and have generic suprema.
The ambient lattice is not given extra metric/topological assumptions.
-/

set_option autoImplicit false

universe u

namespace CoreCompactSimplified

open Set TopologicalSpace CoreCompactNonSober
open scoped Topology

section Opens

variable {X : Type u} [TopologicalSpace X]

theorem openWayBelow_mono {A B C D : Opens X} (hAB : A ≤ B)
    (hBC : OpenWayBelow B C) (hCD : C ≤ D) : OpenWayBelow A D := by
  intro E hne hdir hcover
  obtain ⟨W, hW, hBW⟩ := hBC E hne hdir (hCD.trans hcover)
  exact ⟨W, hW, hAB.trans hBW⟩

theorem openWayBelow_bot (U : Opens X) : OpenWayBelow ⊥ U := by
  intro E hne _ _
  obtain ⟨W, hW⟩ := hne
  exact ⟨W, hW, bot_le⟩

theorem openWayBelow_sup {A B U : Opens X} (hA : OpenWayBelow A U)
    (hB : OpenWayBelow B U) : OpenWayBelow (A ⊔ B) U := by
  intro E hne hdir hcover
  obtain ⟨W, hW, hAW⟩ := hA E hne hdir hcover
  obtain ⟨Z, hZ, hBZ⟩ := hB E hne hdir hcover
  obtain ⟨T, hT, hWT, hZT⟩ := hdir W hW Z hZ
  exact ⟨T, hT, sup_le (hAW.trans hWT) (hBZ.trans hZT)⟩

/-- Continuity of the open-set lattice, with its actual directed-family
way-below relation, in exactly the neighborhood sense used in the paper. -/
theorem openWayBelow_interpolate (hX : IsCoreCompact X) {V U : Opens X}
    (hVU : OpenWayBelow V U) :
    ∃ W : Opens X, OpenWayBelow V W ∧ OpenWayBelow W U := by
  let E : Set (Opens X) := {A | ∃ B, OpenWayBelow A B ∧ OpenWayBelow B U}
  have hne : E.Nonempty := ⟨⊥, ⊥, openWayBelow_bot _, openWayBelow_bot _⟩
  have hdir : DirectedOn (· ≤ ·) E := by
    rintro A ⟨B, hAB, hBU⟩ C ⟨D, hCD, hDU⟩
    refine ⟨A ⊔ C, ⟨B ⊔ D, ?_, openWayBelow_sup hBU hDU⟩,
      le_sup_left, le_sup_right⟩
    exact openWayBelow_sup
      (openWayBelow_mono le_rfl hAB le_sup_left)
      (openWayBelow_mono le_rfl hCD le_sup_right)
  have hcover : U ≤ sSup E := by
    intro x hx
    obtain ⟨B, hxB, hBU⟩ := hX U x hx
    obtain ⟨A, hxA, hAB⟩ := hX B x hxB
    exact Opens.mem_sSup.mpr ⟨A, ⟨B, hAB, hBU⟩, hxA⟩
  obtain ⟨A, ⟨B, hAB, hBU⟩, hVA⟩ := hVU E hne hdir hcover
  exact ⟨B, openWayBelow_mono hVA hAB le_rfl, hBU⟩

/-- The neighborhood definition uses exactly the element way-below relation
of the complete lattice of opens, not a different compact-containment notion. -/
theorem openWayBelow_iff_elementWayBelow (V U : Opens X) :
    OpenWayBelow V U ↔ ElementWayBelow V U := by
  constructor
  · intro h E hE p hp hUp
    have heq : sSup E = p := (isLUB_sSup E).unique hp
    apply h E hE.1 hE.2
    simpa only [heq] using hUp
  · intro h E hne hdir hcover
    exact h E ⟨hne, hdir⟩ (sSup E) (isLUB_sSup E) hcover

/-- Explicit semantic bridge to the source's continuous-open-lattice
characterization of core-compactness. This is an equivalence, not a
definitional-equality claim. -/
theorem coreCompact_iff_continuous_opens :
    IsCoreCompact X ↔ IsContinuousDcpo (Opens X) := by
  constructor
  · intro hX
    refine ⟨fun E _ ↦ ⟨sSup E, isLUB_sSup E⟩, ?_⟩
    intro U
    have hbot : ElementWayBelow (⊥ : Opens X) U :=
      (openWayBelow_iff_elementWayBelow _ _).mp (openWayBelow_bot U)
    refine ⟨⟨⟨⊥, hbot⟩, ?_⟩, ?_, ?_⟩
    · intro A hA B hB
      exact ⟨A ⊔ B,
        (openWayBelow_iff_elementWayBelow _ _).mp (openWayBelow_sup
          ((openWayBelow_iff_elementWayBelow _ _).mpr hA)
          ((openWayBelow_iff_elementWayBelow _ _).mpr hB)), le_sup_left, le_sup_right⟩
    · intro V hV
      exact ((openWayBelow_iff_elementWayBelow _ _).mpr hV).le
    · intro B hB x hx
      obtain ⟨V, hxV, hVU⟩ := hX U x hx
      exact hB ((openWayBelow_iff_elementWayBelow _ _).mp hVU) hxV
  · rintro ⟨_, hcontinuous⟩ U x hx
    obtain ⟨_, hU⟩ := hcontinuous U
    have heq : sSup {V : Opens X | ElementWayBelow V U} = U := (isLUB_sSup _).unique hU
    rw [← heq] at hx
    obtain ⟨V, hV, hxV⟩ := Opens.mem_sSup.mp hx
    exact ⟨V, hxV, (openWayBelow_iff_elementWayBelow _ _).mpr hV⟩

end Opens

section Lattice

variable {P : Type u} [CompleteLattice P]

local instance : TopologicalSpace P := scottTopology P

theorem isLUB_sup_image {E : Set P} (hne : E.Nonempty) {s : P}
    (hs : IsLUB E s) (a : P) :
    IsLUB ((fun e : P ↦ e ⊔ a) '' E) (s ⊔ a) := by
  constructor
  · rintro _ ⟨e, he, rfl⟩
    exact sup_le_sup_right (hs.1 he) a
  · intro b hb
    apply sup_le
    · exact hs.2 (fun e he ↦ le_sup_left.trans (hb ⟨e, he, rfl⟩))
    · obtain ⟨e, he⟩ := hne
      exact le_sup_right.trans (hb ⟨e, he, rfl⟩)

theorem sup_image_directed {E : Set P} (hE : NonemptyDirected E) (a : P) :
    NonemptyDirected ((fun e : P ↦ e ⊔ a) '' E) := by
  refine ⟨hE.1.image _, ?_⟩
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  obtain ⟨z, hz, hxz, hyz⟩ := hE.2 x hx y hy
  exact ⟨z ⊔ a, ⟨z, hz, rfl⟩, sup_le_sup_right hxz a, sup_le_sup_right hyz a⟩

noncomputable def joinSection (U : ScottOpens P) (b : P) : ScottOpens P := by
  letI : TopologicalSpace P := scottTopology P
  refine ⟨{a | b ⊔ a ∈ U}, (isOpen_scott_iff _).mpr ⟨?_, ?_⟩⟩
  · intro a c hac ha
    exact ((isOpen_scott_iff _).mp U.isOpen).1 (sup_le_sup_left hac b) ha
  · intro E hE s hs hbs
    have hbs' : s ⊔ b ∈ U := by simpa only [sup_comm] using hbs
    obtain ⟨_, ⟨e, he, rfl⟩, heU⟩ := ((isOpen_scott_iff _).mp U.isOpen).2 _
      (sup_image_directed hE b) (s ⊔ b) (isLUB_sup_image hE.1 hs b) hbs'
    exact ⟨e, he, by simpa only [sup_comm] using heU⟩

theorem joinSection_mono (U : ScottOpens P) : Monotone (joinSection U) := by
  letI : TopologicalSpace P := scottTopology P
  intro b c hbc a ha
  exact ((isOpen_scott_iff _).mp U.isOpen).1 (sup_le_sup_right hbc a) ha

theorem joinSection_lub (U : ScottOpens P) (E : Set P) (hE : NonemptyDirected E)
    (s : P) (hs : IsLUB E s) :
    joinSection U s = sSup (joinSection U '' E) := by
  letI : TopologicalSpace P := scottTopology P
  apply Opens.ext
  ext a
  constructor
  · intro ha
    have ha' : s ⊔ a ∈ U := ha
    obtain ⟨_, ⟨e, he, rfl⟩, heU⟩ := ((isOpen_scott_iff _).mp U.isOpen).2 _
      (sup_image_directed hE a) (s ⊔ a) (isLUB_sup_image hE.1 hs a) ha'
    exact Opens.mem_sSup.mpr ⟨joinSection U e, ⟨e, he, rfl⟩, heU⟩
  · intro ha
    obtain ⟨V, ⟨e, he, rfl⟩, haV⟩ := Opens.mem_sSup.mp ha
    exact joinSection_mono U (hs.1 he) haV

theorem joinSection_wayBelow_open (hP : ScottCoreCompact P)
    (U V : ScottOpens P) :
    @IsOpen P (scottTopology P) {b | OpenWayBelow V (joinSection U b)} := by
  letI : TopologicalSpace P := scottTopology P
  apply (isOpen_scott_iff _).mpr
  constructor
  · intro b c hbc hb
    exact openWayBelow_mono le_rfl hb (joinSection_mono U hbc)
  · intro E hE s hs hVs
    obtain ⟨W, hVW, hWs⟩ := openWayBelow_interpolate hP hVs
    have hdir : DirectedOn (· ≤ ·) (joinSection U '' E) := by
      rintro _ ⟨b, hb, rfl⟩ _ ⟨c, hc, rfl⟩
      obtain ⟨d, hd, hbd, hcd⟩ := hE.2 b hb c hc
      exact ⟨joinSection U d, ⟨d, hd, rfl⟩,
        joinSection_mono U hbd, joinSection_mono U hcd⟩
    obtain ⟨_, ⟨e, he, rfl⟩, hWe⟩ := hWs _ (hE.1.image _) hdir
      (le_of_eq (joinSection_lub U E hE s hs))
    exact ⟨e, he, openWayBelow_mono le_rfl hVW hWe⟩

theorem continuous_sup_of_coreCompact (hP : ScottCoreCompact P) :
    @Continuous (P × P) P
      (@instTopologicalSpaceProd P P (scottTopology P) (scottTopology P))
      (scottTopology P) (fun p ↦ p.1 ⊔ p.2) := by
  letI : TopologicalSpace P := scottTopology P
  apply continuous_def.mpr
  intro U hU
  apply isOpen_iff_mem_nhds.mpr
  rintro ⟨a, b⟩ hab
  let Uo : ScottOpens P := ⟨U, hU⟩
  have ha : a ∈ joinSection Uo b := by
    change b ⊔ a ∈ U
    simpa only [sup_comm] using hab
  obtain ⟨V, haV, hVs⟩ := hP (joinSection Uo b) a ha
  let W : Set P := {c | OpenWayBelow V (joinSection Uo c)}
  have hW : IsOpen W := joinSection_wayBelow_open hP Uo V
  have hprod : (V : Set P) ×ˢ W ∈ 𝓝 (a, b) :=
    (V.isOpen.prod hW).mem_nhds ⟨haV, hVs⟩
  apply Filter.mem_of_superset hprod
  rintro ⟨x, y⟩ ⟨hx, hy⟩
  have hxy : y ⊔ x ∈ U := hy.le hx
  simpa only [Set.mem_preimage, sup_comm] using hxy

/-- Exact background implication cited as Jia–Jung–Li Corollary 3.3.
It is proved here, not declared as an external axiom. -/
theorem coreCompact_completeLattice_sober (hP : ScottCoreCompact P) : ScottSober P :=
  scottSober_of_continuous_sup (continuous_sup_of_coreCompact hP)

end Lattice

end CoreCompactSimplified
