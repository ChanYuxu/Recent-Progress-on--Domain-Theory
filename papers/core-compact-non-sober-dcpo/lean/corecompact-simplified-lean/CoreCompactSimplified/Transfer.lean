import CoreCompactSimplified.SourceDefinitions
import CoreCompactNonSober.TopologicalConsequences

/-!
Theorem `thm:transfer` (source lines 203–290), following its printed route.
All suprema below are `IsLUB`; the ambient order is only a dcpo, not a
complete lattice. The common-lower property is a hypothesis here and must
later be proved for the actual recursive construction.
-/

set_option autoImplicit false

universe u

namespace CoreCompactSimplified

open Set TopologicalSpace CoreCompactNonSober

variable {L : Type u} [PartialOrder L] {D : Set L}

theorem directed_image {E : Set D} (hE : NonemptyDirected E) :
    NonemptyDirected (Subtype.val '' E : Set L) := by
  refine ⟨hE.1.image Subtype.val, ?_⟩
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  obtain ⟨c, hc, hac, hbc⟩ := hE.2 a ha b hb
  exact ⟨c.val, ⟨c, hc, rfl⟩, hac, hbc⟩

theorem subdcpo_isDcpo (hL : IsDcpo L) (hD : IsSubDcpo D) : IsDcpo D := by
  intro E hE
  obtain ⟨s, hs⟩ := hL (Subtype.val '' E) (directed_image hE)
  have hsD : s ∈ D := hD _ (by rintro _ ⟨d, _, rfl⟩; exact d.property)
    (directed_image hE) s hs
  refine ⟨⟨s, hsD⟩, ?_, ?_⟩
  · intro e he
    exact hs.1 (Set.mem_image_of_mem Subtype.val he)
  · intro b hb
    exact hs.2 (by rintro _ ⟨e, he, rfl⟩; exact hb he)

theorem subtype_isLUB_ambient (hL : IsDcpo L) (hD : IsSubDcpo D)
    {E : Set D} (hE : NonemptyDirected E) {p : D} (hp : IsLUB E p) :
    IsLUB (Subtype.val '' E : Set L) (p : L) := by
  obtain ⟨s, hs⟩ := hL (Subtype.val '' E) (directed_image hE)
  have hsD : s ∈ D := hD _ (by rintro _ ⟨d, _, rfl⟩; exact d.property)
    (directed_image hE) s hs
  have hps : (p : L) ≤ s := hp.2 (show (⟨s, hsD⟩ : D) ∈ upperBounds E from
    fun e he ↦ hs.1 (Set.mem_image_of_mem Subtype.val he))
  have hsp : s ≤ (p : L) := hs.2 (by rintro _ ⟨e, he, rfl⟩; exact hp.1 he)
  have heq : s = (p : L) := le_antisymm hsp hps
  exact heq ▸ hs

theorem inclusion_continuous (hL : IsDcpo L) (hD : IsSubDcpo D) :
    @Continuous D L (scottTopology D) (scottTopology L) Subtype.val := by
  letI : TopologicalSpace D := scottTopology D
  letI : TopologicalSpace L := scottTopology L
  apply continuous_def.mpr
  intro V hV
  apply (isOpen_scott_iff _).mpr
  have hV' := (isOpen_scott_iff V).mp hV
  refine ⟨fun a b hab ha ↦ hV'.1 hab ha, ?_⟩
  intro E hE p hp hpV
  obtain ⟨e, ⟨d, hd, rfl⟩, heV⟩ := hV'.2 _ (directed_image hE) p.val
    (subtype_isLUB_ambient hL hD hE hp) hpV
  exact ⟨d, hd, heV⟩

def restrictionHom (hL : IsDcpo L) (hD : IsSubDcpo D) :
    FrameHom (ScottOpens L) (ScottOpens D) := by
  letI : TopologicalSpace D := scottTopology D
  letI : TopologicalSpace L := scottTopology L
  exact Opens.comap ⟨Subtype.val, inclusion_continuous hL hD⟩

@[simp] theorem restrictionHom_mem (hL : IsDcpo L) (hD : IsSubDcpo D)
    (V : ScottOpens L) (d : D) : d ∈ restrictionHom hL hD V ↔ (d : L) ∈ V := Iff.rfl

theorem upward_isOpen (hcommon : CommonLowerWitness D) (U : ScottOpens D) :
    @IsOpen L (scottTopology L) (upperHull (Subtype.val '' (U : Set D))) := by
  apply (isOpen_scott_iff _).mpr
  refine ⟨?_, ?_⟩
  · rintro a b hab ⟨q, ⟨d, hd, rfl⟩, hqa⟩
    exact ⟨d.val, ⟨d, hd, rfl⟩, hqa.trans hab⟩
  · rintro E hE s hs ⟨q, ⟨d, hd, rfl⟩, hds⟩
    obtain ⟨r, hrU, _, e, he, hre⟩ := hcommon U d hd E hE s hs hds
    exact ⟨e, he, r.val, ⟨r, hrU, rfl⟩, hre⟩

theorem upward_trace (U : ScottOpens D) (d : D) :
    (d : L) ∈ upperHull (Subtype.val '' (U : Set D)) ↔ d ∈ U := by
  letI : TopologicalSpace D := scottTopology D
  constructor
  · rintro ⟨q, ⟨r, hr, rfl⟩, hrd⟩
    exact ((isOpen_scott_iff _).mp U.isOpen).1 hrd hr
  · intro hd
    exact ⟨d.val, ⟨d, hd, rfl⟩, le_rfl⟩

theorem trace_upward (happrox : LowerNeighborhoodApproximation D) (V : ScottOpens L) :
    upperHull (Subtype.val '' (Subtype.val ⁻¹' (V : Set L) : Set D)) = (V : Set L) := by
  letI : TopologicalSpace L := scottTopology L
  ext p
  constructor
  · rintro ⟨q, ⟨d, hd, rfl⟩, hdp⟩
    exact ((isOpen_scott_iff _).mp V.isOpen).1 hdp hd
  · intro hp
    obtain ⟨d, hd, hdp⟩ := happrox p V hp
    exact ⟨d.val, ⟨d, hd, rfl⟩, hdp⟩

theorem restriction_bijective (hL : IsDcpo L) (hD : IsSubDcpo D)
    (happrox : LowerNeighborhoodApproximation D) (hcommon : CommonLowerWitness D) :
    Function.Bijective (restrictionHom hL hD) := by
  letI : TopologicalSpace L := scottTopology L
  letI : TopologicalSpace D := scottTopology D
  constructor
  · intro U V heq
    apply Opens.ext
    have htr : (Subtype.val ⁻¹' (U : Set L) : Set D) = Subtype.val ⁻¹' (V : Set L) :=
      congrArg (fun W : ScottOpens D ↦ (W : Set D)) heq
    rw [← trace_upward happrox U, ← trace_upward happrox V, htr]
  · intro U
    refine ⟨⟨_, upward_isOpen hcommon U⟩, ?_⟩
    apply Opens.ext
    ext d
    exact upward_trace U d

theorem restriction_isomorphism (hL : IsDcpo L) (hD : IsSubDcpo D)
    (happrox : LowerNeighborhoodApproximation D) (hcommon : CommonLowerWitness D) :
    RestrictionFrameIsomorphism D :=
  ⟨restrictionHom hL hD, restriction_bijective hL hD happrox hcommon,
    restrictionHom_mem hL hD⟩

theorem meetContinuous_of_common (hL : IsDcpo L) (hD : IsSubDcpo D)
    (hcommon : CommonLowerWitness D) : MeetContinuous D := by
  letI : TopologicalSpace D := scottTopology D
  intro E hE p hp q hqp
  apply mem_closure_iff.mpr
  intro U hU hqU
  obtain ⟨r, hrU, hrq, e, ⟨d, hd, rfl⟩, hrd⟩ :=
    hcommon ⟨U, hU⟩ q hqU _ (directed_image hE) p.val
      (subtype_isLUB_ambient hL hD hE hp) hqp
  exact ⟨r, hrU, hrq, d, hd, hrd⟩

theorem secondCountable_of_restriction (hL : ScottSecondCountable L)
    (hρ : RestrictionFrameIsomorphism D) : ScottSecondCountable D := by
  letI : TopologicalSpace L := scottTopology L
  letI : TopologicalSpace D := scottTopology D
  letI : SecondCountableTopology L := hL
  have htop : scottTopology D = TopologicalSpace.induced Subtype.val (scottTopology L) := by
    apply TopologicalSpace.ext
    funext U
    apply propext
    rw [hρ.open_iff_trace U]
    rw [isOpen_induced_iff]
    constructor
    · rintro ⟨V, hV, rfl⟩
      exact ⟨V, hV, rfl⟩
    · rintro ⟨V, hV, hVU⟩
      exact ⟨V, hV, hVU.symm⟩
  rw [ScottSecondCountable, htop]
  infer_instance

theorem closed_restriction_of_open (hρ : RestrictionFrameIsomorphism D) :
    ClosedRestrictionIsomorphism D := by
  letI : TopologicalSpace L := scottTopology L
  letI : TopologicalSpace D := scottTopology D
  obtain ⟨ρ, hbij, htrace⟩ := hρ
  let e := orderIsoOfBijectiveFrameHom ρ hbij
  let cL : ScottCloseds L ≃o (ScottOpens L)ᵒᵈ := Closeds.complOrderIso L
  let cD : ScottCloseds D ≃o (ScottOpens D)ᵒᵈ := Closeds.complOrderIso D
  refine ⟨cL.trans (e.dual.trans cD.symm), ?_⟩
  intro C d
  change d ∉ ρ (⟨(C : Set L)ᶜ, C.isClosed.isOpen_compl⟩ : ScottOpens L) ↔ (d : L) ∈ C
  rw [htrace]
  simp

theorem noGreatest_of_approx [OrderTop L] (htop : (⊤ : L) ∉ D)
    (happrox : LowerNeighborhoodApproximation D) : NoGreatestElement D := by
  letI : TopologicalSpace L := scottTopology L
  rintro ⟨g, hg⟩
  have hgtop : (g : L) ≠ ⊤ := by intro heq; exact htop (heq ▸ g.property)
  have hU : @IsOpen L (scottTopology L) (Set.Iic (g : L))ᶜ := by
    letI : TopologicalSpace L := scottTopology L
    letI : Topology.IsScott L Set.univ := ⟨rfl⟩
    exact isClosed_Iic.isOpen_compl
  obtain ⟨d, hdU, _⟩ := happrox ⊤ ⟨_, hU⟩ (by
    change ¬ (⊤ : L) ≤ (g : L)
    intro h
    exact hgtop (le_antisymm le_top h))
  exact hdU (hg d)

theorem irreducible_of_approx [OrderTop L] (happrox : LowerNeighborhoodApproximation D)
    (hρ : RestrictionFrameIsomorphism D) :
    @IsIrreducible D (scottTopology D) Set.univ := by
  letI : TopologicalSpace L := scottTopology L
  letI : TopologicalSpace D := scottTopology D
  obtain ⟨ρ, hbij, htrace⟩ := hρ
  constructor
  · obtain ⟨d, _, _⟩ := happrox ⊤ ⊤ (by trivial)
    exact ⟨d, trivial⟩
  · intro U V hU hV hmeetU hmeetV
    obtain ⟨UL, hUL⟩ := hbij.2 (⟨U, hU⟩ : ScottOpens D)
    obtain ⟨VL, hVL⟩ := hbij.2 (⟨V, hV⟩ : ScottOpens D)
    obtain ⟨a, _, ha⟩ := hmeetU
    obtain ⟨b, _, hb⟩ := hmeetV
    have haUL : (a : L) ∈ UL := (htrace UL a).mp (by simpa only [hUL] using ha)
    have hbVL : (b : L) ∈ VL := (htrace VL b).mp (by simpa only [hVL] using hb)
    have htopU := ((isOpen_scott_iff _).mp UL.isOpen).1 (le_top (a := (a : L))) haUL
    have htopV := ((isOpen_scott_iff _).mp VL.isOpen).1 (le_top (a := (b : L))) hbVL
    obtain ⟨d, hdUV, _⟩ := happrox ⊤ (UL ⊓ VL) ⟨htopU, htopV⟩
    refine ⟨d, trivial, ?_, ?_⟩
    · have ht := (htrace UL d).mpr hdUV.1
      simpa only [hUL] using ht
    · have ht := (htrace VL d).mpr hdUV.2
      simpa only [hVL] using ht

/-- `thm:transfer` with precisely an arbitrary dcpo with bottom/top. -/
theorem transfer [OrderBot L] [OrderTop L]
    (hL : IsDcpo L) (hsecond : ScottSecondCountable L) (hcore : ScottCoreCompact L)
    (hD : IsSubDcpo D) (hbot : (⊥ : L) ∈ D) (htop : (⊤ : L) ∉ D)
    (happrox : LowerNeighborhoodApproximation D) (hcommon : CommonLowerWitness D) :
    TransferConclusion D := by
  have hρ := restriction_isomorphism hL hD happrox hcommon
  have hng := noGreatest_of_approx htop happrox
  refine {
    dcpo := subdcpo_isDcpo hL hD
    restriction := hρ
    upward_open := upward_isOpen hcommon
    upward_trace := upward_trace
    trace_upward := trace_upward happrox
    meetContinuous := meetContinuous_of_common hL hD hcommon
    compact := ?_
    secondCountable := secondCountable_of_restriction hsecond hρ
    coreCompact := scottCoreCompact_of_restriction D hcore hρ
    not_sober := not_scottSober_of_irreducible_univ (irreducible_of_approx happrox hρ) hng
    noGreatest := hng
    closed_restriction := closed_restriction_of_open hρ
    not_orderIso := ?_ }
  · letI : OrderBot D := { bot := ⟨⊥, hbot⟩, bot_le := fun _ ↦ bot_le }
    exact scottCompact_of_least (⊥ : D) (fun _ ↦ bot_le)
  · rintro ⟨e⟩
    apply hng
    exact ⟨e ⊤, fun d ↦ by
      obtain ⟨x, rfl⟩ := e.surjective d
      exact e.monotone le_top⟩

end CoreCompactSimplified
