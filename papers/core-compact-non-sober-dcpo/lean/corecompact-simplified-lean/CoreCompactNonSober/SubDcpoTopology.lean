import CoreCompactNonSober.ScottClosure

/-!
# Intrinsic Scott topology of a retained sub-dcpo

Source: `eq:approx`, `lem:localized-closure`, and `prop:trace`.

The construction-specific approximation and localized-closure statements
are hypotheses of these general implications, not axioms. Their existence
for the constructed set remains a separate proof obligation.
-/

set_option autoImplicit false

universe u

namespace CoreCompactNonSober

open Set TopologicalSpace

variable {L : Type u} [CompleteLattice L] {S : Set L}

/-- The exact static approximation property `eq:approx`, with the retained
point represented as an element of the subtype. -/
def LowerApproximation (S : Set L) : Prop :=
  ∀ (p : L) (U : ScottOpens L), p ∈ U →
    ∃ s : S, (s : L) ≤ p ∧ (s : L) ∈ U

/-- The actual source-localized lower set, in the intrinsic order on `S`. -/
def localizedLowerSet (S : Set L) (q : S) (E : Set L) : Set S :=
  {r | (r : L) ≤ (q : L) ∧ (r : L) ∈ lowerHull E}

/-- The exact two-stage local closure assertion of the manuscript. -/
def LocalizedClosure (S : Set L) : Prop :=
  ∀ E : Set L, NonemptyDirected E →
    ∀ q : S, (q : L) ≤ sSup E →
      q ∈ closureStage 2 (localizedLowerSet S q E)

/-- The literal Scott-closure conclusion printed in manuscript Lemma 4.11.
`LocalizedClosure` records the stronger two-stage witness used by the
construction; this theorem exposes the proved implication to the intrinsic
Scott closure of the retained subtype. -/
theorem localizedClosure_mem_scottClosure
    (hlocal : LocalizedClosure S) (E : Set L) (hE : NonemptyDirected E)
    (q : S) (hq : (q : L) ≤ sSup E) :
    q ∈ @closure S (scottTopology S) (localizedLowerSet S q E) :=
  closureStage_subset_closure 2 _ (hlocal E hE q hq)

theorem image_nonemptyDirected {E : Set S} (hE : NonemptyDirected E) :
    NonemptyDirected (Subtype.val '' E : Set L) := by
  refine ⟨hE.1.image Subtype.val, ?_⟩
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  obtain ⟨c, hc, hac, hbc⟩ := hE.2 a ha b hb
  exact ⟨c.val, ⟨c, hc, rfl⟩, hac, hbc⟩

/-- A supremum in a retained sub-dcpo is the ambient supremum, not merely
some potentially different least upper bound in the subtype. -/
theorem isLUB_subtype_ambient (hS : IsSubDcpo S) {E : Set S}
    (hE : NonemptyDirected E) {p : S} (hp : IsLUB E p) :
    IsLUB (Subtype.val '' E : Set L) (p : L) := by
  let F : Set L := Subtype.val '' E
  have hFS : F ⊆ S := by
    rintro _ ⟨e, _, rfl⟩
    exact e.property
  have hF := image_nonemptyDirected hE
  have hsup : sSup F ∈ S := hS F hFS hF (sSup F) (isLUB_sSup F)
  let qsup : S := ⟨sSup F, hsup⟩
  have hp_le : (p : L) ≤ sSup F := by
    have hpq : p ≤ qsup := hp.2 (fun e he ↦
      (le_sSup (Set.mem_image_of_mem Subtype.val he) : (e : L) ≤ sSup F))
    exact hpq
  have hsup_le : sSup F ≤ (p : L) := by
    apply sSup_le
    rintro _ ⟨e, he, rfl⟩
    exact hp.1 he
  have heq : sSup F = (p : L) := le_antisymm hsup_le hp_le
  exact heq ▸ isLUB_sSup F

theorem inclusion_scottContinuous (hS : IsSubDcpo S) :
    ScottContinuous (Subtype.val : S → L) := by
  intro E hne hdir p hp
  exact isLUB_subtype_ambient hS ⟨hne, hdir⟩ hp

theorem inclusion_continuous (hS : IsSubDcpo S) :
    @Continuous S L (scottTopology S) (scottTopology L) Subtype.val := by
  letI : TopologicalSpace L := scottTopology L
  letI : TopologicalSpace S := scottTopology S
  letI : Topology.IsScott L Set.univ := ⟨rfl⟩
  letI : Topology.IsScott S Set.univ := ⟨rfl⟩
  apply (Topology.IsScott.scottContinuousOn_iff_continuous
    (D := Set.univ) (fun _ _ _ ↦ Set.mem_univ _)).mp
  exact (inclusion_scottContinuous hS).scottContinuousOn

/-- The closed-trace extension `A_C` of `eq:closed-trace`. -/
def closedTraceExtension (S : Set L) (C : Set S) : Set L :=
  {p | ∀ q : S, (q : L) ≤ p → q ∈ C}

theorem closedTraceExtension_isScottClosed
    (hlocal : LocalizedClosure S) {C : Set S}
    (hC : @IsClosed S (scottTopology S) C) :
    IsScottClosed (closedTraceExtension S C) := by
  constructor
  · intro p r hpr hr q hqp
    exact hr q (hqp.trans hpr)
  · intro E hE hdir p hp q hqp
    have hqSup : (q : L) ≤ sSup E := by
      have heq : sSup E = p := (isLUB_sSup E).unique hp
      simpa only [heq] using hqp
    have hq := hlocal E hdir q hqSup
    apply closureStage_subset_closed 2 hC ?_ hq
    rintro r ⟨_, e, he, hre⟩
    exact hE he r hre

theorem closedTraceExtension_mem_iff {C : Set S}
    (hC : @IsClosed S (scottTopology S) C) (p : S) :
    (p : L) ∈ closedTraceExtension S C ↔ p ∈ C := by
  constructor
  · intro hp
    exact hp p le_rfl
  · intro hp q hqp
    have hlower := ((isClosed_scott_iff C).mp hC).1
    exact hlower hqp hp

/-- The canonical restriction frame homomorphism is obtained from the
proved continuous inclusion; arbitrary joins and finite meets are supplied
by mathlib's actual `Opens.comap`. -/
def restrictionFrameHom (hS : IsSubDcpo S) :
    FrameHom (ScottOpens L) (ScottOpens S) := by
  letI : TopologicalSpace L := scottTopology L
  letI : TopologicalSpace S := scottTopology S
  exact Opens.comap ⟨Subtype.val, inclusion_continuous hS⟩

@[simp] theorem restrictionFrameHom_mem (hS : IsSubDcpo S)
    (U : ScottOpens L) (s : S) :
    s ∈ restrictionFrameHom hS U ↔ (s : L) ∈ U :=
  Iff.rfl

theorem restrictionFrameHom_injective (hS : IsSubDcpo S)
    (happ : LowerApproximation S) : Function.Injective (restrictionFrameHom hS) := by
  letI : TopologicalSpace L := scottTopology L
  letI : TopologicalSpace S := scottTopology S
  intro U V heq
  apply Opens.ext
  ext p
  constructor
  · intro hp
    obtain ⟨s, hsp, hsU⟩ := happ p U hp
    have hsV : (s : L) ∈ V := by
      have hs : s ∈ restrictionFrameHom hS U := hsU
      rw [heq] at hs
      exact hs
    exact ((isOpen_scott_iff _).mp V.isOpen).1 hsp hsV
  · intro hp
    obtain ⟨s, hsp, hsV⟩ := happ p V hp
    have hsU : (s : L) ∈ U := by
      have hs : s ∈ restrictionFrameHom hS V := hsV
      rw [← heq] at hs
      exact hs
    exact ((isOpen_scott_iff _).mp U.isOpen).1 hsp hsU

theorem restrictionFrameHom_surjective (hS : IsSubDcpo S)
    (hlocal : LocalizedClosure S) : Function.Surjective (restrictionFrameHom hS) := by
  letI : TopologicalSpace L := scottTopology L
  letI : TopologicalSpace S := scottTopology S
  intro V
  let C : Set S := (V : Set S)ᶜ
  have hC : IsClosed C := V.isOpen.isClosed_compl
  let A : Set L := closedTraceExtension S C
  have hA : IsClosed A :=
    (isClosed_scott_iff A).mpr (closedTraceExtension_isScottClosed hlocal hC)
  let U : ScottOpens L := ⟨Aᶜ, hA.isOpen_compl⟩
  refine ⟨U, ?_⟩
  apply Opens.ext
  ext s
  change (s : L) ∉ A ↔ s ∈ V
  have ht := closedTraceExtension_mem_iff hC s
  simpa only [C, Set.mem_compl_iff, not_not] using not_congr ht

/-- `prop:trace`, reduced to precisely the preceding construction lemmas.
There is no assumed topology equality: it follows from localized closure. -/
theorem restrictionFrameIsomorphism_of_localizedClosure
    (hS : IsSubDcpo S) (happ : LowerApproximation S)
    (hlocal : LocalizedClosure S) : RestrictionFrameIsomorphism S :=
  ⟨restrictionFrameHom hS,
    ⟨restrictionFrameHom_injective hS happ,
      restrictionFrameHom_surjective hS hlocal⟩,
    restrictionFrameHom_mem hS⟩

/-- The meet-continuity conclusion of `thm:main` follows from the exact
localized closure assertion and ambient-supremum retention. -/
theorem meetContinuous_of_localizedClosure
    (hS : IsSubDcpo S) (hlocal : LocalizedClosure S) : MeetContinuous S := by
  intro E hE p hp q hqp
  let F : Set L := Subtype.val '' E
  have hF := image_nonemptyDirected hE
  have hpF : IsLUB F (p : L) := isLUB_subtype_ambient hS hE hp
  have heq : sSup F = (p : L) := (isLUB_sSup F).unique hpF
  have hq : q ∈ closureStage 2 (localizedLowerSet S q F) :=
    hlocal F hF q (by simpa only [heq] using hqp)
  have hsets : localizedLowerSet S q F = Set.Iic q ∩ lowerHull E := by
    ext r
    constructor
    · rintro ⟨hrq, e, ⟨s, hs, rfl⟩, hrs⟩
      exact ⟨hrq, s, hs, hrs⟩
    · rintro ⟨hrq, s, hs, hrs⟩
      exact ⟨hrq, s.val, ⟨s, hs, rfl⟩, hrs⟩
  rw [hsets] at hq
  exact closureStage_subset_closure 2 _ hq

end CoreCompactNonSober
