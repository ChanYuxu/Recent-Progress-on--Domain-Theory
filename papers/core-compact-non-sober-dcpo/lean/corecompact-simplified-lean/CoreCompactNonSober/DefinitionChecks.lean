import CoreCompactNonSober.FrameRestriction
import CoreCompactNonSober.AmbientDefinitions

/-!
# Definition and encoding checks

These small proofs verify semantic bridges in the definitions. They do not
prove or assume the manuscript's counterexample theorem.
-/

set_option autoImplicit false

universe u

namespace CoreCompactNonSober

open Set TopologicalSpace

section Order

variable {P : Type u} [PartialOrder P]

/-- Pairwise directedness plus nonemptiness is equivalent to existence of
an upper bound in the set for every finite subset, including the empty one. -/
theorem nonemptyDirected_iff_finite_bounds (E : Set P) :
    NonemptyDirected E ↔
      ∀ F : Finset P, (↑F : Set P) ⊆ E →
        ∃ e ∈ E, ∀ f ∈ F, f ≤ e := by
  classical
  constructor
  · rintro ⟨hne, hdir⟩ F
    induction F using Finset.induction_on with
    | empty =>
      intro _
      obtain ⟨e, he⟩ := hne
      exact ⟨e, he, by simp⟩
    | @insert a F _ ih =>
      intro hFE
      obtain ⟨b, hb, hFb⟩ := ih (by
        intro f hf
        exact hFE (Finset.mem_insert_of_mem hf))
      have ha : a ∈ E := hFE (Finset.mem_insert_self a F)
      obtain ⟨c, hc, hac, hbc⟩ := hdir a ha b hb
      refine ⟨c, hc, ?_⟩
      intro f hf
      rcases Finset.mem_insert.mp hf with rfl | hf
      · exact hac
      · exact (hFb f hf).trans hbc
  · intro h
    obtain ⟨e, he, _⟩ := h ∅ (by simp)
    refine ⟨⟨e, he⟩, ?_⟩
    intro a ha b hb
    have hpair : (↑({a, b} : Finset P) : Set P) ⊆ E := by
      intro f hf
      simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hf
      rcases hf with rfl | rfl
      · exact ha
      · exact hb
    obtain ⟨c, hc, hbound⟩ := h {a, b} hpair
    exact ⟨c, hc, hbound a (by simp), hbound b (by simp)⟩

/-- The explicit Scott-open definition agrees with mathlib's intrinsic
Scott topology, with no dcpo or countability assumptions hidden in the bridge. -/
theorem isOpen_scott_iff (U : Set P) :
    @IsOpen P (scottTopology P) U ↔ IsScottOpen U := by
  letI : TopologicalSpace P := scottTopology P
  letI : Topology.IsScott P Set.univ := ⟨rfl⟩
  rw [Topology.IsScott.isOpen_iff_isUpperSet_and_dirSupInaccOn (D := Set.univ)]
  constructor
  · rintro ⟨hu, hd⟩
    refine ⟨hu, ?_⟩
    intro E hE p hp hpU
    obtain ⟨e, heE, heU⟩ := hd (Set.mem_univ E) hE.1 hE.2 hp hpU
    exact ⟨e, heE, heU⟩
  · rintro ⟨hu, hd⟩
    refine ⟨hu, ?_⟩
    intro E _ hne hdir p hp hpU
    obtain ⟨e, heE, heU⟩ := hd E ⟨hne, hdir⟩ p hp hpU
    exact ⟨e, heE, heU⟩

theorem isClosed_scott_iff (C : Set P) :
    @IsClosed P (scottTopology P) C ↔ IsScottClosed C := by
  letI : TopologicalSpace P := scottTopology P
  letI : Topology.IsScott P Set.univ := ⟨rfl⟩
  rw [Topology.IsScott.isClosed_iff_isLowerSet_and_dirSupClosed]
  constructor
  · rintro ⟨hl, hd⟩
    exact ⟨hl, fun E hEC hE p hp ↦ hd hEC hE.1 hE.2 hp⟩
  · rintro ⟨hl, hd⟩
    exact ⟨hl, fun E hEC hne hdir p hp ↦ hd E hEC ⟨hne, hdir⟩ p hp⟩

theorem scott_closure_singleton (p : P) :
    @closure P (scottTopology P) ({p} : Set P) = Set.Iic p := by
  letI : TopologicalSpace P := scottTopology P
  letI : Topology.IsScott P Set.univ := ⟨rfl⟩
  exact Topology.IsScott.closure_singleton

/-- The direction of the specialization order matches the source exactly. -/
theorem specializationLE_scott_iff (p q : P) :
    @SpecializationLE P (scottTopology P) p q ↔ p ≤ q := by
  change p ∈ @closure P (scottTopology P) ({q} : Set P) ↔ p ≤ q
  rw [scott_closure_singleton]
  rfl

end Order

section DirectedCompleteness

variable {L : Type u} [CompleteLattice L]

theorem completeLattice_isDcpo : IsDcpo L := by
  intro E _
  exact ⟨sSup E, isLUB_sSup E⟩

theorem isSubDcpo_iff_sSup_mem (S : Set L) :
    IsSubDcpo S ↔
      ∀ E : Set L, E ⊆ S → NonemptyDirected E → sSup E ∈ S := by
  constructor
  · intro h E hES hE
    exact h E hES hE (sSup E) (isLUB_sSup E)
  · intro h E hES hE p hp
    have heq : sSup E = p := (isLUB_sSup E).unique hp
    rw [← heq]
    exact h E hES hE

/-- The explicit `IsDcpo S` field in the main statement is redundant,
because ambient directed-supremum closure supplies it. -/
theorem isSubDcpo_isDcpo {S : Set L} (hS : IsSubDcpo S) : IsDcpo S := by
  intro E hE
  let F : Set L := Subtype.val '' E
  have hFS : F ⊆ S := by
    rintro _ ⟨e, _, rfl⟩
    exact e.property
  have hFne : F.Nonempty := hE.1.image Subtype.val
  have hFdir : DirectedOn (· ≤ ·) F := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    obtain ⟨c, hc, hac, hbc⟩ := hE.2 a ha b hb
    exact ⟨c.val, ⟨c, hc, rfl⟩, hac, hbc⟩
  have hsup : sSup F ∈ S :=
    hS F hFS ⟨hFne, hFdir⟩ (sSup F) (isLUB_sSup F)
  refine ⟨⟨sSup F, hsup⟩, ?_⟩
  constructor
  · intro e he
    exact le_sSup (Set.mem_image_of_mem Subtype.val he)
  · intro b hb
    exact sSup_le (by rintro _ ⟨e, he, rfl⟩; exact hb he)

end DirectedCompleteness

section Topological

variable {X : Type u} [TopologicalSpace X]

/-- Mathlib compactness is precisely the open-cover definition used in the
source, with no separation hypothesis. -/
theorem isCompact_iff_source (K : Set X) :
    IsCompact K ↔ ∀ {ι : Type u} (U : ι → Set X),
      (∀ i, IsOpen (U i)) → K ⊆ ⋃ i, U i →
        ∃ F : Finset ι, K ⊆ ⋃ i ∈ F, U i :=
  isCompact_iff_finite_subcover

theorem opens_sSup_coe (D : Set (Opens X)) :
    ((sSup D : Opens X) : Set X) =
      ⋃₀ ((fun U : Opens X ↦ (U : Set X)) '' D) := by
  simp only [Opens.coe_sSup, Set.sUnion_image]

theorem isIrreducible_iff_source (C : Set X) :
    IsIrreducible C ↔ C.Nonempty ∧
      ∀ U V : Set X, IsOpen U → IsOpen V →
        (C ∩ U).Nonempty → (C ∩ V).Nonempty → (C ∩ (U ∩ V)).Nonempty :=
  Iff.rfl

/-- In a T0 space, the manuscript's uniqueness formulation is equivalent
to mathlib's existence-only `QuasiSober` class. -/
theorem isSober_iff_quasiSober [T0Space X] : IsSober X ↔ QuasiSober X := by
  constructor
  · intro h
    constructor
    intro C hC hclosed
    obtain ⟨x, hx, _⟩ := h C hclosed hC
    exact ⟨x, hx⟩
  · intro h
    letI : QuasiSober X := h
    intro C hclosed hC
    obtain ⟨x, hx⟩ := QuasiSober.sober hC hclosed
    refine ⟨x, hx, ?_⟩
    intro y hy
    exact (show IsGenericPoint y C from hy).eq hx

theorem secondCountable_iff_countable_basis :
    SecondCountableTopology X ↔
      ∃ B : Set (Set X), B.Countable ∧ IsTopologicalBasis B := by
  constructor
  · intro h
    letI : SecondCountableTopology X := h
    obtain ⟨B, hcount, _, hbasis⟩ := TopologicalSpace.exists_countable_basis X
    exact ⟨B, hcount, hbasis⟩
  · rintro ⟨B, hcount, hbasis⟩
    exact hbasis.secondCountableTopology hcount

/-- A way-below open is contained in its target. This is derived from the
definition, rather than silently imposed as an extra assumption. -/
theorem OpenWayBelow.le {V U : Opens X} (h : OpenWayBelow V U) : V ≤ U := by
  have hne : ({U} : Set (Opens X)).Nonempty := Set.singleton_nonempty U
  have hdir : DirectedOn (· ≤ ·) ({U} : Set (Opens X)) := by
    intro a ha b hb
    have ha' : a = U := Set.mem_singleton_iff.mp ha
    have hb' : b = U := Set.mem_singleton_iff.mp hb
    subst a
    subst b
    exact ⟨U, by simp, le_rfl, le_rfl⟩
  obtain ⟨W, hW, hVW⟩ := h {U} hne hdir (by simp)
  simpa only [Set.mem_singleton_iff.mp hW] using hVW

end Topological

section Restriction

variable {L : Type u} [PartialOrder L] {S : Set L}

/-- The formal restriction-isomorphism condition really identifies every
intrinsic Scott open of `S` with the trace of an ambient Scott open. -/
theorem RestrictionFrameIsomorphism.open_iff_trace
    (hS : RestrictionFrameIsomorphism S) (V : Set S) :
    @IsOpen S (scottTopology S) V ↔
      ∃ U : Set L, @IsOpen L (scottTopology L) U ∧
        V = Subtype.val ⁻¹' U := by
  letI : TopologicalSpace L := scottTopology L
  letI : TopologicalSpace S := scottTopology S
  obtain ⟨ρ, hbij, htrace⟩ := hS
  constructor
  · intro hV
    let Vopen : ScottOpens S := ⟨V, hV⟩
    obtain ⟨U, hU⟩ := hbij.2 Vopen
    refine ⟨U, U.isOpen, ?_⟩
    ext s
    change s ∈ Vopen ↔ (s : L) ∈ U
    rw [← hU]
    exact htrace U s
  · rintro ⟨U, hU, rfl⟩
    let Uopen : ScottOpens L := ⟨U, hU⟩
    have heq : Subtype.val ⁻¹' U = ((ρ Uopen : ScottOpens S) : Set S) := by
      ext s
      exact (htrace Uopen s).symm
    rw [heq]
    exact (ρ Uopen).isOpen

end Restriction

end CoreCompactNonSober
