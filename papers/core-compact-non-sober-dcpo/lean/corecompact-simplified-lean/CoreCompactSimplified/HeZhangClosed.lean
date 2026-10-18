import CoreCompactSimplified.Transfer
import Mathlib.Order.Zorn
import Mathlib.Topology.Irreducible

/-!
He–Zhang Theorem 4.13, Claim 1 and its preliminary compact-set facts.

The intrinsic Scott topology on a Scott-closed sub-dcpo is proved equal to
the inherited topology; it is not assumed. Local compactness means the
source's compact saturated neighborhood sandwich. All directed sets remain
arbitrary nonempty directed sets, not sequences.
-/

set_option autoImplicit false

universe u

namespace CoreCompactSimplified.HeZhangClosed

open Set TopologicalSpace CoreCompactNonSober

section ClosedSubDcpo

variable {P : Type u} [PartialOrder P] {C : Set P}

local instance ambientScottTopology : TopologicalSpace P := scottTopology P
local instance closedScottTopology : TopologicalSpace C := scottTopology C

theorem closed_isSubDcpo (hC : IsClosed C) : IsSubDcpo C :=
  ((isClosed_scott_iff C).mp hC).2

theorem closed_isDcpo (hP : IsDcpo P) (hC : IsClosed C) : IsDcpo C :=
  subdcpo_isDcpo hP (closed_isSubDcpo hC)

/-- A relatively Scott-closed subset of a Scott-closed set is Scott closed
in the ambient order. This establishes the converse half of Claim 1. -/
theorem closed_image_isClosed (hC : IsClosed C) {A : Set C} (hA : IsClosed A) :
    IsClosed (Subtype.val '' A : Set P) := by
  have hC' := (isClosed_scott_iff C).mp hC
  have hA' := (isClosed_scott_iff A).mp hA
  apply (isClosed_scott_iff _).mpr
  constructor
  · intro x y hyx hx
    obtain ⟨a, ha, hax⟩ := hx
    have hxC : x ∈ C := hax ▸ a.property
    have hyC : y ∈ C := hC'.1 hyx hxC
    refine ⟨⟨y, hyC⟩, hA'.1 ?_ ha, rfl⟩
    change y ≤ a.val
    exact hax.symm ▸ hyx
  · intro E hEA hE s hs
    have hEC : E ⊆ C := by
      rintro x hx
      obtain ⟨a, _, rfl⟩ := hEA hx
      exact a.property
    have hsC : s ∈ C := hC'.2 E hEC hE s hs
    let F : Set C := Subtype.val ⁻¹' E
    have hF : NonemptyDirected F := by
      constructor
      · obtain ⟨x, hx⟩ := hE.1
        exact ⟨⟨x, hEC hx⟩, hx⟩
      · intro a ha b hb
        obtain ⟨z, hz, haz, hbz⟩ := hE.2 a.val ha b.val hb
        exact ⟨⟨z, hEC hz⟩, hz, haz, hbz⟩
    have hFA : F ⊆ A := by
      intro a ha
      obtain ⟨b, hb, hab⟩ := hEA ha
      have heq : b = a := Subtype.ext hab
      exact heq ▸ hb
    have hsF : IsLUB F (⟨s, hsC⟩ : C) := by
      constructor
      · intro a ha
        exact hs.1 ha
      · intro b hb
        apply hs.2
        intro x hx
        exact hb (show (⟨x, hEC hx⟩ : C) ∈ F from hx)
    exact ⟨⟨s, hsC⟩, hA'.2 F hFA hF _ hsF, rfl⟩

/-- He–Zhang Theorem 4.13 Claim 1, as an actual topology equality. -/
theorem scott_eq_induced (hP : IsDcpo P) (hC : IsClosed C) :
    scottTopology C = TopologicalSpace.induced Subtype.val (scottTopology P) := by
  apply TopologicalSpace.ext
  funext U
  apply propext
  constructor
  · intro hU
    have hA : IsClosed (Subtype.val '' Uᶜ : Set P) :=
      closed_image_isClosed hC hU.isClosed_compl
    apply isOpen_induced_iff.mpr
    refine ⟨(Subtype.val '' Uᶜ : Set P)ᶜ, hA.isOpen_compl, ?_⟩
    ext x
    simp
  · rintro ⟨V, hV, rfl⟩
    exact hV.preimage (CoreCompactSimplified.inclusion_continuous hP (closed_isSubDcpo hC))

theorem closed_secondCountable (hP : IsDcpo P) (hC : IsClosed C)
    (hsecond : ScottSecondCountable P) : ScottSecondCountable C := by
  rw [ScottSecondCountable, scott_eq_induced hP hC]
  letI : SecondCountableTopology P := hsecond
  infer_instance

theorem isUpperSet_of_saturated {K : Set P} (hK : IsSaturated K) : IsUpperSet K := by
  intro x y hxy hx
  rw [hK] at hx ⊢
  apply Set.mem_sInter.mpr
  intro U hU
  exact ((isOpen_scott_iff U).mp hU.1).1 hxy (Set.mem_sInter.mp hx U hU)

/-- Closed inheritance of the exact compact-saturated local compactness
notion, after the intrinsic/inherited-topology bridge has been proved. -/
theorem closed_locallyCompact (hP : IsDcpo P) (hC : IsClosed C)
    (hlc : ScottLocallyCompact P) : ScottLocallyCompact C := by
  intro U x hx
  have hU : @IsOpen C (TopologicalSpace.induced Subtype.val (scottTopology P))
      (U : Set C) := by
    rw [← scott_eq_induced hP hC]
    exact U.isOpen
  obtain ⟨V, hV, hVU⟩ := isOpen_induced_iff.mp hU
  have hxV : x.val ∈ V := by
    have : x ∈ Subtype.val ⁻¹' V := by simpa only [hVU] using hx
    exact this
  obtain ⟨W, K, hxW, hWK, hKV, hK, hsat⟩ := hlc ⟨V, hV⟩ x.val hxV
  let W' : ScottOpens C :=
    ⟨Subtype.val ⁻¹' (W : Set P),
      W.isOpen.preimage (CoreCompactSimplified.inclusion_continuous hP (closed_isSubDcpo hC))⟩
  refine ⟨W', Subtype.val ⁻¹' K, hxW, fun y hy ↦ hWK hy, ?_, ?_, ?_⟩
  · intro y hy
    have hyV : y ∈ Subtype.val ⁻¹' V := hKV hy
    simpa only [hVU] using hyV
  · have hcompact : @IsCompact C
        (TopologicalSpace.induced Subtype.val (scottTopology P))
        (Subtype.val ⁻¹' K) := by
      letI : TopologicalSpace C := TopologicalSpace.induced Subtype.val (scottTopology P)
      exact hC.isClosedEmbedding_subtypeVal.isCompact_preimage hK
    rw [← scott_eq_induced hP hC] at hcompact
    exact hcompact
  · apply isSaturated_of_isUpperSet_scott
    exact fun a b hab ha ↦ isUpperSet_of_saturated hsat hab ha

theorem closed_irreducible_univ (hP : IsDcpo P) (hC : IsClosed C)
    (hirr : IsIrreducible C) : IsIrreducible (Set.univ : Set C) := by
  have h : @IsIrreducible C
      (TopologicalSpace.induced Subtype.val (scottTopology P)) Set.univ := by
    letI : TopologicalSpace C := TopologicalSpace.induced Subtype.val (scottTopology P)
    letI : IrreducibleSpace C := Subtype.irreducibleSpace hirr
    exact IrreducibleSpace.isIrreducible_univ C
  rw [← scott_eq_induced hP hC] at h
  exact h

end ClosedSubDcpo

section CompactMinimal

variable {P : Type u} [PartialOrder P]

local instance minimalScottTopology : TopologicalSpace P := scottTopology P

theorem principal_lower_isClosed (p : P) : IsClosed (Set.Iic p) := by
  rw [← scott_closure_singleton p]
  exact isClosed_closure

/-- The minimal-point existence used by He–Zhang Lemma 4.3.
The proof uses compactness and the finite-intersection property for the
closed principal lower sets along a chain. -/
theorem compact_exists_minimal_le {K : Set P} (hK : IsCompact K)
    {x : P} (hx : x ∈ K) : ∃ m, m ≤ x ∧ Minimal (· ∈ K) m := by
  classical
  apply @zorn_le_nonempty₀ Pᵒᵈ _ K ?_ x hx
  intro c hcK hc y hy
  have hfinite : ∀ F : Finset c, ∃ z ∈ c,
      ∀ a ∈ F, OrderDual.ofDual z ≤ OrderDual.ofDual a.val := by
    intro F
    induction F using Finset.induction_on with
    | empty => exact ⟨y, hy, by simp⟩
    | @insert a F ha ih =>
      obtain ⟨z, hz, hF⟩ := ih
      obtain ⟨w, hw, haw, hzw⟩ := hc.directedOn a.val a.property z hz
      refine ⟨w, hw, ?_⟩
      intro b hb
      rcases Finset.mem_insert.mp hb with rfl | hb
      · exact haw
      · have hwz : OrderDual.ofDual w ≤ OrderDual.ofDual z := hzw
        exact hwz.trans (hF b hb)
  obtain ⟨m, hmK, hm⟩ := hK.inter_iInter_nonempty
    (fun a : c ↦ Set.Iic (OrderDual.ofDual a.val))
    (fun a ↦ principal_lower_isClosed (P := P) (OrderDual.ofDual a.val)) (by
      intro F
      obtain ⟨z, hz, hF⟩ := hfinite F
      exact ⟨z, hcK hz, Set.mem_iInter.mpr (fun a ↦
        Set.mem_iInter.mpr (fun ha ↦ hF a ha))⟩)
  exact ⟨m, hmK, fun a ha ↦ Set.mem_iInter.mp hm ⟨a, ha⟩⟩

/-- The actual set of minimal points; minimality is in the inherited order,
not an arbitrary choice of one representative for each compact-set point. -/
def minimalPoints (K : Set P) : Set P := {m | Minimal (· ∈ K) m}

theorem minimalPoints_subset (K : Set P) : minimalPoints K ⊆ K := fun _ hm ↦ hm.1

/-- The first assertion of He–Zhang Lemma 4.3. -/
theorem compact_saturated_eq_upper_minimal {K : Set P} (hK : IsCompact K)
    (hsat : IsSaturated K) : K = upperHull (minimalPoints K) := by
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨m, hmx, hm⟩ := compact_exists_minimal_le hK hx
    exact ⟨m, hm, hmx⟩
  · rintro x ⟨m, hm, hmx⟩
    exact isUpperSet_of_saturated hsat hmx hm.1

/-- The second assertion of He–Zhang Lemma 4.3. The open cover of the
minimal points covers every compact-set point above them, because Scott
opens are upper. Compactness is therefore transferred without assuming
Hausdorffness or that the minimal-point set is closed. -/
theorem compact_minimalPoints {K : Set P} (hK : IsCompact K) :
    IsCompact (minimalPoints K) := by
  rw [isCompact_iff_finite_subcover]
  intro ι O hO hcover
  have hKcover : K ⊆ ⋃ i, O i := by
    intro x hx
    obtain ⟨m, hmx, hm⟩ := compact_exists_minimal_le hK hx
    obtain ⟨i, hmi⟩ := Set.mem_iUnion.mp (hcover hm)
    exact Set.mem_iUnion.mpr ⟨i, ((isOpen_scott_iff _).mp (hO i)).1 hmx hmi⟩
  obtain ⟨F, hF⟩ := hK.elim_finite_subcover O hO hKcover
  exact ⟨F, (minimalPoints_subset K).trans hF⟩

theorem compact_saturated_minimal (K : Set P) (hK : IsCompact K)
    (hsat : IsSaturated K) :
    K = upperHull (minimalPoints K) ∧ IsCompact (minimalPoints K) :=
  ⟨compact_saturated_eq_upper_minimal hK hsat, compact_minimalPoints hK⟩

end CompactMinimal

end CoreCompactSimplified.HeZhangClosed
