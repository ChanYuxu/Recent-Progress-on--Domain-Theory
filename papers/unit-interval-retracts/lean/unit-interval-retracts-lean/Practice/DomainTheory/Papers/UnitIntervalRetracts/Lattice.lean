import Practice.DomainTheory.Papers.UnitIntervalRetracts.SkeletonFiniteness

/-!
# Complete lattice and filtered compactness

This file proves `prop:complete-lattice`, `eq:sup-as-intersection`,
`lem:filtered-compactness`, and `cor:top-in-directed-family` from the source.
The arbitrary-supremum operation is constructed explicitly from intersections
of represented subsets.
-/

set_option autoImplicit false
set_option linter.unnecessarySimpa false

namespace UnitIntervalRetracts

open Set Filter Topology
open AbramskyJung.Chapter2

noncomputable section

/-- The source's skeleton-finiteness clause (3), packaged for the lattice
construction. -/
def SkeletonFiniteAbove : Prop :=
  ∀ ε : ℝ, 0 < ε →
    {B : Set X | B ∈ Skeleton ∧ ε ≤ Metric.diam B}.Finite

theorem skeletonFiniteAbove : SkeletonFiniteAbove :=
  fun _ε hε => skeleton_large_diameter_finite hε

/-- Every subset of the compact metric space `X` is bounded. -/
theorem isBounded_subset_X (A : Set X) : Bornology.IsBounded A :=
  isCompact_univ.isBounded.subset (Set.subset_univ A)

/-- Every carrier represented in `P` is closed in `X`. -/
theorem isClosed_carrier (A : P) : IsClosed (A : Set X) := by
  rcases A.isSparse with hA | ⟨x, hx⟩ | hA
  · exact Skeleton.isClosed hA
  · rw [hx]
    exact isClosed_singleton
  · rw [hA]
    exact isClosed_empty

/-- Every carrier represented in `P` is compact. -/
theorem isCompact_carrier (A : P) : IsCompact (A : Set X) :=
  (isClosed_carrier A).isCompact

/-- A finite nonempty intersection of skeleton members is again a skeleton
member as soon as the intersection is nontrivial. -/
theorem skeleton_sInter_of_finite_nonempty
    {𝒜 : Set (Set X)}
    (hfinite : 𝒜.Finite)
    (hnonempty : 𝒜.Nonempty)
    (hskeleton : ∀ A ∈ 𝒜, A ∈ Skeleton)
    (hnontrivial : (⋂₀ 𝒜).Nontrivial) :
    ⋂₀ 𝒜 ∈ Skeleton := by
  revert hnonempty hskeleton hnontrivial
  induction 𝒜, hfinite using Set.Finite.induction_on with
  | empty =>
      intro hnonempty
      simpa using hnonempty
  | @insert A 𝒜 hA hfinite ih =>
      intro _hnonempty hskeleton hnontrivial
      by_cases h𝒜empty : 𝒜 = ∅
      · subst 𝒜
        simpa using hskeleton A (by simp)
      · have h𝒜nonempty : 𝒜.Nonempty :=
          Set.nonempty_iff_ne_empty.mpr h𝒜empty
        have hA_skeleton : A ∈ Skeleton :=
          hskeleton A (Set.mem_insert A 𝒜)
        have hrest_skeleton : ⋂₀ 𝒜 ∈ Skeleton := by
          apply ih h𝒜nonempty
          · intro B hB
            exact hskeleton B (Set.mem_insert_of_mem A hB)
          · apply hnontrivial.mono
            rw [Set.sInter_insert]
            exact Set.inter_subset_right
        rw [Set.sInter_insert]
        apply skeleton_inter_of_nontrivial hA_skeleton hrest_skeleton
        simpa only [Set.sInter_insert] using hnontrivial

/-- The set-theoretic intersection underlying the supremum in reverse
inclusion order.  The empty indexed intersection is `X`. -/
def carrierIntersection (𝒜 : Set P) : Set X :=
  ⋂ A : 𝒜, (A.1 : Set X)

theorem carrierIntersection_subset {𝒜 : Set P} {A : P} (hA : A ∈ 𝒜) :
    carrierIntersection 𝒜 ⊆ (A : Set X) := by
  intro x hx
  exact Set.mem_iInter.mp hx ⟨A, hA⟩

/-- Closure of `P` under arbitrary intersections. -/
theorem carrierIntersection_isSparse
    (hfiniteAbove : SkeletonFiniteAbove)
    (𝒜 : Set P) :
    IsSparse (carrierIntersection 𝒜) := by
  classical
  by_cases h𝒜empty : 𝒜 = ∅
  · left
    simpa [carrierIntersection, h𝒜empty] using univ_mem_skeleton
  · let S : Set X := carrierIntersection 𝒜
    by_cases hS : S.Nontrivial
    · left
      have h𝒜nonempty : 𝒜.Nonempty :=
        Set.nonempty_iff_ne_empty.mpr h𝒜empty
      let carriers : Set (Set X) :=
        Set.range (fun A : 𝒜 => (A.1 : Set X))
      have hcarrier_skeleton :
          ∀ B ∈ carriers, B ∈ Skeleton := by
        intro B hB
        rcases hB with ⟨A, rfl⟩
        rcases A.1.isSparse with hskel | ⟨x, hx⟩ | hempty
        · exact hskel
        · exfalso
          apply hS.not_subset_singleton
          rw [← hx]
          exact carrierIntersection_subset A.2
        · exfalso
          apply hS.not_subset_empty
          rw [← hempty]
          exact carrierIntersection_subset A.2
      have hS_bounded : Bornology.IsBounded S :=
        isBounded_subset_X S
      have hdiam_pos : 0 < Metric.diam S :=
        Metric.diam_pos hS hS_bounded
      have hcarriers_finite : carriers.Finite := by
        apply (hfiniteAbove (Metric.diam S) hdiam_pos).subset
        intro B hB
        refine ⟨hcarrier_skeleton B hB, ?_⟩
        rcases hB with ⟨A, rfl⟩
        apply Metric.diam_mono (carrierIntersection_subset A.2)
        exact isBounded_subset_X (A.1 : Set X)
      have hcarriers_nonempty : carriers.Nonempty := by
        rcases h𝒜nonempty with ⟨A, hA⟩
        exact ⟨(A : Set X), ⟨⟨A, hA⟩, rfl⟩⟩
      have hsInter_skeleton :
          ⋂₀ carriers ∈ Skeleton :=
        skeleton_sInter_of_finite_nonempty hcarriers_finite
          hcarriers_nonempty hcarrier_skeleton (by
            simpa only [S, carriers, Set.sInter_range] using hS)
      simpa only [S, carriers, Set.sInter_range, carrierIntersection] using
        hsInter_skeleton
    · have hSsubsingleton : S.Subsingleton :=
        Set.not_nontrivial_iff.mp hS
      rcases hSsubsingleton.eq_empty_or_singleton with hSempty | ⟨x, hx⟩
      · exact Or.inr (Or.inr (by simpa only [S] using hSempty))
      · exact Or.inr (Or.inl ⟨x, by simpa only [S] using hx⟩)

/-- The candidate supremum, with carrier equal to the intersection. -/
def intersectionSup (hfiniteAbove : SkeletonFiniteAbove) (𝒜 : Set P) : P :=
  ⟨carrierIntersection 𝒜, carrierIntersection_isSparse hfiniteAbove 𝒜⟩

@[simp]
theorem coe_intersectionSup
    (hfiniteAbove : SkeletonFiniteAbove) (𝒜 : Set P) :
    (intersectionSup hfiniteAbove 𝒜 : Set X) = carrierIntersection 𝒜 :=
  rfl

/-- Every family has a least upper bound, namely its carrier intersection. -/
theorem isLUB_intersectionSup
    (hfiniteAbove : SkeletonFiniteAbove) (𝒜 : Set P) :
    IsLUB 𝒜 (intersectionSup hfiniteAbove 𝒜) := by
  constructor
  · intro A hA
    change carrierIntersection 𝒜 ⊆ (A : Set X)
    exact carrierIntersection_subset hA
  · intro B hB
    change (B : Set X) ⊆ carrierIntersection 𝒜
    intro x hx
    rw [carrierIntersection, Set.mem_iInter]
    intro A
    exact hB A.2 hx

/-- Complete-semilattice structure whose arbitrary supremum is literal
intersection of carriers. -/
@[reducible]
def completeSemilatticeSupOfSkeletonFinite
    (hfiniteAbove : SkeletonFiniteAbove) :
    CompleteSemilatticeSup P where
  sSup := intersectionSup hfiniteAbove
  isLUB_sSup := isLUB_intersectionSup hfiniteAbove

/-- The source complete lattice, derived from the explicit arbitrary-supremum
construction. -/
@[reducible]
def completeLatticeOfSkeletonFinite
    (hfiniteAbove : SkeletonFiniteAbove) :
    CompleteLattice P := by
  letI : CompleteSemilatticeSup P :=
    completeSemilatticeSupOfSkeletonFinite hfiniteAbove
  exact completeLatticeOfCompleteSemilatticeSup P

noncomputable instance : CompleteLattice P :=
  completeLatticeOfSkeletonFinite skeletonFiniteAbove

/-- Equation `eq:sup-as-intersection`. -/
@[simp]
theorem coe_sSup_eq_carrierIntersection (𝒜 : Set P) :
    ((sSup 𝒜 : P) : Set X) = carrierIntersection 𝒜 := by
  rfl

theorem top_eq_empty : (⊤ : P) = empty := by
  apply le_antisymm
  · exact le_empty _
  · exact le_top

theorem bot_eq_whole : (⊥ : P) = whole := by
  apply le_antisymm
  · exact bot_le
  · exact whole_le _

@[simp] theorem coe_top : ((⊤ : P) : Set X) = ∅ := by
  rw [top_eq_empty, coe_empty]

@[simp] theorem coe_bot : ((⊥ : P) : Set X) = Set.univ := by
  rw [bot_eq_whole, coe_whole]

/-- Lemma `lem:filtered-compactness`. -/
theorem filteredCompactness
    {𝒟 : Set P}
    (h𝒟 : DirectedSet 𝒟)
    {O : Set X}
    (hO : IsOpen O)
    (hsub : carrierIntersection 𝒟 ⊆ O) :
    ∃ D ∈ 𝒟, (D : Set X) ⊆ O := by
  letI : Nonempty 𝒟 := Set.nonempty_coe_sort.mpr h𝒟.1
  let V : 𝒟 → Set X := fun D => (D.1 : Set X)
  have hV_directed : Directed (· ⊇ ·) V := by
    intro A B
    rcases h𝒟.2 A.2 B.2 with ⟨C, hC, hAC, hBC⟩
    refine ⟨⟨C, hC⟩, ?_, ?_⟩
    · exact hAC
    · exact hBC
  have hV_compact : ∀ D : 𝒟, IsCompact (V D) := by
    intro D
    exact isCompact_carrier D.1
  have hV_closed : ∀ D : 𝒟, IsClosed (V D) := by
    intro D
    exact isClosed_carrier D.1
  have hO_nhds : ∀ x ∈ ⋂ D : 𝒟, V D, O ∈ 𝓝 x := by
    intro x hx
    apply hO.mem_nhds
    apply hsub
    simpa only [carrierIntersection, V] using hx
  rcases exists_subset_nhds_of_isCompact'
      hV_directed hV_compact hV_closed hO_nhds with ⟨D, hDO⟩
  exact ⟨D.1, D.2, hDO⟩

/-- Corollary `cor:top-in-directed-family`, first in its literal carrier form. -/
theorem empty_mem_of_directed_carrierIntersection
    {𝒟 : Set P}
    (h𝒟 : DirectedSet 𝒟)
    (hempty : carrierIntersection 𝒟 = ∅) :
    empty ∈ 𝒟 := by
  rcases filteredCompactness h𝒟 isOpen_empty (by simpa [hempty]) with
    ⟨D, hD, hDempty⟩
  have hcarrier : (D : Set X) = ∅ :=
    Set.eq_empty_iff_forall_notMem.mpr (fun x hx => hDempty hx)
  have hD_eq : D = empty := by
    apply SetLike.coe_injective
    simpa only [coe_empty] using hcarrier
  simpa only [hD_eq] using hD

theorem top_mem_of_directed_sSup_eq_top
    {𝒟 : Set P} (h𝒟 : DirectedSet 𝒟) (hsup : sSup 𝒟 = (⊤ : P)) :
    (⊤ : P) ∈ 𝒟 := by
  rw [top_eq_empty] at hsup ⊢
  apply empty_mem_of_directed_carrierIntersection h𝒟
  rw [← coe_sSup_eq_carrierIntersection 𝒟, hsup, coe_empty]

end

end UnitIntervalRetracts
