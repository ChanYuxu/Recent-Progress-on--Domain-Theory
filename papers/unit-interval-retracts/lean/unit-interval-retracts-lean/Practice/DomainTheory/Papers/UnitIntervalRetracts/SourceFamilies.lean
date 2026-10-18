import Practice.DomainTheory.Papers.UnitIntervalRetracts.IntervalGeometry
import Practice.DomainTheory.Papers.UnitIntervalRetracts.Quasicontinuity

/-!
# The source approximation families `F_m(K)`

This file recovers `eq:Fm-definition`, `lem:Fm-way-below`,
`lem:Fm-cofinal`, and `lem:Fm-intersection`.  Lean uses zero-based indices, so
`Fm 0 K` corresponds to the first source family.
-/

set_option autoImplicit false
set_option linter.unnecessarySimpa false

namespace UnitIntervalRetracts
namespace SourceFamilies

open Set Filter Topology
open AbramskyJung.Chapter2

noncomputable section

theorem skeleton_of_ne_top_of_not_singleton
    (K : P) (hTop : K ≠ ⊤)
    (hSingleton : ¬ ∃ x : X, K = singleton x) :
    (K : Set X) ∈ Skeleton := by
  rcases K.isSparse with hSkeleton | ⟨x, hx⟩ | hEmpty
  · exact hSkeleton
  · exfalso
    apply hSingleton
    refine ⟨x, ?_⟩
    apply SetLike.coe_injective
    simpa only [coe_singleton] using hx
  · exfalso
    apply hTop
    apply SetLike.coe_injective
    rw [coe_top]
    exact hEmpty

/-- Equation `eq:Fm-definition`, zero-based. -/
noncomputable def Fm (m : ℕ) (K : P) : FiniteFamily P :=
  by
    classical
    exact
      if hTop : K = ⊤ then
        AbstractApproximation.singletonFiniteFamily (⊤ : P)
      else if hSingleton : ∃ x : X, K = singleton x then
        AbstractApproximation.singletonFiniteFamily
          (selectedNeighborhood hSingleton.choose m)
      else
        ⟨({K, selectedNeighborhood (sInf (K : Set X)) m,
            selectedNeighborhood (sSup (K : Set X)) m} : Set P),
          by simp,
          by simp⟩

/-- Lemma `lem:Fm-way-below`. -/
theorem Fm_finiteWayBelow (K : P) (m : ℕ) :
    FiniteWayBelow (Fm m K) K := by
  classical
  unfold Fm
  split
  next hTop =>
    subst K
    exact finiteWayBelow_top _
  next hTop =>
    split
    next hSingleton =>
      have hKx : K = singleton hSingleton.choose :=
        hSingleton.choose_spec
      have hKcarrier : (K : Set X) = {hSingleton.choose} :=
        congrArg (fun A : P => (A : Set X)) hKx
      apply (finiteWayBelow_iff _ K).2
      constructor
      · refine
          ⟨selectedNeighborhood hSingleton.choose m, by simp, ?_⟩
        rw [hKcarrier, Set.singleton_subset_iff]
        exact
          interior_subset
            (point_mem_interior_selectedNeighborhood hSingleton.choose m)
      · intro y hyK
        have hyx : y = hSingleton.choose := by
          rw [hKcarrier] at hyK
          simpa using hyK
        subst y
        simpa using
          point_mem_interior_selectedNeighborhood hSingleton.choose m
    next hSingleton =>
      have hSkeleton :=
        skeleton_of_ne_top_of_not_singleton K hTop hSingleton
      apply (finiteWayBelow_iff _ K).2
      constructor
      · refine ⟨K, ?_, Set.Subset.rfl⟩
        change K ∈
          ({K, selectedNeighborhood (sInf (K : Set X)) m,
            selectedNeighborhood (sSup (K : Set X)) m} : Set P)
        simp
      · intro x hxK
        by_cases hxInterior : x ∈ interior (K : Set X)
        · rw [Set.mem_iUnion]
          refine ⟨K, ?_⟩
          rw [Set.mem_iUnion]
          refine ⟨?_, hxInterior⟩
          change K ∈
            ({K, selectedNeighborhood (sInf (K : Set X)) m,
              selectedNeighborhood (sSup (K : Set X)) m} : Set P)
          simp
        · have hxBoundary : x ∈
              (K : Set X) \ interior (K : Set X) :=
            ⟨hxK, hxInterior⟩
          have hxEndpoint :=
            Skeleton.diff_interior_subset_endpoints hSkeleton hxBoundary
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hxEndpoint
          rcases hxEndpoint with hxLeft | hxRight
          · subst x
            rw [Set.mem_iUnion]
            refine ⟨selectedNeighborhood (sInf (K : Set X)) m, ?_⟩
            rw [Set.mem_iUnion]
            refine ⟨?_,
              point_mem_interior_selectedNeighborhood
                (sInf (K : Set X)) m⟩
            change selectedNeighborhood (sInf (K : Set X)) m ∈
              ({K, selectedNeighborhood (sInf (K : Set X)) m,
                selectedNeighborhood (sSup (K : Set X)) m} : Set P)
            simp
          · subst x
            rw [Set.mem_iUnion]
            refine ⟨selectedNeighborhood (sSup (K : Set X)) m, ?_⟩
            rw [Set.mem_iUnion]
            refine ⟨?_,
              point_mem_interior_selectedNeighborhood
                (sSup (K : Set X)) m⟩
            change selectedNeighborhood (sSup (K : Set X)) m ∈
              ({K, selectedNeighborhood (sInf (K : Set X)) m,
                selectedNeighborhood (sSup (K : Set X)) m} : Set P)
            simp

/-- Selected neighbourhoods are eventually contained in every set whose
relative interior contains their center. -/
theorem eventually_selectedNeighborhood_subset
    {x : X} {A : Set X} (hx : x ∈ interior A) :
    ∃ n : ℕ, ∀ m ≥ n,
      (selectedNeighborhood x m : Set X) ⊆ A := by
  let data := sparseIntervalData
  have hDirected :
      DirectedSet (Set.range (selectedNeighborhood x)) :=
    data.neighborhood_directed x
  have hSupSubset :
      (data.realized (data.sup (Set.range (selectedNeighborhood x)))) ⊆
        interior A := by
    have hSupEq :
        sSup (Set.range (selectedNeighborhood x)) = singleton x :=
      AbstractApproximation.SparseIntervalData.sup_neighborhood_eq_point
        sparseIntervalData x
    change
      (((sSup (Set.range (selectedNeighborhood x)) : P) : Set X)) ⊆
        interior A
    rw [hSupEq, coe_singleton]
    exact Set.singleton_subset_iff.mpr hx
  obtain ⟨N, hNrange, hNsubset⟩ :=
    data.filtered_compactness hDirected isOpen_interior hSupSubset
  rcases hNrange with ⟨n, rfl⟩
  refine ⟨n, ?_⟩
  intro m hnm
  have hOrder :
      selectedNeighborhood x n ≤ selectedNeighborhood x m :=
    data.neighborhood_monotone x hnm
  exact
    ((le_def.mp hOrder).trans hNsubset).trans interior_subset

/-- Lemma `lem:Fm-cofinal`. -/
theorem Fm_cofinal
    (K : P) (G : FiniteFamily P) (hG : FiniteWayBelow G K) :
    ∃ n : ℕ, ∀ m ≥ n,
      AbramskyJung.Chapter2.upperClosure (Fm m K : Set P) ⊆
        AbramskyJung.Chapter2.upperClosure (G : Set P) := by
  classical
  have hGeometry := (finiteWayBelow_iff G K).1 hG
  by_cases hTop : K = ⊤
  · subst K
    refine ⟨0, ?_⟩
    intro m _hm C hC
    rcases G.nonempty with ⟨A, hAG⟩
    rcases hC with ⟨T, hTFm, hTleC⟩
    have hTtop : T = (⊤ : P) := by
      simpa [Fm] using hTFm
    subst T
    exact ⟨A, hAG, le_trans le_top hTleC⟩
  · by_cases hSingleton : ∃ x : X, K = singleton x
    · let x : X := hSingleton.choose
      have hKx : K = singleton x := hSingleton.choose_spec
      have hxK : x ∈ (K : Set X) := by
        rw [hKx, coe_singleton]
        simp
      have hxCover := hGeometry.2 hxK
      rw [Set.mem_iUnion] at hxCover
      rcases hxCover with ⟨A, hxCover⟩
      rw [Set.mem_iUnion] at hxCover
      rcases hxCover with ⟨hAG, hxInterior⟩
      obtain ⟨n, hn⟩ :=
        eventually_selectedNeighborhood_subset hxInterior
      refine ⟨n, ?_⟩
      intro m hnm C hC
      rcases hC with ⟨N, hNFm, hNleC⟩
      have hNx : N = selectedNeighborhood x m := by
        simpa [Fm, hTop, hSingleton, x] using hNFm
      subst N
      refine ⟨A, hAG, ?_⟩
      apply le_trans ?_ hNleC
      apply le_def.mpr
      exact hn m hnm
    · have hSkeleton :=
        skeleton_of_ne_top_of_not_singleton K hTop hSingleton
      rcases hGeometry.1 with ⟨A₀, hA₀G, hKsubsetA₀⟩
      have hLeftCover := hGeometry.2 (Skeleton.sInf_mem hSkeleton)
      rw [Set.mem_iUnion] at hLeftCover
      rcases hLeftCover with ⟨Aₗ, hLeftCover⟩
      rw [Set.mem_iUnion] at hLeftCover
      rcases hLeftCover with ⟨hAₗG, hLeftInterior⟩
      have hRightCover := hGeometry.2 (Skeleton.sSup_mem hSkeleton)
      rw [Set.mem_iUnion] at hRightCover
      rcases hRightCover with ⟨Aᵣ, hRightCover⟩
      rw [Set.mem_iUnion] at hRightCover
      rcases hRightCover with ⟨hAᵣG, hRightInterior⟩
      obtain ⟨nₗ, hnₗ⟩ :=
        eventually_selectedNeighborhood_subset hLeftInterior
      obtain ⟨nᵣ, hnᵣ⟩ :=
        eventually_selectedNeighborhood_subset hRightInterior
      refine ⟨max nₗ nᵣ, ?_⟩
      intro m hm C hC
      rcases hC with ⟨H, hHFm, hHleC⟩
      have hCases :
          H = K ∨
            H = selectedNeighborhood (sInf (K : Set X)) m ∨
            H = selectedNeighborhood (sSup (K : Set X)) m := by
        simpa [Fm, hTop, hSingleton] using hHFm
      rcases hCases with hHK | hHLeft | hHRight
      · subst H
        exact
          ⟨A₀, hA₀G,
            le_trans (le_def.mpr hKsubsetA₀) hHleC⟩
      · subst H
        refine ⟨Aₗ, hAₗG, le_trans ?_ hHleC⟩
        apply le_def.mpr
        exact hnₗ m ((Nat.le_max_left _ _).trans hm)
      · subst H
        refine ⟨Aᵣ, hAᵣG, le_trans ?_ hHleC⟩
        apply le_def.mpr
        exact hnᵣ m ((Nat.le_max_right _ _).trans hm)

/-- Lemma `lem:Fm-intersection`. -/
theorem iInter_upperClosure_Fm (K : P) :
    (⋂ m : ℕ,
        AbramskyJung.Chapter2.upperClosure (Fm m K : Set P)) =
      AbramskyJung.Chapter2.upperClosure ({K} : Set P) := by
  apply Set.Subset.antisymm
  · intro C hC
    have hCarrierSubset : (C : Set X) ⊆ (K : Set X) := by
      intro y hyC
      by_contra hyK
      obtain ⟨G, hG, hAvoid⟩ :=
        Quasicontinuity.exists_finiteWayBelow_avoiding K hyK
      obtain ⟨n, hn⟩ := Fm_cofinal K G hG
      have hCFm :
          C ∈ AbramskyJung.Chapter2.upperClosure (Fm n K : Set P) :=
        Set.mem_iInter.mp hC n
      have hCG :
          C ∈ AbramskyJung.Chapter2.upperClosure (G : Set P) :=
        hn n le_rfl hCFm
      rcases hCG with ⟨A, hAG, hAleC⟩
      exact hAvoid A hAG (hAleC hyC)
    exact ⟨K, by simp, hCarrierSubset⟩
  · intro C hC
    rcases hC with ⟨K', hK'mem, hK'leC⟩
    have hK'eq : K' = K := by simpa using hK'mem
    subst K'
    rw [Set.mem_iInter]
    intro m
    exact
      isUpperSet_upperClosure (Fm m K : Set P)
        (mem_upperClosure_of_finiteWayBelow (Fm_finiteWayBelow K m))
        hK'leC

end

end SourceFamilies
end UnitIntervalRetracts
