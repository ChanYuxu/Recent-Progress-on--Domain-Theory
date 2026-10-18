import Practice.DomainTheory.Papers.UnitIntervalRetracts.ConcreteApproximation
import Mathlib.Analysis.Real.Cardinality

/-!
# Failure of quasialgebraicity, countable chains, and the interval quotient

This file formalizes `lem:eta-continuous`, `lem:finite-open-trace`,
`prop:not-quasialgebraic`, `prop:chains-countable`, `prop:surjection`, and the
two negative consequences in the main theorem.
-/

set_option autoImplicit false
set_option linter.unnecessarySimpa false

namespace UnitIntervalRetracts

open Set Filter Topology
open AbramskyJung.Chapter2

noncomputable section

/-- The singleton-layer map has open inverse images of all project-local
Scott-open subsets.  This is the unbundled form of `lem:eta-continuous`,
matching the project's unbundled Scott topology. -/
theorem isOpen_singleton_preimage_scottOpen
    {W : Set P} (hW : ScottOpen W) :
    IsOpen (singleton ⁻¹' W) := by
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  let D : Set P := Set.range (selectedNeighborhood x)
  have hDdir : DirectedSet D := by
    exact
      AbstractApproximation.SparseIntervalData.neighborhood_directed
        sparseIntervalData x
  have hDsup : IsSup D (singleton x) := by
    have hs := sparseIntervalData.sup_isSup D
    have heq :
        sparseIntervalData.sup D = singleton x :=
      AbstractApproximation.SparseIntervalData.sup_neighborhood_eq_point
        sparseIntervalData x
    simpa [heq] using hs
  have hhit : ∃ N ∈ D, N ∈ W := by
    by_contra hnone
    have hDcompl : D ⊆ Wᶜ := by
      intro N hND hNW
      exact hnone ⟨N, hND, hNW⟩
    exact (hW.2 hDdir hDcompl hDsup) hx
  rcases hhit with ⟨N, ⟨n, rfl⟩, hNW⟩
  refine
    ⟨interior (selectedNeighborhood x n : Set X), ?_, isOpen_interior,
      point_mem_interior_selectedNeighborhood x n⟩
  intro y hy
  apply scottOpen_upper hW hNW
  change ({y} : Set X) ⊆ (selectedNeighborhood x n : Set X)
  simpa using interior_subset hy

/-- Equation `eq:singleton-trace`. -/
theorem singleton_preimage_upperClosure
    (F : FiniteFamily P) :
    singleton ⁻¹'
        AbramskyJung.Chapter2.upperClosure (F : Set P) =
      ⋃ A ∈ (F : Set P), (A : Set X) := by
  ext x
  constructor
  · rintro ⟨A, hAF, hAle⟩
    rw [Set.mem_iUnion]
    refine ⟨A, ?_⟩
    rw [Set.mem_iUnion]
    refine ⟨hAF, ?_⟩
    exact hAle (by simp)
  · intro hx
    rw [Set.mem_iUnion] at hx
    rcases hx with ⟨A, hx⟩
    rw [Set.mem_iUnion] at hx
    rcases hx with ⟨hAF, hxA⟩
    exact ⟨A, hAF, by
      change ({x} : Set X) ⊆ (A : Set X)
      simpa using hxA⟩

/-- Lemma `lem:finite-open-trace`. -/
theorem finiteOpenTrace_isClopen
    (F : FiniteFamily P)
    (hF : FamilyWayBelow (F : Set P) (F : Set P)) :
    IsClopen
      (singleton ⁻¹'
        AbramskyJung.Chapter2.upperClosure (F : Set P)) := by
  constructor
  · rw [singleton_preimage_upperClosure F]
    exact F.finite.isClosed_biUnion (fun A _hA => isClosed_carrier A)
  · exact
      isOpen_singleton_preimage_scottOpen
        (familyWayBelow_self_scottOpen hF)

theorem singleton_mem_all_finiteOpen_neighborhoods
    (F : FiniteFamily P)
    (hFself : FamilyWayBelow (F : Set P) (F : Set P))
    {x y : X}
    (hx : singleton x ∈
      AbramskyJung.Chapter2.upperClosure (F : Set P)) :
    singleton y ∈
      AbramskyJung.Chapter2.upperClosure (F : Set P) := by
  have hclopen := finiteOpenTrace_isClopen F hFself
  have hnonempty :
      (singleton ⁻¹'
        AbramskyJung.Chapter2.upperClosure (F : Set P)).Nonempty :=
    ⟨x, hx⟩
  have huniv :
      singleton ⁻¹'
          AbramskyJung.Chapter2.upperClosure (F : Set P) =
        Set.univ :=
    hclopen.eq_univ hnonempty
  have hy : y ∈
      singleton ⁻¹'
        AbramskyJung.Chapter2.upperClosure (F : Set P) := by
    rw [huniv]
    simp
  exact hy

/-- Proposition `prop:not-quasialgebraic`. -/
theorem not_isQuasialgebraic_P :
    ¬ IsQuasialgebraic P := by
  intro hqa
  let x : X := ⟨0, by norm_num⟩
  let y : X := ⟨1, by norm_num⟩
  let neighborhoods : Set (Set P) :=
    {U | ∃ F : FiniteFamily P,
      singleton x ∈
        AbramskyJung.Chapter2.upperClosure (F : Set P) ∧
      FamilyWayBelow (F : Set P) (F : Set P) ∧
      U = AbramskyJung.Chapter2.upperClosure (F : Set P)}
  have hqaX :
      FilteredUnderInclusion neighborhoods ∧
        ⋂₀ neighborhoods =
          AbramskyJung.Chapter2.upperClosure ({singleton x} : Set P) := by
    simpa only [IsQuasialgebraic, neighborhoods] using hqa (singleton x)
  have hyInter : singleton y ∈ ⋂₀ neighborhoods := by
    intro U hU
    rcases hU with ⟨F, hxF, hFself, rfl⟩
    exact singleton_mem_all_finiteOpen_neighborhoods F hFself hxF
  rw [hqaX.2] at hyInter
  rcases hyInter with ⟨A, hAsingleton, hAle⟩
  have hAeq : A = singleton x := by
    simpa using hAsingleton
  subst A
  have hyx : y = x := by
    have hy_mem : y ∈ ({x} : Set X) := by
      exact
        (show ({y} : Set X) ⊆ ({x} : Set X) from hAle) (by simp)
    simpa using hy_mem
  norm_num [x, y] at hyx

/-- Proposition `prop:chains-countable`. -/
theorem chain_countable
    {C : Set P} (hC : IsChainSet C) :
    C.Countable := by
  let skeletonLayer : Set P :=
    {A | (A : Set X) ∈ Skeleton}
  let singletonLayerInChain : Set P :=
    {A | A ∈ C ∧ ∃ x : X, A = singleton x}
  have hSkeleton : skeletonLayer.Countable := by
    simpa only [skeletonLayer, Set.preimage_setOf_eq] using
      skeleton_countable.preimage (SetLike.coe_injective :
        Function.Injective (fun A : P => (A : Set X)))
  have hSingletonSubsingleton :
      singletonLayerInChain.Subsingleton := by
    intro A hA B hB
    rcases hA with ⟨hAC, x, rfl⟩
    rcases hB with ⟨hBC, y, rfl⟩
    rcases hC.2 hAC hBC with hxy | hyx
    · have hy_mem : y ∈ ({x} : Set X) := by
        exact
          (show ({y} : Set X) ⊆ ({x} : Set X) from hxy) (by simp)
      have hyx : y = x := by simpa using hy_mem
      subst y
      rfl
    · have hx_mem : x ∈ ({y} : Set X) := by
        exact
          (show ({x} : Set X) ⊆ ({y} : Set X) from hyx) (by simp)
      have hxy : x = y := by simpa using hx_mem
      subst y
      rfl
  have hSingleton : singletonLayerInChain.Countable :=
    hSingletonSubsingleton.countable
  have hcover :
      C ⊆ skeletonLayer ∪ singletonLayerInChain ∪ ({empty} : Set P) := by
    intro A hAC
    rcases A.isSparse with hSkeletonA | hPointA | hEmptyA
    · exact Or.inl (Or.inl hSkeletonA)
    · rcases hPointA with ⟨x, hx⟩
      have hAeq : A = singleton x := by
        apply SetLike.coe_injective
        simpa using hx
      exact Or.inl (Or.inr ⟨hAC, x, hAeq⟩)
    · have hAeq : A = empty := by
        apply SetLike.coe_injective
        simpa using hEmptyA
      exact Or.inr (by simpa [hAeq])
  exact
    (hSkeleton.union hSingleton |>.union (Set.countable_singleton empty)).mono
      hcover

theorem carrier_nonempty_of_ne_top
    (A : P) (hA : A ≠ (⊤ : P)) :
    (A : Set X).Nonempty := by
  by_contra hne
  have hempty : (A : Set X) = ∅ :=
    Set.not_nonempty_iff_eq_empty.mp hne
  apply hA
  apply SetLike.coe_injective
  simpa only [coe_top] using hempty

theorem carrier_sInf_isLeast
    (A : P) (hA : A ≠ (⊤ : P)) :
    _root_.IsLeast (A : Set X) (sInf (A : Set X)) :=
  (isCompact_carrier A).isLeast_sInf
    (carrier_nonempty_of_ne_top A hA)

/-- Equation `eq:q-definition`. -/
noncomputable def endpointMap (A : P) : X := by
  classical
  exact if A = (⊤ : P) then ⊤ else sInf (A : Set X)

@[simp] theorem endpointMap_top :
    endpointMap (⊤ : P) = (⊤ : X) := by
  simp [endpointMap]

@[simp] theorem endpointMap_of_ne_top
    (A : P) (hA : A ≠ (⊤ : P)) :
    endpointMap A = sInf (A : Set X) := by
  simp [endpointMap, hA]

theorem singleton_ne_top (x : X) :
    singleton x ≠ (⊤ : P) := by
  intro h
  have hsets :
      ({x} : Set X) = ∅ := by
    simpa using congrArg (fun A : P => (A : Set X)) h
  exact Set.singleton_ne_empty x hsets

@[simp] theorem endpointMap_singleton (x : X) :
    endpointMap (singleton x) = x := by
  simp [endpointMap, singleton_ne_top]

theorem endpointMap_surjective :
    Function.Surjective endpointMap := by
  intro x
  exact ⟨singleton x, endpointMap_singleton x⟩

theorem endpointMap_monotone :
    Monotone endpointMap := by
  intro A B hAB
  by_cases hB : B = (⊤ : P)
  · subst B
    rw [endpointMap_top]
    exact le_top
  · have hA : A ≠ (⊤ : P) := by
      intro hAtop
      subst A
      exact hB (top_unique hAB)
    have hminA :=
      carrier_sInf_isLeast A hA
    have hminB :=
      carrier_sInf_isLeast B hB
    rw [endpointMap_of_ne_top A hA, endpointMap_of_ne_top B hB]
    exact hminA.2 (hAB hminB.1)

theorem eq_sSup_of_isSup
    {D : Set P} {S : P} (hS : IsSup D S) :
    S = sSup D := by
  apply le_antisymm
  · exact hS.2 _ (fun A hAD => le_sSup hAD)
  · exact sSup_le hS.1

/-- Proposition `prop:surjection`: the endpoint map preserves directed
suprema. -/
theorem endpointMap_scottContinuous :
    AbramskyJung.Chapter2.ScottContinuous endpointMap := by
  constructor
  · exact endpointMap_monotone
  · intro D S hD hS
    have hSeq : S = sSup D :=
      eq_sSup_of_isSup hS
    by_cases hStop : S = (⊤ : P)
    · have hsSupTop : sSup D = (⊤ : P) :=
        hSeq.symm.trans hStop
      have htopD : (⊤ : P) ∈ D := by
        exact top_mem_of_directed_sSup_eq_top hD hsSupTop
      rw [hStop]
      constructor
      · rintro _ ⟨A, _hAD, rfl⟩
        simpa only [endpointMap_top] using
          (show endpointMap A ≤ (⊤ : X) from le_top)
      · intro u hu
        exact hu ⟨(⊤ : P), htopD, rfl⟩
    · have hminS :=
        carrier_sInf_isLeast S hStop
      constructor
      · rintro _ ⟨A, hAD, rfl⟩
        exact endpointMap_monotone (hS.1 hAD)
      · intro u hu
        by_contra hnot
        have huq : u < endpointMap S :=
          lt_of_not_ge hnot
        rcases exists_between huq with ⟨c, huc, hcq⟩
        let O : Set X := Set.Ioi c
        have hSsub : (S : Set X) ⊆ O := by
          intro z hz
          have hqz : endpointMap S ≤ z := by
            rw [endpointMap_of_ne_top S hStop]
            exact hminS.2 hz
          exact lt_of_lt_of_le hcq hqz
        have hcarrier :
            carrierIntersection D = (S : Set X) := by
          rw [← coe_sSup_eq_carrierIntersection D, ← hSeq]
        have hCarrierSub : carrierIntersection D ⊆ O := by
          rw [hcarrier]
          exact hSsub
        rcases filteredCompactness hD isOpen_Ioi hCarrierSub with
          ⟨A, hAD, hAO⟩
        have hAne : A ≠ (⊤ : P) := by
          intro hAtop
          subst A
          exact hStop (top_unique (hS.1 hAD))
        have hqA_mem : endpointMap A ∈ (A : Set X) := by
          rw [endpointMap_of_ne_top A hAne]
          exact (carrier_sInf_isLeast A hAne).1
        have hcqA : c < endpointMap A :=
          hAO hqA_mem
        have hqAu : endpointMap A ≤ u :=
          hu ⟨A, hAD, rfl⟩
        exact (lt_asymm hcqA (lt_of_le_of_lt hqAu huc)).elim

/-- Paper notation for the explicit quotient map. -/
abbrev q : P → X :=
  endpointMap

theorem q_scottContinuous_surjective :
    AbramskyJung.Chapter2.ScottContinuous q ∧
      Function.Surjective q :=
  ⟨endpointMap_scottContinuous, endpointMap_surjective⟩

theorem no_monotone_injective_X_to_P :
    ¬ ∃ s : X → P, Monotone s ∧ Function.Injective s := by
  rintro ⟨s, hsmono, hsinj⟩
  have hRangeChain : IsChainSet (Set.range s) := by
    constructor
    · exact Set.range_nonempty s
    · rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
      rcases le_total x y with hxy | hyx
      · exact Or.inl (hsmono hxy)
      · exact Or.inr (hsmono hyx)
  have hRangeCountable : (Set.range s).Countable :=
    chain_countable hRangeChain
  let rangeEmbedding : X ↪ Set.range s :=
    ⟨fun x => ⟨s x, Set.mem_range_self x⟩, by
      intro x y hxy
      exact hsinj (Subtype.ext_iff.mp hxy)⟩
  letI : Countable (Set.range s) :=
    hRangeCountable.to_subtype
  letI : Countable X :=
    rangeEmbedding.injective.countable
  have hIccCountable :
      (Set.Icc (0 : ℝ) 1).Countable :=
    Set.countable_coe_iff.mp (inferInstance : Countable X)
  have hbad : (1 : ℝ) ≤ 0 :=
    Cardinal.Real.Icc_countable_iff.mp hIccCountable
  norm_num at hbad

theorem no_orderEmbedding_X_to_P :
    ¬ Nonempty (X ↪o P) := by
  rintro ⟨s⟩
  exact no_monotone_injective_X_to_P
    ⟨s, s.monotone, s.injective⟩

theorem no_scottContinuous_retract_X_of_P :
    ¬ ∃ (r : P → X) (s : X → P),
        AbramskyJung.Chapter2.ScottContinuous r ∧
        AbramskyJung.Chapter2.ScottContinuous s ∧
        Function.LeftInverse r s := by
  rintro ⟨r, s, _hr, hs, hrs⟩
  exact no_monotone_injective_X_to_P
    ⟨s, hs.1, hrs.injective⟩

end

end UnitIntervalRetracts
