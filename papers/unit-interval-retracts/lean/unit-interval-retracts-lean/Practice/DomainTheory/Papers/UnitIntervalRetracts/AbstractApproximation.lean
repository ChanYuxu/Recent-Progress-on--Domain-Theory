import Practice.DomainTheory.Papers.UnitIntervalRetracts.Basic
import Mathlib.Topology.Basic

/-!
# Abstract finite approximation for the sparse interval lattice

This module isolates the order/topology argument behind
`thm:finite-way-below`.  Its hypotheses are exactly the geometric results
proved by the concrete sparse-interval construction; the characterization
itself is proved here and is not postulated.
-/

set_option autoImplicit false
set_option linter.unnecessarySimpa false

universe u v

namespace UnitIntervalRetracts
namespace AbstractApproximation

open Set
open AbramskyJung.Chapter2

/-- The singleton member of the source-facing `FiniteFamily` type. -/
def singletonFiniteFamily {P : Type v} (A : P) : FiniteFamily P :=
  ⟨({A} : Set P), Set.finite_singleton A, Set.singleton_nonempty A⟩

@[simp]
theorem coe_singletonFiniteFamily {P : Type v} (A : P) :
    ((singletonFiniteFamily A : FiniteFamily P) : Set P) = {A} :=
  rfl

/-- The concrete obligations supplied by the sparse interval construction. -/
structure SparseIntervalData
    (X : Type u) (P : Type v)
    [TopologicalSpace X] [PartialOrder P] [OrderTop P] where
  realized : P → Set X
  le_iff_realized_reverse_subset :
    ∀ A B : P, A ≤ B ↔ realized B ⊆ realized A
  realized_top : realized ⊤ = ∅
  sup : Set P → P
  sup_isSup : ∀ family : Set P, IsSup family (sup family)
  realized_sup :
    ∀ family : Set P,
      realized (sup family) = ⋂₀ (realized '' family)
  point : X → P
  realized_point : ∀ x : X, realized (point x) = {x}
  neighborhood : X → Nat → P
  point_mem_interior :
    ∀ (x : X) (n : Nat), x ∈ interior (realized (neighborhood x n))
  neighborhood_step :
    ∀ (x : X) (n : Nat),
      realized (neighborhood x (n + 1)) ⊆
        interior (realized (neighborhood x n))
  neighborhood_intersection :
    ∀ x : X,
      ⋂₀ (realized '' Set.range (neighborhood x)) = {x}
  filtered_compactness :
    ∀ {family : Set P} {O : Set X},
      DirectedSet family →
      IsOpen O →
      realized (sup family) ⊆ O →
      ∃ A ∈ family, realized A ⊆ O
  finite_of_nonsingleton_directed_sup :
    ∀ {family : Set P},
      DirectedSet family →
      (realized (sup family)).Nonempty →
      (∀ x : X, realized (sup family) ≠ {x}) →
      family.Finite

namespace SparseIntervalData

variable
    {X : Type u} {P : Type v}
    [TopologicalSpace X] [PartialOrder P] [OrderTop P]
    (data : SparseIntervalData X P)

theorem realized_injective : Function.Injective data.realized := by
  intro A B hAB
  apply le_antisymm
  · apply (data.le_iff_realized_reverse_subset A B).2
    simpa [hAB]
  · apply (data.le_iff_realized_reverse_subset B A).2
    simpa [hAB]

theorem neighborhood_le_succ (x : X) (n : Nat) :
    data.neighborhood x n ≤ data.neighborhood x (n + 1) := by
  apply (data.le_iff_realized_reverse_subset _ _).2
  exact (data.neighborhood_step x n).trans interior_subset

theorem neighborhood_monotone (x : X) :
    Monotone (data.neighborhood x) :=
  monotone_nat_of_le_succ (data.neighborhood_le_succ x)

theorem neighborhood_directed (x : X) :
    DirectedSet (Set.range (data.neighborhood x)) := by
  constructor
  · exact ⟨data.neighborhood x 0, ⟨0, rfl⟩⟩
  · intro A hA B hB
    rcases hA with ⟨m, rfl⟩
    rcases hB with ⟨n, rfl⟩
    refine
      ⟨data.neighborhood x (max m n), ⟨max m n, rfl⟩,
        data.neighborhood_monotone x (Nat.le_max_left m n),
        data.neighborhood_monotone x (Nat.le_max_right m n)⟩

theorem sup_neighborhood_eq_point (x : X) :
    data.sup (Set.range (data.neighborhood x)) = data.point x := by
  apply data.realized_injective
  rw [data.realized_sup, data.neighborhood_intersection, data.realized_point]

/-- The source corollary `cor:top-in-directed-family`, derived here from
filtered compactness. -/
theorem top_mem_of_directed_sup_realized_empty
    {family : Set P}
    (hDirected : DirectedSet family)
    (hEmpty : data.realized (data.sup family) = ∅) :
    (⊤ : P) ∈ family := by
  obtain ⟨A, hAfamily, hAempty⟩ :=
    data.filtered_compactness hDirected isOpen_empty (by simpa [hEmpty])
  have hRealizedA : data.realized A = ∅ :=
    Set.Subset.antisymm hAempty (Set.empty_subset _)
  have hATop : A = (⊤ : P) := by
    apply data.realized_injective
    exact hRealizedA.trans data.realized_top.symm
  simpa [hATop] using hAfamily

/-- The exact finite-family way-below formula in
`thm:finite-way-below`. -/
theorem finiteWayBelow_iff
    (approximants : FiniteFamily P) (K : P) :
    FiniteWayBelow approximants K ↔
      (∃ A ∈ (approximants : Set P),
        data.realized K ⊆ data.realized A) ∧
      data.realized K ⊆
        ⋃ A ∈ (approximants : Set P), interior (data.realized A) := by
  constructor
  · intro hWayBelow
    constructor
    · obtain ⟨C, hCsingleton, hCupper⟩ :=
        hWayBelow (directed_singleton K) (isSup_singleton K)
          (AbramskyJung.Chapter2.subset_upperClosure
            ({K} : Set P) (by simp))
      have hCK : C = K := by
        simpa using hCsingleton
      rcases hCupper with ⟨A, hAfamily, hAleC⟩
      subst C
      exact
        ⟨A, hAfamily,
          (data.le_iff_realized_reverse_subset A K).1 hAleC⟩
    · intro x hxK
      let neighborhoodRange : Set P := Set.range (data.neighborhood x)
      have hNeighborhoodDirected :
          DirectedSet neighborhoodRange :=
        data.neighborhood_directed x
      have hNeighborhoodSup :
          data.sup neighborhoodRange = data.point x :=
        data.sup_neighborhood_eq_point x
      have hPointIsSup :
          IsSup neighborhoodRange (data.point x) := by
        rw [← hNeighborhoodSup]
        exact data.sup_isSup neighborhoodRange
      have hPointInUpper :
          data.point x ∈
            AbramskyJung.Chapter2.upperClosure ({K} : Set P) := by
        refine ⟨K, by simp, ?_⟩
        apply (data.le_iff_realized_reverse_subset K (data.point x)).2
        rw [data.realized_point]
        exact Set.singleton_subset_iff.mpr hxK
      obtain ⟨N, hNrange, hNupper⟩ :=
        hWayBelow hNeighborhoodDirected hPointIsSup hPointInUpper
      rcases hNrange with ⟨n, rfl⟩
      rcases hNupper with ⟨A, hAfamily, hAleN⟩
      rw [Set.mem_iUnion]
      refine ⟨A, ?_⟩
      rw [Set.mem_iUnion]
      refine ⟨hAfamily, ?_⟩
      exact
        interior_mono
          ((data.le_iff_realized_reverse_subset A
            (data.neighborhood x n)).1 hAleN)
          (data.point_mem_interior x n)
  · rintro ⟨hContains, hInteriorCover⟩
    intro family s hDirected hIsSup hSInUpper
    have hsEq : s = data.sup family :=
      IsSup.unique hIsSup (data.sup_isSup family)
    subst s
    rcases hSInUpper with ⟨K', hK'singleton, hK'leSup⟩
    have hK'eq : K' = K := by
      simpa using hK'singleton
    subst K'
    have hSupSubsetK :
        data.realized (data.sup family) ⊆ data.realized K :=
      (data.le_iff_realized_reverse_subset K (data.sup family)).1 hK'leSup
    by_cases hEmpty : data.realized (data.sup family) = ∅
    · refine
        ⟨⊤, data.top_mem_of_directed_sup_realized_empty hDirected hEmpty, ?_⟩
      rcases approximants.nonempty with ⟨A, hAfamily⟩
      exact ⟨A, hAfamily, le_top⟩
    · by_cases hSingleton :
        ∃ x : X, data.realized (data.sup family) = {x}
      · rcases hSingleton with ⟨x, hSupPoint⟩
        have hxSup : x ∈ data.realized (data.sup family) := by
          rw [hSupPoint]
          simp
        have hxK : x ∈ data.realized K := hSupSubsetK hxSup
        have hxCover := hInteriorCover hxK
        rw [Set.mem_iUnion] at hxCover
        rcases hxCover with ⟨A, hxCover⟩
        rw [Set.mem_iUnion] at hxCover
        rcases hxCover with ⟨hAfamily, hxInterior⟩
        obtain ⟨C, hCfamily, hCsub⟩ :=
          data.filtered_compactness hDirected isOpen_interior (by
            intro y hy
            have hyx : y = x := by
              rw [hSupPoint] at hy
              simpa using hy
            simpa [hyx] using hxInterior)
        refine ⟨C, hCfamily, A, hAfamily, ?_⟩
        apply (data.le_iff_realized_reverse_subset A C).2
        exact hCsub.trans interior_subset
      · have hSupNonempty :
            (data.realized (data.sup family)).Nonempty :=
          Set.nonempty_iff_ne_empty.mpr hEmpty
        have hNotSingleton :
            ∀ x : X, data.realized (data.sup family) ≠ {x} := by
          intro x hx
          exact hSingleton ⟨x, hx⟩
        have hFamilyFinite : family.Finite :=
          data.finite_of_nonsingleton_directed_sup
            hDirected hSupNonempty hNotSingleton
        obtain ⟨C, hCfamily, hCSup⟩ :=
          DirectedSet.exists_isSup_of_finite hDirected hFamilyFinite
        have hCeq : C = data.sup family :=
          IsSup.unique hCSup (data.sup_isSup family)
        rcases hContains with ⟨A, hAfamily, hKsubA⟩
        refine ⟨C, hCfamily, A, hAfamily, ?_⟩
        apply (data.le_iff_realized_reverse_subset A C).2
        rw [hCeq]
        exact hSupSubsetK.trans hKsubA

theorem finiteWayBelow_iff_of_ne_top
    (approximants : FiniteFamily P) {K : P} (_hK : K ≠ ⊤) :
    FiniteWayBelow approximants K ↔
      (∃ A ∈ (approximants : Set P),
        data.realized K ⊆ data.realized A) ∧
      data.realized K ⊆
        ⋃ A ∈ (approximants : Set P), interior (data.realized A) :=
  data.finiteWayBelow_iff approximants K

theorem finiteWayBelow_top
    (data : SparseIntervalData X P) (approximants : FiniteFamily P) :
    FiniteWayBelow approximants (⊤ : P) := by
  apply (finiteWayBelow_iff data approximants (⊤ : P)).2
  constructor
  · rcases approximants.nonempty with ⟨A, hAfamily⟩
    exact ⟨A, hAfamily, by simp [data.realized_top]⟩
  · simp [data.realized_top]

omit [OrderTop P] in
/-- Family way-below on singleton families is ordinary way-below. -/
theorem familyWayBelow_singletons_iff_wayBelow (A K : P) :
    FamilyWayBelow ({A} : Set P) ({K} : Set P) ↔ A ≪ K := by
  constructor
  · intro hFamily D s hDirected hIsSup hKle
    rcases hFamily hDirected hIsSup
        ⟨K, by simp, hKle⟩ with
      ⟨d, hdD, d', hd'singleton, hd'leD⟩
    have hd'A : d' = A := by
      simpa using hd'singleton
    subst d'
    exact ⟨d, hdD, hd'leD⟩
  · intro hWayBelow D s hDirected hIsSup hSupper
    rcases hSupper with ⟨K', hK'singleton, hK'leS⟩
    have hK'eq : K' = K := by
      simpa using hK'singleton
    subst K'
    rcases hWayBelow hDirected hIsSup hK'leS with ⟨d, hdD, hAleD⟩
    exact ⟨d, hdD, A, by simp, hAleD⟩

/-- Corollary `cor:one-point-way-below`. -/
theorem wayBelow_iff_interior
    (A : P) {K : P} (hK : K ≠ ⊤) :
    A ≪ K ↔ data.realized K ⊆ interior (data.realized A) := by
  have hFinite :
      FiniteWayBelow (singletonFiniteFamily A) K ↔
        data.realized K ⊆ interior (data.realized A) := by
    rw [data.finiteWayBelow_iff_of_ne_top _ hK]
    constructor
    · rintro ⟨_, hCover⟩
      simpa using hCover
    · intro hInterior
      constructor
      · exact
          ⟨A, by simp,
            hInterior.trans interior_subset⟩
      · simpa using hInterior
  have hFamily :
      FamilyWayBelow ({A} : Set P) ({K} : Set P) ↔
        data.realized K ⊆ interior (data.realized A) := by
    simpa [FiniteWayBelow] using hFinite
  rw [familyWayBelow_singletons_iff_wayBelow] at hFamily
  exact hFamily

end SparseIntervalData

end AbstractApproximation
end UnitIntervalRetracts
