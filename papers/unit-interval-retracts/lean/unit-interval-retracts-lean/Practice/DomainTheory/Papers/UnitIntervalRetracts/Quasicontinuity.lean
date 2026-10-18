import Practice.DomainTheory.Papers.UnitIntervalRetracts.ConcreteApproximation

/-!
# Quasicontinuity of the sparse interval lattice

Filteredness is proved by pairwise sup-products of finite approximating
families.  The exact intersection is proved by constructing, for every point
outside the target carrier, a finite interior cover all of whose members avoid
that point.  This is equivalent to the cofinal `F_m` argument in the source and
avoids any hidden endpoint regularity assumption.
-/

set_option autoImplicit false
set_option linter.unnecessarySimpa false

namespace UnitIntervalRetracts
namespace Quasicontinuity

open Set Filter Topology
open AbramskyJung.Chapter2

noncomputable section

@[simp]
theorem coe_sup_eq_inter (A B : P) :
    ((A ⊔ B : P) : Set X) = (A : Set X) ∩ (B : Set X) := by
  rw [← sSup_pair, coe_sSup_eq_carrierIntersection]
  ext x
  simp [carrierIntersection]

/-- Pairwise sup-products of two finite families. -/
def supProduct (F G : FiniteFamily P) : FiniteFamily P :=
  ⟨Set.image2 (· ⊔ ·) (F : Set P) (G : Set P),
    F.finite.image2 (· ⊔ ·) G.finite,
    by
      rcases F.nonempty with ⟨A, hA⟩
      rcases G.nonempty with ⟨B, hB⟩
      exact ⟨A ⊔ B, A, hA, B, hB, rfl⟩⟩

@[simp]
theorem mem_supProduct_iff {F G : FiniteFamily P} {H : P} :
    H ∈ (supProduct F G : Set P) ↔
      ∃ A ∈ (F : Set P), ∃ B ∈ (G : Set P), A ⊔ B = H :=
  Iff.rfl

theorem upperClosure_supProduct_subset
    (F G : FiniteFamily P) :
    AbramskyJung.Chapter2.upperClosure (supProduct F G : Set P) ⊆
      AbramskyJung.Chapter2.upperClosure (F : Set P) ∩
        AbramskyJung.Chapter2.upperClosure (G : Set P) := by
  intro C hC
  rcases hC with ⟨H, hH, hHleC⟩
  rcases hH with ⟨A, hAF, B, hBG, rfl⟩
  constructor
  · exact ⟨A, hAF, le_trans le_sup_left hHleC⟩
  · exact ⟨B, hBG, le_trans le_sup_right hHleC⟩

theorem finiteWayBelow_supProduct
    {F G : FiniteFamily P} {K : P}
    (hF : FiniteWayBelow F K) (hG : FiniteWayBelow G K) :
    FiniteWayBelow (supProduct F G) K := by
  rw [finiteWayBelow_iff] at hF hG ⊢
  constructor
  · rcases hF.1 with ⟨A, hAF, hKA⟩
    rcases hG.1 with ⟨B, hBG, hKB⟩
    refine ⟨A ⊔ B, ?_, ?_⟩
    · exact ⟨A, hAF, B, hBG, rfl⟩
    · rw [coe_sup_eq_inter]
      exact fun x hx => ⟨hKA hx, hKB hx⟩
  · intro x hxK
    have hxF := hF.2 hxK
    have hxG := hG.2 hxK
    rw [Set.mem_iUnion] at hxF hxG
    rcases hxF with ⟨A, hxF⟩
    rcases hxG with ⟨B, hxG⟩
    rw [Set.mem_iUnion] at hxF hxG
    rcases hxF with ⟨hAF, hxA⟩
    rcases hxG with ⟨hBG, hxB⟩
    rw [Set.mem_iUnion]
    refine ⟨A ⊔ B, ?_⟩
    rw [Set.mem_iUnion]
    refine ⟨⟨A, hAF, B, hBG, rfl⟩, ?_⟩
    rw [coe_sup_eq_inter, interior_inter]
    exact ⟨hxA, hxB⟩

theorem bottomFamily_finiteWayBelow (K : P) :
    FiniteWayBelow
      (AbstractApproximation.singletonFiniteFamily (⊥ : P)) K := by
  rw [finiteWayBelow_iff]
  constructor
  · refine ⟨⊥, by simp, ?_⟩
    simp [coe_bot]
  · simp [coe_bot]

/-- For every point outside `K`, a finite approximating family can be selected
whose every carrier avoids that point. -/
theorem exists_finiteWayBelow_avoiding
    (K : P) {y : X} (hyK : y ∉ (K : Set X)) :
    ∃ F : FiniteFamily P,
      FiniteWayBelow F K ∧
      ∀ A ∈ (F : Set P), y ∉ (A : Set X) := by
  classical
  let away : Set X := ({y} : Set X)ᶜ
  have hAwayOpen : IsOpen away := isClosed_singleton.isOpen_compl
  let indexType := {x : X // x ∈ (K : Set X)}
  have hIndexAway (z : indexType) : z.1 ∈ away := by
    intro hzy
    have hEq : z.1 = y := by
      simpa using hzy
    exact hyK (hEq ▸ z.2)
  let witness (z : indexType) :=
    exists_skeleton_closed_neighborhood hAwayOpen (hIndexAway z)
  let neighborSet (z : indexType) : Set X :=
    Classical.choose (witness z)
  have hNeighborSet (z : indexType) :
      neighborSet z ∈ Skeleton ∧
        z.1 ∈ interior (neighborSet z) ∧
        neighborSet z ⊆ away :=
    Classical.choose_spec (witness z)
  let neighbor (z : indexType) : P :=
    ofSkeleton (hNeighborSet z).1
  have hNeighborCoe (z : indexType) :
      (neighbor z : Set X) = neighborSet z :=
    rfl
  have hCenterInterior (z : indexType) :
      z.1 ∈ interior (neighbor z : Set X) := by
    rw [hNeighborCoe]
    exact (hNeighborSet z).2.1
  have hNeighborAvoids (z : indexType) :
      y ∉ (neighbor z : Set X) := by
    intro hy
    have hyAway : y ∈ away := by
      apply (hNeighborSet z).2.2
      simpa only [hNeighborCoe] using hy
    exact hyAway (by simp)
  obtain ⟨t, hCover⟩ :=
    (isCompact_carrier K).elim_finite_subcover
      (fun z : indexType => interior (neighbor z : Set X))
      (fun _z => isOpen_interior)
      (by
        intro x hxK
        rw [Set.mem_iUnion]
        exact ⟨⟨x, hxK⟩, hCenterInterior ⟨x, hxK⟩⟩)
  let familySet : Set P :=
    {K} ∪ neighbor '' (t : Set indexType)
  have hFamilyFinite : familySet.Finite := by
    apply Set.Finite.union (Set.finite_singleton K)
    exact t.finite_toSet.image neighbor
  have hFamilyNonempty : familySet.Nonempty :=
    ⟨K, Set.mem_union_left _ (Set.mem_singleton K)⟩
  let F : FiniteFamily P :=
    ⟨familySet, hFamilyFinite, hFamilyNonempty⟩
  refine ⟨F, ?_, ?_⟩
  · apply (finiteWayBelow_iff F K).2
    constructor
    · exact
        ⟨K, Set.mem_union_left _ (Set.mem_singleton K),
          Set.Subset.rfl⟩
    · intro x hxK
      have hxCover := hCover hxK
      rw [Set.mem_iUnion] at hxCover
      rcases hxCover with ⟨z, hxCover⟩
      rw [Set.mem_iUnion] at hxCover
      rcases hxCover with ⟨hzt, hxInterior⟩
      rw [Set.mem_iUnion]
      refine ⟨neighbor z, ?_⟩
      rw [Set.mem_iUnion]
      refine ⟨Set.mem_union_right _ ⟨z, hzt, rfl⟩, hxInterior⟩
  · intro A hAF
    change A ∈ familySet at hAF
    rcases hAF with hAK | hAneighbor
    · have hAKeq : A = K := by simpa using hAK
      simpa [hAKeq] using hyK
    · rcases hAneighbor with ⟨z, _hzt, rfl⟩
      exact hNeighborAvoids z

def quasiUpperFamily (K : P) : Set (Set P) :=
  {U | ∃ F : FiniteFamily P, FiniteWayBelow F K ∧
    U = AbramskyJung.Chapter2.upperClosure (F : Set P)}

theorem quasiUpperFamily_filtered (K : P) :
    FilteredUnderInclusion (quasiUpperFamily K) := by
  constructor
  · let F := AbstractApproximation.singletonFiniteFamily (⊥ : P)
    refine
      ⟨AbramskyJung.Chapter2.upperClosure (F : Set P),
        F, bottomFamily_finiteWayBelow K, rfl⟩
  · intro U V hU hV
    rcases hU with ⟨F, hF, rfl⟩
    rcases hV with ⟨G, hG, rfl⟩
    let H := supProduct F G
    refine
      ⟨AbramskyJung.Chapter2.upperClosure (H : Set P),
        ⟨H, finiteWayBelow_supProduct hF hG, rfl⟩, ?_⟩
    exact upperClosure_supProduct_subset F G

theorem sInter_quasiUpperFamily (K : P) :
    ⋂₀ (quasiUpperFamily K) =
      AbramskyJung.Chapter2.upperClosure ({K} : Set P) := by
  apply Set.Subset.antisymm
  · intro C hC
    have hCarrierSubset : (C : Set X) ⊆ (K : Set X) := by
      intro y hyC
      by_contra hyK
      obtain ⟨F, hF, hAvoid⟩ :=
        exists_finiteWayBelow_avoiding K hyK
      have hUpperMem :
          AbramskyJung.Chapter2.upperClosure (F : Set P) ∈
            quasiUpperFamily K :=
        ⟨F, hF, rfl⟩
      have hCUpper :
          C ∈ AbramskyJung.Chapter2.upperClosure (F : Set P) :=
        hC _ hUpperMem
      rcases hCUpper with ⟨A, hAF, hAleC⟩
      exact hAvoid A hAF (hAleC hyC)
    exact ⟨K, by simp, hCarrierSubset⟩
  · intro C hC
    rcases hC with ⟨K', hK'singleton, hK'leC⟩
    have hK'eq : K' = K := by
      simpa using hK'singleton
    subst K'
    intro U hU
    rcases hU with ⟨F, hF, rfl⟩
    exact
      isUpperSet_upperClosure (F : Set P)
        (mem_upperClosure_of_finiteWayBelow hF) hK'leC

/-- The sparse interval complete lattice is quasicontinuous. -/
theorem isQuasicontinuous_P : IsQuasicontinuous P := by
  intro K
  change
    FilteredUnderInclusion (quasiUpperFamily K) ∧
      ⋂₀ (quasiUpperFamily K) =
        AbramskyJung.Chapter2.upperClosure ({K} : Set P)
  exact ⟨quasiUpperFamily_filtered K, sInter_quasiUpperFamily K⟩

end

end Quasicontinuity

/-- Theorem `thm:quasicontinuous`. -/
theorem isQuasicontinuous_P : IsQuasicontinuous P :=
  Quasicontinuity.isQuasicontinuous_P

end UnitIntervalRetracts
