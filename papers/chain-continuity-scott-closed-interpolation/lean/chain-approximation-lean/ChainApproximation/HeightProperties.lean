import ChainApproximation.HeightTwo
import ChainApproximation.LowerSetBasis

/-! # Structural properties and relation comparisons on the counterexample -/

set_option autoImplicit false

namespace ChainApproximation
namespace HeightTwo

open Set

theorem le_b_eq {q : HeightTwo} {n : ℕ} (h : q ≤ b n) : q = b n := by
  cases q with
  | b m => exact congrArg b h
  | c m => exact False.elim h

theorem directed_has_greatest {D : Set HeightTwo} (hD : NonemptyDirected D) :
    ∃ q ∈ D, ∀ p ∈ D, p ≤ q := by
  classical
  by_cases hC : ∃ n, c n ∈ D
  · obtain ⟨n, hn⟩ := hC
    refine ⟨c n, hn, ?_⟩
    intro p hp
    obtain ⟨q, _, hcnq, hpq⟩ := hD.2 (c n) hn p hp
    exact c_maximal hcnq ▸ hpq
  · obtain ⟨q, hq⟩ := hD.1
    refine ⟨q, hq, ?_⟩
    intro p hp
    obtain ⟨r, hr, hqr, hpr⟩ := hD.2 q hq p hp
    cases r with
    | b n =>
      have heq := le_b_eq hqr
      exact heq.symm ▸ hpr
    | c n => exact False.elim (hC ⟨n, hr⟩)

theorem dcpo : IsDcpo HeightTwo := by
  intro D hD
  obtain ⟨q, hq, hbound⟩ := directed_has_greatest hD
  exact ⟨q, hbound, fun _ h ↦ h hq⟩

theorem all_compact (q : HeightTwo) : Compact q := by
  intro D hD s hs hqs
  obtain ⟨p, hp, hbound⟩ := directed_has_greatest hD
  have hsp : s = p := hs.unique ⟨hbound, fun _ h ↦ h hp⟩
  exact ⟨p, hp, hsp ▸ hqs⟩

theorem scottClosed_iff_lower (F : Set HeightTwo) : IsScottClosed F ↔ IsLowerSet F := by
  refine ⟨And.left, fun hl ↦ ⟨hl, ?_⟩⟩
  intro D hDF hD s hs
  obtain ⟨p, hp, hbound⟩ := directed_has_greatest hD
  have hsp : s = p := hs.unique ⟨hbound, fun _ h ↦ h hp⟩
  exact hsp.symm ▸ hDF hp

theorem principal_finite (q : HeightTwo) : (Set.Iic q).Finite := by
  classical
  cases q with
  | b n =>
    apply (Set.finite_singleton (b n)).subset
    intro p hp
    exact Set.mem_singleton_iff.mpr (le_b_eq hp)
  | c n =>
    let F : Finset HeightTwo := insert (c n) ((Finset.range (n + 1)).image b)
    apply F.finite_toSet.subset
    intro p hp
    cases p with
    | b m =>
      exact Finset.mem_insert_of_mem (Finset.mem_image.mpr
        ⟨m, Finset.mem_range.mpr hp, rfl⟩)
    | c m =>
      exact Finset.mem_insert.mpr (Or.inl (congrArg c hp))

theorem B_infinite : (B : Set HeightTwo).Infinite := by
  have hinj : Function.Injective b := fun m n h ↦ HeightTwo.b.inj h
  have heq : (B : Set HeightTwo) = Set.range b := by
    ext q
    constructor
    · rintro ⟨n, rfl⟩
      exact Set.mem_range_self n
    · rintro ⟨n, rfl⟩
      exact b_mem_B n
  rw [heq]
  exact Set.infinite_range_of_injective hinj

/-- Source `prop:same-lattice`, the complete three-way characterization. -/
theorem same_lattice_formula (A E : LowerSet HeightTwo) :
    (ChainBelow A E ↔ WayBelow A E) ∧
      (WayBelow A E ↔ A ≤ E ∧ (A : Set HeightTwo).Finite) :=
  ⟨lowerSet_chainBelow_iff_wayBelow A E, lowerSet_wayBelow_iff_finite principal_finite A E⟩

theorem B_not_wayBelow_top : ¬ WayBelow B (⊤ : LowerSet HeightTwo) :=
  fun h ↦ B_infinite ((lowerSet_wayBelow_iff_finite principal_finite B ⊤).mp h).2

def twoB : LowerSet HeightTwo :=
  ⟨{b 0, b 1}, by
    intro y x hxy hy
    rcases Set.mem_insert_iff.mp hy with hy | hy
    · exact Set.mem_insert_iff.mpr (Or.inl (le_b_eq (hy ▸ hxy)))
    · exact Set.mem_insert_iff.mpr (Or.inr
        (Set.mem_singleton_iff.mpr (le_b_eq ((Set.mem_singleton_iff.mp hy) ▸ hxy))))⟩

theorem twoB_finite : (twoB : Set HeightTwo).Finite := (Set.finite_singleton (b 1)).insert (b 0)

theorem twoB_wayBelow_self : WayBelow twoB twoB := finite_lowerSet_wayBelow twoB_finite le_rfl

theorem twoB_not_closedBelow_self : ¬ ClosedBelow twoB twoB := by
  intro hF
  obtain ⟨q, hq, hbound⟩ := (closedBelow_iff_finiteUpper twoB twoB
    ⟨b 0, Set.mem_insert _ _⟩).mp hF {b 0, b 1} (by simp [twoB])
  have h0 : b 0 ≤ q := hbound _ (Finset.mem_insert_self _ _)
  have h1 : b 1 ≤ q := hbound _ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  rcases Set.mem_insert_iff.mp hq with rfl | hq
  · have hbad : 1 = 0 := h1
    omega
  · have heq : q = b 1 := Set.mem_singleton_iff.mp hq
    have hbad : b 0 ≤ b 1 := heq ▸ h0
    change 0 = 1 at hbad
    omega

/-- The relations are incomparable, with the two source witnesses. -/
theorem relations_incomparable :
    (∃ A E : LowerSet HeightTwo, ClosedBelow A E ∧ ¬ WayBelow A E) ∧
      ∃ A E : LowerSet HeightTwo, WayBelow A E ∧ ¬ ClosedBelow A E :=
  ⟨⟨B, ⊤, B_closedBelow_top, B_not_wayBelow_top⟩,
    ⟨twoB, twoB, twoB_wayBelow_self, twoB_not_closedBelow_self⟩⟩

/-- Source `thm:closed-counter`, the structural hypotheses and the explicit
noninterpolating pair, using the actual completely distributive lower-set lattice. -/
theorem closed_counter :
    IsCountablyBased (LowerSet HeightTwo) ∧ IsCompletelyDistributive (LowerSet HeightTwo) ∧
      IsAlgebraic (LowerSet HeightTwo) ∧ IsClosedContinuous (LowerSet HeightTwo) ∧
      IsClosedContinuousPlus (LowerSet HeightTwo) ∧ ClosedBelow B (⊤ : LowerSet HeightTwo) ∧
      ¬ RelComp ClosedBelow ClosedBelow B (⊤ : LowerSet HeightTwo) :=
  ⟨lowerSet_countablyBased, lowerSet_completelyDistributive, lowerSet_algebraic,
    lowerSet_closedContinuous, lowerSet_closedContinuousPlus, B_closedBelow_top, B_no_closed_intermediate⟩

/-- Source `prop:same-lattice`, the positive chain-approximation assertions
and the negative Scott-closed assertions on the same lattice. -/
theorem same_lattice :
    IsDcpo (LowerSet HeightTwo) ∧ IsChainContinuous (LowerSet HeightTwo) ∧
      Interpolates (ChainBelow (P := LowerSet HeightTwo)) ∧
      (∀ A E : LowerSet HeightTwo, (ChainBelow A E ↔ WayBelow A E) ∧
        (WayBelow A E ↔ A ≤ E ∧ (A : Set HeightTwo).Finite)) ∧
      ¬ Interpolates (ClosedBelow (M := LowerSet HeightTwo)) ∧
      ¬ Interpolates (ClosedBelowPlus (M := LowerSet HeightTwo)) :=
  ⟨completeLattice_dcpo, lowerSet_chainContinuous, lowerSet_chain_interpolates,
    same_lattice_formula, closedBelow_does_not_interpolate, closedBelowPlus_does_not_interpolate⟩

end HeightTwo
end ChainApproximation
