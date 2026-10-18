import Practice.DomainTheory.Papers.UnitIntervalRetracts.Lattice
import Mathlib.Topology.Order.IntermediateValue

/-!
# Interval geometry of the skeleton

The source repeatedly regards skeleton members as nondegenerate closed
intervals.  This file proves that identification in the relative order topology
of `X`, including the fact that only the two endpoints can lie outside the
relative interior.
-/

set_option autoImplicit false
set_option linter.unnecessarySimpa false

namespace UnitIntervalRetracts

open Set Topology

noncomputable section

theorem ordConnected_J (i : BasicIndex) : (J i).OrdConnected := by
  rw [Set.ordConnected_iff_uIcc_subset]
  intro x hx y hy z hz
  rcases le_total x y with hxy | hyx
  · rw [Set.uIcc_of_le hxy] at hz
    change basicLeft i ≤ (z : ℝ) ∧ (z : ℝ) ≤ basicRight i
    have hxz : (x : ℝ) ≤ (z : ℝ) := hz.1
    have hzy : (z : ℝ) ≤ (y : ℝ) := hz.2
    exact ⟨hx.1.trans hxz, hzy.trans hy.2⟩
  · rw [Set.uIcc_comm, Set.uIcc_of_le hyx] at hz
    change basicLeft i ≤ (z : ℝ) ∧ (z : ℝ) ≤ basicRight i
    have hyz : (y : ℝ) ≤ (z : ℝ) := hz.1
    have hzx : (z : ℝ) ≤ (x : ℝ) := hz.2
    exact ⟨hy.1.trans hyz, hzx.trans hx.2⟩

theorem ordConnected_basicIntersection (s : Finset BasicIndex) :
    (basicIntersection s).OrdConnected := by
  unfold basicIntersection
  apply Set.ordConnected_iInter
  intro i
  apply Set.ordConnected_iInter
  intro _hi
  exact ordConnected_J i

theorem Skeleton.ordConnected {B : Set X} (hB : B ∈ Skeleton) :
    B.OrdConnected := by
  rcases hB with ⟨s, _hs, rfl, _hNontrivial⟩
  exact ordConnected_basicIntersection s

theorem Skeleton.isConnected {B : Set X} (hB : B ∈ Skeleton) :
    IsConnected B :=
  ⟨Skeleton.nonempty hB, (Skeleton.ordConnected hB).isPreconnected⟩

/-- Every skeleton member is the closed interval between its two extrema. -/
theorem Skeleton.eq_Icc_sInf_sSup {B : Set X} (hB : B ∈ Skeleton) :
    B = Set.Icc (sInf B) (sSup B) := by
  exact
    eq_Icc_csInf_csSup_of_connected_bdd_closed
      (Skeleton.isConnected hB)
      (OrderBot.bddBelow B)
      (OrderTop.bddAbove B)
      (Skeleton.isClosed hB)

theorem Skeleton.sInf_mem {B : Set X} (hB : B ∈ Skeleton) :
    sInf B ∈ B :=
  (Skeleton.isClosed hB).isCompact.sInf_mem (Skeleton.nonempty hB)

theorem Skeleton.sSup_mem {B : Set X} (hB : B ∈ Skeleton) :
    sSup B ∈ B :=
  (Skeleton.isClosed hB).isCompact.sSup_mem (Skeleton.nonempty hB)

/-- The relative boundary of a skeleton interval is contained in its endpoint
pair; at `0` or `1`, an endpoint may itself be an interior point, so inclusion
is the correct source statement. -/
theorem Skeleton.diff_interior_subset_endpoints
    {B : Set X} (hB : B ∈ Skeleton) :
    B \ interior B ⊆ ({sInf B, sSup B} : Set X) := by
  intro x hx
  by_contra hEndpoints
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hEndpoints
  have hxIcc : x ∈ Set.Icc (sInf B) (sSup B) := by
    rw [← Skeleton.eq_Icc_sInf_sSup hB]
    exact hx.1
  have hLeft : sInf B < x :=
    lt_of_le_of_ne hxIcc.1 (Ne.symm hEndpoints.1)
  have hRight : x < sSup B :=
    lt_of_le_of_ne hxIcc.2 hEndpoints.2
  apply hx.2
  rw [Skeleton.eq_Icc_sInf_sSup hB]
  exact
    interior_maximal Set.Ioo_subset_Icc_self isOpen_Ioo
      ⟨hLeft, hRight⟩

end

end UnitIntervalRetracts
