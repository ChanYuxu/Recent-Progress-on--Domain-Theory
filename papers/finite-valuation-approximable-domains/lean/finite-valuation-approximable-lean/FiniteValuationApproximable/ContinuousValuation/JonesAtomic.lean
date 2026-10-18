import FiniteValuationApproximable.ContinuousValuation.JonesWayAbove
import Mathlib.Data.Set.Finite.Range

/-!
# Finite atomic continuous valuations

This file packages an arbitrary finite real linear combination of Dirac
valuations as a genuine continuous subprobability valuation.  The index type
is allowed to be any finite type; repeated support points are harmless and
make later dissection refinements substantially simpler.
-/

set_option autoImplicit false
set_option linter.unnecessarySimpa false

universe u v

namespace FiniteValuationApproximable
namespace ContinuousValuation

open Set
open AbramskyJung.Chapter2
open scoped ENNReal BigOperators

/-- Real mass of a finite atomic family on a Scott open. -/
noncomputable def finiteAtomicRealMass
    {D : Type u} [Preorder D] {I : Type v} [Fintype I]
    (point : I → D) (weight : I → ℝ) (U : ScottOpen D) : ℝ := by
  classical
  exact ∑ i, if point i ∈ U then weight i else 0

theorem finiteAtomicRealMass_nonneg
    {D : Type u} [Preorder D] {I : Type v} [Fintype I]
    (point : I → D) (weight : I → ℝ)
    (hweight : ∀ i, 0 ≤ weight i) (U : ScottOpen D) :
    0 ≤ finiteAtomicRealMass point weight U := by
  classical
  unfold finiteAtomicRealMass
  exact Finset.sum_nonneg fun i _ => by
    split_ifs
    · exact hweight i
    · exact le_rfl

theorem finiteAtomicRealMass_mono
    {D : Type u} [Preorder D] {I : Type v} [Fintype I]
    (point : I → D) (weight : I → ℝ)
    (hweight : ∀ i, 0 ≤ weight i) :
    Monotone (finiteAtomicRealMass point weight) := by
  classical
  intro U V hUV
  unfold finiteAtomicRealMass
  apply Finset.sum_le_sum
  intro i hi
  by_cases hiU : point i ∈ U
  · have hiV : point i ∈ V := hUV hiU
    simp [hiU, hiV]
  · by_cases hiV : point i ∈ V
    · simp [hiU, hiV, hweight i]
    · simp [hiU, hiV]

theorem finiteAtomicRealMass_empty
    {D : Type u} [Preorder D] {I : Type v} [Fintype I]
    (point : I → D) (weight : I → ℝ) :
    finiteAtomicRealMass point weight
      (ScottOpen.empty : ScottOpen D) = 0 := by
  classical
  simp [finiteAtomicRealMass]

theorem finiteAtomicRealMass_univ
    {D : Type u} [Preorder D] {I : Type v} [Fintype I]
    (point : I → D) (weight : I → ℝ) :
    finiteAtomicRealMass point weight
      (ScottOpen.univ : ScottOpen D) = ∑ i, weight i := by
  classical
  simp [finiteAtomicRealMass]

theorem finiteAtomicRealMass_modular
    {D : Type u} [Preorder D] {I : Type v} [Fintype I]
    (point : I → D) (weight : I → ℝ)
    (U V : ScottOpen D) :
    finiteAtomicRealMass point weight U +
        finiteAtomicRealMass point weight V =
      finiteAtomicRealMass point weight (ScottOpen.union U V) +
        finiteAtomicRealMass point weight (ScottOpen.inter U V) := by
  classical
  unfold finiteAtomicRealMass
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hiU : point i ∈ U <;>
      by_cases hiV : point i ∈ V <;>
    simp [hiU, hiV]

/-- Finite atomic mass is Scott-continuous as a function of the Scott open. -/
theorem finiteAtomicValue_scottContinuous
    {D : Type u} [Preorder D] {I : Type v} [Fintype I]
    (point : I → D) (weight : I → ℝ)
    (hweight : ∀ i, 0 ≤ weight i) :
    AbramskyJung.Chapter2.ScottContinuous
      (fun U : ScottOpen D =>
        ENNReal.ofReal (finiteAtomicRealMass point weight U)) := by
  classical
  constructor
  · intro U V hUV
    exact ENNReal.ofReal_le_ofReal
      (finiteAtomicRealMass_mono point weight hweight hUV)
  · intro A S hA hS
    constructor
    · rintro _ ⟨U, hUA, rfl⟩
      exact ENNReal.ofReal_le_ofReal
        (finiteAtomicRealMass_mono point weight hweight (hS.1 hUA))
    · intro y hy
      rcases hA.1 with ⟨U0, hU0A⟩
      have hSUnion : S = ScottOpen.sUnion A :=
        IsSup.unique hS (ScottOpen.sUnion_isSup A)
      have hwitness (i : I) (hiS : point i ∈ S) :
          ∃ U ∈ A, point i ∈ U := by
        have hiUnion : point i ∈ ScottOpen.sUnion A := by
          simpa [← hSUnion] using hiS
        exact ScottOpen.mem_sUnion_iff.mp hiUnion
      let pick : I → ScottOpen D := fun i =>
        if hi : point i ∈ S then Classical.choose (hwitness i hi) else U0
      have hpickA (i : I) : pick i ∈ A := by
        by_cases hi : point i ∈ S
        · simpa [pick, hi] using (Classical.choose_spec (hwitness i hi)).1
        · simp [pick, hi, hU0A]
      have hpickPoint (i : I) (hi : point i ∈ S) :
          point i ∈ pick i := by
        simpa [pick, hi] using (Classical.choose_spec (hwitness i hi)).2
      rcases hA.exists_upper_finite (Set.finite_range pick)
          (by rintro U ⟨i, rfl⟩; exact hpickA i) with
        ⟨Z, hZA, hZupper⟩
      have hZS : Z ≤ S := hS.1 hZA
      have hmass : finiteAtomicRealMass point weight S =
          finiteAtomicRealMass point weight Z := by
        unfold finiteAtomicRealMass
        apply Finset.sum_congr rfl
        intro i hi
        by_cases hiS : point i ∈ S
        · have hiZ : point i ∈ Z :=
            hZupper (pick i) ⟨i, rfl⟩ (hpickPoint i hiS)
          simp [hiS, hiZ]
        · have hiZ : point i ∉ Z := fun h => hiS (hZS h)
          simp [hiS, hiZ]
      change ENNReal.ofReal
          (finiteAtomicRealMass point weight S) ≤ y
      rw [hmass]
      exact hy ⟨Z, hZA, rfl⟩

/-- A finite nonnegative linear combination of Dirac valuations, with total
mass at most one. -/
noncomputable def finiteAtomicVSub
    {D : Type u} [Preorder D] {I : Type v} [Fintype I]
    (point : I → D) (weight : I → ℝ)
    (hweight : ∀ i, 0 ≤ weight i)
    (htotal : (∑ i, weight i) ≤ 1) : VSub D := by
  refine ⟨
    { toFun := fun U => ENNReal.ofReal
          (finiteAtomicRealMass point weight U)
      continuous := finiteAtomicValue_scottContinuous point weight hweight
      strict := by simp [finiteAtomicRealMass_empty]
      modular := ?_ }, ?_⟩
  · intro U V
    rw [← ENNReal.ofReal_add
          (finiteAtomicRealMass_nonneg point weight hweight U)
          (finiteAtomicRealMass_nonneg point weight hweight V),
      ← ENNReal.ofReal_add
          (finiteAtomicRealMass_nonneg point weight hweight
            (ScottOpen.union U V))
          (finiteAtomicRealMass_nonneg point weight hweight
            (ScottOpen.inter U V)),
      finiteAtomicRealMass_modular]
  · change ENNReal.ofReal
        (finiteAtomicRealMass point weight
          (ScottOpen.univ : ScottOpen D)) ≤ 1
    rw [finiteAtomicRealMass_univ point weight]
    calc
      ENNReal.ofReal (∑ i, weight i) ≤ ENNReal.ofReal 1 :=
        ENNReal.ofReal_le_ofReal htotal
      _ = 1 := by simp

@[simp]
theorem finiteAtomicVSub_apply
    {D : Type u} [Preorder D] {I : Type v} [Fintype I]
    (point : I → D) (weight : I → ℝ)
    (hweight : ∀ i, 0 ≤ weight i)
    (htotal : (∑ i, weight i) ≤ 1) (U : ScottOpen D) :
    finiteAtomicVSub point weight hweight htotal U =
      ENNReal.ofReal (finiteAtomicRealMass point weight U) :=
  rfl

theorem finiteAtomicVSub_apply_toReal
    {D : Type u} [Preorder D] {I : Type v} [Fintype I]
    (point : I → D) (weight : I → ℝ)
    (hweight : ∀ i, 0 ≤ weight i)
    (htotal : (∑ i, weight i) ≤ 1) (U : ScottOpen D) :
    (finiteAtomicVSub point weight hweight htotal U).toReal =
      finiteAtomicRealMass point weight U := by
  rw [finiteAtomicVSub_apply, ENNReal.toReal_ofReal]
  exact finiteAtomicRealMass_nonneg point weight hweight U

end ContinuousValuation
end FiniteValuationApproximable
