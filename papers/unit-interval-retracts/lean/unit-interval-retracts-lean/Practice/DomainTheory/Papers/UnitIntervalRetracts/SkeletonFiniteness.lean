import Practice.DomainTheory.Papers.UnitIntervalRetracts.SparseInterval

/-!
# Finiteness of large intervals in the sparse skeleton

This file proves item (3) of `lem:skeleton-finiteness` from the source
manuscript.  The proof first bounds the diameter of every basic interval, then
shows that only finitely many basic indices can occur at a fixed positive
diameter scale, and finally passes to finite intersections via a powerset.
-/

set_option autoImplicit false
set_option linter.unnecessarySimpa false

namespace UnitIntervalRetracts

open Set

noncomputable section

/-- Every subset of the unit-interval subtype is metrically bounded. -/
theorem isBounded_set_X (A : Set X) : Bornology.IsBounded A :=
  Metric.isBounded_iff.2 ⟨2, by
    intro x _hx y _hy
    have hx0 : 0 ≤ (x : ℝ) := x.2.1
    have hx1 : (x : ℝ) ≤ 1 := x.2.2
    have hy0 : 0 ≤ (y : ℝ) := y.2.1
    have hy1 : (y : ℝ) ≤ 1 := y.2.2
    rw [Subtype.dist_eq, Real.dist_eq]
    have hxy : |(x : ℝ) - (y : ℝ)| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith
    linarith⟩

/-- Equation `eq:J-diameter-bound`: `diam J_{n,k} ≤ 2 / 2^n`. -/
theorem diam_J_le (i : BasicIndex) :
    Metric.diam (J i) ≤ 2 / (2 : ℝ) ^ i.level := by
  apply Metric.diam_le_of_forall_dist_le (by positivity)
  intro x hx y hy
  have hx' := (mem_J_iff (i := i) (x := x)).1 hx
  have hy' := (mem_J_iff (i := i) (x := y)).1 hy
  have hwidth :
      basicRight i - basicLeft i = 2 / (2 : ℝ) ^ i.level := by
    rw [basicLeft, basicRight]
    ring
  rw [Subtype.dist_eq, Real.dist_eq, abs_le]
  constructor
  · rw [← hwidth]
    linarith
  · rw [← hwidth]
    linarith

/-- At each fixed level there are only finitely many valid basic indices. -/
theorem finite_indices_at_level (n : ℕ) :
    {i : BasicIndex | i.level = n}.Finite := by
  by_cases hn : 1 ≤ n
  · let positions : Set ℕ := {k | k ≤ 2 ^ n}
    have hPositions : positions.Finite := Set.finite_le_nat (2 ^ n)
    let makeIndex : positions → BasicIndex :=
      fun k => ⟨(n, k.1), hn, k.2⟩
    have hRange : (Set.range makeIndex).Finite := by
      letI : Finite positions := hPositions.to_subtype
      exact Set.finite_range makeIndex
    apply hRange.subset
    intro i hi
    change i.level = n at hi
    have hpos : i.position ∈ positions := by
      change i.position ≤ 2 ^ n
      rw [← hi]
      exact i.position_le
    refine ⟨⟨i.position, hpos⟩, ?_⟩
    apply Subtype.ext
    apply Prod.ext
    · exact hi.symm
    · rfl
  · have hEmpty : {i : BasicIndex | i.level = n} = ∅ := by
      ext i
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro hi
      exact hn (hi ▸ i.one_le_level)
    rw [hEmpty]
    exact Set.finite_empty

/-- There are finitely many valid source indices up to any fixed level. -/
theorem finite_indices_level_le (N : ℕ) :
    {i : BasicIndex | i.level ≤ N}.Finite := by
  let levels : Set ℕ := {n | n ≤ N}
  have hLevels : levels.Finite := Set.finite_le_nat N
  have hFibers :
      ∀ n ∈ levels,
        ((fun i : BasicIndex => i.level) ⁻¹' {n}).Finite := by
    intro n _hn
    have hFiberEq :
        (fun i : BasicIndex => i.level) ⁻¹' {n} =
          {i : BasicIndex | i.level = n} := by
      ext i
      simp
    rw [hFiberEq]
    exact finite_indices_at_level n
  have hPreimage :
      ((fun i : BasicIndex => i.level) ⁻¹' levels).Finite :=
    hLevels.preimage' hFibers
  simpa [levels] using hPreimage

/-- For positive `ε`, only finitely many basic intervals have diameter at
least `ε`. -/
theorem finite_large_basic_indices {ε : ℝ} (hε : 0 < ε) :
    {i : BasicIndex | ε ≤ Metric.diam (J i)}.Finite := by
  obtain ⟨N, hN⟩ := exists_nat_gt (2 / ε)
  apply (finite_indices_level_le N).subset
  intro i hi
  change i.level ≤ N
  by_contra hnot
  have hNlevelNat : N < i.level := Nat.lt_of_not_ge hnot
  have hNlevel : (N : ℝ) < (i.level : ℝ) := by
    exact_mod_cast hNlevelNat
  have hLevelPowNat : i.level < 2 ^ i.level :=
    Nat.lt_two_pow_self
  have hLevelPow :
      (i.level : ℝ) < (2 : ℝ) ^ i.level := by
    exact_mod_cast hLevelPowNat
  have hRatioPow : 2 / ε < (2 : ℝ) ^ i.level :=
    hN.trans (hNlevel.trans hLevelPow)
  have hPowPos : 0 < (2 : ℝ) ^ i.level := by positivity
  have hSmall : 2 / (2 : ℝ) ^ i.level < ε := by
    apply (div_lt_iff₀ hPowPos).2
    have hMul : 2 < (2 : ℝ) ^ i.level * ε :=
      (div_lt_iff₀ hε).1 hRatioPow
    simpa [mul_comm] using hMul
  have hLargeBound :
      ε ≤ 2 / (2 : ℝ) ^ i.level :=
    hi.trans (diam_J_le i)
  exact (not_lt_of_ge hLargeBound) hSmall

/-- Lemma `lem:skeleton-finiteness` (3): at every positive scale, only
finitely many skeleton intervals remain. -/
theorem skeleton_large_diameter_finite {ε : ℝ} (hε : 0 < ε) :
    {B : Set X | B ∈ Skeleton ∧ ε ≤ Metric.diam B}.Finite := by
  let largeIndices : Set BasicIndex :=
    {i | ε ≤ Metric.diam (J i)}
  have hLargeIndices : largeIndices.Finite := by
    exact finite_large_basic_indices hε
  let indexFinset : Finset BasicIndex := hLargeIndices.toFinset
  let candidateRepresentations : Set (Finset BasicIndex) :=
    (indexFinset.powerset : Set (Finset BasicIndex))
  have hCandidateRepresentations : candidateRepresentations.Finite :=
    indexFinset.powerset.finite_toSet
  have hCandidateIntersections :
      (basicIntersection '' candidateRepresentations).Finite :=
    hCandidateRepresentations.image basicIntersection
  apply hCandidateIntersections.subset
  intro B hB
  rcases hB.1 with ⟨s, _hsNonempty, _hBeq, _hBNontrivial⟩
  subst B
  refine ⟨s, ?_, rfl⟩
  change s ∈ indexFinset.powerset
  rw [Finset.mem_powerset]
  intro i hi
  apply hLargeIndices.mem_toFinset.2
  change ε ≤ Metric.diam (J i)
  have hSubset : basicIntersection s ⊆ J i := by
    intro x hx
    exact (mem_basicIntersection_iff.mp hx) i hi
  exact hB.2.trans (Metric.diam_mono hSubset (isBounded_set_X (J i)))

end

end UnitIntervalRetracts
