import Practice.DomainTheory.Papers.UnitIntervalRetracts.ConcreteApproximation

/-!
# The critical interval and failure of continuity

This file formalizes `lem:K0-principal-ideal` and `prop:not-continuous`.
-/

set_option autoImplicit false
set_option linter.unnecessarySimpa false

namespace UnitIntervalRetracts

open Set Filter Topology
open AbramskyJung.Chapter2

noncomputable section

def K0Index : BasicIndex :=
  ⟨(2, 2), by norm_num⟩

def quarter : X :=
  ⟨(1 : ℝ) / 4, by norm_num⟩

def threeQuarter : X :=
  ⟨(3 : ℝ) / 4, by norm_num⟩

def eighth : X :=
  ⟨(1 : ℝ) / 8, by norm_num⟩

def half : X :=
  ⟨(1 : ℝ) / 2, by norm_num⟩

def zeroPoint : X :=
  ⟨0, by norm_num⟩

def K0Set : Set X :=
  J K0Index

@[simp]
theorem quarter_mem_K0Set : quarter ∈ K0Set := by
  change
    basicLeft K0Index ≤ (quarter : ℝ) ∧
      (quarter : ℝ) ≤ basicRight K0Index
  norm_num [K0Index, quarter, basicLeft, basicRight, BasicIndex.level,
    BasicIndex.position]

@[simp]
theorem threeQuarter_mem_K0Set : threeQuarter ∈ K0Set := by
  change
    basicLeft K0Index ≤ (threeQuarter : ℝ) ∧
      (threeQuarter : ℝ) ≤ basicRight K0Index
  norm_num [K0Index, threeQuarter, basicLeft, basicRight, BasicIndex.level,
    BasicIndex.position]

theorem zeroPoint_not_mem_K0Set : zeroPoint ∉ K0Set := by
  intro h
  have hleft := (mem_J_iff (i := K0Index) (x := zeroPoint)).mp h
  norm_num [K0Index, zeroPoint, basicLeft, BasicIndex.level,
    BasicIndex.position] at hleft

theorem K0Set_nontrivial : K0Set.Nontrivial := by
  refine ⟨quarter, quarter_mem_K0Set, threeQuarter,
    threeQuarter_mem_K0Set, ?_⟩
  intro h
  have hval := congrArg Subtype.val h
  norm_num [quarter, threeQuarter] at hval

theorem K0Set_mem_skeleton : K0Set ∈ Skeleton := by
  refine ⟨{K0Index}, by simp, ?_, K0Set_nontrivial⟩
  simp [K0Set, basicIntersection]

/-- The critical lattice element `K₀ = J_{2,2}`. -/
def K0 : P :=
  ofSkeleton K0Set_mem_skeleton

@[simp]
theorem coe_K0 : (K0 : Set X) = K0Set :=
  rfl

theorem mem_K0Set_iff {x : X} :
    x ∈ K0Set ↔ (1 : ℝ) / 4 ≤ (x : ℝ) ∧ (x : ℝ) ≤ (3 : ℝ) / 4 := by
  change
    basicLeft K0Index ≤ (x : ℝ) ∧ (x : ℝ) ≤ basicRight K0Index ↔ _
  norm_num [K0Index, basicLeft, basicRight, BasicIndex.level,
    BasicIndex.position]

/-- A basic interval containing `K₀` has index `(1,1)` or `(2,2)`. -/
theorem basicIndex_eq_whole_or_K0Index_of_K0Set_subset
    {i : BasicIndex} (hsubset : K0Set ⊆ J i) :
    i = BasicIndex.whole ∨ i = K0Index := by
  have hquarter :=
    (mem_J_iff (i := i) (x := quarter)).mp
      (hsubset quarter_mem_K0Set)
  have hthreeQuarter :=
    (mem_J_iff (i := i) (x := threeQuarter)).mp
      (hsubset threeQuarter_mem_K0Set)
  have hpowPos : 0 < (2 : ℝ) ^ i.level := by positivity
  have hleft :
      (i.position : ℝ) - 1 ≤
        ((1 : ℝ) / 4) * (2 : ℝ) ^ i.level := by
    apply (div_le_iff₀ hpowPos).mp
    simpa only [basicLeft, quarter] using hquarter.1
  have hright :
      ((3 : ℝ) / 4) * (2 : ℝ) ^ i.level ≤
        (i.position : ℝ) + 1 := by
    apply (le_div_iff₀ hpowPos).mp
    simpa only [basicRight, threeQuarter] using hthreeQuarter.2
  have hpowLe : (2 : ℝ) ^ i.level ≤ (2 : ℝ) ^ 2 := by
    norm_num
    linarith
  have hlevelLe : i.level ≤ 2 :=
    (pow_le_pow_iff_right₀ (a := (2 : ℝ)) (by norm_num)).mp hpowLe
  have honeLevel : 1 ≤ i.level := i.one_le_level
  have hlevel : i.level = 1 ∨ i.level = 2 := by
    omega
  rcases hlevel with hlevel | hlevel
  · have hpositionPosReal : 0 < (i.position : ℝ) := by
      norm_num [hlevel] at hright
      linarith
    have hpositionLtReal : (i.position : ℝ) < 2 := by
      norm_num [hlevel] at hleft
      linarith
    have hpositionPos : 0 < i.position := by
      exact_mod_cast hpositionPosReal
    have hpositionLt : i.position < 2 := by
      exact_mod_cast hpositionLtReal
    have hposition : i.position = 1 := by omega
    left
    apply Subtype.ext
    apply Prod.ext
    · simpa [BasicIndex.level, BasicIndex.whole] using hlevel
    · simpa [BasicIndex.position, BasicIndex.whole] using hposition
  · have hpositionLe : i.position ≤ 2 := by
      norm_num [hlevel] at hleft
      exact_mod_cast hleft
    have hpositionGe : 2 ≤ i.position := by
      norm_num [hlevel] at hright
      have hpositionGe' : 3 ≤ i.position + 1 := by
        exact_mod_cast hright
      omega
    have hposition : i.position = 2 :=
      Nat.le_antisymm hpositionLe hpositionGe
    right
    apply Subtype.ext
    apply Prod.ext
    · simpa [BasicIndex.level, K0Index] using hlevel
    · simpa [BasicIndex.position, K0Index] using hposition

theorem J_eq_univ_or_K0Set_of_K0Set_subset
    {i : BasicIndex} (hsubset : K0Set ⊆ J i) :
    J i = Set.univ ∨ J i = K0Set := by
  rcases basicIndex_eq_whole_or_K0Index_of_K0Set_subset hsubset with hi | hi
  · left
    simpa only [hi] using J_whole
  · right
    simpa only [K0Set, hi]

/-- Lemma `lem:K0-principal-ideal` in pointwise order form. -/
theorem le_K0_iff (A : P) :
    A ≤ K0 ↔ A = (⊥ : P) ∨ A = K0 := by
  constructor
  · intro hAK0
    have hK0subset : K0Set ⊆ (A : Set X) := by
      simpa only [coe_K0] using (le_def.mp hAK0)
    rcases A.isSparse with hA_skeleton | ⟨x, hx⟩ | hempty
    · rcases hA_skeleton with ⟨s, _hs_nonempty, hAeq, _hA_nontrivial⟩
      have hclassify :
          ∀ i ∈ s, J i = Set.univ ∨ J i = K0Set := by
        intro i hi
        apply J_eq_univ_or_K0Set_of_K0Set_subset
        intro y hy
        have hyA : y ∈ (A : Set X) := hK0subset hy
        rw [hAeq] at hyA
        exact (mem_basicIntersection_iff.mp hyA) i hi
      by_cases hK0occurs : ∃ i ∈ s, J i = K0Set
      · rcases hK0occurs with ⟨i, hi, hiK0⟩
        have hintersection_subset :
            basicIntersection s ⊆ K0Set := by
          intro y hy
          have hyi := (mem_basicIntersection_iff.mp hy) i hi
          simpa only [hiK0] using hyi
        have hK0_subset_intersection :
            K0Set ⊆ basicIntersection s := by
          intro y hy
          rw [mem_basicIntersection_iff]
          intro j hj
          rcases hclassify j hj with hjuniv | hjK0
          · rw [hjuniv]
            exact Set.mem_univ y
          · simpa only [hjK0] using hy
        right
        apply SetLike.coe_injective
        rw [coe_K0]
        exact hAeq.trans
          (Set.Subset.antisymm hintersection_subset hK0_subset_intersection)
      · have hall_univ : ∀ i ∈ s, J i = Set.univ := by
          intro i hi
          rcases hclassify i hi with hiuniv | hiK0
          · exact hiuniv
          · exact False.elim (hK0occurs ⟨i, hi, hiK0⟩)
        have hintersection_univ : basicIntersection s = Set.univ := by
          ext y
          constructor
          · intro _hy
            exact Set.mem_univ y
          · intro _hy
            rw [mem_basicIntersection_iff]
            intro i hi
            rw [hall_univ i hi]
            exact Set.mem_univ y
        left
        apply SetLike.coe_injective
        rw [coe_bot]
        exact hAeq.trans hintersection_univ
    · exfalso
      apply K0Set_nontrivial.not_subset_singleton
      rw [← hx]
      exact hK0subset
    · exfalso
      apply K0Set_nontrivial.not_subset_empty
      rw [← hempty]
      exact hK0subset
  · rintro (rfl | rfl)
    · exact bot_le
    · exact le_rfl

theorem lowerClosure_singleton_K0 :
    AbramskyJung.Chapter2.lowerClosure ({K0} : Set P) =
      ({⊥, K0} : Set P) := by
  ext A
  constructor
  · rintro ⟨B, hB, hAB⟩
    have hB_eq : B = K0 := by simpa using hB
    subst B
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using
      (le_K0_iff A).mp hAB
  · intro hA
    have hAK0 : A ≤ K0 :=
      (le_K0_iff A).mpr (by
        simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hA)
    exact ⟨K0, by simp, hAK0⟩

theorem K0_ne_top : K0 ≠ (⊤ : P) := by
  intro h
  have hcarrier := congrArg (fun A : P => (A : Set X)) h
  change (K0 : Set X) = ((⊤ : P) : Set X) at hcarrier
  rw [coe_K0, coe_top] at hcarrier
  exact K0Set_nontrivial.ne_empty hcarrier

theorem K0_ne_bot : K0 ≠ (⊥ : P) := by
  intro h
  have hcarrier := congrArg (fun A : P => (A : Set X)) h
  change (K0 : Set X) = ((⊥ : P) : Set X) at hcarrier
  rw [coe_K0, coe_bot] at hcarrier
  exact zeroPoint_not_mem_K0Set (hcarrier.symm ▸ Set.mem_univ zeroPoint)

/-- `1/4` is not a relative interior point of `K₀`. -/
theorem quarter_not_mem_interior_K0Set :
    quarter ∉ interior K0Set := by
  intro hquarterInterior
  have hlower : ∃ y : X, y < quarter := by
    exact ⟨eighth, by norm_num [eighth, quarter]⟩
  have hupper : ∃ y : X, quarter < y := by
    exact ⟨half, by norm_num [half, quarter]⟩
  have hnhds : K0Set ∈ 𝓝 quarter :=
    mem_interior_iff_mem_nhds.mp hquarterInterior
  rcases
      (mem_nhds_iff_exists_Ioo_subset' hlower hupper).mp hnhds with
    ⟨l, u, hquarterIoo, hIooSubset⟩
  rcases exists_between hquarterIoo.1 with ⟨y, hly, hyquarter⟩
  have hyIoo : y ∈ Set.Ioo l u :=
    ⟨hly, hyquarter.trans hquarterIoo.2⟩
  have hyK0 : y ∈ K0Set := hIooSubset hyIoo
  have hquarterLeY : quarter ≤ y := by
    exact (mem_K0Set_iff.mp hyK0).1
  exact (not_lt_of_ge hquarterLeY) hyquarter

theorem bot_wayBelow_K0 : (⊥ : P) ≪ K0 := by
  rw [wayBelow_iff_interior (⊥ : P) K0_ne_top]
  simp

theorem K0_not_wayBelow_self : ¬ K0 ≪ K0 := by
  rw [wayBelow_iff_interior K0 K0_ne_top]
  intro hsubset
  apply quarter_not_mem_interior_K0Set
  simpa only [coe_K0] using hsubset quarter_mem_K0Set

theorem wayBelowLower_K0 :
    wayBelowLower K0 = ({⊥} : Set P) := by
  ext A
  constructor
  · intro hA
    have hAway : A ≪ K0 := hA
    rcases (le_K0_iff A).mp (prop_2_2_2_1 hAway) with hAbot | hAK0
    · simpa only [Set.mem_singleton_iff] using hAbot
    · subst A
      exact False.elim (K0_not_wayBelow_self hAway)
  · intro hA
    have hAbot : A = (⊥ : P) := by simpa using hA
    subst A
    exact bot_wayBelow_K0

theorem not_isSup_wayBelowLower_K0 :
    ¬ IsSup (wayBelowLower K0) K0 := by
  intro hsup
  have hbotSup : IsSup ({⊥} : Set P) (⊥ : P) :=
    isSup_singleton (⊥ : P)
  rw [wayBelowLower_K0] at hsup
  exact K0_ne_bot (IsSup.unique hsup hbotSup)

/-- Proposition `prop:not-continuous`. -/
theorem not_isContinuousDomain_P :
    ¬ IsContinuousDomain P := by
  intro hcontinuous
  have hwholeBasis : IsBasis (Set.univ : Set P) :=
    prop_2_2_7_1.mp hcontinuous
  have hsupApproximants : IsSup (Approximants Set.univ K0) K0 :=
    (hwholeBasis K0).2
  have hApproximants :
      Approximants Set.univ K0 = wayBelowLower K0 := by
    ext A
    simp only [Approximants, Set.mem_setOf_eq, Set.mem_univ, true_and,
      mem_wayBelowLower]
  apply not_isSup_wayBelowLower_K0
  simpa only [hApproximants] using hsupApproximants

theorem not_isContinuousDcpo_P :
    ¬ IsContinuousDcpo P := by
  intro hcontinuous
  exact not_isContinuousDomain_P hcontinuous.2

end

end UnitIntervalRetracts
