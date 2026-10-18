import CoreCompactNonSober.AmbientBasis
import CoreCompactNonSober.AuxiliaryNeighborhood
import CoreCompactNonSober.Protection
import Mathlib.Data.Finset.Max

/-!
# Protected singleton insertion

Source: `lem:insertion` (i). We lower the height within a finite Scott
basis neighborhood and delete one common protecting letter on a sufficiently
late tail. Both membership in the genuine ambient carrier and membership in
the original Scott neighborhood are proved.
-/

set_option autoImplicit false

namespace CoreCompactNonSober.Ambient

open Set Cardinal Localization

private def heightThreshold : Constraint → ℝ
  | Sum.inl _ => 0
  | Sum.inr q => q

theorem intermediate_basic_height (b : Carrier) (hb : Positive b)
    (F : Finset Constraint) (hbF : b ∈ basicSet F) :
    ∃ u : ℝ, 0 < u ∧ u < height b ∧
      ∀ q : ℚ, Sum.inr q ∈ F → (q : ℝ) < u := by
  classical
  let T : Finset ℝ := insert 0 (F.image heightThreshold)
  have hTne : T.Nonempty := Finset.insert_nonempty _ _
  have hTlt : T.max' hTne < height b := by
    apply (Finset.max'_lt_iff T hTne).mpr
    intro r hr
    rcases Finset.mem_insert.mp hr with rfl | hr
    · exact hb
    · obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hr
      cases c with
      | inl e => exact hb
      | inr q => exact Set.mem_iInter.mp (Set.mem_iInter.mp hbF (Sum.inr q)) hc
  have hzero : 0 ≤ T.max' hTne := T.le_max' 0 (Finset.mem_insert_self _ _)
  let u : ℝ := (T.max' hTne + height b) / 2
  have hu0 : 0 < u := by dsimp [u]; linarith
  have hut : u < height b := by dsimp [u]; linarith
  refine ⟨u, hu0, hut, ?_⟩
  intro q hq
  have hqT : (q : ℝ) ∈ T :=
    Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨Sum.inr q, hq, rfl⟩)
  have hqm := T.le_max' (q : ℝ) hqT
  dsimp [u]
  linarith

def deleteTail (A : Configuration) (f : (j : Coordinate) → Alphabet j) (M : ℕ) :
    Configuration :=
  fun j ↦ if j.val < M then A j else A j \ {f j}

def entryCutoff : Constraint → ℕ
  | Sum.inl e => e.1.val + 1
  | Sum.inr _ => 0

/-- The exact recipe must survive the subsequent classical choice of a
recursive step, not merely occur in an erased existential proof. -/
def SingleInsertionRecipe (P : Set Carrier) (b : Carrier) (U : ScottOpens Carrier)
    (s : Carrier) : Prop :=
  ∃ (f : (j : Coordinate) → Alphabet j) (M : ℕ) (a c : ℝ) (J : Finset Coordinate),
    Protects P f ∧ 2 ≤ M ∧ height s < height b ∧
    1 / (M : ℝ) < height b - height s ∧
    configuration s = deleteTail (configuration b) f M ∧
    height b ∈ Set.Ioo a c ∧ height s ∈ Set.Ioo a c ∧
    (∀ j ∈ J, j.val < M) ∧
    (∀ q : Carrier, height q ∈ Set.Ioo a c →
      (∀ j ∈ J, configuration q j = configuration b j) → q ∈ U)

theorem single_insertion_prescribed (P : Set Carrier) (hP : ∀ p ∈ P, Positive p)
    (hsmall : Cardinal.mk P < lambda) (b : Carrier) (hb : Positive b)
    (U : ScottOpens Carrier) (hbU : b ∈ U) :
    ∃ s : Carrier, Positive s ∧ height s < 1 ∧ s ≤ b ∧ s ∈ U ∧
      (∀ p ∈ P, ¬ p ≤ s) ∧ HasHole s ∧ TailOmission s ∧
      SingleInsertionRecipe P b U s := by
  classical
  letI : TopologicalSpace Carrier := scottTopology Carrier
  obtain ⟨f, hf⟩ := exists_protection_pattern P hP hsmall
  have hUaux : @IsOpen Carrier auxiliaryTopology (U : Set Carrier) :=
    ((isOpen_scott_iff_aux_open_upper _).mp U.isOpen).1
  obtain ⟨a, c, J, hab, hbc, hneigh⟩ :=
    auxiliary_interval_finite_neighborhood b U hUaux hbU
  obtain ⟨u, hu0, hut, huI⟩ := lower_height_in_open hb isOpen_Ioo ⟨hab, hbc⟩
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / (height b - u))
  let M : ℕ := max 2 (max N (J.sup (fun j ↦ j.val + 1)))
  have hMtwo : 2 ≤ M := le_max_left _ _
  have htail : ∀ j : Coordinate, M ≤ j.val → 1 / (j.val : ℝ) < height b - u := by
    intro j hj
    have hgap : 0 < height b - u := sub_pos.mpr hut
    have hNj : (N : ℝ) ≤ (j.val : ℝ) := by
      exact_mod_cast ((le_max_left N (J.sup (fun j ↦ j.val + 1))).trans
        ((le_max_right 2 _).trans hj))
    have hmul : 1 < (N : ℝ) * (height b - u) := (div_lt_iff₀ hgap).mp hN
    apply (div_lt_iff₀ (coordinate_real_pos j)).mpr
    nlinarith
  have hadm : ∀ j, u ≤ capacity j (deleteTail (configuration b) f M j) := by
    intro j
    unfold deleteTail
    split_ifs with hj
    · exact hut.le.trans (b.property j)
    · have hloss := (capacity_deletion_loss j (configuration b j) (f j)).2
      have hstrict := htail j (by omega)
      have hcap := b.property j
      change height b ≤ capacity j (configuration b j) at hcap
      linarith
  let s : Carrier :=
    ⟨(⟨u, ⟨hu0.le, hut.le.trans b.val.1.property.2⟩⟩, deleteTail (configuration b) f M), hadm⟩
  refine ⟨s, hu0, hut.trans_le b.val.1.property.2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply (le_iff s b).mpr
    refine ⟨hut.le, ?_⟩
    intro j
    change deleteTail (configuration b) f M j ⊆ configuration b j
    unfold deleteTail
    split_ifs
    · exact Finset.Subset.refl _
    · exact Finset.sdiff_subset
  · apply hneigh s huI
    intro j hj
    have hcut : j.val + 1 ≤ J.sup (fun j ↦ j.val + 1) :=
      Finset.le_sup (f := fun j : Coordinate ↦ j.val + 1) hj
    have hjM : j.val < M := by dsimp [M]; omega
    change deleteTail (configuration b) f M j = configuration b j
    rw [deleteTail, if_pos hjM]
  · intro p hp
    apply not_le_of_tail_omission hf hp s M
    intro j hj
    change f j ∉ deleteTail (configuration b) f M j
    simp [deleteTail, not_lt_of_ge hj]
  · let j : Coordinate := ⟨max M 2, le_max_right _ _⟩
    refine ⟨j, f j, ?_⟩
    change f j ∉ deleteTail (configuration b) f M j
    have hj : M ≤ j.val := le_max_left _ _
    simp [deleteTail, not_lt_of_ge hj]
  · refine ⟨f, M, ?_⟩
    intro j hj
    change f j ∉ deleteTail (configuration b) f M j
    simp [deleteTail, not_lt_of_ge hj]
  · refine ⟨f, M, a, c, J, hf, hMtwo, hut, ?_, rfl, ⟨hab, hbc⟩, huI, ?_, hneigh⟩
    · exact htail ⟨M, hMtwo⟩ le_rfl
    · intro j hj
      have hcut : j.val + 1 ≤ J.sup (fun j ↦ j.val + 1) :=
        Finset.le_sup (f := fun j : Coordinate ↦ j.val + 1) hj
      dsimp [M]
      omega

/-- Printed existence conclusion, derived from the preserved recipe. -/
theorem single_insertion (P : Set Carrier) (hP : ∀ p ∈ P, Positive p)
    (hsmall : Cardinal.mk P < lambda) (b : Carrier) (hb : Positive b)
    (U : ScottOpens Carrier) (hbU : b ∈ U) :
    ∃ s : Carrier, Positive s ∧ height s < 1 ∧ s ≤ b ∧ s ∈ U ∧
      (∀ p ∈ P, ¬ p ≤ s) ∧ HasHole s ∧ TailOmission s := by
  obtain ⟨s, hpos, h1, hsb, hsU, havoid, hhole, htail, _⟩ :=
    single_insertion_prescribed P hP hsmall b hb U hbU
  exact ⟨s, hpos, h1, hsb, hsU, havoid, hhole, htail⟩

end CoreCompactNonSober.Ambient
