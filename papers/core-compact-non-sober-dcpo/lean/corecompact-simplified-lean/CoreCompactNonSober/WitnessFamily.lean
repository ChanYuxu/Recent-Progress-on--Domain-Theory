import CoreCompactNonSober.HoleAlphabets
import CoreCompactNonSober.FinitePrefix
import CoreCompactNonSober.AuxiliaryNeighborhood

/-!
# A small family of downward neighborhood witnesses

Source: `lem:approximating-family`. The family uses exactly the printed
recipe: a uniform cutoff `M₀(h,k)` fixed before `ψ`, only `M ≥ M₀`, and
capacity-qualified finite prefixes. The tail is the complement of `Hⱼ^ψ`.
-/

set_option autoImplicit false

namespace CoreCompactNonSober.Ambient

open Set Cardinal Localization
open scoped Topology

abbrev RationalPair := {q : ℚ × ℚ // 0 < q.1 ∧ q.1 < q.2 ∧ q.2 < 1}

noncomputable def firstLevel (q : RationalPair) : ℝ := q.val.1
noncomputable def secondLevel (q : RationalPair) : ℝ := q.val.2

theorem firstLevel_pos (q : RationalPair) : 0 < firstLevel q := by
  change (0 : ℝ) < (q.val.1 : ℝ)
  exact_mod_cast q.property.1

theorem firstLevel_lt_second (q : RationalPair) : firstLevel q < secondLevel q := by
  change (q.val.1 : ℝ) < (q.val.2 : ℝ)
  exact_mod_cast q.property.2.1

theorem secondLevel_lt_one (q : RationalPair) : secondLevel q < 1 := by
  change (q.val.2 : ℝ) < 1
  exact_mod_cast q.property.2.2

theorem secondLevel_pos (q : RationalPair) : 0 < secondLevel q :=
  (firstLevel_pos q).trans (firstLevel_lt_second q)

noncomputable def chosenWitnessSlaloms (q : RationalPair) :
    Set (Slalom (HoleAlphabet (secondLevel q))
      (exponentialWidth ((secondLevel q - firstLevel q) / 2))) :=
  Classical.choose (hole_alphabet_capturing_family (secondLevel_pos q)
    (secondLevel_lt_one q).le (by linarith [firstLevel_lt_second q]))

theorem chosenWitnessSlaloms_spec (q : RationalPair) :
    IsCapturing (chosenWitnessSlaloms q) ∧ Cardinal.mk (chosenWitnessSlaloms q) ≤ lambda :=
  Classical.choose_spec (hole_alphabet_capturing_family (secondLevel_pos q)
    (secondLevel_lt_one q).le (by linarith [firstLevel_lt_second q]))

abbrev PrefixData := Σ M : ℕ, PrefixConfiguration M

abbrev WitnessData := Σ q : RationalPair, (chosenWitnessSlaloms q) × PrefixData

theorem witnessData_card_le : Cardinal.mk WitnessData ≤ lambda := by
  rw [Cardinal.mk_sigma]
  calc
    Cardinal.sum (fun q : RationalPair ↦ Cardinal.mk ((chosenWitnessSlaloms q) × PrefixData)) ≤
        Cardinal.sum (fun _q : RationalPair ↦ lambda) := by
      apply Cardinal.sum_le_sum
      intro q
      calc
        Cardinal.mk ((chosenWitnessSlaloms q) × PrefixData) =
            Cardinal.mk (chosenWitnessSlaloms q) * Cardinal.mk PrefixData := by simp
        _ ≤ lambda * Cardinal.aleph0 :=
          mul_le_mul' (chosenWitnessSlaloms_spec q).2 Cardinal.mk_le_aleph0
        _ = lambda := Cardinal.mul_eq_left aleph0_lt_lambda.le aleph0_lt_lambda.le Cardinal.aleph0_ne_zero
    _ = Cardinal.mk RationalPair * lambda := Cardinal.sum_const' _ _
    _ ≤ Cardinal.aleph0 * lambda := mul_le_mul_left Cardinal.mk_le_aleph0 lambda
    _ = lambda := Cardinal.mul_eq_right aleph0_lt_lambda.le aleph0_lt_lambda.le Cardinal.aleph0_ne_zero

noncomputable def witnessConfiguration (d : WitnessData) : Configuration :=
  splicePrefix d.2.2.1 d.2.2.2
    (fun j ↦ Finset.univ \ unionHoles d.2.1.val j)

/-- The source's uniform `M₀(h,k)`, independent of the slalom `ψ`. -/
noncomputable def witnessCutoff (q : RationalPair) : ℕ :=
  uniformWitnessCutoff (firstLevel_pos q) (firstLevel_lt_second q) (secondLevel_lt_one q)

theorem witnessCutoff_ge_two (q : RationalPair) : 2 ≤ witnessCutoff q :=
  (uniformWitnessCutoff_spec (firstLevel_pos q)
    (firstLevel_lt_second q) (secondLevel_lt_one q)).1

/-- These are exactly the permitted choices in the manuscript, not a filter
over all points that happen to satisfy the ambient capacity constraint. -/
def WitnessAdmissible (d : WitnessData) : Prop :=
  witnessCutoff d.1 ≤ d.2.2.1 ∧
    ∀ j : PrefixIndex d.2.2.1,
      firstLevel d.1 ≤ capacity (prefixCoordinate j) (d.2.2.2 j)

theorem witnessConfiguration_capacity (d : WitnessData) (hd : WitnessAdmissible d) :
    ∀ j, firstLevel d.1 ≤ capacity j (witnessConfiguration d j) := by
  intro j
  unfold witnessConfiguration splicePrefix
  split_ifs with hj
  · exact hd.2 ⟨j.val, Finset.mem_Ico.mpr ⟨j.property, hj⟩⟩
  · exact unionHoles_capacity_at (firstLevel_pos d.1)
      (firstLevel_lt_second d.1) (secondLevel_lt_one d.1) d.2.1.val j
      (hd.1.trans (by omega))

noncomputable def witnessPoint (d : {d : WitnessData // WitnessAdmissible d}) : Carrier :=
  ⟨(⟨firstLevel d.val.1, ⟨(firstLevel_pos d.val.1).le,
    ((firstLevel_lt_second d.val.1).trans (secondLevel_lt_one d.val.1)).le⟩⟩,
      witnessConfiguration d.val), witnessConfiguration_capacity d.val d.property⟩

def witnessFamily : Set Carrier := Set.range witnessPoint

theorem witnessFamily_card_le : Cardinal.mk witnessFamily ≤ lambda :=
  Cardinal.mk_range_le.trans ((Cardinal.mk_subtype_le WitnessAdmissible).trans witnessData_card_le)

theorem witnessFamily_positive : ∀ b ∈ witnessFamily, Positive b := by
  rintro b ⟨d, rfl⟩
  exact firstLevel_pos d.val.1

/-- Every actual reference point has exactly the manuscript's recipe; in
particular no cutoff below the common `M₀(h,k)` is admitted. -/
theorem witnessFamily_recipe (b : Carrier) (hb : b ∈ witnessFamily) :
    ∃ (q : RationalPair)
      (s : Slalom (HoleAlphabet (secondLevel q))
        (exponentialWidth ((secondLevel q - firstLevel q) / 2)))
      (M : ℕ) (A : PrefixConfiguration M),
      s ∈ chosenWitnessSlaloms q ∧ witnessCutoff q ≤ M ∧
        (∀ j : PrefixIndex M, firstLevel q ≤ capacity (prefixCoordinate j) (A j)) ∧
        height b = firstLevel q ∧
        ∀ j : Coordinate, configuration b j =
          if hj : j.val < M then
            A ⟨j.val, Finset.mem_Ico.mpr ⟨j.property, hj⟩⟩
          else Finset.univ \ unionHoles s j := by
  obtain ⟨⟨d, hd⟩, rfl⟩ := hb
  refine ⟨d.1, d.2.1.val, d.2.2.1, d.2.2.2,
    d.2.1.property, hd.1, hd.2, rfl, ?_⟩
  intro j
  rfl

theorem witnessFamily_approx (p : Carrier) (hp : Positive p)
    (U : ScottOpens Carrier) (hpU : p ∈ U) :
    ∃ b ∈ witnessFamily, b ∈ U ∧ b ≤ p := by
  classical
  letI : TopologicalSpace Carrier := scottTopology Carrier
  have hUaux : @IsOpen Carrier auxiliaryTopology (U : Set Carrier) :=
    ((isOpen_scott_iff_aux_open_upper _).mp U.isOpen).1
  obtain ⟨I, J, hI, hpI, hneigh⟩ := auxiliary_finite_neighborhood p U hUaux hpU
  obtain ⟨a, b, ⟨hat, htb⟩, hab⟩ :=
    mem_nhds_iff_exists_Ioo_subset.mp (hI.mem_nhds hpI)
  obtain ⟨h, hah, hht⟩ := exists_rat_btwn (max_lt hat hp)
  have hhI : (h : ℝ) ∈ I :=
    hab ⟨(le_max_left a 0).trans_lt hah, hht.trans htb⟩
  obtain ⟨k, hhk, hkt⟩ := exists_rat_btwn hht
  have hh0 : (0 : ℝ) < h := (le_max_right a 0).trans_lt hah
  have hk1 : (k : ℝ) < 1 := hkt.trans_le p.val.1.property.2
  let q : RationalPair := ⟨(h, k), by
    refine ⟨?_, ?_, ?_⟩
    · exact_mod_cast hh0
    · exact_mod_cast hhk
    · exact_mod_cast hk1⟩
  let holes : (j : Coordinate) → HoleAlphabet (secondLevel q) j := fun j ↦
    ⟨Finset.univ \ configuration p j,
      (capacity_ge_iff_holeBound j (configuration p j) (secondLevel_pos q)
        (secondLevel_lt_one q).le).mp (hkt.le.trans (p.property j))⟩
  obtain ⟨s, hs, M₀, hcapture⟩ := (chosenWitnessSlaloms_spec q).1 holes
  let M : ℕ := max M₀ (max (witnessCutoff q) (J.sup (fun j ↦ j.val + 1)))
  let d : WitnessData := ⟨q, (⟨s, hs⟩, ⟨M, restrictPrefix (configuration p) M⟩)⟩
  have hd : WitnessAdmissible d := by
    constructor
    · exact (le_max_left _ _).trans (le_max_right _ _)
    · intro j
      exact hht.le.trans (p.property (prefixCoordinate j))
  let b : Carrier := witnessPoint ⟨d, hd⟩
  have hbheight : height b = (h : ℝ) := rfl
  have hbconfig : ∀ j, configuration b j =
      if j.val < M then configuration p j else Finset.univ \ unionHoles s j := fun _ ↦ rfl
  have hbB : b ∈ witnessFamily := ⟨⟨d, hd⟩, rfl⟩
  refine ⟨b, hbB, ?_, ?_⟩
  · apply hneigh b (by rw [hbheight]; exact hhI)
    intro j hj
    have hcut : j.val + 1 ≤ J.sup (fun j ↦ j.val + 1) :=
      Finset.le_sup (f := fun j : Coordinate ↦ j.val + 1) hj
    have hjM : j.val < M := by dsimp [M]; omega
    rw [hbconfig, if_pos hjM]
  · apply (le_iff b p).mpr
    refine ⟨hht.le, ?_⟩
    intro j
    rw [hbconfig]
    split_ifs with hj
    · exact Finset.Subset.refl _
    · intro z hz
      have hjM₀ : M₀ ≤ j.val := by dsimp [M] at hj; omega
      have hhcap : holes j ∈ s.list j := hcapture j hjM₀
      by_contra hzp
      have hzholes : z ∈ (holes j).val := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hzp⟩
      have hzunion : z ∈ unionHoles s j := Finset.mem_biUnion.mpr ⟨holes j, hhcap, hzholes⟩
      exact (Finset.mem_sdiff.mp hz).2 hzunion

/-- The complete source witness-family lemma, now with its actual range. -/
theorem exists_witness_family : ∃ B : Set Carrier,
    Cardinal.mk B ≤ lambda ∧ (∀ b ∈ B, Positive b) ∧
      ∀ (p : Carrier), Positive p → ∀ U : ScottOpens Carrier, p ∈ U →
        ∃ b ∈ B, b ∈ U ∧ b ≤ p :=
  ⟨witnessFamily, witnessFamily_card_le, witnessFamily_positive, witnessFamily_approx⟩

end CoreCompactNonSober.Ambient
