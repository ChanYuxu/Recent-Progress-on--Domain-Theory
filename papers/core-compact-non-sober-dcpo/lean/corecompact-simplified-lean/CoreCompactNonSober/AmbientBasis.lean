import CoreCompactNonSober.AmbientScott
import Mathlib.Data.Finset.Max
import Mathlib.Logic.Encodable.Basic

/-!
# A countable basis of positive finite-coordinate tests

Source: the basis argument of `prop:ambient-properties`. The first basis below
uses arbitrary finite intersections of required-entry and rational-height
tests. The source-exact `PrintedBasic` family then normalizes those tests to
finitely many entry requirements and at most one rational threshold in
`[0,1)`, exactly as displayed in Proposition 3.4.
-/

set_option autoImplicit false

namespace CoreCompactNonSober.Ambient

open Set TopologicalSpace

abbrev Entry := Σ j : Coordinate, Alphabet j
abbrev Constraint := Entry ⊕ ℚ

def constraintSet : Constraint → Set Carrier
  | Sum.inl e => entrySet e.1 e.2
  | Sum.inr q => heightAbove (q : ℝ)

def basicSet (F : Finset Constraint) : Set Carrier :=
  ⋂ c ∈ F, constraintSet c

theorem constraintSet_isOpen_scott (c : Constraint) :
    @IsOpen Carrier (scottTopology Carrier) (constraintSet c) := by
  apply (isOpen_scott_iff _).mpr
  cases c with
  | inl e => exact entrySet_isScottOpen e.1 e.2
  | inr q => exact heightAbove_isScottOpen q

theorem basicSet_isOpen_scott (F : Finset Constraint) :
    @IsOpen Carrier (scottTopology Carrier) (basicSet F) := by
  letI : TopologicalSpace Carrier := scottTopology Carrier
  exact isOpen_biInter_finset (fun c _ ↦ constraintSet_isOpen_scott c)

private theorem separating_constraint {U : Set Carrier}
    (hU : @IsOpen Carrier (scottTopology Carrier) U)
    {x y : Carrier} (hx : x ∈ U) (hy : y ∉ U) :
    ∃ c : Constraint, x ∈ constraintSet c ∧
      ∃ O : Set Carrier, IsOpen O ∧ y ∈ O ∧ Disjoint O (constraintSet c) := by
  classical
  have hupper : IsUpperSet U := ((isOpen_scott_iff U).mp hU).1
  have hxy : ¬ x ≤ y := fun h ↦ hy (hupper h hx)
  by_cases hheight : height x ≤ height y
  · have hmiss : ¬ ∀ j, configuration x j ⊆ configuration y j :=
      fun h ↦ hxy ((le_iff x y).mpr ⟨hheight, h⟩)
    obtain ⟨j, hj⟩ := not_forall.mp hmiss
    obtain ⟨z, hzx, hzy⟩ := Finset.not_subset.mp hj
    refine ⟨Sum.inl ⟨j, z⟩, hzx, (entrySet j z)ᶜ,
      (entrySet_isClosed_aux j z).isOpen_compl, hzy, ?_⟩
    exact Set.disjoint_left.mpr (fun _ hpO hpC ↦ hpO hpC)
  · have hlt : height y < height x := lt_of_not_ge hheight
    obtain ⟨q, hyq, hqx⟩ := exists_rat_btwn hlt
    refine ⟨Sum.inr q, hqx, {p : Carrier | height p < (q : ℝ)},
      isOpen_lt continuous_height continuous_const, hyq, ?_⟩
    apply Set.disjoint_left.mpr
    intro p hpO hpC
    change (q : ℝ) < height p at hpC
    exact lt_asymm hpO hpC

/-- Every intrinsic Scott neighborhood contains a finite positive test
neighborhood, using compactness of its auxiliary-closed complement. -/
theorem exists_basic_subset (x : Carrier) (U : Set Carrier)
    (hx : x ∈ U) (hU : @IsOpen Carrier (scottTopology Carrier) U) :
    ∃ F : Finset Constraint, x ∈ basicSet F ∧ basicSet F ⊆ U := by
  classical
  let K : Set Carrier := Uᶜ
  have hK : IsCompact K :=
    ((isOpen_scott_iff_aux_open_upper U).mp hU).1.isClosed_compl.isCompact
  have hchoose : ∀ y : K, ∃ c : Constraint, x ∈ constraintSet c ∧
      ∃ O : Set Carrier, IsOpen O ∧ (y : Carrier) ∈ O ∧ Disjoint O (constraintSet c) := by
    intro y
    exact separating_constraint hU hx y.property
  choose c hc O hO hyO hdisj using hchoose
  have hcover : K ⊆ ⋃ y : K, O y := by
    intro y hy
    exact Set.mem_iUnion.mpr ⟨⟨y, hy⟩, hyO ⟨y, hy⟩⟩
  obtain ⟨I, hI⟩ := hK.elim_finite_subcover O hO hcover
  let F : Finset Constraint := I.image c
  refine ⟨F, ?_, ?_⟩
  · apply Set.mem_iInter.mpr
    intro d
    apply Set.mem_iInter.mpr
    intro hd
    obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hd
    exact hc y
  · intro p hp
    by_contra hpU
    obtain ⟨y, hy⟩ := Set.mem_iUnion.mp (hI hpU)
    obtain ⟨hyI, hpO⟩ := Set.mem_iUnion.mp hy
    have hpC : p ∈ constraintSet (c y) :=
      Set.mem_iInter.mp (Set.mem_iInter.mp hp (c y)) (Finset.mem_image_of_mem c hyI)
    exact Set.disjoint_left.mp (hdisj y) hpO hpC

theorem basic_isTopologicalBasis :
    @IsTopologicalBasis Carrier (scottTopology Carrier) (Set.range basicSet) := by
  letI : TopologicalSpace Carrier := scottTopology Carrier
  apply isTopologicalBasis_of_isOpen_of_nhds
  · rintro _ ⟨F, rfl⟩
    exact basicSet_isOpen_scott F
  · intro x U hx hU
    obtain ⟨F, hxF, hFU⟩ := exists_basic_subset x U hx hU
    exact ⟨basicSet F, ⟨F, rfl⟩, hxF, hFU⟩

/-- A rational threshold in the exact range printed in Proposition 3.4. -/
abbrev PrintedThreshold := {q : ℚ // 0 ≤ q ∧ q < 1}

/-- An index for one of the two displayed forms in Proposition 3.4:
finitely many positive coordinate-entry requirements, and optionally one
rational height threshold in `[0,1)`. -/
structure PrintedBasic where
  entries : Finset Entry
  threshold : Option PrintedThreshold
deriving DecidableEq

instance : Countable PrintedBasic :=
  (show Function.Injective
      (fun B : PrintedBasic => (B.entries, B.threshold)) from by
    intro B C h
    cases B
    cases C
    simpa using h).countable

/-- The subset of the ambient lattice specified by a printed basis index.
Every entry in `B.entries` is required to be present; the optional threshold
is a single strict height test. -/
def printedBasicSet (B : PrintedBasic) : Set Carrier :=
  (⋂ e ∈ B.entries, entrySet e.1 e.2) ∩
    match B.threshold with
    | none => Set.univ
    | some q => heightAbove (q : ℚ)

theorem printedBasicSet_isOpen_scott (B : PrintedBasic) :
    @IsOpen Carrier (scottTopology Carrier) (printedBasicSet B) := by
  letI : TopologicalSpace Carrier := scottTopology Carrier
  apply IsOpen.inter
  · exact isOpen_biInter_finset (fun e _ => (isOpen_scott_iff _).mpr
      (entrySet_isScottOpen e.1 e.2))
  · cases B.threshold with
    | none => exact isOpen_univ
    | some q => exact (isOpen_scott_iff _).mpr (heightAbove_isScottOpen q)

private def entryRequirements (F : Finset Constraint) : Finset Entry :=
  F.biUnion fun c =>
    match c with
    | Sum.inl e => {e}
    | Sum.inr _ => ∅

private def nonnegativeThresholds (F : Finset Constraint) : Finset ℚ :=
  F.biUnion fun c =>
    match c with
    | Sum.inl _ => ∅
    | Sum.inr q => if 0 ≤ q then {q} else ∅

private theorem mem_entryRequirements_iff (F : Finset Constraint) (e : Entry) :
    e ∈ entryRequirements F ↔ Sum.inl e ∈ F := by
  classical
  simp [entryRequirements]

private theorem mem_nonnegativeThresholds_iff (F : Finset Constraint) (q : ℚ) :
    q ∈ nonnegativeThresholds F ↔ Sum.inr q ∈ F ∧ 0 ≤ q := by
  classical
  rw [nonnegativeThresholds, Finset.mem_biUnion]
  constructor
  · rintro ⟨c, hcF, hc⟩
    cases c with
    | inl e => simp at hc
    | inr r =>
        by_cases hr : 0 ≤ r
        · simp [hr] at hc
          subst r
          exact ⟨hcF, hr⟩
        · simp [hr] at hc
  · rintro ⟨hqF, hq⟩
    exact ⟨Sum.inr q, hqF, by simp [hq]⟩

/-- Every finite-constraint basic neighborhood has, at each of its points, a
contained member of the exact two-form family printed in Proposition 3.4.
Negative height constraints are redundant, while all remaining height
constraints collapse to their finite maximum. -/
theorem exists_printedBasic_subset_basicSet (x : Carrier) (F : Finset Constraint)
    (hxF : x ∈ basicSet F) :
    ∃ B : PrintedBasic,
      x ∈ printedBasicSet B ∧ printedBasicSet B ⊆ basicSet F := by
  classical
  let E : Finset Entry := entryRequirements F
  let T : Finset ℚ := nonnegativeThresholds F
  by_cases hT : T.Nonempty
  · have hmax_mem : T.max' hT ∈ T := T.max'_mem hT
    have hmaxF : Sum.inr (T.max' hT) ∈ F :=
      (mem_nonnegativeThresholds_iff F (T.max' hT)).mp hmax_mem |>.1
    have hmax_nonneg : 0 ≤ T.max' hT :=
      (mem_nonnegativeThresholds_iff F (T.max' hT)).mp hmax_mem |>.2
    have hmax_x : (T.max' hT : ℝ) < height x :=
      Set.mem_iInter.mp (Set.mem_iInter.mp hxF (Sum.inr (T.max' hT))) hmaxF
    have hmax_one : T.max' hT < (1 : ℚ) := by
      exact_mod_cast hmax_x.trans_le x.val.1.property.2
    let r : PrintedThreshold := ⟨T.max' hT, hmax_nonneg, hmax_one⟩
    let B : PrintedBasic := ⟨E, some r⟩
    refine ⟨B, ?_, ?_⟩
    · refine ⟨?_, hmax_x⟩
      apply Set.mem_iInter.mpr
      intro e
      apply Set.mem_iInter.mpr
      intro he
      have heF : Sum.inl e ∈ F := (mem_entryRequirements_iff F e).mp he
      exact Set.mem_iInter.mp (Set.mem_iInter.mp hxF (Sum.inl e)) heF
    · intro p hp
      apply Set.mem_iInter.mpr
      intro c
      apply Set.mem_iInter.mpr
      intro hcF
      rcases hp with ⟨hpE, hpR⟩
      cases c with
      | inl e =>
          have heE : e ∈ E := (mem_entryRequirements_iff F e).mpr hcF
          exact Set.mem_iInter.mp (Set.mem_iInter.mp hpE e) heE
      | inr q =>
          by_cases hq : 0 ≤ q
          · have hqT : q ∈ T :=
              (mem_nonnegativeThresholds_iff F q).mpr ⟨hcF, hq⟩
            have hqmax : q ≤ T.max' hT := T.le_max' q hqT
            change (T.max' hT : ℝ) < height p at hpR
            change (q : ℝ) < height p
            have hqmaxR : (q : ℝ) ≤ (T.max' hT : ℝ) := by
              exact_mod_cast hqmax
            exact hqmaxR.trans_lt hpR
          · have hqneg : q < 0 := lt_of_not_ge hq
            have hp0 : (0 : ℝ) ≤ height p := p.val.1.property.1
            change (q : ℝ) < height p
            have hqnegR : (q : ℝ) < 0 := by exact_mod_cast hqneg
            exact hqnegR.trans_le hp0
  · let B : PrintedBasic := ⟨E, none⟩
    refine ⟨B, ?_, ?_⟩
    · refine ⟨?_, Set.mem_univ x⟩
      apply Set.mem_iInter.mpr
      intro e
      apply Set.mem_iInter.mpr
      intro he
      have heF : Sum.inl e ∈ F := (mem_entryRequirements_iff F e).mp he
      exact Set.mem_iInter.mp (Set.mem_iInter.mp hxF (Sum.inl e)) heF
    · intro p hp
      apply Set.mem_iInter.mpr
      intro c
      apply Set.mem_iInter.mpr
      intro hcF
      rcases hp with ⟨hpE, _⟩
      cases c with
      | inl e =>
          have heE : e ∈ E := (mem_entryRequirements_iff F e).mpr hcF
          exact Set.mem_iInter.mp (Set.mem_iInter.mp hpE e) heE
      | inr q =>
          have hqneg : q < 0 := by
            by_contra hqn
            have hq : 0 ≤ q := le_of_not_gt hqn
            have hqT : q ∈ T :=
              (mem_nonnegativeThresholds_iff F q).mpr ⟨hcF, hq⟩
            exact hT ⟨q, hqT⟩
          have hp0 : (0 : ℝ) ≤ height p := p.val.1.property.1
          change (q : ℝ) < height p
          have hqnegR : (q : ℝ) < 0 := by exact_mod_cast hqneg
          exact hqnegR.trans_le hp0

/-- The literal family printed in Proposition 3.4 is a basis for the intrinsic
Scott topology on the ambient lattice. -/
theorem printedBasic_isTopologicalBasis :
    @IsTopologicalBasis Carrier (scottTopology Carrier)
      (Set.range printedBasicSet) := by
  letI : TopologicalSpace Carrier := scottTopology Carrier
  apply isTopologicalBasis_of_isOpen_of_nhds
  · rintro _ ⟨B, rfl⟩
    exact printedBasicSet_isOpen_scott B
  · intro x U hx hU
    obtain ⟨F, hxF, hFU⟩ := exists_basic_subset x U hx hU
    obtain ⟨B, hxB, hBF⟩ := exists_printedBasic_subset_basicSet x F hxF
    exact ⟨printedBasicSet B, ⟨B, rfl⟩, hxB, hBF.trans hFU⟩

theorem printedBasicFamily_countable : (Set.range printedBasicSet).Countable :=
  Set.countable_range printedBasicSet

theorem scottSecondCountable : ScottSecondCountable Carrier := by
  letI : TopologicalSpace Carrier := scottTopology Carrier
  exact printedBasic_isTopologicalBasis.secondCountableTopology
    printedBasicFamily_countable

end CoreCompactNonSober.Ambient
