import FiniteValuationApproximable.ContinuousValuation.JonesApproximation

/-!
# Target-open estimates for Jones approximations

The selected refined cells partition according to their original Boolean
pattern.  Summing the cellwise cover estimates proves that the constructed
finite atomic valuation captures more than any prescribed factor `r < 1` of
the source valuation on every positive-mass finite union of target opens.
-/

set_option autoImplicit false
set_option linter.unnecessarySimpa false

universe u

namespace FiniteValuationApproximable
namespace ContinuousValuation

open Set
open AbramskyJung.Chapter2
open scoped ENNReal BigOperators

/-- A Boolean pattern meets one of the coordinates in `T`. -/
def patternHits {I : Type u} (T : Finset I) (p : MembershipPattern I) : Prop :=
  ∃ i ∈ T, p i = true

instance patternHits_decidable {I : Type u} [DecidableEq I]
    (T : Finset I) (p : MembershipPattern I) : Decidable (patternHits T p) := by
  unfold patternHits
  infer_instance

/-- Valid refined patterns whose original pattern meets `T`. -/
def selectedTargetPatterns
    {D : Type u} [Preorder D]
    (hD : AbramskyJung.Chapter2.IsContinuousDomain D)
    {I : Type u} [Fintype I] [DecidableEq I]
    (mu : VSub D) (O : I → ScottOpen D)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1)
    (T : Finset I) :
    Set (MembershipPattern
      (I ⊕ JonesSupport hD mu O t ht0 ht1)) :=
  {q | IsChosenRefinedPattern hD mu O t ht0 ht1 q ∧
    patternHits T (refinedOriginalPattern q)}

theorem refinedAtomicPoint_mem_target_iff
    {D : Type u} [Preorder D] [Nonempty D]
    (hD : AbramskyJung.Chapter2.IsContinuousDomain D)
    {I : Type u} [Fintype I] [DecidableEq I]
    (mu : VSub D) (O : I → ScottOpen D)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1)
    (T : Finset I)
    (q : MembershipPattern
      (I ⊕ JonesSupport hD mu O t ht0 ht1))
    (hq : IsChosenRefinedPattern hD mu O t ht0 ht1 q) :
    refinedAtomicPoint hD mu O t ht0 ht1 q ∈ finiteUnion O T ↔
      patternHits T (refinedOriginalPattern q) := by
  classical
  rw [mem_finiteUnion_iff]
  unfold patternHits
  have hpattern := refinedAtomicPoint_originalPattern
    hD mu O t ht0 ht1 q hq
  constructor
  · rintro ⟨i, hiT, hi⟩
    refine ⟨i, hiT, ?_⟩
    rw [← hpattern]
    exact (membershipSignature_apply_eq_true O _ i).mpr hi
  · rintro ⟨i, hiT, hi⟩
    refine ⟨i, hiT, ?_⟩
    apply (membershipSignature_apply_eq_true O _ i).mp
    rw [hpattern]
    exact hi

/-- Atomic real mass on a target union is the scale times the refined
signature mass of the selected target patterns. -/
theorem refinedAtomicRealMass_target
    {D : Type u} [Preorder D] [Nonempty D]
    (hD : AbramskyJung.Chapter2.IsContinuousDomain D)
    {I : Type u} [Fintype I] [DecidableEq I]
    (mu : VSub D) (O : I → ScottOpen D)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1)
    (T : Finset I) :
    letI : Fintype (JonesSupport hD mu O t ht0 ht1) := Fintype.ofFinite _
    letI : DecidableEq (JonesSupport hD mu O t ht0 ht1) := Classical.decEq _
    finiteAtomicRealMass
        (refinedAtomicPoint hD mu O t ht0 ht1)
        (refinedAtomicWeight hD mu O t ht0 ht1)
        (finiteUnion O T) =
      t * (signatureVector mu
        (refinedOpenFamily hD mu O t ht0 ht1)).mass
          (selectedTargetPatterns hD mu O t ht0 ht1 T) := by
  classical
  letI : Fintype (JonesSupport hD mu O t ht0 ht1) := Fintype.ofFinite _
  letI : DecidableEq (JonesSupport hD mu O t ht0 ht1) := Classical.decEq _
  unfold finiteAtomicRealMass SubprobabilityVector.mass
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  simp only [selectedTargetPatterns, Set.mem_setOf_eq]
  by_cases hvalid : IsChosenRefinedPattern hD mu O t ht0 ht1 q
  · have hmem := refinedAtomicPoint_mem_target_iff
      hD mu O t ht0 ht1 T q hvalid
    by_cases hhit : patternHits T (refinedOriginalPattern q)
    · have hpoint : refinedAtomicPoint hD mu O t ht0 ht1 q ∈
          finiteUnion O T := hmem.mpr hhit
      rw [if_pos hpoint]
      unfold refinedAtomicWeight
      rw [if_pos hvalid, if_pos ⟨hvalid, hhit⟩]
      rfl
    · have hpoint : refinedAtomicPoint hD mu O t ht0 ht1 q ∉
          finiteUnion O T := fun h => hhit (hmem.mp h)
      rw [if_neg hpoint, if_neg (fun h => hhit h.2), mul_zero]
  · have hrhs : ¬ (IsChosenRefinedPattern hD mu O t ht0 ht1 q ∧
        patternHits T (refinedOriginalPattern q)) := fun h => hvalid h.1
    rw [if_neg hrhs, mul_zero]
    by_cases hpoint : refinedAtomicPoint hD mu O t ht0 ht1 q ∈ finiteUnion O T
    · rw [if_pos hpoint]
      unfold refinedAtomicWeight
      rw [if_neg hvalid]
    · rw [if_neg hpoint]

/-- The selected target patterns are the disjoint union of the selected
patterns of all original cells which meet `T`. -/
theorem selectedTargetPatterns_mass_partition
    {D : Type u} [Preorder D]
    (hD : AbramskyJung.Chapter2.IsContinuousDomain D)
    {I : Type u} [Fintype I] [DecidableEq I]
    (mu : VSub D) (O : I → ScottOpen D)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1)
    (T : Finset I) :
    letI : Fintype (JonesSupport hD mu O t ht0 ht1) := Fintype.ofFinite _
    letI : DecidableEq (JonesSupport hD mu O t ht0 ht1) := Classical.decEq _
    (signatureVector mu
      (refinedOpenFamily hD mu O t ht0 ht1)).mass
        (selectedTargetPatterns hD mu O t ht0 ht1 T) =
      ∑ p : MembershipPattern I,
        if patternHits T p then
          (signatureVector mu
            (refinedOpenFamily hD mu O t ht0 ht1)).mass
              (selectedCellPatterns hD mu O t ht0 ht1 p)
        else 0 := by
  classical
  letI : Fintype (JonesSupport hD mu O t ht0 ht1) := Fintype.ofFinite _
  letI : DecidableEq (JonesSupport hD mu O t ht0 ht1) := Classical.decEq _
  let v := signatureVector mu (refinedOpenFamily hD mu O t ht0 ht1)
  unfold SubprobabilityVector.mass
  calc
    (∑ q, if q ∈ selectedTargetPatterns hD mu O t ht0 ht1 T
        then v q else 0) =
      ∑ q, ∑ p : MembershipPattern I,
        if patternHits T p ∧ refinedOriginalPattern q = p ∧
            IsChosenRefinedPattern hD mu O t ht0 ht1 q then v q else 0 := by
      apply Finset.sum_congr rfl
      intro q hq
      by_cases hv : IsChosenRefinedPattern hD mu O t ht0 ht1 q
      · by_cases hh : patternHits T (refinedOriginalPattern q)
        · rw [if_pos (show q ∈ selectedTargetPatterns
              hD mu O t ht0 ht1 T from ⟨hv, hh⟩)]
          rw [Finset.sum_eq_single (refinedOriginalPattern q)]
          · simp [hh, hv]
          · intro p hp hpne
            simp [hpne.symm]
          · simp
        · rw [if_neg (fun h => hh h.2)]
          symm
          apply Finset.sum_eq_zero
          intro p hp
          by_cases hpq : refinedOriginalPattern q = p
          · subst p
            simp [hh]
          · simp [hpq]
      · rw [if_neg (fun h => hv h.1)]
        simp [hv]
    _ = ∑ p : MembershipPattern I, ∑ q,
        if patternHits T p ∧ refinedOriginalPattern q = p ∧
            IsChosenRefinedPattern hD mu O t ht0 ht1 q then v q else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ p : MembershipPattern I,
        if patternHits T p then
          (signatureVector mu
            (refinedOpenFamily hD mu O t ht0 ht1)).mass
              (selectedCellPatterns hD mu O t ht0 ht1 p)
        else 0 := by
      apply Finset.sum_congr rfl
      intro p hp
      by_cases hh : patternHits T p
      · rw [if_pos hh]
        unfold SubprobabilityVector.mass selectedCellPatterns
        apply Finset.sum_congr rfl
        intro q hq
        simp [hh, v]
      · rw [if_neg hh]
        apply Finset.sum_eq_zero
        intro q hq
        simp [hh]

/-- Original signature coefficients over patterns meeting `T` sum to the
source valuation of the target union. -/
theorem originalPattern_mass_target
    {D : Type u} [Preorder D]
    {I : Type u} [Fintype I] [DecidableEq I]
    (mu : VSub D) (O : I → ScottOpen D) (T : Finset I) :
    (∑ p : MembershipPattern I,
      if patternHits T p then signatureVector mu O p else 0) =
      (mu (finiteUnion O T)).toReal := by
  have h := signatureVector_someTrueMass_real mu O T
  rw [← h]
  unfold SubprobabilityVector.mass patternHits someTrueUpper
  apply Finset.sum_congr rfl
  intro p hp
  simp

theorem selectedCell_scaled_le
    {D : Type u} [Preorder D]
    (hD : AbramskyJung.Chapter2.IsContinuousDomain D)
    {I : Type u} [Fintype I] [DecidableEq I]
    (mu : VSub D) (O : I → ScottOpen D)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1)
    (p : MembershipPattern I) :
    letI : Fintype (JonesSupport hD mu O t ht0 ht1) := Fintype.ofFinite _
    letI : DecidableEq (JonesSupport hD mu O t ht0 ht1) := Classical.decEq _
    t * signatureVector mu O p ≤
      (signatureVector mu
        (refinedOpenFamily hD mu O t ht0 ht1)).mass
          (selectedCellPatterns hD mu O t ht0 ht1 p) := by
  classical
  letI : Fintype (JonesSupport hD mu O t ht0 ht1) := Fintype.ofFinite _
  letI : DecidableEq (JonesSupport hD mu O t ht0 ht1) := Classical.decEq _
  by_cases hp : 0 < signatureVector mu O p
  · exact le_of_lt (by
      rw [selectedCellPatterns_mass]
      exact chosenCellCover_capture hD mu O t ht0 ht1 p hp)
  · have hz : signatureVector mu O p = 0 :=
      le_antisymm (not_lt.mp hp) ((signatureVector mu O).coeff_nonneg p)
    rw [hz, mul_zero]
    exact (signatureVector mu
      (refinedOpenFamily hD mu O t ht0 ht1)).mass_nonneg _

theorem selectedCell_scaled_lt
    {D : Type u} [Preorder D]
    (hD : AbramskyJung.Chapter2.IsContinuousDomain D)
    {I : Type u} [Fintype I] [DecidableEq I]
    (mu : VSub D) (O : I → ScottOpen D)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1)
    (p : MembershipPattern I) (hp : 0 < signatureVector mu O p) :
    letI : Fintype (JonesSupport hD mu O t ht0 ht1) := Fintype.ofFinite _
    letI : DecidableEq (JonesSupport hD mu O t ht0 ht1) := Classical.decEq _
    t * signatureVector mu O p <
      (signatureVector mu
        (refinedOpenFamily hD mu O t ht0 ht1)).mass
          (selectedCellPatterns hD mu O t ht0 ht1 p) := by
  classical
  letI : Fintype (JonesSupport hD mu O t ht0 ht1) := Fintype.ofFinite _
  letI : DecidableEq (JonesSupport hD mu O t ht0 ht1) := Classical.decEq _
  rw [selectedCellPatterns_mass]
  exact chosenCellCover_capture hD mu O t ht0 ht1 p hp

/-- The refined selected mass over a positive target union strictly exceeds
`t` times its original mass. -/
theorem refined_selected_target_gt
    {D : Type u} [Preorder D]
    (hD : AbramskyJung.Chapter2.IsContinuousDomain D)
    {I : Type u} [Fintype I] [DecidableEq I]
    (mu : VSub D) (O : I → ScottOpen D)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1)
    (T : Finset I) (hpos : 0 < (mu (finiteUnion O T)).toReal) :
    letI : Fintype (JonesSupport hD mu O t ht0 ht1) := Fintype.ofFinite _
    letI : DecidableEq (JonesSupport hD mu O t ht0 ht1) := Classical.decEq _
    t * (mu (finiteUnion O T)).toReal <
      (signatureVector mu
        (refinedOpenFamily hD mu O t ht0 ht1)).mass
          (selectedTargetPatterns hD mu O t ht0 ht1 T) := by
  classical
  letI : Fintype (JonesSupport hD mu O t ht0 ht1) := Fintype.ofFinite _
  letI : DecidableEq (JonesSupport hD mu O t ht0 ht1) := Classical.decEq _
  let f : MembershipPattern I → ℝ := fun p =>
    if patternHits T p then t * signatureVector mu O p else 0
  let g : MembershipPattern I → ℝ := fun p =>
    if patternHits T p then
      (signatureVector mu
        (refinedOpenFamily hD mu O t ht0 ht1)).mass
          (selectedCellPatterns hD mu O t ht0 ht1 p)
    else 0
  have hterm (p : MembershipPattern I) : f p ≤ g p := by
    by_cases hh : patternHits T p
    · simp only [f, g, hh, if_true]
      exact selectedCell_scaled_le hD mu O t ht0 ht1 p
    · simp [f, g, hh]
  have horigpos : 0 < ∑ p : MembershipPattern I,
      if patternHits T p then signatureVector mu O p else 0 := by
    rw [originalPattern_mass_target mu O T]
    exact hpos
  have hnonneg (p : MembershipPattern I) (hp : p ∈ Finset.univ) :
      0 ≤ (if patternHits T p then signatureVector mu O p else 0) := by
    split_ifs
    · exact (signatureVector mu O).coeff_nonneg p
    · exact le_rfl
  rcases (Finset.sum_pos_iff_of_nonneg hnonneg).mp horigpos with
    ⟨p0, hp0u, hp0pos⟩
  have hp0hit : patternHits T p0 := by
    by_contra hn
    simp [hn] at hp0pos
  have hp0coeff : 0 < signatureVector mu O p0 := by
    simpa [hp0hit] using hp0pos
  have hstrict : f p0 < g p0 := by
    simp only [f, g, hp0hit, if_true]
    exact selectedCell_scaled_lt hD mu O t ht0 ht1 p0 hp0coeff
  have hsum : (∑ p, f p) < ∑ p, g p :=
    Finset.sum_lt_sum (fun p hp => hterm p) ⟨p0, hp0u, hstrict⟩
  rw [selectedTargetPatterns_mass_partition]
  calc
    t * (mu (finiteUnion O T)).toReal = ∑ p, f p := by
      rw [← originalPattern_mass_target mu O T, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      simp only [f]
      by_cases hh : patternHits T p <;> simp [hh]
    _ < ∑ p, g p := hsum
    _ = ∑ p : MembershipPattern I,
        if patternHits T p then
          (signatureVector mu
            (refinedOpenFamily hD mu O t ht0 ht1)).mass
              (selectedCellPatterns hD mu O t ht0 ht1 p)
        else 0 := rfl

/-- Jones Lemma 5.3, corrected at zero mass: on every positive target union,
the constructed finite atomic valuation beats `r` times the source value. -/
theorem refinedAtomicVSub_target_gt
    {D : Type u} [Preorder D] [Nonempty D]
    (hD : AbramskyJung.Chapter2.IsContinuousDomain D)
    {I : Type u} [Fintype I] [DecidableEq I]
    (mu : VSub D) (O : I → ScottOpen D)
    (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (T : Finset I) (hpos : 0 < (mu (finiteUnion O T)).toReal) :
    r * (mu (finiteUnion O T)).toReal <
      (refinedAtomicVSub hD mu O (jonesMid r)
        (jonesMid_nonneg hr0) (jonesMid_lt_one hr1)
        (finiteUnion O T)).toReal := by
  classical
  let t := jonesMid r
  have ht0 : 0 ≤ t := jonesMid_nonneg hr0
  have ht1 : t < 1 := jonesMid_lt_one hr1
  letI : Fintype (JonesSupport hD mu O t ht0 ht1) := Fintype.ofFinite _
  letI : DecidableEq (JonesSupport hD mu O t ht0 ht1) := Classical.decEq _
  have hrefined := refined_selected_target_gt hD mu O t ht0 ht1 T hpos
  have hatomic :
      (refinedAtomicVSub hD mu O t ht0 ht1 (finiteUnion O T)).toReal =
        finiteAtomicRealMass
          (refinedAtomicPoint hD mu O t ht0 ht1)
          (refinedAtomicWeight hD mu O t ht0 ht1)
          (finiteUnion O T) := by
    exact finiteAtomicVSub_apply_toReal _ _ _ _ _
  rw [hatomic, refinedAtomicRealMass_target]
  have hscale : r * (mu (finiteUnion O T)).toReal <
      t * (t * (mu (finiteUnion O T)).toReal) := by
    have hsquare : r < t * t := lt_jonesMid_sq hr0 hr1
    nlinarith
  exact hscale.trans (mul_lt_mul_of_pos_left hrefined (jonesMid_pos hr0))

end ContinuousValuation
end FiniteValuationApproximable
