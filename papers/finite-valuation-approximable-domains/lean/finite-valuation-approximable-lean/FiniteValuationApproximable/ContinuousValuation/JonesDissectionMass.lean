import FiniteValuationApproximable.ContinuousValuation.JonesDissection

/-!
# Mass identities for Jones dissections

The selected refined patterns over one original Boolean cell form the
difference of two upper sets.  Their reconstructed atomic mass is therefore
the valuation mass captured by the chosen finite crescent cover.  These
finite identities replace all uses of a measure extension in Jones's proof.
-/

set_option autoImplicit false
set_option linter.unnecessarySimpa false

universe u

namespace FiniteValuationApproximable
namespace ContinuousValuation

open Set
open AbramskyJung.Chapter2
open scoped ENNReal BigOperators

/-- Refined upper set requiring membership above an original pattern `p` and
membership in one of `p`'s selected cover opens. -/
def cellCoverUpper
    {D : Type u} [Preorder D]
    (hD : AbramskyJung.Chapter2.IsContinuousDomain D)
    {I : Type u} [Fintype I] [DecidableEq I]
    (mu : VSub D) (O : I → ScottOpen D)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1)
    (p : MembershipPattern I) :
    UpperSet (MembershipPattern
      (I ⊕ JonesSupport hD mu O t ht0 ht1)) where
  carrier := {q | p ≤ refinedOriginalPattern q ∧
    ∃ j : JonesSupport hD mu O t ht0 ht1,
      j.1 = p ∧ q (Sum.inr j) = true}
  upper' := by
    intro q q' hqq' hq
    refine ⟨?_, ?_⟩
    · intro i
      exact (hq.1 i).trans (hqq' (Sum.inl i))
    · rcases hq.2 with ⟨j, hjp, hjq⟩
      exact ⟨j, hjp, Bool.eq_true_of_true_le (hjq ▸ hqq' (Sum.inr j))⟩

/-- The punctured part of `cellCoverUpper`: the original pattern has moved
strictly above `p`. -/
def cellCoverPuncturedUpper
    {D : Type u} [Preorder D]
    (hD : AbramskyJung.Chapter2.IsContinuousDomain D)
    {I : Type u} [Fintype I] [DecidableEq I]
    (mu : VSub D) (O : I → ScottOpen D)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1)
    (p : MembershipPattern I) :
    UpperSet (MembershipPattern
      (I ⊕ JonesSupport hD mu O t ht0 ht1)) where
  carrier := {q | q ∈ cellCoverUpper hD mu O t ht0 ht1 p ∧
    refinedOriginalPattern q ≠ p}
  upper' := by
    intro q q' hqq' hq
    have hupper := (cellCoverUpper hD mu O t ht0 ht1 p).upper' hqq' hq.1
    refine ⟨hupper, ?_⟩
    intro heq
    have hforward : refinedOriginalPattern q ≤ refinedOriginalPattern q' :=
      fun i => hqq' (Sum.inl i)
    have hback : refinedOriginalPattern q' ≤ refinedOriginalPattern q := by
      rw [heq]
      exact hq.1.1
    have hqp : refinedOriginalPattern q = p := by
      apply le_antisymm
      · simpa [heq] using hforward
      · exact hq.1.1
    exact hq.2 hqp

/-- Selected refined patterns belonging to one exact original cell. -/
def selectedCellPatterns
    {D : Type u} [Preorder D]
    (hD : AbramskyJung.Chapter2.IsContinuousDomain D)
    {I : Type u} [Fintype I] [DecidableEq I]
    (mu : VSub D) (O : I → ScottOpen D)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1)
    (p : MembershipPattern I) :
    Set (MembershipPattern
      (I ⊕ JonesSupport hD mu O t ht0 ht1)) :=
  {q | refinedOriginalPattern q = p ∧
    IsChosenRefinedPattern hD mu O t ht0 ht1 q}

theorem selectedCellPatterns_eq_diff
    {D : Type u} [Preorder D]
    (hD : AbramskyJung.Chapter2.IsContinuousDomain D)
    {I : Type u} [Fintype I] [DecidableEq I]
    (mu : VSub D) (O : I → ScottOpen D)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1)
    (p : MembershipPattern I) :
    selectedCellPatterns hD mu O t ht0 ht1 p =
      (cellCoverUpper hD mu O t ht0 ht1 p : Set _) \
        (cellCoverPuncturedUpper hD mu O t ht0 ht1 p : Set _) := by
  ext q
  change (refinedOriginalPattern q = p ∧
      ∃ j, j.1 = refinedOriginalPattern q ∧ q (Sum.inr j) = true) ↔
    ((p ≤ refinedOriginalPattern q ∧
        ∃ j, j.1 = p ∧ q (Sum.inr j) = true) ∧
      ¬ ((p ≤ refinedOriginalPattern q ∧
        ∃ j, j.1 = p ∧ q (Sum.inr j) = true) ∧
        refinedOriginalPattern q ≠ p))
  constructor
  · rintro ⟨hqp, j, hjq, hjtrue⟩
    subst hqp
    exact ⟨⟨le_rfl, ⟨j, hjq, hjtrue⟩⟩, by simp⟩
  · rintro ⟨⟨hpq, j, hjp, hjtrue⟩, hnot⟩
    have heq : refinedOriginalPattern q = p := by
      by_contra hne
      exact hnot ⟨⟨hpq, ⟨j, hjp, hjtrue⟩⟩, hne⟩
    exact ⟨heq, ⟨j, hjp.trans heq.symm, hjtrue⟩⟩

/-- Finite atomic mass of a set difference. -/
theorem subprobabilityVector_mass_diff
    {Q : Type u} [Fintype Q]
    (v : SubprobabilityVector Q) {A B : Set Q} (hBA : B ⊆ A) :
    v.mass (A \ B) = v.mass A - v.mass B := by
  classical
  have hadd : v.mass A = v.mass (A \ B) + v.mass B := by
    unfold SubprobabilityVector.mass
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro q hq
    by_cases hqB : q ∈ B
    · have hqA : q ∈ A := hBA hqB
      simp [hqA, hqB]
    · by_cases hqA : q ∈ A
      · simp [hqA, hqB]
      · simp [hqA, hqB]
  have hnonneg := v.mass_nonneg (A \ B)
  linarith

@[simp]
theorem refinedOriginalPattern_signature
    {D : Type u} [Preorder D]
    (hD : AbramskyJung.Chapter2.IsContinuousDomain D)
    {I : Type u} [Fintype I] [DecidableEq I]
    (mu : VSub D) (O : I → ScottOpen D)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1) (x : D) :
    refinedOriginalPattern
      (membershipSignature (refinedOpenFamily hD mu O t ht0 ht1) x) =
      membershipSignature O x := by
  classical
  funext i
  simp [refinedOriginalPattern, membershipSignature, refinedOpenFamily]

/-- Preimage of the cell-cover upper set is the finite union of the selected
way-above opens. -/
theorem cellCoverUpper_preimage
    {D : Type u} [Preorder D]
    (hD : AbramskyJung.Chapter2.IsContinuousDomain D)
    {I : Type u} [Fintype I] [DecidableEq I]
    (mu : VSub D) (O : I → ScottOpen D)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1)
    (p : MembershipPattern I) :
    letI : Fintype (JonesSupport hD mu O t ht0 ht1) := Fintype.ofFinite _
    letI : DecidableEq (JonesSupport hD mu O t ht0 ht1) := Classical.decEq _
    ScottOpen.preimage
        (membershipSignatureMap (refinedOpenFamily hD mu O t ht0 ht1))
        (membershipSignatureMap
          (refinedOpenFamily hD mu O t ht0 ht1)).continuous
        (upperSetToScottOpen (cellCoverUpper hD mu O t ht0 ht1 p)) =
      finiteUnion (wayAboveOpen hD)
        (chosenCellCover hD mu O t ht0 ht1 p) := by
  classical
  letI : Fintype (JonesSupport hD mu O t ht0 ht1) := Fintype.ofFinite _
  letI : DecidableEq (JonesSupport hD mu O t ht0 ht1) := Classical.decEq _
  apply ScottOpen.ext
  ext x
  change ((p ≤ refinedOriginalPattern
      (membershipSignature (refinedOpenFamily hD mu O t ht0 ht1) x)) ∧
      ∃ j, j.1 = p ∧
        membershipSignature (refinedOpenFamily hD mu O t ht0 ht1) x
          (Sum.inr j) = true) ↔
    x ∈ finiteUnion (wayAboveOpen hD)
      (chosenCellCover hD mu O t ht0 ht1 p)
  rw [mem_finiteUnion_iff]
  constructor
  · rintro ⟨hp, j, hjp, hjx⟩
    have hxopen : x ∈ jonesSupportOpen hD mu O t ht0 ht1 j := by
      exact (membershipSignature_apply_eq_true
        (refinedOpenFamily hD mu O t ht0 ht1) x (Sum.inr j)).mp hjx
    subst hjp
    exact ⟨j.2.1, j.2.2, hxopen⟩
  · rintro ⟨b, hb, hbx⟩
    let j : JonesSupport hD mu O t ht0 ht1 := ⟨p, ⟨b, hb⟩⟩
    have hpattern := chosenCellCover_mem_pattern hD mu O t ht0 ht1 p hb
    have hpmono : p ≤ membershipSignature O x := by
      rw [← hpattern]
      exact membershipSignature_mono O (prop_2_2_2_1 hbx)
    refine ⟨?_, j, rfl, ?_⟩
    · simpa using hpmono
    · apply (membershipSignature_apply_eq_true
          (refinedOpenFamily hD mu O t ht0 ht1) x (Sum.inr j)).mpr
      exact hbx

/-- Preimage of the punctured cell-cover upper set is the intersection of
the finite cover with the punctured original cell. -/
theorem cellCoverPuncturedUpper_preimage
    {D : Type u} [Preorder D]
    (hD : AbramskyJung.Chapter2.IsContinuousDomain D)
    {I : Type u} [Fintype I] [DecidableEq I]
    (mu : VSub D) (O : I → ScottOpen D)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1)
    (p : MembershipPattern I) :
    letI : Fintype (JonesSupport hD mu O t ht0 ht1) := Fintype.ofFinite _
    letI : DecidableEq (JonesSupport hD mu O t ht0 ht1) := Classical.decEq _
    ScottOpen.preimage
        (membershipSignatureMap (refinedOpenFamily hD mu O t ht0 ht1))
        (membershipSignatureMap
          (refinedOpenFamily hD mu O t ht0 ht1)).continuous
        (upperSetToScottOpen
          (cellCoverPuncturedUpper hD mu O t ht0 ht1 p)) =
      ScottOpen.inter
        (finiteUnion (wayAboveOpen hD)
          (chosenCellCover hD mu O t ht0 ht1 p))
        (signatureCellPunctured O p) := by
  classical
  letI : Fintype (JonesSupport hD mu O t ht0 ht1) := Fintype.ofFinite _
  letI : DecidableEq (JonesSupport hD mu O t ht0 ht1) := Classical.decEq _
  apply ScottOpen.ext
  ext x
  change ((x ∈ ScottOpen.preimage
      (membershipSignatureMap (refinedOpenFamily hD mu O t ht0 ht1))
      (membershipSignatureMap
        (refinedOpenFamily hD mu O t ht0 ht1)).continuous
      (upperSetToScottOpen (cellCoverUpper hD mu O t ht0 ht1 p))) ∧
      refinedOriginalPattern
        (membershipSignature (refinedOpenFamily hD mu O t ht0 ht1) x) ≠ p) ↔
    (x ∈ finiteUnion (wayAboveOpen hD)
      (chosenCellCover hD mu O t ht0 ht1 p) ∧
      x ∈ signatureCellPunctured O p)
  rw [cellCoverUpper_preimage hD mu O t ht0 ht1 p,
    refinedOriginalPattern_signature]
  constructor
  · rintro ⟨hxC, hne⟩
    refine ⟨hxC, ?_⟩
    change p ≤ membershipSignature O x ∧ membershipSignature O x ≠ p
    refine ⟨?_, hne⟩
    rcases (mem_finiteUnion_iff (wayAboveOpen hD)
      (chosenCellCover hD mu O t ht0 ht1 p) x).mp hxC with
      ⟨b, hb, hbx⟩
    have hpattern := chosenCellCover_mem_pattern
      hD mu O t ht0 ht1 p hb
    rw [← hpattern]
    exact membershipSignature_mono O (prop_2_2_2_1 hbx)
  · rintro ⟨hxC, hp, hne⟩
    exact ⟨hxC, hne⟩

/-- Exact raw mass captured from one original Boolean cell. -/
theorem selectedCellPatterns_mass
    {D : Type u} [Preorder D]
    (hD : AbramskyJung.Chapter2.IsContinuousDomain D)
    {I : Type u} [Fintype I] [DecidableEq I]
    (mu : VSub D) (O : I → ScottOpen D)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1)
    (p : MembershipPattern I) :
    letI : Fintype (JonesSupport hD mu O t ht0 ht1) := Fintype.ofFinite _
    letI : DecidableEq (JonesSupport hD mu O t ht0 ht1) := Classical.decEq _
    (signatureVector mu (refinedOpenFamily hD mu O t ht0 ht1)).mass
        (selectedCellPatterns hD mu O t ht0 ht1 p) =
      (mu (crescentCoverOpen hD (signatureCellPunctured O p)
        (chosenCellCover hD mu O t ht0 ht1 p))).toReal -
        (mu (signatureCellPunctured O p)).toReal := by
  classical
  letI : Fintype (JonesSupport hD mu O t ht0 ht1) := Fintype.ofFinite _
  letI : DecidableEq (JonesSupport hD mu O t ht0 ht1) := Classical.decEq _
  let v := signatureVector mu (refinedOpenFamily hD mu O t ht0 ht1)
  let U := cellCoverUpper hD mu O t ht0 ht1 p
  let L := cellCoverPuncturedUpper hD mu O t ht0 ht1 p
  have hLU : (L : Set (MembershipPattern
      (I ⊕ JonesSupport hD mu O t ht0 ht1))) ⊆
      (U : Set (MembershipPattern
        (I ⊕ JonesSupport hD mu O t ht0 ht1))) := by
    intro q hq
    exact hq.1
  rw [selectedCellPatterns_eq_diff,
    subprobabilityVector_mass_diff v hLU,
    signatureVector_upperMass_real mu
      (refinedOpenFamily hD mu O t ht0 ht1) U,
    signatureVector_upperMass_real mu
      (refinedOpenFamily hD mu O t ht0 ht1) L,
    cellCoverUpper_preimage,
    cellCoverPuncturedUpper_preimage]
  let C : ScottOpen D := finiteUnion (wayAboveOpen hD)
    (chosenCellCover hD mu O t ht0 ht1 p)
  let B : ScottOpen D := signatureCellPunctured O p
  have hmod := mu.1.modular C B
  have hCfin : mu C ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (mu.value_le_one C)
  have hBfin : mu B ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (mu.value_le_one B)
  have hUfin : mu (ScottOpen.union C B) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top
      (mu.value_le_one (ScottOpen.union C B))
  have hIfin : mu (ScottOpen.inter C B) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top
      (mu.value_le_one (ScottOpen.inter C B))
  have hreal := congrArg ENNReal.toReal hmod
  rw [ENNReal.toReal_add hCfin hBfin,
    ENNReal.toReal_add hUfin hIfin] at hreal
  change (mu C).toReal - (mu (ScottOpen.inter C B)).toReal =
    (mu (ScottOpen.union B C)).toReal - (mu B).toReal
  rw [show ScottOpen.union B C = ScottOpen.union C B by
    apply ScottOpen.ext; ext x; simp [or_comm]]
  linarith

end ContinuousValuation
end FiniteValuationApproximable
