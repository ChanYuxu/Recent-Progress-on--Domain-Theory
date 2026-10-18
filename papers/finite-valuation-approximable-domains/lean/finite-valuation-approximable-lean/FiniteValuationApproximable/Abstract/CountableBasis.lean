import FiniteValuationApproximable.Abstract.Saturation

/-!
# Countable bases from finitely separated approximations

This file formalizes source item `prop:countable-basis` (source lines
1574--1599 of `main17-4b2e65f0f963`) in two layers.  First, a sequential FS
approximate identity on a continuous domain is shown to generate a countable
basis by the exact set

`B = { f_j(m) | j,n : ℕ, m ∈ M_n }`,

where `M_n` is a finite separator for `f_n`.  Second, the result is combined
with the conditional saturation theorem.  Consequently the only remaining
premise in the FVA-facing statement is the openly stated finite-stage erosion
theorem `FiniteStagesHaveFSApproximateIdentities`.
-/

set_option autoImplicit false
set_option linter.unnecessarySimpa false

universe u w

namespace FiniteValuationApproximable

open AbstractApproximation
open Set
open AbramskyJung.Chapter2

section BasisCriterion

variable {D : Type u} [Preorder D]

/-- The elementary criterion used verbatim in the source proof: a subset is a
basis if it contains a way-below interpolant above every `y ≪ x`. -/
theorem isBasis_of_wayBelow_intermediate
    (hD : AbramskyJung.Chapter2.IsContinuousDomain D) {C : Set D}
    (hC : ∀ {x y : D}, y ≪ x →
      ∃ c ∈ C, y ≤ c ∧ c ≪ x) :
    IsBasis C := by
  intro x
  constructor
  · constructor
    · rcases (continuous_wayBelowLower_directed hD x).1 with ⟨y, hyx⟩
      rcases hC hyx with ⟨c, hcC, _hyc, hcx⟩
      exact ⟨c, hcC, hcx⟩
    · intro c₁ hc₁ c₂ hc₂
      let M : Set D := {c₁, c₂}
      have hMfinite : M.Finite :=
        (Set.finite_singleton c₂).insert c₁
      have hMway : ∀ m ∈ M, m ≪ x := by
        intro m hm
        rcases hm with rfl | hm
        · exact hc₁.2
        · have hm₂ : m = c₂ := by simpa [M] using hm
          simpa [hm₂] using hc₂.2
      rcases lemma_2_2_15_interpolation hD hMfinite hMway with
        ⟨y, hMy, hyx⟩
      rcases hC hyx with ⟨c, hcC, hyc, hcx⟩
      refine ⟨c, ⟨hcC, hcx⟩, ?_, ?_⟩
      · exact le_trans (prop_2_2_2_1 (hMy c₁ (by simp [M]))) hyc
      · exact le_trans (prop_2_2_2_1 (hMy c₂ (by simp [M]))) hyc
  · constructor
    · intro c hc
      exact prop_2_2_2_1 hc.2
    · intro z hz
      apply (continuous_wayBelowLower_isSup hD x).2 z
      intro y hyx
      rcases hC hyx with ⟨c, hcC, hyc, hcx⟩
      exact le_trans hyc (hz ⟨hcC, hcx⟩)

end BasisCriterion

section FSCountableBasis

variable {D : Type u} [Preorder D]

/-- The exact countable set generated from chosen finite separators of an FS
approximate identity. -/
noncomputable def separatorBasis (A : FSApproximateIdentity D) : Set D :=
  let M : Nat → Set D := fun n =>
    Classical.choose (A.finitelySeparated n)
  ⋃ j : Nat, ⋃ n : Nat, A.map j '' M n

theorem separatorBasis_countable (A : FSApproximateIdentity D) :
    (separatorBasis A).Countable := by
  let M : Nat → Set D := fun n =>
    Classical.choose (A.finitelySeparated n)
  have hMfinite : ∀ n : Nat, (M n).Finite := by
    intro n
    exact (Classical.choose_spec (A.finitelySeparated n)).1
  have hcount :
      (⋃ j : Nat, ⋃ n : Nat, A.map j '' M n).Countable :=
    Set.countable_iUnion fun j : Nat =>
      Set.countable_iUnion fun n : Nat =>
        Set.Countable.image (hMfinite n).countable (A.map j)
  simpa only [separatorBasis, M] using hcount

/-- Source item `prop:countable-basis`, stated at the exact FS-approximation
layer used by its proof. -/
theorem FSApproximateIdentity.separatorBasis_isBasis
    (A : FSApproximateIdentity D)
    (hD : AbramskyJung.Chapter2.IsContinuousDomain D) :
    IsBasis (separatorBasis A) := by
  let M : Nat → Set D := fun n =>
    Classical.choose (A.finitelySeparated n)
  have hMsep : ∀ n : Nat, IsFiniteSeparator (M n) (A.map n) := by
    intro n
    exact Classical.choose_spec (A.finitelySeparated n)
  apply isBasis_of_wayBelow_intermediate hD
  intro x y hyx
  rcases wayBelow_interpolation hD hyx with ⟨z, hyz, hzx⟩
  rcases hzx (A.range_directed x) (A.pointwise_sup x) le_rfl with
    ⟨_fx, ⟨n, rfl⟩, hzfn⟩
  rcases (hMsep n).2 x with ⟨m, hmM, hfnm, hmx⟩
  have hym : y ≪ m :=
    prop_2_2_2_2 le_rfl hyz (le_trans hzfn hfnm)
  rcases hym (A.range_directed m) (A.pointwise_sup m) le_rfl with
    ⟨_fm, ⟨j, rfl⟩, hyfjm⟩
  refine ⟨A.map j m, ?_, hyfjm, ?_⟩
  · change A.map j m ∈
      ⋃ j : Nat, ⋃ n : Nat, A.map j '' M n
    exact Set.mem_iUnion.2 ⟨j, Set.mem_iUnion.2
      ⟨n, ⟨m, hmM, rfl⟩⟩⟩
  · exact prop_2_2_2_2 le_rfl
      (IsFinitelySeparated.wayBelow
        (A.map j).continuous (A.finitelySeparated j) m) hmx

/-- A sequential FS approximate identity on a continuous dcpo supplies the
countable-basis component of omega continuity. -/
theorem FSApproximateIdentity.isOmegaContinuousDomain
    (A : FSApproximateIdentity D)
    (hD : AbramskyJung.Chapter2.IsContinuousDomain D) :
    IsOmegaContinuousDomain D := by
  refine ⟨separatorBasis A, separatorBasis_countable A, ?_⟩
  exact basis_to_raw
    (FiniteValuationApproximable.FSApproximateIdentity.separatorBasis_isBasis
      A hD)

end FSCountableBasis

section FVACountableBasis

variable {D : Type u} [PartialOrder D]

/-- Exact conditional source-facing form of `prop:countable-basis`: after the
finite-stage erosion theorem is supplied, every FVA object is omega
continuous, hence countably based. -/
theorem IsFVA.isOmegaContinuousDcpo
    (hStages : FiniteStagesHaveFSApproximateIdentities.{w})
    (hD : IsFVA.{u, w} D) :
    AbramskyJung.Chapter2.IsOmegaContinuousDcpo D := by
  rcases hD.saturated hStages with ⟨A⟩
  exact ⟨hD.1.1,
    FiniteValuationApproximable.FSApproximateIdentity.isOmegaContinuousDomain
      A.toFSApproximateIdentity hD.1.hasBasis⟩

end FVACountableBasis

end FiniteValuationApproximable
