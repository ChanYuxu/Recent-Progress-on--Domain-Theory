import FiniteValuationApproximable.ContinuousValuation.Basic

/-!
# Probability valuations as a continuous retract of subprobability valuations

On a pointed dcpo, missing subprobability mass can be placed at the least
element.  In the Scott-open presentation this has the especially simple form

`N(μ)(U) = 1` if `U` is the whole carrier, and `N(μ)(U) = μ(U)` otherwise.

The least element is absent from every proper Scott open, which is the key to
strictness, modularity, and preservation of directed suprema.  This module
proves both maps Scott-continuous and packages them as the section--retraction
used in source theorem `thm:global-Vone` of `main (17).tex`.
-/

set_option autoImplicit false
set_option linter.unnecessarySimpa false

universe u

namespace FiniteValuationApproximable
namespace ContinuousValuation

open Set
open AbramskyJung.Chapter2
open scoped ENNReal

namespace ScottOpen

variable {D : Type u} [Preorder D]

/-- An upper Scott open containing a least element is the whole carrier. -/
theorem eq_univ_of_least_mem {b : D} (hb : IsLeast b)
    {U : ScottOpen D} (hbU : b ∈ U) : U = univ := by
  apply ScottOpen.ext
  apply Set.eq_univ_of_forall
  intro x
  exact U.upper (hb x) hbU

/-- A proper Scott open cannot contain a least element. -/
theorem least_not_mem_of_ne_univ {b : D} (hb : IsLeast b)
    {U : ScottOpen D} (hU : U ≠ univ) : b ∉ U := by
  intro hbU
  exact hU (eq_univ_of_least_mem hb hbU)

end ScottOpen

section Normalization

variable {D : Type u} [Preorder D]

/-- The value of the probability normalization on a Scott open. -/
noncomputable def normalizeValue (μ : VSub D) (U : ScottOpen D) : ℝ≥0∞ := by
  classical
  exact if U = ScottOpen.univ then 1 else μ U

@[simp]
theorem normalizeValue_univ (μ : VSub D) :
    normalizeValue μ ScottOpen.univ = 1 := by
  simp [normalizeValue]

theorem normalizeValue_of_ne_univ (μ : VSub D) {U : ScottOpen D}
    (hU : U ≠ ScottOpen.univ) : normalizeValue μ U = μ U := by
  simp [normalizeValue, hU]

theorem normalizeValue_le_one (μ : VSub D) (U : ScottOpen D) :
    normalizeValue μ U ≤ 1 := by
  by_cases hU : U = ScottOpen.univ
  · simp [hU]
  · rw [normalizeValue_of_ne_univ μ hU]
    exact μ.value_le_one U

theorem normalizeValue_monotone (μ : VSub D) :
    Monotone (normalizeValue μ) := by
  intro U V hUV
  by_cases hV : V = ScottOpen.univ
  · rw [hV, normalizeValue_univ]
    exact normalizeValue_le_one μ U
  · have hU : U ≠ ScottOpen.univ := by
      intro hU
      apply hV
      apply le_antisymm
      · intro x hx
        trivial
      · simpa [hU] using hUV
    rw [normalizeValue_of_ne_univ μ hU,
      normalizeValue_of_ne_univ μ hV]
    exact μ.monotone hUV

/-- For a pointed carrier, normalization is Scott-continuous as a function of
the Scott-open argument. -/
theorem normalizeValue_scottContinuous
    (hD : AbramskyJung.Chapter3.HasLeastElement D) (μ : VSub D) :
    AbramskyJung.Chapter2.ScottContinuous (normalizeValue μ) := by
  constructor
  · exact normalizeValue_monotone μ
  · intro A S hA hS
    by_cases hSuniv : S = ScottOpen.univ
    · subst S
      rcases hD with ⟨b, hb⟩
      have hUnion : ScottOpen.sUnion A = (ScottOpen.univ : ScottOpen D) :=
        IsSup.unique (ScottOpen.sUnion_isSup A) hS
      have hbUnion : b ∈ ScottOpen.sUnion A := by
        rw [hUnion]
        exact ScottOpen.mem_univ b
      rcases ScottOpen.mem_sUnion_iff.mp hbUnion with ⟨U, hUA, hbU⟩
      have hUuniv : U = (ScottOpen.univ : ScottOpen D) :=
        ScottOpen.eq_univ_of_least_mem hb hbU
      constructor
      · rintro _ ⟨V, hVA, rfl⟩
        simpa using normalizeValue_le_one μ V
      · intro y hy
        have hOne : (1 : ℝ≥0∞) ≤ y := by
          simpa [hUuniv] using
            hy ⟨U, hUA, rfl⟩
        simpa using hOne
    · have hProper : ∀ U ∈ A, U ≠ (ScottOpen.univ : ScottOpen D) := by
        intro U hUA hU
        apply hSuniv
        apply le_antisymm
        · intro x hx
          trivial
        · simpa [hU] using hS.1 hUA
      have hμSup :
          IsSup ((fun U : ScottOpen D => μ U) '' A) (μ S) :=
        μ.1.continuous.maps_isSup hA hS
      constructor
      · rintro _ ⟨U, hUA, rfl⟩
        rw [normalizeValue_of_ne_univ μ (hProper U hUA),
          normalizeValue_of_ne_univ μ hSuniv]
        exact hμSup.1 ⟨U, hUA, rfl⟩
      · intro y hy
        rw [normalizeValue_of_ne_univ μ hSuniv]
        apply hμSup.2 y
        rintro _ ⟨U, hUA, rfl⟩
        have hbound := hy
          ⟨U, hUA, rfl⟩
        simpa [normalizeValue_of_ne_univ μ (hProper U hUA)] using hbound

/-- The underlying continuous valuation obtained by placing all missing mass
at the least element. -/
noncomputable def normalizeValuation
    (hD : AbramskyJung.Chapter3.HasLeastElement D) (μ : VSub D) :
    Valuation D where
  toFun := normalizeValue μ
  continuous := normalizeValue_scottContinuous hD μ
  strict := by
    rcases hD with ⟨b, hb⟩
    have hne : (ScottOpen.empty : ScottOpen D) ≠ ScottOpen.univ := by
      intro h
      have hbEmpty : b ∈ (ScottOpen.empty : ScottOpen D) := by
        rw [h]
        exact ScottOpen.mem_univ b
      exact ScottOpen.not_mem_empty b hbEmpty
    rw [normalizeValue_of_ne_univ μ hne]
    exact μ.1.strict
  modular := by
    intro U V
    classical
    by_cases hU : U = ScottOpen.univ
    · subst U
      have hUnion : ScottOpen.union ScottOpen.univ V =
          (ScottOpen.univ : ScottOpen D) := by
        apply ScottOpen.ext
        ext x
        simp
      have hInter : ScottOpen.inter ScottOpen.univ V = V := by
        apply ScottOpen.ext
        ext x
        simp
      simp [hUnion, hInter]
    · by_cases hV : V = ScottOpen.univ
      · subst V
        have hUnion : ScottOpen.union U ScottOpen.univ =
            (ScottOpen.univ : ScottOpen D) := by
          apply ScottOpen.ext
          ext x
          simp
        have hInter : ScottOpen.inter U ScottOpen.univ = U := by
          apply ScottOpen.ext
          ext x
          simp
        simp [hUnion, hInter, add_comm]
      · rcases hD with ⟨b, hb⟩
        have hbU : b ∉ U := ScottOpen.least_not_mem_of_ne_univ hb hU
        have hbV : b ∉ V := ScottOpen.least_not_mem_of_ne_univ hb hV
        have hUnion : ScottOpen.union U V ≠
            (ScottOpen.univ : ScottOpen D) := by
          intro h
          have hbUnion : b ∈ ScottOpen.union U V := by
            rw [h]
            exact ScottOpen.mem_univ b
          rcases (ScottOpen.mem_union b U V).mp hbUnion with hbU' | hbV'
          · exact hbU hbU'
          · exact hbV hbV'
        have hInter : ScottOpen.inter U V ≠
            (ScottOpen.univ : ScottOpen D) := by
          intro h
          have hbInter : b ∈ ScottOpen.inter U V := by
            rw [h]
            exact ScottOpen.mem_univ b
          exact hbU (ScottOpen.mem_inter b U V |>.mp hbInter).1
        simpa [normalizeValue_of_ne_univ μ hU,
          normalizeValue_of_ne_univ μ hV,
          normalizeValue_of_ne_univ μ hUnion,
          normalizeValue_of_ne_univ μ hInter] using μ.1.modular U V

/-- Normalize a subprobability valuation by placing its missing mass at the
least point. -/
noncomputable def normalize
    (hD : AbramskyJung.Chapter3.HasLeastElement D) (μ : VSub D) : VOne D :=
  ⟨normalizeValuation hD μ, normalizeValue_univ μ⟩

@[simp]
theorem normalize_apply_univ
    (hD : AbramskyJung.Chapter3.HasLeastElement D) (μ : VSub D) :
    normalize hD μ ScottOpen.univ = 1 :=
  normalizeValue_univ μ

theorem normalize_apply_of_ne_univ
    (hD : AbramskyJung.Chapter3.HasLeastElement D) (μ : VSub D)
    {U : ScottOpen D} (hU : U ≠ ScottOpen.univ) :
    normalize hD μ U = μ U :=
  normalizeValue_of_ne_univ μ hU

/-- The canonical inclusion of probabilities into subprobabilities is
monotone. -/
theorem vOneInclusion_monotone :
    Monotone (VOne.toVSub : VOne D → VSub D) := by
  intro μ ν hμν U
  exact hμν U

/-- The canonical inclusion of probabilities into subprobabilities preserves
all directed suprema. -/
theorem vOneInclusion_scottContinuous :
    AbramskyJung.Chapter2.ScottContinuous
      (VOne.toVSub : VOne D → VSub D) := by
  constructor
  · exact vOneInclusion_monotone
  · intro A s hA hs
    constructor
    · rintro _ ⟨μ, hμA, rfl⟩
      exact hs.1 hμA
    · intro τ hτ
      rcases hA.1 with ⟨μ₀, hμ₀A⟩
      have hOneLe : (1 : ℝ≥0∞) ≤ τ ScottOpen.univ := by
        have hbound := hτ
          ⟨μ₀, hμ₀A, rfl⟩
        simpa [VOne.toVSub, μ₀.2] using hbound ScottOpen.univ
      have hτOne : τ ScottOpen.univ = 1 :=
        le_antisymm τ.2 hOneLe
      let τ₁ : VOne D := ⟨τ.1, hτOne⟩
      have hsτ : s ≤ τ₁ := hs.2 τ₁ (by
        intro μ hμA U
        exact hτ ⟨μ, hμA, rfl⟩ U)
      intro U
      exact hsτ U

/-- Normalization is monotone in the valuation argument. -/
theorem normalize_monotone
    (hD : AbramskyJung.Chapter3.HasLeastElement D) :
    Monotone (normalize hD : VSub D → VOne D) := by
  intro μ ν hμν U
  by_cases hU : U = ScottOpen.univ
  · subst U
    simp
  · rw [normalize_apply_of_ne_univ hD μ hU,
      normalize_apply_of_ne_univ hD ν hU]
    exact hμν U

/-- Normalization preserves every directed supremum of subprobability
valuations. -/
theorem normalize_scottContinuous
    (hD : AbramskyJung.Chapter3.HasLeastElement D) :
    AbramskyJung.Chapter2.ScottContinuous
      (normalize hD : VSub D → VOne D) := by
  constructor
  · exact normalize_monotone hD
  · intro A s hA hs
    constructor
    · rintro _ ⟨μ, hμA, rfl⟩
      exact normalize_monotone hD (hs.1 hμA)
    · intro τ hτ U
      by_cases hU : U = ScottOpen.univ
      · subst U
        simpa [τ.2]
      · rw [normalize_apply_of_ne_univ hD s hU]
        exact (VSub.eval_isSup hA hs U).2 (τ U) (by
          rintro _ ⟨μ, hμA, rfl⟩
          have hbound := hτ
            ⟨μ, hμA, rfl⟩ U
          simpa [normalize_apply_of_ne_univ hD μ hU] using hbound)

/-- Normalizing an already normalized valuation is the identity. -/
@[simp]
theorem normalize_vOneInclusion
    (hD : AbramskyJung.Chapter3.HasLeastElement D) (μ : VOne D) :
    normalize hD (VOne.toVSub μ) = μ := by
  apply VOne.ext
  intro U
  by_cases hU : U = ScottOpen.univ
  · subst U
    simpa using μ.2.symm
  · rw [normalize_apply_of_ne_univ hD (VOne.toVSub μ) hU]
    rfl

/-- Probability valuations form a continuous retract of subprobability
valuations on every pointed carrier. -/
noncomputable def vOneVSubContinuousSectionRetractionPair
    (hD : AbramskyJung.Chapter3.HasLeastElement D) :
    AbramskyJung.Chapter3.ContinuousSectionRetractionPair (VOne D) (VSub D) where
  s := VOne.toVSub
  r := normalize hD
  monotone_s := vOneInclusion_monotone
  monotone_r := normalize_monotone hD
  retract := normalize_vOneInclusion hD
  continuous_s := vOneInclusion_scottContinuous
  continuous_r := normalize_scottContinuous hD

end Normalization

end ContinuousValuation
end FiniteValuationApproximable
