import Practice.DomainTheory.Order.DCPO.Basic
import Mathlib.Order.CompleteLatticeIntervals
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Archimedean.Basic

/-!
# Regularized sections and the dyadic-thread criterion

This file formalizes `prop:regularize-section` and `thm:dyadic-thread` from the
source manuscript.
-/

set_option autoImplicit false
set_option linter.unnecessarySimpa false

universe u

namespace UnitIntervalRetracts

open Set
open AbramskyJung.Chapter2

/-- The unit interval with its inherited order. -/
abbrev UnitInterval := Set.Icc (0 : ℝ) 1

section Regularization

variable {Q : Type u} [PartialOrder Q]

/-- Values of a monotone candidate section strictly below `t`. -/
def lowerSectionValues (j : UnitInterval → Q) (t : UnitInterval) : Set Q :=
  j '' Set.Iio t

theorem lowerSectionValues_directed
    {j : UnitInterval → Q} (hj : Monotone j)
    {t : UnitInterval} (ht : t ≠ 0) :
    DirectedSet (lowerSectionValues j t) := by
  have h0t : (0 : UnitInterval) < t :=
    lt_of_le_of_ne bot_le (Ne.symm ht)
  constructor
  · exact ⟨j 0, ⟨0, h0t, rfl⟩⟩
  · intro x hx y hy
    rcases hx with ⟨r, hrt, rfl⟩
    rcases hy with ⟨s, hst, rfl⟩
    refine ⟨j (max r s),
      ⟨max r s, (show max r s < t from max_lt hrt hst), rfl⟩, ?_, ?_⟩
    · exact hj (le_max_left r s)
    · exact hj (le_max_right r s)

/-- A chosen supremum of the values of `j` strictly below `t`. -/
noncomputable def lowerSectionSup
    (hQ : IsDcpo Q) (j : UnitInterval → Q) (hj : Monotone j)
    (t : UnitInterval) (ht : t ≠ 0) : Q :=
  Classical.choose (hQ (lowerSectionValues j t)
    (lowerSectionValues_directed hj ht))

theorem lowerSectionSup_isSup
    (hQ : IsDcpo Q) (j : UnitInterval → Q) (hj : Monotone j)
    (t : UnitInterval) (ht : t ≠ 0) :
    IsSup (lowerSectionValues j t) (lowerSectionSup hQ j hj t ht) :=
  Classical.choose_spec (hQ (lowerSectionValues j t)
    (lowerSectionValues_directed hj ht))

/-- The lower regularization of a monotone section. -/
noncomputable def regularizedSection
    (hQ : IsDcpo Q) (j : UnitInterval → Q) (hj : Monotone j) :
    UnitInterval → Q :=
  fun t =>
    if ht : t = 0 then
      j 0
    else
      lowerSectionSup hQ j hj t ht

@[simp] theorem regularizedSection_zero
    (hQ : IsDcpo Q) (j : UnitInterval → Q) (hj : Monotone j) :
    regularizedSection hQ j hj 0 = j 0 := by
  simp [regularizedSection]

theorem regularizedSection_isSup
    (hQ : IsDcpo Q) (j : UnitInterval → Q) (hj : Monotone j)
    {t : UnitInterval} (ht : t ≠ 0) :
    IsSup (lowerSectionValues j t) (regularizedSection hQ j hj t) := by
  simp only [regularizedSection, dif_neg ht]
  exact lowerSectionSup_isSup hQ j hj t ht

theorem regularizedSection_monotone
    (hQ : IsDcpo Q) (j : UnitInterval → Q) (hj : Monotone j) :
    Monotone (regularizedSection hQ j hj) := by
  intro a b hab
  by_cases ha : a = 0
  · subst a
    by_cases hb : b = 0
    · subst b
      exact le_rfl
    · have h0b : (0 : UnitInterval) < b :=
        lt_of_le_of_ne bot_le (Ne.symm hb)
      have hs := regularizedSection_isSup hQ j hj hb
      simpa using hs.1 ⟨0, h0b, rfl⟩
  · have hb : b ≠ 0 := by
      intro hb0
      apply ha
      apply le_antisymm
      · simpa [hb0] using hab
      · exact bot_le
    have hsa := regularizedSection_isSup hQ j hj ha
    have hsb := regularizedSection_isSup hQ j hj hb
    apply hsa.2
    intro x hx
    apply hsb.1
    rcases hx with ⟨r, hra, rfl⟩
    exact ⟨r, lt_of_lt_of_le hra hab, rfl⟩

/-- In the inherited dense order on `[0,1]`, `t` is the supremum of its strict
lower interval. -/
theorem unitInterval_isSup_Iio (t : UnitInterval) :
    IsSup (Set.Iio t) t := by
  constructor
  · intro r hrt
    exact le_of_lt hrt
  · intro y hy
    by_contra hty
    have hyt : y < t := lt_of_not_ge hty
    obtain ⟨r, hyr, hrt⟩ := exists_between hyt
    exact (not_le_of_gt hyr) (hy hrt)

omit [PartialOrder Q] in
theorem image_lowerSectionValues
    {f : Q → UnitInterval} {j : UnitInterval → Q}
    (hfj : Function.LeftInverse f j) (t : UnitInterval) :
    f '' lowerSectionValues j t = Set.Iio t := by
  ext y
  constructor
  · rintro ⟨q, ⟨r, hrt, rfl⟩, rfl⟩
    simpa [hfj r] using hrt
  · intro hyt
    exact ⟨j y, ⟨y, hyt, rfl⟩, hfj y⟩

theorem regularizedSection_leftInverse
    (hQ : IsDcpo Q) {f : Q → UnitInterval}
    (hf : AbramskyJung.Chapter2.ScottContinuous f)
    {j : UnitInterval → Q} (hj : Monotone j)
    (hfj : Function.LeftInverse f j) :
    Function.LeftInverse f (regularizedSection hQ j hj) := by
  intro t
  by_cases ht : t = 0
  · subst t
    simpa using hfj 0
  · have hdir := lowerSectionValues_directed hj ht
    have hsup := regularizedSection_isSup hQ j hj ht
    have hfSup :
        IsSup (f '' lowerSectionValues j t)
          (f (regularizedSection hQ j hj t)) :=
      hf.2 hdir hsup
    have htSup : IsSup (f '' lowerSectionValues j t) t := by
      rw [image_lowerSectionValues hfj t]
      exact unitInterval_isSup_Iio t
    exact IsSup.unique hfSup htSup

theorem regularizedSection_maps_isSup
    (hQ : IsDcpo Q) (j : UnitInterval → Q) (hj : Monotone j)
    {A : Set UnitInterval} {t : UnitInterval}
    (hA : DirectedSet A) (ht : IsSup A t) :
    IsSup ((regularizedSection hQ j hj) '' A)
      (regularizedSection hQ j hj t) := by
  constructor
  · intro q hq
    rcases hq with ⟨a, ha, rfl⟩
    exact regularizedSection_monotone hQ j hj (ht.1 ha)
  · intro q hq
    by_cases ht0 : t = 0
    · subst t
      rcases hA.1 with ⟨a, ha⟩
      have ha0 : a = 0 := le_antisymm (ht.1 ha) bot_le
      subst a
      exact hq ⟨0, ha, rfl⟩
    · have hs := regularizedSection_isSup hQ j hj ht0
      apply hs.2
      intro x hx
      rcases hx with ⟨r, hrt, rfl⟩
      have hex : ∃ a ∈ A, r < a := by
        by_contra hnone
        have hrUpper : IsUpperBound A r := by
          intro a ha
          exact le_of_not_gt (by
            intro hra
            exact hnone ⟨a, ha, hra⟩)
        exact (not_le_of_gt hrt) (ht.2 r hrUpper)
      rcases hex with ⟨a, ha, hra⟩
      have ha0 : a ≠ 0 := by
        intro ha0
        subst a
        exact (not_lt_of_ge (show (0 : UnitInterval) ≤ r from bot_le)) hra
      have hja : j r ≤ regularizedSection hQ j hj a :=
        (regularizedSection_isSup hQ j hj ha0).1 ⟨r, hra, rfl⟩
      exact le_trans hja (hq ⟨a, ha, rfl⟩)

theorem regularizedSection_scottContinuous
    (hQ : IsDcpo Q) (j : UnitInterval → Q) (hj : Monotone j) :
    AbramskyJung.Chapter2.ScottContinuous
      (regularizedSection hQ j hj) := by
  constructor
  · exact regularizedSection_monotone hQ j hj
  · intro A t hA ht
    exact regularizedSection_maps_isSup hQ j hj hA ht

/-- Proposition `prop:regularize-section`. -/
theorem monotoneSection_iff_scottContinuousSection
    (hQ : IsDcpo Q) (f : Q → UnitInterval)
    (hf : AbramskyJung.Chapter2.ScottContinuous f)
    (_hfSurjective : Function.Surjective f) :
    (∃ j : UnitInterval → Q, Monotone j ∧ Function.LeftInverse f j) ↔
      ∃ s : UnitInterval → Q,
        AbramskyJung.Chapter2.ScottContinuous s ∧
          Function.LeftInverse f s := by
  constructor
  · rintro ⟨j, hj, hfj⟩
    exact ⟨regularizedSection hQ j hj,
      regularizedSection_scottContinuous hQ j hj,
      regularizedSection_leftInverse hQ hf hj hfj⟩
  · rintro ⟨s, hs, hfs⟩
    exact ⟨s, hs.1, hfs⟩

end Regularization

/-- A point represented by a dyadic rational `k / 2^n`. -/
def IsDyadic (d : UnitInterval) : Prop :=
  ∃ n k : ℕ, (d : ℝ) = (k : ℝ) / (2 : ℝ) ^ n

theorem isDyadic_iff_bounded_representation (d : UnitInterval) :
    IsDyadic d ↔
      ∃ n k : ℕ, k ≤ 2 ^ n ∧
        (d : ℝ) = (k : ℝ) / (2 : ℝ) ^ n := by
  constructor
  · rintro ⟨n, k, hdk⟩
    have hpowpos : 0 < (2 : ℝ) ^ n := by positivity
    have hkReal : (k : ℝ) ≤ (2 : ℝ) ^ n := by
      have hdle : (d : ℝ) ≤ 1 := d.property.2
      rw [hdk] at hdle
      exact (div_le_one₀ hpowpos).mp hdle
    have hk : k ≤ 2 ^ n := by
      exact_mod_cast hkReal
    exact ⟨n, k, hk, hdk⟩
  · rintro ⟨n, k, _hk, hdk⟩
    exact ⟨n, k, hdk⟩

@[simp] theorem isDyadic_zero : IsDyadic (0 : UnitInterval) := by
  exact ⟨0, 0, by norm_num⟩

/-- Dyadics below `1`, exactly as indexed by the source criterion. -/
abbrev DyadicBelowOne :=
  {d : UnitInterval // IsDyadic d ∧ d < 1}

def dyadicZero : DyadicBelowOne :=
  ⟨0, isDyadic_zero, by norm_num⟩

@[simp] theorem dyadicZero_value :
    (dyadicZero : UnitInterval) = 0 := rfl

/-- Dyadic rationals are order-dense in the unit interval. -/
theorem exists_dyadic_between
    {x y : UnitInterval} (hxy : x < y) :
    ∃ d : UnitInterval, x < d ∧ d < y ∧ IsDyadic d := by
  have hgap : 0 < (y : ℝ) - (x : ℝ) := sub_pos.mpr hxy
  obtain ⟨n, hn⟩ :=
    exists_pow_lt_of_lt_one hgap (show (1 / 2 : ℝ) < 1 by norm_num)
  let N : ℝ := (2 : ℝ) ^ n
  have hNpos : 0 < N := by
    dsimp [N]
    positivity
  have hmesh : 1 / N < (y : ℝ) - (x : ℝ) := by
    dsimp [N]
    simpa [div_pow] using hn
  let k : ℕ := ⌊N * (x : ℝ)⌋₊ + 1
  have hxscale : 0 ≤ N * (x : ℝ) :=
    mul_nonneg hNpos.le x.property.1
  have hxk : N * (x : ℝ) < (k : ℝ) := by
    dsimp [k]
    simpa using Nat.lt_floor_add_one (N * (x : ℝ))
  have hkUpper : (k : ℝ) ≤ N * (x : ℝ) + 1 := by
    dsimp [k]
    push_cast
    linarith [Nat.floor_le hxscale]
  have hxd : (x : ℝ) < (k : ℝ) / N := by
    rw [lt_div_iff₀ hNpos]
    simpa [mul_comm] using hxk
  have hdUpper : (k : ℝ) / N ≤ (x : ℝ) + 1 / N := by
    rw [div_le_iff₀ hNpos]
    calc
      (k : ℝ) ≤ N * (x : ℝ) + 1 := hkUpper
      _ = ((x : ℝ) + 1 / N) * N := by
        field_simp
  have hdy : (k : ℝ) / N < (y : ℝ) := by
    linarith
  let d : UnitInterval :=
    ⟨(k : ℝ) / N,
      ⟨div_nonneg (Nat.cast_nonneg k) hNpos.le,
        (le_of_lt hdy).trans y.property.2⟩⟩
  refine ⟨d, ?_, ?_, ?_⟩
  · exact hxd
  · exact hdy
  · exact ⟨n, k, by simp [d, N]⟩

section DyadicThread

variable {Q : Type u} [PartialOrder Q]

/-- An increasing exact choice over all dyadics below `1`. -/
def IsIncreasingDyadicThread
    (f : Q → UnitInterval) (x : DyadicBelowOne → Q) : Prop :=
  (∀ d, f (x d) = (d : UnitInterval)) ∧
    ∀ ⦃d e : DyadicBelowOne⦄, d < e → x d ≤ x e

theorem IsIncreasingDyadicThread.monotone
    {f : Q → UnitInterval} {x : DyadicBelowOne → Q}
    (hx : IsIncreasingDyadicThread f x) :
    Monotone x := by
  intro d e hde
  rcases eq_or_lt_of_le hde with h | h
  · subst e
    exact le_rfl
  · exact hx.2 h

def threadValues (x : DyadicBelowOne → Q) (t : UnitInterval) : Set Q :=
  x '' {d : DyadicBelowOne | (d : UnitInterval) < t}

theorem threadValues_directed
    {f : Q → UnitInterval} {x : DyadicBelowOne → Q}
    (hx : IsIncreasingDyadicThread f x)
    {t : UnitInterval} (ht : t ≠ 0) :
    DirectedSet (threadValues x t) := by
  have h0t : (0 : UnitInterval) < t :=
    lt_of_le_of_ne bot_le (Ne.symm ht)
  have hxmono := hx.monotone
  constructor
  · exact ⟨x dyadicZero, ⟨dyadicZero, h0t, rfl⟩⟩
  · intro q hq r hr
    rcases hq with ⟨d, hdt, rfl⟩
    rcases hr with ⟨e, het, rfl⟩
    rcases le_total d e with hde | hed
    · exact ⟨x e, ⟨e, het, rfl⟩, hxmono hde, le_rfl⟩
    · exact ⟨x d, ⟨d, hdt, rfl⟩, le_rfl, hxmono hed⟩

noncomputable def threadSup
    (hQ : IsDcpo Q) {f : Q → UnitInterval}
    (x : DyadicBelowOne → Q) (hx : IsIncreasingDyadicThread f x)
    (t : UnitInterval) (ht : t ≠ 0) : Q :=
  Classical.choose (hQ (threadValues x t) (threadValues_directed hx ht))

theorem threadSup_isSup
    (hQ : IsDcpo Q) {f : Q → UnitInterval}
    (x : DyadicBelowOne → Q) (hx : IsIncreasingDyadicThread f x)
    (t : UnitInterval) (ht : t ≠ 0) :
    IsSup (threadValues x t) (threadSup hQ x hx t ht) :=
  Classical.choose_spec
    (hQ (threadValues x t) (threadValues_directed hx ht))

noncomputable def dyadicThreadSection
    (hQ : IsDcpo Q) {f : Q → UnitInterval}
    (x : DyadicBelowOne → Q) (hx : IsIncreasingDyadicThread f x) :
    UnitInterval → Q :=
  fun t =>
    if ht : t = 0 then
      x dyadicZero
    else
      threadSup hQ x hx t ht

@[simp] theorem dyadicThreadSection_zero
    (hQ : IsDcpo Q) {f : Q → UnitInterval}
    (x : DyadicBelowOne → Q) (hx : IsIncreasingDyadicThread f x) :
    dyadicThreadSection hQ x hx 0 = x dyadicZero := by
  simp [dyadicThreadSection]

theorem dyadicThreadSection_isSup
    (hQ : IsDcpo Q) {f : Q → UnitInterval}
    (x : DyadicBelowOne → Q) (hx : IsIncreasingDyadicThread f x)
    {t : UnitInterval} (ht : t ≠ 0) :
    IsSup (threadValues x t) (dyadicThreadSection hQ x hx t) := by
  simp only [dyadicThreadSection, dif_neg ht]
  exact threadSup_isSup hQ x hx t ht

theorem dyadicThreadSection_monotone
    (hQ : IsDcpo Q) {f : Q → UnitInterval}
    (x : DyadicBelowOne → Q) (hx : IsIncreasingDyadicThread f x) :
    Monotone (dyadicThreadSection hQ x hx) := by
  intro a b hab
  by_cases ha : a = 0
  · subst a
    by_cases hb : b = 0
    · subst b
      exact le_rfl
    · have h0b : (0 : UnitInterval) < b :=
        lt_of_le_of_ne bot_le (Ne.symm hb)
      have hs := dyadicThreadSection_isSup hQ x hx hb
      simpa using hs.1 ⟨dyadicZero, h0b, rfl⟩
  · have hb : b ≠ 0 := by
      intro hb0
      apply ha
      apply le_antisymm
      · simpa [hb0] using hab
      · exact bot_le
    have hsa := dyadicThreadSection_isSup hQ x hx ha
    have hsb := dyadicThreadSection_isSup hQ x hx hb
    apply hsa.2
    intro q hq
    apply hsb.1
    rcases hq with ⟨d, hda, rfl⟩
    exact ⟨d, lt_of_lt_of_le hda hab, rfl⟩

def dyadicLowerSet (t : UnitInterval) : Set UnitInterval :=
  {d | IsDyadic d ∧ d < t}

theorem dyadicLowerSet_isSup (t : UnitInterval) :
    IsSup (dyadicLowerSet t) t := by
  constructor
  · intro d hd
    exact le_of_lt hd.2
  · intro y hy
    by_contra hty
    have hyt : y < t := lt_of_not_ge hty
    obtain ⟨d, hyd, hdt, hdDyadic⟩ := exists_dyadic_between hyt
    exact (not_le_of_gt hyd) (hy ⟨hdDyadic, hdt⟩)

theorem image_threadValues
    {f : Q → UnitInterval} {x : DyadicBelowOne → Q}
    (hx : IsIncreasingDyadicThread f x) (t : UnitInterval) :
    f '' threadValues x t = dyadicLowerSet t := by
  ext y
  constructor
  · rintro ⟨q, ⟨d, hdt, rfl⟩, rfl⟩
    simpa [dyadicLowerSet, hx.1 d] using And.intro d.property.1 hdt
  · rintro ⟨hyDyadic, hyt⟩
    have hy1 : y < (1 : UnitInterval) :=
      lt_of_lt_of_le hyt t.property.2
    let d : DyadicBelowOne := ⟨y, hyDyadic, hy1⟩
    exact ⟨x d, ⟨d, hyt, rfl⟩, hx.1 d⟩

theorem dyadicThreadSection_leftInverse
    (hQ : IsDcpo Q) {f : Q → UnitInterval}
    (hf : AbramskyJung.Chapter2.ScottContinuous f)
    (x : DyadicBelowOne → Q) (hx : IsIncreasingDyadicThread f x) :
    Function.LeftInverse f (dyadicThreadSection hQ x hx) := by
  intro t
  by_cases ht : t = 0
  · subst t
    simpa using hx.1 dyadicZero
  · have hdir := threadValues_directed hx ht
    have hsup := dyadicThreadSection_isSup hQ x hx ht
    have hfSup :
        IsSup (f '' threadValues x t) (f (dyadicThreadSection hQ x hx t)) :=
      hf.2 hdir hsup
    have htSup : IsSup (f '' threadValues x t) t := by
      rw [image_threadValues hx t]
      exact dyadicLowerSet_isSup t
    exact IsSup.unique hfSup htSup

theorem dyadicThreadSection_maps_isSup
    (hQ : IsDcpo Q) {f : Q → UnitInterval}
    (x : DyadicBelowOne → Q) (hx : IsIncreasingDyadicThread f x)
    {A : Set UnitInterval} {t : UnitInterval}
    (hA : DirectedSet A) (ht : IsSup A t) :
    IsSup ((dyadicThreadSection hQ x hx) '' A)
      (dyadicThreadSection hQ x hx t) := by
  constructor
  · intro q hq
    rcases hq with ⟨a, ha, rfl⟩
    exact dyadicThreadSection_monotone hQ x hx (ht.1 ha)
  · intro q hq
    by_cases ht0 : t = 0
    · subst t
      rcases hA.1 with ⟨a, ha⟩
      have ha0 : a = 0 := le_antisymm (ht.1 ha) bot_le
      subst a
      exact hq ⟨0, ha, rfl⟩
    · have hs := dyadicThreadSection_isSup hQ x hx ht0
      apply hs.2
      intro z hz
      rcases hz with ⟨d, hdt, rfl⟩
      have hex : ∃ a ∈ A, (d : UnitInterval) < a := by
        by_contra hnone
        have hdUpper : IsUpperBound A (d : UnitInterval) := by
          intro a ha
          exact le_of_not_gt (by
            intro hda
            exact hnone ⟨a, ha, hda⟩)
        exact (not_le_of_gt hdt) (ht.2 (d : UnitInterval) hdUpper)
      rcases hex with ⟨a, ha, hda⟩
      have ha0 : a ≠ 0 := by
        intro ha0
        subst a
        exact (not_lt_of_ge
          (show (0 : UnitInterval) ≤ (d : UnitInterval) from bot_le)) hda
      have hxda : x d ≤ dyadicThreadSection hQ x hx a :=
        (dyadicThreadSection_isSup hQ x hx ha0).1 ⟨d, hda, rfl⟩
      exact le_trans hxda (hq ⟨a, ha, rfl⟩)

theorem dyadicThreadSection_scottContinuous
    (hQ : IsDcpo Q) {f : Q → UnitInterval}
    (x : DyadicBelowOne → Q) (hx : IsIncreasingDyadicThread f x) :
    AbramskyJung.Chapter2.ScottContinuous
      (dyadicThreadSection hQ x hx) := by
  constructor
  · exact dyadicThreadSection_monotone hQ x hx
  · intro A t hA ht
    exact dyadicThreadSection_maps_isSup hQ x hx hA ht

/-- Theorem `thm:dyadic-thread`. -/
theorem dyadicThreadCriterion
    (hQ : IsDcpo Q) (f : Q → UnitInterval)
    (hf : AbramskyJung.Chapter2.ScottContinuous f)
    (_hfSurjective : Function.Surjective f) :
    (∃ s : UnitInterval → Q,
        AbramskyJung.Chapter2.ScottContinuous s ∧
          Function.LeftInverse f s) ↔
      ∃ x : DyadicBelowOne → Q, IsIncreasingDyadicThread f x := by
  constructor
  · rintro ⟨s, hs, hfs⟩
    let x : DyadicBelowOne → Q := fun d => s (d : UnitInterval)
    refine ⟨x, ?_, ?_⟩
    · intro d
      exact hfs d
    · intro d e hde
      exact hs.1 (le_of_lt hde)
  · rintro ⟨x, hx⟩
    exact ⟨dyadicThreadSection hQ x hx,
      dyadicThreadSection_scottContinuous hQ x hx,
      dyadicThreadSection_leftInverse hQ hf x hx⟩

end DyadicThread

end UnitIntervalRetracts
