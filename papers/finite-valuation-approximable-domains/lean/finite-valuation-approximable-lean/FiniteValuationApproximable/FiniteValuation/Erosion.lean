import FiniteValuationApproximable.FiniteValuation.Basic
import Mathlib.Order.Preorder.Finite

/-!
# Frontier erosion on a finite poset

This module formalizes the finite combinatorial core of Sections
`sec:construction` and `sec:upper-set` of `main (17).tex`.

Source version: SHA-256
`4b2e65f0f96347bea4df7571e8993ad6e888c0ff7181c1305c5056880365ac94`.

The source writes `A(p)` for the maximal elements of the positive support and
`c(A) = (n+1)^(n-|down A|)`.  We keep the corresponding finite sets explicit,
so their cardinality arguments can be checked by Lean.
-/

set_option autoImplicit false
set_option linter.unnecessarySimpa false

universe u

namespace FiniteValuationApproximable

open scoped Classical
open Set

namespace Erosion

variable {P : Type u} [Fintype P] [PartialOrder P]

open SubprobabilityVector

/-! ## Finite antichains and their lower closures -/

/-- The finite lower closure `down A`. -/
noncomputable def lowerClosure (A : Finset P) : Finset P := by
  classical
  exact Finset.univ.filter fun x => ∃ a ∈ A, x ≤ a

@[simp]
theorem mem_lowerClosure {A : Finset P} {x : P} :
    x ∈ lowerClosure A ↔ ∃ a ∈ A, x ≤ a := by
  classical
  simp [lowerClosure]

/-- A finite-set formulation of the source's antichain condition. -/
def IsAntichain (A : Finset P) : Prop :=
  ∀ ⦃a⦄, a ∈ A → ∀ ⦃b⦄, b ∈ A → a ≤ b → a = b

/-- `A` lies below `B`, i.e. `A subset down B`. -/
def FrontierBelow (A B : Finset P) : Prop :=
  ∀ ⦃a⦄, a ∈ A → ∃ b ∈ B, a ≤ b

theorem lowerClosure_subset {A B : Finset P} (hAB : FrontierBelow A B) :
    lowerClosure A ⊆ lowerClosure B := by
  intro x hx
  obtain ⟨a, haA, hxa⟩ := mem_lowerClosure.mp hx
  obtain ⟨b, hbB, hab⟩ := hAB haA
  exact mem_lowerClosure.mpr ⟨b, hbB, hxa.trans hab⟩

private theorem lowerClosure_eq_imp_eq {A B : Finset P}
    (hA : IsAntichain A) (hB : IsAntichain B)
    (hcl : lowerClosure A = lowerClosure B) : A = B := by
  apply Finset.ext
  intro x
  constructor
  · intro hxA
    have hxclB : x ∈ lowerClosure B := by
      rw [← hcl]
      exact mem_lowerClosure.mpr ⟨x, hxA, le_rfl⟩
    obtain ⟨b, hbB, hxb⟩ := mem_lowerClosure.mp hxclB
    have hbclA : b ∈ lowerClosure A := by
      rw [hcl]
      exact mem_lowerClosure.mpr ⟨b, hbB, le_rfl⟩
    obtain ⟨a, haA, hba⟩ := mem_lowerClosure.mp hbclA
    have hxa : x ≤ a := hxb.trans hba
    have hxeqa : x = a := hA hxA haA hxa
    have hbex : b = x := le_antisymm (hba.trans_eq hxeqa.symm) hxb
    simpa [hbex] using hbB
  · intro hxB
    have hxclA : x ∈ lowerClosure A := by
      rw [hcl]
      exact mem_lowerClosure.mpr ⟨x, hxB, le_rfl⟩
    obtain ⟨a, haA, hxa⟩ := mem_lowerClosure.mp hxclA
    have haclB : a ∈ lowerClosure B := by
      rw [← hcl]
      exact mem_lowerClosure.mpr ⟨a, haA, le_rfl⟩
    obtain ⟨b, hbB, hab⟩ := mem_lowerClosure.mp haclB
    have hxb : x ≤ b := hxa.trans hab
    have hxeqb : x = b := hB hxB hbB hxb
    have haex : a = x := le_antisymm (hab.trans_eq hxeqb.symm) hxa
    simpa [haex] using haA

/-- The natural-number coefficient underlying equation `eq:coefficient`. -/
noncomputable def coefficientNat (A : Finset P) : Nat :=
  (Fintype.card P + 1) ^ (Fintype.card P - (lowerClosure A).card)

/-- Equation `eq:coefficient`: `c(A) = (n+1)^(n-|down A|)`. -/
noncomputable def coefficient (A : Finset P) : Real :=
  coefficientNat A

theorem lowerClosure_card_le (A : Finset P) :
    (lowerClosure A).card ≤ Fintype.card P := by
  simpa using Finset.card_le_card
    (show lowerClosure A ⊆ Finset.univ from fun _ _ => Finset.mem_univ _)

theorem coefficient_pos (A : Finset P) : 0 < coefficient A := by
  unfold coefficient coefficientNat
  positivity

private theorem coefficient_comparison_nat {A B : Finset P}
    (hA : IsAntichain A) (hB : IsAntichain B)
    (hAB : FrontierBelow A B) (hne : A ≠ B) :
    (Fintype.card P + 1) * coefficientNat B ≤ coefficientNat A := by
  have hsub : lowerClosure A ⊆ lowerClosure B := lowerClosure_subset hAB
  have hclne : lowerClosure A ≠ lowerClosure B :=
    fun h => hne (lowerClosure_eq_imp_eq hA hB h)
  have hcard : (lowerClosure A).card < (lowerClosure B).card :=
    Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hclne⟩)
  have hBcard : (lowerClosure B).card ≤ Fintype.card P := lowerClosure_card_le B
  have hexp : Fintype.card P - (lowerClosure B).card + 1 ≤
      Fintype.card P - (lowerClosure A).card := by
    omega
  have hbase : 1 ≤ Fintype.card P + 1 := by omega
  have hpow := Nat.pow_le_pow_right hbase hexp
  simpa [coefficientNat, pow_succ', Nat.mul_comm] using hpow

/-- Lemma `lem:coefficient-comparison`.

For nonempty antichains `A` and `B`, if `A subset down B` and `A != B`,
then `c(A) >= (n+1)c(B) > n c(B)`.  Nonemptiness is retained exactly as in
the source, although positivity of this particular coefficient formula does
not need it. -/
theorem lem_coefficient_comparison {A B : Finset P}
    (hA_nonempty : A.Nonempty) (hB_nonempty : B.Nonempty)
    (hA : IsAntichain A) (hB : IsAntichain B)
    (hAB : FrontierBelow A B) (hne : A ≠ B) :
    ((Fintype.card P + 1 : Nat) : Real) * coefficient B ≤ coefficient A ∧
      (Fintype.card P : Real) * coefficient B <
        ((Fintype.card P + 1 : Nat) : Real) * coefficient B := by
  have _hA_witness : ∃ a, a ∈ A := hA_nonempty
  have _hB_witness : ∃ b, b ∈ B := hB_nonempty
  have hmain : ((Fintype.card P + 1 : Nat) : Real) * coefficient B ≤ coefficient A := by
    unfold coefficient
    norm_cast
    exact coefficient_comparison_nat hA hB hAB hne
  have hpositive := coefficient_pos B
  constructor
  · exact hmain
  · push_cast
    nlinarith

/-! ## Positive supports and frontiers -/

/-- The positive support `supp(p)`. -/
noncomputable def support (p : SubprobabilityVector P) : Finset P := by
  classical
  exact Finset.univ.filter fun x => 0 < p x

@[simp]
theorem mem_support {p : SubprobabilityVector P} {x : P} :
    x ∈ support p ↔ 0 < p x := by
  classical
  simp [support]

/-- The frontier `A(p)`: maximal elements of the positive support. -/
noncomputable def frontier (p : SubprobabilityVector P) : Finset P := by
  classical
  exact Finset.univ.filter fun x => Maximal (fun y => y ∈ support p) x

@[simp]
theorem mem_frontier {p : SubprobabilityVector P} {x : P} :
    x ∈ frontier p ↔ Maximal (fun y => y ∈ support p) x := by
  classical
  simp [frontier]

theorem frontier_subset_support (p : SubprobabilityVector P) :
    frontier p ⊆ support p := by
  intro x hx
  exact (mem_frontier.mp hx).1

theorem frontier_isAntichain (p : SubprobabilityVector P) :
    IsAntichain (frontier p) := by
  intro a ha b hb hab
  have hba : b ≤ a := (mem_frontier.mp ha).2 (mem_frontier.mp hb).1 hab
  exact le_antisymm hab hba

theorem support_nonempty_iff_ne_zero (p : SubprobabilityVector P) :
    (support p).Nonempty ↔ p ≠ 0 := by
  constructor
  · intro hs hp0
    subst p
    obtain ⟨x, hx⟩ := hs
    have hxpos : 0 < (0 : SubprobabilityVector P) x := mem_support.mp hx
    simpa using hxpos
  · intro hp0
    by_contra hs
    have hs_empty : support p = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    apply hp0
    apply SubprobabilityVector.ext
    intro x
    have hx_not_pos : ¬ 0 < p x := by
      intro hx
      have hxmem : x ∈ support p := mem_support.mpr hx
      simpa [hs_empty] using hxmem
    exact le_antisymm (le_of_not_gt hx_not_pos) (p.coeff_nonneg x)

theorem frontier_nonempty_of_ne_zero {p : SubprobabilityVector P} (hp : p ≠ 0) :
    (frontier p).Nonempty := by
  obtain ⟨x, hx⟩ := (support_nonempty_iff_ne_zero p).2 hp
  obtain ⟨a, hxa, hamax⟩ := (support p).exists_le_maximal hx
  exact ⟨a, mem_frontier.mpr hamax⟩

private theorem exists_support_mem_of_mass_pos
    (p : SubprobabilityVector P) (S : Set P) (hmass : 0 < p.mass S) :
    ∃ x, x ∈ support p ∧ x ∈ S := by
  classical
  by_contra hnone
  push Not at hnone
  have hmass_zero : p.mass S = 0 := by
    unfold SubprobabilityVector.mass
    apply Finset.sum_eq_zero
    intro x hx
    by_cases hxS : x ∈ S
    · have hx_not_pos : ¬ 0 < p x := by
        intro hxpos
        exact hnone x (mem_support.mpr hxpos) hxS
      have hpx : p x = 0 :=
        le_antisymm (le_of_not_gt hx_not_pos) (p.coeff_nonneg x)
      simp [hxS, hpx]
    · simp [hxS]
  linarith

/-- Lemma `lem:max-support-meets-upper`.

If an upper set has positive mass, it meets the maximal positive support. -/
theorem lem_max_support_meets_upper (p : SubprobabilityVector P)
    (U : UpperSet P) (hmass : 0 < upperMass p U) :
    ∃ a, a ∈ frontier p ∧ a ∈ (U : Set P) := by
  obtain ⟨x, hx_support, hxU⟩ :=
    exists_support_mem_of_mass_pos p (U : Set P) hmass
  obtain ⟨a, hxa, hamax⟩ := (support p).exists_le_maximal hx_support
  exact ⟨a, mem_frontier.mpr hamax, U.upper hxa hxU⟩

/-- Every positive atom contributes positive mass to its principal upper set. -/
private theorem upperMass_principal_pos_of_mem_support
    (p : SubprobabilityVector P) {a : P} (ha : a ∈ support p) :
    0 < upperMass p (principalUpperSet a) := by
  have hpa : 0 < p a := mem_support.mp ha
  have hle : p a ≤ p.mass (Set.Ici a) := by
    rw [← show p.mass ({a} : Set P) = p a by
      classical
      simp [SubprobabilityVector.mass]]
    apply p.mass_mono
    intro x hx
    have hxa : x = a := by simpa only [Set.mem_singleton_iff] using hx
    subst x
    exact le_rfl
  exact lt_of_lt_of_le hpa (by simpa [upperMass, principalUpperSet] using hle)

/-- Lemma `lem:max-support-comparison`.

If `p <= q` stochastically and `p != 0`, every maximal support point of `p`
lies below a maximal support point of `q`. -/
theorem lem_max_support_comparison {p q : SubprobabilityVector P}
    (hpq : p ≤ q) (hp : p ≠ 0) :
    FrontierBelow (frontier p) (frontier q) := by
  have _hp_support : (support p).Nonempty := (support_nonempty_iff_ne_zero p).2 hp
  intro a ha
  have ha_support : a ∈ support p := frontier_subset_support p ha
  have hp_mass : 0 < upperMass p (principalUpperSet a) :=
    upperMass_principal_pos_of_mem_support p ha_support
  have hq_mass : 0 < upperMass q (principalUpperSet a) :=
    lt_of_lt_of_le hp_mass (hpq (principalUpperSet a))
  obtain ⟨x, hx_support, hax⟩ :=
    exists_support_mem_of_mass_pos q (Set.Ici a) (by
      simpa [upperMass, principalUpperSet] using hq_mass)
  obtain ⟨b, hxb, hbmax⟩ := (support q).exists_le_maximal hx_support
  exact ⟨b, mem_frontier.mpr hbmax, hax.trans hxb⟩

/-! ## One exact erosion stage -/

/-- The duration of the current recursive interval,
`min_{a in A(p)} p_a / c(A(p))`.  It is set to zero only when the frontier is
empty (equivalently, for the zero vector). -/
noncomputable def stageTime (p : SubprobabilityVector P) : Real := by
  classical
  by_cases hA : (frontier p).Nonempty
  · let values : Finset Real :=
      (frontier p).image fun a => p a / coefficient (frontier p)
    exact values.min' (hA.image fun a => p a / coefficient (frontier p))
  · exact 0

theorem stageTime_pos_of_ne_zero {p : SubprobabilityVector P} (hp : p ≠ 0) :
    0 < stageTime p := by
  classical
  have hA : (frontier p).Nonempty := frontier_nonempty_of_ne_zero hp
  let values : Finset Real :=
    (frontier p).image fun a => p a / coefficient (frontier p)
  have hvalues : values.Nonempty :=
    hA.image fun a => p a / coefficient (frontier p)
  have hminmem : values.min' hvalues ∈ values := Finset.min'_mem values hvalues
  obtain ⟨a, ha, hvalue⟩ := Finset.mem_image.mp hminmem
  have hpa : 0 < p a := mem_support.mp (frontier_subset_support p ha)
  have hratio : 0 < p a / coefficient (frontier p) :=
    div_pos hpa (coefficient_pos (frontier p))
  simpa [stageTime, hA, values, ← hvalue] using hratio

theorem stageTime_le_ratio {p : SubprobabilityVector P} {a : P}
    (ha : a ∈ frontier p) :
    stageTime p ≤ p a / coefficient (frontier p) := by
  classical
  have hA : (frontier p).Nonempty := ⟨a, ha⟩
  let values : Finset Real :=
    (frontier p).image fun x => p x / coefficient (frontier p)
  have ha_values : p a / coefficient (frontier p) ∈ values :=
    Finset.mem_image.mpr ⟨a, ha, rfl⟩
  have hmin : values.min' (hA.image fun x => p x / coefficient (frontier p)) ≤
      p a / coefficient (frontier p) :=
    Finset.min'_le values _ ha_values
  simpa [stageTime, hA, values] using hmin

theorem stageTime_attained {p : SubprobabilityVector P} (hp : p ≠ 0) :
    ∃ a ∈ frontier p,
      stageTime p = p a / coefficient (frontier p) := by
  classical
  have hA : (frontier p).Nonempty := frontier_nonempty_of_ne_zero hp
  let values : Finset Real :=
    (frontier p).image fun a => p a / coefficient (frontier p)
  have hvalues : values.Nonempty :=
    hA.image fun a => p a / coefficient (frontier p)
  have hminmem : values.min' hvalues ∈ values := Finset.min'_mem values hvalues
  obtain ⟨a, ha, hvalue⟩ := Finset.mem_image.mp hminmem
  exact ⟨a, ha, by simpa [stageTime, hA, values] using hvalue.symm⟩

theorem le_stageTime {p : SubprobabilityVector P} (hp : p ≠ 0) {r : Real}
    (hr : ∀ a ∈ frontier p, r ≤ p a / coefficient (frontier p)) :
    r ≤ stageTime p := by
  classical
  have hA : (frontier p).Nonempty := frontier_nonempty_of_ne_zero hp
  let values : Finset Real :=
    (frontier p).image fun a => p a / coefficient (frontier p)
  have hvalues : values.Nonempty :=
    hA.image fun a => p a / coefficient (frontier p)
  have hmin : r ≤ values.min' hvalues := by
    apply Finset.le_min' values hvalues r
    intro y hy
    obtain ⟨a, ha, hay⟩ := Finset.mem_image.mp hy
    simpa [← hay] using hr a ha
  simpa [stageTime, hA, values] using hmin

/-- One simultaneous frontier erosion by time `h`.  The subtraction is
clipped at zero, so this is a total function; on `0 <= h <= stageTime p` the
clipping is inactive and this is exactly equation `eq:recursive-interval`. -/
noncomputable def erodeBy (p : SubprobabilityVector P) (h : Real) :
    SubprobabilityVector P := by
  classical
  exact
    { coeff := fun x =>
        if x ∈ frontier p then
          max (p x - max h 0 * coefficient (frontier p)) 0
        else p x
      coeff_nonneg := fun x => by
        by_cases hx : x ∈ frontier p
        · rw [if_pos hx]
          exact le_max_right _ _
        · rw [if_neg hx]
          exact p.coeff_nonneg x
      total_le_one := by
        calc
          (∑ x, if x ∈ frontier p then
              max (p x - max h 0 * coefficient (frontier p)) 0 else p x) ≤
              ∑ x, p x := by
                apply Finset.sum_le_sum
                intro x hx
                by_cases hxA : x ∈ frontier p
                · rw [if_pos hxA]
                  exact max_le
                    (sub_le_self _
                      (mul_nonneg (le_max_right _ _) (le_of_lt (coefficient_pos _))))
                    (p.coeff_nonneg x)
                · rw [if_neg hxA]
          _ ≤ 1 := p.total_le_one }

@[simp]
theorem erodeBy_apply (p : SubprobabilityVector P) (h : Real) (x : P) :
    erodeBy p h x =
      if x ∈ frontier p then
        max (p x - max h 0 * coefficient (frontier p)) 0
      else p x := by
  classical
  rfl

/-- Coordinatewise comparison, deliberately kept separate from the stochastic
order instance. -/
def CoordinatewiseLE (p q : SubprobabilityVector P) : Prop :=
  ∀ x, p x ≤ q x

theorem CoordinatewiseLE.refl (p : SubprobabilityVector P) :
    CoordinatewiseLE p p := fun _ => le_rfl

theorem CoordinatewiseLE.trans {p q r : SubprobabilityVector P}
    (hpq : CoordinatewiseLE p q) (hqr : CoordinatewiseLE q r) :
    CoordinatewiseLE p r := fun x => (hpq x).trans (hqr x)

theorem erodeBy_coordinatewise_le (p : SubprobabilityVector P) (h : Real) :
    CoordinatewiseLE (erodeBy p h) p := by
  intro x
  classical
  by_cases hx : x ∈ frontier p
  · rw [erodeBy_apply, if_pos hx]
    exact max_le
      (sub_le_self _ (mul_nonneg (le_max_right _ _) (le_of_lt (coefficient_pos _))))
      (p.coeff_nonneg x)
  · simp [erodeBy_apply, hx]

theorem support_erodeBy_subset (p : SubprobabilityVector P) (h : Real) :
    support (erodeBy p h) ⊆ support p := by
  intro x hx
  exact mem_support.mpr (lt_of_lt_of_le (mem_support.mp hx) (erodeBy_coordinatewise_le p h x))

/-- On a genuine recursive interval, a frontier coordinate has the exact
affine formula from `eq:recursive-interval`. -/
theorem erodeBy_apply_of_mem_frontier {p : SubprobabilityVector P} {a : P}
    {h : Real} (ha : a ∈ frontier p)
    (hh0 : 0 ≤ h) (hht : h ≤ stageTime p) :
    erodeBy p h a = p a - h * coefficient (frontier p) := by
  rw [erodeBy_apply, if_pos ha, max_eq_left hh0]
  have hcpos : 0 < coefficient (frontier p) := coefficient_pos _
  have hratio : stageTime p ≤ p a / coefficient (frontier p) :=
    stageTime_le_ratio ha
  have hmul : h * coefficient (frontier p) ≤ p a := by
    have := mul_le_mul_of_nonneg_right (hht.trans hratio) (le_of_lt hcpos)
    rwa [div_mul_cancel₀ _ (ne_of_gt hcpos)] at this
  rw [max_eq_left (sub_nonneg.mpr hmul)]

@[simp]
theorem erodeBy_apply_of_not_mem_frontier (p : SubprobabilityVector P)
    {x : P} {h : Real} (hx : x ∉ frontier p) :
    erodeBy p h x = p x := by
  simp [erodeBy_apply, hx]

/-- Strictly before the next event, no positive coordinate has vanished. -/
theorem support_erodeBy_eq {p : SubprobabilityVector P} (hp : p ≠ 0)
    {h : Real} (hh0 : 0 ≤ h) (hht : h < stageTime p) :
    support (erodeBy p h) = support p := by
  apply Finset.Subset.antisymm (support_erodeBy_subset p h)
  intro x hx
  have hpx : 0 < p x := mem_support.mp hx
  by_cases hxA : x ∈ frontier p
  · have hcpos : 0 < coefficient (frontier p) := coefficient_pos _
    have hratio : stageTime p ≤ p x / coefficient (frontier p) :=
      stageTime_le_ratio hxA
    have hmul : h * coefficient (frontier p) < p x := by
      have hmul' := mul_lt_mul_of_pos_right (hht.trans_le hratio) hcpos
      rwa [div_mul_cancel₀ _ (ne_of_gt hcpos)] at hmul'
    apply mem_support.mpr
    rw [erodeBy_apply_of_mem_frontier hxA hh0 (le_of_lt hht)]
    linarith
  · apply mem_support.mpr
    rw [erodeBy_apply_of_not_mem_frontier p hxA]
    exact hpx

theorem frontier_erodeBy_eq {p : SubprobabilityVector P} (hp : p ≠ 0)
    {h : Real} (hh0 : 0 ≤ h) (hht : h < stageTime p) :
    frontier (erodeBy p h) = frontier p := by
  unfold frontier
  rw [support_erodeBy_eq hp hh0 hht]

theorem erodeBy_ne_zero_of_lt {p : SubprobabilityVector P} (hp : p ≠ 0)
    {h : Real} (hh0 : 0 ≤ h) (hht : h < stageTime p) :
    erodeBy p h ≠ 0 := by
  apply (support_nonempty_iff_ne_zero (erodeBy p h)).mp
  rw [support_erodeBy_eq hp hh0 hht]
  exact (support_nonempty_iff_ne_zero p).2 hp

/-- Strictly inside a recursive interval, the time remaining until its endpoint
is exactly the old stage time minus elapsed time. -/
theorem stageTime_erodeBy {p : SubprobabilityVector P} (hp : p ≠ 0)
    {h : Real} (hh0 : 0 ≤ h) (hht : h < stageTime p) :
    stageTime (erodeBy p h) = stageTime p - h := by
  have hfront : frontier (erodeBy p h) = frontier p :=
    frontier_erodeBy_eq hp hh0 hht
  have hr0 : erodeBy p h ≠ 0 := erodeBy_ne_zero_of_lt hp hh0 hht
  have hc0 : coefficient (frontier p) ≠ 0 := ne_of_gt (coefficient_pos _)
  have hratio (a : P) (ha : a ∈ frontier p) :
      erodeBy p h a / coefficient (frontier (erodeBy p h)) =
        p a / coefficient (frontier p) - h := by
    rw [hfront, erodeBy_apply_of_mem_frontier ha hh0 (le_of_lt hht)]
    field_simp
  apply le_antisymm
  · obtain ⟨a, ha, hstage⟩ := stageTime_attained hp
    have ha' : a ∈ frontier (erodeBy p h) := by simpa [hfront] using ha
    have hle := stageTime_le_ratio ha'
    rw [hratio a ha, ← hstage] at hle
    exact hle
  · apply le_stageTime hr0
    intro a ha'
    have ha : a ∈ frontier p := by simpa [hfront] using ha'
    rw [hratio a ha]
    have hle := stageTime_le_ratio ha
    linarith

@[simp]
theorem erodeBy_zero (p : SubprobabilityVector P) : erodeBy p 0 = p := by
  apply SubprobabilityVector.ext
  intro x
  by_cases hx : x ∈ frontier p
  · rw [erodeBy_apply, if_pos hx]
    simp [p.coeff_nonneg x]
  · rw [erodeBy_apply_of_not_mem_frontier p hx]

/-- Additivity of erosion while the combined time stays in one recursive
interval. -/
theorem erodeBy_add {p : SubprobabilityVector P} (hp : p ≠ 0)
    {h k : Real} (hh0 : 0 ≤ h) (hk0 : 0 ≤ k)
    (hsum : h + k ≤ stageTime p) :
    erodeBy (erodeBy p h) k = erodeBy p (h + k) := by
  by_cases hkzero : k = 0
  · subst k
    simp
  · have hkpos : 0 < k := lt_of_le_of_ne hk0 (Ne.symm hkzero)
    have hlt : h < stageTime p := by linarith
    have hfront : frontier (erodeBy p h) = frontier p :=
      frontier_erodeBy_eq hp hh0 hlt
    have hstage : stageTime (erodeBy p h) = stageTime p - h :=
      stageTime_erodeBy hp hh0 hlt
    have hkstage : k ≤ stageTime (erodeBy p h) := by
      rw [hstage]
      linarith
    have hhstage : h ≤ stageTime p := le_trans (by linarith) hsum
    apply SubprobabilityVector.ext
    intro x
    by_cases hx : x ∈ frontier p
    · have hx' : x ∈ frontier (erodeBy p h) := by simpa [hfront] using hx
      rw [erodeBy_apply_of_mem_frontier hx' hk0 hkstage,
        erodeBy_apply_of_mem_frontier hx hh0 hhstage,
        erodeBy_apply_of_mem_frontier hx (add_nonneg hh0 hk0) hsum,
        hfront]
      ring
    · have hx' : x ∉ frontier (erodeBy p h) := by simpa [hfront] using hx
      rw [erodeBy_apply_of_not_mem_frontier _ hx',
        erodeBy_apply_of_not_mem_frontier p hx,
        erodeBy_apply_of_not_mem_frontier p hx]

/-- A full recursive stage kills at least one current frontier coordinate and
strictly decreases the positive support. -/
theorem support_erodeBy_stageTime_ssubset {p : SubprobabilityVector P}
    (hp : p ≠ 0) :
    support (erodeBy p (stageTime p)) ⊂ support p := by
  classical
  have hA : (frontier p).Nonempty := frontier_nonempty_of_ne_zero hp
  let values : Finset Real :=
    (frontier p).image fun a => p a / coefficient (frontier p)
  have hvalues : values.Nonempty :=
    hA.image fun a => p a / coefficient (frontier p)
  have hminmem : values.min' hvalues ∈ values := Finset.min'_mem values hvalues
  obtain ⟨a, ha, hvalue⟩ := Finset.mem_image.mp hminmem
  have hstage : stageTime p = p a / coefficient (frontier p) := by
    simpa [stageTime, hA, values] using hvalue.symm
  have hstage_pos : 0 < stageTime p := stageTime_pos_of_ne_zero hp
  have hkill : erodeBy p (stageTime p) a = 0 := by
    rw [erodeBy_apply, if_pos ha, max_eq_left (le_of_lt hstage_pos), hstage]
    rw [div_mul_cancel₀ _ (ne_of_gt (coefficient_pos (frontier p))), sub_self, max_self]
  refine Finset.ssubset_iff_subset_ne.mpr ⟨support_erodeBy_subset p _, ?_⟩
  intro heq
  have ha_old : a ∈ support p := frontier_subset_support p ha
  have ha_new : a ∈ support (erodeBy p (stageTime p)) := by simpa [heq] using ha_old
  have : 0 < erodeBy p (stageTime p) a := mem_support.mp ha_new
  linarith

/-- Current frontier points lying in an upper set. -/
noncomputable def frontierIn (p : SubprobabilityVector P) (U : UpperSet P) : Finset P :=
  (frontier p).filter fun x => x ∈ (U : Set P)

@[simp]
theorem mem_frontierIn {p : SubprobabilityVector P} {U : UpperSet P} {x : P} :
    x ∈ frontierIn p U ↔ x ∈ frontier p ∧ x ∈ (U : Set P) := by
  simp [frontierIn]

/-- Equation `eq:gamma`: instantaneous upper-set loss rate. -/
noncomputable def gamma (U : UpperSet P) (p : SubprobabilityVector P) : Real :=
  if p = 0 then 0 else coefficient (frontier p) * (frontierIn p U).card

theorem gamma_eq_of_ne_zero {p : SubprobabilityVector P} (hp : p ≠ 0)
    (U : UpperSet P) :
    gamma U p = coefficient (frontier p) * (frontierIn p U).card := by
  simp [gamma, hp]

/-- Exact upper-set mass formula on one recursive interval.  This is the
single-stage content used by `lem:local-upper-formula`. -/
theorem upperMass_erodeBy {p : SubprobabilityVector P} (U : UpperSet P)
    {h : Real} (hp : p ≠ 0) (hh0 : 0 ≤ h) (hht : h ≤ stageTime p) :
    upperMass (erodeBy p h) U = upperMass p U - h * gamma U p := by
  classical
  let loss : P → Real := fun x =>
    if x ∈ frontierIn p U then
      h * coefficient (frontier p)
    else 0
  have hpoint (x : P) :
      (if x ∈ (U : Set P) then erodeBy p h x else 0) =
        (if x ∈ (U : Set P) then p x else 0) - loss x := by
    dsimp only [loss]
    by_cases hxU : x ∈ (U : Set P)
    · by_cases hxA : x ∈ frontier p
      · have hxI : x ∈ frontierIn p U := mem_frontierIn.mpr ⟨hxA, hxU⟩
        rw [if_pos hxU, erodeBy_apply_of_mem_frontier hxA hh0 hht]
        rw [if_pos hxI]
        rw [if_pos hxU]
      · have hxI : x ∉ frontierIn p U := fun hmem => hxA (mem_frontierIn.mp hmem).1
        rw [if_pos hxU, erodeBy_apply_of_not_mem_frontier p hxA]
        rw [if_neg hxI]
        rw [if_pos hxU]
        ring
    · have hxI : x ∉ frontierIn p U := fun hmem => hxU (mem_frontierIn.mp hmem).2
      rw [if_neg hxU, if_neg hxI]
      rw [if_neg hxU]
      ring
  have hloss :
      (∑ x, loss x) =
        (frontierIn p U).card * (h * coefficient (frontier p)) := by
    dsimp only [loss]
    rw [Finset.sum_ite_mem_eq]
    simp
  unfold upperMass SubprobabilityVector.mass
  calc
    (∑ x, if x ∈ (U : Set P) then erodeBy p h x else 0) =
        ∑ x, ((if x ∈ (U : Set P) then p x else 0) - loss x) := by
          apply Finset.sum_congr rfl
          intro x hx
          exact hpoint x
    _ = (∑ x, if x ∈ (U : Set P) then p x else 0) - ∑ x, loss x := by
      rw [Finset.sum_sub_distrib]
    _ = (∑ x, if x ∈ (U : Set P) then p x else 0) - h * gamma U p := by
      rw [hloss, gamma_eq_of_ne_zero hp]
      ring

private theorem upperMass_pos_of_mem_support_mem
    (p : SubprobabilityVector P) (U : UpperSet P) {a : P}
    (ha : a ∈ support p) (haU : a ∈ (U : Set P)) :
    0 < upperMass p U := by
  have hpa : 0 < p a := mem_support.mp ha
  have hle : p a ≤ p.mass (U : Set P) := by
    rw [← show p.mass ({a} : Set P) = p a by
      classical
      simp [SubprobabilityVector.mass]]
    apply p.mass_mono
    intro x hx
    have hxa : x = a := by simpa only [Set.mem_singleton_iff] using hx
    simpa [hxa] using haU
  exact lt_of_lt_of_le hpa (by simpa [upperMass] using hle)

theorem frontierIn_eq_empty_of_upperMass_eq_zero
    (p : SubprobabilityVector P) (U : UpperSet P)
    (hmass : upperMass p U = 0) : frontierIn p U = ∅ := by
  apply Finset.not_nonempty_iff_eq_empty.mp
  intro hnonempty
  obtain ⟨a, ha⟩ := hnonempty
  have ha' := mem_frontierIn.mp ha
  have hpos := upperMass_pos_of_mem_support_mem p U
    (frontier_subset_support p ha'.1) ha'.2
  linarith

theorem gamma_eq_zero_of_upperMass_eq_zero
    (p : SubprobabilityVector P) (U : UpperSet P)
    (hmass : upperMass p U = 0) : gamma U p = 0 := by
  by_cases hp : p = 0
  · simp [gamma, hp]
  · rw [gamma_eq_of_ne_zero hp U, frontierIn_eq_empty_of_upperMass_eq_zero p U hmass]
    simp

/-- Lemma `lem:boundary-comparison`: at an upper-set equality boundary, the
lower trajectory has at least the instantaneous loss rate of the upper one. -/
theorem lem_boundary_comparison {p q : SubprobabilityVector P}
    (hpq : p ≤ q) (U : UpperSet P)
    (heq : upperMass p U = upperMass q U) :
    gamma U q ≤ gamma U p := by
  by_cases hzero : upperMass p U = 0
  · have hqzero : upperMass q U = 0 := by simpa [← heq] using hzero
    rw [gamma_eq_zero_of_upperMass_eq_zero p U hzero,
      gamma_eq_zero_of_upperMass_eq_zero q U hqzero]
  · have hp_nonneg : 0 ≤ upperMass p U := by
      simpa [upperMass] using p.mass_nonneg (U : Set P)
    have hp_pos : 0 < upperMass p U := lt_of_le_of_ne hp_nonneg (Ne.symm hzero)
    have hq_pos : 0 < upperMass q U := by simpa [← heq] using hp_pos
    have hp0 : p ≠ 0 := by
      intro hpzero
      subst p
      simpa [upperMass] using hp_pos
    have hq0 : q ≠ 0 := by
      intro hqzero
      subst q
      simpa [upperMass] using hq_pos
    have hA_nonempty : (frontier p).Nonempty := frontier_nonempty_of_ne_zero hp0
    have hB_nonempty : (frontier q).Nonempty := frontier_nonempty_of_ne_zero hq0
    have hAI_nonempty : (frontierIn p U).Nonempty := by
      obtain ⟨a, ha, haU⟩ := lem_max_support_meets_upper p U hp_pos
      exact ⟨a, mem_frontierIn.mpr ⟨ha, haU⟩⟩
    have hBI_nonempty : (frontierIn q U).Nonempty := by
      obtain ⟨b, hb, hbU⟩ := lem_max_support_meets_upper q U hq_pos
      exact ⟨b, mem_frontierIn.mpr ⟨hb, hbU⟩⟩
    have hbelow : FrontierBelow (frontier p) (frontier q) :=
      lem_max_support_comparison hpq hp0
    by_cases hfront : frontier p = frontier q
    · have hfrontIn : frontierIn p U = frontierIn q U := by
        simp [frontierIn, hfront]
      rw [gamma_eq_of_ne_zero hp0 U, gamma_eq_of_ne_zero hq0 U,
        hfront, hfrontIn]
    · have hcoeff := lem_coefficient_comparison hA_nonempty hB_nonempty
        (frontier_isAntichain p) (frontier_isAntichain q) hbelow hfront
      have hcoeff_strict :
          (Fintype.card P : Real) * coefficient (frontier q) <
            coefficient (frontier p) :=
        hcoeff.2.trans_le hcoeff.1
      have hcardAI : (1 : Real) ≤ (frontierIn p U).card := by
        exact_mod_cast hAI_nonempty.card_pos
      have hcardBI : ((frontierIn q U).card : Real) ≤ Fintype.card P := by
        exact_mod_cast Finset.card_le_card
          (show frontierIn q U ⊆ Finset.univ from fun _ _ => Finset.mem_univ _)
      rw [gamma_eq_of_ne_zero hp0 U, gamma_eq_of_ne_zero hq0 U]
      have hq_bound :
          coefficient (frontier q) * (frontierIn q U).card ≤
            coefficient (frontier q) * Fintype.card P :=
        mul_le_mul_of_nonneg_left hcardBI (le_of_lt (coefficient_pos _))
      have hp_bound :
          coefficient (frontier p) ≤
            coefficient (frontier p) * (frontierIn p U).card := by
        simpa only [mul_one] using
          mul_le_mul_of_nonneg_left hcardAI (le_of_lt (coefficient_pos _))
      exact le_of_lt <| calc
          coefficient (frontier q) * (frontierIn q U).card ≤
              coefficient (frontier q) * Fintype.card P := hq_bound
          _ = (Fintype.card P : Real) * coefficient (frontier q) := by ring
          _ < coefficient (frontier p) := hcoeff_strict
          _ ≤ coefficient (frontier p) * (frontierIn p U).card := hp_bound

/-! ## Fuelled event recursion -/

/-- Coordinatewise comparison implies stochastic comparison on every upper
set. -/
theorem stochasticLE_of_coordinatewise {p q : SubprobabilityVector P}
    (hpq : CoordinatewiseLE p q) : p ≤ q := by
  intro U
  unfold upperMass SubprobabilityVector.mass
  apply Finset.sum_le_sum
  intro x hx
  by_cases hxU : x ∈ (U : Set P)
  · simp [hxU, hpq x]
  · simp [hxU]

/-- State of the finite event recursion: the current vector and the amount of
time still to erode. -/
structure ErosionState (P : Type u) [Fintype P] where
  value : SubprobabilityVector P
  remaining : Real

/-- Terminal states have consumed all requested time or reached the zero
vector. -/
def ErosionState.Done (s : ErosionState P) : Prop :=
  s.remaining ≤ 0 ∨ s.value = 0

/-- Perform one recursive interval, or the remaining part of one interval.
The active time is `min remaining stageTime`; a nonpositive remaining time or
the zero vector is terminal. -/
noncomputable def advance (s : ErosionState P) : ErosionState P :=
  if s.Done then s
  else
    let h := min s.remaining (stageTime s.value)
    { value := erodeBy s.value h
      remaining := s.remaining - h }

/-- Execute at most `fuel` recursive events. -/
noncomputable def run : Nat → ErosionState P → ErosionState P
  | 0, s => s
  | fuel + 1, s => run fuel (advance s)

theorem advance_eq_self_of_done {s : ErosionState P}
    (hdone : s.Done) : advance s = s := by
  simp [advance, hdone]

theorem run_eq_self_of_done (fuel : Nat) {s : ErosionState P}
    (hdone : s.Done) : run fuel s = s := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
      rw [run, advance_eq_self_of_done hdone, ih]

theorem advance_value_coordinatewise_le (s : ErosionState P) :
    CoordinatewiseLE (advance s).value s.value := by
  by_cases hdone : s.remaining ≤ 0 ∨ s.value = 0
  · rw [advance_eq_self_of_done hdone]
    exact CoordinatewiseLE.refl s.value
  · have hdone' : ¬ ErosionState.Done s := hdone
    rw [advance, if_neg hdone']
    exact erodeBy_coordinatewise_le s.value (min s.remaining (stageTime s.value))

theorem advance_remaining_nonneg {s : ErosionState P} (hrem : 0 ≤ s.remaining) :
    0 ≤ (advance s).remaining := by
  by_cases hdone : s.Done
  · rw [advance_eq_self_of_done hdone]
    exact hrem
  · have hmin : min s.remaining (stageTime s.value) ≤ s.remaining := min_le_left _ _
    rw [advance, if_neg hdone]
    exact sub_nonneg.mpr hmin

/-- One active event either finishes the requested time or strictly decreases
the finite support. -/
theorem advance_done_or_support_card_lt (s : ErosionState P) :
    (advance s).Done ∨
      (support (advance s).value).card < (support s.value).card := by
  by_cases hdone : s.Done
  · left
    rw [advance_eq_self_of_done hdone]
    exact hdone
  · have hp : s.value ≠ 0 := fun hp0 => hdone (Or.inr hp0)
    have hrem_pos : 0 < s.remaining := lt_of_not_ge fun h => hdone (Or.inl h)
    by_cases hle : s.remaining ≤ stageTime s.value
    · left
      left
      rw [advance, if_neg hdone]
      simp [min_eq_left hle]
    · right
      have ht_le : stageTime s.value ≤ s.remaining := le_of_not_ge hle
      have hstrict := support_erodeBy_stageTime_ssubset hp
      have hcard := Finset.card_lt_card hstrict
      rw [advance, if_neg hdone]
      simpa [min_eq_right ht_le] using hcard

theorem run_value_coordinatewise_le (fuel : Nat) (s : ErosionState P) :
    CoordinatewiseLE (run fuel s).value s.value := by
  induction fuel generalizing s with
  | zero => exact CoordinatewiseLE.refl s.value
  | succ fuel ih =>
      exact (ih (s := advance s)).trans (advance_value_coordinatewise_le s)

/-- Any fuel strictly larger than the current support cardinality suffices to
reach a terminal state.  This certifies the `|P|+1` fuel bound used by `Phi`. -/
theorem run_done_of_support_card_lt (fuel : Nat) (s : ErosionState P)
    (hrem : 0 ≤ s.remaining) (hcard : (support s.value).card < fuel) :
    (run fuel s).Done := by
  induction fuel generalizing s with
  | zero => omega
  | succ fuel ih =>
      rw [run]
      have hrem' : 0 ≤ (advance s).remaining := advance_remaining_nonneg hrem
      rcases advance_done_or_support_card_lt s with hdone | hdrop
      · rw [run_eq_self_of_done fuel hdone]
        exact hdone
      · apply ih (s := advance s) hrem'
        omega

/-- The source erosion trajectory with an explicit fuel parameter. -/
noncomputable def phiFuel (fuel : Nat) (t : Real)
    (p : SubprobabilityVector P) : SubprobabilityVector P :=
  (run fuel { value := p, remaining := max t 0 }).value

/-- The finite-poset erosion map `Phi_t`.  There are at most `|P|` nonzero
full stages; one extra step also covers a final partial interval. -/
noncomputable def Phi (t : Real) (p : SubprobabilityVector P) :
    SubprobabilityVector P :=
  phiFuel (Fintype.card P + 1) t p

theorem phiFuel_zero (fuel : Nat) (p : SubprobabilityVector P) :
    phiFuel fuel 0 p = p := by
  have hdone : ({ value := p, remaining := max (0 : Real) 0 } : ErosionState P).Done := by
    left
    norm_num
  simp only [phiFuel]
  rw [run_eq_self_of_done fuel hdone]

/-- The identity-at-zero part of Lemma `lem:basic-family(ii)`. -/
theorem Phi_zero : Phi (P := P) 0 = id := by
  funext p
  exact phiFuel_zero _ p

theorem phiFuel_coordinatewise_le (fuel : Nat) (t : Real)
    (p : SubprobabilityVector P) : CoordinatewiseLE (phiFuel fuel t p) p :=
  run_value_coordinatewise_le fuel _

/-- Lemma `lem:basic-family(i)`, coordinatewise half. -/
theorem Phi_coordinatewise_le (t : Real) (p : SubprobabilityVector P) :
    CoordinatewiseLE (Phi t p) p :=
  phiFuel_coordinatewise_le _ t p

/-- Lemma `lem:basic-family(i)`, stochastic-order conclusion. -/
theorem Phi_le (t : Real) (p : SubprobabilityVector P) : Phi t p ≤ p :=
  stochasticLE_of_coordinatewise (Phi_coordinatewise_le t p)

/-- The fixed fuel in `Phi` really reaches a terminal state. -/
theorem Phi_run_done (t : Real) (p : SubprobabilityVector P) :
    (run (Fintype.card P + 1) { value := p, remaining := max t 0 }).Done := by
  apply run_done_of_support_card_lt
  · exact le_max_right _ _
  · have hs : (support p).card ≤ Fintype.card P := by
      simpa using Finset.card_le_card
        (show support p ⊆ Finset.univ from fun _ _ => Finset.mem_univ _)
    change (support p).card < Fintype.card P + 1
    omega

end Erosion

end FiniteValuationApproximable
