import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Order.UpperLower.CompleteLattice
import Mathlib.Tactic

/-!
# Finite subprobability valuations

This module formalizes the finite-dimensional valuation notation from the
preliminaries of `main (17).tex`, including Lemma `lem:monotone-integrals`.

Source version: SHA-256
`4b2e65f0f96347bea4df7571e8993ad6e888c0ff7181c1305c5056880365ac94`.

For a finite poset `P`, a subprobability valuation is represented by its
nonnegative atomic coefficients.  Its stochastic order is defined by comparing
the mass of every upper set; the integral characterization is then proved from
this definition.
-/

set_option autoImplicit false
set_option linter.unnecessarySimpa false

universe u

namespace FiniteValuationApproximable

open scoped BigOperators Classical
open Set

section Vectors

/-- The simplex `Delta_{<= 1}(P)` of nonnegative vectors of total mass at most
one.  These are exactly the atomic coefficient vectors used for finite
subprobability valuations in the source. -/
structure SubprobabilityVector (P : Type u) [Fintype P] where
  coeff : P -> Real
  coeff_nonneg : forall x, 0 <= coeff x
  total_le_one : (∑ x, coeff x) <= 1

namespace SubprobabilityVector

variable {P : Type u} [Fintype P]

instance : CoeFun (SubprobabilityVector P) (fun _ => P -> Real) where
  coe p := p.coeff

@[ext]
theorem ext {p q : SubprobabilityVector P}
    (h : forall x, p x = q x) : p = q := by
  cases p with
  | mk p hp hptotal =>
    cases q with
    | mk q hq hqtotal =>
      congr
      funext x
      exact h x

/-- Total atomic mass. -/
def totalMass (p : SubprobabilityVector P) : Real :=
  ∑ x, p x

/-- Mass of an arbitrary subset of the finite carrier. -/
noncomputable def mass (p : SubprobabilityVector P) (A : Set P) : Real := by
  classical
  exact ∑ x, if x ∈ A then p x else 0

@[simp]
theorem totalMass_eq_sum (p : SubprobabilityVector P) :
    p.totalMass = ∑ x, p x :=
  rfl

theorem totalMass_nonneg (p : SubprobabilityVector P) : 0 <= p.totalMass := by
  exact Finset.sum_nonneg fun x _ => p.coeff_nonneg x

theorem totalMass_le_one (p : SubprobabilityVector P) : p.totalMass <= 1 :=
  p.total_le_one

@[simp]
theorem mass_empty (p : SubprobabilityVector P) : p.mass (∅ : Set P) = 0 := by
  classical
  simp [mass]

@[simp]
theorem mass_univ (p : SubprobabilityVector P) : p.mass (Set.univ : Set P) = p.totalMass := by
  classical
  simp [mass, totalMass]

theorem mass_nonneg (p : SubprobabilityVector P) (A : Set P) : 0 <= p.mass A := by
  classical
  apply Finset.sum_nonneg
  intro x hx
  by_cases hxA : x ∈ A
  · simp [mass, hxA, p.coeff_nonneg x]
  · simp [mass, hxA]

theorem mass_mono (p : SubprobabilityVector P) {A B : Set P} (hAB : A ⊆ B) :
    p.mass A <= p.mass B := by
  classical
  apply Finset.sum_le_sum
  intro x hx
  by_cases hxA : x ∈ A
  · have hxB : x ∈ B := hAB hxA
    simp [mass, hxA, hxB]
  · by_cases hxB : x ∈ B
    · simp [mass, hxA, hxB, p.coeff_nonneg x]
    · simp [mass, hxA, hxB]

/-- The normalized simplex `Delta_1(P)`, represented as the total-mass-one
subtype of the subprobability simplex. -/
def ProbabilityVector (P : Type u) [Fintype P] :=
  {p : SubprobabilityVector P // p.totalMass = 1}

/-- The zero subprobability vector. -/
def zero : SubprobabilityVector P where
  coeff _ := 0
  coeff_nonneg _ := le_rfl
  total_le_one := by simp

instance : Zero (SubprobabilityVector P) :=
  ⟨zero⟩

@[simp]
theorem zero_apply (x : P) : (0 : SubprobabilityVector P) x = 0 := by
  change zero.coeff x = 0
  rfl

@[simp]
theorem totalMass_zero : (0 : SubprobabilityVector P).totalMass = 0 := by
  simp [totalMass]

@[simp]
theorem mass_zero (A : Set P) : (0 : SubprobabilityVector P).mass A = 0 := by
  classical
  simp [mass]

/-- The Dirac vector concentrated at `x`. -/
noncomputable def dirac (x : P) : SubprobabilityVector P where
  coeff y := if y = x then 1 else 0
  coeff_nonneg y := by
    by_cases hy : y = x <;> simp [hy]
  total_le_one := by
    classical
    simp

@[simp]
theorem dirac_apply (x y : P) : dirac x y = if y = x then 1 else 0 :=
  rfl

@[simp]
theorem totalMass_dirac (x : P) : (dirac x).totalMass = 1 := by
  classical
  simp [totalMass, dirac]

/-- The Dirac probability vector. -/
noncomputable def diracProbability (x : P) : ProbabilityVector P :=
  ⟨dirac x, totalMass_dirac x⟩

@[simp]
theorem mass_dirac (x : P) (A : Set P) :
    (dirac x).mass A = if x ∈ A then 1 else 0 := by
  classical
  unfold mass
  by_cases hx : x ∈ A
  · calc
      (∑ y, if y ∈ A then dirac x y else 0) =
          ∑ y, if y = x then (1 : Real) else 0 := by
            apply Finset.sum_congr rfl
            intro y hy
            by_cases hyx : y = x
            · subst y
              simp [hx]
            · simp [hyx]
      _ = 1 := by simp
      _ = (if x ∈ A then 1 else 0) := by simp [hx]
  · have hzero : forall y : P, (if y ∈ A then dirac x y else 0) = 0 := by
      intro y
      by_cases hyx : y = x
      · subst y
        simp [hx]
      · simp [dirac, hyx]
    rw [if_neg hx]
    exact Finset.sum_eq_zero fun y hy => hzero y

end SubprobabilityVector

end Vectors

section StochasticOrder

variable {P : Type u} [Fintype P] [PartialOrder P]

open SubprobabilityVector

/-- Mass evaluated on a bundled upper set. -/
noncomputable def upperMass (p : SubprobabilityVector P) (U : UpperSet P) : Real :=
  p.mass (U : Set P)

/-- The stochastic order from equation `eq:upper-set-order`: every upper-set
observation has no more mass under `p` than under `q`. -/
def StochasticLE (p q : SubprobabilityVector P) : Prop :=
  forall U : UpperSet P, upperMass p U <= upperMass q U

/-- The principal upper set generated by `x`. -/
def principalUpperSet (x : P) : UpperSet P :=
  ⟨Set.Ici x, isUpperSet_Ici x⟩

/-- The principal upper set generated by `x`, with `x` itself removed.  This is
still upper because antisymmetry prevents a point strictly above `x` from
returning to `x`. -/
def puncturedPrincipalUpperSet (x : P) : UpperSet P where
  carrier := Set.Ici x \ {x}
  upper' := by
    intro y z hyz hy
    refine ⟨le_trans hy.1 hyz, ?_⟩
    intro hzx
    subst z
    exact hy.2 (le_antisymm hyz hy.1)

/-- Atomic coefficient reconstruction from the two upper-set coordinates in
equation `eq:atomic-representation`. -/
theorem upperMass_principal_sub_punctured
    (p : SubprobabilityVector P) (x : P) :
    upperMass p (principalUpperSet x) -
        upperMass p (puncturedPrincipalUpperSet x) = p x := by
  classical
  simp only [upperMass, SubprobabilityVector.mass, principalUpperSet,
    puncturedPrincipalUpperSet, UpperSet.coe_mk, Set.mem_Ici, Set.mem_diff,
    Set.mem_singleton_iff]
  rw [← Finset.sum_sub_distrib]
  calc
    (∑ y, ((if x <= y then p y else 0) -
        (if x <= y ∧ y ≠ x then p y else 0))) =
        ∑ y, if y = x then p y else 0 := by
          apply Finset.sum_congr rfl
          intro y hy
          by_cases hyx : y = x
          · subst y
            simp
          · by_cases hxy : x <= y
            · simp [hyx, hxy]
            · simp [hyx, hxy]
    _ = p x := by simp

/-- Antisymmetry of stochastic comparison, obtained by reconstructing every
atomic coefficient from principal upper-set masses. -/
theorem stochasticLE_antisymm {p q : SubprobabilityVector P}
    (hpq : StochasticLE p q) (hqp : StochasticLE q p) : p = q := by
  apply SubprobabilityVector.ext
  intro x
  have hprincipal :
      upperMass p (principalUpperSet x) = upperMass q (principalUpperSet x) :=
    le_antisymm (hpq (principalUpperSet x)) (hqp (principalUpperSet x))
  have hpunctured :
      upperMass p (puncturedPrincipalUpperSet x) =
        upperMass q (puncturedPrincipalUpperSet x) :=
    le_antisymm (hpq (puncturedPrincipalUpperSet x))
      (hqp (puncturedPrincipalUpperSet x))
  have hp := upperMass_principal_sub_punctured p x
  have hq := upperMass_principal_sub_punctured q x
  linarith

instance : PartialOrder (SubprobabilityVector P) where
  le := StochasticLE
  le_refl p U := le_rfl
  le_trans p q r hpq hqr U := le_trans (hpq U) (hqr U)
  le_antisymm p q := stochasticLE_antisymm

theorem stochasticLE_def {p q : SubprobabilityVector P} :
    p <= q <-> forall U : UpperSet P, upperMass p U <= upperMass q U :=
  Iff.rfl

theorem zero_le (p : SubprobabilityVector P) :
    (0 : SubprobabilityVector P) <= p := by
  intro U
  simpa [upperMass] using p.mass_nonneg (U : Set P)

instance : OrderBot (SubprobabilityVector P) where
  bot := 0
  bot_le := zero_le

/-- The finite sum representing integration of `g` against an atomic vector. -/
def weightedSum (p : SubprobabilityVector P) (g : P -> Real) : Real :=
  ∑ x, p x * g x

@[simp]
theorem weightedSum_dirac (x : P) (g : P -> Real) :
    weightedSum (dirac x) g = g x := by
  classical
  simp [weightedSum, dirac]

private noncomputable def positiveSupport (g : P -> Real) : Finset P := by
  classical
  exact Finset.univ.filter fun x => 0 < g x

private theorem weightedSum_le_of_stochasticLE
    {p q : SubprobabilityVector P} (hpq : p <= q)
    (g : P -> Real) (hg : Monotone g) (hg0 : forall x, 0 <= g x) :
    weightedSum p g <= weightedSum q g := by
  classical
  by_cases hsupport : (positiveSupport g).Nonempty
  · let values : Finset Real := (positiveSupport g).image g
    have hvalues : values.Nonempty := hsupport.image g
    let t : Real := values.min' hvalues
    have ht_mem : t ∈ values := Finset.min'_mem values hvalues
    obtain ⟨x0, hx0_support, hx0_value⟩ := Finset.mem_image.mp ht_mem
    have hx0_pos : 0 < g x0 := (Finset.mem_filter.mp hx0_support).2
    have ht_pos : 0 < t := by simpa [hx0_value] using hx0_pos
    have ht_le {x : P} (hx : 0 < g x) : t <= g x := by
      apply Finset.min'_le values (g x)
      exact Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx⟩, rfl⟩
    let U : UpperSet P :=
      { carrier := {x | 0 < g x}
        upper' := by
          intro x y hxy hx
          exact lt_of_lt_of_le hx (hg hxy) }
    let residual : P -> Real := fun x => max (g x - t) 0
    have hresidual_nonneg : forall x, 0 <= residual x := by
      intro x
      exact le_max_right _ _
    have hresidual_mono : Monotone residual := by
      intro x y hxy
      exact max_le_max (sub_le_sub_right (hg hxy) t) le_rfl
    have hsupport_subset : positiveSupport residual ⊆ positiveSupport g := by
      intro x hx
      have hxres : 0 < residual x := (Finset.mem_filter.mp hx).2
      have hxg : 0 < g x := by
        by_contra hnot
        have hg_nonpos : g x <= 0 := le_of_not_gt hnot
        have hsub_nonpos : g x - t <= 0 := by linarith
        have : residual x = 0 := by simp [residual, max_eq_right hsub_nonpos]
        linarith
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, hxg⟩
    have hx0_not_residual : x0 ∉ positiveSupport residual := by
      have hresidual_x0 : residual x0 = 0 := by
        simp [residual, hx0_value]
      simp [positiveSupport, hresidual_x0]
    have hsupport_ne : positiveSupport residual ≠ positiveSupport g := by
      intro heq
      have : x0 ∈ positiveSupport residual := by simpa [heq] using hx0_support
      exact hx0_not_residual this
    have hsupport_lt : (positiveSupport residual).card < (positiveSupport g).card :=
      Finset.card_lt_card
        (Finset.ssubset_iff_subset_ne.mpr ⟨hsupport_subset, hsupport_ne⟩)
    have hrec : weightedSum p residual <= weightedSum q residual :=
      weightedSum_le_of_stochasticLE hpq residual hresidual_mono hresidual_nonneg
    have hmass : upperMass p U <= upperMass q U := hpq U
    have ht_nonneg : 0 <= t := le_of_lt ht_pos
    have decompose (r : SubprobabilityVector P) :
        weightedSum r g = weightedSum r residual + t * upperMass r U := by
      simp only [weightedSum, upperMass, SubprobabilityVector.mass]
      rw [Finset.mul_sum]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro x hx
      by_cases hxg : 0 < g x
      · have htx : t <= g x := ht_le hxg
        simp [U, residual, hxg, max_eq_left (sub_nonneg.mpr htx)]
        ring
      · have hgx : g x = 0 := le_antisymm (le_of_not_gt hxg) (hg0 x)
        simp [U, residual, hxg, hgx, ht_nonneg]
    calc
      weightedSum p g = weightedSum p residual + t * upperMass p U := decompose p
      _ <= weightedSum q residual + t * upperMass q U :=
        add_le_add hrec (mul_le_mul_of_nonneg_left hmass ht_nonneg)
      _ = weightedSum q g := (decompose q).symm
  · have hg_zero : forall x, g x = 0 := by
      intro x
      have hx_not_pos : ¬ 0 < g x := by
        intro hx
        exact hsupport ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx⟩⟩
      exact le_antisymm (le_of_not_gt hx_not_pos) (hg0 x)
    simp [weightedSum, hg_zero]
termination_by (positiveSupport g).card
decreasing_by exact hsupport_lt

/-- Lemma `lem:monotone-integrals`: stochastic comparison on upper sets is
equivalent to comparison of all nonnegative monotone finite integrals. -/
theorem stochasticLE_iff_weightedSum_le {p q : SubprobabilityVector P} :
    p <= q <->
      forall g : P -> Real, Monotone g -> (forall x, 0 <= g x) ->
        weightedSum p g <= weightedSum q g := by
  constructor
  · intro hpq g hg hg0
    exact weightedSum_le_of_stochasticLE hpq g hg hg0
  · intro hint U
    let indicator : P -> Real := fun x => if x ∈ U.carrier then 1 else 0
    have hindicator_nonneg : forall x, 0 <= indicator x := by
      intro x
      dsimp only [indicator]
      by_cases hx : x ∈ U.carrier
      · rw [if_pos hx]
        norm_num
      · rw [if_neg hx]
    have hindicator_mono : Monotone indicator := by
      intro x y hxy
      dsimp only [indicator]
      by_cases hx : x ∈ U.carrier
      · have hy : y ∈ U.carrier := U.upper hxy hx
        rw [if_pos hx, if_pos hy]
      · rw [if_neg hx]
        by_cases hy : y ∈ U.carrier
        · rw [if_pos hy]
          norm_num
        · rw [if_neg hy]
    simpa [weightedSum, upperMass, SubprobabilityVector.mass, indicator] using
      hint indicator hindicator_mono hindicator_nonneg

/-- Dirac vectors embed the underlying finite poset into its stochastic
preorder. -/
theorem dirac_le_dirac_iff {x y : P} :
    dirac x <= dirac y <-> x <= y := by
  constructor
  · intro hxy
    let U : UpperSet P := ⟨Set.Ici x, isUpperSet_Ici x⟩
    have hmass := hxy U
    by_cases hle : x <= y
    · exact hle
    · have : (1 : Real) <= 0 := by
        simpa [upperMass, U, hle] using hmass
      linarith
  · intro hxy U
    by_cases hxU : x ∈ (U : Set P)
    · have hyU : y ∈ (U : Set P) := U.upper hxy hxU
      simp [upperMass, hxU, hyU]
    · by_cases hyU : y ∈ (U : Set P) <;> simp [upperMass, hxU, hyU]

end StochasticOrder

end FiniteValuationApproximable
