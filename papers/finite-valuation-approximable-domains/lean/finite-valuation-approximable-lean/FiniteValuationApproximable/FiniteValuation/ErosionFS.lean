import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Order.ScottContinuity
import FiniteValuationApproximable.FiniteValuation.Erosion

/-!
# Exact recursive flow and FS consequences

This continuation isolates the semigroup, order-preservation, and finite
separation layer from the finite combinatorial implementation in
`FiniteValuation.Erosion`.

Source version: SHA-256
`4b2e65f0f96347bea4df7571e8993ad6e888c0ff7181c1305c5056880365ac94`.

All flow, comparison, estimate, and finite-separation results below are
unconditional.  Scott continuity and the explicit FS approximate identity
retain `DirectedUpperMassApproximation` as a visible premise, matching the
standard pointwise-directed-supremum fact cited (rather than proved) in the
manuscript.
-/

set_option autoImplicit false

universe u

namespace FiniteValuationApproximable.Erosion

open scoped Classical

variable {P : Type u} [Fintype P] [PartialOrder P]

/-- Every active-set coefficient is at least one. -/
theorem one_le_coefficient (A : Finset P) : 1 ≤ coefficient A := by
  unfold coefficient coefficientNat
  norm_cast
  exact Nat.one_le_pow _ _ (by omega)

/-- The uniform finite-poset loss constant `K_P = n (n+1)^(n-1)`. -/
noncomputable def erosionConstant : Real :=
  Fintype.card P * (Fintype.card P + 1) ^ (Fintype.card P - 1)

/-- The coefficient bound used in the lower upper-set estimate. -/
theorem coefficient_le_uniform_scale {A : Finset P} (hA : A.Nonempty) :
    coefficient A ≤
      (((Fintype.card P + 1) ^ (Fintype.card P - 1) : Nat) : Real) := by
  unfold coefficient coefficientNat
  norm_cast
  apply Nat.pow_le_pow_right (by omega)
  obtain ⟨a, ha⟩ := hA
  have hclosure : (lowerClosure A).Nonempty :=
    ⟨a, mem_lowerClosure.mpr ⟨a, ha, le_rfl⟩⟩
  have hpositive : 0 < (lowerClosure A).card := Finset.card_pos.mpr hclosure
  omega

/-- A positive upper-set mass has instantaneous erosion rate at least one. -/
theorem one_le_gamma_of_upperMass_pos {p : SubprobabilityVector P}
    (U : UpperSet P) (hmass : 0 < upperMass p U) : 1 ≤ gamma U p := by
  have hp : p ≠ 0 := by
    intro hpzero
    subst p
    simpa [upperMass] using hmass
  obtain ⟨a, haA, haU⟩ := lem_max_support_meets_upper p U hmass
  have haI : a ∈ frontierIn p U := mem_frontierIn.mpr ⟨haA, haU⟩
  have hcardNat : 1 ≤ (frontierIn p U).card :=
    Finset.one_le_card.mpr ⟨a, haI⟩
  have hcard : (1 : Real) ≤ (frontierIn p U).card := by
    exact_mod_cast hcardNat
  rw [gamma_eq_of_ne_zero hp U]
  calc
    (1 : Real) ≤ coefficient (frontier p) * 1 := by
      simpa using one_le_coefficient (frontier p)
    _ ≤ coefficient (frontier p) * (frontierIn p U).card :=
      mul_le_mul_of_nonneg_left hcard (le_of_lt (coefficient_pos (frontier p)))

/-- Every instantaneous upper-set loss rate is bounded by `K_P`. -/
theorem gamma_le_erosionConstant {p : SubprobabilityVector P} (hp : p ≠ 0)
    (U : UpperSet P) : gamma U p ≤ erosionConstant (P := P) := by
  have hfrontier : (frontier p).Nonempty := frontier_nonempty_of_ne_zero hp
  have hcoeff := coefficient_le_uniform_scale hfrontier
  have hcardNat : (frontierIn p U).card ≤ Fintype.card P := by
    simpa using Finset.card_le_card
      (show frontierIn p U ⊆ Finset.univ from fun _ _ => Finset.mem_univ _)
  have hcard : ((frontierIn p U).card : Real) ≤ Fintype.card P := by
    exact_mod_cast hcardNat
  rw [gamma_eq_of_ne_zero hp U]
  calc
    coefficient (frontier p) * (frontierIn p U).card ≤
        (((Fintype.card P + 1) ^ (Fintype.card P - 1) : Nat) : Real) *
          (frontierIn p U).card :=
      mul_le_mul_of_nonneg_right hcoeff (Nat.cast_nonneg _)
    _ ≤ (((Fintype.card P + 1) ^ (Fintype.card P - 1) : Nat) : Real) *
          Fintype.card P :=
      mul_le_mul_of_nonneg_left hcard (Nat.cast_nonneg _)
    _ = erosionConstant (P := P) := by
      norm_num [erosionConstant]
      ring

/-- The source recursion `phi_p(t)`, defined by well-founded recursion on the
cardinality of the positive support. -/
noncomputable def exactPhi (t : Real) (p : SubprobabilityVector P) :
    SubprobabilityVector P :=
  if ht : t ≤ 0 then p
  else if hp : p = 0 then 0
  else if hsmall : t ≤ stageTime p then erodeBy p t
  else exactPhi (t - stageTime p) (erodeBy p (stageTime p))
termination_by (support p).card
decreasing_by
  exact Finset.card_lt_card (support_erodeBy_stageTime_ssubset hp)

@[simp]
theorem exactPhi_of_nonpos {t : Real} (p : SubprobabilityVector P) (ht : t ≤ 0) :
    exactPhi t p = p := by
  rw [exactPhi]
  simp [ht]

@[simp]
theorem exactPhi_zero (t : Real) :
    exactPhi (P := P) t 0 = 0 := by
  by_cases ht : t ≤ 0
  · rw [exactPhi_of_nonpos 0 ht]
  · rw [exactPhi]
    simp [ht]

theorem exactPhi_of_pos_le_stage {t : Real} {p : SubprobabilityVector P}
    (ht : 0 < t) (hp : p ≠ 0) (hstage : t ≤ stageTime p) :
    exactPhi t p = erodeBy p t := by
  rw [exactPhi]
  simp [not_le.mpr ht, hp, hstage]

theorem exactPhi_of_stage_lt {t : Real} {p : SubprobabilityVector P}
    (ht : stageTime p < t) (hp : p ≠ 0) :
    exactPhi t p =
      exactPhi (t - stageTime p) (erodeBy p (stageTime p)) := by
  have htpos : 0 < t := (stageTime_pos_of_ne_zero hp).trans ht
  rw [exactPhi]
  simp [not_le.mpr htpos, hp, not_le.mpr ht]

theorem exactPhi_coordinatewise_le (t : Real) (p : SubprobabilityVector P) :
    CoordinatewiseLE (exactPhi t p) p := by
  by_cases ht : t ≤ 0
  · rw [exactPhi_of_nonpos p ht]
    exact CoordinatewiseLE.refl p
  · by_cases hp : p = 0
    · subst p
      rw [exactPhi_zero]
      exact CoordinatewiseLE.refl 0
    · by_cases hsmall : t ≤ stageTime p
      · rw [exactPhi_of_pos_le_stage (lt_of_not_ge ht) hp hsmall]
        exact erodeBy_coordinatewise_le p t
      · rw [exactPhi_of_stage_lt (lt_of_not_ge hsmall) hp]
        exact (exactPhi_coordinatewise_le (t - stageTime p)
          (erodeBy p (stageTime p))).trans
            (erodeBy_coordinatewise_le p (stageTime p))
termination_by (support p).card
decreasing_by
  exact Finset.card_lt_card (support_erodeBy_stageTime_ssubset hp)

theorem exactPhi_le (t : Real) (p : SubprobabilityVector P) : exactPhi t p ≤ p :=
  stochasticLE_of_coordinatewise (exactPhi_coordinatewise_le t p)

/-- Translation inside one recursive interval. -/
theorem exactPhi_erodeBy {p : SubprobabilityVector P} (hp : p ≠ 0)
    {t s : Real} (ht0 : 0 ≤ t) (hs0 : 0 ≤ s) (ht : t < stageTime p) :
    exactPhi s (erodeBy p t) = exactPhi (t + s) p := by
  by_cases htzero : t = 0
  · subst t
    simp
  have htpos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm htzero)
  by_cases hszero : s = 0
  · subst s
    rw [exactPhi_of_nonpos _ le_rfl, add_zero,
      exactPhi_of_pos_le_stage htpos hp (le_of_lt ht)]
  have hspos : 0 < s := lt_of_le_of_ne hs0 (Ne.symm hszero)
  have hr0 : erodeBy p t ≠ 0 := erodeBy_ne_zero_of_lt hp ht0 ht
  have hstage : stageTime (erodeBy p t) = stageTime p - t :=
    stageTime_erodeBy hp ht0 ht
  by_cases hs : s ≤ stageTime (erodeBy p t)
  · rw [exactPhi_of_pos_le_stage hspos hr0 hs]
    have hsum : t + s ≤ stageTime p := by linarith
    rw [exactPhi_of_pos_le_stage (by linarith) hp hsum]
    exact erodeBy_add hp ht0 hs0 hsum
  · have hslarge : stageTime (erodeBy p t) < s := lt_of_not_ge hs
    have htotal_large : stageTime p < t + s := by linarith
    rw [exactPhi_of_stage_lt hslarge hr0,
      exactPhi_of_stage_lt htotal_large hp]
    have hk0 : 0 ≤ stageTime p - t := by linarith
    have hstep0 := erodeBy_add hp ht0 hk0
      (show t + (stageTime p - t) ≤ stageTime p by linarith)
    have hstep :
        erodeBy (erodeBy p t) (stageTime (erodeBy p t)) =
          erodeBy p (stageTime p) := by
      rw [hstage]
      convert hstep0 using 1 <;> ring
    rw [hstep]
    congr 1
    rw [hstage]
    ring

/-- Lemma `lem:basic-family(ii)`: the exact erosion flow is a semigroup. -/
theorem exactPhi_add (p : SubprobabilityVector P) {s t : Real}
    (hs0 : 0 ≤ s) (ht0 : 0 ≤ t) :
    exactPhi (s + t) p = exactPhi s (exactPhi t p) := by
  by_cases htzero : t = 0
  · subst t
    simp
  have htpos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm htzero)
  by_cases hp : p = 0
  · subst p
    simp
  by_cases hlt : t < stageTime p
  · rw [exactPhi_of_pos_le_stage htpos hp (le_of_lt hlt)]
    have htail := exactPhi_erodeBy hp ht0 hs0 hlt
    simpa [add_comm] using htail.symm
  have hstage_le : stageTime p ≤ t := le_of_not_gt hlt
  by_cases heq : t = stageTime p
  · subst t
    rw [exactPhi_of_pos_le_stage (stageTime_pos_of_ne_zero hp) hp le_rfl]
    by_cases hszero : s = 0
    · subst s
      rw [exactPhi_of_nonpos _ le_rfl]
      simpa using
        (exactPhi_of_pos_le_stage (stageTime_pos_of_ne_zero hp) hp le_rfl)
    · have hspos : 0 < s := lt_of_le_of_ne hs0 (Ne.symm hszero)
      rw [exactPhi_of_stage_lt (by linarith) hp]
      congr 1
      ring
  · have hlarge : stageTime p < t := lt_of_le_of_ne hstage_le (Ne.symm heq)
    rw [exactPhi_of_stage_lt (hlarge.trans_le (le_add_of_nonneg_left hs0)) hp,
      exactPhi_of_stage_lt hlarge hp]
    have ih := exactPhi_add (erodeBy p (stageTime p)) hs0
      (sub_nonneg.mpr hstage_le)
    convert ih using 1 <;> ring
termination_by (support p).card
decreasing_by
  exact Finset.card_lt_card (support_erodeBy_stageTime_ssubset hp)

/-- Lemma `lem:basic-family(i)` at time zero. -/
@[simp]
theorem exactPhi_time_zero (p : SubprobabilityVector P) : exactPhi 0 p = p :=
  exactPhi_of_nonpos p le_rfl

/-- Increasing the erosion time can only decrease every coefficient. -/
theorem exactPhi_antitone_time_coordinatewise (p : SubprobabilityVector P)
    {s t : Real} (ht0 : 0 ≤ t) (hts : t ≤ s) :
    CoordinatewiseLE (exactPhi s p) (exactPhi t p) := by
  have hu0 : 0 ≤ s - t := sub_nonneg.mpr hts
  rw [show s = (s - t) + t by ring, exactPhi_add p hu0 ht0]
  exact exactPhi_coordinatewise_le (s - t) (exactPhi t p)

/-- Lemma `lem:basic-family(iii)`: the erosion flow is antitone in time. -/
theorem exactPhi_antitone_time (p : SubprobabilityVector P)
    {s t : Real} (ht0 : 0 ≤ t) (hts : t ≤ s) :
    exactPhi s p ≤ exactPhi t p :=
  stochasticLE_of_coordinatewise
    (exactPhi_antitone_time_coordinatewise p ht0 hts)

/-- Lemma `lem:local-upper-formula`: after any time `s`, upper-set mass is
affine on a nontrivial right neighborhood, with slope `-gamma`. -/
theorem exactPhi_local_upper_formula (p : SubprobabilityVector P)
    (U : UpperSet P) {s : Real} (hs0 : 0 ≤ s) :
    ∃ η : Real, 0 < η ∧ ∀ h : Real, 0 ≤ h → h ≤ η →
      upperMass (exactPhi (s + h) p) U =
        upperMass (exactPhi s p) U - h * gamma U (exactPhi s p) := by
  by_cases hq : exactPhi s p = 0
  · refine ⟨1, zero_lt_one, ?_⟩
    intro h hh0 hh1
    rw [show s + h = h + s by ring, exactPhi_add p hh0 hs0, hq,
      exactPhi_zero]
    simp [hq, gamma, upperMass]
  · refine ⟨stageTime (exactPhi s p), stageTime_pos_of_ne_zero hq, ?_⟩
    intro h hh0 hhstage
    rw [show s + h = h + s by ring, exactPhi_add p hh0 hs0]
    by_cases hhzero : h = 0
    · subst h
      simp
    · have hhpos : 0 < h := lt_of_le_of_ne hh0 (Ne.symm hhzero)
      rw [exactPhi_of_pos_le_stage hhpos hq hhstage,
        upperMass_erodeBy U hq hh0 hhstage]

/-- The loss rate is constant strictly inside one recursive interval. -/
theorem gamma_erodeBy {p : SubprobabilityVector P} (hp : p ≠ 0)
    (U : UpperSet P) {h : Real} (hh0 : 0 ≤ h) (hht : h < stageTime p) :
    gamma U (erodeBy p h) = gamma U p := by
  have hr : erodeBy p h ≠ 0 := erodeBy_ne_zero_of_lt hp hh0 hht
  have hf : frontier (erodeBy p h) = frontier p :=
    frontier_erodeBy_eq hp hh0 hht
  rw [gamma_eq_of_ne_zero hr U, gamma_eq_of_ne_zero hp U]
  simp [frontierIn, hf]

@[simp]
theorem erodeBy_zero_vector (h : Real) :
    erodeBy (0 : SubprobabilityVector P) h = 0 := by
  apply SubprobabilityVector.ext
  intro x
  simp [erodeBy_apply, frontier, support]

/-- Shift the exact recursion by any time contained in its first interval. -/
theorem exactPhi_shift_within_stage {p : SubprobabilityVector P} (hp : p ≠ 0)
    {a t : Real} (ha0 : 0 ≤ a) (ha : a ≤ stageTime p) (hat : a < t) :
    exactPhi t p = exactPhi (t - a) (erodeBy p a) := by
  by_cases halt : a < stageTime p
  · have hrem0 : 0 ≤ t - a := sub_nonneg.mpr (le_of_lt hat)
    have htail := exactPhi_erodeBy hp ha0 hrem0 halt
    symm
    convert htail using 1 <;> ring
  · have hae : a = stageTime p := le_antisymm ha (le_of_not_gt halt)
    subst a
    exact exactPhi_of_stage_lt hat hp

/-- On a common recursive interval, the erosion update preserves stochastic
order.  The proof selects the earliest possible crossing among the finite
family of upper sets and rules it out by `lem_boundary_comparison`. -/
theorem erodeBy_mono_common_stage {p q : SubprobabilityVector P}
    (hpq : p ≤ q) {h : Real} (hh0 : 0 ≤ h)
    (hpstage : h ≤ stageTime p) (hqstage : h ≤ stageTime q) :
    erodeBy p h ≤ erodeBy q h := by
  by_cases hpzero : p = 0
  · subst p
    rw [erodeBy_zero_vector]
    exact bot_le
  by_cases hqzero : q = 0
  · subst q
    have hpzero' : p = 0 := le_antisymm hpq bot_le
    exact (hpzero hpzero').elim
  intro U
  rw [upperMass_erodeBy U hpzero hh0 hpstage,
    upperMass_erodeBy U hqzero hh0 hqstage]
  let gap : UpperSet P → Real := fun V => upperMass q V - upperMass p V
  let slope : UpperSet P → Real := fun V => gamma V p - gamma V q
  have hgap (V : UpperSet P) : 0 ≤ gap V := by
    exact sub_nonneg.mpr (hpq V)
  suffices hnonneg : 0 ≤ gap U + h * slope U by
    dsimp only [gap, slope] at hnonneg
    linarith
  by_contra hcross
  have hnegative : gap U + h * slope U < 0 := lt_of_not_ge hcross
  have hslopeU : slope U < 0 := by
    by_contra hs
    have hs0 : 0 ≤ slope U := le_of_not_gt hs
    have := add_nonneg (hgap U) (mul_nonneg hh0 hs0)
    linarith
  let bad : Finset (UpperSet P) := Finset.univ.filter fun V => slope V < 0
  have hUbad : U ∈ bad := by simp [bad, hslopeU]
  have hbad : bad.Nonempty := ⟨U, hUbad⟩
  let crossing : UpperSet P → Real := fun V => gap V / (-slope V)
  let times : Finset Real := bad.image crossing
  have htimes : times.Nonempty := hbad.image crossing
  let c : Real := times.min' htimes
  have hcmem : c ∈ times := Finset.min'_mem times htimes
  obtain ⟨W, hWbad, hWcross⟩ := Finset.mem_image.mp hcmem
  have hslopeW : slope W < 0 := (Finset.mem_filter.mp hWbad).2
  have hdenW : 0 < -slope W := by linarith
  have hcrossW0 : 0 ≤ crossing W := div_nonneg (hgap W) (le_of_lt hdenW)
  have hc0 : 0 ≤ c := by simpa [hWcross] using hcrossW0
  have hUtime : crossing U ∈ times :=
    Finset.mem_image.mpr ⟨U, hUbad, rfl⟩
  have hcleU : c ≤ crossing U := Finset.min'_le times (crossing U) hUtime
  have hcrossUlt : crossing U < h := by
    apply (div_lt_iff₀ (show 0 < -slope U by linarith)).2
    dsimp only [crossing]
    nlinarith
  have hclt : c < h := hcleU.trans_lt hcrossUlt
  have hcpstage : c < stageTime p := hclt.trans_le hpstage
  have hcqstage : c < stageTime q := hclt.trans_le hqstage
  have hall (V : UpperSet P) : 0 ≤ gap V + c * slope V := by
    by_cases hs : slope V < 0
    · have hVbad : V ∈ bad := by simp [bad, hs]
      have hVtime : crossing V ∈ times :=
        Finset.mem_image.mpr ⟨V, hVbad, rfl⟩
      have hcleV : c ≤ crossing V := Finset.min'_le times (crossing V) hVtime
      have hdenV : 0 < -slope V := by linarith
      have hmul : c * (-slope V) ≤ gap V := by
        exact (le_div_iff₀ hdenV).mp (by simpa [crossing] using hcleV)
      nlinarith
    · have hs0 : 0 ≤ slope V := le_of_not_gt hs
      exact add_nonneg (hgap V) (mul_nonneg hc0 hs0)
  have hpcq : erodeBy p c ≤ erodeBy q c := by
    intro V
    have hpformula := upperMass_erodeBy V hpzero hc0 (le_of_lt hcpstage)
    have hqformula := upperMass_erodeBy V hqzero hc0 (le_of_lt hcqstage)
    have hV := hall V
    dsimp only [gap, slope] at hV
    linarith
  have hzeroW : gap W + c * slope W = 0 := by
    rw [← hWcross]
    dsimp only [crossing]
    calc
      gap W + gap W / -slope W * slope W =
          gap W - (gap W / -slope W) * (-slope W) := by ring
      _ = 0 := by
        rw [div_mul_cancel₀ _ (ne_of_gt hdenW)]
        ring
  have heqW :
      upperMass (erodeBy p c) W = upperMass (erodeBy q c) W := by
    have hpformula := upperMass_erodeBy W hpzero hc0 (le_of_lt hcpstage)
    have hqformula := upperMass_erodeBy W hqzero hc0 (le_of_lt hcqstage)
    dsimp only [gap, slope] at hzeroW
    linarith
  have hboundary := lem_boundary_comparison hpcq W heqW
  rw [gamma_erodeBy hpzero W hc0 hcpstage,
    gamma_erodeBy hqzero W hc0 hcqstage] at hboundary
  dsimp only [slope] at hslopeW
  linarith

/-- Theorem `thm:order-preservation`: every exact erosion map preserves the
stochastic order. -/
theorem exactPhi_mono {p q : SubprobabilityVector P} (hpq : p ≤ q)
    {t : Real} (ht0 : 0 ≤ t) : exactPhi t p ≤ exactPhi t q := by
  by_cases htzero : t = 0
  · subst t
    simpa using hpq
  have htpos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm htzero)
  by_cases hpzero : p = 0
  · subst p
    rw [exactPhi_zero]
    exact bot_le
  by_cases hqzero : q = 0
  · subst q
    have hpzero' : p = 0 := le_antisymm hpq bot_le
    exact (hpzero hpzero').elim
  let d : Real := min (stageTime p) (stageTime q)
  have hdpos : 0 < d :=
    lt_min (stageTime_pos_of_ne_zero hpzero) (stageTime_pos_of_ne_zero hqzero)
  have hdp : d ≤ stageTime p := min_le_left _ _
  have hdq : d ≤ stageTime q := min_le_right _ _
  by_cases hsmall : t ≤ d
  · rw [exactPhi_of_pos_le_stage htpos hpzero (hsmall.trans hdp),
      exactPhi_of_pos_le_stage htpos hqzero (hsmall.trans hdq)]
    exact erodeBy_mono_common_stage hpq ht0 (hsmall.trans hdp) (hsmall.trans hdq)
  · have hdt : d < t := lt_of_not_ge hsmall
    have hd0 : 0 ≤ d := le_of_lt hdpos
    have hstep : erodeBy p d ≤ erodeBy q d :=
      erodeBy_mono_common_stage hpq hd0 hdp hdq
    have ih := exactPhi_mono hstep (sub_nonneg.mpr (le_of_lt hdt))
    rw [exactPhi_shift_within_stage hpzero hd0 hdp hdt,
      exactPhi_shift_within_stage hqzero hd0 hdq hdt]
    exact ih
termination_by (support p).card + (support q).card
decreasing_by
  by_cases hpqtime : stageTime p ≤ stageTime q
  · have hpstrict :
        (support (erodeBy p (min (stageTime p) (stageTime q)))).card <
          (support p).card := by
      rw [min_eq_left hpqtime]
      exact Finset.card_lt_card (support_erodeBy_stageTime_ssubset hpzero)
    have hqweak :
        (support (erodeBy q (min (stageTime p) (stageTime q)))).card ≤
          (support q).card :=
      Finset.card_le_card (support_erodeBy_subset q _)
    omega
  · have hqptime : stageTime q ≤ stageTime p :=
      le_of_lt (lt_of_not_ge hpqtime)
    have hpweak :
        (support (erodeBy p (min (stageTime p) (stageTime q)))).card ≤
          (support p).card :=
      Finset.card_le_card (support_erodeBy_subset p _)
    have hqstrict :
        (support (erodeBy q (min (stageTime p) (stageTime q)))).card <
          (support q).card := by
      rw [min_eq_right hqptime]
      exact Finset.card_lt_card (support_erodeBy_stageTime_ssubset hqzero)
    omega

theorem erosionConstant_nonneg : 0 ≤ erosionConstant (P := P) := by
  unfold erosionConstant
  exact mul_nonneg (Nat.cast_nonneg _)
    (pow_nonneg (add_nonneg (Nat.cast_nonneg _) zero_le_one) _)

/-- Positive terminal mass forces loss at speed at least one on every
recursive interval crossed by the trajectory. -/
theorem exactPhi_upperMass_sub_if_pos (p : SubprobabilityVector P)
    (U : UpperSet P) {t : Real} (ht0 : 0 ≤ t)
    (hfinal : 0 < upperMass (exactPhi t p) U) :
    upperMass (exactPhi t p) U ≤ upperMass p U - t := by
  have hinitial : 0 < upperMass p U :=
    lt_of_lt_of_le hfinal ((exactPhi_le t p) U)
  by_cases htzero : t = 0
  · subst t
    simp
  have htpos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm htzero)
  by_cases hp : p = 0
  · subst p
    simp [upperMass] at hinitial
  by_cases hsmall : t ≤ stageTime p
  · rw [exactPhi_of_pos_le_stage htpos hp hsmall,
      upperMass_erodeBy U hp ht0 hsmall]
    have hgamma : 1 ≤ gamma U p := one_le_gamma_of_upperMass_pos U hinitial
    nlinarith
  · have hlarge : stageTime p < t := lt_of_not_ge hsmall
    have hstage0 : 0 ≤ stageTime p := le_of_lt (stageTime_pos_of_ne_zero hp)
    have hrem0 : 0 ≤ t - stageTime p := sub_nonneg.mpr (le_of_lt hlarge)
    have hfinal' :
        0 < upperMass
          (exactPhi (t - stageTime p) (erodeBy p (stageTime p))) U := by
      simpa [exactPhi_of_stage_lt hlarge hp] using hfinal
    have ih := exactPhi_upperMass_sub_if_pos
      (erodeBy p (stageTime p)) U hrem0 hfinal'
    have hstage := upperMass_erodeBy U hp hstage0 le_rfl
    have hgamma : 1 ≤ gamma U p := one_le_gamma_of_upperMass_pos U hinitial
    have hloss : stageTime p ≤ stageTime p * gamma U p := by
      nlinarith
    rw [exactPhi_of_stage_lt hlarge hp]
    linarith
termination_by (support p).card
decreasing_by
  exact Finset.card_lt_card (support_erodeBy_stageTime_ssubset hp)

/-- Lemma `lem:upper-set-estimate`. -/
theorem exactPhi_upperMass_estimate (p : SubprobabilityVector P)
    (U : UpperSet P) {t : Real} (ht0 : 0 ≤ t) :
    upperMass (exactPhi t p) U ≤ max (upperMass p U - t) 0 := by
  by_cases hzero : upperMass (exactPhi t p) U = 0
  · rw [hzero]
    exact le_max_right _ _
  · have hnonneg : 0 ≤ upperMass (exactPhi t p) U := by
      simpa [upperMass] using (exactPhi t p).mass_nonneg (U : Set P)
    have hpos : 0 < upperMass (exactPhi t p) U :=
      lt_of_le_of_ne hnonneg (Ne.symm hzero)
    have hraw := exactPhi_upperMass_sub_if_pos p U ht0 hpos
    have hsub0 : 0 ≤ upperMass p U - t := le_trans hnonneg hraw
    rw [max_eq_left hsub0]
    exact hraw

/-- Uniform loss over the whole finite recursion is at most `K_P t`. -/
theorem exactPhi_lowerMass_sub (p : SubprobabilityVector P)
    (U : UpperSet P) {t : Real} (ht0 : 0 ≤ t) :
    upperMass p U - erosionConstant (P := P) * t ≤
      upperMass (exactPhi t p) U := by
  by_cases htzero : t = 0
  · subst t
    simp
  have htpos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm htzero)
  by_cases hp : p = 0
  · subst p
    rw [exactPhi_zero]
    have hK := erosionConstant_nonneg (P := P)
    simp only [upperMass, SubprobabilityVector.mass_zero]
    nlinarith
  by_cases hsmall : t ≤ stageTime p
  · rw [exactPhi_of_pos_le_stage htpos hp hsmall,
      upperMass_erodeBy U hp ht0 hsmall]
    have hgamma : gamma U p ≤ erosionConstant (P := P) :=
      gamma_le_erosionConstant hp U
    nlinarith
  · have hlarge : stageTime p < t := lt_of_not_ge hsmall
    have hstage0 : 0 ≤ stageTime p := le_of_lt (stageTime_pos_of_ne_zero hp)
    have hrem0 : 0 ≤ t - stageTime p := sub_nonneg.mpr (le_of_lt hlarge)
    have ih := exactPhi_lowerMass_sub (erodeBy p (stageTime p)) U hrem0
    have hstage := upperMass_erodeBy U hp hstage0 le_rfl
    have hgamma : gamma U p ≤ erosionConstant (P := P) :=
      gamma_le_erosionConstant hp U
    have hK := erosionConstant_nonneg (P := P)
    rw [exactPhi_of_stage_lt hlarge hp]
    nlinarith
termination_by (support p).card
decreasing_by
  exact Finset.card_lt_card (support_erodeBy_stageTime_ssubset hp)

/-- Lemma `lem:lower-set-estimate`; nonemptiness is not needed by the
formal proof, so the result is slightly stronger than the source statement. -/
theorem exactPhi_lowerMass_estimate (p : SubprobabilityVector P)
    (U : UpperSet P) {t : Real} (ht0 : 0 ≤ t) :
    max (upperMass p U - erosionConstant (P := P) * t) 0 ≤
      upperMass (exactPhi t p) U := by
  apply max_le
  · exact exactPhi_lowerMass_sub p U ht0
  · simpa [upperMass] using (exactPhi t p).mass_nonneg (U : Set P)

/-- Corollary `cor:finite-two-sided`. -/
theorem exactPhi_two_sided (p : SubprobabilityVector P)
    (U : UpperSet P) {t : Real} (ht0 : 0 ≤ t) :
    max (upperMass p U - erosionConstant (P := P) * t) 0 ≤
        upperMass (exactPhi t p) U ∧
      upperMass (exactPhi t p) U ≤ max (upperMass p U - t) 0 :=
  ⟨exactPhi_lowerMass_estimate p U ht0,
    exactPhi_upperMass_estimate p U ht0⟩

/-! ## Scott continuity: explicit remaining directed-supremum bridge -/

/-- The finite-dimensional directed-supremum approximation property used in
the manuscript's equation `eq:simultaneous-approximation`.

This is isolated as an explicit premise: proving it requires a separate
construction of directed suprema for the stochastic simplex, which is not
part of `FiniteValuation.Basic`. -/
def DirectedUpperMassApproximation : Prop :=
  ∀ (D : Set (SubprobabilityVector P)) (p : SubprobabilityVector P),
    D.Nonempty → DirectedOn (· ≤ ·) D → IsLUB D p →
      ∀ ε : Real, 0 < ε →
        ∃ q ∈ D, ∀ U : UpperSet P,
          upperMass p U - ε < upperMass q U

/-- Conditional Scott-continuity theorem.  Every other ingredient of
`prop:Phi-scott` is proved internally; the sole premise is the explicit
finite-dimensional directed-supremum bridge above. -/
theorem exactPhi_scott_of_directedUpperMassApproximation
    (happrox : DirectedUpperMassApproximation (P := P))
    {t : Real} (ht0 : 0 ≤ t) :
    ScottContinuous (fun p : SubprobabilityVector P => exactPhi t p) := by
  intro D hDne hDdir p hp
  constructor
  · intro y hy
    obtain ⟨q, hqD, rfl⟩ := hy
    exact exactPhi_mono (hp.1 hqD) ht0
  · intro b hb
    intro U
    by_contra hnot
    have hstrict : upperMass b U < upperMass (exactPhi t p) U :=
      lt_of_not_ge hnot
    let g : Real := upperMass (exactPhi t p) U - upperMass b U
    have hg : 0 < g := sub_pos.mpr hstrict
    let K : Real := erosionConstant (P := P)
    have hK0 : 0 ≤ K := erosionConstant_nonneg (P := P)
    let ε : Real := g / (K + 1)
    have hden : 0 < K + 1 := by linarith
    have hε : 0 < ε := div_pos hg hden
    have hdecomp : (K + 1) * ε = g := by
      dsimp only [ε]
      exact mul_div_cancel₀ g (ne_of_gt hden)
    have hKε : K * ε < g := by linarith
    obtain ⟨q, hqD, hq⟩ := happrox D p hDne hDdir hp ε hε
    have hshift : exactPhi ε p ≤ q := by
      intro V
      have hupp := exactPhi_upperMass_estimate p V (le_of_lt hε)
      by_cases hpV : upperMass p V ≤ ε
      · rw [max_eq_right (by linarith)] at hupp
        have hq0 : 0 ≤ upperMass q V := by
          simpa [upperMass] using q.mass_nonneg (V : Set P)
        linarith
      · rw [max_eq_left (by linarith)] at hupp
        exact hupp.trans (le_of_lt (hq V))
    have hthrough : exactPhi t (exactPhi ε p) ≤ b :=
      (exactPhi_mono hshift ht0).trans (hb ⟨q, hqD, rfl⟩)
    have hcommute :
        exactPhi ε (exactPhi t p) = exactPhi t (exactPhi ε p) := by
      rw [← exactPhi_add p (le_of_lt hε) ht0,
        ← exactPhi_add p ht0 (le_of_lt hε)]
      congr 1
      ring
    have hlower := exactPhi_lowerMass_sub (exactPhi t p) U (le_of_lt hε)
    rw [hcommute] at hlower
    have hthroughU := hthrough U
    dsimp only [g] at hg hKε
    dsimp only [K] at hKε hlower
    linarith

/-! ## Explicit finite grid separation -/

/-- Integer coefficient tables with denominator `N` and total numerator at
most `N`. -/
def NatFloorGridCode (N : Nat) :=
  {k : P → Fin (N + 1) // (∑ x, (k x).val) ≤ N}

noncomputable instance natFloorGridCodeFintype (N : Nat) :
    Fintype (NatFloorGridCode (P := P) N) :=
  Fintype.ofInjective (fun k : NatFloorGridCode (P := P) N => k.1)
    Subtype.val_injective

/-- A grid code denotes a subprobability vector. -/
noncomputable def gridVector (N : Nat) (hN : 0 < N)
    (k : NatFloorGridCode (P := P) N) : SubprobabilityVector P where
  coeff x := (k.1 x).val / (N : Real)
  coeff_nonneg x := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  total_le_one := by
    have hsum : (∑ x, ((k.1 x).val : Real)) ≤ (N : Real) := by
      exact_mod_cast k.2
    calc
      (∑ x, ((k.1 x).val : Real) / (N : Real)) =
          (∑ x, ((k.1 x).val : Real)) / (N : Real) := by
        rw [Finset.sum_div]
      _ ≤ (N : Real) / (N : Real) :=
        div_le_div_of_nonneg_right hsum (Nat.cast_nonneg _)
      _ = 1 := by
        exact div_self (ne_of_gt (Nat.cast_pos.mpr hN))

private theorem coeff_le_one (p : SubprobabilityVector P) (x : P) : p x ≤ 1 := by
  calc
    p x = p.mass ({x} : Set P) := by
      simp [SubprobabilityVector.mass]
    _ ≤ p.mass (Set.univ : Set P) :=
      p.mass_mono (Set.subset_univ _)
    _ = p.totalMass := SubprobabilityVector.mass_univ p
    _ ≤ 1 := p.totalMass_le_one

/-- The numerator table obtained by flooring all scaled coefficients. -/
noncomputable def natFloorCode (N : Nat) (hN : 0 < N)
    (p : SubprobabilityVector P) : NatFloorGridCode (P := P) N := by
  let k : P → Fin (N + 1) := fun x =>
    ⟨⌊(N : Real) * p x⌋₊, by
      rw [Nat.lt_add_one_iff]
      apply Nat.floor_le_of_le
      exact mul_le_of_le_one_right (Nat.cast_nonneg N) (coeff_le_one p x)⟩
  refine ⟨k, ?_⟩
  have hterm (x : P) :
      ((⌊(N : Real) * p x⌋₊ : Nat) : Real) ≤ (N : Real) * p x :=
    Nat.floor_le (mul_nonneg (Nat.cast_nonneg _) (p.coeff_nonneg x))
  have hsum :
      (∑ x, ((⌊(N : Real) * p x⌋₊ : Nat) : Real)) ≤ (N : Real) := by
    calc
      (∑ x, ((⌊(N : Real) * p x⌋₊ : Nat) : Real)) ≤
          ∑ x, (N : Real) * p x := Finset.sum_le_sum fun x _ => hterm x
      _ = (N : Real) * p.totalMass := by
        simp [SubprobabilityVector.totalMass, Finset.mul_sum]
      _ ≤ (N : Real) * 1 :=
        mul_le_mul_of_nonneg_left p.totalMass_le_one (Nat.cast_nonneg _)
      _ = (N : Real) := by ring
  change (∑ x, ⌊(N : Real) * p x⌋₊) ≤ N
  exact_mod_cast hsum

/-- Coordinatewise flooring onto the denominator-`N` grid. -/
noncomputable def roundDown (N : Nat) (hN : 0 < N)
    (p : SubprobabilityVector P) : SubprobabilityVector P :=
  gridVector N hN (natFloorCode N hN p)

theorem roundDown_apply (N : Nat) (hN : 0 < N)
    (p : SubprobabilityVector P) (x : P) :
    roundDown N hN p x = ⌊(N : Real) * p x⌋₊ / (N : Real) :=
  rfl

theorem roundDown_coordinatewise_le (N : Nat) (hN : 0 < N)
    (p : SubprobabilityVector P) : CoordinatewiseLE (roundDown N hN p) p := by
  intro x
  rw [roundDown_apply]
  apply (div_le_iff₀ (Nat.cast_pos.mpr hN)).2
  simpa [mul_comm] using
    (Nat.floor_le (mul_nonneg (Nat.cast_nonneg N) (p.coeff_nonneg x)) :
      ((⌊(N : Real) * p x⌋₊ : Nat) : Real) ≤ (N : Real) * p x)

theorem roundDown_le (N : Nat) (hN : 0 < N)
    (p : SubprobabilityVector P) : roundDown N hN p ≤ p :=
  stochasticLE_of_coordinatewise (roundDown_coordinatewise_le N hN p)

private theorem roundDown_coordinate_error_le (N : Nat) (hN : 0 < N)
    (p : SubprobabilityVector P) (x : P) :
    p x - roundDown N hN p x ≤ 1 / (N : Real) := by
  rw [roundDown_apply]
  have hfloor := Nat.lt_floor_add_one ((N : Real) * p x)
  have hNreal : 0 < (N : Real) := Nat.cast_pos.mpr hN
  have hscaled :
      p x < (((⌊(N : Real) * p x⌋₊ : Nat) : Real) + 1) / (N : Real) := by
    apply (lt_div_iff₀ hNreal).2
    simpa [mul_comm] using hfloor
  rw [add_div] at hscaled
  exact le_of_lt (by linarith)

/-- Uniform rounding error on every upper set. -/
theorem upperMass_sub_roundDown_le (N : Nat) (hN : 0 < N)
    (p : SubprobabilityVector P) (U : UpperSet P) :
    upperMass p U - upperMass (roundDown N hN p) U ≤
      Fintype.card P / (N : Real) := by
  unfold upperMass SubprobabilityVector.mass
  rw [← Finset.sum_sub_distrib]
  calc
    (∑ x : P, ((if x ∈ (U : Set P) then p x else 0) -
        (if x ∈ (U : Set P) then roundDown N hN p x else 0))) ≤
        ∑ _x : P, 1 / (N : Real) := by
      apply Finset.sum_le_sum
      intro x hx
      by_cases hxU : x ∈ (U : Set P)
      · simp only [if_pos hxU]
        exact roundDown_coordinate_error_le N hN p x
      · simp [hxU]
    _ = Fintype.card P / (N : Real) := by
      simp
      ring

/-- A map is finitely separated from the identity when a finite set contains
an intermediate point between `f p` and `p` for every `p`. -/
def FinitelySeparatedFromId
    (f : SubprobabilityVector P → SubprobabilityVector P) : Prop :=
  ∃ M : Set (SubprobabilityVector P), M.Finite ∧
    ∀ p, ∃ m ∈ M, f p ≤ m ∧ m ≤ p

/-- Proposition `prop:finite-separation`: every positive-time erosion map
has an explicit finite grid separator. -/
theorem exactPhi_finitelySeparated {t : Real} (ht : 0 < t) :
    FinitelySeparatedFromId (P := P) (fun p => exactPhi t p) := by
  obtain ⟨N, hNlarge⟩ := exists_nat_gt (Fintype.card P / t)
  have hratio0 : 0 ≤ (Fintype.card P : Real) / t :=
    div_nonneg (Nat.cast_nonneg _) (le_of_lt ht)
  have hN : 0 < N := by
    exact_mod_cast (lt_of_le_of_lt hratio0 hNlarge)
  have hgridlt : (Fintype.card P : Real) / (N : Real) < t := by
    apply (div_lt_iff₀ (Nat.cast_pos.mpr hN)).2
    have hmul := (div_lt_iff₀ ht).mp hNlarge
    simpa [mul_comm] using hmul
  let M : Set (SubprobabilityVector P) :=
    Set.range (gridVector (P := P) N hN)
  refine ⟨M, Set.finite_range _, ?_⟩
  intro p
  let m := roundDown N hN p
  refine ⟨m, ⟨natFloorCode N hN p, rfl⟩, ?_, roundDown_le N hN p⟩
  intro U
  have hupp := exactPhi_upperMass_estimate p U (le_of_lt ht)
  have herr := upperMass_sub_roundDown_le N hN p U
  by_cases hpt : upperMass p U ≤ t
  · rw [max_eq_right (by linarith)] at hupp
    have hm0 : 0 ≤ upperMass m U := by
      simpa [m, upperMass] using m.mass_nonneg (U : Set P)
    linarith
  · rw [max_eq_left (by linarith)] at hupp
    dsimp only [m]
    linarith

/-! ## Strongest self-contained FS conclusion -/

/-- A countable FS approximate identity, stated only with Mathlib's
`ScottContinuous`, finite separation, pointwise monotonicity, and `IsLUB`.
This avoids importing any project-level domain package. -/
def HasExplicitFSApproximateIdentity : Prop :=
  ∃ f : Nat → SubprobabilityVector P → SubprobabilityVector P,
    (∀ k, ScottContinuous (f k)) ∧
    (∀ k, FinitelySeparatedFromId (P := P) (f k)) ∧
    (∀ k p, f k p ≤ f (k + 1) p) ∧
    (∀ p, IsLUB (Set.range fun k => f k p) p)

/-- A convenient decreasing positive time scale tending to zero. -/
noncomputable def erosionTime (k : Nat) : Real := 1 / (k + 1)

theorem erosionTime_pos (k : Nat) : 0 < erosionTime k := by
  unfold erosionTime
  positivity

theorem erosionTime_succ_le (k : Nat) : erosionTime (k + 1) ≤ erosionTime k := by
  unfold erosionTime
  apply one_div_le_one_div_of_le
  · positivity
  · norm_num

/-- The pointwise erosion chain has supremum exactly the identity, proved
quantitatively from the lower mass estimate. -/
theorem erosionTime_range_isLUB (p : SubprobabilityVector P) :
    IsLUB (Set.range fun k => exactPhi (erosionTime k) p) p := by
  constructor
  · intro y hy
    obtain ⟨k, rfl⟩ := hy
    exact exactPhi_le (erosionTime k) p
  · intro b hb
    intro U
    by_contra hnot
    have hstrict : upperMass b U < upperMass p U := lt_of_not_ge hnot
    let g : Real := upperMass p U - upperMass b U
    have hg : 0 < g := sub_pos.mpr hstrict
    let K : Real := erosionConstant (P := P)
    have hK0 : 0 ≤ K := erosionConstant_nonneg (P := P)
    obtain ⟨k, hk⟩ := exists_nat_gt (K / g)
    have hk0 : 0 ≤ (k : Real) := Nat.cast_nonneg k
    have hKgk : K < (k : Real) * g := (div_lt_iff₀ hg).mp hk
    have hKsmall : K * erosionTime k < g := by
      unfold erosionTime
      rw [show K * (1 / ((k : Real) + 1)) = K / ((k : Real) + 1) by ring]
      apply (div_lt_iff₀ (by positivity : (0 : Real) < k + 1)).2
      nlinarith
    have hlower := exactPhi_lowerMass_sub p U
      (le_of_lt (erosionTime_pos k))
    have hbelow := hb ⟨k, rfl⟩
    have hbelowU := hbelow U
    dsimp only [g] at hg hKsmall
    dsimp only [K] at hKsmall hlower
    linarith

/-- Strongest debt-free form of `thm:subprobability-FS` available from the
self-contained finite-vector development.  The only premise is precisely the
directed-supremum bridge needed for Scott continuity; countable-basedness is
not asserted here. -/
theorem explicitFSApproximateIdentity_of_directedUpperMassApproximation
    (happrox : DirectedUpperMassApproximation (P := P)) :
    HasExplicitFSApproximateIdentity (P := P) := by
  refine ⟨(fun k p => exactPhi (erosionTime k) p), ?_, ?_, ?_, ?_⟩
  · intro k
    exact exactPhi_scott_of_directedUpperMassApproximation happrox
      (le_of_lt (erosionTime_pos k))
  · intro k
    exact exactPhi_finitelySeparated (erosionTime_pos k)
  · intro k p
    exact exactPhi_antitone_time p (le_of_lt (erosionTime_pos (k + 1)))
      (erosionTime_succ_le k)
  · exact erosionTime_range_isLUB

end FiniteValuationApproximable.Erosion
