import FiniteValuationApproximable.FiniteValuation.Basic
import Mathlib.Order.Preorder.Finite

/-!
# Normalized finite probability valuations

This module formalizes the order-theoretic core of
`prop:probability-positive`, `prop:probability-negative`, and
`cor:probability-characterization` from `main (17).tex`.

Source version: SHA-256
`4b2e65f0f96347bea4df7571e8993ad6e888c0ff7181c1305c5056880365ac94`.
-/

set_option autoImplicit false
set_option linter.unnecessarySimpa false

universe u

namespace FiniteValuationApproximable

open scoped BigOperators Classical
open Set
open SubprobabilityVector

namespace ProbabilityVector

variable {Q : Type u} [Fintype Q]

instance : CoeFun (ProbabilityVector Q) (fun _ => Q -> Real) where
  coe p := p.1

instance [PartialOrder Q] : PartialOrder (ProbabilityVector Q) where
  le p q := p.1 <= q.1
  le_refl p := le_rfl
  le_trans p q r hpq hqr := le_trans hpq hqr
  le_antisymm p q hpq hqp := Subtype.ext (le_antisymm hpq hqp)

@[ext]
theorem ext {p q : ProbabilityVector Q} (h : forall x, p x = q x) : p = q := by
  apply Subtype.ext
  apply SubprobabilityVector.ext
  exact h

@[simp]
theorem totalMass_eq_one (p : ProbabilityVector Q) : p.1.totalMass = 1 :=
  p.2

theorem coeff_nonneg (p : ProbabilityVector Q) (x : Q) : 0 <= p x :=
  p.1.coeff_nonneg x

/-- A probability vector is supported on the order-minimal elements. -/
def SupportedOnMinima [PartialOrder Q] (p : ProbabilityVector Q) : Prop :=
  forall x, ¬ IsMin x -> p x = 0

end ProbabilityVector

section MinimalFace

variable {Q : Type u} [Fintype Q] [PartialOrder Q]

open ProbabilityVector

/-- The source assertion that the finite poset has a least element. -/
def HasLeastElement (Q : Type u) [PartialOrder Q] : Prop :=
  exists bot : Q, forall x, bot <= x

/-- The complement of a minimal point is an upper set. -/
def complementSingletonUpper (m : Q) (hm : IsMin m) : UpperSet Q where
  carrier := ({m} : Set Q)ᶜ
  upper' := by
    intro x y hxy hx
    intro hym
    subst y
    apply hx
    simpa using le_antisymm hxy (hm hxy)

/-- For a normalized vector, the mass outside one point is one minus that
point's coefficient. -/
theorem mass_compl_singleton (p : ProbabilityVector Q) (x : Q) :
    p.1.mass ({x}ᶜ : Set Q) = 1 - p x := by
  classical
  have hsplit : p.1.totalMass = p x + p.1.mass ({x}ᶜ : Set Q) := by
    simp only [SubprobabilityVector.totalMass, SubprobabilityVector.mass,
      Set.mem_compl_iff, Set.mem_singleton_iff]
    calc
      (∑ y, p y) =
          ∑ y, ((if y = x then p y else 0) +
            (if y ≠ x then p y else 0)) := by
              apply Finset.sum_congr rfl
              intro y hy
              by_cases hyx : y = x
              · simp [hyx]
              · simp [hyx]
      _ = (∑ y, if y = x then p y else 0) +
          ∑ y, if y ≠ x then p y else 0 := Finset.sum_add_distrib
      _ = p x + ∑ y, if y ≠ x then p y else 0 := by simp
  rw [ProbabilityVector.totalMass_eq_one p] at hsplit
  linarith

/-- A normalized vector supported on minimal points is itself a minimal point
of the stochastic order. -/
theorem supportedOnMinima_isMin {p : ProbabilityVector Q}
    (hp : ProbabilityVector.SupportedOnMinima p) : IsMin p := by
  intro q hqp
  have hcoeff : forall x, p x <= q x := by
    intro x
    by_cases hx : IsMin x
    · let U := complementSingletonUpper x hx
      have hmass : upperMass q.1 U <= upperMass p.1 U := hqp U
      have hqmass := mass_compl_singleton q x
      have hpmass := mass_compl_singleton p x
      change q.1.mass ({x}ᶜ : Set Q) <= p.1.mass ({x}ᶜ : Set Q) at hmass
      rw [hqmass, hpmass] at hmass
      linarith
    · rw [hp x hx]
      exact ProbabilityVector.coeff_nonneg q x
  have hcoeff_eq : forall x, p x = q x := by
    classical
    intro x
    have hrest :
        (∑ y ∈ Finset.univ.erase x, p y) <=
          ∑ y ∈ Finset.univ.erase x, q y :=
      Finset.sum_le_sum fun y hy => hcoeff y
    have hpdecomp :
        p x + ∑ y ∈ Finset.univ.erase x, p y = 1 := by
      rw [Finset.add_sum_erase _ _ (Finset.mem_univ x)]
      exact ProbabilityVector.totalMass_eq_one p
    have hqdecomp :
        q x + ∑ y ∈ Finset.univ.erase x, q y = 1 := by
      rw [Finset.add_sum_erase _ _ (Finset.mem_univ x)]
      exact ProbabilityVector.totalMass_eq_one q
    exact le_antisymm (hcoeff x) (by linarith)
  have hpq : p = q := ProbabilityVector.ext hcoeff_eq
  exact hpq.le

/-- A finite nonempty poset without a least point has two distinct minimal
points.  This is where minimal and least are kept explicitly distinct. -/
theorem exists_two_isMin [Nonempty Q] (hno : ¬ HasLeastElement Q) :
    exists a b : Q, IsMin a ∧ IsMin b ∧ a ≠ b := by
  classical
  obtain ⟨a, ha⟩ := (Finset.univ : Finset Q).exists_minimal Finset.univ_nonempty
  have ha_min : IsMin a := by simpa using ha
  have hb_exists : exists b : Q, IsMin b ∧ b ≠ a := by
    by_contra h
    push_neg at h
    have ha_least : forall x : Q, a <= x := by
      intro x
      obtain ⟨b, hbx, hb⟩ :=
        (Finset.univ : Finset Q).exists_le_minimal (Finset.mem_univ x)
      have hb_min : IsMin b := by simpa using hb
      simpa [h b hb_min] using hbx
    exact hno ⟨a, ha_least⟩
  obtain ⟨b, hb_min, hba⟩ := hb_exists
  exact ⟨a, b, ha_min, hb_min, Ne.symm hba⟩

/-- A two-point probability vector with weight `t` at `a` and `1-t` at `b`. -/
noncomputable def binaryProbability (a b : Q) (hab : a ≠ b)
    (t : Real) (ht0 : 0 <= t) (ht1 : t <= 1) : ProbabilityVector Q := by
  classical
  have hba : b ≠ a := Ne.symm hab
  have hsum :
      (∑ x : Q, if x = a then t else if x = b then 1 - t else 0) = 1 := by
    calc
      (∑ x : Q, if x = a then t else if x = b then 1 - t else 0) =
          (∑ x : Q, if x = a then t else 0) +
            ∑ x : Q, if x = b then 1 - t else 0 := by
              rw [← Finset.sum_add_distrib]
              apply Finset.sum_congr rfl
              intro x hx
              by_cases hxa : x = a
              · subst x
                simp [hab]
              · by_cases hxb : x = b
                · subst x
                  simp [hba]
                · simp [hxa, hxb]
      _ = t + (1 - t) := by simp
      _ = 1 := by ring
  let v : SubprobabilityVector Q :=
    { coeff := fun x => if x = a then t else if x = b then 1 - t else 0
      coeff_nonneg := by
        intro x
        by_cases hxa : x = a
        · simp [hxa, ht0]
        · by_cases hxb : x = b
          · subst x
            simp [hba, sub_nonneg.mpr ht1]
          · simp [hxa, hxb]
      total_le_one := hsum.le }
  refine ⟨v, ?_⟩
  change (∑ x : Q, if x = a then t else if x = b then 1 - t else 0) = 1
  exact hsum

@[simp]
theorem binaryProbability_apply_left (a b : Q) (hab : a ≠ b)
    (t : Real) (ht0 : 0 <= t) (ht1 : t <= 1) :
    binaryProbability a b hab t ht0 ht1 a = t := by
  classical
  change (if a = a then t else if a = b then 1 - t else 0) = t
  simp

theorem binaryProbability_supportedOnMinima {a b : Q}
    (ha : IsMin a) (hb : IsMin b) (hab : a ≠ b)
    (t : Real) (ht0 : 0 <= t) (ht1 : t <= 1) :
    ProbabilityVector.SupportedOnMinima
      (binaryProbability a b hab t ht0 ht1) := by
  intro x hx
  by_cases hxa : x = a
  · subst x
    exact (hx ha).elim
  · by_cases hxb : x = b
    · subst x
      exact (hx hb).elim
    · classical
      change (if x = a then t else if x = b then 1 - t else 0) = 0
      simp [hxa, hxb]

/-- A countable family of distinct points in the minimal face. -/
noncomputable def binaryProbabilitySequence (a b : Q) (hab : a ≠ b)
    (n : Nat) : ProbabilityVector Q := by
  have hdenom : 0 < (n : Real) + 2 := by positivity
  exact binaryProbability a b hab (((n : Real) + 2)⁻¹)
    (le_of_lt (inv_pos.mpr hdenom))
    (inv_le_one_of_one_le₀ (by linarith))

theorem binaryProbabilitySequence_injective (a b : Q) (hab : a ≠ b) :
    Function.Injective (binaryProbabilitySequence a b hab) := by
  intro n m hnm
  have hcoeff := congrArg (fun p : ProbabilityVector Q => p a) hnm
  simp only [binaryProbabilitySequence, binaryProbability_apply_left] at hcoeff
  have hdenom : (n : Real) + 2 = (m : Real) + 2 := inv_injective hcoeff
  have hcast : (n : Real) = (m : Real) := by linarith
  exact_mod_cast hcast

theorem binaryProbabilitySequence_supportedOnMinima {a b : Q}
    (ha : IsMin a) (hb : IsMin b) (hab : a ≠ b) (n : Nat) :
    ProbabilityVector.SupportedOnMinima (binaryProbabilitySequence a b hab n) := by
  unfold binaryProbabilitySequence
  apply binaryProbability_supportedOnMinima ha hb hab

/-- The face of probability vectors supported on the minimal points is
infinite whenever the carrier has no least point. -/
theorem minimalFace_infinite [Nonempty Q] (hno : ¬ HasLeastElement Q) :
    Set.Infinite {p : ProbabilityVector Q |
      ProbabilityVector.SupportedOnMinima p} := by
  obtain ⟨a, b, ha, hb, hab⟩ := exists_two_isMin hno
  have hrange : Set.Infinite (Set.range (binaryProbabilitySequence a b hab)) :=
    Set.infinite_range_of_injective (binaryProbabilitySequence_injective a b hab)
  apply hrange.mono
  intro p hp
  obtain ⟨n, rfl⟩ := hp
  exact binaryProbabilitySequence_supportedOnMinima ha hb hab n

/-- A finite separator for a self-map, exactly as used in the source's
definition of finite separation from the identity. -/
def HasFiniteSeparator (f : ProbabilityVector Q -> ProbabilityVector Q) : Prop :=
  exists F : Set (ProbabilityVector Q),
    F.Finite ∧ forall p, ∃ m ∈ F, f p <= m ∧ m <= p

/-- Proposition `prop:probability-negative`, at its exact finite-separator
strength: without a least carrier point, no self-map has a finite separator. -/
theorem no_finiteSeparator_of_no_least [Nonempty Q]
    (hno : ¬ HasLeastElement Q) (f : ProbabilityVector Q -> ProbabilityVector Q) :
    ¬ HasFiniteSeparator f := by
  intro hseparator
  obtain ⟨F, hFfinite, hF⟩ := hseparator
  have hface := minimalFace_infinite hno
  have hnsubset : ¬ {p : ProbabilityVector Q |
      ProbabilityVector.SupportedOnMinima p} ⊆ F := by
    intro hsubset
    exact hface (hFfinite.subset hsubset)
  obtain ⟨p, hpface, hpnotF⟩ := Set.not_subset.mp hnsubset
  obtain ⟨m, hmF, hfm, hmp⟩ := hF p
  have hpmin : IsMin p := supportedOnMinima_isMin hpface
  have hpm : p <= m := hpmin hmp
  have hmp_eq : m = p := le_antisymm hmp hpm
  exact hpnotF (hmp_eq ▸ hmF)

/-! ## The positive case: deleting a least point -/

/-- The finite poset obtained by deleting the chosen least point. -/
abbrev WithoutPoint (bot : Q) :=
  {x : Q // x ≠ bot}

instance (bot : Q) : PartialOrder (WithoutPoint bot) :=
  inferInstanceAs (PartialOrder {x : Q // x ≠ bot})

/-- Restriction of a normalized vector to all coordinates except `bot`. -/
noncomputable def restrictProbability (bot : Q) (p : ProbabilityVector Q) :
    SubprobabilityVector (WithoutPoint bot) := by
  classical
  have hsum := Fintype.sum_eq_add_sum_subtype_ne (fun x : Q => p x) bot
  have hpTotal : (∑ x : Q, p x) = 1 := by
    exact ProbabilityVector.totalMass_eq_one p
  have hnonneg : 0 <= ∑ x : WithoutPoint bot, p x.1 :=
    Finset.sum_nonneg fun x hx => ProbabilityVector.coeff_nonneg p x.1
  have hpbot : 0 <= p bot := ProbabilityVector.coeff_nonneg p bot
  refine
    { coeff := fun x => p x.1
      coeff_nonneg := fun x => ProbabilityVector.coeff_nonneg p x.1
      total_le_one := ?_ }
  rw [hpTotal] at hsum
  linarith

@[simp]
theorem restrictProbability_apply (bot : Q) (p : ProbabilityVector Q)
    (x : WithoutPoint bot) : restrictProbability bot p x = p x.1 := by
  classical
  unfold restrictProbability
  rfl

theorem totalMass_restrictProbability (bot : Q) (p : ProbabilityVector Q) :
    (restrictProbability bot p).totalMass = 1 - p bot := by
  classical
  have hsum := Fintype.sum_eq_add_sum_subtype_ne (fun x : Q => p x) bot
  have hpTotal : (∑ x : Q, p x) = 1 := by
    exact ProbabilityVector.totalMass_eq_one p
  rw [hpTotal] at hsum
  simp only [SubprobabilityVector.totalMass, restrictProbability_apply]
  linarith

/-- Put the missing subprobability mass at `bot`. -/
noncomputable def addMissingMass (bot : Q)
    (mu : SubprobabilityVector (WithoutPoint bot)) : ProbabilityVector Q := by
  classical
  let coeff : Q -> Real := fun x =>
    if h : x = bot then 1 - mu.totalMass else mu ⟨x, h⟩
  have htail : (∑ x : WithoutPoint bot, coeff x.1) = mu.totalMass := by
    change (∑ x : WithoutPoint bot, coeff x.1) = ∑ x, mu x
    apply Finset.sum_congr rfl
    intro x hx
    simp [coeff, x.property]
  have hsum : (∑ x : Q, coeff x) = 1 := by
    rw [Fintype.sum_eq_add_sum_subtype_ne coeff bot]
    have htail' :
        (∑ x : {x : Q // x ≠ bot}, coeff x.1) = mu.totalMass := htail
    rw [htail']
    simp [coeff]
  let v : SubprobabilityVector Q :=
    { coeff := coeff
      coeff_nonneg := by
        intro x
        by_cases hx : x = bot
        · subst x
          simpa [coeff, SubprobabilityVector.totalMass] using mu.totalMass_le_one
        · simp [coeff, hx, mu.coeff_nonneg]
      total_le_one := hsum.le }
  exact ⟨v, hsum⟩

@[simp]
theorem addMissingMass_apply_bot (bot : Q)
    (mu : SubprobabilityVector (WithoutPoint bot)) :
    addMissingMass bot mu bot = 1 - mu.totalMass := by
  classical
  change (if h : bot = bot then 1 - mu.totalMass else mu ⟨bot, h⟩) =
    1 - mu.totalMass
  simp

@[simp]
theorem addMissingMass_apply_ne (bot : Q)
    (mu : SubprobabilityVector (WithoutPoint bot)) (x : Q) (hx : x ≠ bot) :
    addMissingMass bot mu x = mu ⟨x, hx⟩ := by
  classical
  change (if h : x = bot then 1 - mu.totalMass else mu ⟨x, h⟩) = mu ⟨x, hx⟩
  simp [hx]

@[simp]
theorem restrictProbability_addMissingMass (bot : Q)
    (mu : SubprobabilityVector (WithoutPoint bot)) :
    restrictProbability bot (addMissingMass bot mu) = mu := by
  apply SubprobabilityVector.ext
  intro x
  rw [restrictProbability_apply]
  rw [addMissingMass_apply_ne bot mu x.1 x.2]

@[simp]
theorem addMissingMass_restrictProbability (bot : Q) (p : ProbabilityVector Q) :
    addMissingMass bot (restrictProbability bot p) = p := by
  apply ProbabilityVector.ext
  intro x
  by_cases hx : x = bot
  · subst x
    change addMissingMass bot (restrictProbability bot p) bot = p bot
    rw [addMissingMass_apply_bot, totalMass_restrictProbability]
    ring
  · simp [hx]

/-- Extend an upper set of the deleted carrier to the original carrier.  The
least-point hypothesis ensures that moving upward cannot return to `bot`. -/
def extendUpperFromWithout (bot : Q) (hbot : forall x, bot <= x)
    (U : UpperSet (WithoutPoint bot)) : UpperSet Q where
  carrier := {x | exists hx : x ≠ bot, (⟨x, hx⟩ : WithoutPoint bot) ∈ U}
  upper' := by
    intro x y hxy hx
    obtain ⟨hxbot, hxU⟩ := hx
    have hybot : y ≠ bot := by
      intro hy
      subst y
      exact hxbot (le_antisymm hxy (hbot x))
    exact ⟨hybot, U.upper hxy hxU⟩

theorem upperMass_restrictProbability (bot : Q) (hbot : forall x, bot <= x)
    (p : ProbabilityVector Q) (U : UpperSet (WithoutPoint bot)) :
    upperMass (restrictProbability bot p) U =
      upperMass p.1 (extendUpperFromWithout bot hbot U) := by
  classical
  simp only [upperMass, SubprobabilityVector.mass]
  simp only [restrictProbability_apply]
  change (∑ x : WithoutPoint bot, if x ∈ U then p x.1 else 0) =
    ∑ x : Q, if x ∈ extendUpperFromWithout bot hbot U then p x else 0
  rw [Fintype.sum_eq_add_sum_subtype_ne
    (fun x : Q => if x ∈ extendUpperFromWithout bot hbot U then p x else 0) bot]
  simp only [extendUpperFromWithout, UpperSet.mem_mk, Set.mem_setOf_eq]
  have hbotTerm : ¬ exists h : bot ≠ bot,
      (⟨bot, h⟩ : WithoutPoint bot) ∈ U := by
    rintro ⟨h, hh⟩
    exact h rfl
  rw [if_neg hbotTerm, zero_add]
  apply Finset.sum_congr rfl
  intro x hx
  have hmem :
      (exists h : x.1 ≠ bot, (⟨x.1, h⟩ : WithoutPoint bot) ∈ U) ↔ x ∈ U := by
    constructor
    · rintro ⟨h, hh⟩
      convert hh using 1
    · intro hxU
      exact ⟨x.2, hxU⟩
  simp [hmem]

theorem restrictProbability_mono (bot : Q) (hbot : forall x, bot <= x) :
    Monotone (restrictProbability bot : ProbabilityVector Q ->
      SubprobabilityVector (WithoutPoint bot)) := by
  intro p q hpq U
  rw [upperMass_restrictProbability bot hbot p U,
    upperMass_restrictProbability bot hbot q U]
  exact hpq (extendUpperFromWithout bot hbot U)

/-- Restrict an upper set of `Q` to the deleted carrier. -/
def restrictUpperToWithout (bot : Q) (U : UpperSet Q) :
    UpperSet (WithoutPoint bot) where
  carrier := {x | x.1 ∈ U}
  upper' := by
    intro x y hxy hx
    exact U.upper hxy hx

theorem upperMass_addMissingMass_of_bot_notMem (bot : Q)
    (mu : SubprobabilityVector (WithoutPoint bot)) (U : UpperSet Q)
    (hbotU : bot ∉ U) :
    upperMass (addMissingMass bot mu).1 U =
      upperMass mu (restrictUpperToWithout bot U) := by
  classical
  simp only [upperMass, SubprobabilityVector.mass]
  change (∑ x : Q, if x ∈ U then addMissingMass bot mu x else 0) =
    ∑ x : WithoutPoint bot,
      if x ∈ restrictUpperToWithout bot U then mu x else 0
  rw [Fintype.sum_eq_add_sum_subtype_ne
      (fun x : Q => if x ∈ U then addMissingMass bot mu x else 0) bot]
  simp only [hbotU, ↓reduceIte, zero_add, restrictUpperToWithout, UpperSet.mem_mk,
    Set.mem_setOf_eq]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hxU : x.1 ∈ U
  · simp [hxU, addMissingMass_apply_ne bot mu x.1 x.2]
  · simp [hxU]

theorem addMissingMass_mono (bot : Q) (hbot : forall x, bot <= x) :
    Monotone (addMissingMass bot : SubprobabilityVector (WithoutPoint bot) ->
      ProbabilityVector Q) := by
  intro mu nu hmunu U
  by_cases hbotU : bot ∈ U
  · have hU : (U : Set Q) = Set.univ := by
      apply Set.eq_univ_of_forall
      intro x
      exact U.upper (hbot x) hbotU
    have hmu : upperMass (addMissingMass bot mu).1 U = 1 := by
      rw [show U = ⟨Set.univ, isUpperSet_univ⟩ from UpperSet.ext hU]
      simpa [upperMass] using ProbabilityVector.totalMass_eq_one (addMissingMass bot mu)
    have hnu : upperMass (addMissingMass bot nu).1 U = 1 := by
      rw [show U = ⟨Set.univ, isUpperSet_univ⟩ from UpperSet.ext hU]
      simpa [upperMass] using ProbabilityVector.totalMass_eq_one (addMissingMass bot nu)
    rw [hmu, hnu]
  · rw [upperMass_addMissingMass_of_bot_notMem bot mu U hbotU,
      upperMass_addMissingMass_of_bot_notMem bot nu U hbotU]
    exact hmunu (restrictUpperToWithout bot U)

/-- Proposition `prop:probability-positive`, order-theoretic part: restriction
is an order isomorphism, with missing mass stored at the least point. -/
noncomputable def probabilityOrderIso (bot : Q) (hbot : forall x, bot <= x) :
    ProbabilityVector Q ≃o SubprobabilityVector (WithoutPoint bot) where
  toFun := restrictProbability bot
  invFun := addMissingMass bot
  left_inv := addMissingMass_restrictProbability bot
  right_inv := restrictProbability_addMissingMass bot
  map_rel_iff' := by
    intro p q
    constructor
    · intro hpq
      have hlift := addMissingMass_mono bot hbot hpq
      simpa using hlift
    · intro hpq
      exact restrictProbability_mono bot hbot hpq

end MinimalFace

end FiniteValuationApproximable
