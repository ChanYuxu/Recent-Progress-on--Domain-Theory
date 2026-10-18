import ChainApproximation.AlgebraExpansion
import Mathlib.Tactic.FinCases

/-!
An explicit Erdős--Hajnal-style Jónsson algebra of cardinality `ℵ₁`.

For each countably infinite proper initial segment, choose an enumeration by
`ℕ`. The binary operation sends `x < y` to the enumeration predecessor of
`x`. An uncountable substructure contains an infinite subset below a chosen
`y`, so predecessor closure forces it to contain the whole initial segment.
This module does not claim local finiteness; that is the separate Devlin step
needed by the manuscript's sharpness example.
-/

set_option autoImplicit false

namespace ChainApproximation
namespace JonssonEH

open FirstOrder FirstOrder.Language Set Cardinal

abbrev I := CofinalIndex (Cardinal.aleph 1 : Cardinal.{0})

noncomputable instance : Nonempty I := Cardinal.mk_ne_zero_iff.mp (by
  rw [cofinalIndex_card]
  exact Cardinal.isRegular_aleph_one.ne_zero)

noncomputable instance : Infinite I := Cardinal.aleph0_le_mk_iff.mp (by
  rw [cofinalIndex_card]
  exact Cardinal.aleph0_le_aleph 1)

theorem I_hasCofinalChain : HasCofinalChain I :=
  ⟨Set.univ, ⟨Set.univ_nonempty, fun _ _ _ _ _ ↦ le_total _ _⟩, IsCofinal.univ⟩

theorem I_cof : Order.cof I = Cardinal.aleph 1 :=
  regular_cofinalIndex_cof Cardinal.isRegular_aleph_one

theorem Iio_countable (y : I) : (Iio y).Countable := by
  apply Cardinal.le_aleph0_iff_set_countable.mp
  exact Cardinal.lt_aleph_one_iff.mp
    (cofinalIndex_initial_small (Cardinal.aleph 1 : Cardinal.{0}) y)

theorem countable_bounded {S : Set I} (hS : S.Countable) : BddAbove S := by
  apply I_hasCofinalChain.small_bounded S
  rw [I_cof]
  exact (Cardinal.le_aleph0_iff_set_countable.mpr hS).trans_lt
    Cardinal.aleph0_lt_aleph_one

noncomputable def enum (y : I) (h : (Iio y).Infinite) : Iio y ≃ ℕ := by
  letI : Countable (Iio y) := (Iio_countable y).to_subtype
  letI : Infinite (Iio y) := h.to_subtype
  exact Classical.choice (inferInstance : Nonempty (Iio y ≃ ℕ))

noncomputable def pred (y : I) (h : (Iio y).Infinite) (x : Iio y) : Iio y :=
  (enum y h).symm (Nat.pred ((enum y h) x))

noncomputable def op (x y : I) : I := by
  classical
  exact if hxy : x < y then
    if hy : (Iio y).Infinite then (pred y hy ⟨x, hxy⟩).1 else x
  else x

def binaryLanguage : FirstOrder.Language :=
  ⟨fun n => PLift (n = 2), fun _ => Empty⟩

@[reducible] noncomputable def binaryStructure : binaryLanguage.Structure I where
  funMap := by
    intro n h xs
    rcases h with ⟨h⟩
    subst n
    exact op (xs 0) (xs 1)
  RelMap := by
    intro n r
    cases r

noncomputable instance : binaryLanguage.Structure I := binaryStructure

theorem op_mem (S : binaryLanguage.Substructure I) {x y : I}
    (hx : x ∈ S) (hy : y ∈ S) : op x y ∈ S := by
  have h := S.fun_mem (PLift.up (rfl : 2 = 2)) ![x, y] (by
    intro i
    fin_cases i <;> simp_all)
  change op x y ∈ S at h
  exact h

theorem binaryLanguage_countable : Countable (Σ n, binaryLanguage.Functions n) := by
  letI (n : ℕ) : Countable (binaryLanguage.Functions n) := by
    change Countable (PLift (n = 2))
    infer_instance
  infer_instance

theorem nat_pred_closed_infinite (T : Set ℕ) (hT : T.Infinite)
    (hpred : ∀ n ∈ T, Nat.pred n ∈ T) : T = Set.univ := by
  ext n
  constructor
  · intro _
    trivial
  · intro _
    obtain ⟨m, hm, hnm⟩ := hT.exists_gt n
    have hdown : ∀ k m : ℕ, k ≤ m → m ∈ T → k ∈ T := by
      intro k m hkm
      induction hkm with
      | refl => exact id
      | @step m hkm ih =>
        intro hm1
        exact ih (by simpa only [Nat.pred_succ] using hpred (m + 1) hm1)
    exact hdown n m hnm.le hm

theorem closed_contains_initial (S : binaryLanguage.Substructure I) (y : I)
    (hy : y ∈ S) (hiy : (Iio y).Infinite)
    (hT : ({x : Iio y | x.1 ∈ S} : Set (Iio y)).Infinite) :
    (Iio y : Set I) ⊆ S := by
  let e := enum y hiy
  let T : Set (Iio y) := {x | x.1 ∈ S}
  let N : Set ℕ := e '' T
  have hN : N.Infinite := hT.image e.injective.injOn
  have hNpred : ∀ n ∈ N, Nat.pred n ∈ N := by
    intro n hn
    obtain ⟨x, hx, rfl⟩ := hn
    let z : Iio y := pred y hiy x
    have hz : z ∈ T := by
      change z.1 ∈ S
      have hf : op x.1 y ∈ S := op_mem S hx hy
      have heq : op x.1 y = z.1 := by
        unfold op
        have hxy : x.1 < y := x.2
        rw [dif_pos hxy, dif_pos hiy]
      exact heq ▸ hf
    refine ⟨z, hz, ?_⟩
    simp [z, pred, e]
  have hfull : N = Set.univ := nat_pred_closed_infinite N hN hNpred
  intro x hxy
  let xx : Iio y := ⟨x, hxy⟩
  have hmem : e xx ∈ N := by rw [hfull]; trivial
  obtain ⟨z, hz, heq⟩ := hmem
  have hzx : z = xx := e.injective heq
  change xx ∈ T
  exact hzx ▸ hz

theorem Iic_countable (y : I) : (Iic y).Countable := by
  rw [← Set.Iio_insert]
  exact (Iio_countable y).insert y

theorem uncountable_unbounded {S : Set I} (hS : ¬ S.Countable) : ¬ BddAbove S := by
  intro hb
  obtain ⟨y, hy⟩ := hb
  apply hS
  exact (Iic_countable y).mono hy

theorem uncountable_substructure_top (S : binaryLanguage.Substructure I)
    (hS : ¬ (S : Set I).Countable) : S = ⊤ := by
  have hSinfinite : (S : Set I).Infinite := by
    intro hfinite
    exact hS hfinite.countable
  obtain ⟨T, hTS, hTcountable, hTinfinite⟩ := hSinfinite.exists_subset_countable_infinite
  obtain ⟨b, hb⟩ := countable_bounded hTcountable
  have hSunbounded : ¬ BddAbove (S : Set I) := uncountable_unbounded hS
  ext x
  constructor
  · intro _
    trivial
  · intro _
    obtain ⟨y, hy, hxy⟩ := (not_bddAbove_iff.mp hSunbounded) (max x b)
    have hby : b < y := lt_of_le_of_lt (le_max_right x b) hxy
    have hxy' : x < y := lt_of_le_of_lt (le_max_left x b) hxy
    have hiy : (Iio y).Infinite := by
      apply hTinfinite.mono
      intro t ht
      exact (hb ht).trans_lt hby
    letI : Infinite T := hTinfinite.to_subtype
    let e : T ↪ Iio y := {
      toFun := fun t => ⟨t.1, (hb t.2).trans_lt hby⟩
      inj' := by intro a c hac; exact Subtype.ext (congrArg (fun z : Iio y => z.val) hac) }
    have hsub : Set.range e ⊆ ({z : Iio y | z.1 ∈ S} : Set (Iio y)) := by
      rintro z ⟨t, rfl⟩
      exact hTS t.2
    have hTiy : ({z : Iio y | z.1 ∈ S} : Set (Iio y)).Infinite :=
      (Set.infinite_range_of_injective e.injective).mono hsub
    exact closed_contains_initial S y hy hiy hTiy hxy'

theorem eh_jonsson : Algebra.Jonsson binaryLanguage I := by
  refine ⟨inferInstance, binaryLanguage_countable, ?_⟩
  intro S hcard
  apply uncountable_substructure_top S
  intro hS
  have hle : Cardinal.mk S ≤ Cardinal.aleph0 :=
    Cardinal.mk_le_aleph0_iff.mpr hS.to_subtype
  rw [hcard, cofinalIndex_card] at hle
  exact Cardinal.aleph0_lt_aleph_one.not_ge hle

theorem eh_card : Cardinal.mk I = Cardinal.aleph 1 :=
  cofinalIndex_card (Cardinal.aleph 1 : Cardinal.{0})

theorem binaryLanguage_isAlgebraic : binaryLanguage.IsAlgebraic := by
  intro n
  change IsEmpty Empty
  infer_instance

theorem binaryLanguage_noOtherFunctions (n : ℕ) (hn : n ≠ 2) :
    IsEmpty (binaryLanguage.Functions n) := by
  change IsEmpty (PLift (n = 2))
  exact ⟨fun h => hn h.down⟩

theorem binaryLanguage_oneBinary : Cardinal.mk (binaryLanguage.Functions 2) = 1 := by
  simp [binaryLanguage]

theorem exists_jonsson_aleph_one :
    ∃ (L : FirstOrder.Language.{0, 0}) (M : Type)
      (str : L.Structure M),
      Cardinal.mk M = Cardinal.aleph 1 ∧ @Algebra.Jonsson L M str := by
  refine ⟨binaryLanguage, I, binaryStructure, eh_card, ?_⟩
  exact eh_jonsson

end JonssonEH
end ChainApproximation
