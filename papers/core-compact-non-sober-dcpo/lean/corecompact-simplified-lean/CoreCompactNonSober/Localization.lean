import CoreCompactNonSober.AmbientCardinality
import CoreCompactNonSober.CountableProductCardinality
import Mathlib.Data.Nat.Pairing

/-!
# Localization slaloms and the common cardinal

Source: `def:localization`, `eq:lambda`, and `lem:lambda-bounds`.
Empty lists are allowed. Capture means membership outside a finite initial
segment of the actual coordinates `j ≥ 2`. The cardinal is the genuine
minimum of the cardinalities of capturing families.
-/

set_option autoImplicit false

namespace CoreCompactNonSober.Localization

open Set Cardinal
open Ambient (Coordinate Alphabet alphabetSize distinguishedLetter)

abbrev Width := Coordinate → ℕ

@[ext] structure Slalom (X : Coordinate → Type) (w : Width) where
  list : (j : Coordinate) → Finset (X j)
  bound : ∀ j, (list j).card ≤ w j

def Captures {X : Coordinate → Type} {w : Width}
    (s : Slalom X w) (x : (j : Coordinate) → X j) : Prop :=
  ∃ N : ℕ, ∀ j : Coordinate, N ≤ j.val → x j ∈ s.list j

def IsCapturing {X : Coordinate → Type} {w : Width}
    (F : Set (Slalom X w)) : Prop :=
  ∀ x : (j : Coordinate) → X j, ∃ s ∈ F, Captures s x

noncomputable def loc (X : Coordinate → Type) (w : Width) : Cardinal :=
  sInf {c : Cardinal | ∃ F : Set (Slalom X w), IsCapturing F ∧ Cardinal.mk F = c}

def singletonSlalom {X : Coordinate → Type} {w : Width}
    (hw : ∀ j, 0 < w j) (x : (j : Coordinate) → X j) : Slalom X w where
  list j := {x j}
  bound j := by simpa only [Finset.card_singleton] using hw j

theorem singleton_captures {X : Coordinate → Type} {w : Width}
    (hw : ∀ j, 0 < w j) (x : (j : Coordinate) → X j) :
    Captures (singletonSlalom hw x) x :=
  ⟨0, fun _ _ ↦ Finset.mem_singleton_self _⟩

theorem singleton_family_capturing {X : Coordinate → Type} {w : Width}
    (hw : ∀ j, 0 < w j) : IsCapturing (Set.range (singletonSlalom (X := X) hw)) := by
  intro x
  exact ⟨singletonSlalom hw x, Set.mem_range_self x, singleton_captures hw x⟩

theorem loc_le_family {X : Coordinate → Type} {w : Width}
    {F : Set (Slalom X w)} (hF : IsCapturing F) : loc X w ≤ Cardinal.mk F :=
  csInf_le (OrderBot.bddBelow _) ⟨F, hF, rfl⟩

theorem exists_minimal_family {X : Coordinate → Type} {w : Width}
    (hw : ∀ j, 0 < w j) :
    ∃ F : Set (Slalom X w), IsCapturing F ∧ Cardinal.mk F = loc X w := by
  change loc X w ∈ {c : Cardinal |
    ∃ F : Set (Slalom X w), IsCapturing F ∧ Cardinal.mk F = c}
  unfold loc
  apply csInf_mem
  exact ⟨_, Set.range (singletonSlalom (X := X) hw), singleton_family_capturing hw, rfl⟩

theorem loc_le_product {X : Coordinate → Type} {w : Width}
    (hw : ∀ j, 0 < w j) : loc X w ≤ Cardinal.mk ((j : Coordinate) → X j) :=
  (loc_le_family (singleton_family_capturing hw)).trans Cardinal.mk_range_le

theorem small_family_not_capturing {X : Coordinate → Type} {w : Width}
    {F : Set (Slalom X w)} (hsmall : Cardinal.mk F < loc X w) : ¬ IsCapturing F :=
  fun hF ↦ not_le_of_gt hsmall (loc_le_family hF)

def widen {X : Coordinate → Type} {w v : Width} (hwv : ∀ j, w j ≤ v j)
    (s : Slalom X w) : Slalom X v where
  list := s.list
  bound j := (s.bound j).trans (hwv j)

theorem loc_antitone_width {X : Coordinate → Type} {w v : Width}
    (hw : ∀ j, 0 < w j) (hwv : ∀ j, w j ≤ v j) : loc X v ≤ loc X w := by
  obtain ⟨F, hF, hcard⟩ := exists_minimal_family (X := X) hw
  have hcapt : IsCapturing (widen hwv '' F) := by
    intro x
    obtain ⟨s, hs, hx⟩ := hF x
    exact ⟨widen hwv s, ⟨s, hs, rfl⟩, hx⟩
  exact (loc_le_family hcapt).trans (Cardinal.mk_image_le.trans_eq hcard)

/-- The width `b_j = 2^j` in `eq:lambda`. -/
def baseWidth (j : Coordinate) : ℕ := 2 ^ j.val

noncomputable def lambda : Cardinal := loc Alphabet baseWidth

theorem baseWidth_pos (j : Coordinate) : 0 < baseWidth j := by
  unfold baseWidth
  positivity

theorem baseWidth_lt_alphabetSize (j : Coordinate) : baseWidth j < alphabetSize j := by
  unfold baseWidth alphabetSize
  gcongr
  · norm_num
  · exact j.val.lt_two_pow_self

theorem sequence_misses (s : ℕ → Slalom Alphabet baseWidth) :
    ∃ x : (j : Coordinate) → Alphabet j, ∀ m, ¬ Captures (s m) x := by
  classical
  have hex : ∀ j : Coordinate,
      ∃ z : Alphabet j, z ∉ (s (Nat.unpair (j.val - 2)).1).list j := by
    intro j
    have hcard : ((s (Nat.unpair (j.val - 2)).1).list j).card <
        (Finset.univ : Finset (Alphabet j)).card := by
      simp only [Finset.card_univ, Fintype.card_fin]
      exact ((s _).bound j).trans_lt (baseWidth_lt_alphabetSize j)
    obtain ⟨z, _, hz⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
    exact ⟨z, hz⟩
  choose x hx using hex
  refine ⟨x, ?_⟩
  intro m hm
  obtain ⟨N, hN⟩ := hm
  let j : Coordinate := ⟨Nat.pair m N + 2, by omega⟩
  have hjN : N ≤ j.val := (Nat.right_le_pair m N).trans (by dsimp [j]; omega)
  have hj : (Nat.unpair (j.val - 2)).1 = m := by
    simp [j, Nat.unpair_pair]
  have hmiss := hx j
  rw [hj] at hmiss
  exact hmiss (hN j hjN)

theorem countable_family_not_capturing (F : Set (Slalom Alphabet baseWidth))
    (hF : F.Countable) : ¬ IsCapturing F := by
  intro hcapt
  have hne : F.Nonempty := by
    obtain ⟨s, hs, _⟩ := hcapt distinguishedLetter
    exact ⟨s, hs⟩
  haveI : Nonempty F := hne.to_subtype
  haveI : Countable F := hF.to_subtype
  obtain ⟨f, hf⟩ := exists_surjective_nat F
  obtain ⟨x, hx⟩ := sequence_misses (fun m ↦ (f m).val)
  obtain ⟨s, hs, hcap⟩ := hcapt x
  obtain ⟨m, hm⟩ := hf ⟨s, hs⟩
  have hms : (f m).val = s := congrArg Subtype.val hm
  exact hx m (hms.symm ▸ hcap)

theorem aleph0_lt_lambda : Cardinal.aleph0 < lambda := by
  apply lt_of_not_ge
  intro hle
  obtain ⟨F, hcapt, hcard⟩ := exists_minimal_family (X := Alphabet) baseWidth_pos
  have hcount : F.Countable :=
    Cardinal.le_aleph0_iff_set_countable.mp (hcard ▸ hle)
  exact countable_family_not_capturing F hcount hcapt

theorem lambda_bounds : Cardinal.aleph 1 ≤ lambda ∧ lambda ≤ Cardinal.continuum := by
  constructor
  · exact Cardinal.aleph_one_le_iff.mpr aleph0_lt_lambda
  · exact (loc_le_product (X := Alphabet) baseWidth_pos).trans
      (mk_countable_pi_le_continuum Alphabet)

end CoreCompactNonSober.Localization
