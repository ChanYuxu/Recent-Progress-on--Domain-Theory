import CoreCompactNonSober.Capacity
import Mathlib.Data.Fintype.Order
import Mathlib.Data.Fintype.Powerset
import Mathlib.Order.CompleteLatticeIntervals

/-!
# The ambient complete lattice

Source: `lem:lattice`. The complete-lattice structure is built on the
reviewed coordinatewise partial order. Suprema use unions of configurations
and the supremum of heights. Infima truncate the height by the capacities of
the intersection configurations, exactly as in the manuscript.
-/

set_option autoImplicit false

namespace CoreCompactNonSober.Ambient

open Set

noncomputable instance coordinateCompleteLattice (j : Coordinate) :
    CompleteLattice (Finset (Alphabet j)) :=
  Fintype.toCompleteLattice _

/-- The capacity as an element of the unit interval. -/
noncomputable def capacityHeight (j : Coordinate) (A : Finset (Alphabet j)) : Height :=
  ⟨capacity j A, capacity_nonneg j A, capacity_le_one j A⟩

/-- Suprema in the ambient carrier, including the empty supremum. -/
noncomputable def join (E : Set Carrier) : Carrier :=
  ⟨(sSup ((fun p : Carrier ↦ p.val.1) '' E),
    fun j ↦ sSup ((fun p : Carrier ↦ configuration p j) '' E)), by
      intro j
      change sSup ((fun p : Carrier ↦ p.val.1) '' E) ≤
        capacityHeight j (sSup ((fun p : Carrier ↦ configuration p j) '' E))
      apply sSup_le
      rintro _ ⟨p, hp, rfl⟩
      exact (p.property j).trans (capacity_monotone j
        (le_sSup (Set.mem_image_of_mem (fun p : Carrier ↦ configuration p j) hp)))⟩

theorem join_isLUB (E : Set Carrier) : IsLUB E (join E) := by
  constructor
  · intro p hp
    refine (le_iff p (join E)).mpr ⟨?_, ?_⟩
    · exact le_sSup (Set.mem_image_of_mem (fun p : Carrier ↦ p.val.1) hp)
    · intro j
      exact le_sSup (Set.mem_image_of_mem (fun p : Carrier ↦ configuration p j) hp)
  · intro q hq
    refine (le_iff (join E) q).mpr ⟨?_, ?_⟩
    · change sSup ((fun p : Carrier ↦ p.val.1) '' E) ≤ q.val.1
      apply sSup_le
      rintro _ ⟨p, hp, rfl⟩
      exact ((le_iff p q).mp (hq hp)).1
    · intro j
      change sSup ((fun p : Carrier ↦ configuration p j) '' E) ≤ configuration q j
      apply sSup_le
      rintro _ ⟨p, hp, rfl⟩
      exact ((le_iff p q).mp (hq hp)).2 j

noncomputable instance : SupSet Carrier := ⟨join⟩

/-- The complete lattice preserves the original partial order by
construction: `completeLatticeOfSup` extends the supplied `PartialOrder`. -/
noncomputable instance : CompleteLattice Carrier :=
  completeLatticeOfSup Carrier join_isLUB

theorem sSup_eq_join (E : Set Carrier) : sSup E = join E := rfl

theorem height_sSup_interval (E : Set Carrier) :
    (sSup E).val.1 = sSup ((fun p : Carrier ↦ p.val.1) '' E) := rfl

theorem configuration_sSup (E : Set Carrier) (j : Coordinate) :
    configuration (sSup E) j =
      sSup ((fun p : Carrier ↦ configuration p j) '' E) := rfl

/-- The real height formula of `eq:join`, with its source nonemptiness
hypothesis. The empty join instead has height zero. -/
theorem height_sSup (E : Set Carrier) (hE : E.Nonempty) :
    height (sSup E) = sSup (height '' E) := by
  change (sSup ((fun p : Carrier ↦ p.val.1) '' E) : Height).val = _
  rw [Set.Icc.coe_sSup (by norm_num) (hE.image _), Set.image_image]
  rfl

/-- Membership in an arbitrary supremum of finite coordinate sets is
membership in one of the input sets: thus the configuration supremum is
the literal union from the manuscript. -/
theorem mem_coordinate_sSup (j : Coordinate)
    (E : Set (Finset (Alphabet j))) (z : Alphabet j) :
    z ∈ sSup E ↔ ∃ A ∈ E, z ∈ A := by
  constructor
  · intro hz
    by_contra h
    have hsup : sSup E ≤ Finset.univ \ {z} := by
      apply sSup_le
      intro A hA a ha
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_singleton]
      intro haz
      subst a
      exact h ⟨A, hA, ha⟩
    have hz' := hsup hz
    simp at hz'
  · rintro ⟨A, hA, hzA⟩
    exact (le_sSup hA) hzA

theorem mem_configuration_sSup (E : Set Carrier)
    (j : Coordinate) (z : Alphabet j) :
    z ∈ configuration (sSup E) j ↔
      ∃ p ∈ E, z ∈ configuration p j := by
  rw [configuration_sSup, mem_coordinate_sSup]
  constructor
  · rintro ⟨_, ⟨p, hp, rfl⟩, hz⟩
    exact ⟨p, hp, hz⟩
  · rintro ⟨p, hp, hz⟩
    exact ⟨configuration p j, ⟨p, hp, rfl⟩, hz⟩

/-- An unrestricted full-configuration point at any allowed height. -/
noncomputable def fullAt (t : Height) : Carrier :=
  ⟨(t, fun _ ↦ Finset.univ), by
    intro j
    rw [capacity_univ]
    exact t.property.2⟩

@[simp] theorem height_fullAt (t : Height) : height (fullAt t) = t.val := rfl

@[simp] theorem configuration_fullAt (t : Height) (j : Coordinate) :
    configuration (fullAt t) j = Finset.univ := rfl

noncomputable def bottomPoint : Carrier :=
  ⟨(⟨0, by norm_num, by norm_num⟩, fun _ ↦ ∅), by
    intro j
    exact capacity_nonneg j ∅⟩

theorem bottom_eq_bottomPoint : (⊥ : Carrier) = bottomPoint := by
  apply le_antisymm
  · exact bot_le
  · refine (le_iff bottomPoint (⊥ : Carrier)).mpr ⟨?_, ?_⟩
    · exact (⊥ : Carrier).val.1.property.1
    · intro j
      exact Finset.empty_subset _

theorem top_eq_fullAt_one :
    (⊤ : Carrier) = fullAt ⟨1, by norm_num, le_rfl⟩ := by
  apply le_antisymm
  · refine (le_iff (⊤ : Carrier) _).mpr ⟨?_, ?_⟩
    · exact (⊤ : Carrier).val.1.property.2
    · intro j
      exact Finset.subset_univ _
  · exact le_top

/-- The source's intersection configurations for an arbitrary family. -/
noncomputable def meetConfiguration (E : Set Carrier) : Configuration :=
  fun j ↦ sInf ((fun p : Carrier ↦ configuration p j) '' E)

/-- The height correction in `eq:meet`. Suprema/infima in `Height` already
include the source's empty-family conventions. -/
noncomputable def meetHeight (E : Set Carrier) : Height :=
  sInf ((fun p : Carrier ↦ p.val.1) '' E) ⊓
    ⨅ j : Coordinate, capacityHeight j (meetConfiguration E j)

noncomputable def meet (E : Set Carrier) : Carrier :=
  ⟨(meetHeight E, meetConfiguration E), by
    intro j
    exact (inf_le_right.trans (iInf_le (fun j : Coordinate ↦
      capacityHeight j (meetConfiguration E j)) j) :
        meetHeight E ≤ capacityHeight j (meetConfiguration E j))⟩

theorem meet_isGLB (E : Set Carrier) : IsGLB E (meet E) := by
  constructor
  · intro p hp
    refine (le_iff (meet E) p).mpr ⟨?_, ?_⟩
    · exact inf_le_left.trans (sInf_le
        (Set.mem_image_of_mem (fun p : Carrier ↦ p.val.1) hp))
    · intro j
      exact sInf_le (Set.mem_image_of_mem (fun p : Carrier ↦ configuration p j) hp)
  · intro q hq
    refine (le_iff q (meet E)).mpr ⟨?_, ?_⟩
    · change q.val.1 ≤ meetHeight E
      apply le_inf
      · apply le_sInf
        rintro _ ⟨p, hp, rfl⟩
        exact ((le_iff q p).mp (hq hp)).1
      · apply le_iInf
        intro j
        have hconfig : configuration q j ≤ meetConfiguration E j := by
          apply le_sInf
          rintro _ ⟨p, hp, rfl⟩
          exact ((le_iff q p).mp (hq hp)).2 j
        exact (q.property j).trans (capacity_monotone j hconfig)
    · intro j
      change configuration q j ≤ sInf ((fun p : Carrier ↦ configuration p j) '' E)
      apply le_sInf
      rintro _ ⟨p, hp, rfl⟩
      exact ((le_iff q p).mp (hq hp)).2 j

theorem sInf_eq_meet (E : Set Carrier) : sInf E = meet E :=
  (isGLB_sInf E).unique (meet_isGLB E)

theorem configuration_sInf (E : Set Carrier) (j : Coordinate) :
    configuration (sInf E) j =
      sInf ((fun p : Carrier ↦ configuration p j) '' E) := by
  rw [sInf_eq_meet]
  rfl

theorem configuration_inf (p q : Carrier) (j : Coordinate) :
    configuration (p ⊓ q) j = configuration p j ∩ configuration q j := by
  rw [← sInf_pair, configuration_sInf, Set.image_pair, sInf_pair]
  rfl

theorem carrier_isDcpo : CoreCompactNonSober.IsDcpo Carrier := by
  intro E _
  exact ⟨sSup E, isLUB_sSup E⟩

end CoreCompactNonSober.Ambient
