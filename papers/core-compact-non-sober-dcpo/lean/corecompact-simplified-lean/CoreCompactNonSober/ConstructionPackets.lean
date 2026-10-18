import CoreCompactNonSober.ConstructionSchedule
import CoreCompactNonSober.PairInsertion

/-!
# Insertion packets and the actual predecessor stock

Source: `eq:stage-size` and the recursive-construction section. Packets have at most countably many labeled entries;
all their entries are positive and have height less than one. The stock
before a stage is the actual partial range of earlier packet labels.
-/

set_option autoImplicit false

namespace CoreCompactNonSober.Construction

open Set Cardinal Ambient Localization

def optionRange {ι α : Type} (f : ι → Option α) : Set α :=
  {x | ∃ i, f i = some x}

theorem optionRange_card_le {ι α : Type} (f : ι → Option α) :
    Cardinal.mk (optionRange f) ≤ Cardinal.mk ι := by
  classical
  let idx : optionRange f → ι := fun x ↦ Classical.choose x.property
  have hidx : ∀ x : optionRange f, f (idx x) = some x.val :=
    fun x ↦ Classical.choose_spec x.property
  apply Cardinal.mk_le_of_injective (f := idx)
  intro x y h
  apply Subtype.ext
  exact Option.some.inj ((hidx x).symm.trans ((congrArg f h).trans (hidx y)))

inductive Packet where
  | empty
  | single (p : Carrier) (positive : Positive p) (height_lt : height p < 1)
  | row (p b : Carrier) (positive : Positive p) (height_lt : height p < 1)
      (height_le_partner : height p ≤ height b) (data : PairRow p b)

def Packet.entry : Packet → ℕ → Option Carrier
  | .empty, _ => none
  | .single p _ _, n => if n = 0 then some p else none
  | .row _ _ _ _ _ R, n => some (R.point n)

def Packet.members (K : Packet) : Set Carrier := optionRange K.entry

/-- Within each of the three printed packet forms, selected points have a
unique internal natural-number label. -/
theorem Packet.entry_injective (K : Packet) {n m : ℕ} {p : Carrier}
    (hn : K.entry n = some p) (hm : K.entry m = some p) : n = m := by
  cases K with
  | empty => cases hn
  | single q hq hq1 =>
    have hn0 : n = 0 := by
      by_contra h
      simp only [Packet.entry, if_neg h] at hn
      cases hn
    have hm0 : m = 0 := by
      by_contra h
      simp only [Packet.entry, if_neg h] at hm
      cases hm
    exact hn0.trans hm0.symm
  | row q b hq hq1 hqb R =>
    exact R.strictMono.injective (Option.some.inj (hn.trans hm.symm))

theorem Packet.not_mem_empty (x : Carrier) : x ∉ Packet.empty.members := by
  rintro ⟨n, hn⟩
  cases hn

theorem Packet.mem_single_iff (p : Carrier) (hp : Positive p) (hp1 : height p < 1)
    (x : Carrier) : x ∈ (Packet.single p hp hp1).members ↔ x = p := by
  constructor
  · rintro ⟨n, hn⟩
    by_cases hn0 : n = 0
    · subst n
      exact (Option.some.inj hn).symm
    · simp only [Packet.entry, if_neg hn0] at hn
      cases hn
  · rintro rfl
    exact ⟨0, rfl⟩

theorem Packet.mem_row_iff (p b : Carrier) (hp : Positive p) (hp1 : height p < 1)
    (hpb : height p ≤ height b) (R : PairRow p b) (x : Carrier) :
    x ∈ (Packet.row p b hp hp1 hpb R).members ↔ x ∈ Set.range R.point := by
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, Option.some.inj hn⟩
  · rintro ⟨n, rfl⟩
    exact ⟨n, rfl⟩

theorem Packet.member_properties (K : Packet) {x : Carrier} (hx : x ∈ K.members) :
    Positive x ∧ height x < 1 := by
  cases K with
  | empty => exact False.elim (Packet.not_mem_empty x hx)
  | single p hp hp1 =>
    have heq := (Packet.mem_single_iff p hp hp1 x).mp hx
    subst x
    exact ⟨hp, hp1⟩
  | row p b hp hp1 hpb R =>
    obtain ⟨n, rfl⟩ := (Packet.mem_row_iff p b hp hp1 hpb R x).mp hx
    exact ⟨R.positive n, (R.height_lt n).trans hp1⟩

def Packet.EndpointsIn (K : Packet) (P : Set Carrier) : Prop :=
  match K with
  | .empty => True
  | .single _ _ _ => True
  | .row p _ _ _ _ _ => p ∈ P

def stock {α : Stage} (prev : Set.Iio α → Packet) : Set Carrier :=
  optionRange (fun l : (Set.Iio α) × ℕ ↦ (prev l.1).entry l.2)

/-- The option-labelled stock is exactly the printed union of all preceding
packets, not a smaller selected stock or a larger closure. -/
theorem stock_eq_predecessor_union {α : Stage} (prev : Set.Iio α → Packet) :
    stock prev = {p | ∃ β : Set.Iio α, p ∈ (prev β).members} := by
  ext p
  constructor
  · rintro ⟨⟨β, n⟩, hn⟩
    exact ⟨β, n, hn⟩
  · rintro ⟨β, n, hn⟩
    exact ⟨(β, n), hn⟩

theorem stock_small {α : Stage} (prev : Set.Iio α → Packet) :
    Cardinal.mk (stock prev) < lambda :=
  (optionRange_card_le _).trans_lt (predecessor_countable_stock_small α)

/-- Both inequalities of the printed stage-size estimate; the right-hand
cardinality is the predecessor initial segment, not a regularity bound. -/
theorem stock_stage_size {α : Stage} (prev : Set.Iio α → Packet) :
    Cardinal.mk (stock prev) ≤ max (Cardinal.mk (Set.Iio α)) Cardinal.aleph0 ∧
      max (Cardinal.mk (Set.Iio α)) Cardinal.aleph0 < lambda :=
  ⟨(optionRange_card_le _).trans (predecessor_countable_stock_card_le α),
    max_lt (stage_predecessors_small α) aleph0_lt_lambda⟩

theorem stock_properties {α : Stage} (prev : Set.Iio α → Packet)
    {x : Carrier} (hx : x ∈ stock prev) : Positive x ∧ height x < 1 := by
  obtain ⟨⟨β, n⟩, hn⟩ := hx
  exact (prev β).member_properties ⟨n, hn⟩

noncomputable def lookupBefore (α : Stage) (prev : Set.Iio α → Packet)
    (l : PotentialLabel) : Option Carrier :=
  if hl : l.1 < α then (prev ⟨l.1, hl⟩).entry l.2 else none

theorem lookupBefore_eq (α : Stage) (prev : Set.Iio α → Packet)
    (l : PotentialLabel) (hl : l.1 < α) :
    lookupBefore α prev l = (prev ⟨l.1, hl⟩).entry l.2 := by
  simp only [lookupBefore, dif_pos hl]

theorem lookupBefore_mem_stock {α : Stage} (prev : Set.Iio α → Packet)
    (l : PotentialLabel) {p : Carrier} (hp : lookupBefore α prev l = some p) : p ∈ stock prev := by
  classical
  by_cases hl : l.1 < α
  · rw [lookupBefore_eq α prev l hl] at hp
    exact ⟨(⟨l.1, hl⟩, l.2), hp⟩
  · simp only [lookupBefore, dif_neg hl] at hp
    cases hp

end CoreCompactNonSober.Construction
