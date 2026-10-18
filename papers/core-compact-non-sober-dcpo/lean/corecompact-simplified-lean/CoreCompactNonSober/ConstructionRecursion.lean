import CoreCompactNonSober.ConstructionPackets
import CoreCompactNonSober.SingleInsertion

/-!
# The protected transfinite recursion

Source: recursive-construction section, lines 908–971. A genuine well-founded recursion on the initial
ordinal chooses a proved-valid packet at each stage. The proof-bearing
step record is constructed from the insertion theorems; its existence is
not an additional hypothesis or axiom.
-/

set_option autoImplicit false

namespace CoreCompactNonSober.Construction

open Set Cardinal Ambient Localization

local instance : TopologicalSpace Carrier := scottTopology Carrier

structure StepResult (α : Stage) (prev : Set.Iio α → Packet) (key : Key) where
  packet : Packet
  protects : ∀ x ∈ stock prev, ∀ y ∈ packet.members, ¬ x ≤ y
  endpointsIn : packet.EndpointsIn (stock prev)
  static_processed : ∀ k : StaticKey, key = Sum.inl k →
    ∃ s ∈ packet.members, s ≤ k.val.1.val ∧ s ∈ printedBasicSet k.val.2
  dynamic_processed : ∀ d : DynamicKey, key = Sum.inr d →
    ∀ p : Carrier, lookupBefore α prev d.1 = some p →
      height p ≤ height d.2.val →
        ∃ R : PairRow p d.2.val, ∀ n, R.point n ∈ packet.members
  static_shape : ∀ k : StaticKey, key = Sum.inl k →
    ∃ (s : Carrier) (hs : Positive s) (hs1 : height s < 1),
      SingleInsertionRecipe (stock prev) k.val.1.val
        (⟨printedBasicSet k.val.2, printedBasicSet_isOpen_scott _⟩ : ScottOpens Carrier) s ∧
        packet = Packet.single s hs hs1
  dynamic_shape : ∀ d : DynamicKey, key = Sum.inr d →
    ∀ p : Carrier, lookupBefore α prev d.1 = some p →
      height p ≤ height d.2.val →
        ∃ (hp : Positive p) (hp1 : height p < 1)
          (hpb : height p ≤ height d.2.val) (R : PairRow p d.2.val),
          Protects (stock prev) R.pattern ∧
            packet = Packet.row p d.2.val hp hp1 hpb R
  ineligible_empty : ∀ d : DynamicKey, key = Sum.inr d →
    (∀ p : Carrier, lookupBefore α prev d.1 = some p → ¬ height p ≤ height d.2.val) →
      packet = Packet.empty
  holes : ∀ y ∈ packet.members, HasHole y
  tailOmissions : ∀ y ∈ packet.members, TailOmission y

theorem stepResult_nonempty (α : Stage) (prev : Set.Iio α → Packet) (key : Key) :
    Nonempty (StepResult α prev key) := by
  classical
  letI : TopologicalSpace Carrier := scottTopology Carrier
  have hP : ∀ x ∈ stock prev, Positive x := fun _ hx ↦ (stock_properties prev hx).1
  cases key with
  | inl k =>
    let U : ScottOpens Carrier := ⟨printedBasicSet k.val.2, printedBasicSet_isOpen_scott _⟩
    obtain ⟨s, hspos, hs1, hsb, hsU, hprotect, hhole, htail, hrecipe⟩ :=
      single_insertion_prescribed (stock prev) hP (stock_small prev) k.val.1.val
        (witnessFamily_positive _ k.val.1.property) U k.property
    refine ⟨{
      packet := Packet.single s hspos hs1
      protects := ?_
      endpointsIn := trivial
      static_processed := ?_
      dynamic_processed := ?_
      static_shape := by
        intro k' heq
        have hkk : k = k' := Sum.inl.inj heq
        subst k'
        exact ⟨s, hspos, hs1, hrecipe, rfl⟩
      dynamic_shape := by intro d heq; cases heq
      ineligible_empty := by intro d heq; cases heq
      holes := ?_
      tailOmissions := ?_ }⟩
    · intro x hx y hy
      have heq := (Packet.mem_single_iff s hspos hs1 y).mp hy
      subst y
      exact hprotect x hx
    · intro k' heq
      have hkk : k = k' := Sum.inl.inj heq
      subst k'
      exact ⟨s, ⟨0, rfl⟩, hsb, hsU⟩
    · intro d heq
      cases heq
    · intro y hy
      have heq := (Packet.mem_single_iff s hspos hs1 y).mp hy
      exact heq.symm ▸ hhole
    · intro y hy
      have heq := (Packet.mem_single_iff s hspos hs1 y).mp hy
      exact heq.symm ▸ htail
  | inr d =>
    by_cases hvalid : ∃ p : Carrier,
        lookupBefore α prev d.1 = some p ∧ height p ≤ height d.2.val
    · obtain ⟨p, hleft, hpb⟩ := hvalid
      let b : Carrier := d.2.val
      have hpold : p ∈ stock prev := lookupBefore_mem_stock prev d.1 hleft
      have hpprop := stock_properties prev hpold
      obtain ⟨R, hpattern, hprotect⟩ := pair_insertion_prescribed (stock prev) hP (stock_small prev)
        p b hpprop.1 hpprop.2 hpb
      refine ⟨{
        packet := Packet.row p b hpprop.1 hpprop.2 hpb R
        protects := ?_
        endpointsIn := hpold
        static_processed := ?_
        dynamic_processed := ?_
        static_shape := by intro k heq; cases heq
        dynamic_shape := by
          intro d' heq p' hleft' _hpb'
          have hdd : d = d' := Sum.inr.inj heq
          subst d'
          have hpeq : p' = p := Option.some.inj (hleft'.symm.trans hleft)
          subst p'
          exact ⟨hpprop.1, hpprop.2, hpb, R, hpattern, rfl⟩
        ineligible_empty := by
          intro d' heq hnot
          have hdd : d = d' := Sum.inr.inj heq
          subst d'
          exact False.elim (hnot p hleft hpb)
        holes := ?_
        tailOmissions := ?_ }⟩
      · intro x hx y hy
        obtain ⟨n, rfl⟩ := (Packet.mem_row_iff p b hpprop.1 hpprop.2 hpb R y).mp hy
        exact hprotect x hx n
      · intro k heq
        cases heq
      · intro d' heq p' hleft' _
        have hdd : d = d' := Sum.inr.inj heq
        subst d'
        have hpeq : p' = p := Option.some.inj (hleft'.symm.trans hleft)
        subst p'
        exact ⟨R, fun n ↦ ⟨n, rfl⟩⟩
      · intro y hy
        obtain ⟨n, rfl⟩ := (Packet.mem_row_iff p b hpprop.1 hpprop.2 hpb R y).mp hy
        exact R.hasHole n
      · intro y hy
        obtain ⟨n, rfl⟩ := (Packet.mem_row_iff p b hpprop.1 hpprop.2 hpb R y).mp hy
        exact R.tailOmission n
    · refine ⟨{
        packet := Packet.empty
        protects := ?_
        endpointsIn := trivial
        static_processed := ?_
        dynamic_processed := ?_
        static_shape := by intro k heq; cases heq
        dynamic_shape := by
          intro d' heq p hl hpb
          have hdd : d = d' := Sum.inr.inj heq
          subst d'
          exact False.elim (hvalid ⟨p, hl, hpb⟩)
        ineligible_empty := by intro _ _ _; rfl
        holes := ?_
        tailOmissions := ?_ }⟩
      · intro _ _ y hy
        exact False.elim (Packet.not_mem_empty y hy)
      · intro k heq
        cases heq
      · intro d' heq p hl hpb
        have hdd : d = d' := Sum.inr.inj heq
        subst d'
        exact False.elim (hvalid ⟨p, hl, hpb⟩)
      · intro y hy
        exact False.elim (Packet.not_mem_empty y hy)
      · intro y hy
        exact False.elim (Packet.not_mem_empty y hy)

noncomputable def selectStep (α : Stage) (prev : Set.Iio α → Packet) (key : Key) :
    StepResult α prev key := Classical.choice (stepResult_nonempty α prev key)

private noncomputable def packetStep (α : Stage) (prev : ∀ β : Stage, β < α → Packet) : Packet :=
  (selectStep α (fun β : Set.Iio α ↦ prev β.val β.property) (scheduledKey α)).packet

/-- The actual packet function, defined by well-founded recursion. -/
noncomputable def packets : Stage → Packet := wellFounded_lt.fix packetStep

noncomputable def resultAt (α : Stage) :
    StepResult α (fun β : Set.Iio α ↦ packets β.val) (scheduledKey α) :=
  selectStep α (fun β : Set.Iio α ↦ packets β.val) (scheduledKey α)

theorem packets_eq_result (α : Stage) : packets α = (resultAt α).packet :=
  WellFounded.fix_eq wellFounded_lt packetStep α

/-- The actual chosen static packet, not merely one available insertion,
has the source's tail-selection/deletion/neighborhood recipe. -/
theorem packets_static_prescribed (α : Stage) (k : StaticKey)
    (hkey : scheduledKey α = Sum.inl k) :
    ∃ (s : Carrier) (hs : Positive s) (hs1 : height s < 1),
      SingleInsertionRecipe (stock (fun β : Set.Iio α ↦ packets β.val)) k.val.1.val
        (⟨printedBasicSet k.val.2, printedBasicSet_isOpen_scott _⟩ : ScottOpens Carrier) s ∧
        packets α = Packet.single s hs hs1 := by
  rw [packets_eq_result α]
  exact (resultAt α).static_shape k hkey

/-- The actual chosen row packet stores a pattern satisfying the full
tail-selection specification against the whole previous stock. -/
theorem packets_dynamic_prescribed (α : Stage) (d : DynamicKey)
    (hkey : scheduledKey α = Sum.inr d) (p : Carrier)
    (hl : lookupBefore α (fun β : Set.Iio α ↦ packets β.val) d.1 = some p)
    (hpb : height p ≤ height d.2.val) :
    ∃ (hp : Positive p) (hp1 : height p < 1)
      (hpb' : height p ≤ height d.2.val) (R : PairRow p d.2.val),
        Protects (stock (fun β : Set.Iio α ↦ packets β.val)) R.pattern ∧
          packets α = Packet.row p d.2.val hp hp1 hpb' R := by
  rw [packets_eq_result α]
  exact (resultAt α).dynamic_shape d hkey p hl hpb

/-- The same post-choice recipe exposed through the manuscript's literal
basis-set task type. Repeated syntactic indices cannot weaken the recipe:
the open set in it is equal to the actual literal task's open set. -/
theorem packets_source_static_prescribed (α : Stage) (k : SourceStaticKey)
    (hkey : sourceScheduledKey α = Sum.inl k) :
    ∃ (s : Carrier) (hs : Positive s) (hs1 : height s < 1),
      SingleInsertionRecipe (stock (fun β : Set.Iio α ↦ packets β.val)) k.val.1.val
        (sourceStaticOpen k) s ∧ packets α = Packet.single s hs hs1 := by
  cases hk : scheduledKey α with
  | inl j =>
    have hjk : staticKeyToSource j = k := Sum.inl.inj (by
      simpa only [sourceScheduledKey, hk, keyToSource] using hkey)
    subst k
    obtain ⟨s, hs, hs1, hrecipe, hpacket⟩ := packets_static_prescribed α j hk
    refine ⟨s, hs, hs1, ?_, hpacket⟩
    simpa only [sourceStaticOpen_staticKeyToSource] using hrecipe
  | inr d =>
    simp only [sourceScheduledKey, hk, keyToSource] at hkey
    cases hkey

/-- The source chronology is derived from the actual recursive step. -/
theorem packet_chronology {α β : Stage} (hβα : β < α)
    {x y : Carrier} (hx : x ∈ (packets β).members) (hy : y ∈ (packets α).members) :
    ¬ x ≤ y := by
  have hxstock : x ∈ stock (fun γ : Set.Iio α ↦ packets γ.val) := by
    obtain ⟨n, hn⟩ := hx
    exact ⟨(⟨β, hβα⟩, n), hn⟩
  rw [packets_eq_result α] at hy
  exact (resultAt α).protects x hxstock y hy

end CoreCompactNonSober.Construction
