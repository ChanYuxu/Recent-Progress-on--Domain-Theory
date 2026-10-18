import CoreCompactNonSober.ConstructionRecursion
import CoreCompactNonSober.SubDcpoTopology

/-!
# The actual retained subset and completed static/dynamic tasks

Source: `eq:D-definition` and `prop:two-conditions`. The subset below is the literal union of the
zero layer and the packets produced by the proved transfinite recursion.
-/

set_option autoImplicit false

namespace CoreCompactNonSober.Construction

open Set Cardinal Ambient Localization

def retained : Set Carrier := zeroLayer ∪ {p | ∃ α : Stage, p ∈ (packets α).members}

theorem zeroLayer_subset_retained : zeroLayer ⊆ retained := Set.subset_union_left

theorem packet_subset_retained (α : Stage) : (packets α).members ⊆ retained :=
  fun _ hp ↦ Or.inr ⟨α, hp⟩

theorem retained_height_lt_one {p : Carrier} (hp : p ∈ retained) : height p < 1 := by
  rcases hp with hz | ⟨α, hα⟩
  · change height p = 0 at hz
    rw [hz]
    norm_num
  · exact ((packets α).member_properties hα).2

theorem positive_retained_label {p : Carrier} (hp : p ∈ retained) (hpos : Positive p) :
    ∃ α : Stage, ∃ n : ℕ, (packets α).entry n = some p := by
  rcases hp with hz | ⟨α, hα⟩
  · change height p = 0 at hz
    exact False.elim (ne_of_gt hpos hz)
  · obtain ⟨n, hn⟩ := hα
    exact ⟨α, n, hn⟩

/-- The unique selected-point index asserted immediately after
`eq:stage-order`, including uniqueness within a row. -/
theorem positive_retained_unique_label {p : Carrier} (hp : p ∈ retained)
    (hpos : Positive p) :
    ∃! l : PotentialLabel, (packets l.1).entry l.2 = some p := by
  obtain ⟨α, n, hn⟩ := positive_retained_label hp hpos
  refine ⟨(α, n), hn, ?_⟩
  rintro ⟨β, m⟩ hm
  have hβα : β = α := by
    rcases lt_trichotomy β α with hlt | heq | hgt
    · exact False.elim (packet_chronology hlt ⟨m, hm⟩ ⟨n, hn⟩ le_rfl)
    · exact heq
    · exact False.elim (packet_chronology hgt ⟨n, hn⟩ ⟨m, hm⟩ le_rfl)
  subst β
  have hmn : m = n := (packets α).entry_injective hm hn
  exact Prod.ext rfl hmn

theorem positive_retained_hasHole {p : Carrier} (hp : p ∈ retained) (hpos : Positive p) :
    HasHole p := by
  obtain ⟨α, n, hn⟩ := positive_retained_label hp hpos
  apply (resultAt α).holes p
  rw [← packets_eq_result α]
  exact ⟨n, hn⟩

theorem positive_retained_tailOmission {p : Carrier} (hp : p ∈ retained) (hpos : Positive p) :
    TailOmission p := by
  obtain ⟨α, n, hn⟩ := positive_retained_label hp hpos
  apply (resultAt α).tailOmissions p
  rw [← packets_eq_result α]
  exact ⟨n, hn⟩

theorem stock_subset_retained (α : Stage) :
    stock (fun β : Set.Iio α ↦ packets β.val) ⊆ retained := by
  rintro p ⟨⟨β, n⟩, hn⟩
  exact packet_subset_retained β.val ⟨n, hn⟩

theorem Packet.EndpointsIn.mono {K : Packet} {P Q : Set Carrier}
    (hK : K.EndpointsIn P) (hPQ : P ⊆ Q) : K.EndpointsIn Q := by
  cases K with
  | empty => trivial
  | single _ _ _ => trivial
  | row p b _ _ _ _ => exact hPQ hK

theorem packet_endpoints_retained (α : Stage) : (packets α).EndpointsIn retained := by
  rw [packets_eq_result α]
  exact (resultAt α).endpointsIn.mono (stock_subset_retained α)

/-- Every occurrence of a static task is processed, with occurrences after
every prescribed stage; no regularity or upper bound on countably many
stages is used. -/
theorem static_task_cofinally_processed (k : StaticKey) (after : Stage) :
    ∃ α : Stage, after < α ∧ scheduledKey α = Sum.inl k ∧
      ∃ s ∈ (packets α).members, s ≤ k.val.1.val ∧ s ∈ printedBasicSet k.val.2 := by
  obtain ⟨α, hafter, hkey⟩ := scheduledKey_unbounded (Sum.inl k) after
  refine ⟨α, hafter, hkey, ?_⟩
  rw [packets_eq_result α]
  exact (resultAt α).static_processed k hkey

/-- Every eligible label/reference task is processed again after any chosen
stage. This statement uses the actual specified row packet, not merely a
downstream-sufficient family of points. -/
theorem dynamic_task_cofinally_processed (l : PotentialLabel) (p : Carrier)
    (hl : (packets l.1).entry l.2 = some p) (b : Reference)
    (hpb : height p ≤ height b.val) (after : Stage) :
    ∃ α : Stage, after < α ∧ l.1 < α ∧ scheduledKey α = Sum.inr (l, b) ∧
      ∃ (hp : Positive p) (hp1 : height p < 1)
        (hpb' : height p ≤ height b.val) (R : PairRow p b.val),
          Protects (stock (fun β : Set.Iio α ↦ packets β.val)) R.pattern ∧
            packets α = Packet.row p b.val hp hp1 hpb' R := by
  obtain ⟨α, hα, hkey⟩ := scheduledKey_unbounded (Sum.inr (l, b)) (max after l.1)
  have hafter : after < α := (le_max_left _ _).trans_lt hα
  have hlα : l.1 < α := (le_max_right _ _).trans_lt hα
  have hlookup : lookupBefore α (fun β : Set.Iio α ↦ packets β.val) l = some p := by
    rw [lookupBefore_eq α _ l hlα]
    exact hl
  refine ⟨α, hafter, hlα, hkey, ?_⟩
  rw [packets_eq_result α]
  exact (resultAt α).dynamic_shape (l, b) hkey p hlookup hpb

def HasReferenceRows (S : Set Carrier) : Prop :=
  ∀ p ∈ S, Positive p → ∀ b ∈ referenceFamily, height p ≤ height b →
    ∃ R : PairRow p b, ∀ n, R.point n ∈ S

theorem retained_referenceRows : HasReferenceRows retained := by
  intro p hp hppos b hb hpb
  obtain ⟨αp, np, hplabel⟩ := positive_retained_label hp hppos
  let d : DynamicKey := ((αp, np), ⟨b, hb⟩)
  obtain ⟨α, hαp, hkey⟩ := scheduledKey_unbounded (Sum.inr d) αp
  have hl : lookupBefore α (fun β : Set.Iio α ↦ packets β.val) d.1 = some p := by
    rw [lookupBefore_eq α _ d.1 hαp]
    exact hplabel
  obtain ⟨_, _, _, R, _, hpacket⟩ := (resultAt α).dynamic_shape d hkey p hl hpb
  refine ⟨R, ?_⟩
  intro n
  apply packet_subset_retained α
  rw [packets_eq_result α, hpacket]
  exact ⟨n, rfl⟩

theorem retained_lowerApproximation : LowerApproximation retained := by
  classical
  letI : TopologicalSpace Carrier := scottTopology Carrier
  intro p U hpU
  by_cases hpos : Positive p
  · obtain ⟨W, hWB, hpB, hBU⟩ :=
      printedBasic_isTopologicalBasis.exists_subset_of_mem_open hpU U.isOpen
    obtain ⟨B, rfl⟩ := hWB
    let V : ScottOpens Carrier := ⟨printedBasicSet B, printedBasicSet_isOpen_scott B⟩
    obtain ⟨b, hbB, hbV, hbp⟩ := witnessFamily_approx p hpos V hpB
    let k : StaticKey := ⟨(⟨b, hbB⟩, B), hbV⟩
    obtain ⟨α, _, hkey⟩ := scheduledKey_unbounded (Sum.inl k)
      (Classical.choice (inferInstance : Nonempty Stage))
    obtain ⟨s, hspacket, hsb, hsV⟩ := (resultAt α).static_processed k hkey
    have hsS : s ∈ retained := by
      apply packet_subset_retained α
      rw [packets_eq_result α]
      exact hspacket
    exact ⟨⟨s, hsS⟩, hsb.trans hbp, hBU hsV⟩
  · have hz : height p = 0 := le_antisymm (le_of_not_gt hpos) p.val.1.property.1
    exact ⟨⟨p, zeroLayer_subset_retained hz⟩, le_rfl, hpU⟩

theorem retained_proper : retained ⊂ Set.univ := by
  refine Set.ssubset_iff_subset_ne.mpr ⟨Set.subset_univ _, ?_⟩
  intro heq
  have htop : (⊤ : Carrier) ∈ retained := by rw [heq]; trivial
  have hlt := retained_height_lt_one htop
  rw [top_eq_fullAt_one] at hlt
  change (1 : ℝ) < 1 at hlt
  exact lt_irrefl _ hlt

theorem retained_cardinality : Cardinal.mk retained = Cardinal.continuum := by
  apply le_antisymm ((Cardinal.mk_set_le retained).trans carrier_cardinality_le)
  rw [← zeroLayer_cardinality]
  exact Cardinal.mk_le_mk_of_subset zeroLayer_subset_retained

theorem retained_noGreatest : NoGreatestElement retained := by
  intro htop
  obtain ⟨p, hp⟩ := htop
  letI : TopologicalSpace Carrier := scottTopology Carrier
  let U : ScottOpens Carrier :=
    ⟨heightAbove (height p.val), (isOpen_scott_iff _).mpr (heightAbove_isScottOpen _)⟩
  have htopU : (⊤ : Carrier) ∈ U := by
    change height p.val < height (⊤ : Carrier)
    rw [top_eq_fullAt_one]
    exact retained_height_lt_one p.property
  obtain ⟨s, _, hsU⟩ := retained_lowerApproximation (⊤ : Carrier) U htopU
  have hle : height s.val ≤ height p.val := ((le_iff _ _).mp (hp s)).1
  exact not_lt_of_ge hle hsU

theorem retained_compact : ScottCompact retained := by
  have hbot : (⊥ : Carrier) ∈ retained := by
    apply zeroLayer_subset_retained
    rw [bottom_eq_bottomPoint]
    rfl
  let b : retained := ⟨⊥, hbot⟩
  apply scottCompact_of_least b
  intro q
  change (⊥ : Carrier) ≤ q.val
  exact bot_le

end CoreCompactNonSober.Construction
