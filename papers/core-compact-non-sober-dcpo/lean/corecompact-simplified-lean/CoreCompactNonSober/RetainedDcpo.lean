import CoreCompactNonSober.RetainedConstruction
import Mathlib.Data.Nat.Lattice

/-!
# Directed completeness of the recursively retained subset

Source: `prop:D-subdcpo`. The least birth stage of a positive member forces
a cofinal tail of any directed set into one packet. A subset of a row has
either a largest row index or the row endpoint as its supremum.
-/

set_option autoImplicit false

namespace CoreCompactNonSober.Construction

open Set Cardinal Ambient Localization

theorem row_subset_supremum {p b : Carrier} (R : PairRow p b)
    (E : Set Carrier) (hne : E.Nonempty) (hER : E ⊆ Set.range R.point) :
    sSup E ∈ Set.range R.point ∨ sSup E = p := by
  classical
  let I : Set ℕ := {n | R.point n ∈ E}
  have hIne : I.Nonempty := by
    obtain ⟨e, he⟩ := hne
    obtain ⟨n, rfl⟩ := hER he
    exact ⟨n, he⟩
  by_cases hbounded : BddAbove I
  · let m := sSup I
    have hm : R.point m ∈ E := Nat.sSup_mem hIne hbounded
    have hlub : IsLUB E (R.point m) := by
      constructor
      · intro e he
        obtain ⟨n, rfl⟩ := hER he
        exact R.strictMono.monotone (le_csSup hbounded he)
      · intro q hq
        exact hq hm
    have heq : sSup E = R.point m := (isLUB_sSup E).unique hlub
    exact Or.inl ⟨m, heq.symm⟩
  · have hlub : IsLUB E p := by
      constructor
      · intro e he
        obtain ⟨n, rfl⟩ := hER he
        exact R.below_endpoint n
      · intro q hq
        apply R.isLUB.2
        rintro _ ⟨n, rfl⟩
        obtain ⟨m, hm, hnm⟩ := not_bddAbove_iff.mp hbounded n
        exact (R.strictMono.monotone hnm.le).trans (hq hm)
    exact Or.inr ((isLUB_sSup E).unique hlub)

theorem retained_sSup_mem (E : Set Carrier) (hES : E ⊆ retained)
    (hE : NonemptyDirected E) : sSup E ∈ retained := by
  classical
  by_cases hEZ : E ⊆ zeroLayer
  · exact zeroLayer_subset_retained
      (zeroLayer_isSubDcpo E hEZ hE (sSup E) (isLUB_sSup E))
  · obtain ⟨z, hzE, hzZ⟩ := Set.not_subset.mp hEZ
    have hzpos : Positive z := lt_of_le_of_ne z.val.1.property.1 (Ne.symm hzZ)
    obtain ⟨αz, nz, hzlabel⟩ := positive_retained_label (hES hzE) hzpos
    let J : Set Stage := {α | (E ∩ (packets α).members).Nonempty}
    have hJne : J.Nonempty := ⟨αz, z, hzE, nz, hzlabel⟩
    obtain ⟨β, hβJ, hmin⟩ := wellFounded_lt.has_min J hJne
    obtain ⟨x, hxE, hxpacket⟩ := hβJ
    have hxpos : Positive x := ((packets β).member_properties hxpacket).1
    let F : Set Carrier := {e | e ∈ E ∧ x ≤ e}
    have hxF : x ∈ F := ⟨hxE, le_rfl⟩
    have hF : NonemptyDirected F := by
      refine ⟨⟨x, hxF⟩, ?_⟩
      intro a ha b hb
      obtain ⟨c, hc, hac, hbc⟩ := hE.2 a ha.1 b hb.1
      exact ⟨c, ⟨hc, ha.2.trans hac⟩, hac, hbc⟩
    have hFcofinal : ∀ e ∈ E, ∃ f ∈ F, e ≤ f := by
      intro e he
      obtain ⟨f, hf, hxf, hef⟩ := hE.2 x hxE e he
      exact ⟨f, ⟨hf, hxf⟩, hef⟩
    have hsup : sSup F = sSup E := by
      apply le_antisymm
      · apply sSup_le
        intro f hf
        exact le_sSup hf.1
      · apply sSup_le
        intro e he
        obtain ⟨f, hf, hef⟩ := hFcofinal e he
        exact hef.trans (le_sSup hf)
    have hFpacket : F ⊆ (packets β).members := by
      intro e he
      have hepos : Positive e := hxpos.trans_le ((le_iff _ _).mp he.2).1
      obtain ⟨γ, n, hn⟩ := positive_retained_label (hES he.1) hepos
      have hγpacket : e ∈ (packets γ).members := ⟨n, hn⟩
      have hγJ : γ ∈ J := ⟨e, he.1, hγpacket⟩
      have hβγ : β ≤ γ := le_of_not_gt (hmin γ hγJ)
      have hγβ : γ ≤ β := by
        apply le_of_not_gt
        intro hlt
        exact packet_chronology hlt hxpacket hγpacket he.2
      have heq : γ = β := le_antisymm hγβ hβγ
      simpa only [heq] using hγpacket
    rw [← hsup]
    cases hK : packets β with
    | empty =>
      have hxempty : x ∈ Packet.empty.members := by simpa only [hK] using hxpacket
      exact False.elim (Packet.not_mem_empty x hxempty)
    | single p hp hp1 =>
      have hpF : p ∈ F := by
        have hxp : x = p := (Packet.mem_single_iff p hp hp1 x).mp (by simpa only [hK] using hxpacket)
        simpa only [hxp] using hxF
      have hlub : IsLUB F p := by
        constructor
        · intro e he
          have hep : e = p := (Packet.mem_single_iff p hp hp1 e).mp (by simpa only [hK] using hFpacket he)
          exact hep.le
        · intro q hq
          exact hq hpF
      rw [(isLUB_sSup F).unique hlub]
      apply packet_subset_retained β
      rw [hK]
      exact ⟨0, rfl⟩
    | row p b hp hp1 hpb R =>
      have hFR : F ⊆ Set.range R.point := by
        intro e he
        exact (Packet.mem_row_iff p b hp hp1 hpb R e).mp (by simpa only [hK] using hFpacket he)
      rcases row_subset_supremum R F hF.1 hFR with hrow | hend
      · apply packet_subset_retained β
        rw [hK]
        exact (Packet.mem_row_iff p b hp hp1 hpb R _).mpr hrow
      · rw [hend]
        have hold := packet_endpoints_retained β
        rw [hK] at hold
        exact hold

theorem retained_isSubDcpo : IsSubDcpo retained := by
  intro E hES hE p hp
  have heq : sSup E = p := (isLUB_sSup E).unique hp
  rw [← heq]
  exact retained_sSup_mem E hES hE

theorem retained_isDcpo : IsDcpo retained := isSubDcpo_isDcpo retained_isSubDcpo

end CoreCompactNonSober.Construction
