import CoreCompactSimplified.CoreCompactLattice
import Mathlib.Topology.Order.LawsonTopology
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Metrizable.Urysohn

/-!
Lawson background for He--Zhang, arXiv:2610.17759v1, Section 4.

The compactness argument below supplies a proof of the cited background
Lemma 4.4, whose internal proof is not specified in that paper. An ultrafilter
converges to the supremum of the infima of its members. The Hausdorff and
closed-order arguments use the exact separating rectangle of Lemma 4.8.

All directed sets are nonempty, and the element-level way-below relation is
the existing source-facing `ElementWayBelow`, not a sequential substitute.
-/

set_option autoImplicit false

universe u

namespace CoreCompactSimplified.HeZhangLawson

open Set TopologicalSpace CoreCompactNonSober Filter
open scoped Topology

section WayBelow

variable {P : Type u} [PartialOrder P]

theorem elementWayBelow_le {a b : P} (h : ElementWayBelow a b) : a ≤ b := by
  obtain ⟨e, he, hae⟩ := h {b} ⟨singleton_nonempty _, directedOn_singleton _⟩
    b isLUB_singleton le_rfl
  simpa only [mem_singleton_iff.mp he] using hae

theorem elementWayBelow_mono {a b c d : P} (hab : a ≤ b)
    (hbc : ElementWayBelow b c) (hcd : c ≤ d) : ElementWayBelow a d := by
  intro E hE p hp hdp
  obtain ⟨e, he, hbe⟩ := hbc E hE p hp (hcd.trans hdp)
  exact ⟨e, he, hab.trans hbe⟩

/-- The usual interpolation property, proved for arbitrary continuous dcpos.
The auxiliary directed set consists of two-stage approximants. -/
theorem elementWayBelow_interpolate (hP : IsContinuousDcpo P) {a c : P}
    (hac : ElementWayBelow a c) :
    ∃ b : P, ElementWayBelow a b ∧ ElementWayBelow b c := by
  let E : Set P := {e | ∃ b, ElementWayBelow e b ∧ ElementWayBelow b c}
  have hne : E.Nonempty := by
    obtain ⟨b, hbc⟩ := (hP.2 c).1.1
    obtain ⟨e, heb⟩ := (hP.2 b).1.1
    exact ⟨e, b, heb, hbc⟩
  have hdir : DirectedOn (· ≤ ·) E := by
    rintro x ⟨b, hxb, hbc⟩ y ⟨d, hyd, hdc⟩
    obtain ⟨k, hkc, hbk, hdk⟩ := (hP.2 c).1.2 b hbc d hdc
    obtain ⟨x', hx'k, hxx'⟩ :=
      (elementWayBelow_mono le_rfl hxb hbk) _ (hP.2 k).1 k (hP.2 k).2 le_rfl
    obtain ⟨y', hy'k, hyy'⟩ :=
      (elementWayBelow_mono le_rfl hyd hdk) _ (hP.2 k).1 k (hP.2 k).2 le_rfl
    obtain ⟨z, hzk, hx'z, hy'z⟩ := (hP.2 k).1.2 x' hx'k y' hy'k
    exact ⟨z, ⟨k, hzk, hkc⟩, hxx'.trans hx'z, hyy'.trans hy'z⟩
  have hsup : IsLUB E c := by
    constructor
    · rintro e ⟨b, heb, hbc⟩
      exact (elementWayBelow_le heb).trans (elementWayBelow_le hbc)
    · intro y hy
      apply (hP.2 c).2.2
      intro b hbc
      apply (hP.2 b).2.2
      intro e heb
      exact hy ⟨b, heb, hbc⟩
  obtain ⟨e, ⟨b, heb, hbc⟩, hae⟩ := hac E ⟨hne, hdir⟩ c hsup le_rfl
  exact ⟨b, elementWayBelow_mono hae heb le_rfl, hbc⟩

/-- The double upper set from the printed proof of Lemma 4.8 is Scott open. -/
theorem isOpen_wayAbove (hP : IsContinuousDcpo P) (a : P) :
    @IsOpen P (Topology.scott P univ) {b | ElementWayBelow a b} := by
  apply (isOpen_scott_iff _).mpr
  constructor
  · intro b c hbc hab
    exact elementWayBelow_mono le_rfl hab hbc
  · intro E hE p hp hap
    obtain ⟨b, hab, hbp⟩ := elementWayBelow_interpolate hP hap
    obtain ⟨e, he, hbe⟩ := hbp E hE p hp le_rfl
    exact ⟨e, he, elementWayBelow_mono le_rfl hab hbe⟩

theorem isOpen_wayAbove_lawson (hP : IsContinuousDcpo P) (a : P) :
    @IsOpen P (Topology.lawson P) {b | ElementWayBelow a b} :=
  Topology.lawson_le_scott _ (isOpen_wayAbove hP a)

theorem isOpen_compl_Ici_lawson (a : P) :
    @IsOpen P (Topology.lawson P) (Ici a)ᶜ :=
  Topology.lawson_le_lower _ (isOpen_generateFrom_of_mem ⟨a, rfl⟩)

/-- The separating rectangle used verbatim in He--Zhang Lemma 4.8. -/
theorem lawson_orderClosed (hP : IsContinuousDcpo P) :
    @OrderClosedTopology P (Topology.lawson P) _ := by
  letI : TopologicalSpace P := Topology.lawson P
  constructor
  apply isOpen_compl_iff.mp
  apply isOpen_iff_mem_nhds.mpr
  rintro ⟨a, b⟩ hab
  change ¬a ≤ b at hab
  have hex : ∃ z, ElementWayBelow z a ∧ ¬z ≤ b := by
    by_contra! h
    exact hab ((hP.2 a).2.2 h)
  obtain ⟨z, hza, hzb⟩ := hex
  let U : Set P := {x | ElementWayBelow z x}
  let V : Set P := (Ici z)ᶜ
  have hUV : U ×ˢ V ∈ 𝓝 (a, b) :=
    ((isOpen_wayAbove_lawson hP z).prod (isOpen_compl_Ici_lawson z)).mem_nhds
      ⟨hza, hzb⟩
  apply Filter.mem_of_superset hUV
  rintro ⟨x, y⟩ ⟨hx, hy⟩ hxy
  exact hy ((elementWayBelow_le hx).trans hxy)

theorem lawson_t2Space (hP : IsContinuousDcpo P) :
    @T2Space P (Topology.lawson P) := by
  letI : TopologicalSpace P := Topology.lawson P
  letI : OrderClosedTopology P := lawson_orderClosed hP
  infer_instance

/-- Both orientations of the order relation are closed, as in Lemma 4.8. -/
theorem lawson_orderRelations_closed (hP : IsContinuousDcpo P) :
    @IsClosed (P × P)
      (@instTopologicalSpaceProd P P (Topology.lawson P) (Topology.lawson P))
      {p | p.1 ≤ p.2} ∧
    @IsClosed (P × P)
      (@instTopologicalSpaceProd P P (Topology.lawson P) (Topology.lawson P))
      {p | p.2 ≤ p.1} := by
  letI : TopologicalSpace P := Topology.lawson P
  letI : OrderClosedTopology P := lawson_orderClosed hP
  exact ⟨isClosed_le_prod, isClosed_le_prod'⟩

end WayBelow

section Compactness

variable {L : Type u} [CompleteLattice L]

/-- Every ultrafilter on a complete lattice converges in the Lawson topology.
This proves compactness without a hidden continuity hypothesis. -/
theorem ultrafilter_le_lawson_nhds (F : Ultrafilter L) :
    ∃ x : L, (F : Filter L) ≤ @nhds L (Topology.lawson L) x := by
  let E : Set L := {e | ∃ A : Set L, A ∈ F ∧ sInf A = e}
  have hne : E.Nonempty := ⟨sInf univ, univ, univ_mem, rfl⟩
  have hdir : DirectedOn (· ≤ ·) E := by
    rintro a ⟨A, hAF, rfl⟩ b ⟨B, hBF, rfl⟩
    refine ⟨sInf (A ∩ B), ⟨A ∩ B, inter_mem hAF hBF, rfl⟩, ?_, ?_⟩
    · exact sInf_le_sInf inter_subset_left
    · exact sInf_le_sInf inter_subset_right
  let x : L := sSup E
  refine ⟨x, ?_⟩
  change (F : Filter L) ≤ @nhds L (Topology.lower L ⊓ Topology.scott L univ) x
  rw [nhds_inf]
  apply le_inf
  · have h : Tendsto (id : L → L) F (@nhds L (Topology.lower L) x) := by
      apply tendsto_nhds_generateFrom_iff.mpr
      rintro _ ⟨a, rfl⟩ hax
      change (Ici a)ᶜ ∈ F
      apply Ultrafilter.compl_mem_iff_notMem.mpr
      intro haF
      apply hax
      change a ≤ sSup E
      have hinf : a ≤ sInf (Ici a) := le_sInf fun b hb ↦ hb
      exact hinf.trans (le_sSup ⟨Ici a, haF, rfl⟩)
    simpa only [Filter.Tendsto, Filter.map_id] using h
  · letI : TopologicalSpace L := Topology.scott L univ
    apply le_nhds_iff.mpr
    intro U hxU hU
    obtain ⟨e, ⟨A, hAF, rfl⟩, heU⟩ :=
      ((isOpen_scott_iff U).mp hU).2 E ⟨hne, hdir⟩ x (isLUB_sSup E) hxU
    apply Filter.mem_of_superset hAF
    intro a ha
    exact ((isOpen_scott_iff U).mp hU).1 (sInf_le ha) heU

theorem lawson_compactSpace : @CompactSpace L (Topology.lawson L) := by
  letI : TopologicalSpace L := Topology.lawson L
  constructor
  apply isCompact_iff_ultrafilter_le_nhds.mpr
  intro F _
  obtain ⟨x, hx⟩ := ultrafilter_le_lawson_nhds F
  exact ⟨x, mem_univ _, hx⟩

/-- Source-exact background Lemma 4.4: a continuous lattice has compact
Hausdorff Lawson topology. -/
theorem continuousLattice_lawson_compact_hausdorff (hL : IsContinuousDcpo L) :
    @CompactSpace L (Topology.lawson L) ∧ @T2Space L (Topology.lawson L) :=
  ⟨lawson_compactSpace, lawson_t2Space hL⟩

end Compactness

end CoreCompactSimplified.HeZhangLawson
