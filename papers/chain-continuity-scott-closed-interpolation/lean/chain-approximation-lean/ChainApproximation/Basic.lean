import ChainApproximation.Definitions

/-! # Elementary source bridges and auxiliary-relation laws -/

set_option autoImplicit false

universe u

namespace ChainApproximation

open Set

variable {P : Type u} [PartialOrder P]

theorem NonemptyChain.directed {C : Set P} (hC : NonemptyChain C) : NonemptyDirected C :=
  ⟨hC.1, hC.2.directedOn⟩

theorem singleton_chain (p : P) : NonemptyChain ({p} : Set P) :=
  ⟨Set.singleton_nonempty p, IsChain.singleton⟩

theorem cut_eq_Iic {A : Set P} {s : P} (hs : IsLUB A s) : cut A = Set.Iic s := by
  ext x
  constructor
  · intro hx
    exact hx hs.1
  · intro hx b hb
    exact hx.trans (hs.2 hb)

theorem lowerHull_subset_cut (A : Set P) : lowerHull A ⊆ cut A := by
  rintro x ⟨a, ha, hxa⟩ b hb
  exact hxa.trans (hb ha)

theorem lowerHull_isLower (A : Set P) : IsLowerSet (lowerHull A) := by
  rintro x y hxy ⟨a, ha, hya⟩
  exact ⟨a, ha, hxy.trans hya⟩

theorem dcpo_chainComplete (hP : IsDcpo P) : IsChainComplete P :=
  fun C hC ↦ hP C hC.directed

theorem chainBelow_iff_sup (hP : IsDcpo P) (x y : P) :
    ChainBelow x y ↔ ChainBelowSup x y := by
  constructor
  · intro h C hC s hs hys
    apply h C hC
    rw [cut_eq_Iic hs]
    exact hys
  · intro h C hC hy
    obtain ⟨s, hs⟩ := hP C hC.directed
    apply h C hC s hs
    rwa [cut_eq_Iic hs] at hy

theorem directedBelow_iff_wayBelow (hP : IsDcpo P) (x y : P) :
    DirectedBelow x y ↔ WayBelow x y := by
  constructor
  · intro h D hD s hs hys
    apply h D hD
    rw [cut_eq_Iic hs]
    exact hys
  · intro h D hD hy
    obtain ⟨s, hs⟩ := hP D hD
    apply h D hD s hs
    rwa [cut_eq_Iic hs] at hy

theorem ChainBelow.le {x y : P} (h : ChainBelow x y) : x ≤ y := by
  obtain ⟨z, hz, hxz⟩ := h {y} (singleton_chain y) (by
    rw [cut_eq_Iic (isLUB_singleton : IsLUB ({y} : Set P) y)]
    exact le_rfl)
  simpa only [Set.mem_singleton_iff.mp hz] using hxz

theorem ChainBelow.mono {a' a b b' : P}
    (haa : a' ≤ a) (hab : ChainBelow a b) (hbb : b ≤ b') : ChainBelow a' b' := by
  intro C hC hb'C
  have hbC : b ∈ cut C := fun t ht ↦ hbb.trans (hb'C ht)
  obtain ⟨c, hc, hac⟩ := hab C hC hbC
  exact ⟨c, hc, haa.trans hac⟩

theorem ChainBelow.trans {a b c : P} (hab : ChainBelow a b) (hbc : ChainBelow b c) :
    ChainBelow a c := hab.mono le_rfl hbc.le

theorem chainBelow_auxiliary : IsAuxiliary (ChainBelow (P := P)) :=
  ⟨fun _ _ h ↦ h.le, fun _ _ _ _ haa hab hbb ↦ hab.mono haa hbb⟩

theorem WayBelow.le {x y : P} (h : WayBelow x y) : x ≤ y := by
  obtain ⟨z, hz, hxz⟩ := h {y} (singleton_chain y).directed y isLUB_singleton le_rfl
  simpa only [Set.mem_singleton_iff.mp hz] using hxz

theorem WayBelow.mono {a' a b b' : P}
    (haa : a' ≤ a) (hab : WayBelow a b) (hbb : b ≤ b') : WayBelow a' b' := by
  intro D hD s hs hb's
  obtain ⟨d, hd, had⟩ := hab D hD s hs (hbb.trans hb's)
  exact ⟨d, hd, haa.trans had⟩

theorem WayBelow.chainBelow (hP : IsDcpo P) {x y : P} (h : WayBelow x y) : ChainBelow x y :=
  (chainBelow_iff_sup hP x y).mpr (fun C hC s hs hys ↦ h C hC.directed s hs hys)

theorem chainSection_isLower (y : P) : IsLowerSet (chainSection y) :=
  fun _ _ hxy hy ↦ hy.mono hxy le_rfl

theorem chainSection_mono {x y : P} (hxy : x ≤ y) : chainSection x ⊆ chainSection y :=
  fun _ h ↦ h.mono le_rfl hxy

theorem IsChainGeneratedIdeal.directed {I : Set P} (hI : IsChainGeneratedIdeal I) :
    NonemptyDirected I := by
  obtain ⟨C, hC, rfl⟩ := hI
  refine ⟨?_, ?_⟩
  · obtain ⟨c, hc⟩ := hC.1
    exact ⟨c, c, hc, le_rfl⟩
  · rintro x ⟨a, ha, hxa⟩ y ⟨b, hb, hyb⟩
    obtain ⟨c, hc, hac, hbc⟩ := hC.2.directedOn a ha b hb
    exact ⟨c, ⟨c, hc, le_rfl⟩, hxa.trans hac, hyb.trans hbc⟩

theorem IsChainContinuous.section_directed (hP : IsChainContinuous P) (p : P) :
    NonemptyDirected (chainSection p) := (hP p).1.directed

theorem IsChainContinuous.section_lub (hP : IsChainContinuous P) (p : P) :
    IsLUB (chainSection p) p := (hP p).2

theorem IsChainContinuous.exists_chain (hP : IsChainContinuous P) (p : P) :
    ∃ C : Set P, NonemptyChain C ∧ C ⊆ chainSection p ∧
      (∀ x ∈ chainSection p, ∃ c ∈ C, x ≤ c) ∧ IsLUB C p := by
  obtain ⟨C, hC, heq⟩ := (hP p).1
  have hCC : C ⊆ chainSection p := fun c hc ↦ heq.symm ▸ ⟨c, hc, le_rfl⟩
  have hcof : ∀ x ∈ chainSection p, ∃ c ∈ C, x ≤ c := by
    intro x hx
    rwa [heq] at hx
  refine ⟨C, hC, hCC, hcof, ?_⟩
  constructor
  · intro c hc
    exact (hCC hc).le
  · intro q hq
    apply (hP p).2.2
    intro x hx
    obtain ⟨c, hc, hxc⟩ := hcof x hx
    exact hxc.trans (hq hc)

theorem isClosed_scott_iff (F : Set P) :
    @IsClosed P (scottTopology P) F ↔ IsScottClosed F := by
  letI : TopologicalSpace P := scottTopology P
  letI : Topology.IsScott P Set.univ := ⟨rfl⟩
  rw [Topology.IsScott.isClosed_iff_isLowerSet_and_dirSupClosed]
  constructor
  · rintro ⟨hl, hc⟩
    exact ⟨hl, fun D hDF hD s hs ↦ hc hDF hD.1 hD.2 hs⟩
  · rintro ⟨hl, hc⟩
    exact ⟨hl, fun D hDF hne hdir s hs ↦ hc D hDF ⟨hne, hdir⟩ s hs⟩

end ChainApproximation
