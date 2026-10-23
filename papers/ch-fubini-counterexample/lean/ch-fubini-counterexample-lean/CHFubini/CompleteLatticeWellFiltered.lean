import CHFubini.WellFiltered

/-!
The Scott space of every complete lattice is well-filtered.

This proves the manuscript's application to L = Opens X without a Lawson
compactness premise and without incorrectly claiming Scott sobriety.
The proof uses the complete-lattice special case of the closed lower-hull
criterion in Xu--Zhao, arXiv:1911.11617, Lemma 3.15 and Corollary 3.10.
All criterion steps and the Rudin/Zorn construction are proved below.
-/

set_option autoImplicit false

open Set Topology TopologicalSpace

universe u v

namespace CHFubini

def joinCut {P : Type u} [CompleteLattice P]
    (F : Set (WithScott P)) (a : WithScott P) : Set (WithScott P) :=
  {x | a ⊔ x ∈ F}

def downwardHit {P : Type u} [CompleteLattice P]
    (F K : Set (WithScott P)) : Set (WithScott P) :=
  {x | ∃ y ∈ K, y ∈ F ∧ x ≤ y}

theorem joinCut_isClosed {P : Type u} [CompleteLattice P]
    {F : Set (WithScott P)} (hF : IsClosed F) (a : WithScott P) :
    IsClosed (joinCut F a) := by
  have hscott : ScottContinuous (fun x : P => WithScott.ofScott a ⊔ x) :=
    ((ScottContinuous.const (WithScott.ofScott a)).prodMk ScottContinuous.id).comp
      ScottContinuous.sup₂
  exact hF.preimage ((CHFubini.scott_continuous_iff _).mp hscott)

theorem joinCut_antitone {P : Type u} [CompleteLattice P]
    {F : Set (WithScott P)} (hF : IsClosed F) : Antitone (joinCut F) := by
  intro a b hab x hx
  exact (Topology.IsScott.isLowerSet_of_isClosed hF)
    (sup_le_sup_right hab x) hx

theorem saturated_scott_isUpperSet {P : Type u} [CompleteLattice P]
    {K : Set (WithScott P)} (hK : CHFubini.IsSaturated K) : IsUpperSet K := by
  intro a b hab ha
  apply CHFubini.saturated_mem_of_mem_closure_singleton K hK ha
  rw [Topology.IsScott.closure_singleton]
  exact hab

theorem downwardHit_isLowerSet {P : Type u} [CompleteLattice P]
    (F K : Set (WithScott P)) : IsLowerSet (downwardHit F K) := by
  intro a b hab
  rintro ⟨y, hyK, hyF, hby⟩
  exact ⟨y, hyK, hyF, hab.trans hby⟩

theorem downwardHit_subset {P : Type u} [CompleteLattice P]
    {F : Set (WithScott P)} (hF : IsClosed F) (K : Set (WithScott P)) :
    downwardHit F K ⊆ F := by
  rintro x ⟨y, _, hyF, hxy⟩
  exact (Topology.IsScott.isLowerSet_of_isClosed hF) hxy hyF

/-- Compactness of K and continuity of finite joins prove that the lower hull
of K ∩ F is Scott closed. This is the needed bridge, not a proof boundary. -/
theorem downwardHit_isClosed {P : Type u} [CompleteLattice P]
    {F K : Set (WithScott P)} (hF : IsClosed F) (hK : IsCompact K)
    (hKsat : CHFubini.IsSaturated K) : IsClosed (downwardHit F K) := by
  classical
  rw [Topology.IsScott.isClosed_iff_isLowerSet_and_dirSupClosed]
  refine ⟨downwardHit_isLowerSet F K, ?_⟩
  intro D hD hn hd s hs
  letI : Nonempty D := hn.to_subtype
  have hmeet : ∀ a : D, (K ∩ joinCut F a.val).Nonempty := by
    intro a
    obtain ⟨y, hyK, hyF, hay⟩ := hD a.property
    refine ⟨y, hyK, ?_⟩
    change a.val ⊔ y ∈ F
    simpa only [sup_eq_right.mpr hay] using hyF
  have hdir : Directed (· ⊇ ·) (fun a : D => joinCut F a.val) := by
    intro a b
    obtain ⟨c, hcD, hac, hbc⟩ := hd a.val a.property b.val b.property
    exact ⟨⟨c, hcD⟩, joinCut_antitone hF hac, joinCut_antitone hF hbc⟩
  have hnonempty : (K ∩ ⋂ a : D, joinCut F a.val).Nonempty := by
    by_contra hno
    obtain ⟨a, hempty⟩ := hK.elim_directed_family_closed
      (fun a : D => joinCut F a.val) (fun a => joinCut_isClosed hF a.val)
      (Set.not_nonempty_iff_eq_empty.mp hno) hdir
    exact (hmeet a).ne_empty hempty
  obtain ⟨z, hzK, hzcut⟩ := hnonempty
  have hjoin : ScottContinuous (fun x : WithScott P => x ⊔ z) :=
    (ScottContinuous.id.prodMk (ScottContinuous.const z)).comp ScottContinuous.sup₂
  have hjoinsF : (fun x : WithScott P => x ⊔ z) '' D ⊆ F := by
    rintro x ⟨a, haD, rfl⟩
    exact mem_iInter.mp hzcut ⟨a, haD⟩
  have hszF : s ⊔ z ∈ F := (Topology.IsScott.dirSupClosed_of_isClosed hF)
    hjoinsF (hn.image _) (directedOn_image.mpr (hd.mono hjoin.monotone)) (hjoin hn hd hs)
  exact ⟨s ⊔ z, saturated_scott_isUpperSet hKsat le_sup_right hzK, hszF, le_sup_left⟩

/-- Every nonempty Scott-closed subset of a complete lattice has a maximal
element. Zorn is applied to chains with their actual lattice suprema. -/
theorem scott_closed_has_maximal {P : Type u} [CompleteLattice P]
    {F : Set (WithScott P)} (hF : IsClosed F) (hn : F.Nonempty) :
    ∃ x ∈ F, ∀ y ∈ F, x ≤ y → y ≤ x := by
  classical
  obtain ⟨x₀, hx₀⟩ := hn
  obtain ⟨x, _, hxmax⟩ := zorn_le_nonempty₀ F (by
    intro C hCF hc y hyC
    refine ⟨sSup C, ?_, fun z hz => le_sSup hz⟩
    exact (Topology.IsScott.dirSupClosed_of_isClosed hF)
      hCF ⟨y, hyC⟩ hc.directedOn (isLUB_sSup C)) x₀ hx₀
  exact ⟨x, hxmax.1, fun y hyF hxy => hxmax.2 hyF hxy⟩

/-- The complete-lattice case of the manuscript's Xu--Yang Lemma 3.17
application. It establishes well-filteredness, never Scott sobriety. -/
theorem completeLattice_scott_isWellFiltered (P : Type u) [CompleteLattice P] :
    CHFubini.IsWellFiltered (WithScott P) := by
  classical
  refine ⟨inferInstance, ?_⟩
  intro K hKn hK hKd U hU hinter
  by_contra hno
  have hnot : ∀ C ∈ K, ¬ C ⊆ U := by
    intro C hCK hCU
    exact hno ⟨C, hCK, hCU⟩
  have hmeet₀ : CHFubini.MeetsFamily Uᶜ K := by
    intro C hCK
    exact inter_compl_nonempty_iff.mpr (hnot C hCK)
  obtain ⟨F, hFclosed, hFU, hFmeet, hFmin⟩ :=
    CHFubini.exists_minimal_closed_meeting_compacts K
      (fun C hCK => (hK C hCK).2.1) Uᶜ hU.isClosed_compl hmeet₀
  have hFn : F.Nonempty := by
    obtain ⟨C, hCK⟩ := hKn
    exact (hFmeet C hCK).mono inter_subset_right
  obtain ⟨x, hxF, hxmax⟩ := scott_closed_has_maximal hFclosed hFn
  have hxinter : x ∈ ⋂₀ K := by
    apply mem_sInter.mpr
    intro C hCK
    have hdownclosed : IsClosed (downwardHit F C) :=
      downwardHit_isClosed hFclosed (hK C hCK).2.1 (hK C hCK).2.2
    have hdownmeet : CHFubini.MeetsFamily (downwardHit F C) K := by
      intro D hDK
      obtain ⟨E, hEK, hEC, hED⟩ := hKd C hCK D hDK
      obtain ⟨y, hyE, hyF⟩ := hFmeet E hEK
      exact ⟨y, hED hyE, y, hEC hyE, hyF, le_rfl⟩
    have hxdown : x ∈ downwardHit F C :=
      hFmin (downwardHit F C) hdownclosed (downwardHit_subset hFclosed C) hdownmeet hxF
    obtain ⟨y, hyC, hyF, hxy⟩ := hxdown
    have hyx := hxmax y hyF hxy
    exact (le_antisymm hxy hyx).symm ▸ hyC
  exact hFU hxF (hinter hxinter)

/-- Direct wrapper for the paper's actual second-factor carrier L = Opens X. -/
theorem opens_scott_isWellFiltered (X : Type v) [TopologicalSpace X] :
    CHFubini.IsWellFiltered (WithScott (Opens X)) :=
  completeLattice_scott_isWellFiltered (Opens X)

end CHFubini
