import ZFCFubini.SourceModel
import ZFCFubini.SameTraceComparison
import ZFCFubini.DensityProbability
import ZFCFubini.StabilizedValuation

/-! The literal two uses of source `lem:same-trace` in
`prop:index-comparison`. In particular the second intersection Z is not
replaced by the invalid mixed-kernel containment H_(V_F) ≤ G_M. -/

set_option autoImplicit false
open Set TopologicalSpace MeasureTheory Topology
open scoped ENNReal
namespace ZFCFubini
open FilterDcpo

noncomputable def finiteNullPatch (M : NullSet) (F : Finset Circle) :
    @Opens Circle densityTopology := by
  letI : TopologicalSpace Circle := densityTopology
  refine ⟨M.valᶜ ∪ (F : Set Circle), ?_⟩
  have hn : volume (M.val \ (F : Set Circle)) = 0 :=
    measure_mono_null Set.diff_subset M.property.2
  convert densityOpen_null_compl hn using 1
  ext y
  simp only [mem_compl_iff, mem_diff, mem_union, Finset.mem_coe]
  tauto

abbrev PatchIndex (M M0 : NullSet) := Finset ↥(M.val \ M0.val)

noncomputable def patchFinite (M M0 : NullSet) (F : PatchIndex M M0) : Finset Circle :=
  by classical exact F.image Subtype.val

theorem patchFinite_subset (M M0 : NullSet) (F : PatchIndex M M0) :
    (patchFinite M M0 F : Set Circle) ⊆ M.val \ M0.val := by
  classical
  intro y hy
  obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hy
  exact z.property

theorem patchFinite_mono (M M0 : NullSet) : Monotone (patchFinite M M0) := by
  classical
  intro F G hFG
  exact Finset.image_mono Subtype.val hFG

noncomputable def patchH (M M0 : NullSet) (F : PatchIndex M M0) : SourceQ :=
  H circleModel (finiteNullPatch M (patchFinite M M0 F))

theorem densityH_mono : Monotone (H circleModel) := by
  intro U V hUV p hp
  exact (WithScott.ofScott p).filter.upward hp (@Opens.isOpen Circle circleModel.tau V) hUV

theorem patchH_mono (M M0 : NullSet) : Monotone (patchH M M0) := by
  intro F G hFG
  apply densityH_mono
  exact Set.union_subset_union_right _ (patchFinite_mono M M0 hFG)

theorem patchH_directed (M M0 : NullSet) : Directed (· ≤ ·) (patchH M M0) := by
  classical
  intro F G
  exact ⟨F ∪ G, patchH_mono M M0 Finset.subset_union_left,
    patchH_mono M M0 Finset.subset_union_right⟩

theorem patch_subset_conull (M M0 : NullSet) (hM : M0 ≤ M) (F : PatchIndex M M0) :
    finiteNullPatch M (patchFinite M M0 F) ≤ conullOpen M0 := by
  intro y hy
  rcases hy with hyM | hyF
  · exact fun hyM0 => hyM (hM hyM0)
  · exact (patchFinite_subset M M0 F hyF).2

theorem patchH_le_L (M M0 : NullSet) (hM : M0 ≤ M) (F : PatchIndex M M0) :
    patchH M M0 F ≤ L circleModel (conullOpen M0) := by
  apply le_L_iff.mpr
  rw [patchH, trace_H]
  exact patch_subset_conull M M0 hM F

theorem patch_union_trace (M M0 : NullSet) (hM : M0 ≤ M) :
    trace (⨆ F : PatchIndex M M0, patchH M M0 F) = M0.valᶜ := by
  classical
  ext y
  change (WithScott.toScott (e circleModel y) ∈ ⨆ F, patchH M M0 F) ↔ y ∉ M0.val
  rw [Opens.mem_iSup]
  constructor
  · rintro ⟨F, hyF⟩
    have hy : y ∈ finiteNullPatch M (patchFinite M M0 F) := by
      simpa only [← mem_trace, patchH, trace_H] using hyF
    exact patch_subset_conull M M0 hM F hy
  · intro hyM0
    by_cases hyM : y ∈ M.val
    · let z : ↥(M.val \ M0.val) := ⟨y, hyM, hyM0⟩
      refine ⟨{z}, ?_⟩
      change y ∈ trace (patchH M M0 {z})
      rw [patchH, trace_H]
      exact Or.inr (Finset.mem_image.mpr ⟨z, by simp, rfl⟩)
    · refine ⟨∅, ?_⟩
      change y ∈ trace (patchH M M0 ∅)
      rw [patchH, trace_H]
      exact Or.inl hyM

theorem source_index_comparison {D : Set Omega} {Nbad : Set Circle}
    (M0 M : NullSet) (hbad : Nbad ⊆ M0.val) (hM : M0 ≤ M)
    (hit : ∀ F : Finset Circle, (∀ y ∈ F, y ∉ Nbad) →
      ∀ W : Set D, IsOpen W → W.Nonempty → ∃ t ∈ W, (F : Set Circle) ⊆ randomOpen t.val)
    (A : ScottOpens SourceQ)
    (hstart : ∃ t : D, WithScott.toScott (sourceG M0 t.val) ∈ A) :
    ∃ s : D, WithScott.toScott (sourceG M s.val) ∈ A := by
  classical
  let J : SourceQ := ⨆ F : PatchIndex M M0, patchH M M0 F
  have hJL : J ≤ L circleModel (conullOpen M0) :=
    iSup_le (patchH_le_L M M0 hM)
  have htrJ : trace J = trace (L circleModel (conullOpen M0)) := by
    rw [trace_L]
    exact patch_union_trace M M0 hM
  have hLavoid : trace (L circleModel (conullOpen M0)) ⊆ M0.valᶜ := by
    rw [trace_L]; exact Set.Subset.rfl
  obtain ⟨s, _, hsA⟩ := same_trace_comparison circleModel randomOpen randomOpen_continuous
    D Nbad M0.val hbad hit J (L circleModel (conullOpen M0)) ⊥ hJL htrJ hLavoid A
    Set.univ isOpen_univ (by
      obtain ⟨t, ht⟩ := hstart
      exact ⟨t, Set.mem_univ _, by simpa only [sup_bot_eq, sourceG] using ht⟩)
  have hJLUB : IsLUB (Set.range (patchH M M0)) J := by
    simpa only [J, sSup_range] using isLUB_sSup (Set.range (patchH M M0))
  obtain ⟨Hf, hHf, hF_A⟩ := scottOpen_capture_map
    (fun C : SourceQ => H_ordinary circleModel (randomOpen s.val) ⊔ C)
    (sup_left_scottContinuous _) (Set.range_nonempty (patchH M M0))
    (patchH_directed M M0).directedOn_range hJLUB A
    (by simpa only [sup_bot_eq] using hsA)
  obtain ⟨F, rfl⟩ := hHf
  let F0 : Finset Circle := patchFinite M M0 F
  let W1 : Set D := {t | WithScott.toScott
    (H_ordinary circleModel (randomOpen t.val) ⊔ patchH M M0 F) ∈ A}
  have hW1 : IsOpen W1 := by
    simpa only [sup_bot_eq] using
      (noise_event_isOpen circleModel randomOpen randomOpen_continuous ⊥ (patchH M M0 F) A).preimage
        continuous_subtype_val
  have hFavoid : ∀ y ∈ F0, y ∉ Nbad := by
    intro y hy hyN
    exact (patchFinite_subset M M0 F hy).2 (hbad hyN)
  obtain ⟨t1, ht1W, hFhit⟩ := hit F0 hFavoid W1 hW1 ⟨s, hF_A⟩
  have hBexists : ∃ B0 : Opens Circle, (F0 : Set Circle) ⊆ B0 ∧
      closure (B0 : Set Circle) ⊆ randomOpen t1.val ∧ (F0 = ∅ → B0 = ⊥) := by
    by_cases hF0 : F0 = ∅
    · refine ⟨⊥, ?_, ?_, fun _ => rfl⟩
      · simp only [hF0, Finset.coe_empty, Set.empty_subset]
      · simp only [Opens.coe_bot, closure_empty, Set.empty_subset]
    · obtain ⟨B, hBo, hFB, hBU⟩ := F0.finite_toSet.isCompact.exists_isOpen_closure_subset
        ((randomOpen t1.val).isOpen.mem_nhdsSet.mpr hFhit)
      exact ⟨⟨B, hBo⟩, hFB, hBU, fun h => (hF0 h).elim⟩
  obtain ⟨B0, hFB, hBcl, _⟩ := hBexists
  let C : SourceQ := L circleModel (conullOpen M) ⊔ H_ordinary circleModel B0
  let H0 : SourceQ := patchH M M0 F
  let Z : SourceQ := H0 ⊓ C
  have hHC : trace H0 ⊆ trace C := by
    dsimp only [H0, C]
    rw [patchH, trace_H, trace_sup, trace_L, trace_H_ordinary]
    exact Set.union_subset_union_right _ hFB
  have htrZ : trace Z = trace H0 := by
    change trace H0 ∩ trace C = trace H0
    exact Set.inter_eq_left.mpr hHC
  have hHavoid : trace H0 ⊆ M0.valᶜ := by
    dsimp only [H0]
    rw [patchH, trace_H]
    exact patch_subset_conull M M0 hM F
  let W2 : Set D := {t | closure (B0 : Set Circle) ⊆ randomOpen t.val}
  have hW2 : IsOpen W2 :=
    (randomOpen_compact_containment_isOpen isClosed_closure.isCompact).preimage
      continuous_subtype_val
  have hstart2 : ∃ t ∈ W2,
      WithScott.toScott (H_ordinary circleModel (randomOpen t.val) ⊔ C ⊔ H0) ∈ A := by
    refine ⟨t1, hBcl, ?_⟩
    have hup := ((scott_isOpen_iff {K : SourceQ | WithScott.toScott K ∈ A}).mp A.isOpen).1
    exact hup (sup_le_sup (le_sup_left : H_ordinary circleModel (randomOpen t1.val) ≤
      H_ordinary circleModel (randomOpen t1.val) ⊔ C) le_rfl) ht1W
  obtain ⟨t2, ht2W, ht2A⟩ := same_trace_comparison circleModel randomOpen randomOpen_continuous
    D Nbad M0.val hbad hit Z H0 C inf_le_left htrZ hHavoid A W2 hW2 hstart2
  have hBsub : B0 ≤ randomOpen t2.val := subset_closure.trans ht2W
  have hCle : C ≤ sourceG M t2.val := by
    exact sup_le le_sup_right ((H_ordinary_mono circleModel hBsub).trans le_sup_left)
  have hfinal : H_ordinary circleModel (randomOpen t2.val) ⊔ C ⊔ Z ≤ sourceG M t2.val :=
    sup_le (sup_le le_sup_left hCle) (inf_le_right.trans hCle)
  have hup := ((scott_isOpen_iff {K : SourceQ | WithScott.toScott K ∈ A}).mp A.isOpen).1
  exact ⟨t2, hup hfinal ht2A⟩

noncomputable def sourceFamily (M : NullSet) (t : Omega) : WithScott SourceQ :=
  WithScott.toScott (sourceG M t)

theorem sourceFamily_antitone (t : Omega) : Antitone (fun M => sourceFamily M t) :=
  sourceG_antitone t

theorem sourceFamily_continuous (M : NullSet) : Continuous (sourceFamily M) :=
  sourceG_continuous M

/-- All comparison premises are discharged by the actual product probability
law and actual filter model. The index is chosen before A and M. -/
theorem sourceCarrierIndexComparison : CarrierIndexComparison sourceFamily parameterMeasure := by
  intro D hD
  obtain ⟨M0, _, hfinite⟩ := hitting_source hD
  have hit : ∀ F : Finset Circle, (∀ y ∈ F, y ∉ M0.val) →
      ∀ W : Set D, IsOpen W → W.Nonempty → ∃ t ∈ W, (F : Set Circle) ⊆ randomOpen t.val := by
    intro F hFN W hWo hWn
    exact hfinite (F : Set Circle) F.finite_toSet
      (Set.disjoint_left.mpr (fun y hy hyN => hFN y hy hyN)) W hWo hWn
  refine ⟨M0, ?_⟩
  intro M hM A hstart
  obtain ⟨t, htD, htA⟩ := hstart
  obtain ⟨s, hs⟩ := source_index_comparison M0 M Set.Subset.rfl hM hit A ⟨⟨t, htD⟩, htA⟩
  exact ⟨s.val, s.property, hs⟩

end ZFCFubini
