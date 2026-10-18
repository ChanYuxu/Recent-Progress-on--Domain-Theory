import ChainApproximation.Cofinality

/-!
# Nonempty chain completeness and directed completeness

Source `lem:chain-directed`. The proof below formalizes the cardinal-induction
argument, using coherent finite upper bounds. It assumes neither a bottom
element nor a cofinal chain in an arbitrary directed set.
-/

set_option autoImplicit false

universe u

namespace ChainApproximation

open Set Cardinal

variable {P : Type u} [PartialOrder P]

private def prefixFinsets {I : Type u} [LinearOrder I] (a : I) : Set (Finset I) :=
  {s | ∀ i ∈ s, i < a}

private theorem prefixFinsets_card {I : Type u} [LinearOrder I] (a : I) :
    Cardinal.mk (prefixFinsets a) ≤ Cardinal.mk (Finset (Set.Iio a)) := by
  classical
  let g : Finset (Set.Iio a) → prefixFinsets a := fun s ↦
    ⟨s.map (Function.Embedding.subtype _), by
      intro i hi
      obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hi
      exact j.property⟩
  apply Cardinal.mk_le_of_surjective (f := g)
  intro s
  refine ⟨s.val.subtype (· < a), Subtype.ext ?_⟩
  change (s.val.subtype (· < a)).map (Function.Embedding.subtype _) = s.val
  rw [Finset.subtype_map]
  exact Finset.filter_eq_self.mpr s.property

private theorem prefixFinsets_mono {I : Type u} [LinearOrder I] {a b : I}
    (hab : a ≤ b) : prefixFinsets a ⊆ prefixFinsets b :=
  fun _ hs i hi ↦ (hs i hi).trans_le hab

private theorem directed_image_prefix {I : Type u} [LinearOrder I]
    (f : Finset I → P) (hf : Monotone f) (a : I) :
    NonemptyDirected (f '' prefixFinsets a) := by
  classical
  refine ⟨⟨f ∅, ∅, by simp [prefixFinsets], rfl⟩, ?_⟩
  rintro _ ⟨s, hs, rfl⟩ _ ⟨t, ht, rfl⟩
  refine ⟨f (s ∪ t), ⟨s ∪ t, ?_, rfl⟩, hf Finset.subset_union_left,
    hf Finset.subset_union_right⟩
  intro i hi
  rcases Finset.mem_union.mp hi with hi | hi
  · exact hs i hi
  · exact ht i hi

/-- Markowsky's strict-inductiveness theorem, with the source's nonempty
convention. All smaller directed subsets are handled by cardinal induction. -/
theorem chainComplete_dcpo (hP : IsChainComplete P) : IsDcpo P := by
  classical
  have aux : ∀ κ : Cardinal.{u}, ∀ D : Set P,
      Cardinal.mk D = κ → NonemptyDirected D → ∃ p, IsLUB D p := by
    intro κ
    induction κ using Cardinal.lt_wf.induction with
    | h κ ih =>
      intro D hcard hD
      by_cases hcount : Cardinal.mk D ≤ Cardinal.aleph0
      · haveI : Countable D := Cardinal.mk_le_aleph0_iff.mp hcount
        obtain ⟨a, ha, hmem, hcof⟩ := countable_directed_cofinal_chain hD
          (show D.Countable from Set.to_countable D)
        obtain ⟨p, hp⟩ := hP (Set.range a) ⟨Set.range_nonempty _, ha.isChain_range⟩
        exact ⟨p, isLUB_of_cofinal_range hmem hcof hp⟩
      · have hinf : Cardinal.aleph0 < κ := by
          rw [← hcard]
          exact lt_of_not_ge hcount
        let I := CofinalIndex κ
        haveI : NoMaxOrder I := Cardinal.noMaxOrder hinf.le
        haveI : Nonempty D := hD.1.to_subtype
        have ecard : Cardinal.mk I = Cardinal.mk D := (cofinalIndex_card κ).trans hcard.symm
        let e : I ≃ D := Classical.choice (Cardinal.eq.mp ecard)
        have hDu : NonemptyDirected (Set.univ : Set D) := by
          refine ⟨Set.univ_nonempty, ?_⟩
          intro a _ b _
          obtain ⟨c, hc, hac, hbc⟩ := hD.2 a.val a.property b.val b.property
          exact ⟨⟨c, hc⟩, trivial, hac, hbc⟩
        let f : Finset I → P := fun s ↦ (coherentUpper hDu (s.map e.toEmbedding)).val
        have hfmem : ∀ s, f s ∈ D := fun s ↦ (coherentUpper hDu _).property
        have hf : Monotone f := by
          intro s t hst
          exact coherentUpper_monotone hDu (Finset.map_subset_map.mpr hst)
        let A : I → Set P := fun a ↦ f '' prefixFinsets a
        have hAcard : ∀ a, Cardinal.mk (A a) < κ := by
          intro a
          calc
            Cardinal.mk (A a) ≤ Cardinal.mk (prefixFinsets a) := Cardinal.mk_image_le
            _ ≤ Cardinal.mk (Finset (Set.Iio a)) := prefixFinsets_card a
            _ ≤ max (Cardinal.mk (Set.Iio a)) Cardinal.aleph0 := mk_finset_le_max _
            _ < κ := max_lt (cofinalIndex_initial_small κ a) hinf
        have hA : ∀ a, NonemptyDirected (A a) := directed_image_prefix f hf
        have hlubs : ∀ a, ∃ p, IsLUB (A a) p :=
          fun a ↦ ih (Cardinal.mk (A a)) (hAcard a) (A a) rfl (hA a)
        choose p hp using hlubs
        have hpmono : Monotone p := by
          intro a b hab
          exact (hp a).mono (hp b) (Set.image_mono (prefixFinsets_mono hab))
        haveI : Nonempty I := ⟨e.symm (Classical.arbitrary D)⟩
        obtain ⟨s, hs⟩ := hP (Set.range p) ⟨Set.range_nonempty _, hpmono.isChain_range⟩
        refine ⟨s, ?_, ?_⟩
        · intro d hd
          let i : I := e.symm ⟨d, hd⟩
          obtain ⟨a, hia⟩ := exists_gt i
          have hda : d ≤ f {i} := by
            have hi : e i ∈ ({i} : Finset I).map e.toEmbedding :=
              Finset.mem_map.mpr ⟨i, Finset.mem_singleton_self _, rfl⟩
            calc
              d = (e i).val := (congrArg Subtype.val (e.apply_symm_apply ⟨d, hd⟩)).symm
              _ ≤ f {i} := le_coherentUpper hDu hi
          have hfa : f {i} ∈ A a := ⟨{i}, by simpa [prefixFinsets] using hia, rfl⟩
          exact hda.trans ((hp a).1 hfa) |>.trans (hs.1 (Set.mem_range_self a))
        · intro q hq
          apply hs.2
          rintro _ ⟨a, rfl⟩
          apply (hp a).2
          rintro _ ⟨t, _, rfl⟩
          exact hq (hfmem t)
  intro D hD
  exact aux (Cardinal.mk D) D rfl hD

theorem chainComplete_iff_dcpo : IsChainComplete P ↔ IsDcpo P :=
  ⟨chainComplete_dcpo, dcpo_chainComplete⟩

/-- Source closed-set consequence: lowerness transports an internal directed
supremum back to the ambient supremum. -/
theorem scottClosed_iff_chainClosed (hP : IsDcpo P) (F : Set P) :
    IsScottClosed F ↔ IsLowerSet F ∧
      ∀ C : Set P, C ⊆ F → NonemptyChain C → ∀ s, IsLUB C s → s ∈ F := by
  constructor
  · rintro ⟨hl, hc⟩
    exact ⟨hl, fun C hCF hC s hs ↦ hc C hCF hC.directed s hs⟩
  · rintro ⟨hl, hc⟩
    have hF : IsChainComplete F := by
      intro C hC
      let A : Set P := Subtype.val '' C
      have hA : NonemptyChain A := by
        refine ⟨hC.1.image _, ?_⟩
        rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ _
        exact hC.2.total ha hb
      obtain ⟨s, hs⟩ := hP A hA.directed
      have hsF : s ∈ F := hc A (by rintro _ ⟨a, _, rfl⟩; exact a.property) hA s hs
      refine ⟨⟨s, hsF⟩, ?_, ?_⟩
      · intro c hcm
        exact hs.1 ⟨c, hcm, rfl⟩
      · intro q hq
        apply hs.2
        rintro _ ⟨c, hcm, rfl⟩
        exact hq hcm
    refine ⟨hl, ?_⟩
    intro D hDF hD s hs
    let B : Set F := Subtype.val ⁻¹' D
    have hB : NonemptyDirected B := by
      refine ⟨?_, ?_⟩
      · obtain ⟨d, hd⟩ := hD.1
        exact ⟨⟨d, hDF hd⟩, hd⟩
      · intro a ha b hb
        obtain ⟨c, hcD, hac, hbc⟩ := hD.2 a.val ha b.val hb
        exact ⟨⟨c, hDF hcD⟩, hcD, hac, hbc⟩
    obtain ⟨p, hp⟩ := chainComplete_dcpo hF B hB
    apply hl (show s ≤ p.val from hs.2 ?_) p.property
    intro d hd
    exact hp.1 (show (⟨d, hDF hd⟩ : F) ∈ B from hd)

/-- Source `lem:diagonal`: chain compactness and directed compactness agree. -/
theorem chainBelow_self_iff_wayBelow (hP : IsDcpo P) (a : P) :
    ChainBelow a a ↔ WayBelow a a := by
  refine ⟨fun ha ↦ ?_, fun ha ↦ ha.chainBelow hP⟩
  let F : Set P := {x | ¬ a ≤ x}
  have hlF : IsLowerSet F := by
    intro x y hxy hy hax
    exact hy (hax.trans hxy)
  have hcF : ∀ C : Set P, C ⊆ F → NonemptyChain C → ∀ s, IsLUB C s → s ∈ F := by
    intro C hCF hC s hs has
    obtain ⟨c, hc, hac⟩ := (chainBelow_iff_sup hP a a).mp ha C hC s hs has
    exact hCF hc hac
  have hF : IsScottClosed F := (scottClosed_iff_chainClosed hP F).mpr ⟨hlF, hcF⟩
  intro D hD s hs has
  by_contra hn
  have hDF : D ⊆ F := by
    intro d hd had
    exact hn ⟨d, hd, had⟩
  exact hF.2 D hDF hD s hs has

end ChainApproximation
