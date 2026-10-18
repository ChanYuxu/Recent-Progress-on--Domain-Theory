import PointCentralFubini.SorgenfreyBasics

/-! The concrete extrema and topology-generation proof for source Lemma 4.5. -/
set_option autoImplicit false
open Set Topology TopologicalSpace Filter
namespace PointCentralFubini

abbrev RationalFragment := {C : Set Sorgenfrey // RationalClopen C}

theorem exists_lowerObservation (C : RationalFragment) (K : SorgenfreyVietoris) :
    ∃ z, IsLowerObservation C.val K z := by
  by_cases h : ((K : Set Sorgenfrey) ∩ C.val).Nonempty
  · obtain ⟨a,ha⟩ := (K.isCompact.inter_right C.property.isClopen.isClosed).exists_isLeast h
    exact ⟨.inl a,ha⟩
  · exact ⟨.inr (),Set.not_nonempty_iff_eq_empty.mp h⟩

theorem exists_upperObservation (C : RationalFragment) (K : SorgenfreyVietoris) :
    ∃ z, IsUpperObservation C.val K z := by
  by_cases h : ((K : Set Sorgenfrey) ∩ C.val).Nonempty
  · obtain ⟨a,ha⟩ := (K.isCompact.inter_right C.property.isClopen.isClosed).exists_isGreatest h
    exact ⟨.inl a,ha⟩
  · exact ⟨.inr (),Set.not_nonempty_iff_eq_empty.mp h⟩

noncomputable def lowerObservation (C : RationalFragment) (K : SorgenfreyVietoris) :
    ObservationCodomain := (exists_lowerObservation C K).choose
noncomputable def upperObservation (C : RationalFragment) (K : SorgenfreyVietoris) :
    ObservationCodomain := (exists_upperObservation C K).choose

theorem lowerObservation_spec (C : RationalFragment) (K : SorgenfreyVietoris) :
    IsLowerObservation C.val K (lowerObservation C K) := (exists_lowerObservation C K).choose_spec
theorem upperObservation_spec (C : RationalFragment) (K : SorgenfreyVietoris) :
    IsUpperObservation C.val K (upperObservation C K) := (exists_upperObservation C K).choose_spec

theorem lowerObservation_star_iff (C : RationalFragment) (K : SorgenfreyVietoris) :
    lowerObservation C K = .inr () ↔ (K : Set Sorgenfrey) ∩ C.val = ∅ := by
  have hs := lowerObservation_spec C K
  cases he : lowerObservation C K with
  | inl a =>
    simp only [he,IsLowerObservation] at hs
    simp only [Sum.inl_ne_inr, false_iff]
    exact Set.nonempty_iff_ne_empty.mp ⟨a,hs.1⟩
  | inr z =>
    cases z
    simp only [he,IsLowerObservation] at hs
    exact ⟨fun _ => hs,fun _ => rfl⟩

theorem upperObservation_star_iff (C : RationalFragment) (K : SorgenfreyVietoris) :
    upperObservation C K = .inr () ↔ (K : Set Sorgenfrey) ∩ C.val = ∅ := by
  have hs := upperObservation_spec C K
  cases he : upperObservation C K with
  | inl a =>
    simp only [he,IsUpperObservation] at hs
    simp only [Sum.inl_ne_inr, false_iff]
    exact Set.nonempty_iff_ne_empty.mp ⟨a,hs.1⟩
  | inr z =>
    cases z
    simp only [he,IsUpperObservation] at hs
    exact ⟨fun _ => hs,fun _ => rfl⟩

def observationIntervals : Set (Set ObservationCodomain) :=
  {V | ∃ a b : Sorgenfrey, V = Sum.inl '' Ico a b} ∪ {{Sum.inr ()}}

theorem observation_basis : IsTopologicalBasis observationIntervals := by
  apply isTopologicalBasis_of_isOpen_of_nhds
  · rintro V (⟨a,b,rfl⟩ | h)
    · exact isOpenMap_inl _ (sorgenfrey_isOpen_Ico a b)
    · rcases h with rfl
      convert isOpenMap_inr (univ : Set Unit) isOpen_univ using 1
      ext z
      cases z with
      | inl x => simp
      | inr u => cases u; simp
  · rintro (x | ⟨⟩) U hx hU
    · obtain ⟨V,⟨a,b,rfl⟩,hxV,hVU⟩ := sorgenfrey_basis.exists_subset_of_mem_open
        hx (hU.preimage continuous_inl)
      exact ⟨Sum.inl '' Ico a b,Or.inl ⟨a,b,rfl⟩,mem_image_of_mem _ hxV,
        image_subset_iff.mpr hVU⟩
    · exact ⟨{Sum.inr ()},Or.inr rfl,mem_singleton _,singleton_subset_iff.mpr hx⟩

theorem lowerObservation_interval (C : RationalFragment) (K : SorgenfreyVietoris)
    (a b : Sorgenfrey) :
    lowerObservation C K ∈ Sum.inl '' Ico a b ↔
      (K : Set Sorgenfrey) ⊆ C.valᶜ ∪ Ici a ∧
      ((K : Set Sorgenfrey) ∩ (C.val ∩ Iio b)).Nonempty := by
  have hs := lowerObservation_spec C K
  cases he : lowerObservation C K with
  | inl z =>
    simp only [he,IsLowerObservation] at hs
    simp only [mem_image,Sum.inl.injEq,exists_eq_right]
    constructor
    · intro hz
      refine ⟨fun y hy => ?_, z,hs.1.1,hs.1.2,hz.2⟩
      by_cases hyC : y ∈ C.val
      · exact Or.inr (hz.1.trans (hs.2 y ⟨hy,hyC⟩))
      · exact Or.inl hyC
    · rintro ⟨hsub,y,hyK,hyC,hyb⟩
      refine ⟨?_,(hs.2 y ⟨hyK,hyC⟩).trans_lt hyb⟩
      exact (hsub hs.1.1).resolve_left (fun h => h hs.1.2)
  | inr z =>
    simp only [he,IsLowerObservation] at hs
    simp only [mem_image,Sum.inl_ne_inr,and_false,exists_false,false_iff,not_and]
    intro _ hn
    obtain ⟨y,hyK,hyC,_⟩ := hn
    exact Set.notMem_empty y (hs ▸ ⟨hyK,hyC⟩)

theorem upperObservation_interval (C : RationalFragment) (K : SorgenfreyVietoris)
    (a b : Sorgenfrey) :
    upperObservation C K ∈ Sum.inl '' Ico a b ↔
      ((K : Set Sorgenfrey) ∩ (C.val ∩ Ici a)).Nonempty ∧
      (K : Set Sorgenfrey) ⊆ C.valᶜ ∪ Iio b := by
  have hs := upperObservation_spec C K
  cases he : upperObservation C K with
  | inl z =>
    simp only [he,IsUpperObservation] at hs
    simp only [mem_image,Sum.inl.injEq,exists_eq_right]
    constructor
    · intro hz
      refine ⟨⟨z,hs.1.1,hs.1.2,hz.1⟩,fun y hy => ?_⟩
      by_cases hyC : y ∈ C.val
      · exact Or.inr ((hs.2 y ⟨hy,hyC⟩).trans_lt hz.2)
      · exact Or.inl hyC
    · rintro ⟨⟨y,hyK,hyC,hay⟩,hsub⟩
      refine ⟨hay.trans (hs.2 y ⟨hyK,hyC⟩),?_⟩
      exact (hsub hs.1.1).resolve_left (fun h => h hs.1.2)
  | inr z =>
    simp only [he,IsUpperObservation] at hs
    simp only [mem_image,Sum.inl_ne_inr,and_false,exists_false,false_iff,not_and]
    rintro ⟨y,hyK,hyC,_⟩ _
    exact Set.notMem_empty y (hs ▸ ⟨hyK,hyC⟩)

theorem lowerObservation_continuous (C : RationalFragment) : Continuous (lowerObservation C) := by
  apply observation_basis.continuous_iff.mpr
  rintro V (⟨a,b,rfl⟩ | hV)
  · have he : lowerObservation C ⁻¹' (Sum.inl '' Ico a b) =
        {K : SorgenfreyVietoris | (K : Set Sorgenfrey) ⊆ C.valᶜ ∪ Ici a} ∩
        {K : SorgenfreyVietoris | ((K : Set Sorgenfrey) ∩ (C.val ∩ Iio b)).Nonempty} :=
      Set.ext (fun K => lowerObservation_interval C K a b)
    rw [he]
    exact (NonemptyCompacts.isOpen_subsets_of_isOpen
      (C.property.isClopen.compl.isOpen.union (sorgenfrey_isOpen_Ici a))).inter
      (NonemptyCompacts.isOpen_inter_nonempty_of_isOpen
        (C.property.isClopen.isOpen.inter (sorgenfrey_isOpen_Iio b)))
  · rcases hV with rfl
    have he : lowerObservation C ⁻¹' {Sum.inr ()} =
        {K : SorgenfreyVietoris | (K : Set Sorgenfrey) ⊆ C.valᶜ} := by
      ext K
      simp only [mem_preimage,mem_singleton_iff,mem_setOf_eq,lowerObservation_star_iff,
         ]
      rw [← Set.disjoint_iff_inter_eq_empty,← Set.subset_compl_iff_disjoint_right]
    rw [he]
    exact NonemptyCompacts.isOpen_subsets_of_isOpen C.property.isClopen.compl.isOpen

theorem upperObservation_continuous (C : RationalFragment) : Continuous (upperObservation C) := by
  apply observation_basis.continuous_iff.mpr
  rintro V (⟨a,b,rfl⟩ | hV)
  · have he : upperObservation C ⁻¹' (Sum.inl '' Ico a b) =
        {K : SorgenfreyVietoris | ((K : Set Sorgenfrey) ∩ (C.val ∩ Ici a)).Nonempty} ∩
        {K : SorgenfreyVietoris | (K : Set Sorgenfrey) ⊆ C.valᶜ ∪ Iio b} :=
      Set.ext (fun K => upperObservation_interval C K a b)
    rw [he]
    exact (NonemptyCompacts.isOpen_inter_nonempty_of_isOpen
      (C.property.isClopen.isOpen.inter (sorgenfrey_isOpen_Ici a))).inter
      (NonemptyCompacts.isOpen_subsets_of_isOpen
        (C.property.isClopen.compl.isOpen.union (sorgenfrey_isOpen_Iio b)))
  · rcases hV with rfl
    have he : upperObservation C ⁻¹' {Sum.inr ()} =
        {K : SorgenfreyVietoris | (K : Set Sorgenfrey) ⊆ C.valᶜ} := by
      ext K
      simp only [mem_preimage,mem_singleton_iff,mem_setOf_eq,upperObservation_star_iff,
         ]
      rw [← Set.disjoint_iff_inter_eq_empty,← Set.subset_compl_iff_disjoint_right]
    rw [he]
    exact NonemptyCompacts.isOpen_subsets_of_isOpen C.property.isClopen.compl.isOpen

@[implicit_reducible] noncomputable def extremalTopology : TopologicalSpace SorgenfreyVietoris :=
  (⨅ C : RationalFragment, induced (lowerObservation C) inferInstance) ⊓
    (⨅ C : RationalFragment, induced (upperObservation C) inferInstance)

private theorem lowerObservation_extremal_continuous (C : RationalFragment) :
    @Continuous SorgenfreyVietoris ObservationCodomain extremalTopology inferInstance
      (lowerObservation C) :=
  continuous_iff_le_induced.mpr (inf_le_left.trans (iInf_le _ C))

private theorem upperObservation_extremal_continuous (C : RationalFragment) :
    @Continuous SorgenfreyVietoris ObservationCodomain extremalTopology inferInstance
      (upperObservation C) :=
  continuous_iff_le_induced.mpr (inf_le_right.trans (iInf_le _ C))

private theorem fragment_empty_extremal_open (C : RationalFragment) :
    @IsOpen SorgenfreyVietoris extremalTopology
      {K | (K : Set Sorgenfrey) ∩ C.val = ∅} := by
  letI : TopologicalSpace SorgenfreyVietoris := extremalTopology
  have he : {K : SorgenfreyVietoris | (K : Set Sorgenfrey) ∩ C.val = ∅} =
      lowerObservation C ⁻¹' {Sum.inr ()} :=
    Set.ext (fun K => (lowerObservation_star_iff C K).symm)
  rw [he]
  have hs : IsOpen ({Sum.inr ()} : Set ObservationCodomain) :=
    observation_basis.isOpen (Or.inr rfl)
  exact hs.preimage (lowerObservation_extremal_continuous C)

private theorem fragment_interval_extremal_open (C : RationalFragment) (a b : Sorgenfrey) :
    @IsOpen SorgenfreyVietoris extremalTopology
      {K | ((K : Set Sorgenfrey) ∩ C.val).Nonempty ∧
        (K : Set Sorgenfrey) ∩ C.val ⊆ Ico a b} := by
  letI : TopologicalSpace SorgenfreyVietoris := extremalTopology
  have he : {K : SorgenfreyVietoris | ((K : Set Sorgenfrey) ∩ C.val).Nonempty ∧
        (K : Set Sorgenfrey) ∩ C.val ⊆ Ico a b} =
      (lowerObservation C ⁻¹' (Sum.inl '' Ici a)) ∩
      (upperObservation C ⁻¹' (Sum.inl '' Iio b)) := by
    ext K
    constructor
    · rintro ⟨⟨z,hz⟩,hsub⟩
      constructor
      · have hs := lowerObservation_spec C K
        cases h : lowerObservation C K with
        | inl l =>
          simp only [h,IsLowerObservation] at hs
          exact ⟨l,(hsub hs.1).1,h.symm⟩
        | inr u =>
          simp only [h,IsLowerObservation] at hs
          exact False.elim (notMem_empty z (hs ▸ hz))
      · have hs := upperObservation_spec C K
        cases h : upperObservation C K with
        | inl u =>
          simp only [h,IsUpperObservation] at hs
          exact ⟨u,(hsub hs.1).2,h.symm⟩
        | inr u =>
          simp only [h,IsUpperObservation] at hs
          exact False.elim (notMem_empty z (hs ▸ hz))
    · rintro ⟨⟨l,hal,hl⟩,⟨u,hub,hu⟩⟩
      have hls := lowerObservation_spec C K
      have hus := upperObservation_spec C K
      rw [← hl] at hls
      rw [← hu] at hus
      exact ⟨⟨l,hls.1⟩,fun y hy =>
        ⟨hal.trans (hls.2 y hy),(hus.2 y hy).trans_lt hub⟩⟩
  rw [he]
  exact ((isOpenMap_inl _ (sorgenfrey_isOpen_Ici a)).preimage
    (lowerObservation_extremal_continuous C)).inter
    ((isOpenMap_inl _ (sorgenfrey_isOpen_Iio b)).preimage
      (upperObservation_extremal_continuous C))

private theorem extremal_diamond_open {U : Set Sorgenfrey} (hU : IsOpen U) :
    @IsOpen SorgenfreyVietoris extremalTopology
      {K | ((K : Set Sorgenfrey) ∩ U).Nonempty} := by
  letI : TopologicalSpace SorgenfreyVietoris := extremalTopology
  apply isOpen_iff_forall_mem_open.mpr
  rintro K ⟨x,hxK,hxU⟩
  obtain ⟨V,⟨a,b,rfl⟩,hxV,hVU⟩ := sorgenfrey_basis.exists_subset_of_mem_open hxU hU
  obtain ⟨C,hC,hxC,hKC⟩ := compact_rationalClopen_refinement K hxK
    (sorgenfrey_isOpen_Ico a b) hxV
  refine ⟨{K' | ((K' : Set Sorgenfrey) ∩ C).Nonempty ∧
      (K' : Set Sorgenfrey) ∩ C ⊆ Ico a b}, ?_,
      fragment_interval_extremal_open ⟨C,hC⟩ a b,⟨x,hxK,hxC⟩,hKC⟩
  rintro K' ⟨⟨y,hy⟩,hsub⟩
  exact ⟨y,hy.1,hVU (hsub hy)⟩

private theorem extremal_box_open {U : Set Sorgenfrey} (hU : IsOpen U) :
    @IsOpen SorgenfreyVietoris extremalTopology {K | (K : Set Sorgenfrey) ⊆ U} := by
  classical
  letI : TopologicalSpace SorgenfreyVietoris := extremalTopology
  apply isOpen_iff_forall_mem_open.mpr
  intro K hKU
  have hc : ∀ x : (K : Set Sorgenfrey), ∃ (C : RationalFragment) (a b : Sorgenfrey),
      x.val ∈ C.val ∧ (K : Set Sorgenfrey) ∩ C.val ⊆ Ico a b ∧ Ico a b ⊆ U := by
    intro x
    obtain ⟨V,⟨a,b,rfl⟩,hxV,hVU⟩ := sorgenfrey_basis.exists_subset_of_mem_open
      (hKU x.property) hU
    obtain ⟨C,hC,hxC,hKC⟩ := compact_rationalClopen_refinement K x.property
      (sorgenfrey_isOpen_Ico a b) hxV
    exact ⟨⟨C,hC⟩,a,b,hxC,hKC,hVU⟩
  choose C a b hxC hKC hCU using hc
  obtain ⟨s,hs⟩ := K.isCompact.elim_finite_subcover (fun x => (C x).val)
    (fun x => (C x).property.isClopen.isOpen) (by
      intro x hx
      exact mem_iUnion.mpr ⟨⟨x,hx⟩,hxC ⟨x,hx⟩⟩)
  let R : Set Sorgenfrey := ⋃ x ∈ s, (C x).val
  have hR : RationalClopen R := by
    dsimp [R]
    clear hs R
    induction s using Finset.induction_on with
    | empty => simpa using RationalClopen.empty
    | @insert x s hx ih =>
      simpa only [Finset.set_biUnion_insert] using (C x).property.union ih
  let W : Set SorgenfreyVietoris := {K' | (K' : Set Sorgenfrey) ∩ Rᶜ = ∅} ∩
    ⋂ x ∈ s, {K' | ((K' : Set Sorgenfrey) ∩ (C x).val).Nonempty ∧
      (K' : Set Sorgenfrey) ∩ (C x).val ⊆ Ico (a x) (b x)}
  refine ⟨W,?_,?_,?_,?_⟩
  · rintro K' ⟨hR',hbound⟩ y hy
    have hyR : y ∈ R := by
      by_contra hn
      exact notMem_empty y (hR' ▸ ⟨hy,hn⟩)
    obtain ⟨x,hxs,hyC⟩ := mem_iUnion₂.mp hyR
    exact hCU x ((mem_iInter₂.mp hbound x hxs).2 ⟨hy,hyC⟩)
  · exact (fragment_empty_extremal_open ⟨Rᶜ,hR.compl⟩).inter
      (s.finite_toSet.isOpen_biInter (fun x _ => fragment_interval_extremal_open (C x) (a x) (b x)))
  · apply Set.eq_empty_iff_forall_notMem.mpr
    rintro y ⟨hyK,hyR⟩
    exact hyR (hs hyK)
  · apply mem_iInter₂.mpr
    intro x _
    exact ⟨⟨x.val,x.property,hxC x⟩,hKC x⟩

theorem extremalTopology_eq :
    (inferInstance : TopologicalSpace SorgenfreyVietoris) = extremalTopology := by
  apply le_antisymm
  · apply le_inf
    · apply le_iInf; intro C
      exact continuous_iff_le_induced.mp (lowerObservation_continuous C)
    · apply le_iInf; intro C
      exact continuous_iff_le_induced.mp (upperObservation_continuous C)
  · have hc : @Continuous SorgenfreyVietoris (Set Sorgenfrey) extremalTopology
        (.vietoris Sorgenfrey) SetLike.coe := by
      apply continuous_generateFrom_iff.mpr
      rintro G (⟨U,hU,rfl⟩ | ⟨U,hU,rfl⟩)
      · exact extremal_box_open hU
      · exact extremal_diamond_open hU
    exact continuous_iff_le_induced.mp hc

theorem sorgenfreyVietoris_firstCountable : FirstCountableTopology SorgenfreyVietoris := by
  let f : SorgenfreyVietoris →
      (RationalFragment → ObservationCodomain) × (RationalFragment → ObservationCodomain) :=
    fun K => (fun C => lowerObservation C K,fun C => upperObservation C K)
  have hf : (inferInstance : TopologicalSpace SorgenfreyVietoris) =
      induced f inferInstance := by
    rw [extremalTopology_eq]
    simp only [f,instTopologicalSpaceProd,induced_inf,Pi.topologicalSpace,induced_iInf,
      induced_compose,Function.comp_def,extremalTopology]
  exact (show IsInducing f from ⟨hf⟩).firstCountableTopology

/-- Source contract: `lem:extremal-observables` (lemma 4.5).
Version: SHA-256 `134da69fa816824e5fefcb93a4e77a8cd5158c8aaab5ffd288ece2372e55d4e6`.
Locator: `source/manuscript.tex`, lines 549--551; no PDF was supplied.
Formalization status: `proved`; human review is pending.

Strict source TeX:
```latex
\begin{lemma}\label{lem:extremal-observables}
The maps $\ell_C,u_C$, $C\in\mathscr A$, are continuous and jointly generate the full Vietoris topology. In particular, $D_{\mathrm V}$ is first-countable.
\end{lemma}
```
-/
theorem extremal_observables : ExtremalObservablesStatement :=
  ⟨lowerObservation,upperObservation,lowerObservation_spec,upperObservation_spec,
    fun C => ⟨lowerObservation_continuous C,upperObservation_continuous C⟩,
    extremalTopology_eq,sorgenfreyVietoris_firstCountable⟩

end PointCentralFubini
