import PointCentralFubini.SourceStatements
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Bases
import Mathlib.Topology.Instances.Real.Lemmas

/-! Elementary topology used in the proof of source Lemma 4.5. -/
set_option autoImplicit false
open Set Topology TopologicalSpace Filter
namespace PointCentralFubini

noncomputable instance : Field Sorgenfrey := inferInstanceAs (Field ℝ)
instance : IsStrictOrderedRing Sorgenfrey := inferInstanceAs (IsStrictOrderedRing ℝ)
instance : Archimedean Sorgenfrey := inferInstanceAs (Archimedean ℝ)

theorem sorgenfrey_isOpen_Ico (a b : Sorgenfrey) : IsOpen (Ico a b) := by
  by_cases h : a < b
  · exact isOpen_generateFrom_of_mem ⟨a, b, h, rfl⟩
  · rw [Ico_eq_empty_of_le (le_of_not_gt h)]
    exact isOpen_empty

theorem sorgenfrey_basis :
    IsTopologicalBasis {U : Set Sorgenfrey | ∃ a b, U = Ico a b} := by
  have hg : (inferInstance : TopologicalSpace Sorgenfrey) =
      generateFrom {U : Set Sorgenfrey | ∃ a b, U = Ico a b} := by
    apply le_antisymm
    · exact le_generateFrom (by rintro _ ⟨a,b,rfl⟩; exact sorgenfrey_isOpen_Ico a b)
    · apply generateFrom_anti
      rintro _ ⟨a,b,_,rfl⟩
      exact ⟨a,b,rfl⟩
  have hb := isTopologicalBasis_of_subbasis_of_inter hg (by
    rintro _ ⟨a,b,rfl⟩ _ ⟨c,d,rfl⟩
    exact ⟨max a c, min b d, Ico_inter_Ico⟩)
  apply hb.isTopologicalBasis_of_exists_subset
  · rintro _ ⟨a,b,rfl⟩; exact sorgenfrey_isOpen_Ico a b
  · intro U hU x hx
    rcases hU with rfl | hU
    · exact ⟨Ico x ((x : ℝ) + 1), ⟨x,((x : ℝ)+1),rfl⟩, ⟨le_rfl,by linarith⟩,
        subset_univ _⟩
    · exact ⟨U,hU,hx,Subset.rfl⟩

theorem sorgenfrey_isOpen_Ici (a : Sorgenfrey) : IsOpen (Ici a) := by
  apply sorgenfrey_basis.isOpen_iff.mpr
  intro x hx
  refine ⟨Ico x ((x : ℝ)+1), ⟨x,((x : ℝ)+1),rfl⟩, ⟨le_rfl,?_⟩, ?_⟩
  · change (x : ℝ) < (x : ℝ)+1; linarith
  · exact fun y hy => hx.trans hy.1

theorem sorgenfrey_isOpen_Iio (b : Sorgenfrey) : IsOpen (Iio b) := by
  apply sorgenfrey_basis.isOpen_iff.mpr
  intro x hx
  exact ⟨Ico x b, ⟨x,b,rfl⟩, ⟨le_rfl,hx⟩, fun _ hy => hy.2⟩

theorem sorgenfrey_isOpen_Ioi (a : Sorgenfrey) : IsOpen (Ioi a) := by
  apply sorgenfrey_basis.isOpen_iff.mpr
  intro x hx
  refine ⟨Ico x ((x : ℝ)+1), ⟨x,((x : ℝ)+1),rfl⟩, ⟨le_rfl,?_⟩, fun _ hy => hx.trans_le hy.1⟩
  change (x : ℝ) < (x : ℝ)+1; linarith

theorem sorgenfrey_isClopen_Iio (a : Sorgenfrey) : IsClopen (Iio a) :=
  ⟨by simpa only [compl_Ici] using (sorgenfrey_isOpen_Ici a).isClosed_compl,
    sorgenfrey_isOpen_Iio a⟩

instance : ClosedIicTopology Sorgenfrey :=
  ⟨fun a => by simpa only [compl_Ioi] using (sorgenfrey_isOpen_Ioi a).isClosed_compl⟩
instance : ClosedIciTopology Sorgenfrey :=
  ⟨fun a => by simpa only [compl_Iio] using (sorgenfrey_isOpen_Iio a).isClosed_compl⟩

theorem sorgenfrey_toReal_continuous :
    @Continuous Sorgenfrey ℝ inferInstance (inferInstanceAs (TopologicalSpace ℝ)) (fun x => x) := by
  apply Real.isTopologicalBasis_Ioo_rat.continuous_iff.mpr
  intro V hV
  simp only [mem_iUnion,mem_singleton_iff] at hV
  obtain ⟨a,b,_,rfl⟩ := hV
  exact (sorgenfrey_isOpen_Ioi (a : ℝ)).inter (sorgenfrey_isOpen_Iio (b : ℝ))

instance : T2Space Sorgenfrey :=
  T2Space.of_injective_continuous (Y := ℝ) (fun _ _ h => h) sorgenfrey_toReal_continuous

instance : FirstCountableTopology Sorgenfrey := by
  constructor
  intro x
  have hb : (𝓝 x).HasBasis (fun q : ℚ => (x : ℝ) < q)
      (fun q => Ico x (q : ℝ)) := by
    constructor
    intro U
    constructor
    · intro hU
      obtain ⟨V,⟨a,b,rfl⟩,hx,hVU⟩ := sorgenfrey_basis.mem_nhds_iff.mp hU
      obtain ⟨q,hxq,hqb⟩ := exists_rat_btwn (show (x : ℝ) < b from hx.2)
      exact ⟨q,hxq,(Ico_subset_Ico_left hx.1).trans
        ((Ico_subset_Ico_right hqb.le).trans hVU)⟩
    · rintro ⟨q,hq,hU⟩
      exact mem_of_superset ((sorgenfrey_isOpen_Ico x (q : ℝ)).mem_nhds ⟨le_rfl,hq⟩) hU
  exact (show (𝓝 x).HasCountableBasis (fun q : ℚ => (x : ℝ) < q)
    (fun q => Ico x (q : ℝ)) from ⟨hb,Set.to_countable _⟩).isCountablyGenerated

instance : FirstCountableTopology ObservationCodomain := by
  constructor
  rintro (x | x)
  · rw [nhds_inl]; infer_instance
  · rw [nhds_inr]; infer_instance

theorem RationalClopen.isClopen {C : Set Sorgenfrey} (hC : RationalClopen C) :
    IsClopen C := by
  induction hC with
  | ray q => exact sorgenfrey_isClopen_Iio (q : ℝ)
  | empty => exact isClopen_empty
  | compl _ ih => exact ih.compl
  | union _ _ ih₁ ih₂ => exact ih₁.union ih₂

theorem RationalClopen.inter {C D : Set Sorgenfrey}
    (hC : RationalClopen C) (hD : RationalClopen D) : RationalClopen (C ∩ D) := by
  simpa only [compl_union, compl_compl] using (hC.compl.union hD.compl).compl

theorem rationalClopen_Ico (p q : ℚ) :
    RationalClopen (Ico (p : ℝ) (q : ℝ)) := by
  convert (RationalClopen.ray p).compl.inter (RationalClopen.ray q) using 1
  ext x; simp [mem_Ico, not_lt]

private def rationalClopenStage : ℕ → Set (Set Sorgenfrey)
  | 0 => insert ∅ (range (fun q : ℚ => Iio (q : ℝ)))
  | n+1 => rationalClopenStage n ∪ (compl '' rationalClopenStage n) ∪
      image2 (· ∪ ·) (rationalClopenStage n) (rationalClopenStage n)

private theorem rationalClopenStage_countable (n : ℕ) :
    (rationalClopenStage n).Countable := by
  induction n with
  | zero => exact (countable_range _).insert _
  | succ n ih => exact (ih.union (ih.image _)).union (ih.image2 ih _)

private theorem rationalClopenStage_mono : Monotone rationalClopenStage :=
  monotone_nat_of_le_succ (fun _ => fun _ h => Or.inl (Or.inl h))

theorem rationalClopen_countable : {C : Set Sorgenfrey | RationalClopen C}.Countable := by
  apply (countable_iUnion rationalClopenStage_countable).mono
  intro C hC
  suffices ∃ n, C ∈ rationalClopenStage n from mem_iUnion.mpr this
  induction hC with
  | ray q => exact ⟨0,Or.inr (mem_range_self q)⟩
  | empty => exact ⟨0,mem_insert _ _⟩
  | compl _ ih =>
    obtain ⟨n,hn⟩ := ih
    exact ⟨n+1,Or.inl (Or.inr (mem_image_of_mem _ hn))⟩
  | union _ _ ih₁ ih₂ =>
    obtain ⟨n,hn⟩ := ih₁
    obtain ⟨m,hm⟩ := ih₂
    exact ⟨max n m+1,Or.inr (mem_image2_of_mem
      (rationalClopenStage_mono (le_max_left n m) hn)
      (rationalClopenStage_mono (le_max_right n m) hm))⟩

instance : Countable {C : Set Sorgenfrey // RationalClopen C} :=
  rationalClopen_countable.to_subtype

/-- A compact Sorgenfrey set has a gap immediately below each of its points.
This proves the rational-clopen refinement on a compact set directly. -/
theorem compact_rationalClopen_refinement (K : SorgenfreyVietoris)
    {x : Sorgenfrey} (_hx : x ∈ K) {U : Set Sorgenfrey} (hU : IsOpen U) (hxU : x ∈ U) :
    ∃ C : Set Sorgenfrey, RationalClopen C ∧ x ∈ C ∧ (K : Set Sorgenfrey) ∩ C ⊆ U := by
  obtain ⟨V,⟨a,b,rfl⟩,hxab,hVU⟩ := sorgenfrey_basis.exists_subset_of_mem_open hxU hU
  have hc := K.isCompact.inter_right (sorgenfrey_isClopen_Iio x).isClosed
  have hgap : ∃ p : ℚ, (p : ℝ) < (x : ℝ) ∧
      ∀ y ∈ (K : Set Sorgenfrey), (p : ℝ) ≤ (y : ℝ) → x ≤ y := by
    by_cases hn : ((K : Set Sorgenfrey) ∩ Iio x).Nonempty
    · obtain ⟨z,hz,hmax⟩ := hc.exists_isGreatest hn
      obtain ⟨p,hzp,hpx⟩ := exists_rat_btwn (show (z : ℝ) < x from hz.2)
      refine ⟨p,hpx,?_⟩
      intro y hy hpy
      by_contra hxy
      exact (not_le_of_gt hzp) (hpy.trans (hmax ⟨hy,lt_of_not_ge hxy⟩))
    · obtain ⟨p,hp⟩ := exists_rat_lt (x : ℝ)
      refine ⟨p,hp,?_⟩
      intro y hy _
      exact le_of_not_gt (fun h => hn ⟨y,hy,h⟩)
  obtain ⟨p,hpx,hp⟩ := hgap
  obtain ⟨q,hxq,hqb⟩ := exists_rat_btwn (show (x : ℝ) < b from hxab.2)
  refine ⟨Ico (p : ℝ) (q : ℝ),rationalClopen_Ico p q,⟨hpx.le,hxq⟩,?_⟩
  intro y hy
  exact hVU ⟨hxab.1.trans (hp y hy.1 hy.2.1), hy.2.2.trans hqb⟩

end PointCentralFubini
