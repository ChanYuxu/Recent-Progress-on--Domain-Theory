import CHFubini.TailTopology
import Mathlib.Topology.Separation.Hausdorff

/-! Compact-countability and the ordinary-representative theorem for the
actual generated tail topology. No probability, Radon structure, or extra
open sets are assumed on the refined source.
-/

set_option autoImplicit false
open Set Topology TopologicalSpace Filter
universe u v
namespace CHFubini

/-- Source Lemma 5.1. The specified forgetful map embeds each compact
subspace into the second-countable Hausdorff ambient space. The basis then
separates all ordinal indices, proving countability of the actual compact set.
-/
theorem source_compact_countable {X : Type u} [TopologicalSpace X]
    [T2Space X] [SecondCountableTopology X] (a : OmegaOneStage → X)
    {C : Set (SourcePoint a)} (hC : IsCompact C) : C.Countable := by
  classical
  letI : CompactSpace C := isCompact_iff_compactSpace.mp hC
  let f : C → X := fun x => x.val.val
  have hf : Continuous f := (source_val_continuous a).comp continuous_subtype_val
  have hinj : Function.Injective f :=
    (SourcePoint.val_injective a).comp Subtype.val_injective
  letI : SecondCountableTopology C := (hf.isClosedEmbedding hinj).isEmbedding.secondCountableTopology
  have hb (x : C) : ∃ B ∈ countableBasis C,
      x ∈ B ∧ B ⊆ Subtype.val ⁻¹' sourceTail a (sourceIndex x.val) := by
    exact (isBasis_countableBasis C).exists_subset_of_mem_open
      (show x ∈ Subtype.val ⁻¹' sourceTail a (sourceIndex x.val) from by
        change sourceIndex x.val ≤ sourceIndex x.val
        exact le_rfl)
      ((sourceTail_isOpen a _).preimage continuous_subtype_val)
  choose B hB hxB hsub using hb
  let code : C → countableBasis C := fun x => ⟨B x,hB x⟩
  have hcode : Function.Injective code := by
    intro x y he
    have hBB : B x = B y := congrArg Subtype.val he
    have hxy : sourceIndex x.val ≤ sourceIndex y.val := hsub x (hBB ▸ hxB y)
    have hyx : sourceIndex y.val ≤ sourceIndex x.val := hsub y (hBB.symm ▸ hxB x)
    have hi := le_antisymm hxy hyx
    apply Subtype.ext
    apply SourcePoint.val_injective a
    rw [← sourceIndex_spec x.val,← sourceIndex_spec y.val,hi]
  letI : Countable C := hcode.countable
  exact Set.to_countable C

/-- The final, arbitrary-family assertion in `lem:ordinary-representatives`.
The one common bound is taken only over a countable circle-open subcover,
never over an uncountable family of ordinal deletion bounds.
-/
theorem ordinary_union_representative {X : Type u} [TopologicalSpace X]
    [SecondCountableTopology X] (a : OmegaOneStage → X)
    {I : Type v} (U : I → Set (SourcePoint a)) (O : I → Set X)
    (β : I → OmegaOneStage) (hO : ∀ i, IsOpen (O i))
    (hlo : ∀ i, sourceBase a (O i) (β i) ⊆ U i)
    (hup : ∀ i, U i ⊆ SourcePoint.val ⁻¹' O i) :
    ∃ σ : OmegaOneStage,
      sourceBase a (⋃ i, O i) σ ⊆ ⋃ i, U i ∧
      (⋃ i, U i) ⊆ SourcePoint.val ⁻¹' (⋃ i, O i) := by
  obtain ⟨J,hJ,hcover⟩ := isOpen_iUnion_countable O hO
  obtain ⟨σ,hσ⟩ := omegaOneStage_countablyBounded (β '' J) (hJ.image β)
  refine ⟨σ,?_,?_⟩
  · intro x hx
    have hxO : x.val ∈ ⋃ i ∈ J, O i := hcover.symm ▸ hx.1
    obtain ⟨i,hi,hxi⟩ := mem_iUnion₂.mp hxO
    exact mem_iUnion.mpr ⟨i,hlo i ⟨hxi,(hσ _ (mem_image_of_mem β hi)).trans hx.2⟩⟩
  · intro x hx
    obtain ⟨i,hxi⟩ := mem_iUnion.mp hx
    exact mem_iUnion.mpr ⟨i,hup i hxi⟩

/-- Source Lemma 3.3, the sandwich form of ordinary representatives. The
countable-deletion equivalent follows after proving initial segments countable.
-/
theorem source_ordinary_representative {X : Type u} [TopologicalSpace X]
    [SecondCountableTopology X] (a : OmegaOneStage → X)
    {U : Set (SourcePoint a)} (hU : IsOpen U) :
    ∃ O : Set X, IsOpen O ∧ ∃ β : OmegaOneStage,
      sourceBase a O β ⊆ U ∧ U ⊆ SourcePoint.val ⁻¹' O := by
  classical
  choose O hO β hx hsub using (fun x : U => hU x.val x.property)
  let V : U → Set (SourcePoint a) := fun x => sourceBase a (O x) (β x)
  have hVU : (⋃ x : U, V x) = U := by
    apply Subset.antisymm
    · intro x hxV
      obtain ⟨y,hxy⟩ := mem_iUnion.mp hxV
      exact hsub y hxy
    · intro x hxU
      exact mem_iUnion.mpr ⟨⟨x,hxU⟩,hx ⟨x,hxU⟩⟩
  obtain ⟨σ,hlo,hup⟩ := ordinary_union_representative a V O β hO
    (fun _ => Subset.rfl) (fun _ _ hy => hy.1)
  refine ⟨⋃ x : U, O x,isOpen_iUnion hO,σ,?_,?_⟩
  · rwa [hVU] at hlo
  · rwa [hVU] at hup

/-- The countable-deletion formulation of the same source lemma. This is a
property of already-open U; it is not a converse declaring more sets open. -/
theorem source_countable_deletion {X : Type u} [TopologicalSpace X]
    [SecondCountableTopology X] (a : OmegaOneStage → X)
    {U : Set (SourcePoint a)} (hU : IsOpen U) :
    ∃ (O : Set X) (C : Set (SourcePoint a)), IsOpen O ∧ C.Countable ∧
      C ⊆ SourcePoint.val ⁻¹' O ∧ U = (SourcePoint.val ⁻¹' O) \ C := by
  obtain ⟨O,hO,β,hlo,hup⟩ := source_ordinary_representative a hU
  let C : Set (SourcePoint a) := (SourcePoint.val ⁻¹' O) \ U
  have hCI : C ⊆ sourceInitial a β := by
    intro x hx
    change sourceIndex x < β
    apply lt_of_not_ge
    intro hβ
    exact hx.2 (hlo ⟨hx.1,hβ⟩)
  refine ⟨O,C,hO,(sourceInitial_countable a β).mono hCI,diff_subset,?_⟩
  ext x
  simp only [C,mem_diff]
  constructor
  · intro hx
    exact ⟨hup hx,fun h => h.2 hx⟩
  · intro hx
    by_contra hxu
    exact hx.2 ⟨hx.1,hxu⟩

end CHFubini
