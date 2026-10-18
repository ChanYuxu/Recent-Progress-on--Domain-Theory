import PointCentralFubini.OrderedVietoris

/-! Embeddings of compact hyperspaces, for both Vietoris topologies. -/
set_option autoImplicit false
open Set Topology TopologicalSpace
universe u v
namespace PointCentralFubini
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

def compactMap (f : X → Y) (hf : Continuous f) : CompactOrder X → CompactOrder Y :=
  fun K => OrderDual.toDual ((OrderDual.ofDual K).map f hf)

theorem compactMap_box_preimage (f : X → Y) (hf : Continuous f) (V : Set Y) :
    compactMap f hf ⁻¹' compactBox V = compactBox (f ⁻¹' V) := by
  ext K
  exact image_subset_iff

theorem compactMap_full_embedding {f : X → Y} (hf : IsEmbedding f) :
    IsEmbedding (compactMap f hf.continuous) := hf.nonemptyCompacts_map

theorem compactMap_upper_inducing {f : X → Y} (hf : IsInducing f) :
    @IsInducing (CompactOrder X) (CompactOrder Y) (upperVietoris X) (upperVietoris Y)
      (compactMap f hf.continuous) := by
  letI : TopologicalSpace (CompactOrder X) := upperVietoris X
  letI : TopologicalSpace (CompactOrder Y) := upperVietoris Y
  refine ⟨?_⟩
  unfold upperVietoris
  rw [induced_generateFrom_eq]
  congr 1
  ext G
  constructor
  · rintro ⟨U,rfl⟩
    obtain ⟨V,hV,heq⟩ := hf.isOpen_iff.mp U.isOpen
    refine ⟨compactBox V,⟨⟨V,hV⟩,rfl⟩,?_⟩
    rw [compactMap_box_preimage,heq]
  · rintro ⟨_,⟨V,rfl⟩,rfl⟩
    exact ⟨Opens.comap ⟨f,hf.continuous⟩ V,compactMap_box_preimage f hf.continuous V⟩

/-- Compact subsets of the embedded image lift back to compact subsets.
This proves upward closure without requiring the image to be Borel. -/
theorem compactMap_range_upper {f : X → Y} (hf : IsEmbedding f) :
    IsUpperSet (range (compactMap f hf.continuous)) := by
  rintro _ H hKH ⟨K,rfl⟩
  have hH : ((OrderDual.ofDual H : NonemptyCompacts Y) : Set Y) ⊆ range f := by
    intro y hy
    obtain ⟨x,_hx,rfl⟩ := hKH hy
    exact mem_range_self x
  have heq : f '' (f ⁻¹' ((OrderDual.ofDual H : NonemptyCompacts Y) : Set Y)) =
      ((OrderDual.ofDual H : NonemptyCompacts Y) : Set Y) := image_preimage_eq_of_subset hH
  have hne : (f ⁻¹' ((OrderDual.ofDual H : NonemptyCompacts Y) : Set Y)).Nonempty := by
    obtain ⟨y,hy⟩ := (OrderDual.ofDual H).nonempty
    obtain ⟨x,rfl⟩ := hH hy
    exact ⟨x,hy⟩
  let L : NonemptyCompacts X :=
    ⟨⟨f ⁻¹' ((OrderDual.ofDual H : NonemptyCompacts Y) : Set Y),
      hf.isCompact_iff.mpr (heq.symm ▸ (OrderDual.ofDual H).isCompact)⟩,hne⟩
  refine ⟨OrderDual.toDual L,?_⟩
  apply NonemptyCompacts.ext
  exact heq

end PointCentralFubini
