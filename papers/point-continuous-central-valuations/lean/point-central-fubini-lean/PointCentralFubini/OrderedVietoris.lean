import PointCentralFubini.SourceStatements
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Homeomorph.Lemmas

/-! The compact ordered hyperspace in Lemma 4.4. Its upward topology is
identified with upper Vietoris directly, without an extra external theorem. -/
set_option autoImplicit false
open Set Topology TopologicalSpace
universe u v
namespace PointCentralFubini

@[implicit_reducible] def upwardTopology (E : Type u) [t : TopologicalSpace E] [Preorder E] :
    TopologicalSpace E where
  IsOpen G := IsOpen[t] G ∧ IsUpperSet G
  isOpen_univ := ⟨isOpen_univ,isUpperSet_univ⟩
  isOpen_inter _G _H hG hH := ⟨hG.1.inter hH.1,hG.2.inter hH.2⟩
  isOpen_sUnion _S hS := ⟨isOpen_sUnion (fun G hG => (hS G hG).1),
    isUpperSet_sUnion (fun G hG => (hS G hG).2)⟩

abbrev CompactOrder (T : Type u) [TopologicalSpace T] := OrderDual (NonemptyCompacts T)

instance compactOrder_compactSpace (T : Type u) [TopologicalSpace T] [CompactSpace T] :
    CompactSpace (CompactOrder T) := inferInstanceAs (CompactSpace (NonemptyCompacts T))

def compactBox {T : Type u} [TopologicalSpace T] (U : Set T) : Set (CompactOrder T) :=
  {K | ((OrderDual.ofDual K : NonemptyCompacts T) : Set T) ⊆ U}

def compactHit {T : Type u} [TopologicalSpace T] (U : Set T) : Set (CompactOrder T) :=
  {K | (((OrderDual.ofDual K : NonemptyCompacts T) : Set T) ∩ U).Nonempty}

theorem compactBox_open {T : Type u} [TopologicalSpace T] {U : Set T} (hU : IsOpen U) :
    IsOpen (compactBox U) := NonemptyCompacts.isOpen_subsets_of_isOpen hU

theorem compactHit_open {T : Type u} [TopologicalSpace T] {U : Set T} (hU : IsOpen U) :
    IsOpen (compactHit U) := NonemptyCompacts.isOpen_inter_nonempty_of_isOpen hU

instance compactOrder_orderClosed (T : Type u) [TopologicalSpace T] [T2Space T] :
    OrderClosedTopology (CompactOrder T) where
  isClosed_le' := by
    rw [← isOpen_compl_iff]
    apply isOpen_iff_forall_mem_open.mpr
    rintro ⟨K,H⟩ hnot
    change ¬ ((OrderDual.ofDual H : NonemptyCompacts T) : Set T) ⊆
      ((OrderDual.ofDual K : NonemptyCompacts T) : Set T) at hnot
    obtain ⟨x,hxH,hxK⟩ := Set.not_subset.mp hnot
    obtain ⟨W,V,hW,hV,hKW,hxV,hd⟩ := (OrderDual.ofDual K).isCompact.separation_of_notMem hxK
    refine ⟨compactBox W ×ˢ compactHit V,?_,(compactBox_open hW).prod (compactHit_open hV),
      hKW,⟨x,hxH,hxV⟩⟩
    rintro ⟨K',H'⟩ ⟨hK',hH'⟩ hle
    obtain ⟨y,hyH',hyV⟩ := hH'
    exact Set.disjoint_left.mp hd (hK' (hle hyH')) hyV

@[implicit_reducible] def upperVietoris (T : Type u) [TopologicalSpace T] :
    TopologicalSpace (CompactOrder T) := generateFrom {G | ∃ U : Opens T, G = compactBox U}

theorem upperVietoris_basis (T : Type u) [TopologicalSpace T] :
    @IsTopologicalBasis (CompactOrder T) (upperVietoris T)
      {G | ∃ U : Opens T, G = compactBox U} := by
  letI : TopologicalSpace (CompactOrder T) := upperVietoris T
  have h := @isTopologicalBasis_of_subbasis_of_inter (CompactOrder T) (upperVietoris T)
    {G | ∃ U : Opens T, G = compactBox U}
    rfl (by
      rintro _ ⟨U,rfl⟩ _ ⟨V,rfl⟩
      refine ⟨U ⊓ V,?_⟩
      ext K
      exact subset_inter_iff.symm)
  have hu : (univ : Set (CompactOrder T)) ∈ {G | ∃ U : Opens T, G = compactBox U} := by
    refine ⟨⊤,?_⟩
    ext K; simp [compactBox]
  simpa only [insert_eq_of_mem hu] using h

/-- An upward full-Vietoris neighbourhood of K contains a box neighbourhood:
adjoin K to any candidate compactum, then use upward closure. -/
theorem upwardVietoris_eq_upperVietoris (T : Type u) [TopologicalSpace T] :
    upwardTopology (CompactOrder T) = upperVietoris T := by
  apply le_antisymm
  · apply le_generateFrom
    rintro G ⟨U,rfl⟩
    exact ⟨compactBox_open U.isOpen,fun _K _L hKL hK x hx => hK (hKL hx)⟩
  · intro G hG
    have hfull : IsOpen G := hG.1
    have hu : IsUpperSet G := hG.2
    have hlocal : ∀ K ∈ G, ∃ U : Opens T, K ∈ compactBox U ∧ compactBox U ⊆ G := by
      intro K hK
      obtain ⟨N,⟨S,⟨hS,hSne,hSo⟩,rfl⟩,hKN,hNG⟩ :=
        NonemptyCompacts.isTopologicalBasis.exists_subset_of_mem_open hK hfull
      let U : Opens T := ⟨⋃₀ S,isOpen_sUnion hSo⟩
      refine ⟨U,hKN.1,?_⟩
      intro L hL
      let H : CompactOrder T := OrderDual.toDual (OrderDual.ofDual L ⊔ OrderDual.ofDual K)
      have hH : H ∈ G := by
        apply hNG
        constructor
        · exact union_subset hL hKN.1
        · intro V hV
          obtain ⟨x,hxK,hxV⟩ := hKN.2 V hV
          exact ⟨x,Or.inr hxK,hxV⟩
      have hHL : H ≤ L := by
        change ((OrderDual.ofDual L : NonemptyCompacts T) : Set T) ⊆
          ((OrderDual.ofDual L : NonemptyCompacts T) : Set T) ∪
            ((OrderDual.ofDual K : NonemptyCompacts T) : Set T)
        exact subset_union_left
      exact hu hHL hH
    letI : TopologicalSpace (CompactOrder T) := upperVietoris T
    apply (upperVietoris_basis T).isOpen_iff.mpr
    intro K hK
    obtain ⟨U,hKU,hUG⟩ := hlocal K hK
    exact ⟨compactBox U,⟨U,rfl⟩,hKU,hUG⟩

end PointCentralFubini
