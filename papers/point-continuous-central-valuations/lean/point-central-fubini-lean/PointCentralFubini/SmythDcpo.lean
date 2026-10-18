import PointCentralFubini.SorgenfreyBasics

/-! The reverse-inclusion dcpo structure is proved from compactness and Hausdorffness. -/
set_option autoImplicit false
open Set Topology TopologicalSpace
universe u
namespace PointCentralFubini

theorem nonemptyCompacts_reverse_isDcpo (X : Type u) [TopologicalSpace X] [T2Space X] :
    IsDcpo (OrderDual (NonemptyCompacts X)) := by
  intro A hn hd
  letI : Nonempty A := hn.to_subtype
  let F : A → Set X := fun K => (OrderDual.ofDual K.val : NonemptyCompacts X)
  have hF : Directed (· ⊇ ·) F := by
    intro K L
    obtain ⟨M,hM,hKM,hLM⟩ := hd K.val K.property L.val L.property
    exact ⟨⟨M,hM⟩,hKM,hLM⟩
  have hne : (⋂ K, F K).Nonempty :=
    IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed F hF
      (fun K => (OrderDual.ofDual K.val).nonempty)
      (fun K => (OrderDual.ofDual K.val).isCompact)
      (fun K => (OrderDual.ofDual K.val).isCompact.isClosed)
  obtain ⟨K₀,hK₀⟩ := hn
  have hc : IsCompact (⋂ K, F K) :=
    (OrderDual.ofDual K₀).isCompact.of_isClosed_subset
      (isClosed_iInter (fun K => (OrderDual.ofDual K.val).isCompact.isClosed))
      (iInter_subset F ⟨K₀,hK₀⟩)
  let K : NonemptyCompacts X := ⟨⟨⋂ i, F i,hc⟩,hne⟩
  refine ⟨OrderDual.toDual K,?_,?_⟩
  · intro L hL
    exact iInter_subset F ⟨L,hL⟩
  · intro L hL
    change ((OrderDual.ofDual L : NonemptyCompacts X) : Set X) ⊆ ⋂ i, F i
    exact subset_iInter (fun i => hL i.property)

end PointCentralFubini
