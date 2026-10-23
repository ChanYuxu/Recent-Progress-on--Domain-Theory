import CHFubini.Foundations
import Mathlib.Topology.Compactness.Compact
import Mathlib.Order.Zorn

/-!
Full Rudin/Zorn proof that the source's sober spaces are well-filtered.
This file imports the actual project definition of saturation/well-filteredness;
it introduces no mathematical axioms and stores no target conclusions in data.
-/

set_option autoImplicit false

open Set Topology TopologicalSpace

universe u

namespace CHFubini

def MeetsFamily {X : Type u} (F : Set X) (K : Set (Set X)) : Prop :=
  ∀ C ∈ K, (C ∩ F).Nonempty

/-- Compactness gives a lower bound for every nonempty chain of closed
sets meeting each compact member of an arbitrary family. -/
theorem exists_minimal_closed_meeting_compacts {X : Type u} [TopologicalSpace X]
    (K : Set (Set X)) (hcompact : ∀ C ∈ K, IsCompact C)
    (F₀ : Set X) (hF₀closed : IsClosed F₀) (hF₀meet : MeetsFamily F₀ K) :
    ∃ F : Set X, IsClosed F ∧ F ⊆ F₀ ∧ MeetsFamily F K ∧
      ∀ G : Set X, IsClosed G → G ⊆ F → MeetsFamily G K → F ⊆ G := by
  classical
  let S : Set (Set X) := {F | IsClosed F ∧ F ⊆ F₀ ∧ MeetsFamily F K}
  have hchain : ∀ c ⊆ S, IsChain (· ⊆ ·) c → c.Nonempty →
      ∃ lb ∈ S, ∀ F ∈ c, lb ⊆ F := by
    intro c hcS hc hcn
    letI : Nonempty c := hcn.to_subtype
    have hclosed : IsClosed (⋂₀ c) := isClosed_sInter (fun F hF => (hcS hF).1)
    have hsub : ⋂₀ c ⊆ F₀ := by
      obtain ⟨F, hF⟩ := hcn
      exact (sInter_subset_of_mem hF).trans (hcS hF).2.1
    have hmeet : MeetsFamily (⋂₀ c) K := by
      intro C hCK
      have hdir : Directed (· ⊇ ·) (fun F : c => F.val) := by
        intro F G
        rcases hc.total F.property G.property with hFG | hGF
        · exact ⟨F, Subset.rfl, hFG⟩
        · exact ⟨G, hGF, Subset.rfl⟩
      have hne : (C ∩ ⋂ F : c, F.val).Nonempty := by
        by_contra hno
        obtain ⟨F, hFempty⟩ := (hcompact C hCK).elim_directed_family_closed
          (fun F : c => F.val) (fun F => (hcS F.property).1)
          (Set.not_nonempty_iff_eq_empty.mp hno) hdir
        exact ((hcS F.property).2.2 C hCK).ne_empty hFempty
      simpa only [sInter_eq_iInter] using hne
    exact ⟨⋂₀ c, ⟨hclosed, hsub, hmeet⟩, fun F hF => sInter_subset_of_mem hF⟩
  obtain ⟨F, _, hFmin⟩ := zorn_superset_nonempty S hchain F₀
    ⟨hF₀closed, Subset.rfl, hF₀meet⟩
  refine ⟨F, hFmin.1.1, hFmin.1.2.1, hFmin.1.2.2, ?_⟩
  intro G hGclosed hGF hGmeet
  exact hFmin.2 ⟨hGclosed, hGF.trans hFmin.1.2.1, hGmeet⟩ hGF

/-- Rudin's irreducibility step: minimality is the conclusion of the Zorn
construction above, not an assumed irreducibility package. -/
theorem minimal_closed_meeting_filtered_irreducible {X : Type u} [TopologicalSpace X]
    (K : Set (Set X)) (hKn : K.Nonempty)
    (hKd : DirectedOn (fun C D : Set X => D ⊆ C) K)
    (F : Set X) (hFclosed : IsClosed F) (hFmeet : MeetsFamily F K)
    (hFmin : ∀ G : Set X, IsClosed G → G ⊆ F → MeetsFamily G K → F ⊆ G) :
    IsIrreducible F := by
  classical
  constructor
  · obtain ⟨C, hCK⟩ := hKn
    exact (hFmeet C hCK).mono inter_subset_right
  · rw [isPreirreducible_iff_isClosed_union_isClosed]
    intro Z₁ Z₂ hZ₁ hZ₂ hcover
    by_contra hno
    push Not at hno
    have hnot₁ : ¬ MeetsFamily (F ∩ Z₁) K := by
      intro hmeet₁
      exact hno.1 ((hFmin (F ∩ Z₁) (hFclosed.inter hZ₁) inter_subset_left hmeet₁).trans
        inter_subset_right)
    have hnot₂ : ¬ MeetsFamily (F ∩ Z₂) K := by
      intro hmeet₂
      exact hno.2 ((hFmin (F ∩ Z₂) (hFclosed.inter hZ₂) inter_subset_left hmeet₂).trans
        inter_subset_right)
    obtain ⟨C₁, hC₁K, hC₁⟩ : ∃ C ∈ K, ¬ (C ∩ (F ∩ Z₁)).Nonempty := by
      simpa only [MeetsFamily, not_forall, Classical.not_imp, exists_prop] using hnot₁
    obtain ⟨C₂, hC₂K, hC₂⟩ : ∃ C ∈ K, ¬ (C ∩ (F ∩ Z₂)).Nonempty := by
      simpa only [MeetsFamily, not_forall, Classical.not_imp, exists_prop] using hnot₂
    obtain ⟨C, hCK, hCC₁, hCC₂⟩ := hKd C₁ hC₁K C₂ hC₂K
    obtain ⟨x, hxC, hxF⟩ := hFmeet C hCK
    rcases hcover hxF with hxZ₁ | hxZ₂
    · exact hC₁ ⟨x, hCC₁ hxC, hxF, hxZ₁⟩
    · exact hC₂ ⟨x, hCC₂ hxC, hxF, hxZ₂⟩

/-- A saturated set containing a specialization of x contains x. This uses
exactly the source definition as an intersection of open supersets. -/
theorem saturated_mem_of_mem_closure_singleton {X : Type u} [TopologicalSpace X]
    (K : Set X) (hK : CHFubini.IsSaturated K) {x y : X}
    (hyK : y ∈ K) (hyx : y ∈ closure ({x} : Set X)) : x ∈ K := by
  rw [hK]
  apply mem_sInter.mpr
  intro U hU
  exact (specializes_iff_mem_closure.mpr hyx).mem_open hU.1 (hU.2 hyK)

/-- The filtered-compact open-test property of any quasi-sober space. T0 is
not needed for this implication; it is packaged separately in the exact
source-facing well-filteredness predicate below. -/
theorem quasiSober_filtered_compact_open_test {X : Type u} [TopologicalSpace X]
    [QuasiSober X] (K : Set (Set X)) (hKn : K.Nonempty)
    (hK : ∀ C ∈ K, C.Nonempty ∧ IsCompact C ∧ CHFubini.IsSaturated C)
    (hKd : DirectedOn (fun C D : Set X => D ⊆ C) K)
    (U : Set X) (hU : IsOpen U) (hinter : ⋂₀ K ⊆ U) :
    ∃ C ∈ K, C ⊆ U := by
  classical
  by_contra hno
  have hnot : ∀ C ∈ K, ¬ C ⊆ U := by
    intro C hCK hCU
    exact hno ⟨C, hCK, hCU⟩
  have hmeet₀ : MeetsFamily Uᶜ K := by
    intro C hCK
    exact inter_compl_nonempty_iff.mpr (hnot C hCK)
  obtain ⟨F, hFclosed, hFU, hFmeet, hFmin⟩ := exists_minimal_closed_meeting_compacts K
    (fun C hCK => (hK C hCK).2.1) Uᶜ hU.isClosed_compl hmeet₀
  have hFirr := minimal_closed_meeting_filtered_irreducible K hKn hKd F hFclosed hFmeet hFmin
  obtain ⟨x, hxgeneric⟩ := QuasiSober.sober hFirr hFclosed
  have hxU : x ∉ U := hFU hxgeneric.mem
  have hxinter : x ∈ ⋂₀ K := by
    apply mem_sInter.mpr
    intro C hCK
    obtain ⟨y, hyC, hyF⟩ := hFmeet C hCK
    apply saturated_mem_of_mem_closure_singleton C (hK C hCK).2.2 hyC
    rw [hxgeneric.def]
    exact hyF
  exact hxU (hinter hxinter)

/-- Source assertion "Every sober space is well-filtered", using the actual
`CHFubini.IsSober` and `CHFubini.IsWellFiltered` definitions. -/
theorem sober_isWellFiltered {X : Type u} [TopologicalSpace X]
    (hX : CHFubini.IsSober X) : CHFubini.IsWellFiltered X := by
  letI : QuasiSober X := hX.2
  exact ⟨hX.1, quasiSober_filtered_compact_open_test⟩

end CHFubini

