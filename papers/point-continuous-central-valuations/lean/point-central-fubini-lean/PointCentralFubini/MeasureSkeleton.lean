import PointCentralFubini.SourceStatements
import Mathlib.Topology.Bases
import Mathlib.Order.CompleteLattice.Finset

/-! Same-mass open subsets and countable inner skeletons for tau-smooth measures. -/
set_option autoImplicit false
open Set Topology TopologicalSpace MeasureTheory
open scoped ENNReal
universe u
namespace PointCentralFubini

namespace TauMeasure
variable {X : Type u} [t : TopologicalSpace X]

theorem null_diff_of_same_mass (m : TauMeasure X) {U V : Set X}
    (hVU : V ⊆ U) (hV : MeasurableSet[borel X] V) (hm : m.measure U = m.measure V) :
    m.measure (U \ V) = 0 := by
  letI : MeasurableSpace X := borel X
  rw [measure_diff hVU hV.nullMeasurableSet
    (ne_top_of_le_ne_top m.finite (measure_mono (subset_univ V))),hm,tsub_self]

/-- Tau-smoothness promotes same-mass refinements of subbasic opens to all opens.
The union step uses directed finite unions; no uncountable union of null sets
is asserted to be null. -/
theorem same_mass_open_of_generated (m : TauMeasure X)
    (t₀ : TopologicalSpace X) (hcoarse : t ≤ t₀) (S : Set (Set X))
    (ht : t = generateFrom S)
    (hS : ∀ U ∈ S, ∃ V, IsOpen[t₀] V ∧ V ⊆ U ∧
      @TauMeasure.measure X t m U = @TauMeasure.measure X t m V) :
    ∀ U : Set X, IsOpen[t] U → ∃ V, IsOpen[t₀] V ∧ V ⊆ U ∧
      @TauMeasure.measure X t m U = @TauMeasure.measure X t m V := by
  classical
  letI : TopologicalSpace X := t
  letI : MeasurableSpace X := borel X
  letI : BorelSpace X := ⟨rfl⟩
  have ho : ∀ U, GenerateOpen S U → IsOpen[t] U :=
    fun _ hU => ht.symm ▸ hU
  intro U hU
  have hg : GenerateOpen S U := by rwa [ht] at hU
  clear hU
  induction hg with
  | basic U hU => exact hS U hU
  | univ => exact ⟨univ,@isOpen_univ X t₀,Subset.rfl,rfl⟩
  | inter U W hU hW ihU ihW =>
    obtain ⟨V,hV,hVU,hUV⟩ := ihU
    obtain ⟨Z,hZ,hZW,hWZ⟩ := ihW
    have hnU := m.null_diff_of_same_mass hVU ((hcoarse V hV).measurableSet) hUV
    have hnW := m.null_diff_of_same_mass hZW ((hcoarse Z hZ).measurableSet) hWZ
    refine ⟨V ∩ Z,@IsOpen.inter X t₀ V Z hV hZ,inter_subset_inter hVU hZW,?_⟩
    symm
    apply measure_eq_measure_of_null_diff (inter_subset_inter hVU hZW)
    apply measure_mono_null (t := (U \ V) ∪ (W \ Z))
    · intro x hx
      by_cases hxV : x ∈ V
      · exact Or.inr ⟨hx.1.2,fun hxZ => hx.2 ⟨hxV,hxZ⟩⟩
      · exact Or.inl ⟨hx.1.1,hxV⟩
    · exact measure_union_null hnU hnW
  | sUnion A hA ih =>
    choose V hV hVA hmass using (fun B : A => ih B.val B.property)
    let W : Set X := ⋃ B : A, V B
    have hW : IsOpen[t₀] W := by
      letI : TopologicalSpace X := t₀
      exact isOpen_iUnion hV
    have hWU : W ⊆ ⋃₀ A := by
      intro x hx
      obtain ⟨B,hxB⟩ := mem_iUnion.mp hx
      exact mem_sUnion.mpr ⟨B.val,B.property,hVA B hxB⟩
    refine ⟨W,hW,hWU,le_antisymm ?_ (measure_mono hWU)⟩
    let G : A → Opens X := fun B => ⟨B.val,ho _ (hA _ B.property)⟩
    let F : Finset A → Opens X := fun s => s.sup G
    have hFmono : Monotone F := fun s r hsr => Finset.sup_mono hsr
    have hsup : (⨆ s, F s : Opens X) = ⟨⋃₀ A,ho _ (.sUnion _ hA)⟩ := by
      rw [show (⨆ s, F s) = ⨆ B, G B by
        simp only [F,Finset.sup_eq_iSup,← iSup_eq_iSup_finset]]
      ext x; simp [G]
    change m.toValuation ⟨⋃₀ A,ho _ (.sUnion _ hA)⟩ ≤ m.measure W
    rw [← hsup,m.toValuation.map_iSup F hFmono.directed_le]
    apply iSup_le
    intro s
    have hn : m.measure ((F s : Opens X) \ W) = 0 := by
      apply measure_mono_null (t := ⋃ B ∈ s, (B.val \ V B))
      · intro x hx
        have hxF : x ∈ (s.sup G : Opens X) := hx.1
        rw [Finset.sup_eq_iSup] at hxF
        obtain ⟨B,hxB⟩ := Opens.mem_iSup.mp hxF
        obtain ⟨hB,hxB⟩ := Opens.mem_iSup.mp hxB
        exact mem_iUnion₂.mpr ⟨B,hB,hxB,fun hxV => hx.2 (mem_iUnion.mpr ⟨B,hxV⟩)⟩
      · apply (measure_biUnion_null_iff s.countable_toSet).mpr
        intro B _
        exact m.null_diff_of_same_mass (hVA B) ((hcoarse _ (hV B)).measurableSet) (hmass B)
    calc
      m.toValuation (F s) ≤ m.measure (W ∪ ((F s : Opens X) \ W)) :=
        measure_mono (by intro x hx; by_cases hxW : x ∈ W <;> simp [hxW,hx])
      _ ≤ m.measure W + m.measure ((F s : Opens X) \ W) := measure_union_le _ _
      _ = m.measure W := by rw [hn,add_zero]

/-- A coarser second-countable topology with same-mass open refinements supplies
the exact inner-approximation family required in source equation (4.2). -/
theorem innerSkeleton_of_coarser (m : TauMeasure X) (t₀ : TopologicalSpace X)
    (hcoarse : t ≤ t₀) (hsecond : @SecondCountableTopology X t₀)
    (hrefine : ∀ U : @Opens X t, ∃ V : Set X, IsOpen[t₀] V ∧ V ⊆ U ∧
      @TauMeasure.measure X t m (U : Set X) = @TauMeasure.measure X t m V) :
    ∃ C : Set (@Opens X t), @InnerSkeleton X t m C := by
  classical
  letI : TopologicalSpace X := t
  let B := @countableBasis X t₀ hsecond
  have hB : @IsTopologicalBasis X t₀ B := @isBasis_countableBasis X t₀ hsecond
  have hBc : B.Countable := @countable_countableBasis X t₀ hsecond
  letI : Countable B := hBc.to_subtype
  let G : B → Opens X := fun b => ⟨b.val,hcoarse _ (@IsTopologicalBasis.isOpen X t₀ b.val B hB b.property)⟩
  let F : Finset B → Opens X := fun s => s.sup G
  refine ⟨range F,countable_range F,?_⟩
  intro U
  apply le_antisymm
  · obtain ⟨V,hV,hVU,hUV⟩ := hrefine U
    let A : Set B := {b | b.val ⊆ V}
    let H : Finset A → Opens X := fun s => s.sup (fun b => G b.val)
    have hHmono : Monotone H := fun s r hsr => Finset.sup_mono hsr
    have hVeq : ((⨆ s, H s : Opens X) : Set X) = V := by
      rw [show (⨆ s, H s) = ⨆ b : A, G b.val by
        simp only [H,Finset.sup_eq_iSup,← iSup_eq_iSup_finset]]
      ext x
      constructor
      · intro hx
        obtain ⟨b,hxb⟩ := Opens.mem_iSup.mp hx
        exact b.property hxb
      · intro hx
        obtain ⟨b,hb,hxb,hbV⟩ := @IsTopologicalBasis.exists_subset_of_mem_open X t₀ B hB x V hx hV
        exact Opens.mem_iSup.mpr ⟨⟨⟨b,hb⟩,hbV⟩,hxb⟩
    rw [hUV,← hVeq]
    change m.toValuation (⨆ s, H s) ≤ _
    rw [m.toValuation.map_iSup H hHmono.directed_le]
    apply iSup_le; intro s
    have himage : H s = F (s.image Subtype.val) := by
      simp only [H,F,Finset.sup_image,Function.comp_def]
    have hHU : H s ≤ U := by
      intro x hx
      apply hVU
      rw [← hVeq]
      exact (le_iSup H s) hx
    exact le_iSup_of_le (H s) (le_iSup_of_le ⟨_,himage.symm⟩
      (le_iSup_of_le hHU le_rfl))
  · apply iSup_le; intro V
    apply iSup_le; intro _
    apply iSup_le; intro hVU
    exact measure_mono hVU
end TauMeasure

end PointCentralFubini
