import PointCentralFubini.CompactOrderedMeasure

/-! Inner regularity concentrates the extension on an upward embedded image,
without assuming that the image is measurable. -/
set_option autoImplicit false
open Set Topology TopologicalSpace MeasureTheory
universe u v
namespace PointCentralFubini

theorem isCompact_downward_hull {E : Type u} [TopologicalSpace E] [PartialOrder E]
    [CompactSpace E] [OrderClosedTopology E] {C : Set E} (hC : IsCompact C) :
    IsCompact {x : E | ∃ y ∈ C, x ≤ y} := by
  letI : CompactSpace C := isCompact_iff_compactSpace.mp hC
  let R : Set (E × C) := {p | p.1 ≤ p.2.val}
  have hR : IsClosed R := isClosed_le continuous_fst
    (continuous_subtype_val.comp continuous_snd)
  have heq : Prod.fst '' R = {x : E | ∃ y ∈ C, x ≤ y} := by
    ext x
    constructor
    · rintro ⟨⟨z,y⟩,hzy,rfl⟩
      exact ⟨y.val,y.property,hzy⟩
    · rintro ⟨y,hy,hxy⟩
      exact ⟨(x,⟨y,hy⟩),hxy,rfl⟩
  exact heq ▸ hR.isCompact.image continuous_fst

theorem radon_complement_range_null {X : Type u} {E : Type v}
    [TopologicalSpace X] [TopologicalSpace E] [PartialOrder E]
    [CompactSpace E] [OrderClosedTopology E]
    (f : X → E) (hf : @Continuous X E inferInstance (upwardTopology E) f)
    (μ : Valuation X) (hupper : IsUpperSet (range f)) (M : FiniteRadonMeasure E)
    (hM : ∀ U : @Opens E (upwardTopology E),
      M.measure (U : Set E) = (@Valuation.push X inferInstance E (upwardTopology E) μ f hf) U) :
    ∀ B : Set E, MeasurableSet[borel E] B → B ⊆ (range f)ᶜ → M.measure B = 0 := by
  letI : MeasurableSpace E := borel E
  letI : BorelSpace E := ⟨rfl⟩
  letI : Measure.InnerRegular M.measure := M.innerRegular
  have htotal : M.measure univ = μ ⊤ := hM ⊤
  have hcompact : ∀ C : Set E, IsCompact C → C ⊆ (range f)ᶜ → M.measure C = 0 := by
    intro C hC hCA
    let D : Set E := {x | ∃ y ∈ C, x ≤ y}
    have hD : IsClosed D := (isCompact_downward_hull hC).isClosed
    have hDup : IsUpperSet Dᶜ := by
      intro x z hxz hx hz
      obtain ⟨y,hy,hzy⟩ := hz
      exact hx ⟨y,hy,hxz.trans hzy⟩
    let U : @Opens E (upwardTopology E) := by
      letI : TopologicalSpace E := upwardTopology E
      exact ⟨Dᶜ,hD.isOpen_compl,hDup⟩
    have hmass : (@Valuation.push X inferInstance E (upwardTopology E) μ f hf) U = μ ⊤ := by
      apply congrArg μ
      ext x
      constructor
      · intro _; trivial
      · intro _ hx
        obtain ⟨y,hy,hxy⟩ := hx
        exact hCA hy (hupper hxy (mem_range_self x))
    have hU : M.measure (U : Set E) = M.measure univ := by
      rw [hM U,hmass,htotal]
    have hnull : M.measure D = 0 := by
      have hz := measure_compl (μ := M.measure) hD.isOpen_compl.measurableSet
        (ne_top_of_le_ne_top M.finite (measure_mono (subset_univ _)))
      change M.measure Dᶜᶜ = M.measure univ - M.measure (U : Set E) at hz
      simpa only [compl_compl,hU,tsub_self] using hz
    apply le_antisymm _ (zero_le _)
    calc
      M.measure C ≤ M.measure D := measure_mono (fun x hx => ⟨x,hx,le_rfl⟩)
      _ = 0 := hnull
  intro B hB hBA
  rw [hB.measure_eq_iSup_isCompact M.measure]
  apply le_antisymm _ (zero_le _)
  apply iSup_le; intro C
  apply iSup_le; intro hCB
  apply iSup_le; intro hC
  exact (hcompact C hC (hCB.trans hBA)).le

end PointCentralFubini
