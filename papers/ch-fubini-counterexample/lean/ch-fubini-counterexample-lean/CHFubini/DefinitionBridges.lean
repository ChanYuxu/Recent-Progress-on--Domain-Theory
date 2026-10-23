import CHFubini.SourceResults

/-! Explicit representation comparisons. These prevent implementation
carriers or bounded extended-real notation from silently changing the source
set A, its initial segments/tails, or its real [0,1] thresholds.
-/
set_option autoImplicit false
open Set Topology TopologicalSpace MeasureTheory
open scoped ENNReal
universe u
namespace CHFubini

def sourceEquivRange {X : Type u} (a : OmegaOneStage → X) : SourcePoint a ≃ range a where
  toFun x := ⟨x.val,x.mem_range⟩
  invFun x := ⟨x.val,x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem sourceInitial_val_image {X : Type u} (a : OmegaOneStage → X)
    (ha : Function.Injective a) (β : OmegaOneStage) :
    SourcePoint.val '' sourceInitial a β = initialSegment a β := by
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact ⟨sourceIndex x,hx,sourceIndex_spec x⟩
  · rintro ⟨γ,hγ,rfl⟩
    exact ⟨pointAt a γ,by simpa only [sourceInitial,mem_setOf_eq,sourceIndex_pointAt ha],rfl⟩

theorem sourceTail_val_image {X : Type u} (a : OmegaOneStage → X)
    (ha : Function.Injective a) (β : OmegaOneStage) :
    SourcePoint.val '' sourceTail a β = a '' Ici β := by
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact ⟨sourceIndex x,hx,sourceIndex_spec x⟩
  · rintro ⟨γ,hγ,rfl⟩
    exact ⟨pointAt a γ,by simpa only [sourceTail,mem_setOf_eq,sourceIndex_pointAt ha],rfl⟩

theorem sourceBase_val_image {X : Type u} (a : OmegaOneStage → X)
    (ha : Function.Injective a) (O : Set X) (β : OmegaOneStage) :
    SourcePoint.val '' sourceBase a O β = O ∩ (a '' Ici β) := by
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact ⟨hx.1,sourceIndex x,hx.2,sourceIndex_spec x⟩
  · rintro ⟨hy,γ,hγ,rfl⟩
    exact ⟨pointAt a γ,⟨hy,by simpa only [sourceIndex_pointAt ha]⟩,rfl⟩

/-- The source's real unit interval and the implementation's bounded
nonnegative extended reals are order isomorphic; infinity is excluded. -/
noncomputable def realUnitIntervalOrderIso : Icc (0 : ℝ) 1 ≃o Iic (1 : ℝ≥0∞) where
  toFun x := ⟨ENNReal.ofReal x.val,by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal x.property.2⟩
  invFun x := ⟨x.val.toReal,ENNReal.toReal_nonneg,by
    simpa only [ENNReal.toReal_one] using ENNReal.toReal_mono ENNReal.one_ne_top x.property⟩
  left_inv x := Subtype.ext (ENNReal.toReal_ofReal x.property.1)
  right_inv x := Subtype.ext (ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.one_ne_top x.property))
  map_rel_iff' := fun {x y} => ENNReal.ofReal_le_ofReal_iff y.property.1

theorem Valuation.Probability.value_ne_top {X : Type u} [TopologicalSpace X]
    {α : Valuation X} (hα : α.Probability) (U : Opens X) : α U ≠ ∞ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (hα.subprobability.mass_le_one U)

/-- Exact real-threshold translation of source H_r (r≥0). -/
theorem massTest_real_threshold {X : Type u} [TopologicalSpace X]
    (α : Valuation X) (hα : α.Probability) {r : ℝ} (hr : 0 ≤ r) (V : Opens X) :
    WithScott.toScott V ∈ massTest α (ENNReal.ofReal r) ↔ r < (α V).toReal :=
  ENNReal.ofReal_lt_iff_lt_toReal hr (hα.value_ne_top V)

theorem paper_profiles_bounded (hCH : CH) (ε : ℝ) (hε : 0 < ε) :
    (∀ V : PaperL hCH, paperMu hCH (leftSection (paperW hCH) V) ≤ 1) ∧
    (∀ C : PaperP hCH, paperRho hCH ε hε (rightSection (paperW hCH) C) ≤ 1) :=
  ⟨fun _ => (paperMu_probability hCH).subprobability.mass_le_one _,
    fun _ => (paperRho_probability hCH ε hε).subprobability.mass_le_one _⟩

/-- Question 7.1, a statement only. No ZFC answer is asserted. -/
def UnconditionalCounterexampleQuestion : Prop :=
  ∀ ε : ℝ, 0 < ε → ε < 1 → CounterexampleAt ε

/-- The property asked about in Question 7.3, not a classification theorem. -/
def AllSubprobabilityValuationsCentral (P : Type u) [PartialOrder P] : Prop :=
  ∀ μ : DValuation P, μ.Subprobability → Central.{u,u} μ

end CHFubini
