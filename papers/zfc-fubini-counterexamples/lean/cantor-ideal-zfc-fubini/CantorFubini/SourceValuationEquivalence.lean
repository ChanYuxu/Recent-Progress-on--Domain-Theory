import CantorFubini.SourceIntegralBridge
import CantorFubini.ValuationDcpo

/-! Full representation equivalence with the source's [0,1]-valued
continuous valuations. Both conversions are defined for every valuation,
are inverse, preserve pointwise order, and preserve the printed real integral.
The final bridges quantify over all source-valued partner valuations. -/

set_option autoImplicit false
open Set Topology TopologicalSpace MeasureTheory
open scoped ENNReal Classical
universe u v

namespace CantorFubini

/-- The printed valuation definition: values in [0,1], strictness, ordinary
real modularity and preservation of every existing nonempty directed LUB. -/
structure UnitValuation (X : Type u) [TopologicalSpace X] where
  mass : Opens X → UnitInterval
  strict : mass ⊥ = unitZero
  modular : ∀ U V, (mass U).val + (mass V).val =
    (mass (U ⊔ V)).val + (mass (U ⊓ V)).val
  continuous : ScottContinuous mass

namespace UnitValuation
variable {X : Type u} [TopologicalSpace X]

instance : CoeFun (UnitValuation X) (fun _ => Opens X → UnitInterval) := ⟨mass⟩

@[ext] theorem ext {μ ν : UnitValuation X} (h : ∀ U, μ U = ν U) : μ = ν := by
  cases μ
  cases ν
  congr
  exact funext h

instance : PartialOrder (UnitValuation X) where
  le μ ν := ∀ U, μ U ≤ ν U
  le_refl μ U := le_rfl
  le_trans μ ν ρ hμν hνρ U := (hμν U).trans (hνρ U)
  le_antisymm μ ν hμν hνμ := ext (fun U => le_antisymm (hμν U) (hνμ U))

def Probability (μ : UnitValuation X) : Prop := μ ⊤ = unitOne

end UnitValuation

theorem unit_ofReal_scottContinuous :
    ScottContinuous (fun x : UnitInterval => ENNReal.ofReal x.val) := by
  intro A hn hd p hp
  have hr := unit_coe_scottContinuous hn hd hp
  constructor
  · rintro b ⟨a, ha, rfl⟩
    exact ENNReal.ofReal_le_ofReal (hp.1 ha)
  · intro b hb
    by_cases hbt : b = ∞
    · simp [hbt]
    · apply (ENNReal.ofReal_le_iff_le_toReal hbt).mpr
      apply hr.2
      rintro r ⟨a, ha, rfl⟩
      exact (ENNReal.ofReal_le_iff_le_toReal hbt).mp (hb (mem_image_of_mem _ ha))

/-- Every source [0,1]-valued valuation yields an actual ENNReal continuous
valuation of total mass at most one. -/
noncomputable def fromUnitValuation {X : Type u} [TopologicalSpace X]
    (μ : UnitValuation X) : SubprobValuation X :=
  ⟨{
    mass := fun U => ENNReal.ofReal (μ U).val
    strict := by
      rw [μ.strict]
      simp [unitZero]
    modular := by
      intro U V
      rw [← ENNReal.ofReal_add (μ U).property.1 (μ V).property.1,
        ← ENNReal.ofReal_add (μ (U ⊔ V)).property.1 (μ (U ⊓ V)).property.1,
        μ.modular U V]
    continuous := μ.continuous.comp unit_ofReal_scottContinuous
  }, by
    change ENNReal.ofReal (μ ⊤).val ≤ 1
    simpa using ENNReal.ofReal_le_ofReal (μ ⊤).property.2⟩

@[simp] theorem fromUnitValuation_apply {X : Type u} [TopologicalSpace X]
    (μ : UnitValuation X) (U : Opens X) :
    (fromUnitValuation μ).val U = ENNReal.ofReal (μ U).val := rfl

/-- Every ENNReal subprobability valuation yields a source-valued valuation,
with the already proved real modularity and full Scott continuity. -/
noncomputable def toUnitValuation {X : Type u} [TopologicalSpace X]
    (μ : SubprobValuation X) : UnitValuation X where
  mass := subprobRealMassUnit μ
  strict := Subtype.ext (subprobRealMass_empty μ)
  modular := subprobRealMass_modular μ
  continuous := subprobRealMassUnit_scottContinuous μ

@[simp] theorem toUnitValuation_apply {X : Type u} [TopologicalSpace X]
    (μ : SubprobValuation X) (U : Opens X) :
    (toUnitValuation μ U).val = (μ.val U).toReal := rfl

@[simp] theorem toUnitValuation_fromUnitValuation {X : Type u} [TopologicalSpace X]
    (μ : UnitValuation X) : toUnitValuation (fromUnitValuation μ) = μ := by
  apply UnitValuation.ext
  intro U
  apply Subtype.ext
  exact ENNReal.toReal_ofReal (μ U).property.1

@[simp] theorem fromUnitValuation_toUnitValuation {X : Type u} [TopologicalSpace X]
    (μ : SubprobValuation X) : fromUnitValuation (toUnitValuation μ) = μ := by
  apply SubprobValuation.ext
  intro U
  exact ENNReal.ofReal_toReal (subprob_mass_ne_top μ U)

theorem fromUnitValuation_probability_iff {X : Type u} [TopologicalSpace X]
    (μ : UnitValuation X) : (fromUnitValuation μ).val.Probability ↔ μ.Probability := by
  constructor
  · intro h
    apply Subtype.ext
    change (μ ⊤).val = 1
    have ht := congrArg ENNReal.toReal h
    change (ENNReal.ofReal (μ ⊤).val).toReal = (1 : ℝ≥0∞).toReal at ht
    simpa only [ENNReal.toReal_ofReal (μ ⊤).property.1, ENNReal.toReal_one] using ht
  · intro h
    change ENNReal.ofReal (μ ⊤).val = 1
    rw [h]
    simp [unitOne]

theorem toUnitValuation_probability_iff {X : Type u} [TopologicalSpace X]
    (μ : SubprobValuation X) : μ.val.Probability ↔ (toUnitValuation μ).Probability := by
  simpa only [fromUnitValuation_toUnitValuation] using
    fromUnitValuation_probability_iff (toUnitValuation μ)

noncomputable def unitValuationEquivSubprob (X : Type u) [TopologicalSpace X] :
    UnitValuation X ≃ SubprobValuation X where
  toFun := fromUnitValuation
  invFun := toUnitValuation
  left_inv := toUnitValuation_fromUnitValuation
  right_inv := fromUnitValuation_toUnitValuation

theorem fromUnitValuation_le_iff {X : Type u} [TopologicalSpace X]
    (μ ν : UnitValuation X) : fromUnitValuation μ ≤ fromUnitValuation ν ↔ μ ≤ ν := by
  constructor
  · intro h U
    exact (ENNReal.ofReal_le_ofReal_iff (ν U).property.1).mp (h U)
  · intro h U
    exact ENNReal.ofReal_le_ofReal (h U)

/-- The representation is also an isomorphism of the actual pointwise orders
used by the valuation DCPO object. -/
noncomputable def unitValuationOrderIsoSubprob (X : Type u) [TopologicalSpace X] :
    UnitValuation X ≃o SubprobValuation X where
  toEquiv := unitValuationEquivSubprob X
  map_rel_iff' := fromUnitValuation_le_iff _ _

/-- The ordinary real strict-level integral printed in the source. Interior
only extends its definition to arbitrary functions; it disappears for LSC f. -/
noncomputable def unitIntegral {X : Type u} [TopologicalSpace X]
    (μ : UnitValuation X) (f : X → ℝ) : ℝ :=
  ∫ a : ℝ in Icc (0 : ℝ) 1,
    (μ ⟨interior {x | a < f x}, isOpen_interior⟩).val

@[simp] theorem sourceIntegral_fromUnitValuation {X : Type u} [TopologicalSpace X]
    (μ : UnitValuation X) (f : X → ℝ) :
    sourceIntegral (fromUnitValuation μ).val f = unitIntegral μ f := by
  unfold sourceIntegral unitIntegral
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro a
  exact ENNReal.toReal_ofReal (μ _).property.1

@[simp] theorem unitIntegral_toUnitValuation {X : Type u} [TopologicalSpace X]
    (μ : SubprobValuation X) (f : X → ℝ) :
    unitIntegral (toUnitValuation μ) f = sourceIntegral μ.val f := rfl

theorem unitIntegral_eq_strictLevels {X : Type u} [TopologicalSpace X]
    (μ : UnitValuation X) (f : X → ℝ) (hf : IsRealLSC f) :
    unitIntegral μ f = ∫ a : ℝ in Icc (0 : ℝ) 1, (μ ⟨{x | a < f x}, hf a⟩).val := by
  unfold unitIntegral
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun a => congrArg
    (fun U : Opens X => (μ U).val) (Opens.ext (hf a).interior_eq))

/-- The source Fubini equation, stated entirely with source-valued
valuations and the ordinary real integral. D and E may have different sizes. -/
def UnitCommute {D : Type u} {E : Type v} [PartialOrder D] [PartialOrder E]
    (μ : UnitValuation (WithScott D)) (ρ : UnitValuation (WithScott E)) : Prop :=
  ∀ h : D × E → UnitInterval, ScottContinuous h →
    unitIntegral ρ (fun y => unitIntegral μ (fun x =>
      (h (WithScott.ofScott x, WithScott.ofScott y)).val)) =
    unitIntegral μ (fun x => unitIntegral ρ (fun y =>
      (h (WithScott.ofScott x, WithScott.ofScott y)).val))

theorem unitCommute_iff_sourceCommute {D : Type u} {E : Type v}
    [PartialOrder D] [PartialOrder E]
    (μ : UnitValuation (WithScott D)) (ρ : UnitValuation (WithScott E)) :
    UnitCommute μ ρ ↔ SourceCommute (fromUnitValuation μ).val (fromUnitValuation ρ).val := by
  unfold UnitCommute SourceCommute
  simp_rw [sourceIntegral_fromUnitValuation]

theorem sourceCommute_iff_unitCommute {D : Type u} {E : Type v}
    [PartialOrder D] [PartialOrder E]
    (μ : SubprobValuation (WithScott D)) (ρ : SubprobValuation (WithScott E)) :
    SourceCommute μ.val ρ.val ↔ UnitCommute (toUnitValuation μ) (toUnitValuation ρ) := by
  rw [unitCommute_iff_sourceCommute,
    fromUnitValuation_toUnitValuation, fromUnitValuation_toUnitValuation]

/-- Centrality quantified over every source [0,1]-valued continuous valuation
on every partner dcpo in the indicated, independent universe. -/
def UnitCentral {D : Type u} [PartialOrder D]
    (μ : UnitValuation (WithScott D)) : Prop :=
  ∀ (E : Type v) [PartialOrder E], IsDcpo E →
    ∀ ρ : UnitValuation (WithScott E), UnitCommute μ ρ

theorem unitCentral_iff_sourceCentral {D : Type u} [PartialOrder D]
    (μ : UnitValuation (WithScott D)) :
    UnitCentral.{u,v} μ ↔ SourceCentral.{u,v} (fromUnitValuation μ).val := by
  constructor
  · intro h
    refine ⟨(fromUnitValuation μ).property, ?_⟩
    intro E instE hE ρ hρ
    have hc := (unitCommute_iff_sourceCommute μ (toUnitValuation ⟨ρ, hρ⟩)).mp
      (h E hE (toUnitValuation ⟨ρ, hρ⟩))
    simpa only [fromUnitValuation_toUnitValuation] using hc
  · intro h E instE hE ρ
    apply (unitCommute_iff_sourceCommute μ ρ).mpr
    exact h.2 E hE (fromUnitValuation ρ).val (fromUnitValuation ρ).property

theorem sourceCentral_iff_unitCentral {D : Type u} [PartialOrder D]
    (μ : SubprobValuation (WithScott D)) :
    SourceCentral.{u,v} μ.val ↔ UnitCentral.{u,v} (toUnitValuation μ) := by
  rw [unitCentral_iff_sourceCentral, fromUnitValuation_toUnitValuation]

end CantorFubini
