import ZFCFubini.SubprobIntegralBridge

/-!
An explicit two-way representation theorem between real [0,1]-valued
continuous subprobability valuations and the ENNReal bounded-mass encoding.
No class of source partners is lost by the latter encoding. Scott continuity
here means preservation of all existing nonempty directed suprema, not only
sequences. Monotonicity is derived from that condition on the lattice of opens.
-/

set_option autoImplicit false
open Set Topology TopologicalSpace
open scoped ENNReal
universe u

namespace ZFCFubini

structure RealSubprobValuation (X : Type u) [TopologicalSpace X] where
  mass : Opens X → ℝ
  range : ∀ U, mass U ∈ Icc (0 : ℝ) 1
  strict : mass ⊥ = 0
  modular : ∀ U V, mass U + mass V = mass (U ⊔ V) + mass (U ⊓ V)
  continuous : ScottContinuous mass

namespace RealSubprobValuation

variable {X : Type u} [TopologicalSpace X]

@[ext] theorem ext {μ ν : RealSubprobValuation X} (h : ∀ U, μ.mass U = ν.mass U) : μ = ν := by
  cases μ; cases ν; congr; exact funext h

theorem mono (μ : RealSubprobValuation X) : Monotone μ.mass := μ.continuous.monotone

noncomputable def ofENN (μ : SubprobValuation X) : RealSubprobValuation X where
  mass := subprobRealMass μ
  range := subprobRealMass_mem_unit μ
  strict := subprobRealMass_empty μ
  modular := subprobRealMass_modular μ
  continuous := subprobRealMass_scottContinuous μ

noncomputable def toENNValuation (μ : RealSubprobValuation X) : Valuation X where
  mass U := ENNReal.ofReal (μ.mass U)
  strict := by rw [μ.strict, ENNReal.ofReal_zero]
  modular U V := by
    rw [← ENNReal.ofReal_add (μ.range U).1 (μ.range V).1,
      ← ENNReal.ofReal_add (μ.range (U ⊔ V)).1 (μ.range (U ⊓ V)).1,
      μ.modular]
  continuous := μ.continuous.comp ofReal_scottContinuous

noncomputable def toENN (μ : RealSubprobValuation X) : SubprobValuation X :=
  ⟨μ.toENNValuation, by
    change ENNReal.ofReal (μ.mass ⊤) ≤ 1
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal (μ.range ⊤).2⟩

@[simp] theorem toENN_apply (μ : RealSubprobValuation X) (U : Opens X) :
    μ.toENN.val U = ENNReal.ofReal (μ.mass U) := rfl

@[simp] theorem ofENN_apply (μ : SubprobValuation X) (U : Opens X) :
    (ofENN μ).mass U = (μ.val U).toReal := rfl

@[simp] theorem toENN_ofENN (μ : SubprobValuation X) : (ofENN μ).toENN = μ := by
  apply Subtype.ext
  apply Valuation.ext
  intro U
  exact ENNReal.ofReal_toReal (subprob_mass_ne_top μ U)

@[simp] theorem ofENN_toENN (μ : RealSubprobValuation X) : ofENN μ.toENN = μ := by
  apply ext
  intro U
  exact ENNReal.toReal_ofReal (μ.range U).1

/-- A genuine bijective encoding, with both inverse identities proved. -/
noncomputable def ennEquiv : RealSubprobValuation X ≃ SubprobValuation X where
  toFun := toENN
  invFun := ofENN
  left_inv := ofENN_toENN
  right_inv := toENN_ofENN

/-- Literal REAL strict-level integral of the real-valued source data. -/
noncomputable def integral (μ : RealSubprobValuation X) (f : X → ℝ) : ℝ :=
  ∫ a : ℝ in Icc (0 : ℝ) 1, μ.mass ⟨interior {x | a < f x}, isOpen_interior⟩

theorem levelMass_toENN (μ : RealSubprobValuation X) (f : X → ℝ) :
    subprobLevelMass μ.toENN f =
      fun a => μ.mass ⟨interior {x | a < f x}, isOpen_interior⟩ := by
  funext a
  exact ENNReal.toReal_ofReal (μ.range _).1

theorem integral_levels_integrable (μ : RealSubprobValuation X) (f : X → ℝ) :
    MeasureTheory.IntegrableOn
      (fun a => μ.mass ⟨interior {x | a < f x}, isOpen_interior⟩) (Icc (0 : ℝ) 1) := by
  rw [← levelMass_toENN]
  exact subprobLevelMass_integrable μ.toENN f

theorem integral_eq_subprobPaperIntegral (μ : RealSubprobValuation X) (f : X → ℝ) :
    μ.integral f = subprobPaperIntegral μ.toENN f := by
  simp only [integral, subprobPaperIntegral, levelMass_toENN]

theorem integral_eq_strictLevels (μ : RealSubprobValuation X) (f : X → ℝ)
    (hf : IsRealLSC f) :
    μ.integral f = ∫ a : ℝ in Icc (0 : ℝ) 1, μ.mass ⟨{x | a < f x}, hf a⟩ := by
  unfold integral
  apply MeasureTheory.integral_congr_ae
  exact Filter.Eventually.of_forall (fun a => congrArg μ.mass (Opens.ext (hf a).interior_eq))

end RealSubprobValuation
end ZFCFubini
