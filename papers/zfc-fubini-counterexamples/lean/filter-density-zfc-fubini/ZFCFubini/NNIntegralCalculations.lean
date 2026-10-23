import ZFCFubini.Evaluation

/-!
An explicit encoding bridge from the manuscript's bounded real strict-level
integral to the existing Foundations.choquetIntegral. Both definitions retain
their actual domains of integration, [0,1] and [0,infinity), respectively;
the extra nonnegative tail is proved zero. No older CH theorem or local proof
module is imported or reused. This implementation is new.
-/

set_option autoImplicit false
open Set TopologicalSpace MeasureTheory Topology
open scoped ENNReal Classical
universe u v

namespace ZFCFubini

/-- `ofReal` preserves every existing directed supremum of real numbers.
The finite-upper-bound case is transferred through the actual `toReal` map. -/
theorem ofReal_scottContinuous : ScottContinuous ENNReal.ofReal := by
  intro A hn hd a ha
  constructor
  · rintro b ⟨x, hx, rfl⟩
    exact ENNReal.ofReal_le_ofReal (ha.1 hx)
  · intro b hb
    by_cases hbtop : b = ∞
    · rw [hbtop]; exact le_top
    · apply (ENNReal.ofReal_le_iff_le_toReal hbtop).mpr
      apply ha.2
      intro x hx
      exact (ENNReal.ofReal_le_iff_le_toReal hbtop).mp
        (hb (Set.mem_image_of_mem ENNReal.ofReal hx))

/-- Equality of the actual totalized strict-level definitions for a real
function bounded above by one. In particular it applies to every source
[0,1]-valued LSC function. No equivalence between integrals is assumed.
The theorem is slightly more general because both totalizations use interiors. -/
theorem choquetIntegral_ofReal_eq_paperIntegral
    {X : Type u} [TopologicalSpace X] (μ : ProbabilityValuation X) (f : X → ℝ)
    (hf1 : ∀ x, f x ≤ 1) :
    choquetIntegral μ.val (fun x => ENNReal.ofReal (f x)) =
      ENNReal.ofReal (paperIntegral μ f) := by
  classical
  let g : ℝ → ℝ≥0∞ := fun a => μ.val
    ⟨interior {x | ENNReal.ofReal a < ENNReal.ofReal (f x)}, isOpen_interior⟩
  have hlevel (a : ℝ) (ha : 0 ≤ a) :
      (⟨interior {x | ENNReal.ofReal a < ENNReal.ofReal (f x)}, isOpen_interior⟩ : Opens X) =
        ⟨interior {x | a < f x}, isOpen_interior⟩ := by
    have hSet : {x | ENNReal.ofReal a < ENNReal.ofReal (f x)} = {x | a < f x} :=
      Set.ext (fun x => ENNReal.ofReal_lt_ofReal_iff_of_nonneg ha)
    exact Opens.ext (congrArg interior hSet)
  have hprofile (a : ℝ) (ha : 0 ≤ a) : g a = ENNReal.ofReal (levelMass μ f a) := by
    change μ.val _ = ENNReal.ofReal ((μ.val _).toReal)
    rw [hlevel a ha]
    exact (ENNReal.ofReal_toReal (probability_mass_ne_top μ _)).symm
  have htail (a : ℝ) (ha : 1 < a) : g a = 0 := by
    have hSet : {x | ENNReal.ofReal a < ENNReal.ofReal (f x)} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      have hax : a < f x := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by linarith)).mp hx
      exact (not_lt_of_ge (hf1 x)) (ha.trans hax)
    have hOpen : (⟨interior {x | ENNReal.ofReal a < ENNReal.ofReal (f x)},
        isOpen_interior⟩ : Opens X) = ⊥ := by
      apply Opens.ext
      simp only [hSet, interior_empty, Opens.coe_bot]
      rfl
    change μ.val _ = 0
    rw [hOpen]
    exact μ.val.strict
  have hIndicator : (Set.Ici (0 : ℝ)).indicator g = (Set.Icc (0 : ℝ) 1).indicator g := by
    funext a
    by_cases ha0 : 0 ≤ a
    · by_cases ha1 : a ≤ 1
      · simp only [Set.indicator, Set.mem_Ici, Set.mem_Icc, ha0, ha1, and_self]
      · have hga : g a = 0 := htail a (lt_of_not_ge ha1)
        simp [Set.indicator, ha0, ha1, hga]
    · simp [Set.indicator, ha0]
  change (∫⁻ a : ℝ in Set.Ici (0 : ℝ), g a) =
    ENNReal.ofReal (∫ a : ℝ in Set.Icc (0 : ℝ) 1, levelMass μ f a)
  calc
    _ = ∫⁻ a : ℝ in Set.Icc (0 : ℝ) 1, g a := by
      rw [← lintegral_indicator measurableSet_Ici, ← lintegral_indicator measurableSet_Icc,
        hIndicator]
    _ = ∫⁻ a : ℝ in Set.Icc (0 : ℝ) 1, ENNReal.ofReal (levelMass μ f a) :=
      setLIntegral_congr_fun measurableSet_Icc (fun a ha => hprofile a ha.1)
    _ = ENNReal.ofReal (∫ a : ℝ in Set.Icc (0 : ℝ) 1, levelMass μ f a) :=
      (ofReal_integral_eq_lintegral_ofReal (levelMass_integrable μ f)
        (Filter.Eventually.of_forall (fun a => ENNReal.toReal_nonneg))).symm

/-- The same specified incidence function, now in the nonnegative encoding
used by Foundations.Commute, not a new integrand or a replacement predicate. -/
noncomputable def nnIncidence (P : Type u) [PartialOrder P]
    (z : P × ScottOpens P) : ℝ≥0∞ := ENNReal.ofReal (incidence P z).val

theorem nnIncidence_scottContinuous (P : Type u) [PartialOrder P] :
    ScottContinuous (nnIncidence P) :=
  ((incidence_scottContinuous P).comp unit_coe_scottContinuous).comp ofReal_scottContinuous

theorem nnIncidence_le_one (P : Type u) [PartialOrder P] (z : P × ScottOpens P) :
    nnIncidence P z ≤ 1 := by
  simpa only [nnIncidence, ENNReal.ofReal_one] using
    ENNReal.ofReal_le_ofReal (incidence P z).property.2

@[simp] theorem nnIncidence_toReal (P : Type u) [PartialOrder P] (z : P × ScottOpens P) :
    (nnIncidence P z).toReal = (incidence P z).val :=
  ENNReal.toReal_ofReal (incidence P z).property.1

@[simp] theorem nnIncidence_value (P : Type u) [PartialOrder P]
    (p : P) (H : ScottOpens P) :
    nnIncidence P (p, H) = if WithScott.toScott p ∈ H then 1 else 0 := by
  classical
  rw [nnIncidence, incidence_value]
  split <;> simp

end ZFCFubini
