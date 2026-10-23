import CHFubini.Foundations
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

/-! Elementary consequences of the actual layer-cake definition. No external
linearity, Fubini, or directed-convergence theorem is installed as an axiom.
Indicator/change-of-variables proofs are adapted from the separately identified
`PointCentralFubini_Lean/PointCentralFubini/Integration.lean`.
-/

set_option autoImplicit false
open Set Topology TopologicalSpace MeasureTheory
open scoped ENNReal
universe u v
namespace CHFubini

theorem IsLSC.comp {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y]
    {g : Y → ℝ≥0∞} (hg : IsLSC g) {f : X → Y} (hf : Continuous f) :
    IsLSC (g ∘ f) := fun r => (hg r).preimage hf

theorem choquetIntegral_mono {X : Type u} [TopologicalSpace X]
    (μ : Valuation X) {f g : X → ℝ≥0∞} (h : f ≤ g) :
    choquetIntegral μ f ≤ choquetIntegral μ g := by
  apply lintegral_mono
  intro t
  apply μ.mono
  apply interior_mono
  exact fun x hx => hx.trans_le (h x)

theorem choquetIntegral_push {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y]
    (μ : Valuation X) (f : X → Y) (hf : Continuous f)
    (g : Y → ℝ≥0∞) (hg : IsLSC g) :
    choquetIntegral (μ.push f hf) g = choquetIntegral μ (g ∘ f) := by
  apply lintegral_congr
  intro t
  change μ (Opens.comap ⟨f,hf⟩ ⟨interior {y | ENNReal.ofReal t < g y}, _⟩) = _
  congr 1
  apply Opens.ext
  change f ⁻¹' interior {y | ENNReal.ofReal t < g y} =
    interior {x | ENNReal.ofReal t < g (f x)}
  rw [(hg _).interior_eq]
  exact ((hg _).preimage hf).interior_eq.symm

noncomputable def indicator {X : Type u} [TopologicalSpace X]
    (U : Opens X) : X → ℝ≥0∞ := by
  classical
  exact fun x => if x ∈ U then 1 else 0

theorem choquetIntegral_indicator {X : Type u} [TopologicalSpace X]
    (μ : Valuation X) (U : Opens X) : choquetIntegral μ (indicator U) = μ U := by
  classical
  have hcut : ∀ t : ℝ,
      (⟨interior {x | ENNReal.ofReal t < indicator U x}, isOpen_interior⟩ : Opens X) =
        if t < 1 then U else ⊥ := by
    intro t
    split_ifs with ht
    · apply Opens.ext
      have he : {x | ENNReal.ofReal t < indicator U x} = (U : Set X) := by
        ext x
        by_cases hx : x ∈ U <;> simp [indicator, hx, ENNReal.ofReal_lt_one, ht]
      simpa only [he] using U.isOpen.interior_eq
    · apply Opens.ext
      have he : {x | ENNReal.ofReal t < indicator U x} = (∅ : Set X) := by
        ext x
        by_cases hx : x ∈ U <;> simp [indicator, hx, ENNReal.ofReal_lt_one, ht]
      simp [he]
  unfold choquetIntegral
  simp_rw [hcut]
  have he : (fun t : ℝ => μ (if t < 1 then U else ⊥)) =
      (Iio (1 : ℝ)).indicator (fun _ => μ U) := by
    funext t
    by_cases ht : t < 1 <;> simp [ht, μ.strict, Set.indicator]
  rw [he, lintegral_indicator measurableSet_Iio, setLIntegral_const]
  rw [Measure.restrict_apply measurableSet_Iio]
  have hi : Iio (1 : ℝ) ∩ Ici (0 : ℝ) = Ico (0 : ℝ) 1 := by
    ext t; simp; tauto
  rw [hi, Real.volume_Ico]
  simp

/-- Canonical sections in the intrinsic Scott topology of the ORDER product. -/
def leftSection {P : Type u} {Q : Type v} [PartialOrder P] [PartialOrder Q]
    (W : ScottOpens (P × Q)) (y : Q) : ScottOpens P := by
  refine ⟨{x | WithScott.toScott (WithScott.ofScott x, y) ∈ W}, ?_⟩
  exact W.isOpen.preimage ((scott_continuous_iff _).mp
    (ScottContinuous.id.prodMk (ScottContinuous.const y)))

def rightSection {P : Type u} {Q : Type v} [PartialOrder P] [PartialOrder Q]
    (W : ScottOpens (P × Q)) (x : P) : ScottOpens Q := by
  refine ⟨{y | WithScott.toScott (x, WithScott.ofScott y) ∈ W}, ?_⟩
  exact W.isOpen.preimage ((scott_continuous_iff _).mp
    ((ScottContinuous.const x).prodMk ScottContinuous.id))

end CHFubini
