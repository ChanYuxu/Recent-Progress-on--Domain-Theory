import ZFCFubini.TopologicalFubiniProduct

/-! Topological valuation Fubini, proved from genuine integration laws and
finite open rectangles. The topology here is the ordinary product topology.
No valuation is assumed to extend to a Borel measure. -/

set_option autoImplicit false
open Set Topology TopologicalSpace MeasureTheory
open scoped ENNReal NNReal Classical
universe u v w
namespace ZFCFubini
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

noncomputable def topologicalExpectation (μ : Valuation X) (ν : Valuation Y)
    (f : X × Y → ℝ≥0∞) : ℝ≥0∞ :=
  choquetIntegral μ (fun x => choquetIntegral ν (fun y => f (x, y)))

theorem topologicalExpectation_add (μ : Valuation X) (hμ : μ.Subprobability)
    (ν : Valuation Y) (hν : ν.Subprobability) {f g : X × Y → ℝ≥0∞}
    (hf : IsLSC f) (hg : IsLSC g) :
    topologicalExpectation μ ν (f + g) = topologicalExpectation μ ν f +
      topologicalExpectation μ ν g := by
  have he : (fun x => choquetIntegral ν (fun y => (f + g) (x, y))) =
      (fun x => choquetIntegral ν (fun y => f (x, y))) +
        (fun x => choquetIntegral ν (fun y => g (x, y))) := by
    funext x
    exact choquetIntegral_add ν hν (hf.section_right x) (hg.section_right x)
  unfold topologicalExpectation
  rw [he, choquetIntegral_add μ hμ (choquetIntegral_sections_isLSC ν hν f hf)
    (choquetIntegral_sections_isLSC ν hν g hg)]

theorem topologicalExpectation_modular (μ : Valuation X) (hμ : μ.Subprobability)
    (ν : Valuation Y) (hν : ν.Subprobability) {f g : X × Y → ℝ≥0∞}
    (hf : IsLSC f) (hg : IsLSC g) :
    topologicalExpectation μ ν f + topologicalExpectation μ ν g =
      topologicalExpectation μ ν (f ⊔ g) + topologicalExpectation μ ν (f ⊓ g) := by
  rw [← topologicalExpectation_add μ hμ ν hν hf hg,
    ← topologicalExpectation_add μ hμ ν hν (hf.sup hg) (hf.inf hg)]
  congr 1
  funext z
  change f z + g z = (f z ⊔ g z) + (f z ⊓ g z)
  rcases le_total (f z) (g z) with h | h
  · simp only [sup_eq_right.mpr h, inf_eq_left.mpr h, add_comm]
  · simp only [sup_eq_left.mpr h, inf_eq_right.mpr h]

theorem topologicalExpectation_iSup (μ : Valuation X) (ν : Valuation Y)
    (hν : ν.Subprobability) {ι : Type w} [Nonempty ι]
    (f : ι → X × Y → ℝ≥0∞) (hf : ∀ i, IsLSC (f i)) (hd : Directed (· ≤ ·) f) :
    topologicalExpectation μ ν (fun z => ⨆ i, f i z) =
      ⨆ i, topologicalExpectation μ ν (f i) := by
  have hds (x : X) : Directed (· ≤ ·) (fun i y => f i (x, y)) := by
    intro i j
    obtain ⟨k, hik, hjk⟩ := hd i j
    exact ⟨k, fun y => hik (x, y), fun y => hjk (x, y)⟩
  have he (x : X) : choquetIntegral ν (fun y => ⨆ i, f i (x, y)) =
      ⨆ i, choquetIntegral ν (fun y => f i (x, y)) :=
    choquetIntegral_iSup ν _ (fun i => (hf i).section_right x) (hds x)
  have hdi : Directed (· ≤ ·) (fun i x => choquetIntegral ν (fun y => f i (x, y))) := by
    intro i j
    obtain ⟨k, hik, hjk⟩ := hd i j
    exact ⟨k, fun x => choquetIntegral_mono ν (fun y => hik (x, y)),
      fun x => choquetIntegral_mono ν (fun y => hjk (x, y))⟩
  simp only [topologicalExpectation, he]
  exact choquetIntegral_iSup μ _ (fun i => choquetIntegral_sections_isLSC ν hν _ (hf i)) hdi

theorem topologicalExpectation_indicator (μ : Valuation X) (hμ : μ.Subprobability)
    (ν : Valuation Y) (W : Opens (X × Y)) (c : ℝ≥0) :
    topologicalExpectation μ ν ((W : Set (X × Y)).indicator (fun _ => (c : ℝ≥0∞))) =
      (c : ℝ≥0∞) * topologicalProductValuation μ hμ ν W := by
  have he : (fun x => choquetIntegral ν (fun y =>
      (W : Set (X × Y)).indicator (fun _ => (c : ℝ≥0∞)) (x, y))) =
      fun x => (c : ℝ≥0∞) * ν (openSection W x) := by
    funext x
    exact choquetIntegral_indicator_nnreal ν (openSection W x) c
  unfold topologicalExpectation
  rw [he, choquetIntegral_mul_const μ hμ c (valuation_openSection_isLSC ν W)]
  rfl

theorem choquetIntegral_topologicalProduct (μ : Valuation X) (hμ : μ.Subprobability)
    (ν : Valuation Y) (hν : ν.Subprobability) (f : X × Y → ℝ≥0∞) (hf : IsLSC f) :
    choquetIntegral (topologicalProductValuation μ hμ ν) f =
      topologicalExpectation μ ν f := by
  symm
  exact choquetIntegral_unique_of_modular_iSup _
    (topologicalProductValuation_subprobability μ hμ ν hν) (topologicalExpectation μ ν)
    (fun f g hf hg => topologicalExpectation_modular μ hμ ν hν hf hg)
    (fun f hf hd => topologicalExpectation_iSup μ ν hν f hf hd)
    (fun W c => topologicalExpectation_indicator μ hμ ν W c) f hf

theorem topologicalProductValuation_swap (μ : Valuation X) (hμ : μ.Subprobability)
    (ν : Valuation Y) (hν : ν.Subprobability) :
    topologicalProductValuation μ hμ ν =
      (topologicalProductValuation ν hν μ).push Prod.swap continuous_swap := by
  apply valuation_ext_rectangles _ _ (topologicalProductValuation_subprobability μ hμ ν hν)
    (topologicalProductValuation_subprobability ν hν μ hμ)
  intro U V
  have he : Opens.comap ⟨Prod.swap, continuous_swap⟩ (openRectangle (U, V)) =
      openRectangle (V, U) := by
    apply Opens.ext
    ext z
    change (z.2 ∈ U ∧ z.1 ∈ V) ↔ (z.1 ∈ V ∧ z.2 ∈ U)
    exact and_comm
  rw [Valuation.push_apply, he, topologicalProductValuation_rectangle μ hμ ν hν,
    topologicalProductValuation_rectangle ν hν μ hμ, mul_comm]

/-- Genuine Fubini for arbitrary nonnegative LSC functions on an ordinary
topological product, with arbitrary mixed universes and subprobability
valuations. In particular this covers the bounded [0,1] background used by
the manuscript. -/
theorem topological_valuation_fubini (μ : Valuation X) (hμ : μ.Subprobability)
    (ν : Valuation Y) (hν : ν.Subprobability) (f : X × Y → ℝ≥0∞) (hf : IsLSC f) :
    choquetIntegral μ (fun x => choquetIntegral ν (fun y => f (x, y))) =
      choquetIntegral ν (fun y => choquetIntegral μ (fun x => f (x, y))) := by
  change topologicalExpectation μ ν f =
    topologicalExpectation ν μ (fun z => f (z.2, z.1))
  have hfs : IsLSC (fun z : Y × X => f (z.2, z.1)) := hf.comp Prod.swap continuous_swap
  calc
    topologicalExpectation μ ν f = choquetIntegral (topologicalProductValuation μ hμ ν) f :=
      (choquetIntegral_topologicalProduct μ hμ ν hν f hf).symm
    _ = choquetIntegral ((topologicalProductValuation ν hν μ).push Prod.swap continuous_swap) f :=
      congrArg (fun ρ => choquetIntegral ρ f) (topologicalProductValuation_swap μ hμ ν hν)
    _ = choquetIntegral (topologicalProductValuation ν hν μ) (fun z => f (z.2, z.1)) :=
      choquetIntegral_push _ Prod.swap continuous_swap f hf
    _ = topologicalExpectation ν μ (fun z => f (z.2, z.1)) :=
      choquetIntegral_topologicalProduct ν hν μ hμ _ hfs

end ZFCFubini
