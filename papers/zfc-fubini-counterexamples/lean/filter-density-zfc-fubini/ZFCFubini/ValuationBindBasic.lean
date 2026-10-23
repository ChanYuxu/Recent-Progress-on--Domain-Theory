import ZFCFubini.ValuationIntegralMCT
import ZFCFubini.IntegralTransport

/-! Infinite constants, Dirac evaluation, and continuity in the valuation
parameter. These are consequences of the actual layer-cake integral and its
proved full directed convergence theorem; they precede bind itself. -/

set_option autoImplicit false
open Set Topology TopologicalSpace MeasureTheory
open scoped ENNReal NNReal Classical
universe u v

namespace ZFCFubini

theorem choquetIntegral_indicator {X : Type u} [TopologicalSpace X]
    (μ : Valuation X) (U : Opens X) (c : ℝ≥0∞) :
    choquetIntegral μ ((U : Set X).indicator (fun _ => c)) = c * μ U := by
  let a : ℕ → ℝ≥0 := fun n => (min c (n : ℝ≥0∞)).toNNReal
  have ha (n : ℕ) : (a n : ℝ≥0∞) = min c n :=
    ENNReal.coe_toNNReal (ne_top_of_le_ne_top (ENNReal.natCast_ne_top n) (min_le_right _ _))
  have hsup : (⨆ n, (a n : ℝ≥0∞)) = c := by
    simp_rw [ha, min_comm c]
    change (⨆ n : ℕ, (n : ℝ≥0∞) ⊓ c) = c
    rw [← iSup_inf_eq, ENNReal.iSup_natCast, top_inf_eq]
  have hd : Directed (· ≤ ·) (fun n => (U : Set X).indicator (fun _ => (a n : ℝ≥0∞))) := by
    intro i j
    refine ⟨max i j, ?_, ?_⟩
    · intro x
      by_cases hx : x ∈ (U : Set X)
      · simp only [Set.indicator_of_mem hx, ha]
        exact min_le_min_left _ (Nat.cast_le.mpr (le_max_left i j))
      · simp only [Set.indicator_of_notMem hx, le_refl]
    · intro x
      by_cases hx : x ∈ (U : Set X)
      · simp only [Set.indicator_of_mem hx, ha]
        exact min_le_min_left _ (Nat.cast_le.mpr (le_max_right i j))
      · simp only [Set.indicator_of_notMem hx, le_refl]
  have heq : (fun x => ⨆ n, (U : Set X).indicator (fun _ => (a n : ℝ≥0∞)) x) =
      (U : Set X).indicator (fun _ => c) := by
    funext x
    by_cases hx : x ∈ (U : Set X)
    · simp only [Set.indicator_of_mem hx, hsup]
    · simp only [Set.indicator_of_notMem hx, iSup_const]
  rw [← heq, choquetIntegral_iSup μ _ (fun n => IsLSC.indicator U (a n)) hd]
  simp_rw [choquetIntegral_indicator_nnreal]
  rw [← ENNReal.iSup_mul, hsup]

theorem choquetIntegral_const {X : Type u} [TopologicalSpace X]
    (μ : Valuation X) (c : ℝ≥0∞) :
    choquetIntegral μ (fun _ => c) = c * μ ⊤ := by
  simpa using choquetIntegral_indicator μ ⊤ c

/-- Dirac integration is evaluation, for the actual strict-level integral. -/
theorem choquetIntegral_dirac {X : Type u} [TopologicalSpace X]
    (x : X) (f : X → ℝ≥0∞) (hf : IsLSC f) :
    choquetIntegral (Valuation.dirac x) f = f x := by
  calc
    choquetIntegral (Valuation.dirac x) f =
        choquetIntegral (Valuation.dirac x) (fun _ : X => f x) := by
      rw [choquetIntegral_eq_layerCake _ _ hf,
        choquetIntegral_eq_layerCake _ _ (IsLSC.const (f x))]
      apply lintegral_congr
      intro t
      simp only [Valuation.dirac_apply, Opens.mem_mk, Set.mem_setOf_eq]
    _ = f x := by
      rw [choquetIntegral_const]
      simp only [Valuation.dirac_apply, Opens.mem_top, if_true, mul_one]

/-- Joint continuity in the actual valuation and the LSC integrand follows
by two directed-sup arguments and a common directed upper index. -/
theorem choquetIntegral_scottContinuous_joint {X : Type u} [TopologicalSpace X]
    {P : Type v} [Preorder P] (μ : P → SubprobValuation X) (hμ : ScottContinuous μ)
    (f : P → X → ℝ≥0∞) (hflsc : ∀ p, IsLSC (f p))
    (hfsc : ∀ x, ScottContinuous (fun p => f p x)) :
    ScottContinuous (fun p => choquetIntegral (μ p).val (f p)) := by
  intro A hn hd p hp
  have hleft := (hμ.comp SubprobValuation.val_scottContinuous |>.comp
    (choquetIntegral_scottContinuous_valuation (f p) (hflsc p))) hn hd hp
  constructor
  · rintro _ ⟨a, ha, rfl⟩
    exact (choquetIntegral_mono_valuation (hμ.monotone (hp.1 ha)) (f a)).trans
      (choquetIntegral_mono (μ p).val (fun x => (hfsc x).monotone (hp.1 ha)))
  · intro b hb
    apply hleft.2
    rintro _ ⟨a, ha, rfl⟩
    apply (choquetIntegral_scottContinuous_param (μ a).val f hflsc hfsc hn hd hp).2
    rintro _ ⟨c, hc, rfl⟩
    obtain ⟨d, hdA, had, hcd⟩ := hd a ha c hc
    exact ((choquetIntegral_mono_valuation (hμ.monotone had) (f c)).trans
      (choquetIntegral_mono (μ d).val (fun x => (hfsc x).monotone hcd))).trans
        (hb ⟨d, hdA, rfl⟩)

end ZFCFubini
