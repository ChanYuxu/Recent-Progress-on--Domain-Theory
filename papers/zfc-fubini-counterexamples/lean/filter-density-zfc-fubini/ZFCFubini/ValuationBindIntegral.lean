import ZFCFubini.ValuationBind

/-! Integral substitution for the actual bind. The proof identifies the
composed expectation by its proved indicator, modular and directed-sup laws.
This is an integration theorem, not an associativity assumption. -/

set_option autoImplicit false
open Set Topology TopologicalSpace
open scoped ENNReal NNReal Classical
universe u v w

namespace ZFCFubini

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

theorem kernelIntegral_isLSC (k : X → SubprobValuation Y)
    (hk : Continuous (fun x => WithScott.toScott (k x)))
    (f : Y → ℝ≥0∞) (hf : IsLSC f) :
    IsLSC (fun x => choquetIntegral (k x).val f) :=
  (scott_isLSC (SubprobValuation.val_scottContinuous.comp
    (choquetIntegral_scottContinuous_valuation f hf))).comp _ hk

noncomputable def bindExpectation (μ : SubprobValuation X)
    (k : X → SubprobValuation Y) (f : Y → ℝ≥0∞) : ℝ≥0∞ :=
  choquetIntegral μ.val (fun x => choquetIntegral (k x).val f)

theorem bindExpectation_mono (μ : SubprobValuation X) (k : X → SubprobValuation Y) :
    Monotone (bindExpectation μ k) := by
  intro f g hfg
  exact choquetIntegral_mono μ.val (fun x => choquetIntegral_mono (k x).val hfg)

theorem bindExpectation_iSup (μ : SubprobValuation X) (k : X → SubprobValuation Y)
    (hk : Continuous (fun x => WithScott.toScott (k x)))
    {ι : Type w} [Nonempty ι] (f : ι → Y → ℝ≥0∞) (hf : ∀ i, IsLSC (f i))
    (hd : Directed (· ≤ ·) f) :
    bindExpectation μ k (fun y => ⨆ i, f i y) = ⨆ i, bindExpectation μ k (f i) := by
  have hdir : Directed (· ≤ ·) (fun i x => choquetIntegral (k x).val (f i)) := by
    intro i j
    obtain ⟨l, hil, hjl⟩ := hd i j
    exact ⟨l, fun x => choquetIntegral_mono (k x).val hil,
      fun x => choquetIntegral_mono (k x).val hjl⟩
  unfold bindExpectation
  simp_rw [choquetIntegral_iSup _ f hf hd]
  exact choquetIntegral_iSup μ.val _ (fun i => kernelIntegral_isLSC k hk _ (hf i)) hdir

theorem bindExpectation_add (μ : SubprobValuation X) (k : X → SubprobValuation Y)
    (hk : Continuous (fun x => WithScott.toScott (k x)))
    {f g : Y → ℝ≥0∞} (hf : IsLSC f) (hg : IsLSC g) :
    bindExpectation μ k (f + g) = bindExpectation μ k f + bindExpectation μ k g := by
  have hi (x : X) : choquetIntegral (k x).val (f + g) =
      choquetIntegral (k x).val f + choquetIntegral (k x).val g :=
    choquetIntegral_add (k x).val (k x).property hf hg
  unfold bindExpectation
  simp_rw [hi]
  exact choquetIntegral_add μ.val μ.property
    (kernelIntegral_isLSC k hk f hf) (kernelIntegral_isLSC k hk g hg)

theorem bindExpectation_modular (μ : SubprobValuation X) (k : X → SubprobValuation Y)
    (hk : Continuous (fun x => WithScott.toScott (k x)))
    (f g : Y → ℝ≥0∞) (hf : IsLSC f) (hg : IsLSC g) :
    bindExpectation μ k f + bindExpectation μ k g =
      bindExpectation μ k (f ⊔ g) + bindExpectation μ k (f ⊓ g) := by
  calc
    bindExpectation μ k f + bindExpectation μ k g = bindExpectation μ k (f + g) :=
      (bindExpectation_add μ k hk hf hg).symm
    _ = bindExpectation μ k ((f ⊔ g) + (f ⊓ g)) := by
      congr 1
      exact funext fun y => (max_add_min (f y) (g y)).symm
    _ = _ := bindExpectation_add μ k hk (hf.sup hg) (hf.inf hg)

theorem bindExpectation_indicator (μ : SubprobValuation X) (k : X → SubprobValuation Y)
    (hk : Continuous (fun x => WithScott.toScott (k x))) (U : Opens Y) (c : ℝ≥0) :
    bindExpectation μ k ((U : Set Y).indicator (fun _ => (c : ℝ≥0∞))) =
      (c : ℝ≥0∞) * (μ.bind k hk).val U := by
  unfold bindExpectation
  simp_rw [choquetIntegral_indicator_nnreal]
  exact choquetIntegral_mul_const μ.val μ.property c (SubprobValuation.kernel_isLSC k hk U)

/-- Integral substitution for bind, proved on all nonnegative LSC functions. -/
theorem choquetIntegral_bind (μ : SubprobValuation X) (k : X → SubprobValuation Y)
    (hk : Continuous (fun x => WithScott.toScott (k x)))
    (f : Y → ℝ≥0∞) (hf : IsLSC f) :
    choquetIntegral (μ.bind k hk).val f =
      choquetIntegral μ.val (fun x => choquetIntegral (k x).val f) := by
  have h := choquetIntegral_unique_of_modular_iSup (μ.bind k hk).val
    (μ.bind k hk).property (bindExpectation μ k)
    (bindExpectation_modular μ k hk)
    (fun g hg hd => bindExpectation_iSup μ k hk g hg hd)
    (bindExpectation_indicator μ k hk) f hf
  exact h.symm

namespace SubprobValuation

theorem bind_assoc {Z : Type w} [TopologicalSpace Z]
    (μ : SubprobValuation X) (k : X → SubprobValuation Y)
    (hk : Continuous (fun x => WithScott.toScott (k x)))
    (l : Y → SubprobValuation Z) (hl : Continuous (fun y => WithScott.toScott (l y))) :
    (μ.bind k hk).bind l hl =
      μ.bind (fun x => (k x).bind l hl) (bindKernel_continuous k hk l hl) := by
  apply Subtype.ext
  apply Valuation.ext
  intro U
  exact choquetIntegral_bind μ k hk _ (kernel_isLSC l hl U)

end SubprobValuation

end ZFCFubini
