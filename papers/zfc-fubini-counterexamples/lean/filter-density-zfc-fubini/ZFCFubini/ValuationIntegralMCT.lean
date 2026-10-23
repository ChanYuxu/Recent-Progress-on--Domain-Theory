import ZFCFubini.ValuationIntegralBasic

/-! Full directed monotone convergence for the existing Choquet integral.
Only the real threshold axis is second countable. The valuation space and the
original directed index need not be countable, metrizable, or measure spaces. -/

set_option autoImplicit false
open Set Topology TopologicalSpace MeasureTheory
open scoped ENNReal NNReal
universe u v w
namespace ZFCFubini

/-- A full-index lower-integral interchange. The countable-envelope theorem
extracts functions with the same pointwise supremum, not a cofinal subset of
the original directed index. Finite subfamilies are bounded by directedness. -/
theorem lintegral_iSup_lsc_directed {Z : Type u} [TopologicalSpace Z]
    [HereditarilyLindelofSpace Z] [MeasurableSpace Z] [OpensMeasurableSpace Z]
    (ξ : Measure Z) {ι : Type v} [Nonempty ι]
    (f : ι → Z → ℝ≥0∞) (hf : ∀ i, LowerSemicontinuous (f i))
    (hd : Directed (· ≤ ·) f) :
    (∫⁻ z, ⨆ i, f i z ∂ξ) = ⨆ i, ∫⁻ z, f i z ∂ξ := by
  classical
  obtain ⟨C, hC, hCcount, hClub⟩ := exists_countable_lowerSemicontinuous_isLUB
    (𝓕 := Set.range f) (s := ⨆ i, f i)
    (by rintro _ ⟨i, rfl⟩; exact hf i) isLUB_iSup
  letI : Countable C := hCcount.to_subtype
  have hchoose (c : C) : ∃ i, f i = (c : Z → ℝ≥0∞) := hC c.property
  choose j hj using hchoose
  let g (F : Finset C) : Z → ℝ≥0∞ := F.sup (fun c => (c : Z → ℝ≥0∞))
  have hg (F : Finset C) : Measurable (g F) := by
    induction F using Finset.induction_on with
    | empty =>
        change Measurable (fun _ : Z => (0 : ℝ≥0∞))
        exact measurable_const
    | @insert c F hc ih =>
        simp only [g, Finset.sup_insert]
        change Measurable (fun z => (c : Z → ℝ≥0∞) z ⊔ g F z)
        rw [← hj c]
        exact (hf (j c)).measurable.sup ih
  have hgd : Directed (· ≤ ·) g := by
    intro F G
    exact ⟨F ∪ G, Finset.sup_mono Finset.subset_union_left,
      Finset.sup_mono Finset.subset_union_right⟩
  have hsupC : (⨆ i, f i) = ⨆ c : C, (c : Z → ℝ≥0∞) := by
    apply hClub.unique
    simpa only [Subtype.range_coe_subtype, setOf_mem_eq] using
      (isLUB_iSup (f := fun c : C => (c : Z → ℝ≥0∞)))
  have hsup (z : Z) : (⨆ i, f i z) = ⨆ F : Finset C, g F z := by
    have he : (⨆ i, f i z) = ⨆ c : C, (c : Z → ℝ≥0∞) z :=
      by simpa only [iSup_apply] using congrFun hsupC z
    rw [he]
    apply le_antisymm
    · apply iSup_le
      intro c
      exact le_iSup_of_le {c} (by simp [g])
    · apply iSup_le
      intro F
      simp only [g, Finset.sup_apply]
      exact Finset.sup_le (fun c _ => le_iSup (fun c : C => (c : Z → ℝ≥0∞) z) c)
  simp_rw [hsup]
  rw [lintegral_iSup_directed_of_measurable hg hgd]
  apply le_antisymm
  · apply iSup_le
    intro F
    obtain ⟨i, hi⟩ := hd.finset_le (F.image j)
    apply le_iSup_of_le i
    apply lintegral_mono
    intro z
    simp only [g, Finset.sup_apply]
    apply Finset.sup_le
    intro c hc
    rw [← hj c]
    exact hi (j c) (Finset.mem_image_of_mem j hc) z
  · apply iSup_le
    intro i
    calc
      (∫⁻ z, f i z ∂ξ) ≤ ∫⁻ z, ⨆ F : Finset C, g F z ∂ξ :=
        lintegral_mono (fun z => by rw [← hsup]; exact le_iSup (fun i => f i z) i)
      _ = ⨆ F : Finset C, ∫⁻ z, g F z ∂ξ :=
        lintegral_iSup_directed_of_measurable hg hgd

variable {X : Type u} [TopologicalSpace X]

theorem integralLevel_eq_iSup_stricter (f : X → ℝ≥0∞) (hf : IsLSC f) (a : ℝ) :
    integralLevel f a = ⨆ b : {b : ℝ // a < b}, integralLevel f b := by
  rw [integralLevel_of_isLSC f hf]
  apply Opens.ext
  ext x
  change (ENNReal.ofReal a < f x) ↔
    x ∈ (⨆ b : {b : ℝ // a < b}, integralLevel f b)
  rw [Opens.mem_iSup]
  constructor
  · intro hx
    change ENNReal.ofReal a < f x at hx
    have hopen : IsOpen {t : ℝ | ENNReal.ofReal t < f x} :=
      isOpen_lt ENNReal.continuous_ofReal continuous_const
    obtain ⟨l, b, hab, hsub⟩ :=
      mem_nhds_iff_exists_Ioo_subset.mp (hopen.mem_nhds hx)
    obtain ⟨c, hac, hcb⟩ := exists_between hab.2
    refine ⟨⟨c, hac⟩, ?_⟩
    rw [integralLevel_of_isLSC f hf]
    exact hsub ⟨hab.1.trans hac, hcb⟩
  · rintro ⟨b, hb⟩
    rw [integralLevel_of_isLSC f hf] at hb
    exact (ENNReal.ofReal_le_ofReal b.property.le).trans_lt hb

theorem integralProfile_lowerSemicontinuous (μ : Valuation X)
    (f : X → ℝ≥0∞) (hf : IsLSC f) : LowerSemicontinuous (integralProfile μ f) := by
  apply lowerSemicontinuous_iff_isOpen_preimage.mpr
  intro r
  apply isOpen_iff_mem_nhds.mpr
  intro a ha
  change r < integralProfile μ f a at ha
  letI : Nonempty {b : ℝ // a < b} := ⟨⟨a + 1, by linarith⟩⟩
  have hd : Directed (· ≤ ·) (fun b : {b : ℝ // a < b} => integralLevel f b) := by
    intro b c
    refine ⟨⟨min b c, lt_min b.property c.property⟩, ?_, ?_⟩
    · exact interior_mono (fun x hx => (ENNReal.ofReal_le_ofReal (min_le_left _ _)).trans_lt hx)
    · exact interior_mono (fun x hx => (ENNReal.ofReal_le_ofReal (min_le_right _ _)).trans_lt hx)
  have he : integralProfile μ f a =
      ⨆ b : {b : ℝ // a < b}, integralProfile μ f b := by
    unfold integralProfile
    rw [integralLevel_eq_iSup_stricter f hf a, μ.map_iSup _ hd]
  rw [he, lt_iSup_iff] at ha
  obtain ⟨b, hb⟩ := ha
  apply Filter.mem_of_superset (Iio_mem_nhds b.property)
  intro c hc
  exact hb.trans_le (integralProfile_antitone μ f hc.le)

theorem integralLevel_iSup {ι : Type v} (f : ι → X → ℝ≥0∞)
    (hf : ∀ i, IsLSC (f i)) (a : ℝ) :
    integralLevel (fun x => ⨆ i, f i x) a = ⨆ i, integralLevel (f i) a := by
  rw [integralLevel_of_isLSC _ (IsLSC.iSup f hf)]
  apply Opens.ext
  ext x
  change (ENNReal.ofReal a < ⨆ i, f i x) ↔ x ∈ (⨆ i, integralLevel (f i) a)
  rw [Opens.mem_iSup]
  simp_rw [integralLevel_of_isLSC _ (hf _)]
  exact lt_iSup_iff

theorem choquetIntegral_iSup (μ : Valuation X) {ι : Type v} [Nonempty ι]
    (f : ι → X → ℝ≥0∞) (hf : ∀ i, IsLSC (f i)) (hd : Directed (· ≤ ·) f) :
    choquetIntegral μ (fun x => ⨆ i, f i x) = ⨆ i, choquetIntegral μ (f i) := by
  have hlevel : ∀ a, Directed (· ≤ ·) (fun i => integralLevel (f i) a) := by
    intro a i j
    obtain ⟨k, hik, hjk⟩ := hd i j
    exact ⟨k, integralLevel_mono hik a, integralLevel_mono hjk a⟩
  have hprofile (a : ℝ) : integralProfile μ (fun x => ⨆ i, f i x) a =
      ⨆ i, integralProfile μ (f i) a := by
    unfold integralProfile
    rw [integralLevel_iSup f hf, μ.map_iSup _ (hlevel a)]
  have hdp : Directed (· ≤ ·) (fun i => integralProfile μ (f i)) := by
    intro i j
    obtain ⟨k, hik, hjk⟩ := hd i j
    exact ⟨k, fun a => μ.mono (integralLevel_mono hik a),
      fun a => μ.mono (integralLevel_mono hjk a)⟩
  simp_rw [choquetIntegral_eq_profile, hprofile]
  exact lintegral_iSup_lsc_directed (volume.restrict (Ici 0)) _
    (fun i => integralProfile_lowerSemicontinuous μ _ (hf i)) hdp

theorem choquetIntegral_iSup_valuation (f : X → ℝ≥0∞) (hf : IsLSC f)
    {ι : Type v} [Nonempty ι] (μ : ι → Valuation X) (ν : Valuation X)
    (hd : Directed (· ≤ ·) μ) (hν : ∀ U, ν U = ⨆ i, μ i U) :
    choquetIntegral ν f = ⨆ i, choquetIntegral (μ i) f := by
  have he (a : ℝ) : integralProfile ν f a = ⨆ i, integralProfile (μ i) f a := hν _
  have hdp : Directed (· ≤ ·) (fun i => integralProfile (μ i) f) := by
    intro i j
    obtain ⟨k, hik, hjk⟩ := hd i j
    exact ⟨k, fun a => hik _, fun a => hjk _⟩
  simp_rw [choquetIntegral_eq_profile, he]
  exact lintegral_iSup_lsc_directed (volume.restrict (Ici 0)) _
    (fun i => integralProfile_lowerSemicontinuous (μ i) f hf) hdp

theorem choquetIntegral_scottContinuous_param {P : Type v} [Preorder P]
    (μ : Valuation X) (F : P → X → ℝ≥0∞) (hFlsc : ∀ p, IsLSC (F p))
    (hFsc : ∀ x, ScottContinuous (fun p => F p x)) :
    ScottContinuous (fun p => choquetIntegral μ (F p)) := by
  intro A hn hd p hp
  letI : Nonempty A := hn.to_subtype
  have hFd : Directed (· ≤ ·) (fun a : A => F a) := by
    intro a b
    obtain ⟨c, hc, hac, hbc⟩ := hd a a.property b b.property
    exact ⟨⟨c, hc⟩, fun x => (hFsc x).monotone hac, fun x => (hFsc x).monotone hbc⟩
  have he (x : X) : F p x = ⨆ a : A, F a x := by
    apply (hFsc x hn hd hp).unique
    constructor
    · rintro _ ⟨a, ha, rfl⟩
      exact le_iSup (fun a : A => F a x) ⟨a, ha⟩
    · intro b hb
      exact iSup_le fun a => hb ⟨a, a.property, rfl⟩
  have hi : choquetIntegral μ (F p) = ⨆ a : A, choquetIntegral μ (F a) := by
    conv_lhs => arg 2; ext x; rw [he]
    exact choquetIntegral_iSup μ _ (fun a => hFlsc a) hFd
  change IsLUB ((fun p => choquetIntegral μ (F p)) '' A) (choquetIntegral μ (F p))
  rw [hi]
  constructor
  · rintro _ ⟨a, ha, rfl⟩
    exact le_iSup (fun a : A => choquetIntegral μ (F a)) ⟨a, ha⟩
  · intro b hb
    exact iSup_le fun a => hb ⟨a, a.property, rfl⟩

theorem choquetIntegral_mono_valuation {μ ν : Valuation X} (hμν : μ ≤ ν)
    (f : X → ℝ≥0∞) : choquetIntegral μ f ≤ choquetIntegral ν f :=
  lintegral_mono (fun _ => hμν _)

theorem choquetIntegral_scottContinuous_valuation (f : X → ℝ≥0∞) (hf : IsLSC f) :
    ScottContinuous (fun μ : Valuation X => choquetIntegral μ f) := by
  intro A hn hd p hp
  letI : Nonempty A := hn.to_subtype
  have hμd : Directed (· ≤ ·) (fun a : A => (a : Valuation X)) := by
    intro a b
    obtain ⟨c, hc, hac, hbc⟩ := hd a a.property b b.property
    exact ⟨⟨c, hc⟩, hac, hbc⟩
  have he (U : Opens X) : p U = ⨆ a : A, (a : Valuation X) U := by
    apply (Valuation.evaluation_scottContinuous U hn hd hp).unique
    constructor
    · rintro _ ⟨a, ha, rfl⟩
      exact le_iSup (fun a : A => (a : Valuation X) U) ⟨a, ha⟩
    · intro b hb
      exact iSup_le fun a => hb ⟨a, a.property, rfl⟩
  change IsLUB ((fun μ => choquetIntegral μ f) '' A) (choquetIntegral p f)
  rw [choquetIntegral_iSup_valuation f hf _ p hμd he]
  constructor
  · rintro _ ⟨a, ha, rfl⟩
    exact le_iSup (fun a : A => choquetIntegral (a : Valuation X) f) ⟨a, ha⟩
  · intro b hb
    exact iSup_le fun a => hb ⟨a, a.property, rfl⟩

end ZFCFubini
