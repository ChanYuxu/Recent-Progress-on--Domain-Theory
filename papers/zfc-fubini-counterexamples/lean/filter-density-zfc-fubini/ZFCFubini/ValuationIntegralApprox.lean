import ZFCFubini.ValuationIntegralMCT

/-! Genuine lower approximation by finite maxima of finite open indicators.
This is an alternative background implementation of lower step approximation;
the manuscript itself cites the general integral/Fubini background. -/

set_option autoImplicit false
open Set Topology TopologicalSpace MeasureTheory
open scoped ENNReal NNReal Classical
universe u v
namespace ZFCFubini
variable {X : Type u} [TopologicalSpace X]

theorem integralLevel_sup {f g : X → ℝ≥0∞} (hf : IsLSC f) (hg : IsLSC g) (a : ℝ) :
    integralLevel (f ⊔ g) a = integralLevel f a ⊔ integralLevel g a := by
  rw [integralLevel_of_isLSC _ (hf.sup hg), integralLevel_of_isLSC _ hf,
    integralLevel_of_isLSC _ hg]
  apply Opens.ext
  ext x
  change (ENNReal.ofReal a < f x ⊔ g x) ↔
    (ENNReal.ofReal a < f x ∨ ENNReal.ofReal a < g x)
  exact lt_sup_iff

theorem integralLevel_inf {f g : X → ℝ≥0∞} (hf : IsLSC f) (hg : IsLSC g) (a : ℝ) :
    integralLevel (f ⊓ g) a = integralLevel f a ⊓ integralLevel g a := by
  rw [integralLevel_of_isLSC _ (hf.inf hg), integralLevel_of_isLSC _ hf,
    integralLevel_of_isLSC _ hg]
  apply Opens.ext
  ext x
  change (ENNReal.ofReal a < f x ⊓ g x) ↔
    (ENNReal.ofReal a < f x ∧ ENNReal.ofReal a < g x)
  exact lt_inf_iff

theorem choquetIntegral_modular (μ : Valuation X) {f g : X → ℝ≥0∞}
    (hf : IsLSC f) (hg : IsLSC g) :
    choquetIntegral μ f + choquetIntegral μ g =
      choquetIntegral μ (f ⊔ g) + choquetIntegral μ (f ⊓ g) := by
  simp only [choquetIntegral_eq_profile]
  rw [← lintegral_add_left (integralProfile_lowerSemicontinuous μ f hf).measurable,
    ← lintegral_add_left (integralProfile_lowerSemicontinuous μ _ (hf.sup hg)).measurable]
  apply lintegral_congr
  intro a
  unfold integralProfile
  rw [integralLevel_sup hf hg, integralLevel_inf hf hg]
  exact μ.modular _ _

abbrev OpenStep (X : Type u) [TopologicalSpace X] := ℝ≥0 × Opens X

noncomputable def openStep (a : OpenStep X) : X → ℝ≥0∞ :=
  (a.2 : Set X).indicator (fun _ => (a.1 : ℝ≥0∞))

noncomputable def finiteOpenStep (F : Finset (OpenStep X)) : X → ℝ≥0∞ := F.sup openStep

noncomputable def finiteOpenStepBound (F : Finset (OpenStep X)) : ℝ≥0 := F.sup Prod.fst

theorem openStep_isLSC (a : OpenStep X) : IsLSC (openStep a) := IsLSC.indicator _ _

theorem finiteOpenStep_isLSC (F : Finset (OpenStep X)) : IsLSC (finiteOpenStep F) := by
  classical
  induction F using Finset.induction_on with
  | empty => exact IsLSC.const 0
  | @insert a F ha ih =>
      simpa only [finiteOpenStep, Finset.sup_insert] using (openStep_isLSC a).sup ih

theorem openStep_le (a : OpenStep X) (x : X) : openStep a x ≤ (a.1 : ℝ≥0∞) :=
  Set.indicator_le_self _ _ x

theorem finiteOpenStep_le (F : Finset (OpenStep X)) (x : X) :
    finiteOpenStep F x ≤ (finiteOpenStepBound F : ℝ≥0∞) := by
  classical
  simp only [finiteOpenStep, Finset.sup_apply]
  apply Finset.sup_le
  intro a ha
  exact (openStep_le a x).trans (ENNReal.coe_le_coe.mpr (Finset.le_sup ha))

theorem finiteOpenStep_integral_ne_top (μ : Valuation X) (hμ : μ.Subprobability)
    (F : Finset (OpenStep X)) : choquetIntegral μ (finiteOpenStep F) ≠ ∞ := by
  apply ne_top_of_le_ne_top (ENNReal.coe_ne_top : (finiteOpenStepBound F : ℝ≥0∞) ≠ ∞)
  calc
    choquetIntegral μ (finiteOpenStep F) ≤
        choquetIntegral μ (fun _ => (finiteOpenStepBound F : ℝ≥0∞)) :=
      choquetIntegral_mono μ (finiteOpenStep_le F)
    _ = (finiteOpenStepBound F : ℝ≥0∞) * μ ⊤ := choquetIntegral_const_nnreal μ _
    _ ≤ (finiteOpenStepBound F : ℝ≥0∞) := by
      simpa using mul_le_mul_left' hμ (finiteOpenStepBound F : ℝ≥0∞)

theorem openStep_inf (a b : OpenStep X) :
    openStep a ⊓ openStep b = openStep (a.1 ⊓ b.1, a.2 ⊓ b.2) := by
  classical
  funext x
  by_cases ha : x ∈ (a.2 : Set X) <;> by_cases hb : x ∈ (b.2 : Set X) <;>
    simp [openStep, ha, hb]

theorem finiteOpenStep_inf (F : Finset (OpenStep X)) (a : OpenStep X) :
    finiteOpenStep F ⊓ openStep a =
      finiteOpenStep (F.image (fun b => (b.1 ⊓ a.1, b.2 ⊓ a.2))) := by
  classical
  induction F using Finset.induction_on with
  | empty => simp [finiteOpenStep]
  | @insert b F hb ih =>
      simp only [finiteOpenStep, Finset.sup_insert, Finset.image_insert, inf_sup_right,
        openStep_inf] at *
      rw [ih]

noncomputable def lowerAtom (f : X → ℝ≥0∞) (hf : IsLSC f) (c : ℝ≥0) : OpenStep X :=
  (c, ⟨{x | (c : ℝ≥0∞) < f x}, hf c⟩)

noncomputable def lowerStep (f : X → ℝ≥0∞) (hf : IsLSC f) (F : Finset ℝ≥0) :
    X → ℝ≥0∞ := finiteOpenStep (F.image (lowerAtom f hf))

theorem lowerStep_isLSC (f : X → ℝ≥0∞) (hf : IsLSC f) (F : Finset ℝ≥0) :
    IsLSC (lowerStep f hf F) := finiteOpenStep_isLSC _

theorem lowerStep_directed (f : X → ℝ≥0∞) (hf : IsLSC f) :
    Directed (· ≤ ·) (lowerStep f hf) := by
  classical
  intro F G
  refine ⟨F ∪ G, ?_, ?_⟩
  · exact Finset.sup_mono (Finset.image_subset_image Finset.subset_union_left)
  · exact Finset.sup_mono (Finset.image_subset_image Finset.subset_union_right)

theorem lowerStep_le (f : X → ℝ≥0∞) (hf : IsLSC f) (F : Finset ℝ≥0) :
    lowerStep f hf F ≤ f := by
  classical
  intro x
  simp only [lowerStep, finiteOpenStep, Finset.sup_apply]
  apply Finset.sup_le
  rintro a ha
  obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp ha
  by_cases hx : (c : ℝ≥0∞) < f x
  · simpa [lowerAtom, openStep, hx] using hx.le
  · simp [lowerAtom, openStep, hx]

theorem iSup_lowerStep (f : X → ℝ≥0∞) (hf : IsLSC f) (x : X) :
    (⨆ F : Finset ℝ≥0, lowerStep f hf F x) = f x := by
  classical
  apply le_antisymm (iSup_le (fun F => lowerStep_le f hf F x))
  by_contra h
  obtain ⟨c, hc, hcf⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp (lt_of_not_ge h)
  have he : lowerStep f hf {c} x = (c : ℝ≥0∞) := by
    simp [lowerStep, finiteOpenStep, lowerAtom, openStep, hcf]
  have hle := le_iSup (fun F : Finset ℝ≥0 => lowerStep f hf F x) {c}
  rw [he] at hle
  exact hc.not_ge hle

theorem choquetIntegral_eq_iSup_lowerStep (μ : Valuation X)
    (f : X → ℝ≥0∞) (hf : IsLSC f) :
    choquetIntegral μ f = ⨆ F : Finset ℝ≥0, choquetIntegral μ (lowerStep f hf F) := by
  have he : f = fun x => ⨆ F : Finset ℝ≥0, lowerStep f hf F x :=
    funext (fun x => (iSup_lowerStep f hf x).symm)
  conv_lhs => arg 2; rw [he]
  exact choquetIntegral_iSup μ _ (lowerStep_isLSC f hf) (lowerStep_directed f hf)

/-- Uniqueness on LSC functions. The displayed fixed index is the genuine
finite-max approximation index; callers with full directed continuity may
specialize it here. Modularity, not a hidden measure representation, handles
overlapping open indicators. -/
theorem choquetIntegral_unique_of_modular_iSup (μ : Valuation X)
    (hμ : μ.Subprobability) (F : (X → ℝ≥0∞) → ℝ≥0∞)
    (hFmod : ∀ (f g : X → ℝ≥0∞), IsLSC f → IsLSC g →
      F f + F g = F (f ⊔ g) + F (f ⊓ g))
    (hFsup : ∀ g : Finset ℝ≥0 → X → ℝ≥0∞,
      (∀ i, IsLSC (g i)) → Directed (· ≤ ·) g →
      F (fun x => ⨆ i, g i x) = ⨆ i, F (g i))
    (hFind : ∀ (U : Opens X) (c : ℝ≥0),
      F ((U : Set X).indicator (fun _ => (c : ℝ≥0∞))) = (c : ℝ≥0∞) * μ U)
    (f : X → ℝ≥0∞) (hf : IsLSC f) : F f = choquetIntegral μ f := by
  classical
  have hFzero : F (fun _ => 0) = 0 := by simpa using hFind ⊥ 0
  have hAtom (a : OpenStep X) : F (openStep a) = choquetIntegral μ (openStep a) := by
    rw [show F (openStep a) = (a.1 : ℝ≥0∞) * μ a.2 from hFind a.2 a.1]
    exact (choquetIntegral_indicator_nnreal μ a.2 a.1).symm
  have hfinite (n : ℕ) : ∀ G : Finset (OpenStep X), G.card = n →
      F (finiteOpenStep G) = choquetIntegral μ (finiteOpenStep G) := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro G hn
      by_cases hGzero : G = ∅
      · subst G
        change F (fun _ => 0) = choquetIntegral μ (fun _ => 0)
        rw [hFzero, choquetIntegral_zero]
      obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.mpr hGzero
      let R := G.erase a
      let S := R.image (fun b => (b.1 ⊓ a.1, b.2 ⊓ a.2))
      have hRn : R.card < n := by
        simpa only [R, ← hn] using Finset.card_erase_lt_of_mem ha
      have hSn : S.card < n := (Finset.card_image_le).trans_lt hRn
      have hR := ih R.card hRn R rfl
      have hS := ih S.card hSn S rfl
      have hG : finiteOpenStep G = openStep a ⊔ finiteOpenStep R := by
        change G.sup openStep = openStep a ⊔ (G.erase a).sup openStep
        conv_lhs => rw [← Finset.insert_erase ha]
        exact Finset.sup_insert
      have hmin : openStep a ⊓ finiteOpenStep R = finiteOpenStep S := by
        rw [inf_comm, finiteOpenStep_inf]
      have hm := hFmod (openStep a) (finiteOpenStep R)
        (openStep_isLSC a) (finiteOpenStep_isLSC R)
      rw [hAtom a, hR, ← hG, hmin, hS] at hm
      have hmI := choquetIntegral_modular μ (openStep_isLSC a) (finiteOpenStep_isLSC R)
      rw [← hG, hmin] at hmI
      exact (ENNReal.add_left_inj (finiteOpenStep_integral_ne_top μ hμ S)).mp
        (hm.symm.trans hmI)
  have hfinite' (G : Finset (OpenStep X)) := hfinite G.card G rfl
  calc
    F f = F (fun x => ⨆ G : Finset ℝ≥0, lowerStep f hf G x) := by
      congr 1
      funext x
      exact (iSup_lowerStep f hf x).symm
    _ = ⨆ G : Finset ℝ≥0, F (lowerStep f hf G) :=
      hFsup _ (lowerStep_isLSC f hf) (lowerStep_directed f hf)
    _ = ⨆ G : Finset ℝ≥0, choquetIntegral μ (lowerStep f hf G) :=
      iSup_congr (fun G => hfinite' _)
    _ = choquetIntegral μ f := (choquetIntegral_eq_iSup_lowerStep μ f hf).symm

end ZFCFubini
