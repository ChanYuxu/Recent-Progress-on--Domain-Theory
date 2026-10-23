import ZFCFubini.TopologicalFubiniRectangles

/-! Lower semicontinuity of section integration on the ordinary product.
Finite maxima are decomposed into positive open indicators by successively
removing a smallest coefficient; overlapping opens remain literal opens. -/

set_option autoImplicit false
open Set Topology TopologicalSpace MeasureTheory
open scoped ENNReal NNReal Classical
universe u v w
namespace ZFCFubini
variable {X : Type u} [TopologicalSpace X]

noncomputable def finiteStepSupport (F : Finset (OpenStep X)) : Opens X := F.sup Prod.snd

theorem finiteOpenStep_min_decomposition (F : Finset (OpenStep X)) (a : OpenStep X)
    (ha : a ∈ F) (hmin : ∀ b ∈ F, a.1 ≤ b.1) :
    finiteOpenStep F = openStep (a.1, finiteStepSupport F) +
      finiteOpenStep ((F.erase a).image (fun b => (b.1 - a.1, b.2))) := by
  let S := (F.erase a).image (fun b => (b.1 - a.1, b.2))
  funext x
  change finiteOpenStep F x = openStep (a.1, finiteStepSupport F) x + finiteOpenStep S x
  by_cases hx : x ∈ finiteStepSupport F
  · have hmle : (a.1 : ℝ≥0∞) ≤ finiteOpenStep F x := by
      obtain ⟨b, hb, hxb⟩ := (mem_finset_sup_opens F Prod.snd x).mp hx
      have hle : openStep b ≤ finiteOpenStep F := Finset.le_sup hb
      exact (ENNReal.coe_le_coe.mpr (hmin b hb)).trans
        (by simpa [openStep, hxb] using hle x)
    rw [show openStep (a.1, finiteStepSupport F) x = (a.1 : ℝ≥0∞) by
      simp only [openStep, Set.indicator_of_mem (show x ∈ (finiteStepSupport F : Set X) from hx)]]
    apply le_antisymm
    · simp only [finiteOpenStep, Finset.sup_apply]
      apply Finset.sup_le
      intro b hb
      by_cases hxb : x ∈ (b.2 : Set X)
      · rw [show openStep b x = (b.1 : ℝ≥0∞) by simp only [openStep, Set.indicator_of_mem hxb]]
        by_cases hba : b = a
        · subst b
          exact le_self_add
        · have hbS : (b.1 - a.1, b.2) ∈ S :=
            Finset.mem_image_of_mem _ (Finset.mem_erase.mpr ⟨hba, hb⟩)
          have hle : openStep (b.1 - a.1, b.2) ≤ finiteOpenStep S := Finset.le_sup hbS
          have hbsub : ((b.1 - a.1 : ℝ≥0) : ℝ≥0∞) ≤ finiteOpenStep S x := by
            simpa [openStep, hxb] using hle x
          have he : (b.1 : ℝ≥0∞) = (a.1 : ℝ≥0∞) + ((b.1 - a.1 : ℝ≥0) : ℝ≥0∞) := by
            rw [← ENNReal.coe_add, add_tsub_cancel_of_le (hmin b hb)]
          rw [he]
          exact add_le_add le_rfl (by simpa only [finiteOpenStep, Finset.sup_apply] using hbsub)
      · simp [openStep, hxb]
    · have hS : finiteOpenStep S x ≤ finiteOpenStep F x - (a.1 : ℝ≥0∞) := by
        simp only [finiteOpenStep, Finset.sup_apply]
        apply Finset.sup_le
        rintro b hb
        obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hb
        by_cases hxd : x ∈ (d.2 : Set X)
        · rw [show openStep (d.1 - a.1, d.2) x = ((d.1 - a.1 : ℝ≥0) : ℝ≥0∞) from
            by simp only [openStep, Set.indicator_of_mem hxd], ENNReal.coe_sub]
          have hle : openStep d ≤ finiteOpenStep F := Finset.le_sup (Finset.mem_of_mem_erase hd)
          apply tsub_le_tsub_right
          simpa [openStep, finiteOpenStep, Finset.sup_apply, hxd] using hle x
        · simp [openStep, hxd]
      calc
        (a.1 : ℝ≥0∞) + finiteOpenStep S x ≤
            (a.1 : ℝ≥0∞) + (finiteOpenStep F x - (a.1 : ℝ≥0∞)) := add_le_add le_rfl hS
        _ = finiteOpenStep F x := by rw [add_comm, tsub_add_cancel_of_le hmle]
  · have hxF (b : OpenStep X) (hb : b ∈ F) : x ∉ (b.2 : Set X) := by
      intro hxb
      exact hx ((mem_finset_sup_opens F Prod.snd x).mpr ⟨b, hb, hxb⟩)
    have hleft : finiteOpenStep F x = 0 := by
      apply le_antisymm _ (zero_le _)
      simp only [finiteOpenStep, Finset.sup_apply]
      apply Finset.sup_le
      intro b hb
      simp only [openStep, Set.indicator_of_notMem (hxF b hb), le_refl]
    have hright : finiteOpenStep S x = 0 := by
      apply le_antisymm _ (zero_le _)
      simp only [finiteOpenStep, Finset.sup_apply]
      apply Finset.sup_le
      rintro b hb
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hb
      simp only [openStep, Set.indicator_of_notMem (hxF d (Finset.mem_of_mem_erase hd)), le_refl]
    rw [hleft, hright, add_zero]
    simp only [openStep, Set.indicator_of_notMem (show x ∉ (finiteStepSupport F : Set X) from hx)]

variable {Y : Type v} [TopologicalSpace Y]

theorem IsLSC.section_right {f : X × Y → ℝ≥0∞} (hf : IsLSC f) (x : X) :
    IsLSC (fun y => f (x, y)) := hf.comp _ (continuous_const.prodMk continuous_id)

theorem IsLSC.section_left {f : X × Y → ℝ≥0∞} (hf : IsLSC f) (y : Y) :
    IsLSC (fun x => f (x, y)) := hf.comp _ (continuous_id.prodMk continuous_const)

theorem choquetIntegral_openStep_section (ν : Valuation Y) (a : OpenStep (X × Y)) (x : X) :
    choquetIntegral ν (fun y => openStep a (x, y)) = (a.1 : ℝ≥0∞) * ν (openSection a.2 x) := by
  exact choquetIntegral_indicator_nnreal ν (openSection a.2 x) a.1

theorem finiteOpenStep_integral_sections_isLSC (ν : Valuation Y) (hν : ν.Subprobability)
    (F : Finset (OpenStep (X × Y))) :
    IsLSC (fun x => choquetIntegral ν (fun y => finiteOpenStep F (x, y))) := by
  have hfinite (n : ℕ) : ∀ F : Finset (OpenStep (X × Y)), F.card = n →
      IsLSC (fun x => choquetIntegral ν (fun y => finiteOpenStep F (x, y))) := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro F hn
      by_cases hF : F = ∅
      · subst F
        simpa [finiteOpenStep, choquetIntegral_zero] using (IsLSC.const (X := X) 0)
      obtain ⟨a, ha, hmin⟩ := F.exists_min_image Prod.fst (Finset.nonempty_iff_ne_empty.mpr hF)
      let S := (F.erase a).image (fun b => (b.1 - a.1, b.2))
      have hSn : S.card < n := (Finset.card_image_le).trans_lt
        (by simpa only [← hn] using Finset.card_erase_lt_of_mem ha)
      have hS := ih S.card hSn S rfl
      have he (x : X) : choquetIntegral ν (fun y => finiteOpenStep F (x, y)) =
          (a.1 : ℝ≥0∞) * ν (openSection (finiteStepSupport F) x) +
            choquetIntegral ν (fun y => finiteOpenStep S (x, y)) := by
        have hfun : (fun y => finiteOpenStep F (x, y)) =
            (fun y => openStep (a.1, finiteStepSupport F) (x, y)) +
              (fun y => finiteOpenStep S (x, y)) := by
          funext y
          exact congrFun (finiteOpenStep_min_decomposition F a ha hmin) (x, y)
        rw [hfun, choquetIntegral_add ν hν
          ((openStep_isLSC _).section_right x) ((finiteOpenStep_isLSC S).section_right x),
          choquetIntegral_openStep_section]
      simp_rw [he]
      exact ((valuation_openSection_isLSC ν _).mul_const a.1).add hS
  exact hfinite F.card F rfl

theorem choquetIntegral_sections_isLSC (ν : Valuation Y) (hν : ν.Subprobability)
    (f : X × Y → ℝ≥0∞) (hf : IsLSC f) :
    IsLSC (fun x => choquetIntegral ν (fun y => f (x, y))) := by
  have he (x : X) : choquetIntegral ν (fun y => f (x, y)) =
      ⨆ F : Finset ℝ≥0, choquetIntegral ν (fun y => lowerStep f hf F (x, y)) := by
    have hfun : (fun y => f (x, y)) = fun y => ⨆ F : Finset ℝ≥0, lowerStep f hf F (x, y) :=
      funext (fun y => (iSup_lowerStep f hf (x, y)).symm)
    have hd : Directed (· ≤ ·) (fun F : Finset ℝ≥0 => fun y => lowerStep f hf F (x, y)) := by
      intro F G
      obtain ⟨H, hFH, hGH⟩ := lowerStep_directed f hf F G
      exact ⟨H, fun y => hFH (x, y), fun y => hGH (x, y)⟩
    rw [hfun]
    exact choquetIntegral_iSup ν _ (fun F => (lowerStep_isLSC f hf F).section_right x) hd
  simp_rw [he]
  exact IsLSC.iSup _ (fun F => finiteOpenStep_integral_sections_isLSC ν hν _)

end ZFCFubini
