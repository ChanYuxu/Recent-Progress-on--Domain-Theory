import CantorFubini.Foundations
import Mathlib.Topology.Semicontinuity.Lindelof
import Mathlib.MeasureTheory.Integral.Layercake

/-!
The nonnegative Choquet integral of a continuous valuation.  The measure in
the defining integral is Lebesgue measure on the REAL threshold parameter;
no measure extension of the valuation on its original space is assumed.
The interior only totalizes the definition outside its LSC domain.
-/

set_option autoImplicit false
open Set Topology TopologicalSpace MeasureTheory
open scoped ENNReal
universe u v w

namespace CantorFubini

def IsVLSC {X : Type u} [TopologicalSpace X] (f : X → ℝ≥0∞) : Prop :=
  ∀ a : ℝ≥0∞, IsOpen {x | a < f x}

theorem isVLSC_iff_lowerSemicontinuous {X : Type u} [TopologicalSpace X]
    {f : X → ℝ≥0∞} : IsVLSC f ↔ LowerSemicontinuous f := by
  exact lowerSemicontinuous_iff_isOpen_preimage.symm

theorem IsVLSC.lowerSemicontinuous {X : Type u} [TopologicalSpace X]
    {f : X → ℝ≥0∞} (hf : IsVLSC f) : LowerSemicontinuous f :=
  isVLSC_iff_lowerSemicontinuous.mp hf

theorem LowerSemicontinuous.isVLSC {X : Type u} [TopologicalSpace X]
    {f : X → ℝ≥0∞} (hf : LowerSemicontinuous f) : IsVLSC f :=
  isVLSC_iff_lowerSemicontinuous.mpr hf

noncomputable def vLevel {X : Type u} [TopologicalSpace X]
    (f : X → ℝ≥0∞) (a : ℝ≥0∞) : Opens X :=
  ⟨interior {x | a < f x}, isOpen_interior⟩

theorem vLevel_eq {X : Type u} [TopologicalSpace X]
    {f : X → ℝ≥0∞} (hf : IsVLSC f) (a : ℝ≥0∞) :
    vLevel f a = ⟨{x | a < f x}, hf a⟩ :=
  Opens.ext (hf a).interior_eq

theorem vLevel_mono {X : Type u} [TopologicalSpace X]
    {f g : X → ℝ≥0∞} (hfg : f ≤ g) (a : ℝ≥0∞) :
    vLevel f a ≤ vLevel g a :=
  interior_mono (fun x hx => lt_of_lt_of_le hx (hfg x))

noncomputable def vLevelMass {X : Type u} [TopologicalSpace X]
    (μ : Valuation X) (f : X → ℝ≥0∞) (t : ℝ) : ℝ≥0∞ :=
  μ (vLevel f (ENNReal.ofReal t))

noncomputable def vIntegral {X : Type u} [TopologicalSpace X]
    (μ : Valuation X) (f : X → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ t : ℝ in Ioi 0, vLevelMass μ f t

theorem vIntegral_eq_strictLevels {X : Type u} [TopologicalSpace X]
    (μ : Valuation X) {f : X → ℝ≥0∞} (hf : IsVLSC f) :
    vIntegral μ f = ∫⁻ t : ℝ in Ioi 0,
      μ ⟨{x | ENNReal.ofReal t < f x}, hf (ENNReal.ofReal t)⟩ := by
  simp only [vIntegral, vLevelMass, vLevel_eq hf]

theorem vLevelMass_antitone {X : Type u} [TopologicalSpace X]
    (μ : Valuation X) (f : X → ℝ≥0∞) : Antitone (vLevelMass μ f) := by
  intro a b hab
  apply μ.mono
  exact interior_mono (fun x hx => lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hab) hx)

theorem vLevelMass_measurable {X : Type u} [TopologicalSpace X]
    (μ : Valuation X) (f : X → ℝ≥0∞) : Measurable (vLevelMass μ f) :=
  (vLevelMass_antitone μ f).measurable

theorem vIntegral_mono {X : Type u} [TopologicalSpace X]
    (μ : Valuation X) {f g : X → ℝ≥0∞} (hfg : f ≤ g) :
    vIntegral μ f ≤ vIntegral μ g :=
  lintegral_mono (fun _ => μ.mono (vLevel_mono hfg _))

@[simp] theorem vIntegral_zero {X : Type u} [TopologicalSpace X]
    (μ : Valuation X) : vIntegral μ (fun _ => 0) = 0 := by
  have h (a : ℝ≥0∞) : vLevel (fun _ : X => 0) a = ⊥ := by
    ext x
    simp [vLevel]
  simp [vIntegral, vLevelMass, h, μ.strict]

theorem isVLSC_const {X : Type u} [TopologicalSpace X] (c : ℝ≥0∞) :
    IsVLSC (fun _ : X => c) := by
  exact isVLSC_iff_lowerSemicontinuous.mpr lowerSemicontinuous_const

theorem isVLSC_indicator {X : Type u} [TopologicalSpace X]
    (U : Opens X) (c : ℝ≥0∞) : IsVLSC ((U : Set X).indicator (fun _ => c)) :=
  isVLSC_iff_lowerSemicontinuous.mpr
    (U.isOpen.lowerSemicontinuous_indicator (zero_le c))

theorem IsVLSC.add {X : Type u} [TopologicalSpace X]
    {f g : X → ℝ≥0∞} (hf : IsVLSC f) (hg : IsVLSC g) :
    IsVLSC (fun x => f x + g x) :=
  isVLSC_iff_lowerSemicontinuous.mpr
    (hf.lowerSemicontinuous.add hg.lowerSemicontinuous)

theorem isVLSC_iSup {X : Type u} [TopologicalSpace X] {ι : Type v}
    (f : ι → X → ℝ≥0∞) (hf : ∀ i, IsVLSC (f i)) :
    IsVLSC (fun x => ⨆ i, f i x) := by
  intro a
  have he : {x | a < ⨆ i, f i x} = ⋃ i, {x | a < f i x} := by
    ext x
    simp only [mem_setOf_eq, mem_iUnion, lt_iSup_iff]
  rw [he]
  exact isOpen_iUnion (fun i => hf i a)

def positiveThreshold (c : ℝ≥0∞) : Set ℝ :=
  {t | 0 < t ∧ ENNReal.ofReal t < c}

theorem positiveThreshold_isOpen (c : ℝ≥0∞) : IsOpen (positiveThreshold c) :=
  isOpen_Ioi.inter (isOpen_lt ENNReal.continuous_ofReal continuous_const)

theorem volume_positiveThreshold (c : ℝ≥0∞) : volume (positiveThreshold c) = c := by
  by_cases hc : c = ∞
  · subst c
    have he : positiveThreshold ∞ = Ioi (0 : ℝ) := by
      ext t
      simp [positiveThreshold]
    rw [he, Real.volume_Ioi]
  · have he : positiveThreshold c = Ioo (0 : ℝ) c.toReal := by
      ext t
      simp only [positiveThreshold, mem_setOf_eq, mem_Ioo]
      exact and_congr_right (fun ht => ENNReal.ofReal_lt_iff_lt_toReal ht.le hc)
    rw [he, Real.volume_Ioo, sub_zero, ENNReal.ofReal_toReal hc]

theorem vLevelMass_indicator {X : Type u} [TopologicalSpace X]
    (μ : Valuation X) (U : Opens X) (c : ℝ≥0∞) (t : ℝ) :
    vLevelMass μ ((U : Set X).indicator (fun _ => c)) t =
      if ENNReal.ofReal t < c then μ U else 0 := by
  rw [vLevelMass, vLevel_eq (isVLSC_indicator U c)]
  split_ifs with h
  · congr 1
    ext x
    by_cases hx : x ∈ U <;> simp [hx, h]
  · have he : (⟨{x | ENNReal.ofReal t < (U : Set X).indicator (fun _ => c) x},
        isVLSC_indicator U c (ENNReal.ofReal t)⟩ : Opens X) = ⊥ := by
      ext x
      by_cases hx : x ∈ U <;> simp [hx, h]
    rw [he, μ.strict]

theorem vIntegral_indicator {X : Type u} [TopologicalSpace X]
    (μ : Valuation X) (U : Opens X) (c : ℝ≥0∞) :
    vIntegral μ ((U : Set X).indicator (fun _ => c)) = c * μ U := by
  have he : (Ioi (0 : ℝ)).indicator
      (vLevelMass μ ((U : Set X).indicator (fun _ => c))) =
      (positiveThreshold c).indicator (fun _ => μ U) := by
    funext t
    by_cases ht : 0 < t <;> by_cases hc : ENNReal.ofReal t < c <;>
      simp [ht, hc, positiveThreshold, vLevelMass_indicator]
  calc
    vIntegral μ ((U : Set X).indicator (fun _ => c)) =
        ∫⁻ t : ℝ, (positiveThreshold c).indicator (fun _ => μ U) t := by
      rw [vIntegral, ← lintegral_indicator measurableSet_Ioi, he]
    _ = μ U * volume (positiveThreshold c) := by
      rw [lintegral_indicator (positiveThreshold_isOpen c).measurableSet]
      simp
    _ = c * μ U := by rw [volume_positiveThreshold, mul_comm]

@[simp] theorem vIntegral_const {X : Type u} [TopologicalSpace X]
    (μ : Valuation X) (c : ℝ≥0∞) : vIntegral μ (fun _ => c) = c * μ ⊤ := by
  simpa using vIntegral_indicator μ ⊤ c

theorem vLevel_eq_iSup_right {X : Type u} [TopologicalSpace X]
    {f : X → ℝ≥0∞} (hf : IsVLSC f) (t : ℝ) :
    vLevel f (ENNReal.ofReal t) =
      ⨆ r : Ioi t, vLevel f (ENNReal.ofReal (r : ℝ)) := by
  apply Opens.ext
  ext x
  simp only [vLevel_eq hf, Opens.coe_mk, Opens.coe_iSup, mem_setOf_eq, mem_iUnion]
  constructor
  · intro hx
    obtain ⟨r, htr, hrx⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hx
    have htr' : t < (r : ℝ) :=
      (ENNReal.ofReal_lt_ofReal_iff'.mp (by simpa using htr)).1
    exact ⟨⟨r, htr'⟩, by simpa using hrx⟩
  · rintro ⟨r, hr⟩
    exact lt_of_le_of_lt (ENNReal.ofReal_le_ofReal r.property.le) hr

theorem vLevelMass_eq_iSup_right {X : Type u} [TopologicalSpace X]
    (μ : Valuation X) {f : X → ℝ≥0∞} (hf : IsVLSC f) (t : ℝ) :
    vLevelMass μ f t = ⨆ r : Ioi t, vLevelMass μ f (r : ℝ) := by
  have : Nonempty (Ioi t) := ⟨⟨t + 1, by simp⟩⟩
  rw [vLevelMass, vLevel_eq_iSup_right hf t, μ.map_iSup]
  · rfl
  · intro a b
    refine ⟨⟨min a.val b.val, ?_⟩, ?_, ?_⟩
    · change t < min a.val b.val
      exact lt_min_iff.mpr ⟨(show t < a.val from a.property),
        (show t < b.val from b.property)⟩
    · exact interior_mono (fun _ hx =>
        lt_of_le_of_lt (ENNReal.ofReal_le_ofReal (min_le_left _ _)) hx)
    · exact interior_mono (fun _ hx =>
        lt_of_le_of_lt (ENNReal.ofReal_le_ofReal (min_le_right _ _)) hx)

theorem vLevelMass_lowerSemicontinuous {X : Type u} [TopologicalSpace X]
    (μ : Valuation X) {f : X → ℝ≥0∞} (hf : IsVLSC f) :
    LowerSemicontinuous (vLevelMass μ f) := by
  intro t a ha
  change a < vLevelMass μ f t at ha
  rw [vLevelMass_eq_iSup_right μ hf t] at ha
  obtain ⟨r, hr⟩ := lt_iSup_iff.mp ha
  filter_upwards [Iio_mem_nhds r.property] with s hs
  exact hr.trans_le ((vLevelMass_antitone μ f) hs.le)

/-- Monotone convergence for an arbitrary directed family of LSC functions
on the second-countable real threshold space.  Countability is derived here,
not imposed on the family being integrated. -/
theorem lintegral_iSup_lsc_directed {ι : Type v} [Nonempty ι]
    (f : ι → ℝ → ℝ≥0∞) (hf : ∀ i, LowerSemicontinuous (f i))
    (hd : Directed (· ≤ ·) f) (m : Measure ℝ) :
    (∫⁻ t, ⨆ i, f i t ∂m) = ⨆ i, ∫⁻ t, f i t ∂m := by
  classical
  obtain ⟨S, hS, hSc, hSlub⟩ := exists_countable_lowerSemicontinuous_isLUB
    (𝓕 := Set.range f) (s := fun t => ⨆ i, f i t)
    (by rintro g ⟨i, rfl⟩; exact hf i)
    (by
      convert (isLUB_iSup (f := f)) using 1
      ext t
      simp only [iSup_apply])
  letI : Countable S := hSc.to_subtype
  have hseq : (fun t => ⨆ i, f i t) = ⨆ s : S, s.val := by
    exact hSlub.unique (by
      simpa only [Subtype.range_coe] using
        (isLUB_iSup (f := fun s : S => s.val)))
  choose index hindex using (fun s : S => hS s.property)
  let F (A : Finset S) : ℝ → ℝ≥0∞ := fun t => ⨆ s ∈ A, s.val t
  have hFmeas (A : Finset S) : Measurable (F A) := by
    apply Measurable.iSup
    intro s
    apply Measurable.iSup
    intro _
    rw [← hindex s]
    exact (hf (index s)).measurable
  have hFdir : Directed (· ≤ ·) F := by
    intro A B
    refine ⟨A ∪ B, ?_, ?_⟩
    · intro t
      exact iSup_le (fun s => iSup_le (fun hs =>
        le_iSup_of_le s (le_iSup_of_le (Finset.mem_union_left B hs) le_rfl)))
    · intro t
      exact iSup_le (fun s => iSup_le (fun hs =>
        le_iSup_of_le s (le_iSup_of_le (Finset.mem_union_right A hs) le_rfl)))
  have hFF : (fun t => ⨆ i, f i t) = fun t => ⨆ A, F A t := by
    funext t
    have he := congrFun hseq t
    simp only [iSup_apply] at he
    rw [he, iSup_eq_iSup_finset]
  apply le_antisymm
  · calc
      (∫⁻ t, ⨆ i, f i t ∂m) = ∫⁻ t, ⨆ A, F A t ∂m := by rw [← hFF]
      _ = ⨆ A, ∫⁻ t, F A t ∂m :=
        lintegral_iSup_directed_of_measurable hFmeas hFdir
      _ ≤ ⨆ i, ∫⁻ t, f i t ∂m := by
        refine iSup_le (fun A => ?_)
        obtain ⟨i, hi⟩ := hd.finset_le (A.image index)
        refine le_iSup_of_le i (lintegral_mono (fun t => ?_))
        refine iSup_le (fun s => iSup_le (fun hs => ?_))
        rw [← hindex s]
        exact hi (index s) (Finset.mem_image_of_mem index hs) t
  · exact iSup_le (fun i => lintegral_mono (fun t => le_iSup (fun i => f i t) i))

theorem vLevel_iSup {X : Type u} [TopologicalSpace X] {ι : Type v}
    (f : ι → X → ℝ≥0∞) (hf : ∀ i, IsVLSC (f i)) (a : ℝ≥0∞) :
    vLevel (fun x => ⨆ i, f i x) a = ⨆ i, vLevel (f i) a := by
  apply Opens.ext
  ext x
  simp only [vLevel_eq (isVLSC_iSup f hf), vLevel_eq (hf _),
    Opens.coe_mk, Opens.coe_iSup, mem_setOf_eq, mem_iUnion, lt_iSup_iff]

theorem vIntegral_iSup_directed {X : Type u} [TopologicalSpace X]
    {ι : Type v} [Nonempty ι] (μ : Valuation X) (f : ι → X → ℝ≥0∞)
    (hf : ∀ i, IsVLSC (f i)) (hd : Directed (· ≤ ·) f) :
    vIntegral μ (fun x => ⨆ i, f i x) = ⨆ i, vIntegral μ (f i) := by
  have hlevel (t : ℝ) : vLevelMass μ (fun x => ⨆ i, f i x) t =
      ⨆ i, vLevelMass μ (f i) t := by
    rw [vLevelMass, vLevel_iSup f hf, μ.map_iSup]
    · rfl
    · intro i j
      obtain ⟨k, hik, hjk⟩ := hd i j
      exact ⟨k, vLevel_mono hik _, vLevel_mono hjk _⟩
  unfold vIntegral
  simp only [hlevel]
  apply lintegral_iSup_lsc_directed
  · exact fun i => vLevelMass_lowerSemicontinuous μ (hf i)
  · intro i j
    obtain ⟨k, hik, hjk⟩ := hd i j
    exact ⟨k, (fun t => μ.mono (vLevel_mono hik _)),
      (fun t => μ.mono (vLevel_mono hjk _))⟩

theorem vIntegral_iSup_valuation {X : Type u} [TopologicalSpace X]
    {ι : Type v} [Nonempty ι] (μ : ι → Valuation X) (ν : Valuation X)
    (hd : Directed (· ≤ ·) (fun i => (μ i).mass))
    (hν : ∀ U, ν U = ⨆ i, μ i U) {f : X → ℝ≥0∞} (hf : IsVLSC f) :
    vIntegral ν f = ⨆ i, vIntegral (μ i) f := by
  unfold vIntegral vLevelMass
  simp only [hν]
  apply lintegral_iSup_lsc_directed
  · exact fun i => vLevelMass_lowerSemicontinuous (μ i) hf
  · intro i j
    obtain ⟨k, hik, hjk⟩ := hd i j
    exact ⟨k, (fun t => hik (vLevel f (ENNReal.ofReal t))),
      (fun t => hjk (vLevel f (ENNReal.ofReal t)))⟩

theorem IsVLSC.comp_continuous {X : Type u} [TopologicalSpace X]
    {Y : Type v} [TopologicalSpace Y] {g : Y → ℝ≥0∞} (hg : IsVLSC g)
    (f : X → Y) (hf : Continuous f) : IsVLSC (g ∘ f) :=
  fun a => (hg a).preimage hf

theorem vIntegral_push {X : Type u} [TopologicalSpace X]
    {Y : Type v} [TopologicalSpace Y] (μ : Valuation X)
    (f : X → Y) (hf : Continuous f) {g : Y → ℝ≥0∞} (hg : IsVLSC g) :
    vIntegral (μ.push f hf) g = vIntegral μ (g ∘ f) := by
  rw [vIntegral_eq_strictLevels _ hg,
    vIntegral_eq_strictLevels _ (hg.comp_continuous f hf)]
  apply lintegral_congr
  intro t
  rw [Valuation.push_apply]
  congr 1

theorem vIntegral_of_dirac_mass {X : Type u} [TopologicalSpace X]
    (μ : Valuation X) (x : X)
    (hμ : ∀ U : Opens X, μ U = (U : Set X).indicator (fun _ => 1) x)
    {f : X → ℝ≥0∞} (hf : IsVLSC f) : vIntegral μ f = f x := by
  classical
  have he : (Ioi (0 : ℝ)).indicator (vLevelMass μ f) =
      (positiveThreshold (f x)).indicator (fun _ => (1 : ℝ≥0∞)) := by
    funext t
    by_cases ht : 0 < t <;> by_cases hx : ENNReal.ofReal t < f x <;>
      simp [vLevelMass, vLevel_eq hf, hμ, ht, hx, positiveThreshold]
  rw [vIntegral, ← lintegral_indicator measurableSet_Ioi, he,
    lintegral_indicator (positiveThreshold_isOpen (f x)).measurableSet]
  simp [volume_positiveThreshold]

theorem IsVLSC.const_mul {X : Type u} [TopologicalSpace X]
    {f : X → ℝ≥0∞} (hf : IsVLSC f) (c : ℝ≥0∞) :
    IsVLSC (fun x => c * f x) := by
  by_cases hc0 : c = 0
  · subst c
    simpa using (isVLSC_const (X := X) 0)
  by_cases hct : c = ∞
  · subst c
    intro a
    by_cases hat : a = ∞
    · subst a
      simpa using (isOpen_empty : IsOpen (∅ : Set X))
    · have he : {x | a < ∞ * f x} = {x | 0 < f x} := by
        ext x
        by_cases hx : f x = 0
        · simp [hx]
        · simp [ENNReal.top_mul hx, lt_top_iff_ne_top, hat, pos_iff_ne_zero, hx]
      rw [he]
      exact hf 0
  · intro a
    have he : {x | a < c * f x} = {x | a / c < f x} := by
      ext x
      simpa only [mul_comm] using
        (ENNReal.div_lt_iff (a := f x) (b := c) (c := a)
          (Or.inl hc0) (Or.inl hct)).symm
    rw [he]
    exact hf (a / c)

theorem IsVLSC.mul_const {X : Type u} [TopologicalSpace X]
    {f : X → ℝ≥0∞} (hf : IsVLSC f) (c : ℝ≥0∞) :
    IsVLSC (fun x => f x * c) := by
  simpa only [mul_comm] using hf.const_mul c

theorem vIntegral_const_mul_of_ne_top {X : Type u} [TopologicalSpace X]
    (μ : Valuation X) (c : ℝ≥0∞) (hct : c ≠ ∞) (f : X → ℝ≥0∞) :
    vIntegral μ (fun x => c * f x) = c * vIntegral μ f := by
  classical
  by_cases hc0 : c = 0
  · subst c
    simp
  let a : ℝ := c.toReal
  have ha : 0 < a := ENNReal.toReal_pos hc0 hct
  have hca : ENNReal.ofReal a = c := ENNReal.ofReal_toReal hct
  let H : ℝ → ℝ≥0∞ := (Ioi 0).indicator (vLevelMass μ f)
  have hH : Measurable H := (vLevelMass_measurable μ f).indicator measurableSet_Ioi
  have hl (t : ℝ) :
      vLevelMass μ (fun x => c * f x) t = vLevelMass μ f (a⁻¹ * t) := by
    unfold vLevelMass
    congr 1
    apply Opens.ext
    change interior {x | ENNReal.ofReal t < c * f x} =
      interior {x | ENNReal.ofReal (a⁻¹ * t) < f x}
    congr 1
    ext x
    have he : ENNReal.ofReal (a⁻¹ * t) = ENNReal.ofReal t / c := by
      rw [mul_comm, ← div_eq_mul_inv, ENNReal.ofReal_div_of_pos ha, hca]
    rw [he]
    simpa only [mul_comm] using
      (ENNReal.div_lt_iff (a := f x) (b := c) (c := ENNReal.ofReal t)
        (Or.inl hc0) (Or.inl hct)).symm
  have hfun : (Ioi (0 : ℝ)).indicator
      (vLevelMass μ (fun x => c * f x)) = fun t => H (a⁻¹ * t) := by
    funext t
    by_cases ht : 0 < t
    · have ht' : 0 < a⁻¹ * t := mul_pos (inv_pos.mpr ha) ht
      simp [H, ht, ht', hl]
    · have ht' : ¬0 < a⁻¹ * t := not_lt.mpr
        (mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr ha.le) (not_lt.mp ht))
      simp [H, ht, ht']
  calc
    vIntegral μ (fun x => c * f x) = ∫⁻ t, H (a⁻¹ * t) := by
      rw [vIntegral, ← lintegral_indicator measurableSet_Ioi, hfun]
    _ = ∫⁻ t, H t ∂Measure.map (fun t : ℝ => a⁻¹ * t) volume :=
      (lintegral_map hH (measurable_const_mul _)).symm
    _ = c * ∫⁻ t, H t := by
      rw [Real.map_volume_mul_left (inv_ne_zero ha.ne'), lintegral_smul_measure]
      simp only [inv_inv, abs_of_pos ha, hca, smul_eq_mul]
    _ = c * vIntegral μ f := by
      simp only [H, lintegral_indicator measurableSet_Ioi, vIntegral]

theorem vIntegral_const_mul {X : Type u} [TopologicalSpace X]
    (μ : Valuation X) (c : ℝ≥0∞) {f : X → ℝ≥0∞} (hf : IsVLSC f) :
    vIntegral μ (fun x => c * f x) = c * vIntegral μ f := by
  by_cases hct : c = ∞
  · subst c
    have he : (fun x => (∞ : ℝ≥0∞) * f x) =
        fun x => ⨆ n : ℕ, (n : ℝ≥0∞) * f x := by
      funext x
      rw [← ENNReal.iSup_natCast, ENNReal.iSup_mul]
    have hd : Directed (· ≤ ·) (fun n : ℕ => fun x => (n : ℝ≥0∞) * f x) := by
      intro i j
      exact ⟨max i j, (fun x => mul_le_mul_left
          (show (i : ℝ≥0∞) ≤ (max i j : ℕ) from Nat.cast_le.mpr (le_max_left i j)) (f x)),
        (fun x => mul_le_mul_left
          (show (j : ℝ≥0∞) ≤ (max i j : ℕ) from Nat.cast_le.mpr (le_max_right i j)) (f x))⟩
    rw [he, vIntegral_iSup_directed μ (fun n : ℕ => fun x => (n : ℝ≥0∞) * f x)
      (fun n => hf.const_mul (n : ℝ≥0∞)) hd]
    have hn (n : ℕ) : vIntegral μ (fun x => (n : ℝ≥0∞) * f x) =
        (n : ℝ≥0∞) * vIntegral μ f :=
      vIntegral_const_mul_of_ne_top μ n (by simp) f
    simp only [hn, ← ENNReal.iSup_mul, ENNReal.iSup_natCast]
  · exact vIntegral_const_mul_of_ne_top μ c hct f

theorem vIntegral_mul_const {X : Type u} [TopologicalSpace X]
    (μ : Valuation X) (c : ℝ≥0∞) {f : X → ℝ≥0∞} (hf : IsVLSC f) :
    vIntegral μ (fun x => f x * c) = vIntegral μ f * c := by
  simpa only [mul_comm] using vIntegral_const_mul μ c hf

end CantorFubini
