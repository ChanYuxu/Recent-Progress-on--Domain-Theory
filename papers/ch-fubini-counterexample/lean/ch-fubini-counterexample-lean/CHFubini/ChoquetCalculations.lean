import CHFubini.Choquet

/-!
Candidate calculations from the actual Choquet layer-cake definition, together
with bounded Scott-continuous indicators for the intrinsic ORDER-product
Scott topology. No iterated integral value is assumed in these helpers.
-/

open Set Filter Topology TopologicalSpace MeasureTheory
open scoped Topology ENNReal

namespace CHFubini

universe u v

/-- Direct integration of a real superlevel cutoff against Lebesgue measure
on the nonnegative half-line. -/
theorem lintegral_unit_cutoff (q : ℝ) :
    (∫⁻ t : ℝ in Ici (0 : ℝ), if t < q then (1 : ℝ≥0∞) else 0) = ENNReal.ofReal q := by
  classical
  have he : (fun t : ℝ => if t < q then (1 : ℝ≥0∞) else 0) =
      (Iio q).indicator (fun _ => (1 : ℝ≥0∞)) := by
    funext t
    by_cases ht : t < q <;> simp [ht, Set.indicator]
  rw [he, lintegral_indicator measurableSet_Iio, setLIntegral_const,
    Measure.restrict_apply measurableSet_Iio]
  have hi : Iio q ∩ Ici (0 : ℝ) = Ico (0 : ℝ) q := by
    ext t
    simp only [mem_inter_iff, mem_Iio, mem_Ici, mem_Ico]
    exact and_comm
  rw [hi, Real.volume_Ico]
  simp

/-- The profile-calculation helper needed for the source's first outer
integral. The literal LSC strict superlevels have mass one below `q` and zero
above it. Normalization need not be assumed separately because its relevant
unit mass is already present in the displayed profile.

The statement is valid for arbitrary real `q`, hence in particular for the
source's nonnegative finite thresholds. -/
theorem choquetIntegral_eq_of_unit_superlevels
    {X : Type u} [TopologicalSpace X]
    (μ : Valuation X) (f : X → ℝ≥0∞) (hf : IsLSC f) (q : ℝ)
    (hprofile : ∀ t : ℝ, 0 ≤ t →
      μ ⟨{x | ENNReal.ofReal t < f x}, hf _⟩ = if t < q then 1 else 0) :
    choquetIntegral μ f = ENNReal.ofReal q := by
  rw [choquetIntegral_eq_layerCake μ f hf]
  calc
    (∫⁻ t : ℝ in Ici (0 : ℝ), μ ⟨{x | ENNReal.ofReal t < f x}, hf _⟩) =
        ∫⁻ t : ℝ in Ici (0 : ℝ), if t < q then (1 : ℝ≥0∞) else 0 :=
      setLIntegral_congr_fun measurableSet_Ici (fun t ht => hprofile t ht)
    _ = ENNReal.ofReal q := lintegral_unit_cutoff q

theorem isLSC_const {X : Type u} [TopologicalSpace X] (c : ℝ≥0∞) :
    IsLSC (fun _ : X => c) := by
  intro r
  by_cases hr : r < c <;> simp [hr]

/-- Constants, including infinity, integrate to themselves against a
probability valuation under the actual layer-cake definition. -/
theorem choquetIntegral_const
    {X : Type u} [TopologicalSpace X]
    (μ : Valuation X) (hμ : μ.Probability) (c : ℝ≥0∞) :
    choquetIntegral μ (fun _ : X => c) = c := by
  classical
  have htop : μ ⊤ = 1 := hμ
  by_cases hc : c = ∞
  · subst c
    have hcut (t : ℝ) :
        (⟨interior {x : X | ENNReal.ofReal t < ∞}, isOpen_interior⟩ : Opens X) = ⊤ := by
      ext x
      simp
    unfold choquetIntegral
    simp_rw [hcut, htop]
    simp [Real.volume_Ici]
  · have hprof (t : ℝ) (ht : 0 ≤ t) :
        μ ⟨{x : X | ENNReal.ofReal t < c}, isLSC_const c _⟩ =
          if t < c.toReal then 1 else 0 := by
      have hiff : ENNReal.ofReal t < c ↔ t < c.toReal :=
        ENNReal.ofReal_lt_iff_lt_toReal ht hc
      by_cases htc : t < c.toReal
      · have hopen : (⟨{x : X | ENNReal.ofReal t < c}, isLSC_const c _⟩ : Opens X) = ⊤ := by
          ext x
          change (ENNReal.ofReal t < c) ↔ True
          exact iff_true_intro (hiff.mpr htc)
        rw [hopen, htop, if_pos htc]
      · have hopen : (⟨{x : X | ENNReal.ofReal t < c}, isLSC_const c _⟩ : Opens X) = ⊥ := by
          ext x
          change (ENNReal.ofReal t < c) ↔ False
          exact iff_false_intro (fun h => htc (hiff.mp h))
        rw [hopen, μ.strict, if_neg htc]
    simpa only [ENNReal.ofReal_toReal hc] using
      choquetIntegral_eq_of_unit_superlevels μ (fun _ : X => c) (isLSC_const c) c.toReal hprof

theorem indicator_le_one {X : Type u} [TopologicalSpace X]
    (U : Opens X) (x : X) : indicator U x ≤ 1 := by
  classical
  by_cases hx : x ∈ U <;> simp [indicator, hx]

theorem indicator_isLSC {X : Type u} [TopologicalSpace X]
    (U : Opens X) : IsLSC (indicator U) := by
  classical
  intro r
  have he : {x : X | r < indicator U x} = if r < 1 then (U : Set X) else ∅ := by
    ext x
    by_cases hx : x ∈ U <;> by_cases hr : r < 1 <;> simp [indicator, hx, hr]
  rw [he]
  split_ifs
  · exact U.isOpen
  · exact isOpen_empty

/-- Characteristic functions of arbitrary full Scott opens preserve every
existing nonempty directed supremum. -/
theorem indicator_scottContinuous
    {P : Type u} [PartialOrder P] (W : ScottOpens P) :
    ScottContinuous (fun p : P => indicator W (WithScott.toScott p)) := by
  classical
  have hup : IsUpperSet (W : Set (WithScott P)) :=
    IsScott.isUpperSet_of_isOpen (D := univ) W.isOpen
  have hacc : DirSupInaccOn univ (W : Set (WithScott P)) :=
    (IsScott.isOpen_iff_isUpperSet_and_dirSupInaccOn (D := univ)).mp W.isOpen |>.2
  have hc : ScottContinuous (indicator W) := by
    intro D hn hd p hp
    by_cases hpW : p ∈ W
    · have hp1 : indicator W p = 1 := by simp [indicator, hpW]
      rw [hp1]
      refine ⟨?_, ?_⟩
      · rintro a ⟨d, _, rfl⟩
        exact indicator_le_one W d
      · intro a ha
        obtain ⟨d, hdD, hdW⟩ := hacc (mem_univ _) hn hd hp hpW
        have h := ha (mem_image_of_mem (indicator W) hdD)
        have hdW' : d ∈ W := hdW
        simpa [indicator, hdW'] using h
    · have hall : ∀ d ∈ D, indicator W d = 0 := by
        intro d hdD
        have hdW : d ∉ W := fun hw => hpW (hup (hp.1 hdD) hw)
        simp [indicator, hdW]
      have hp0 : indicator W p = 0 := by simp [indicator, hpW]
      rw [hp0]
      refine ⟨?_, ?_⟩
      · rintro a ⟨d, hdD, rfl⟩
        rw [hall d hdD]
      · intro a ha
        obtain ⟨d, hdD⟩ := hn
        simpa only [hall d hdD] using ha (mem_image_of_mem (indicator W) hdD)
  exact hc

/-- The actual order-product integrand used for the noncentrality witness. -/
noncomputable def orderIndicator
    {P : Type u} {Q : Type v} [PartialOrder P] [PartialOrder Q]
    (W : ScottOpens (P × Q)) : P × Q → ℝ≥0∞ :=
  fun z => indicator W (WithScott.toScott z)

theorem orderIndicator_scottContinuous
    {P : Type u} {Q : Type v} [PartialOrder P] [PartialOrder Q]
    (W : ScottOpens (P × Q)) : ScottContinuous (orderIndicator W) :=
  indicator_scottContinuous W

theorem orderIndicator_bounded
    {P : Type u} {Q : Type v} [PartialOrder P] [PartialOrder Q]
    (W : ScottOpens (P × Q)) : ∀ z, orderIndicator W z ≤ 1 :=
  fun z => indicator_le_one W (WithScott.toScott z)

theorem orderIndicator_leftSection
    {P : Type u} {Q : Type v} [PartialOrder P] [PartialOrder Q]
    (W : ScottOpens (P × Q)) (y : Q) :
    (fun x : WithScott P => orderIndicator W (WithScott.ofScott x, y)) =
      indicator (leftSection W y) := rfl

theorem orderIndicator_rightSection
    {P : Type u} {Q : Type v} [PartialOrder P] [PartialOrder Q]
    (W : ScottOpens (P × Q)) (x : P) :
    (fun y : WithScott Q => orderIndicator W (x, WithScott.ofScott y)) =
      indicator (rightSection W x) := rfl

/-- Transposition is the specified order-product swap, not an arbitrary
homeomorphic replacement of the Scott open. -/
def swapScottOpen
    {P : Type u} {Q : Type v} [PartialOrder P] [PartialOrder Q]
    (W : ScottOpens (P × Q)) : ScottOpens (Q × P) :=
  Opens.comap ⟨fun z : WithScott (Q × P) =>
    WithScott.toScott (Prod.swap (WithScott.ofScott z)),
    (scott_continuous_iff Prod.swap).mp (ScottContinuous.snd.prodMk ScottContinuous.fst)⟩ W

theorem orderIndicator_swap
    {P : Type u} {Q : Type v} [PartialOrder P] [PartialOrder Q]
    (W : ScottOpens (P × Q)) (z : Q × P) :
    orderIndicator (swapScottOpen W) z = orderIndicator W z.swap := rfl

theorem orderIndicator_swap_scottContinuous
    {P : Type u} {Q : Type v} [PartialOrder P] [PartialOrder Q]
    (W : ScottOpens (P × Q)) : ScottContinuous (orderIndicator (swapScottOpen W)) :=
  orderIndicator_scottContinuous _

end CHFubini

#print axioms CHFubini.choquetIntegral_eq_of_unit_superlevels
#print axioms CHFubini.choquetIntegral_const
#print axioms CHFubini.orderIndicator_scottContinuous
#print axioms CHFubini.orderIndicator_swap_scottContinuous
