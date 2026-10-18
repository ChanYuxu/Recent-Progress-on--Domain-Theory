import PointCentralFubini.OpenFubini
import Mathlib.Topology.Semicontinuity.Basic

/-! Finite sums and bounds for the Choquet integral used in Section 4. -/
set_option autoImplicit false
open Set Topology TopologicalSpace MeasureTheory
open scoped ENNReal BigOperators
universe u v
namespace PointCentralFubini

theorem isLSC_const {X : Type u} [TopologicalSpace X] (c : ℝ≥0∞) :
    IsLSC (fun _ : X => c) := by
  intro r
  by_cases h : r < c <;> simp [h]

theorem IsLSC.add {X : Type u} [TopologicalSpace X] {f g : X → ℝ≥0∞}
    (hf : IsLSC f) (hg : IsLSC g) : IsLSC (f+g) := by
  exact lowerSemicontinuous_iff_isOpen_preimage.mp
    ((lowerSemicontinuous_iff_isOpen_preimage.mpr hf).add
      (lowerSemicontinuous_iff_isOpen_preimage.mpr hg))

theorem IsLSC.finset_sum {X : Type u} [TopologicalSpace X] {ι : Type v}
    (s : Finset ι) (f : ι → X → ℝ≥0∞) (hf : ∀ i ∈ s, IsLSC (f i)) :
    IsLSC (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isLSC_const (X := X) 0
  | @insert i s hi ih =>
    simpa only [Finset.sum_insert hi] using
      (hf i (Finset.mem_insert_self i s)).add
        (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

theorem integral_const {X : Type u} [TopologicalSpace X] (μ : Valuation X) (c : ℝ≥0∞) :
    integral μ (fun _ => c) = c * μ ⊤ := by
  have hi : indicator (⊤ : Opens X) = fun _ => (1 : ℝ≥0∞) := by
    classical
    funext x; simp [indicator]
  have h := fpr_integral_smul μ c (fun _ => 1) (isLSC_const 1)
  simpa only [mul_one,← hi,integral_indicator] using h

theorem integral_zero {X : Type u} [TopologicalSpace X] (μ : Valuation X) :
    integral μ (fun _ => 0) = 0 := by rw [integral_const,zero_mul]

theorem integral_finset_sum {X : Type u} [TopologicalSpace X] {ι : Type v}
    (μ : Valuation X) (s : Finset ι) (f : ι → X → ℝ≥0∞)
    (hf : ∀ i ∈ s, IsLSC (f i)) :
    integral μ (fun x => ∑ i ∈ s, f i x) = ∑ i ∈ s, integral μ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using integral_zero μ
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    rw [show (fun x => f i x + ∑ j ∈ s, f j x) = f i + (fun x => ∑ j ∈ s, f j x) from rfl,
      fpr_integral_add μ _ _ (hf i (Finset.mem_insert_self i s))
        (IsLSC.finset_sum s f (fun j hj => hf j (Finset.mem_insert_of_mem hj))),
      ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))]

theorem integral_le_const {X : Type u} [TopologicalSpace X] (μ : Valuation X)
    {f : X → ℝ≥0∞} {c : ℝ≥0∞} (hf : ∀ x, f x ≤ c) : integral μ f ≤ c * μ ⊤ := by
  exact (integral_mono μ hf).trans_eq (integral_const μ c)

theorem scottContinuous_add {P : Type u} [Preorder P] {f g : P → ℝ≥0∞}
    (hf : ScottContinuous f) (hg : ScottContinuous g) : ScottContinuous (f+g) := by
  exact (isLSC_scott_iff (fun x => f (WithScott.ofScott x) + g (WithScott.ofScott x))).mp
    ((scott_isLSC hf).add (scott_isLSC hg))

theorem scottContinuous_finset_sum {P : Type u} [Preorder P] {ι : Type v}
    (s : Finset ι) (f : ι → P → ℝ≥0∞) (hf : ∀ i ∈ s, ScottContinuous (f i)) :
    ScottContinuous (fun x => ∑ i ∈ s, f i x) :=
  (isLSC_scott_iff (fun x => ∑ i ∈ s, f i (WithScott.ofScott x))).mp
    (IsLSC.finset_sum s _ (fun i hi => scott_isLSC (hf i hi)))

end PointCentralFubini
