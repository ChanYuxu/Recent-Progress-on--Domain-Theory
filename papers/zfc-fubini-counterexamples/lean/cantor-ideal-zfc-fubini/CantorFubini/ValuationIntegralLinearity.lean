import CantorFubini.ValuationIntegralApproximation
import CantorFubini.ValuationIntegral.IndicatorAddition

/-! Positive additivity and uniqueness of the actual valuation integral.
Finite open-indicator induction is followed by the proved dyadic exhaustion.
The uniqueness lemma is instantiated with concrete operators in the monad
proofs; its hypotheses are never premises of the constructed monad. -/

set_option autoImplicit false
open Set Topology TopologicalSpace
open scoped ENNReal Classical BigOperators
universe u v

namespace CantorFubini

theorem isVLSC_finset_sum {X : Type u} [TopologicalSpace X] {ι : Type v}
    (s : Finset ι) (f : ι → X → ℝ≥0∞) (hf : ∀ i ∈ s, IsVLSC (f i)) :
    IsVLSC (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (isVLSC_const (X := X) 0)
  | @insert a s ha ih =>
      have hs : IsVLSC (fun x => ∑ i ∈ s, f i x) :=
        ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
      simpa only [Finset.sum_insert ha] using (hf a (Finset.mem_insert_self _ _)).add hs

theorem functional_add_finiteIndicators {X : Type u} [TopologicalSpace X] {ι : Type v}
    (μ : Valuation X) (L : (X → ℝ≥0∞) → ℝ≥0∞)
    (hadd : ∀ (f : X → ℝ≥0∞), IsVLSC f → ∀ (U : Opens X) (c : ℝ≥0∞), c ≠ ∞ →
      L (fun x => f x + (U : Set X).indicator (fun _ => c) x) = L f + c * μ U)
    (f : X → ℝ≥0∞) (hf : IsVLSC f) (s : Finset ι)
    (U : ι → Opens X) (c : ι → ℝ≥0∞) (hc : ∀ i ∈ s, c i ≠ ∞) :
    L (fun x => f x + ∑ i ∈ s, (U i : Set X).indicator (fun _ => c i) x) =
      L f + ∑ i ∈ s, c i * μ (U i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      have hcS : ∀ i ∈ s, c i ≠ ∞ := fun i hi => hc i (Finset.mem_insert_of_mem hi)
      have hsum : IsVLSC (fun x => ∑ i ∈ s, (U i : Set X).indicator (fun _ => c i) x) :=
        isVLSC_finset_sum s _ (fun i _ => isVLSC_indicator (U i) (c i))
      calc
        L (fun x => f x + ∑ i ∈ insert a s, (U i : Set X).indicator (fun _ => c i) x) =
            L (fun x => (f x + ∑ i ∈ s, (U i : Set X).indicator (fun _ => c i) x) +
              (U a : Set X).indicator (fun _ => c a) x) := by
          congr 1
          funext x
          rw [Finset.sum_insert ha]
          ac_rfl
        _ = L (fun x => f x + ∑ i ∈ s, (U i : Set X).indicator (fun _ => c i) x) +
            c a * μ (U a) := hadd _ (hf.add hsum) (U a) (c a) (hc a (Finset.mem_insert_self _ _))
        _ = L f + ∑ i ∈ insert a s, c i * μ (U i) := by
          rw [ih hcS, Finset.sum_insert ha]
          ac_rfl

theorem vIntegral_add_finiteIndicators {X : Type u} [TopologicalSpace X] {ι : Type v}
    (μ : Valuation X) (f : X → ℝ≥0∞) (hf : IsVLSC f) (s : Finset ι)
    (U : ι → Opens X) (c : ι → ℝ≥0∞) (hc : ∀ i ∈ s, c i ≠ ∞) :
    vIntegral μ (fun x => f x + ∑ i ∈ s, (U i : Set X).indicator (fun _ => c i) x) =
      vIntegral μ f + ∑ i ∈ s, c i * μ (U i) :=
  functional_add_finiteIndicators μ (vIntegral μ)
    (fun _ hf U c hc => vIntegral_add_indicator μ hf U c hc) f hf s U c hc

theorem vIntegral_finiteIndicators {X : Type u} [TopologicalSpace X] {ι : Type v}
    (μ : Valuation X) (s : Finset ι) (U : ι → Opens X) (c : ι → ℝ≥0∞)
    (hc : ∀ i ∈ s, c i ≠ ∞) :
    vIntegral μ (fun x => ∑ i ∈ s, (U i : Set X).indicator (fun _ => c i) x) =
      ∑ i ∈ s, c i * μ (U i) := by
  simpa only [zero_add, vIntegral_zero] using
    vIntegral_add_finiteIndicators μ (fun _ => 0) (isVLSC_const 0) s U c hc

theorem vIntegral_dyadicApprox {X : Type u} [TopologicalSpace X]
    (μ : Valuation X) (f : X → ℝ≥0∞) (n : ℕ) :
    vIntegral μ (dyadicApprox f n) =
      ∑ k ∈ Finset.range (dyadicCut n), dyadicCoeff n * μ (dyadicOpen f n k) := by
  have he : dyadicApprox f n = fun x => ∑ k ∈ Finset.range (dyadicCut n),
      (dyadicOpen f n k : Set X).indicator (fun _ => dyadicCoeff n) x :=
    funext (dyadicApprox_eq_sum f n)
  rw [he]
  exact vIntegral_finiteIndicators μ (Finset.range (dyadicCut n)) (dyadicOpen f n)
    (fun _ => dyadicCoeff n) (fun _ _ => dyadicCoeff_ne_top n)

/-- Positive additivity for arbitrary lower-semicontinuous ENNReal functions,
including unbounded values and infinite integrals. -/
theorem vIntegral_add {X : Type u} [TopologicalSpace X] (μ : Valuation X)
    {f g : X → ℝ≥0∞} (hf : IsVLSC f) (hg : IsVLSC g) :
    vIntegral μ (fun x => f x + g x) = vIntegral μ f + vIntegral μ g := by
  let a : ℕ → X → ℝ≥0∞ := dyadicApprox g
  have ha : ∀ n, IsVLSC (a n) := fun n => isVLSC_dyadicApprox g n
  have hm : Monotone a := dyadicApprox_mono hg
  have hs : (fun x => ⨆ n, a n x) = g := funext (iSup_dyadicApprox hg)
  have he : (fun x => f x + g x) = fun x => ⨆ n, (f x + a n x) := by
    funext x
    rw [← congrFun hs x, ENNReal.add_iSup]
  have hd : Directed (· ≤ ·) (fun n => fun x => f x + a n x) := by
    intro i j
    exact ⟨max i j, (fun x => add_le_add le_rfl (hm (le_max_left i j) x)),
      (fun x => add_le_add le_rfl (hm (le_max_right i j) x))⟩
  have hi (n : ℕ) : vIntegral μ (fun x => f x + a n x) =
      vIntegral μ f + vIntegral μ (a n) := by
    have he : a n = fun x => ∑ k ∈ Finset.range (dyadicCut n),
        (dyadicOpen g n k : Set X).indicator (fun _ => dyadicCoeff n) x :=
      funext (dyadicApprox_eq_sum g n)
    rw [he]
    rw [vIntegral_add_finiteIndicators μ f hf]
    · rw [vIntegral_finiteIndicators]
      intro k hk
      exact dyadicCoeff_ne_top n
    · intro k hk
      exact dyadicCoeff_ne_top n
  calc
    vIntegral μ (fun x => f x + g x) =
        ⨆ n, vIntegral μ (fun x => f x + a n x) := by
      rw [he, vIntegral_iSup_directed μ _ (fun n => hf.add (ha n)) hd]
    _ = ⨆ n, (vIntegral μ f + vIntegral μ (a n)) := iSup_congr hi
    _ = vIntegral μ f + (⨆ n, vIntegral μ (a n)) := (ENNReal.add_iSup _).symm
    _ = vIntegral μ f + vIntegral μ g := by
      rw [← vIntegral_iSup_directed μ a ha hm.directed_le, hs]

/-- Uniqueness from values on open indicators, positive indicator addition,
and sequential directed continuity, using the actual dyadic exhaustion. -/
theorem vIntegral_unique {X : Type u} [TopologicalSpace X]
    (μ : Valuation X) (L : (X → ℝ≥0∞) → ℝ≥0∞)
    (hzero : L (fun _ => 0) = 0)
    (hadd : ∀ (f : X → ℝ≥0∞), IsVLSC f → ∀ (U : Opens X) (c : ℝ≥0∞), c ≠ ∞ →
      L (fun x => f x + (U : Set X).indicator (fun _ => c) x) = L f + c * μ U)
    (hsup : ∀ (f : ℕ → X → ℝ≥0∞), (∀ n, IsVLSC (f n)) → Monotone f →
      L (fun x => ⨆ n, f n x) = ⨆ n, L (f n))
    {f : X → ℝ≥0∞} (hf : IsVLSC f) : L f = vIntegral μ f := by
  have hfinite (n : ℕ) : L (dyadicApprox f n) = vIntegral μ (dyadicApprox f n) := by
    have h := functional_add_finiteIndicators μ L hadd (fun _ => 0) (isVLSC_const 0)
      (Finset.range (dyadicCut n)) (dyadicOpen f n) (fun _ => dyadicCoeff n)
      (fun _ _ => dyadicCoeff_ne_top n)
    rw [vIntegral_dyadicApprox]
    have he : dyadicApprox f n = fun x => ∑ k ∈ Finset.range (dyadicCut n),
        (dyadicOpen f n k : Set X).indicator (fun _ => dyadicCoeff n) x :=
      funext (dyadicApprox_eq_sum f n)
    rw [he]
    simpa only [zero_add, hzero] using h
  have he : (fun x => ⨆ n, dyadicApprox f n x) = f := funext (iSup_dyadicApprox hf)
  calc
    L f = L (fun x => ⨆ n, dyadicApprox f n x) := congrArg L he.symm
    _ = ⨆ n, L (dyadicApprox f n) := hsup _ (isVLSC_dyadicApprox f) (dyadicApprox_mono hf)
    _ = ⨆ n, vIntegral μ (dyadicApprox f n) := iSup_congr hfinite
    _ = vIntegral μ f := by
      rw [← vIntegral_iSup_directed μ _ (isVLSC_dyadicApprox f) (dyadicApprox_mono hf).directed_le, he]

end CantorFubini
