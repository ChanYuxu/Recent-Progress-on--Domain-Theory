import PointCentralFubini.Scott

set_option autoImplicit false
open Set Topology TopologicalSpace MeasureTheory
open scoped ENNReal
universe u v w
namespace PointCentralFubini

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

theorem IsLSC.comp {g : Y → ℝ≥0∞} (hg : IsLSC g)
    {f : X → Y} (hf : Continuous f) : IsLSC (g ∘ f) :=
  fun r => (hg r).preimage hf

theorem integral_mono (μ : Valuation X) {f g : X → ℝ≥0∞} (h : f ≤ g) :
    integral μ f ≤ integral μ g := by
  apply lintegral_mono; intro t
  apply μ.mono; apply interior_mono
  exact fun x hx => hx.trans_le (h x)

theorem integral_congr (μ : Valuation X) {f g : X → ℝ≥0∞} (h : ∀ x, f x = g x) :
    integral μ f = integral μ g := by rw [funext h]

/-- Source equation `eq:change-variables`, proved from the layer-cake definition. -/
theorem integral_push (μ : Valuation X) (f : X → Y) (hf : Continuous f)
    (g : Y → ℝ≥0∞) (hg : IsLSC g) :
    integral (μ.push f hf) g = integral μ (g ∘ f) := by
  apply lintegral_congr; intro t
  change μ (Opens.comap ⟨f,hf⟩ ⟨interior {y | ENNReal.ofReal t < g y}, _⟩) = _
  congr 1
  apply Opens.ext
  change f ⁻¹' interior {y | ENNReal.ofReal t < g y} =
    interior {x | ENNReal.ofReal t < g (f x)}
  rw [(hg _).interior_eq]
  exact ((hg _).preimage hf).interior_eq.symm

noncomputable def indicator (U : Opens X) : X → ℝ≥0∞ := by
  classical
  exact fun x => if x ∈ U then 1 else 0

/-- Evaluation of the Choquet integral of a characteristic function. -/
theorem integral_indicator (μ : Valuation X) (U : Opens X) :
    integral μ (indicator U) = μ U := by
  classical
  have hcut : ∀ t : ℝ,
      (⟨interior {x | ENNReal.ofReal t < indicator U x}, isOpen_interior⟩ : Opens X) =
        if t < 1 then U else ⊥ := by
    intro t
    split_ifs with ht
    · apply Opens.ext
      have he : {x | ENNReal.ofReal t < indicator U x} = (U : Set X) := by
        ext x; by_cases hx : x ∈ U <;> simp [indicator, hx, ENNReal.ofReal_lt_one, ht]
      simpa only [he] using U.isOpen.interior_eq
    · apply Opens.ext
      have he : {x | ENNReal.ofReal t < indicator U x} = (∅ : Set X) := by
        ext x; by_cases hx : x ∈ U <;> simp [indicator, hx, ENNReal.ofReal_lt_one, ht]
      simp [he]
  unfold integral
  simp_rw [hcut]
  have he : (fun t : ℝ => μ (if t < 1 then U else ⊥)) =
      (Iio (1 : ℝ)).indicator (fun _ => μ U) := by
    funext t; by_cases ht : t < 1 <;> simp [ht, μ.strict, Set.indicator]
  rw [he, lintegral_indicator measurableSet_Iio, setLIntegral_const]
  rw [Measure.restrict_apply measurableSet_Iio]
  have hi : Iio (1 : ℝ) ∩ Ici (0 : ℝ) = Ico (0 : ℝ) 1 := by ext t; simp; tauto
  rw [hi, Real.volume_Ico]
  simp

/-- Verified external reference: FPR, arXiv:1910.03752v3, Theorem 3.5,
linearity (only the stated LSC domain). This is a disclosed literature axiom. -/
axiom fpr_integral_add (μ : Valuation X) (f g : X → ℝ≥0∞)
    (hf : IsLSC f) (hg : IsLSC g) :
    integral μ (f + g) = integral μ f + integral μ g

/-- Verified external reference: the homogeneity clause of FPR Theorem 3.5. -/
axiom fpr_integral_smul (μ : Valuation X) (a : ℝ≥0∞) (f : X → ℝ≥0∞)
    (hf : IsLSC f) : integral μ (fun x => a * f x) = a * integral μ f

/-- Verified external reference: FPR Theorem 3.5, directed convergence. -/
axiom fpr_integral_iSup (μ : Valuation X) {ι : Type w} [Nonempty ι]
    (f : ι → X → ℝ≥0∞) (hf : ∀ i, IsLSC (f i)) (hd : Directed (· ≤ ·) f) :
    integral μ (fun x => ⨆ i, f i x) = ⨆ i, integral μ (f i)

/-- Evaluation at directed suprema for a Scott-continuous ENNReal map. -/
theorem scott_map_iSup {P : Type u} [PartialOrder P] (f : P → ℝ≥0∞)
    (hf : ScottContinuous f) {A : Set P} (hn : A.Nonempty)
    (hd : DirectedOn (· ≤ ·) A) {p : P} (hp : IsLUB A p) :
    f p = ⨆ a : A, f a := by
  have he := hf hn hd hp
  apply le_antisymm
  · apply he.2; rintro z ⟨a, ha, rfl⟩
    exact le_iSup (fun a : A => f a) ⟨a,ha⟩
  · exact iSup_le fun a => he.1 (mem_image_of_mem f a.property)

/-- The source's claim that inner integrals are Scott-continuous.
Its only imported analytic law is the cited FPR directed-convergence theorem. -/
theorem innerIntegral_scott {P : Type u} {Q : Type v}
    [PartialOrder P] [PartialOrder Q] (ν : DValuation Q)
    (h : P × Q → ℝ≥0∞) (hh : ScottContinuous h) :
    ScottContinuous (fun x : P => integral ν (fun y => h (x, WithScott.ofScott y))) := by
  intro A hn hd p hp
  have hm : Monotone (fun x : P => integral ν (fun y => h (x, WithScott.ofScott y))) := by
    intro a b hab
    exact integral_mono ν (fun y => hh.monotone ⟨hab,le_rfl⟩)
  have he : (fun y : WithScott Q => h (p,WithScott.ofScott y)) =
      (fun y => ⨆ a : A, h (a, WithScott.ofScott y)) := by
    funext y
    exact scott_map_iSup _ ((ScottContinuous.id.prodMk (ScottContinuous.const _)).comp hh)
      hn hd hp
  haveI : Nonempty A := hn.to_subtype
  have hs := fpr_integral_iSup ν (fun a : A => fun y => h (a,WithScott.ofScott y))
    (fun a => scott_isLSC ((ScottContinuous.const a.val).prodMk ScottContinuous.id |>.comp hh))
    (fun a b => by
      obtain ⟨c,hc,hac,hbc⟩ := hd a a.property b b.property
      exact ⟨⟨c,hc⟩, fun y => hh.monotone ⟨hac,le_rfl⟩, fun y => hh.monotone ⟨hbc,le_rfl⟩⟩)
  rw [← he] at hs
  constructor
  · rintro z ⟨a,ha,rfl⟩; exact hm (hp.1 ha)
  · intro b hb
    change integral ν (fun y => h (p,WithScott.ofScott y)) ≤ b
    rw [hs]
    exact iSup_le fun a => hb (mem_image_of_mem _ a.property)

end PointCentralFubini
