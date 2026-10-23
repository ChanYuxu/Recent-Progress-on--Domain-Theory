import CHFubini.PositiveCarrier
import Mathlib.Probability.ProductMeasure
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.MetricSpace.PiNat

/-!
Candidate implementation of manuscript `lem:dense-incidence` for the actual
countable product probability measure. Independence is used only through the
proved finite-cylinder formula `Measure.infinitePi_pi`; no independence on a
carrier or relatively open subset is assumed.
-/

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal

namespace CHFubini

universe u

/-- The law used in the manuscript: independent identically distributed
coordinates indexed by the natural numbers. -/
noncomputable def productLaw {T : Type u} [MeasurableSpace T]
    (ν : Measure T) : Measure (ℕ → T) := Measure.infinitePi (fun _ : ℕ => ν)

instance productLaw_probability {T : Type u} [MeasurableSpace T]
    (ν : Measure T) [IsProbabilityMeasure ν] : IsProbabilityMeasure (productLaw ν) := by
  unfold productLaw
  infer_instance

theorem productLaw_innerRegular
    {T : Type u} [MetricSpace T] [CompactSpace T] [SecondCountableTopology T]
    [MeasurableSpace T] [BorelSpace T]
    (ν : Measure T) [IsProbabilityMeasure ν] : Measure.InnerRegular (productLaw ν) := by
  infer_instance

/-- Any positive-probability sample set sweeps out a conull union of random
opens, provided every coordinate center belongs to its sample's random open.
This supplies the independence estimate in the source proof. -/
theorem forbidden_union_null
    {T : Type u} [TopologicalSpace T] [MeasurableSpace T]
    [OpensMeasurableSpace T] (ν : Measure T) [IsProbabilityMeasure ν]
    (U : (ℕ → T) → Set T) (ho : ∀ s, IsOpen (U s))
    (hcenter : ∀ s n, s n ∈ U s)
    {W : Set (ℕ → T)} (hW : 0 < productLaw ν W) :
    ν ((⋃ s ∈ W, U s)ᶜ) = 0 := by
  let N : Set T := (⋃ s ∈ W, U s)ᶜ
  have hNm : MeasurableSet N :=
    (isOpen_iUnion (fun s => isOpen_iUnion (fun _ => ho s))).isClosed_compl.measurableSet
  change ν N = 0
  by_contra hN
  have hcomp : ν Nᶜ < 1 :=
    lt_of_le_of_ne prob_le_one (fun h => hN ((prob_compl_eq_one_iff hNm).mp h))
  have hbound (k : ℕ) : productLaw ν W ≤ (ν Nᶜ) ^ k := by
    have hsub : W ⊆ Set.pi (Finset.range k : Set ℕ) (fun _ => Nᶜ) := by
      intro s hs n _
      change s n ∉ N
      intro hn
      exact hn (mem_iUnion.mpr ⟨s, mem_iUnion.mpr ⟨hs, hcenter s n⟩⟩)
    calc
      productLaw ν W ≤ productLaw ν (Set.pi (Finset.range k : Set ℕ) (fun _ => Nᶜ)) :=
        measure_mono hsub
      _ = (ν Nᶜ) ^ k := by
        rw [productLaw, Measure.infinitePi_pi (fun _ : ℕ => ν) (fun _ _ => hNm.compl)]
        simp
  exact (not_le_of_gt hW)
    (ge_of_tendsto' (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hcomp) hbound)

/-- Source `lem:dense-incidence` in a general second-countable coordinate
space, with its actual independent product law. -/
theorem dense_random_incidence
    {T : Type u} [TopologicalSpace T] [SecondCountableTopology T]
    [MeasurableSpace T] [OpensMeasurableSpace T]
    (ν : Measure T) [IsProbabilityMeasure ν]
    (U : (ℕ → T) → Set T) (ho : ∀ s, IsOpen (U s))
    (hcenter : ∀ s n, s n ∈ U s)
    (hincOpen : ∀ t, IsOpen {s : ℕ → T | t ∈ U s})
    {D : Set (ℕ → T)} (hD : PositiveCarrier (productLaw ν) D) :
    ∃ N : Set T, MeasurableSet N ∧ ν N = 0 ∧ ∀ t ∉ N,
      IsOpen {s : D | t ∈ U s.1} ∧ Dense {s : D | t ∈ U s.1} := by
  classical
  let B := countableBasis D
  let forbidden (b : B) : Set T := (⋃ s ∈ Subtype.val '' b.1, U s)ᶜ
  have hfm (b : B) : MeasurableSet (forbidden b) :=
    (isOpen_iUnion (fun s => isOpen_iUnion (fun _ => ho s))).isClosed_compl.measurableSet
  have hf0 (b : B) : ν (forbidden b) = 0 := by
    apply forbidden_union_null ν U ho hcenter
    exact hD.2.2 b.1 (isOpen_of_mem_countableBasis b.2)
      (nonempty_of_mem_countableBasis b.2)
  let N : Set T := ⋃ b : B, forbidden b
  refine ⟨N, MeasurableSet.iUnion hfm, measure_iUnion_null hf0, fun t ht => ?_⟩
  refine ⟨(hincOpen t).preimage continuous_subtype_val, ?_⟩
  apply (isBasis_countableBasis D).dense_iff.mpr
  intro W hW _
  have htf : t ∉ forbidden ⟨W, hW⟩ :=
    fun h => ht (mem_iUnion.mpr ⟨⟨W, hW⟩, h⟩)
  have htunion : t ∈ ⋃ s ∈ Subtype.val '' W, U s := by
    simpa only [forbidden, mem_compl_iff, not_not] using htf
  obtain ⟨s, hsW, hts⟩ := mem_iUnion₂.mp htunion
  obtain ⟨d, hdW, rfl⟩ := hsW
  exact ⟨d, hdW, hts⟩

/-- The actual random-open formula from the source (with the natural-number
index shifted when matching the printed `n ≥ 1` convention). -/
def randomBallUnion {T : Type u} [PseudoMetricSpace T]
    (r : ℕ → ℝ) (s : ℕ → T) : Set T := ⋃ n, Metric.ball (s n) (r n)

theorem randomBallUnion_isOpen {T : Type u} [PseudoMetricSpace T]
    (r : ℕ → ℝ) (s : ℕ → T) : IsOpen (randomBallUnion r s) :=
  isOpen_iUnion (fun _ => Metric.isOpen_ball)

theorem randomBallUnion_contains_coordinate {T : Type u} [PseudoMetricSpace T]
    (r : ℕ → ℝ) (hr : ∀ n, 0 < r n) (s : ℕ → T) (n : ℕ) :
    s n ∈ randomBallUnion r s := by
  apply mem_iUnion.mpr
  exact ⟨n, Metric.mem_ball_self (hr n)⟩

theorem randomBallUnion_incidence_isOpen {T : Type u} [PseudoMetricSpace T]
    (r : ℕ → ℝ) (t : T) :
    IsOpen {s : ℕ → T | t ∈ randomBallUnion r s} := by
  have heq : {s : ℕ → T | t ∈ randomBallUnion r s} =
      ⋃ n, (fun s : ℕ → T => s n) ⁻¹' Metric.ball t (r n) := by
    ext s
    simp only [mem_setOf_eq, randomBallUnion, mem_iUnion, Metric.mem_ball, mem_preimage]
    simp only [dist_comm]
  rw [heq]
  exact isOpen_iUnion (fun n => Metric.isOpen_ball.preimage (continuous_apply n))

/-- Instantiation at the manuscript's random ball union. The independent
coordinate estimate and dense relative incidence are both actually proved. -/
theorem dense_random_ball_incidence
    {T : Type u} [PseudoMetricSpace T] [SecondCountableTopology T]
    [MeasurableSpace T] [OpensMeasurableSpace T]
    (ν : Measure T) [IsProbabilityMeasure ν]
    (r : ℕ → ℝ) (hr : ∀ n, 0 < r n)
    {D : Set (ℕ → T)} (hD : PositiveCarrier (productLaw ν) D) :
    ∃ N : Set T, MeasurableSet N ∧ ν N = 0 ∧ ∀ t ∉ N,
      IsOpen {s : D | t ∈ randomBallUnion r s.1} ∧
        Dense {s : D | t ∈ randomBallUnion r s.1} :=
  dense_random_incidence ν (randomBallUnion r) (randomBallUnion_isOpen r)
    (randomBallUnion_contains_coordinate r hr) (randomBallUnion_incidence_isOpen r) hD

/-- Instantiation of the arbitrary-union null-defect theorem at the actual
random ball unions and iid product law. Its only source-set assumptions are
the explicit countable initial-segment laws and the null-trace property
constructed under CH earlier in the manuscript.

No carrier, incidence, event stabilization, or arbitrary-union conclusion is
assumed: those are all derived by the proofs in this candidate chain.
-/
theorem random_ball_arbitrary_union_defect_null
    {I : Type*} [SemilatticeSup I] (hI : CountablyBounded I)
    {T : Type u} [MetricSpace T] [CompactSpace T] [SecondCountableTopology T]
    [MeasurableSpace T] [BorelSpace T]
    (ν : Measure T) [IsProbabilityMeasure ν]
    {A : Type*} {Y : Type*}
    (initial : I → Set A) (hmono : Monotone initial)
    (hcount : ∀ β, (initial β).Countable)
    (hcapture : ∀ N : Set A, N.Countable → ∃ β₀ : I, N ⊆ initial β₀)
    (h : A → T)
    (hnullTrace : ∀ N : Set T, MeasurableSet N → ν N = 0 →
      {a : A | h a ∈ N}.Countable)
    (r : ℕ → ℝ) (hr : ∀ n, 0 < r n)
    (F : I → (ℕ → T) → Y) (decode : Y → Set A)
    (hinj : Function.Injective decode)
    (hF : ∀ β s, decode (F β s) =
      (initial β)ᶜ ∪ {a : A | h a ∈ randomBallUnion r s})
    {J : Type*} (H : J → Set Y)
    (ho : ∀ β j, IsOpen (F β ⁻¹' H j))
    (ha : ∀ j, Antitone (fun β => F β ⁻¹' H j)) :
    productLaw ν (limitPreimage F (⋃ j, H j) \ ⋃ j, limitPreimage F (H j)) = 0 := by
  letI : Measure.InnerRegular (productLaw ν) := productLaw_innerRegular ν
  apply tail_map_arbitrary_union_defect_null hI (productLaw ν) initial hmono hcount hcapture
    (fun s => {a : A | h a ∈ randomBallUnion r s}) F decode hinj hF ?_ H ho ha
  intro D hD
  obtain ⟨N, hNm, hN0, hNgood⟩ := dense_random_ball_incidence ν r hr hD
  refine ⟨{a : A | h a ∈ N}, hnullTrace N hNm hN0, fun a haN => ?_⟩
  exact hNgood (h a) haN

end CHFubini

#print axioms CHFubini.forbidden_union_null
#print axioms CHFubini.dense_random_incidence
#print axioms CHFubini.dense_random_ball_incidence
#print axioms CHFubini.random_ball_arbitrary_union_defect_null

