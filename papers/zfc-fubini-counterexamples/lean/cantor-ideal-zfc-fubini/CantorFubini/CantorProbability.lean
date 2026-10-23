import CantorFubini.ParameterMeasure
import Mathlib.Probability.Distributions.Uniform
import Mathlib.MeasureTheory.Measure.Typeclasses.NoAtoms
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Clopen

/-! Actual Cantor space and its fair-coin product law. All construction code
in this module is new, using Mathlib's infinite product probability. Measures
of arbitrary subsets are outer measures; on null subsets this agrees with the
completion used in the manuscript, as recorded in `NullTopology.lean`. -/

set_option autoImplicit false
open Set Filter Topology TopologicalSpace MeasureTheory
open scoped ENNReal Topology BigOperators

namespace CantorFubini

abbrev Cantor := ℕ → Bool
abbrev Omega := ℕ → Cantor

/-- The standard Cantor metric, with exactly the existing product uniformity
and product topology. -/
noncomputable instance cantorMetricSpace : MetricSpace Cantor :=
  PiNat.metricSpaceOfDiscreteUniformity (fun _ => rfl)

noncomputable instance omegaMetricSpace : MetricSpace Omega := PiCountable.metricSpace

noncomputable def fairCoin : Measure Bool := (PMF.uniformOfFintype Bool).toMeasure
instance fairCoin_probability : IsProbabilityMeasure fairCoin := by
  unfold fairCoin
  infer_instance

@[simp] theorem fairCoin_singleton (b : Bool) : fairCoin {b} = (2 : ℝ≥0∞)⁻¹ := by
  rw [fairCoin, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  simp [PMF.uniformOfFintype_apply]

noncomputable def cantorMeasure : Measure Cantor := Measure.infinitePi (fun _ : ℕ => fairCoin)
noncomputable def parameterProbability : Measure Omega :=
  Measure.infinitePi (fun _ : ℕ => cantorMeasure)

instance cantorMeasure_probability : IsProbabilityMeasure cantorMeasure := by
  unfold cantorMeasure
  infer_instance
instance parameterProbability_probability : IsProbabilityMeasure parameterProbability := by
  unfold parameterProbability
  infer_instance

theorem cantor_compact : CompactSpace Cantor := inferInstance
theorem cantor_secondCountable : SecondCountableTopology Cantor := inferInstance
theorem cantor_borel : BorelSpace Cantor := inferInstance
theorem cantor_radon : cantorMeasure.InnerRegular := inferInstance
theorem omega_compact : CompactSpace Omega := inferInstance
theorem omega_secondCountable : SecondCountableTopology Omega := inferInstance
theorem omega_borel : BorelSpace Omega := inferInstance
theorem parameterProbability_radon : parameterProbability.InnerRegular := inferInstance

/-- The source cylinder `[x↾n]`, without a change of its topology. -/
def cylinder (x : Cantor) (n : ℕ) : Opens Cantor :=
  ⟨PiNat.cylinder x n, PiNat.isOpen_cylinder _ _ _⟩

@[simp] theorem mem_cylinder {x y : Cantor} {n : ℕ} :
    y ∈ cylinder x n ↔ ∀ i < n, y i = x i := Iff.rfl

theorem cylinder_mem_self (x : Cantor) (n : ℕ) : x ∈ cylinder x n :=
  PiNat.self_mem_cylinder x n

theorem cylinder_isClopen (x : Cantor) (n : ℕ) : IsClopen (cylinder x n : Set Cantor) := by
  have he : (cylinder x n : Set Cantor) =
      ⋂ i : Fin n, (fun y : Cantor => y i.val) ⁻¹' {x i.val} := by
    ext y
    simp only [mem_iInter, mem_preimage, mem_singleton_iff]
    exact ⟨fun h i => h i.val i.isLt, fun h i hi => h ⟨i, hi⟩⟩
  rw [he]
  exact isClopen_iInter_of_finite (fun i =>
    (isClopen_discrete ({x i.val} : Set Bool)).preimage (continuous_apply i.val))

theorem cylinder_anti (x : Cantor) {n k : ℕ} (h : n ≤ k) :
    cylinder x k ≤ cylinder x n := PiNat.cylinder_anti x h

theorem cylinder_eq_of_mem {x y : Cantor} {n : ℕ} (h : y ∈ cylinder x n) :
    cylinder y n = cylinder x n := Opens.ext (PiNat.mem_cylinder_iff_eq.mp h)

/-- Cylinders centered at the given point are an ordinary neighborhood base. -/
theorem exists_cylinder_subset {O : Set Cantor} (hO : IsOpen O) {x : Cantor} (hx : x ∈ O) :
    ∃ n : ℕ, (cylinder x n : Set Cantor) ⊆ O := by
  obtain ⟨V, ⟨y, n, rfl⟩, hxV, hVO⟩ :=
    (PiNat.isTopologicalBasis_cylinders (fun _ : ℕ => Bool)).exists_subset_of_mem_open hx hO
  exact ⟨n, by simpa only [← PiNat.mem_cylinder_iff_eq.mp hxV] using hVO⟩

def extendWord {n : ℕ} (w : Fin n → Bool) : Cantor :=
  fun i => if h : i < n then w ⟨i, h⟩ else false

theorem cylinders_countable :
    ({V : Set Cantor | ∃ x : Cantor, ∃ n : ℕ, V = cylinder x n}).Countable := by
  classical
  let f : (Σ n : ℕ, Fin n → Bool) → Set Cantor :=
    fun w => cylinder (extendWord w.2) w.1
  apply (countable_range f).mono
  rintro V ⟨x, n, rfl⟩
  refine ⟨⟨n, fun i => x i.val⟩, ?_⟩
  apply congrArg (fun U : Opens Cantor => (U : Set Cantor))
  apply cylinder_eq_of_mem
  intro i hi
  simp only [extendWord, dif_pos hi]

/-- Source statement that the literal finite-word cylinders form a countable
clopen basis of the usual Cantor topology. -/
theorem cylinders_countable_clopen_basis :
    ({V : Set Cantor | ∃ x : Cantor, ∃ n : ℕ, V = cylinder x n}).Countable ∧
    IsTopologicalBasis {V : Set Cantor | ∃ x : Cantor, ∃ n : ℕ, V = cylinder x n} ∧
    ∀ x : Cantor, ∀ n : ℕ, IsClopen (cylinder x n : Set Cantor) :=
  ⟨cylinders_countable, PiNat.isTopologicalBasis_cylinders _, cylinder_isClopen⟩

/-- A finite subset of an ordinary open admits a clopen neighborhood inside it. -/
theorem finite_clopen_between {F : Finset Cantor} {U : Opens Cantor}
    (hF : (F : Set Cantor) ⊆ U) :
    ∃ V : Opens Cantor, IsClopen (V : Set Cantor) ∧ (F : Set Cantor) ⊆ V ∧ V ≤ U := by
  classical
  have hh : ∀ x : F, ∃ n, (cylinder x.val n : Set Cantor) ⊆ U :=
    fun x => exists_cylinder_subset U.isOpen (hF x.property)
  choose n hn using hh
  let V : Opens Cantor := ⨆ x : F, cylinder x.val (n x)
  refine ⟨V, ?_, ?_, ?_⟩
  · change IsClopen ((⨆ x : F, cylinder x.val (n x) : Opens Cantor) : Set Cantor)
    rw [Opens.coe_iSup]
    exact isClopen_iUnion_of_finite (fun x : F => cylinder_isClopen x.val (n x))
  · intro x hx
    exact Opens.mem_iSup.mpr ⟨⟨x, hx⟩, cylinder_mem_self x (n ⟨x, hx⟩)⟩
  · exact iSup_le (fun x => hn x)

/-- Printed fair-coin cylinder probability. -/
theorem cantorMeasure_cylinder (x : Cantor) (n : ℕ) :
    cantorMeasure (cylinder x n : Set Cantor) = ((2 : ℝ≥0∞)⁻¹) ^ n := by
  change Measure.infinitePi (fun _ : ℕ => fairCoin) (PiNat.cylinder x n) = _
  rw [PiNat.cylinder_eq_pi, Measure.infinitePi_pi _ (fun i _ => measurableSet_singleton (x i))]
  simp

@[simp] theorem cantorMeasure_singleton (x : Cantor) : cantorMeasure {x} = 0 := by
  apply le_antisymm _ (zero_le _)
  have hb : ∀ n, cantorMeasure {x} ≤ ((2 : ℝ≥0∞)⁻¹) ^ n := by
    intro n
    rw [← cantorMeasure_cylinder x n]
    exact measure_mono (singleton_subset_iff.mpr (cylinder_mem_self x n))
  exact ge_of_tendsto' (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one
    (show (2 : ℝ≥0∞)⁻¹ < 1 by norm_num)) hb

instance cantorMeasure_noAtoms : NoAtoms cantorMeasure := ⟨cantorMeasure_singleton⟩

theorem cantorMeasure_countable {A : Set Cantor} (hA : A.Countable) : cantorMeasure A = 0 :=
  hA.measure_zero cantorMeasure

/-- Independence at any finite set of parameter coordinates, including the
literal initial-segment avoidance calculation in the hitting lemma. -/
theorem finite_coordinate_avoidance {N : Set Cantor} (hN : MeasurableSet N) (k : ℕ) :
    parameterProbability {t : Omega | ∀ n < k, t n ∉ N} =
      (1 - cantorMeasure N) ^ k := by
  have he : {t : Omega | ∀ n < k, t n ∉ N} =
      (Finset.range k : Set ℕ).pi (fun _ => Nᶜ) := by ext t; simp
  rw [he, parameterProbability, Measure.infinitePi_pi _ (fun _ _ => hN.compl)]
  simp [measure_compl hN]

end CantorFubini
