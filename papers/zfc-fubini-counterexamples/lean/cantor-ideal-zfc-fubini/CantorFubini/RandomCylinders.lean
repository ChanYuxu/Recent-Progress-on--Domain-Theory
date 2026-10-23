import CantorFubini.CantorProbability
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-! Literal random cylinder unions of source §4. The source index n≥1 is
represented by n+1, so coordinate n has cylinder length n+2. The Cantor
construction is new. The Scott-continuity proof skeleton and compact tube
argument are adapted from ZFC_Fubini_Lean/ZFCFubini/RandomOpen.lean, SHA256
b19d74217a597a076c87c18af74c4ccf992c84dcbf99ac24e1b9a5b8bb8313ca.
Elementary infinite-product inequalities below are adapted from
ZFC_Fubini_Lean/ZFCFubini/CircleProbability.lean, original SHA256
bf82fbf65b386ee4251f98556a3336c8d7e23a4ccd7720e8da0462dec5c62025.
No legacy theorem or legacy model is imported. -/

set_option autoImplicit false
open Set Filter Topology TopologicalSpace MeasureTheory
open scoped ENNReal Topology BigOperators

namespace CantorFubini

def randomPrefix (t : Omega) (k : ℕ) : Opens Cantor :=
  ⨆ n : Fin k, cylinder (t n.val) (n.val + 2)

def randomOpen (t : Omega) : Opens Cantor := ⨆ n : ℕ, cylinder (t n) (n + 2)

theorem randomPrefix_isClopen (t : Omega) (k : ℕ) :
    IsClopen (randomPrefix t k : Set Cantor) := by
  rw [randomPrefix, Opens.coe_iSup]
  exact isClopen_iUnion_of_finite (fun n => cylinder_isClopen (t n.val) (n.val + 2))

theorem randomPrefix_isCompact (t : Omega) (k : ℕ) :
    IsCompact (randomPrefix t k : Set Cantor) := (randomPrefix_isClopen t k).isClosed.isCompact

theorem randomPrefix_le_randomOpen (t : Omega) (k : ℕ) : randomPrefix t k ≤ randomOpen t :=
  iSup_le (fun n => le_iSup (fun n : ℕ => cylinder (t n) (n + 2)) n.val)

theorem randomPrefix_mono (t : Omega) : Monotone (randomPrefix t) := by
  intro k l hkl
  apply iSup_le
  intro n
  exact le_iSup_of_le (⟨n.val, n.isLt.trans_le hkl⟩ : Fin l) le_rfl

theorem randomPrefix_isLUB (t : Omega) :
    IsLUB (range (randomPrefix t)) (randomOpen t) := by
  refine ⟨?_, ?_⟩
  · rintro V ⟨k, rfl⟩; exact randomPrefix_le_randomOpen t k
  · intro V hV
    apply iSup_le
    intro n
    exact (le_iSup_of_le (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)) le_rfl).trans
      (hV (mem_range_self (n + 1)))

theorem randomPrefix_iSup (t : Omega) : (⨆ k, randomPrefix t k) = randomOpen t :=
  isLUB_iSup.unique (randomPrefix_isLUB t)

/-- Literal finite-prefix compact-cover step in the first proof of source
Lemma `lem:random-continuity`. -/
theorem compact_subset_randomPrefix {C : Set Cantor} (hC : IsCompact C)
    {t : Omega} (ht : C ⊆ randomOpen t) : ∃ k, C ⊆ randomPrefix t k := by
  have hc : C ⊆ ⋃ k, (randomPrefix t k : Set Cantor) := by
    rw [← Opens.coe_iSup, randomPrefix_iSup]
    exact ht
  exact hC.elim_directed_cover (fun k => (randomPrefix t k : Set Cantor))
    (fun k => (randomPrefix t k).isOpen) hc (randomPrefix_mono t).directed_le

theorem randomOpen_contains_coordinate (t : Omega) (n : ℕ) : t n ∈ randomOpen t :=
  Opens.mem_iSup.mpr ⟨n, cylinder_mem_self (t n) (n + 2)⟩

theorem randomPrefix_locally_constant (t : Omega) (k : ℕ) :
    ∃ N : Set Omega, IsOpen N ∧ t ∈ N ∧ ∀ s ∈ N, randomPrefix s k = randomPrefix t k := by
  let N : Set Omega := ⋂ n : Fin k,
    (fun s : Omega => s n.val) ⁻¹' (cylinder (t n.val) (n.val + 2) : Set Cantor)
  refine ⟨N, ?_, ?_, ?_⟩
  · exact isOpen_iInter_of_finite (fun n =>
      (cylinder (t n.val) (n.val + 2)).isOpen.preimage (continuous_apply n.val))
  · exact mem_iInter.mpr (fun n => cylinder_mem_self (t n.val) (n.val + 2))
  · intro s hs
    apply iSup_congr
    intro n
    exact cylinder_eq_of_mem (mem_iInter.mp hs n)

/-- The full Scott topology on ordinary opens, with the literal finite clopen
approximants used in the manuscript. -/
theorem randomOpen_scott_continuous :
    Continuous (fun t : Omega => WithScott.toScott (randomOpen t)) := by
  apply continuous_def.mpr
  intro A hA
  apply isOpen_iff_mem_nhds.mpr
  intro t ht
  have hu : IsUpperSet A := IsScott.isUpperSet_of_isOpen (D := univ) hA
  have hi : DirSupInaccOn univ A :=
    ((IsScott.isOpen_iff_isUpperSet_and_dirSupInaccOn (D := univ)).mp hA).2
  let f : ℕ → WithScott (Opens Cantor) := fun k => WithScott.toScott (randomPrefix t k)
  have hd : Directed (· ≤ ·) f := (randomPrefix_mono t).directed_le
  have hl : IsLUB (range f) (WithScott.toScott (randomOpen t)) := randomPrefix_isLUB t
  obtain ⟨V, ⟨k, rfl⟩, hkA⟩ :=
    hi (mem_univ _) (range_nonempty f) hd.directedOn_range hl ht
  obtain ⟨N, hNo, htN, hNc⟩ := randomPrefix_locally_constant t k
  apply mem_of_superset (hNo.mem_nhds htN)
  intro s hs
  apply hu (randomPrefix_le_randomOpen s k)
  change WithScott.toScott (randomPrefix s k) ∈ A
  rw [hNc s hs]
  exact hkA

theorem randomOpen_continuous :
    Continuous (fun t : Omega => WithScott.toScott (randomOpen t)) := randomOpen_scott_continuous

theorem randomOpen_scott_comp_continuous {Q : Type*} [Preorder Q]
    (f : Opens Cantor → Q) (hf : ScottContinuous f) :
    Continuous (fun t : Omega => WithScott.toScott (f (randomOpen t))) :=
  ((scott_continuous_iff f).mp hf).comp randomOpen_scott_continuous

theorem randomOpen_scott_sup_continuous {Q : Type*} [CompleteLattice Q]
    (f : Opens Cantor → Q) (hf : ScottContinuous f) (H : Q) :
    Continuous (fun t : Omega => WithScott.toScott (f (randomOpen t) ⊔ H)) := by
  have hs : ScottContinuous (fun Z : Q => Z ⊔ H) :=
    (ScottContinuous.id.prodMk (ScottContinuous.const H)).comp ScottContinuous.sup₂
  exact randomOpen_scott_comp_continuous (fun U => f U ⊔ H) (hf.comp hs)

theorem randomOpen_joint_isOpen : IsOpen {z : Cantor × Omega | z.1 ∈ randomOpen z.2} := by
  have he : {z : Cantor × Omega | z.1 ∈ randomOpen z.2} =
      ⋃ n : ℕ, ⋂ i : Fin (n + 2), {z : Cantor × Omega | z.1 i.val = z.2 n i.val} := by
    ext z
    simp only [mem_setOf_eq, randomOpen, Opens.mem_iSup, mem_cylinder, mem_iUnion, mem_iInter]
    exact exists_congr (fun n => ⟨fun h i => h i.val i.isLt, fun h i hi => h ⟨i, hi⟩⟩)
  rw [he]
  apply isOpen_iUnion
  intro n
  apply isOpen_iInter_of_finite
  intro i
  have hc : Continuous (fun z : Cantor × Omega => (z.1 i.val, z.2 n i.val)) :=
    (((continuous_apply i.val).comp continuous_fst).prodMk
      ((continuous_apply i.val).comp ((continuous_apply n).comp continuous_snd)))
  exact (isOpen_discrete {p : Bool × Bool | p.1 = p.2}).preimage hc

theorem randomOpen_incidence_isOpen (x : Cantor) : IsOpen {t : Omega | x ∈ randomOpen t} :=
  randomOpen_joint_isOpen.preimage (continuous_const.prodMk continuous_id)

/-- First printed assertion of Lemma `lem:random-continuity`, including C=∅. -/
theorem randomOpen_compact_containment_isOpen {C : Set Cantor} (hC : IsCompact C) :
    IsOpen {t : Omega | C ⊆ randomOpen t} := by
  apply isOpen_iff_mem_nhds.mpr
  intro t ht
  apply hC.eventually_forall_of_forall_eventually
  intro x hx
  have hj : IsOpen {z : Omega × Cantor | z.2 ∈ randomOpen z.1} :=
    randomOpen_joint_isOpen.preimage continuous_swap
  exact hj.mem_nhds (ht hx)

theorem random_cylinder_sum : (∑' n : ℕ, ((2 : ℝ≥0∞)⁻¹) ^ (n + 2)) = 1 / 2 := by
  simp only [pow_add, ENNReal.tsum_mul_right, ENNReal.tsum_geometric_two]
  rw [pow_two, ← mul_assoc, ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]
  simp

/-- Exact source union bound `eq:small-opens`. -/
theorem randomOpen_measure_le (t : Omega) : cantorMeasure (randomOpen t : Set Cantor) ≤ 1 / 2 := by
  rw [randomOpen, Opens.coe_iSup]
  calc
    cantorMeasure (⋃ n : ℕ, (cylinder (t n) (n + 2) : Set Cantor)) ≤
        ∑' n, cantorMeasure (cylinder (t n) (n + 2) : Set Cantor) := measure_iUnion_le _
    _ = 1 / 2 := by simp_rw [cantorMeasure_cylinder]; exact random_cylinder_sum

noncomputable def hitLength (n : ℕ) : ℝ := (1 / 2 : ℝ) ^ (n + 2)
noncomputable def q : ℝ := 1 - ∏' n : ℕ, (1 - hitLength n)

/-- Literal negative-exponent source notation after n≥1 ↔ n+1. -/
theorem hitLength_source (n : ℕ) : hitLength n = (2 : ℝ) ^ (-((n : ℤ) + 2)) := by
  have he : -((n : ℤ) + 2) = -((n + 2 : ℕ) : ℤ) := by omega
  rw [he, zpow_neg, zpow_natCast]
  simp [hitLength, one_div, inv_pow]

theorem q_source : q = 1 - ∏' n : ℕ, (1 - (2 : ℝ) ^ (-((n : ℤ) + 2))) := by
  unfold q
  simp_rw [hitLength_source]

theorem hitLength_nonneg (n : ℕ) : 0 ≤ hitLength n := by unfold hitLength; positivity
theorem hitLength_le_one (n : ℕ) : hitLength n ≤ 1 :=
  pow_le_one₀ (by norm_num) (by norm_num)

theorem hasSum_hitLength : HasSum hitLength (1 / 2 : ℝ) := by
  convert hasSum_geometric_two.mul_left (1 / 4 : ℝ) using 1
  · funext n
    simp only [hitLength, pow_add]
    ring
  · norm_num

theorem hitFactors_multipliable : Multipliable (fun n : ℕ => 1 - hitLength n) := by
  exact (Real.multipliable_one_add_of_summable hasSum_hitLength.summable.neg).congr
    (fun _ => by ring)

theorem one_sub_prod_one_sub_le_sum {ι : Type*} (f : ι → ℝ)
    (hf0 : ∀ i, 0 ≤ f i) (hf1 : ∀ i, f i ≤ 1) (s : Finset ι) :
    1 - ∏ i ∈ s, (1 - f i) ≤ ∑ i ∈ s, f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha]
      have hprod : ∏ i ∈ s, (1 - f i) ≤ 1 :=
        Finset.prod_le_one (fun i _ => sub_nonneg.mpr (hf1 i))
          (fun i _ => by linarith [hf0 i])
      have hmul := mul_le_of_le_one_right (hf0 a) hprod
      nlinarith

theorem hitFactors_tprod_nonneg : 0 ≤ ∏' n : ℕ, (1 - hitLength n) := by
  apply le_hasProd_of_le_prod hitFactors_multipliable.hasProd
  intro s
  exact Finset.prod_nonneg (fun n _ => sub_nonneg.mpr (hitLength_le_one n))

theorem q_bounds : 1 / 4 ≤ q ∧ q ≤ 1 / 2 := by
  have hlow : 1 - (1 / 2 : ℝ) ≤ ∏' n : ℕ, (1 - hitLength n) := by
    apply le_hasProd_of_le_prod hitFactors_multipliable.hasProd
    intro s
    have hsum : ∑ n ∈ s, hitLength n ≤ 1 / 2 := by
      simpa only [hasSum_hitLength.tsum_eq] using
        hasSum_hitLength.summable.sum_le_tsum s (fun n _ => hitLength_nonneg n)
    have hf := one_sub_prod_one_sub_le_sum hitLength hitLength_nonneg hitLength_le_one s
    linarith
  have hupp : (∏' n : ℕ, (1 - hitLength n)) ≤ 1 - hitLength 0 := by
    have he : ∀ᶠ s : Finset ℕ in atTop,
        (∏ n ∈ s, (1 - hitLength n)) ≤ 1 - hitLength 0 := by
      refine eventually_atTop.mpr ⟨{0}, fun s hs => ?_⟩
      have h := Finset.prod_le_prod_of_subset_of_le_one hs
        (fun n _ => sub_nonneg.mpr (hitLength_le_one n))
        (fun n _ _ => by linarith [hitLength_nonneg n])
      simpa using h
    exact le_of_tendsto hitFactors_multipliable.hasProd he
  have hzero : hitLength 0 = 1 / 4 := by norm_num [hitLength]
  rw [hzero] at hupp
  dsimp [q]
  constructor <;> linarith

/-- The manuscript's infinite product is explicitly the limit of the printed
finite products, rather than an opaque chosen probability constant. -/
theorem q_source_limit :
    Tendsto (fun k : ℕ => 1 - ∏ n ∈ Finset.range k, (1 - (1 / 2 : ℝ) ^ (n + 2)))
      atTop (𝓝 q) := by
  exact tendsto_const_nhds.sub hitFactors_multipliable.hasProd.tendsto_prod_nat

theorem hitLength_ofReal (n : ℕ) : ENNReal.ofReal (hitLength n) = ((2 : ℝ≥0∞)⁻¹) ^ (n + 2) := by
  rw [hitLength, ENNReal.ofReal_pow (by norm_num)]
  congr 1
  norm_num [ENNReal.ofReal_div_of_pos]

theorem hitFactors_hasProd_ofReal :
    HasProd (fun n : ℕ => ENNReal.ofReal (1 - hitLength n))
      (ENNReal.ofReal (∏' n : ℕ, (1 - hitLength n))) := by
  have h := ENNReal.tendsto_ofReal hitFactors_multipliable.hasProd
  unfold HasProd
  convert h using 1
  funext s
  exact (ENNReal.ofReal_prod_of_nonneg
    (fun n _ => sub_nonneg.mpr (hitLength_le_one n))).symm

def pointHit (x : Cantor) : Set Omega := {t | x ∈ randomOpen t}
theorem pointHit_isOpen (x : Cantor) : IsOpen (pointHit x) := randomOpen_incidence_isOpen x

theorem pointHit_compl_eq_pi (x : Cantor) :
    (pointHit x)ᶜ = univ.pi (fun n : ℕ => (cylinder x (n + 2) : Set Cantor)ᶜ) := by
  ext t
  simp only [pointHit, mem_compl_iff, mem_setOf_eq, randomOpen, Opens.mem_iSup,
    not_exists, Set.mem_pi, mem_univ, true_implies]
  apply forall_congr'
  intro n
  exact not_congr (PiNat.mem_cylinder_comm x (t n) (n + 2)).symm

/-- Exact constant fixed-point incidence probability for the actual iid
fair-coin product, with the source infinite product and its finite-product
limit exposed by `q_source_limit`. -/
theorem pointHit_probability (x : Cantor) :
    parameterProbability (pointHit x) = ENNReal.ofReal q := by
  have hmiss : parameterProbability (pointHit x)ᶜ =
      ENNReal.ofReal (∏' n : ℕ, (1 - hitLength n)) := by
    rw [pointHit_compl_eq_pi, parameterProbability,
      Measure.infinitePi_pi_univ (fun _ : ℕ => cantorMeasure)
        (fun n => (cylinder x (n + 2)).isOpen.measurableSet.compl)]
    calc
      (∏' n : ℕ, cantorMeasure (cylinder x (n + 2) : Set Cantor)ᶜ) =
          ∏' n : ℕ, ENNReal.ofReal (1 - hitLength n) := by
        apply tprod_congr
        intro n
        rw [prob_compl_eq_one_sub (cylinder x (n + 2)).isOpen.measurableSet,
          cantorMeasure_cylinder, ← hitLength_ofReal]
        simpa using (ENNReal.ofReal_sub 1 (hitLength_nonneg n)).symm
      _ = ENNReal.ofReal (∏' n : ℕ, (1 - hitLength n)) := hitFactors_hasProd_ofReal.tprod_eq
  calc
    parameterProbability (pointHit x) = 1 - parameterProbability (pointHit x)ᶜ := by
      simpa only [compl_compl] using
        prob_compl_eq_one_sub (μ := parameterProbability) (pointHit_isOpen x).measurableSet.compl
    _ = ENNReal.ofReal q := by
      rw [hmiss]
      simpa only [q, ENNReal.ofReal_one] using (ENNReal.ofReal_sub 1 hitFactors_tprod_nonneg).symm

end CantorFubini
