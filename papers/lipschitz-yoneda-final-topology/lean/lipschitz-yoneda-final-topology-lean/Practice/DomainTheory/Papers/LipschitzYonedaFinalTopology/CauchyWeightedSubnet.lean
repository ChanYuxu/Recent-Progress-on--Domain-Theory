import Mathlib.Analysis.SpecificLimits.Basic
import Practice.DomainTheory.Papers.LipschitzYonedaFinalTopology.StandardConsequences

/-!
# Cauchy-weighted cofinal subnets

Every Cauchy net admits a cofinal subnet carrying geometrically decreasing
weights for which the corresponding formal balls are monotone.  This is the
subnet construction used in the converse formal-ball criterion (the step
cited as the Cauchy-weightable-subnet lemma in the source literature).
-/

set_option autoImplicit false
set_option linter.unnecessarySimpa false

open Set Function Filter Topology
open scoped NNReal ENNReal Topology

noncomputable section

universe u v w

namespace LipschitzYonedaFinalTopology
namespace QuasiMetric

variable {X : Type u} (d : QuasiMetric X)

/-- The geometric radii used for the weighted subnet. -/
def geometricRadius (n : ℕ) : ℝ≥0 := (1 / 2 : ℝ≥0) ^ n

theorem geometricRadius_pos (n : ℕ) : 0 < geometricRadius n := by
  unfold geometricRadius
  positivity

theorem geometricRadius_succ_add (n : ℕ) :
    geometricRadius (n + 1) + geometricRadius (n + 1) =
      geometricRadius n := by
  unfold geometricRadius
  rw [pow_succ]
  ring

theorem geometricRadius_antitone : Antitone geometricRadius := by
  intro n m hnm
  exact pow_le_pow_right_of_le_one' (by norm_num : (1 / 2 : ℝ≥0) ≤ 1) hnm

theorem geometricRadius_tendsto_zero :
    Tendsto geometricRadius atTop (𝓝 0) := by
  exact NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one
    (by norm_num : (1 / 2 : ℝ≥0) < 1)

/-- Indices of the cofinal subnet.  A point records a precision level `n`
and an original index beyond the Cauchy threshold for that level. -/
structure WeightedSubnetIndex
    {ι : Type u} [Preorder ι] (threshold : ℕ → ι) where
  level : ℕ
  index : ι
  threshold_le : threshold level ≤ index

namespace WeightedSubnetIndex

variable {ι : Type u} [Preorder ι] {threshold : ℕ → ι}

/-- Moving forward either means staying at the identical index or moving
strictly to a finer precision level and forward in the original preorder. -/
instance : LE (WeightedSubnetIndex threshold) where
  le a b := a = b ∨ (a.level < b.level ∧ a.index ≤ b.index)

instance : Preorder (WeightedSubnetIndex threshold) where
  le := (· ≤ ·)
  le_refl a := Or.inl rfl
  le_trans a b c hab hbc := by
    rcases hab with rfl | ⟨habLevel, habIndex⟩
    · exact hbc
    rcases hbc with rfl | ⟨hbcLevel, hbcIndex⟩
    · exact Or.inr ⟨habLevel, habIndex⟩
    · exact Or.inr ⟨habLevel.trans hbcLevel,
        habIndex.trans hbcIndex⟩

theorem index_mono : Monotone
    (fun a : WeightedSubnetIndex threshold ↦ a.index) := by
  intro a b hab
  rcases hab with rfl | hab
  · exact le_rfl
  · exact hab.2

theorem level_le_of_le {a b : WeightedSubnetIndex threshold}
    (hab : a ≤ b) : a.level ≤ b.level := by
  rcases hab with rfl | hab
  · exact le_rfl
  · exact hab.1.le

theorem level_lt_of_le_of_ne {a b : WeightedSubnetIndex threshold}
    (hab : a ≤ b) (hne : a ≠ b) : a.level < b.level := by
  rcases hab with rfl | hab
  · exact (hne rfl).elim
  · exact hab.1

theorem isDirectedIndex
    (hdir : IsDirectedIndex ι) :
    IsDirectedIndex (WeightedSubnetIndex threshold) := by
  constructor
  · exact ⟨⟨0, threshold 0, le_rfl⟩⟩
  · intro a b
    obtain ⟨k₀, hak₀, hbk₀⟩ := hdir.2 a.index b.index
    let N := max a.level b.level + 1
    obtain ⟨k, hk₀, hNk⟩ := hdir.2 k₀ (threshold N)
    let c : WeightedSubnetIndex threshold := ⟨N, k, hNk⟩
    refine ⟨c, Or.inr ⟨?_, hak₀.trans hk₀⟩,
      Or.inr ⟨?_, hbk₀.trans hk₀⟩⟩
    · exact (le_max_left _ _).trans_lt (Nat.lt_succ_self _)
    · exact (le_max_right _ _).trans_lt (Nat.lt_succ_self _)

/-- The projection to the original index is cofinal. -/
theorem projection_cofinal
    (hdir : IsDirectedIndex ι) (i : ι) :
    ∃ a : WeightedSubnetIndex threshold, i ≤ a.index := by
  obtain ⟨k, hik, _hthreshold⟩ := hdir.2 i (threshold 0)
  exact ⟨⟨0, k, _hthreshold⟩, hik⟩

end WeightedSubnetIndex

/-- A cofinal monotone subnet of a Cauchy net has the same explicit
distance limsups, hence the same `d`-limits. -/
theorem netLimsup_edist_comp_eq
    {ι : Type v} {κ : Type w} [Preorder ι] [Preorder κ]
    (x : ι → X)
    (hdirκ : IsDirectedIndex κ)
    (hxCauchy : d.IsCauchyNet x)
    (φ : κ → ι) (hφmono : Monotone φ)
    (hφcofinal : ∀ i : ι, ∃ k : κ, i ≤ φ k)
    (y : X) :
    netLimsup (fun k ↦ d.edist (x (φ k)) y) =
      netLimsup (fun i ↦ d.edist (x i) y) := by
  apply le_antisymm
  · apply le_iInf
    intro i
    obtain ⟨k, hik⟩ := hφcofinal i
    refine (iInf_le (fun k₀ : κ ↦
      ⨆ l : κ, ⨆ (_h : k₀ ≤ l), d.edist (x (φ l)) y) k).trans ?_
    apply iSup_le
    intro l
    apply iSup_le
    intro hkl
    exact le_iSup_of_le (φ l)
      (le_iSup_of_le (hik.trans (hφmono hkl)) le_rfl)
  · apply ENNReal.le_of_forall_pos_le_add
    intro ε hε _hfinite
    obtain ⟨i₀, hi₀⟩ := hxCauchy ε hε
    refine (iInf_le (fun i : ι ↦
      ⨆ j : ι, ⨆ (_h : i ≤ j), d.edist (x j) y) i₀).trans ?_
    change (⨆ j : ι, ⨆ (_h : i₀ ≤ j), d.edist (x j) y) ≤
      (⨅ k : κ, ⨆ l : κ, ⨆ (_h : k ≤ l),
        d.edist (x (φ l)) y) + (ε : ℝ≥0∞)
    rw [ENNReal.iInf_add]
    apply le_iInf
    intro k
    obtain ⟨k₀, hi₀k₀⟩ := hφcofinal i₀
    obtain ⟨l, hkl, hk₀l⟩ := hdirκ.2 k k₀
    apply iSup_le
    intro j
    apply iSup_le
    intro hi₀j
    obtain ⟨m₀, hjm₀⟩ := hφcofinal j
    obtain ⟨m, hlm, hm₀m⟩ := hdirκ.2 l m₀
    have hjφm : j ≤ φ m := hjm₀.trans (hφmono hm₀m)
    have hsmall : d.edist (x j) (x (φ m)) < (ε : ℝ≥0∞) :=
      hi₀ j (φ m) hi₀j hjφm
    have htail : d.edist (x (φ m)) y ≤
        ⨆ n : κ, ⨆ (_h : k ≤ n), d.edist (x (φ n)) y :=
      le_iSup_of_le m (le_iSup_of_le (hkl.trans hlm) le_rfl)
    calc
      d.edist (x j) y
          ≤ d.edist (x j) (x (φ m)) + d.edist (x (φ m)) y :=
        d.edist_triangle _ _ _
      _ ≤ (ε : ℝ≥0∞) +
          (⨆ n : κ, ⨆ (_h : k ≤ n), d.edist (x (φ n)) y) :=
        add_le_add hsmall.le htail
      _ = (⨆ n : κ, ⨆ (_h : k ≤ n),
          d.edist (x (φ n)) y) + (ε : ℝ≥0∞) := add_comm _ _

theorem IsDLimit.comp_cofinal
    {ι : Type v} {κ : Type w} [Preorder ι] [Preorder κ]
    {x : ι → X} {x₀ : X}
    (hxLimit : d.IsDLimit x x₀)
    (hdirκ : IsDirectedIndex κ)
    (hxCauchy : d.IsCauchyNet x)
    (φ : κ → ι) (hφmono : Monotone φ)
    (hφcofinal : ∀ i : ι, ∃ k : κ, i ≤ φ k) :
    d.IsDLimit (fun k ↦ x (φ k)) x₀ := by
  intro y
  rw [netLimsup_edist_comp_eq d x hdirκ hxCauchy φ hφmono
    hφcofinal y]
  exact hxLimit y

/-- Data of the canonical geometrically weighted cofinal subnet. -/
structure CauchyWeightedSubnet
    {ι : Type u} [Preorder ι] (x : ι → X) where
  Index : Type u
  indexPreorder : Preorder Index
  directed : IsDirectedIndex Index
  map : Index → ι
  map_monotone : Monotone map
  map_cofinal : ∀ i : ι, ∃ k : Index, i ≤ map k
  radius : Index → ℝ≥0
  formalBall_monotone : Monotone
    (fun k ↦ (⟨x (map k), radius k⟩ : d.FormalBall))
  radius_eventually_lt : ∀ ε : ℝ≥0, 0 < ε →
    ∃ k : Index, ∀ l : Index, k ≤ l → radius l < ε

namespace CauchyWeightedSubnet

attribute [instance] indexPreorder

/-- Construction of a Cauchy-weighted cofinal subnet from the manuscript's
one-sided Cauchy condition. -/
noncomputable def ofCauchy
    {ι : Type u} [Preorder ι]
    (x : ι → X) (hdir : IsDirectedIndex ι)
    (hx : d.IsCauchyNet x) : d.CauchyWeightedSubnet x := by
  choose threshold hthreshold using
    fun n ↦ hx (geometricRadius (n + 1)) (geometricRadius_pos (n + 1))
  let K := WeightedSubnetIndex threshold
  let map : K → ι := fun k ↦ k.index
  let radius : K → ℝ≥0 := fun k ↦ geometricRadius k.level
  have hKdir : IsDirectedIndex K :=
    WeightedSubnetIndex.isDirectedIndex hdir
  have hmapMono : Monotone map := WeightedSubnetIndex.index_mono
  have hballMono : Monotone
      (fun k : K ↦ (⟨x (map k), radius k⟩ : d.FormalBall)) := by
    intro a b hab
    rcases hab with rfl | hab
    · exact le_rfl
    rw [FormalBall.le_def]
    have hdist : d.edist (x a.index) (x b.index) <
        (geometricRadius (a.level + 1) : ℝ≥0∞) :=
      hthreshold a.level a.index b.index a.threshold_le hab.2
    have hlevel : a.level + 1 ≤ b.level := hab.1
    have hradius : geometricRadius b.level ≤
        geometricRadius (a.level + 1) :=
      geometricRadius_antitone hlevel
    calc
      d.edist (x a.index) (x b.index) +
          (geometricRadius b.level : ℝ≥0∞)
          ≤ (geometricRadius (a.level + 1) : ℝ≥0∞) +
              (geometricRadius (a.level + 1) : ℝ≥0∞) :=
        add_le_add hdist.le (ENNReal.coe_le_coe.mpr hradius)
      _ = (geometricRadius a.level : ℝ≥0∞) := by
        exact_mod_cast geometricRadius_succ_add a.level
  have hradiusSmall : ∀ ε : ℝ≥0, 0 < ε →
      ∃ k : K, ∀ l : K, k ≤ l → radius l < ε := by
    intro ε hε
    have hevent : ∀ᶠ n in atTop, geometricRadius n < ε :=
      (tendsto_order.1 geometricRadius_tendsto_zero).2 ε hε
    obtain ⟨N, hN⟩ := eventually_atTop.1 hevent
    let k : K := ⟨N, threshold N, le_rfl⟩
    refine ⟨k, ?_⟩
    intro l hkl
    exact (geometricRadius_antitone
      (WeightedSubnetIndex.level_le_of_le hkl)).trans_lt (hN N le_rfl)
  exact
    { Index := K
      indexPreorder := inferInstance
      directed := hKdir
      map := map
      map_monotone := hmapMono
      map_cofinal := WeightedSubnetIndex.projection_cofinal hdir
      radius := radius
      formalBall_monotone := hballMono
      radius_eventually_lt := hradiusSmall }

/-- The selected centers retain the original `d`-limit. -/
theorem center_isDLimit
    {ι : Type u} [Preorder ι]
    {x : ι → X} {x₀ : X}
    (W : d.CauchyWeightedSubnet x)
    (hxCauchy : d.IsCauchyNet x)
    (hxLimit : d.IsDLimit x x₀) :
    d.IsDLimit (fun k ↦ x (W.map k)) x₀ :=
  hxLimit.comp_cofinal d W.directed hxCauchy W.map
    W.map_monotone W.map_cofinal

/-- The weighted subnet has the expected zero-radius formal-ball supremum. -/
theorem formalBall_isLUB
    {ι : Type u} [Preorder ι]
    {x : ι → X} {x₀ : X}
    (W : d.CauchyWeightedSubnet x)
    (hxCauchy : d.IsCauchyNet x)
    (hxLimit : d.IsDLimit x x₀) :
    IsLUB
      (Set.range (fun k ↦
        (⟨x (W.map k), W.radius k⟩ : d.FormalBall)))
      (⟨x₀, 0⟩ : d.FormalBall) :=
  zeroRadius_isLUB_of_center_isDLimit d
    (fun k ↦ (⟨x (W.map k), W.radius k⟩ : d.FormalBall))
    W.directed W.formalBall_monotone W.radius_eventually_lt x₀
    (CauchyWeightedSubnet.center_isDLimit d W hxCauchy hxLimit)

end CauchyWeightedSubnet

end QuasiMetric
end LipschitzYonedaFinalTopology
