import CoreCompactNonSober.CompactOrderedConvergence
import CoreCompactNonSober.DefinitionChecks
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Constructions
import Mathlib.Topology.Order.Lattice

/-!
# Scott closed sets in compact metrizable topological meet-semilattices

Source: the full proof of `lem:scott-ambient`. Nested metric neighborhoods
control finite tail meets, compact order convergence controls their infinite
infima, and a directed supremum recovers the closure point.

The proof does not assume that small neighborhoods are subsemilattices.
-/

set_option autoImplicit false

universe u

namespace CoreCompactNonSober.CompactSemilattice

open Set Filter Metric
open scoped Topology

variable {P : Type u} [CompleteLattice P] [MetricSpace P] [ContinuousInf P]

private theorem smallRadius_exists (x : P) (r b : ℝ) (hr : 0 < r) (hb : 0 < b) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ r ∧ δ ≤ b ∧
      ∀ y z : P, dist y x ≤ δ → dist z x ≤ δ → dist (y ⊓ z) x ≤ r := by
  have hc : ContinuousAt (fun yz : P × P ↦ yz.1 ⊓ yz.2) (x, x) :=
    continuous_inf.continuousAt
  obtain ⟨η, hη, hηinf⟩ := (Metric.continuousAt_iff.mp hc) r hr
  let δ := min (η / 2) (min r b)
  have hδ : 0 < δ := lt_min (by linarith) (lt_min hr hb)
  refine ⟨δ, hδ, (min_le_right _ _).trans (min_le_left _ _),
    (min_le_right _ _).trans (min_le_right _ _), ?_⟩
  intro y z hy hz
  have hδη : δ < η := (min_le_left _ _).trans_lt (by linarith)
  have hprod : dist (y, z) (x, x) < η := by
    rw [Prod.dist_eq]
    exact max_lt (hy.trans_lt hδη) (hz.trans_lt hδη)
  have h := hηinf hprod
  simpa only [inf_idem] using h.le

private abbrev PositiveRadius := {r : ℝ // 0 < r}

private noncomputable def radiusStep (x : P) (n : ℕ) (r : PositiveRadius) : ℝ :=
  Classical.choose (smallRadius_exists x r.val (1 / ((n + 2 : ℕ) : ℝ))
    r.property (by positivity))

private theorem radiusStep_spec (x : P) (n : ℕ) (r : PositiveRadius) :
    0 < radiusStep x n r ∧ radiusStep x n r ≤ r.val ∧
      radiusStep x n r ≤ 1 / ((n + 2 : ℕ) : ℝ) ∧
      ∀ y z : P, dist y x ≤ radiusStep x n r → dist z x ≤ radiusStep x n r →
        dist (y ⊓ z) x ≤ r.val :=
  Classical.choose_spec (smallRadius_exists x r.val (1 / ((n + 2 : ℕ) : ℝ))
    r.property (by positivity))

private noncomputable def radii (x : P) : ℕ → PositiveRadius
  | 0 => ⟨1, zero_lt_one⟩
  | n + 1 => ⟨radiusStep x n (radii x n), (radiusStep_spec x n (radii x n)).1⟩

private theorem radii_succ_le (x : P) (n : ℕ) :
    (radii x (n + 1)).val ≤ (radii x n).val :=
  (radiusStep_spec x n (radii x n)).2.1

private theorem radii_le_inv (x : P) (n : ℕ) :
    (radii x n).val ≤ 1 / ((n + 1 : ℕ) : ℝ) := by
  cases n with
  | zero => norm_num [radii]
  | succ n =>
    simpa only [Nat.succ_eq_add_one, Nat.add_assoc] using
      (radiusStep_spec x n (radii x n)).2.2.1

private theorem radii_inf_bound (x : P) (n : ℕ) (y z : P)
    (hy : dist y x ≤ (radii x (n + 1)).val)
    (hz : dist z x ≤ (radii x (n + 1)).val) :
    dist (y ⊓ z) x ≤ (radii x n).val :=
  (radiusStep_spec x n (radii x n)).2.2.2 y z hy hz

private theorem radii_tendsto (x : P) :
    Tendsto (fun n : ℕ ↦ (radii x n).val) atTop (𝓝 (0 : ℝ)) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
  have hNmul : 1 < (N : ℝ) * ε := (div_lt_iff₀ hε).mp hN
  refine ⟨N, ?_⟩
  intro n hn
  rw [Real.dist_eq, sub_zero, abs_of_pos (radii x n).property]
  apply (radii_le_inv x n).trans_lt
  apply (div_lt_iff₀ (by positivity)).mpr
  have hnreal : (N : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : N ≤ n + 1)
  nlinarith

private def tailMeet (a : ℕ → P) (n : ℕ) : ℕ → P
  | 0 => a n
  | k + 1 => a n ⊓ tailMeet a (n + 1) k

omit [MetricSpace P] [ContinuousInf P] in
private theorem le_tailMeet_iff (a : ℕ → P) (n k : ℕ) (q : P) :
    q ≤ tailMeet a n k ↔ ∀ l ≤ k, q ≤ a (n + l) := by
  induction k generalizing n with
  | zero =>
    constructor
    · intro h l hl
      have hl0 : l = 0 := by omega
      subst l
      simpa [tailMeet] using h
    · intro h
      simpa [tailMeet] using h 0 le_rfl
  | succ k ih =>
    constructor
    · intro h l hl
      cases l with
      | zero => simpa using h.trans (inf_le_left : a n ⊓ tailMeet a (n + 1) k ≤ a n)
      | succ l =>
        have ht : q ≤ tailMeet a (n + 1) k := h.trans inf_le_right
        have := (ih (n + 1)).mp ht l (by omega)
        simpa only [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this
    · intro h
      apply le_inf
      · simpa using h 0 (by omega)
      · apply (ih (n + 1)).mpr
        intro l hl
        have := h (l + 1) (by omega)
        simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this

omit [MetricSpace P] [ContinuousInf P] in
private theorem tailMeet_antitone (a : ℕ → P) (n : ℕ) : Antitone (tailMeet a n) := by
  apply antitone_nat_of_succ_le
  intro k
  apply (le_tailMeet_iff a n k _).mpr
  intro l hl
  exact (le_tailMeet_iff a n (k + 1) _).mp le_rfl l (by omega)

private theorem tailMeet_dist_le (x : P) (a : ℕ → P)
    (ha : ∀ n, dist (a n) x ≤ (radii x (n + 1)).val) (n k : ℕ) :
    dist (tailMeet a n k) x ≤ (radii x n).val := by
  induction k generalizing n with
  | zero => exact (ha n).trans (radii_succ_le x n)
  | succ k ih => exact radii_inf_bound x n _ _ (ha n) (ih (n + 1))

private noncomputable def tailInf (a : ℕ → P) (n : ℕ) : P :=
  sInf (Set.range (fun k : ℕ ↦ a (n + k)))

omit [MetricSpace P] [ContinuousInf P] in
private theorem tailInf_isGLB (a : ℕ → P) (n : ℕ) :
    IsGLB (Set.range (tailMeet a n)) (tailInf a n) := by
  constructor
  · rintro _ ⟨k, rfl⟩
    apply (le_tailMeet_iff a n k _).mpr
    intro l _
    exact sInf_le (Set.mem_range_self l)
  · intro q hq
    apply le_sInf
    rintro _ ⟨k, rfl⟩
    exact (hq (Set.mem_range_self k)).trans
      ((le_tailMeet_iff a n k _).mp le_rfl k le_rfl)

variable [CompactSpace P] [OrderClosedTopology P]

private theorem tailInf_dist_le (x : P) (a : ℕ → P)
    (ha : ∀ n, dist (a n) x ≤ (radii x (n + 1)).val) (n : ℕ) :
    dist (tailInf a n) x ≤ (radii x n).val := by
  letI : InfConvergenceClass P := compact_infConvergenceClass
  have ht : Tendsto (tailMeet a n) atTop (𝓝 (tailInf a n)) :=
    tendsto_atTop_isGLB (tailMeet_antitone a n) (tailInf_isGLB a n)
  apply Metric.mem_closedBall.mp
  exact isClosed_closedBall.mem_of_tendsto ht
    (Filter.Eventually.of_forall (fun k ↦ Metric.mem_closedBall.mpr (tailMeet_dist_le x a ha n k)))

omit [MetricSpace P] [CompactSpace P] [OrderClosedTopology P] [ContinuousInf P] in
private theorem tailInf_monotone (a : ℕ → P) : Monotone (tailInf a) := by
  intro n m hnm
  apply le_sInf
  rintro _ ⟨k, rfl⟩
  have heq : n + (m - n + k) = m + k := by omega
  exact sInf_le ⟨m - n + k, congrArg a heq⟩

/-- The nontrivial direction of `lem:scott-ambient`: every intrinsic
Scott-closed set is closed for the auxiliary metric topology. -/
theorem isClosed_of_isScottClosed {F : Set P} (hF : IsScottClosed F) : IsClosed F := by
  apply closure_eq_iff_isClosed.mp
  apply Set.Subset.antisymm ?_ subset_closure
  intro x hx
  have hchoose : ∀ n : ℕ, ∃ a ∈ F, dist a x ≤ (radii x (n + 1)).val := by
    intro n
    obtain ⟨a, ha, hdist⟩ := (Metric.mem_closure_iff.mp hx)
      (radii x (n + 1)).val (radii x (n + 1)).property
    exact ⟨a, ha, (dist_comm a x ▸ hdist).le⟩
  choose a haF hadist using hchoose
  let b : ℕ → P := tailInf a
  have hbF : ∀ n, b n ∈ F := by
    intro n
    have hbn : b n ≤ a n := sInf_le ⟨0, by simp⟩
    exact hF.1 hbn (haF n)
  have hbmono : Monotone b := tailInf_monotone a
  have hbX : Tendsto b atTop (𝓝 x) := by
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp (radii_tendsto x)) ε hε
    refine ⟨N, ?_⟩
    intro n hn
    have hr := hN n hn
    rw [Real.dist_eq, sub_zero, abs_of_pos (radii x n).property] at hr
    exact (tailInf_dist_le x a hadist n).trans_lt hr
  letI : SupConvergenceClass P := compact_supConvergenceClass
  have hbSup : Tendsto b atTop (𝓝 (sSup (Set.range b))) :=
    tendsto_atTop_isLUB hbmono (isLUB_sSup (Set.range b))
  have heq : sSup (Set.range b) = x := tendsto_nhds_unique hbSup hbX
  rw [← heq]
  apply hF.2 (Set.range b) (by rintro _ ⟨n, rfl⟩; exact hbF n)
    ⟨Set.range_nonempty b, hbmono.directed_le.directedOn_range⟩ _ (isLUB_sSup _)

omit [ContinuousInf P] in
theorem isScottClosed_of_closed_lower {F : Set P}
    (hF : IsClosed F) (hlower : IsLowerSet F) : IsScottClosed F := by
  refine ⟨hlower, ?_⟩
  intro E hEF hE p hp
  haveI : Nonempty E := hE.1.to_subtype
  haveI : IsDirectedOrder E := ⟨fun a b ↦ by
    obtain ⟨c, hc, hac, hbc⟩ := hE.2 a a.property b b.property
    exact ⟨⟨c, hc⟩, hac, hbc⟩⟩
  letI : SupConvergenceClass P := compact_supConvergenceClass
  have ht : Tendsto (Subtype.val : E → P) atTop (𝓝 p) :=
    SupConvergenceClass.tendsto_coe_atTop_isLUB p E hp
  exact hF.mem_of_tendsto ht (Filter.Eventually.of_forall (fun e : E ↦ hEF e.property))

/-- The complete closed-set identification in `lem:scott-ambient`. -/
theorem isScottClosed_iff_closed_lower (F : Set P) :
    IsScottClosed F ↔ IsClosed F ∧ IsLowerSet F :=
  ⟨fun h ↦ ⟨isClosed_of_isScottClosed h, h.1⟩,
    fun h ↦ isScottClosed_of_closed_lower h.1 h.2⟩

/-- A convergent sequence in a compact metrizable topological meet-semilattice
has a subsequence with a common lower bound in any prescribed neighborhood of
its limit. This uses the same nested-meet estimates as the Scott-closed-set
identification above, with no positivity or order approximation assumption. -/
theorem exists_subsequence_lowerBound_mem_of_tendsto
    {a : ℕ → P} {x : P} (ha : Tendsto a atTop (𝓝 x))
    {U : Set P} (hU : IsOpen U) (hxU : x ∈ U) :
    ∃ (φ : ℕ → ℕ), StrictMono φ ∧ ∃ b ∈ U, ∀ n, b ≤ a (φ n) := by
  classical
  have hnear : ∀ n : ℕ, ∃ N : ℕ, ∀ k ≥ N,
      dist (a k) x ≤ (radii x (n + 1)).val := by
    intro n
    obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp ha)
      (radii x (n + 1)).val (radii x (n + 1)).property
    exact ⟨N, fun k hk ↦ (hN k hk).le⟩
  choose N hN using hnear
  let ψ : ℕ → ℕ := Nat.rec (N 0) (fun n prev ↦ max (N (n + 1)) (prev + 1))
  have hψN : ∀ n, N n ≤ ψ n := by
    intro n
    cases n with
    | zero => exact le_rfl
    | succ n => exact le_max_left _ _
  have hψmono : StrictMono ψ := strictMono_nat_of_lt_succ (fun n ↦ by
    exact (Nat.lt_succ_self (ψ n)).trans_le (le_max_right _ _))
  let c : ℕ → P := a ∘ ψ
  have hc : ∀ n, dist (c n) x ≤ (radii x (n + 1)).val :=
    fun n ↦ hN n (ψ n) (hψN n)
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU x hxU
  obtain ⟨K, hK⟩ := (Metric.tendsto_atTop.mp (radii_tendsto x)) ε hε
  have hrK : (radii x K).val < ε := by
    simpa only [Real.dist_eq, sub_zero, abs_of_pos (radii x K).property] using hK K le_rfl
  refine ⟨fun n ↦ ψ (K + n), hψmono.comp (fun _ _ h ↦ Nat.add_lt_add_left h K),
    tailInf c K, ?_, ?_⟩
  · apply hball
    exact (tailInf_dist_le x c hc K).trans_lt hrK
  · intro n
    exact sInf_le (Set.mem_range_self n)

end CoreCompactNonSober.CompactSemilattice
