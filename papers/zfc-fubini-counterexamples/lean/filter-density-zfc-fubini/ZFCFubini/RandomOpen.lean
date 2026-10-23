import ZFCFubini.ParameterMeasure

/-!
Source random-open continuity, adapted from CHFubini/RandomOpenContinuity.lean,
SHA256 2a64d18bf86e65aaf033babd4654cf43b7f09ec72151eba663e0a090dd363ced.
The approximants are finite shrinking balls, following the printed proof route.
Initial segments and a common shrink parameter form a proved cofinal
parametrization of the source's arbitrary finite sets and separate radii.
-/

set_option autoImplicit false
open Set Filter TopologicalSpace Topology
open scoped Topology

namespace ZFCFubini

universe u v

/-- Actual ordinary union of metric balls. -/
def randomBallUnion {T : Type u} [PseudoMetricSpace T]
    (r : ℕ → ℝ) (s : ℕ → T) : Set T := ⋃ n, Metric.ball (s n) (r n)

theorem randomBallUnion_isOpen {T : Type u} [PseudoMetricSpace T]
    (r : ℕ → ℝ) (s : ℕ → T) : IsOpen (randomBallUnion r s) :=
  isOpen_iUnion (fun _ => Metric.isOpen_ball)

theorem randomBallUnion_contains_coordinate {T : Type u} [PseudoMetricSpace T]
    (r : ℕ → ℝ) (hr : ∀ n, 0 < r n) (s : ℕ → T) (n : ℕ) :
    s n ∈ randomBallUnion r s :=
  mem_iUnion.mpr ⟨n, Metric.mem_ball_self (hr n)⟩

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


/-- Actual pullback of the random union of metric balls. -/
def randomOpenPullback {A : Type u} [TopologicalSpace A]
    {T : Type v} [PseudoMetricSpace T]
    (h : A → T) (hh : Continuous h) (r : ℕ → ℝ) (s : ℕ → T) : Opens A :=
  ⟨h ⁻¹' randomBallUnion r s, (randomBallUnion_isOpen r s).preimage hh⟩

/-- Adapted cofinal parametrization by initial segments and a common positive
shrink amount. Balls with nonpositive radius are empty in mathlib. -/
def shrinkingOpen {A : Type u} [TopologicalSpace A]
    {T : Type v} [PseudoMetricSpace T]
    (h : A → T) (hh : Continuous h) (r : ℕ → ℝ) (s₀ : ℕ → T)
    (m k : ℕ) : Opens A :=
  ⟨h ⁻¹' ⋃ n : Fin m, Metric.ball (s₀ n) (r n - 1 / (k + 1 : ℝ)),
    (isOpen_iUnion (fun _ => Metric.isOpen_ball)).preimage hh⟩

theorem shrinkingOpen_le_randomOpenPullback
    {A : Type u} [TopologicalSpace A] {T : Type v} [PseudoMetricSpace T]
    (h : A → T) (hh : Continuous h) (r : ℕ → ℝ) (s₀ : ℕ → T)
    (m k : ℕ) : shrinkingOpen h hh r s₀ m k ≤ randomOpenPullback h hh r s₀ := by
  intro a ha
  obtain ⟨n, hn⟩ := mem_iUnion.mp ha
  apply mem_iUnion.mpr
  refine ⟨n.1, ?_⟩
  change dist (h a) (s₀ n) < r n - 1 / (k + 1 : ℝ) at hn
  change dist (h a) (s₀ n) < r n
  linarith [show 0 < 1 / (k + 1 : ℝ) by positivity]

theorem shrinkingOpen_mono
    {A : Type u} [TopologicalSpace A] {T : Type v} [PseudoMetricSpace T]
    (h : A → T) (hh : Continuous h) (r : ℕ → ℝ) (s₀ : ℕ → T)
    {m m' k k' : ℕ} (hm : m ≤ m') (hk : k ≤ k') :
    shrinkingOpen h hh r s₀ m k ≤ shrinkingOpen h hh r s₀ m' k' := by
  intro a ha
  obtain ⟨n, hn⟩ := mem_iUnion.mp ha
  apply mem_iUnion.mpr
  refine ⟨⟨n.1, lt_of_lt_of_le n.2 hm⟩, ?_⟩
  change dist (h a) (s₀ n.1) < r n.1 - 1 / (k + 1 : ℝ) at hn
  change dist (h a) (s₀ n.1) < r n.1 - 1 / (k' + 1 : ℝ)
  have hkk : (k + 1 : ℝ) ≤ (k' + 1 : ℝ) := by exact_mod_cast Nat.succ_le_succ hk
  have hi := one_div_le_one_div_of_le (by positivity : 0 < (k + 1 : ℝ)) hkk
  linarith

theorem randomOpenPullback_mem_shrinkingOpen
    {A : Type u} [TopologicalSpace A] {T : Type v} [PseudoMetricSpace T]
    (h : A → T) (hh : Continuous h) (r : ℕ → ℝ) (s₀ : ℕ → T)
    {a : A} (ha : a ∈ randomOpenPullback h hh r s₀) :
    ∃ m k : ℕ, a ∈ shrinkingOpen h hh r s₀ m k := by
  obtain ⟨n, hn⟩ := mem_iUnion.mp ha
  change dist (h a) (s₀ n) < r n at hn
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt (sub_pos.mpr hn)
  refine ⟨n + 1, k, mem_iUnion.mpr ⟨⟨n, Nat.lt_succ_self n⟩, ?_⟩⟩
  change dist (h a) (s₀ n) < r n - 1 / (k + 1 : ℝ)
  linarith

theorem shrinkingOpen_directed
    {A : Type u} [TopologicalSpace A] {T : Type v} [PseudoMetricSpace T]
    (h : A → T) (hh : Continuous h) (r : ℕ → ℝ) (s₀ : ℕ → T) :
    Directed (· ≤ ·) (fun p : ℕ × ℕ => shrinkingOpen h hh r s₀ p.1 p.2) := by
  intro p q
  refine ⟨(max p.1 q.1, max p.2 q.2), ?_, ?_⟩
  · exact shrinkingOpen_mono h hh r s₀ (le_max_left _ _) (le_max_left _ _)
  · exact shrinkingOpen_mono h hh r s₀ (le_max_right _ _) (le_max_right _ _)

theorem shrinkingOpen_isLUB
    {A : Type u} [TopologicalSpace A] {T : Type v} [PseudoMetricSpace T]
    (h : A → T) (hh : Continuous h) (r : ℕ → ℝ) (s₀ : ℕ → T) :
    IsLUB (range (fun p : ℕ × ℕ => shrinkingOpen h hh r s₀ p.1 p.2))
      (randomOpenPullback h hh r s₀) := by
  refine ⟨?_, ?_⟩
  · rintro V ⟨p, rfl⟩
    exact shrinkingOpen_le_randomOpenPullback h hh r s₀ p.1 p.2
  · intro V hV a ha
    obtain ⟨m, k, hmk⟩ := randomOpenPullback_mem_shrinkingOpen h hh r s₀ ha
    exact hV (mem_range_self (m, k)) hmk

/-- A fixed finite shrinking approximation remains included in `R_s` on an
ordinary open neighborhood of its center sample. -/
theorem shrinkingOpen_local_subset
    {A : Type u} [TopologicalSpace A] {T : Type v} [PseudoMetricSpace T]
    (h : A → T) (hh : Continuous h) (r : ℕ → ℝ) (s₀ : ℕ → T)
    (m k : ℕ) :
    ∃ N : Set (ℕ → T), IsOpen N ∧ s₀ ∈ N ∧
      ∀ s ∈ N, shrinkingOpen h hh r s₀ m k ≤ randomOpenPullback h hh r s := by
  let δ : ℝ := 1 / (2 * (k + 1 : ℝ))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  let N : Set (ℕ → T) :=
    ⋂ n : Fin m, (fun s : ℕ → T => s n) ⁻¹' Metric.ball (s₀ n) δ
  have ho : IsOpen N :=
    isOpen_iInter_of_finite (fun n => Metric.isOpen_ball.preimage (continuous_apply n.1))
  have hs₀ : s₀ ∈ N := mem_iInter.mpr (fun _ => Metric.mem_ball_self hδ)
  refine ⟨N, ho, hs₀, fun s hs a ha => ?_⟩
  obtain ⟨n, hn⟩ := mem_iUnion.mp ha
  have hsn : dist (s n) (s₀ n) < δ := mem_iInter.mp hs n
  apply mem_iUnion.mpr
  refine ⟨n.1, ?_⟩
  change dist (h a) (s n) < r n
  change dist (h a) (s₀ n) < r n - 1 / (k + 1 : ℝ) at hn
  have htriangle := dist_triangle (h a) (s₀ n) (s n)
  have hδsmall : δ ≤ 1 / (k + 1 : ℝ) := by
    dsimp [δ]
    apply one_div_le_one_div_of_le (by positivity)
    linarith
  rw [dist_comm (s₀ n) (s n)] at htriangle
  linarith

/-- Source `lem:random-continuity`: ordinary product topology in the domain,
full intrinsic Scott topology on the actual lattice of opens in the target. -/
theorem randomOpenPullback_continuous
    {A : Type u} [TopologicalSpace A] {T : Type v} [PseudoMetricSpace T]
    (h : A → T) (hh : Continuous h) (r : ℕ → ℝ) :
    Continuous (fun s : ℕ → T => WithScott.toScott (randomOpenPullback h hh r s)) := by
  apply continuous_def.mpr
  intro H hH
  apply isOpen_iff_mem_nhds.mpr
  intro s₀ hs₀
  have hup : IsUpperSet H := IsScott.isUpperSet_of_isOpen (D := univ) hH
  have hacc : DirSupInaccOn univ H :=
    (IsScott.isOpen_iff_isUpperSet_and_dirSupInaccOn (D := univ)).mp hH |>.2
  let approx : ℕ × ℕ → WithScott (Opens A) :=
    fun p => WithScott.toScott (shrinkingOpen h hh r s₀ p.1 p.2)
  have hd : Directed (· ≤ ·) approx := shrinkingOpen_directed h hh r s₀
  have hlub : IsLUB (range approx) (WithScott.toScott (randomOpenPullback h hh r s₀)) :=
    shrinkingOpen_isLUB h hh r s₀
  obtain ⟨V, ⟨p, rfl⟩, hVH⟩ :=
    hacc (mem_univ _) (range_nonempty approx) hd.directedOn_range hlub hs₀
  obtain ⟨N, hNo, hs₀N, hNsub⟩ := shrinkingOpen_local_subset h hh r s₀ p.1 p.2
  apply mem_of_superset (hNo.mem_nhds hs₀N)
  intro s hs
  exact hup (hNsub s hs) hVH

/-- Literal auxiliary data in the NEW source proof: arbitrary finite F and
separately chosen positive s_i below r_i. -/
structure BallApproximation (r : ℕ → ℝ) where
  support : Finset ℕ
  innerRadius : ℕ → ℝ
  radius_pos : ∀ n ∈ support, 0 < innerRadius n
  radius_lt : ∀ n ∈ support, innerRadius n < r n

instance (r : ℕ → ℝ) : Nonempty (BallApproximation r) :=
  ⟨⟨∅, fun _ => 0, by simp, by simp⟩⟩

noncomputable def BallApproximation.join {r : ℕ → ℝ}
    (a b : BallApproximation r) : BallApproximation r := by
  classical
  refine
    { support := a.support ∪ b.support
      innerRadius := fun n => if n ∈ a.support then
        (if n ∈ b.support then max (a.innerRadius n) (b.innerRadius n) else a.innerRadius n)
        else b.innerRadius n
      radius_pos := ?_
      radius_lt := ?_ }
  · intro n hn
    split_ifs with ha hb
    · exact lt_max_of_lt_left (a.radius_pos n ha)
    · exact a.radius_pos n ha
    · exact b.radius_pos n ((Finset.mem_union.mp hn).resolve_left ha)
  · intro n hn
    split_ifs with ha hb
    · exact max_lt (a.radius_lt n ha) (b.radius_lt n hb)
    · exact a.radius_lt n ha
    · exact b.radius_lt n ((Finset.mem_union.mp hn).resolve_left ha)

def finiteShrinkingOpen {A : Type u} [TopologicalSpace A]
    {T : Type v} [PseudoMetricSpace T] (h : A → T) (hh : Continuous h)
    (r : ℕ → ℝ) (t : ℕ → T) (a : BallApproximation r) : Opens A :=
  ⟨h ⁻¹' ⋃ n ∈ a.support, Metric.ball (t n) (a.innerRadius n),
    (isOpen_iUnion (fun _ => isOpen_iUnion (fun _ => Metric.isOpen_ball))).preimage hh⟩

theorem finiteShrinkingOpen_le_randomOpen
    {A : Type u} [TopologicalSpace A] {T : Type v} [PseudoMetricSpace T]
    (h : A → T) (hh : Continuous h) (r : ℕ → ℝ) (t : ℕ → T)
    (a : BallApproximation r) : finiteShrinkingOpen h hh r t a ≤ randomOpenPullback h hh r t := by
  intro x hx
  obtain ⟨n, hn, hxn⟩ := mem_iUnion₂.mp hx
  exact mem_iUnion.mpr ⟨n, Metric.ball_subset_ball (a.radius_lt n hn).le hxn⟩

theorem finiteShrinkingOpen_directed
    {A : Type u} [TopologicalSpace A] {T : Type v} [PseudoMetricSpace T]
    (h : A → T) (hh : Continuous h) (r : ℕ → ℝ) (t : ℕ → T) :
    Directed (· ≤ ·) (finiteShrinkingOpen h hh r t) := by
  classical
  intro a b
  refine ⟨a.join b, ?_, ?_⟩
  · intro x hx
    obtain ⟨n, hn, hxn⟩ := mem_iUnion₂.mp hx
    refine mem_iUnion₂.mpr ⟨n, Finset.mem_union_left _ hn, ?_⟩
    apply Metric.ball_subset_ball _ hxn
    by_cases hb : n ∈ b.support
    · simp [BallApproximation.join, hn, hb]
    · simp [BallApproximation.join, hn, hb]
  · intro x hx
    obtain ⟨n, hn, hxn⟩ := mem_iUnion₂.mp hx
    refine mem_iUnion₂.mpr ⟨n, Finset.mem_union_right _ hn, ?_⟩
    apply Metric.ball_subset_ball _ hxn
    by_cases ha : n ∈ a.support
    · simp [BallApproximation.join, ha, hn]
    · simp [BallApproximation.join, ha]

theorem finiteShrinkingOpen_isLUB
    {A : Type u} [TopologicalSpace A] {T : Type v} [PseudoMetricSpace T]
    (h : A → T) (hh : Continuous h) (r : ℕ → ℝ) (t : ℕ → T) :
    IsLUB (range (finiteShrinkingOpen h hh r t)) (randomOpenPullback h hh r t) := by
  classical
  refine ⟨?_, ?_⟩
  · rintro V ⟨a, rfl⟩
    exact finiteShrinkingOpen_le_randomOpen h hh r t a
  · intro V hV x hx
    obtain ⟨n, hn⟩ := mem_iUnion.mp hx
    change dist (h x) (t n) < r n at hn
    obtain ⟨s, hds, hsr⟩ := exists_between hn
    let a : BallApproximation r :=
      { support := {n}
        innerRadius := fun _ => s
        radius_pos := by intro k hk; simpa using (lt_of_le_of_lt dist_nonneg hds)
        radius_lt := by intro k hk; obtain rfl := Finset.mem_singleton.mp hk; exact hsr }
    apply hV (mem_range_self a)
    exact mem_iUnion₂.mpr ⟨n, Finset.mem_singleton_self n, hds⟩

theorem finiteShrinkingOpen_local_subset
    {A : Type u} [TopologicalSpace A] {T : Type v} [PseudoMetricSpace T]
    (h : A → T) (hh : Continuous h) (r : ℕ → ℝ) (t : ℕ → T)
    (a : BallApproximation r) :
    ∃ N : Set (ℕ → T), IsOpen N ∧ t ∈ N ∧
      ∀ u ∈ N, finiteShrinkingOpen h hh r t a ≤ randomOpenPullback h hh r u := by
  let N : Set (ℕ → T) := ⋂ n : a.support,
    (fun u : ℕ → T => u n) ⁻¹' Metric.ball (t n) (r n - a.innerRadius n)
  have hNo : IsOpen N :=
    isOpen_iInter_of_finite (fun n => Metric.isOpen_ball.preimage (continuous_apply n.1))
  have htN : t ∈ N := mem_iInter.mpr (fun n =>
    Metric.mem_ball_self (sub_pos.mpr (a.radius_lt n n.2)))
  refine ⟨N, hNo, htN, fun u hu x hx => ?_⟩
  obtain ⟨n, hn, hxn⟩ := mem_iUnion₂.mp hx
  have hun : dist (u n) (t n) < r n - a.innerRadius n := mem_iInter.mp hu ⟨n, hn⟩
  refine mem_iUnion.mpr ⟨n, ?_⟩
  change dist (h x) (u n) < r n
  change dist (h x) (t n) < a.innerRadius n at hxn
  have htri := dist_triangle (h x) (t n) (u n)
  rw [dist_comm (t n) (u n)] at htri
  linarith

/-- Every literal source approximation is contained in one initial-segment
common-shrink approximation; this proves the advertised cofinal relation. -/
theorem finiteShrinkingOpen_le_common_shrink
    {A : Type u} [TopologicalSpace A] {T : Type v} [PseudoMetricSpace T]
    (h : A → T) (hh : Continuous h) (r : ℕ → ℝ) (t : ℕ → T)
    (a : BallApproximation r) :
    ∃ m k, finiteShrinkingOpen h hh r t a ≤ shrinkingOpen h hh r t m k := by
  classical
  have hsmall : ∀ n : a.support, ∃ k : ℕ, 1 / (k + 1 : ℝ) < r n - a.innerRadius n :=
    fun n => exists_nat_one_div_lt (sub_pos.mpr (a.radius_lt n n.2))
  choose k hk using hsmall
  let K : ℕ := Finset.univ.sup k
  let m : ℕ := a.support.sup id + 1
  refine ⟨m, K, ?_⟩
  intro x hx
  obtain ⟨n, hn, hxn⟩ := mem_iUnion₂.mp hx
  have hnm : n < m := Nat.lt_succ_of_le (Finset.le_sup (f := id) hn)
  have hkK : k ⟨n, hn⟩ ≤ K :=
    Finset.le_sup (f := k) (Finset.mem_univ (⟨n, hn⟩ : a.support))
  have hden : (k ⟨n, hn⟩ + 1 : ℝ) ≤ (K + 1 : ℝ) := by exact_mod_cast Nat.succ_le_succ hkK
  have hinv := one_div_le_one_div_of_le (by positivity : 0 < (k ⟨n, hn⟩ + 1 : ℝ)) hden
  refine mem_iUnion.mpr ⟨⟨n, hnm⟩, ?_⟩
  change dist (h x) (t n) < r n - 1 / (K + 1 : ℝ)
  change dist (h x) (t n) < a.innerRadius n at hxn
  linarith [hk ⟨n, hn⟩]

/-- Conversely, for positive radii the common-shrink helpers are dominated
by literal source approximations. Nonpositive helper balls cause no problem. -/
theorem common_shrink_le_finiteShrinkingOpen
    {A : Type u} [TopologicalSpace A] {T : Type v} [PseudoMetricSpace T]
    (h : A → T) (hh : Continuous h) (r : ℕ → ℝ) (hr : ∀ n, 0 < r n)
    (t : ℕ → T) (m k : ℕ) :
    ∃ a : BallApproximation r, shrinkingOpen h hh r t m k ≤ finiteShrinkingOpen h hh r t a := by
  let a : BallApproximation r :=
    { support := Finset.range m
      innerRadius := fun n => max (r n - 1 / (k + 1 : ℝ)) (r n / 2)
      radius_pos := fun n _ => lt_max_of_lt_right (half_pos (hr n))
      radius_lt := by
        intro n _
        apply max_lt
        · linarith [show 0 < 1 / (k + 1 : ℝ) by positivity]
        · linarith [hr n] }
  refine ⟨a, ?_⟩
  intro x hx
  obtain ⟨n, hxn⟩ := mem_iUnion.mp hx
  refine mem_iUnion₂.mpr ⟨n.1, Finset.mem_range.mpr n.2, ?_⟩
  exact Metric.ball_subset_ball (le_max_left _ _) hxn

/-- Public source route through the literal finite support/individual-radii
family. The earlier common-shrink result is only an internal helper. -/
theorem finiteShrinking_randomOpen_continuous
    {A : Type u} [TopologicalSpace A] {T : Type v} [PseudoMetricSpace T]
    (h : A → T) (hh : Continuous h) (r : ℕ → ℝ) :
    Continuous (fun t : ℕ → T => WithScott.toScott (randomOpenPullback h hh r t)) := by
  apply continuous_def.mpr
  intro H hH
  apply isOpen_iff_mem_nhds.mpr
  intro t ht
  have hup : IsUpperSet H := IsScott.isUpperSet_of_isOpen (D := univ) hH
  have hacc : DirSupInaccOn univ H :=
    (IsScott.isOpen_iff_isUpperSet_and_dirSupInaccOn (D := univ)).mp hH |>.2
  let approx : BallApproximation r → WithScott (Opens A) :=
    fun a => WithScott.toScott (finiteShrinkingOpen h hh r t a)
  have hd : Directed (· ≤ ·) approx := finiteShrinkingOpen_directed h hh r t
  have hlub : IsLUB (range approx) (WithScott.toScott (randomOpenPullback h hh r t)) :=
    finiteShrinkingOpen_isLUB h hh r t
  obtain ⟨V, ⟨a, rfl⟩, hVH⟩ :=
    hacc (mem_univ _) (range_nonempty approx) hd.directedOn_range hlub ht
  obtain ⟨N, hNo, htN, hNsub⟩ := finiteShrinkingOpen_local_subset h hh r t a
  exact mem_of_superset (hNo.mem_nhds htN) (fun u hu => hup (hNsub u hu) hVH)


/-- Printed radius 2^{-i-7}, with i=n+1. -/
noncomputable def radius (n : ℕ) : ℝ := (1 / 2 : ℝ) ^ (n + 8)

theorem radius_pos (n : ℕ) : 0 < radius n := by unfold radius; positivity

theorem radius_source (n : ℕ) :
    radius n = (2 : ℝ) ^ (-((n : ℤ) + 1) - 7) := by
  have he : -((n : ℤ) + 1) - 7 = -((n + 8 : ℕ) : ℤ) := by omega
  rw [he, zpow_neg, zpow_natCast]
  simp [radius, one_div, inv_pow]

noncomputable def randomOpen (t : Omega) : Opens Circle :=
  randomOpenPullback id continuous_id radius t

theorem randomOpen_continuous :
    Continuous (fun t : Omega => WithScott.toScott (randomOpen t)) :=
  finiteShrinking_randomOpen_continuous id continuous_id radius

/-- Source random-continuity consequence for any actual Scott-continuous
open-lattice map; the filter branch instantiates this with U ↦ H_U. -/
theorem randomOpen_scott_comp_continuous {Q : Type u} [Preorder Q]
    (f : Opens Circle → Q) (hf : ScottContinuous f) :
    Continuous (fun t : Omega => WithScott.toScott (f (randomOpen t))) :=
  ((scott_continuous_iff f).mp hf).comp randomOpen_continuous

theorem randomOpen_scott_sup_continuous {Q : Type u} [CompleteLattice Q]
    (f : Opens Circle → Q) (hf : ScottContinuous f) (C : Q) :
    Continuous (fun t : Omega => WithScott.toScott (f (randomOpen t) ⊔ C)) := by
  have hs : ScottContinuous (fun H : Q => H ⊔ C) :=
    ((ScottContinuous.id).prodMk (ScottContinuous.const C)).comp ScottContinuous.sup₂
  exact randomOpen_scott_comp_continuous (fun U => f U ⊔ C) (hf.comp hs)

theorem randomOpen_contains_coordinate (t : Omega) (n : ℕ) : t n ∈ randomOpen t :=
  randomBallUnion_contains_coordinate radius radius_pos t n

theorem randomOpen_joint_isOpen :
    IsOpen {z : Circle × Omega | z.1 ∈ randomOpen z.2} := by
  have heq : {z : Circle × Omega | z.1 ∈ randomOpen z.2} =
      ⋃ n : ℕ, {z : Circle × Omega | dist z.1 (z.2 n) < radius n} := by
    ext z
    simp [randomOpen, randomOpenPullback, randomBallUnion, Metric.mem_ball]
  rw [heq]
  apply isOpen_iUnion
  intro n
  exact isOpen_lt (continuous_fst.dist ((continuous_apply n).comp continuous_snd))
    continuous_const

theorem randomOpen_incidence_isOpen (y : Circle) :
    IsOpen {t : Omega | y ∈ randomOpen t} :=
  randomBallUnion_incidence_isOpen radius y

/-- Source compact-event assertion, obtained from joint openness and a finite
ordinary compact subcover (the compact tube-neighborhood lemma). -/
theorem randomOpen_compact_containment_isOpen {K : Set Circle} (hK : IsCompact K) :
    IsOpen {t : Omega | K ⊆ randomOpen t} := by
  apply isOpen_iff_mem_nhds.mpr
  intro t ht
  apply hK.eventually_forall_of_forall_eventually
  intro y hy
  have hj : IsOpen {z : Omega × Circle | z.2 ∈ randomOpen z.1} :=
    randomOpen_joint_isOpen.preimage continuous_swap
  exact hj.mem_nhds (ht hy)

end ZFCFubini

