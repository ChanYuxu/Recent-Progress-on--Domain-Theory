import CHFubini.DenseIncidence
import CHFubini.Foundations

/-!
Candidate proof of manuscript `prop:R-continuous`. The approximants are the
source's finitely many shrinking balls, indexed by `(m,k) ∈ ℕ × ℕ`, with
`1/(k+1)` replacing the printed positive-integer convention `1/k`.
-/

open Set Filter TopologicalSpace Topology
open scoped Topology

namespace CHFubini

universe u v

/-- Actual pullback of the random union of metric balls. -/
def randomOpen {A : Type u} [TopologicalSpace A]
    {T : Type v} [PseudoMetricSpace T]
    (h : A → T) (hh : Continuous h) (r : ℕ → ℝ) (s : ℕ → T) : Opens A :=
  ⟨h ⁻¹' randomBallUnion r s, (randomBallUnion_isOpen r s).preimage hh⟩

/-- The source's `V_{m,k}`: finitely many balls, all shrunk by the same
positive amount. Balls with nonpositive radius are empty in mathlib. -/
def shrinkingOpen {A : Type u} [TopologicalSpace A]
    {T : Type v} [PseudoMetricSpace T]
    (h : A → T) (hh : Continuous h) (r : ℕ → ℝ) (s₀ : ℕ → T)
    (m k : ℕ) : Opens A :=
  ⟨h ⁻¹' ⋃ n : Fin m, Metric.ball (s₀ n) (r n - 1 / (k + 1 : ℝ)),
    (isOpen_iUnion (fun _ => Metric.isOpen_ball)).preimage hh⟩

theorem shrinkingOpen_le_randomOpen
    {A : Type u} [TopologicalSpace A] {T : Type v} [PseudoMetricSpace T]
    (h : A → T) (hh : Continuous h) (r : ℕ → ℝ) (s₀ : ℕ → T)
    (m k : ℕ) : shrinkingOpen h hh r s₀ m k ≤ randomOpen h hh r s₀ := by
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

theorem randomOpen_mem_shrinkingOpen
    {A : Type u} [TopologicalSpace A] {T : Type v} [PseudoMetricSpace T]
    (h : A → T) (hh : Continuous h) (r : ℕ → ℝ) (s₀ : ℕ → T)
    {a : A} (ha : a ∈ randomOpen h hh r s₀) :
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
      (randomOpen h hh r s₀) := by
  refine ⟨?_, ?_⟩
  · rintro V ⟨p, rfl⟩
    exact shrinkingOpen_le_randomOpen h hh r s₀ p.1 p.2
  · intro V hV a ha
    obtain ⟨m, k, hmk⟩ := randomOpen_mem_shrinkingOpen h hh r s₀ ha
    exact hV (mem_range_self (m, k)) hmk

/-- A fixed finite shrinking approximation remains included in `R_s` on an
ordinary open neighborhood of its center sample. -/
theorem shrinkingOpen_local_subset
    {A : Type u} [TopologicalSpace A] {T : Type v} [PseudoMetricSpace T]
    (h : A → T) (hh : Continuous h) (r : ℕ → ℝ) (s₀ : ℕ → T)
    (m k : ℕ) :
    ∃ N : Set (ℕ → T), IsOpen N ∧ s₀ ∈ N ∧
      ∀ s ∈ N, shrinkingOpen h hh r s₀ m k ≤ randomOpen h hh r s := by
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

/-- Source `prop:R-continuous`: ordinary product topology in the domain,
full intrinsic Scott topology on the actual lattice of opens in the target. -/
theorem randomOpen_continuous
    {A : Type u} [TopologicalSpace A] {T : Type v} [PseudoMetricSpace T]
    (h : A → T) (hh : Continuous h) (r : ℕ → ℝ) :
    Continuous (fun s : ℕ → T => WithScott.toScott (randomOpen h hh r s)) := by
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
  have hlub : IsLUB (range approx) (WithScott.toScott (randomOpen h hh r s₀)) :=
    shrinkingOpen_isLUB h hh r s₀
  obtain ⟨V, ⟨p, rfl⟩, hVH⟩ :=
    hacc (mem_univ _) (range_nonempty approx) hd.directedOn_range hlub hs₀
  obtain ⟨N, hNo, hs₀N, hNsub⟩ := shrinkingOpen_local_subset h hh r s₀ p.1 p.2
  apply mem_of_superset (hNo.mem_nhds hs₀N)
  intro s hs
  exact hup (hNsub s hs) hVH

/-- The source's specified `F_beta = T_beta union R_s`, as an actual bundled
open and not an arbitrary isomorphic replacement. -/
def tailRandomOpen {A : Type u} [TopologicalSpace A]
    {T : Type v} [PseudoMetricSpace T]
    (tail : Opens A) (h : A → T) (hh : Continuous h)
    (r : ℕ → ℝ) (s : ℕ → T) : Opens A := tail ⊔ randomOpen h hh r s

theorem tailRandomOpen_continuous
    {A : Type u} [TopologicalSpace A] {T : Type v} [PseudoMetricSpace T]
    (tail : Opens A) (h : A → T) (hh : Continuous h) (r : ℕ → ℝ) :
    Continuous (fun s : ℕ → T => WithScott.toScott (tailRandomOpen tail h hh r s)) := by
  have hc : ScottContinuous (fun V : Opens A => tail ⊔ V) := by
    exact ((ScottContinuous.const tail).prodMk ScottContinuous.id).comp ScottContinuous.sup₂
  exact ((scott_continuous_iff (fun V : Opens A => tail ⊔ V)).mp hc).comp
    (randomOpen_continuous h hh r)

theorem tailRandomOpen_event_isOpen
    {A : Type u} [TopologicalSpace A] {T : Type v} [PseudoMetricSpace T]
    (tail : Opens A) (h : A → T) (hh : Continuous h) (r : ℕ → ℝ)
    {H : Set (WithScott (Opens A))} (hH : IsOpen H) :
    IsOpen ((fun s : ℕ → T => WithScott.toScott (tailRandomOpen tail h hh r s)) ⁻¹' H) :=
  hH.preimage (tailRandomOpen_continuous tail h hh r)

theorem tailRandomOpen_event_antitone
    {I : Type*} [Preorder I]
    {A : Type u} [TopologicalSpace A] {T : Type v} [PseudoMetricSpace T]
    (tail : I → Opens A) (hTail : Antitone tail)
    (h : A → T) (hh : Continuous h) (r : ℕ → ℝ)
    {H : Set (WithScott (Opens A))} (hH : IsOpen H) :
    Antitone (fun β =>
      (fun s : ℕ → T => WithScott.toScott (tailRandomOpen (tail β) h hh r s)) ⁻¹' H) := by
  intro β γ hβγ s hs
  have hup : IsUpperSet H := IsScott.isUpperSet_of_isOpen (D := univ) hH
  exact hup (sup_le_sup (hTail hβγ) le_rfl) hs

end CHFubini

#print axioms CHFubini.randomOpen_continuous
#print axioms CHFubini.tailRandomOpen_continuous

