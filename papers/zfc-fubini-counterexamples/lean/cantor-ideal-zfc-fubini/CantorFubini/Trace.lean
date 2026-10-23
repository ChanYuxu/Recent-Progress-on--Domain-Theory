import CantorFubini.ScottBasics
import CantorFubini.NullTopology
import Mathlib.Topology.Sequences

/-! Source generated ideals, maximal approximation, convergent-sequence trace
argument, and first probability valuation. Literal ideal construction, new code. -/
set_option autoImplicit false
open Set Topology TopologicalSpace MeasureTheory Filter
universe u v
namespace CantorFubini
variable {X : Type u} [TopologicalSpace X] [T2Space X] [MeasurableSpace X]
open IdealPoint

def generatedIdeal (m : Measure X) (K M : Set X) : NullIdeal m where
  sets := {N | m N = 0 ∧ Disjoint (closure (N \ M)) K}
  empty_mem := by simp
  null hN := hN.1
  lower hN hL := ⟨measure_mono_null hL hN.1,
    hN.2.mono_left (closure_mono (diff_subset_diff_left hL))⟩
  union_mem hN hL := ⟨measure_union_null hN.1 hL.1, by
    rw [union_diff_distrib, closure_union]
    exact disjoint_union_left.mpr ⟨hN.2, hL.2⟩⟩

theorem generatedIdeal_lower (m : Measure X) (K M : Set X) :
    (lowerIdeal m K).sets ⊆ (generatedIdeal m K M).sets :=
  fun _ hN => ⟨hN.1, hN.2.mono_left (closure_mono diff_subset)⟩

theorem generatedIdeal_upper (m : Measure X) (K M : Set X) (hMK : Disjoint M K) :
    (generatedIdeal m K M).sets ⊆ (upperIdeal m K).sets := by
  intro N hN
  refine ⟨hN.1, disjoint_left.mpr (fun y hyN hyK => ?_)⟩
  by_cases hyM : y ∈ M
  · exact disjoint_left.mp hMK hyM hyK
  · exact disjoint_left.mp hN.2 (subset_closure ⟨hyN, hyM⟩) hyK

theorem mem_generatedIdeal_iff (m : Measure X) (K M N : Set X) :
    N ∈ (generatedIdeal m K M).sets ↔
    m N = 0 ∧ ∃ N₀ ∈ (lowerIdeal m K).sets, N ⊆ M ∪ N₀ := by
  constructor
  · intro hN
    exact ⟨hN.1, N \ M, ⟨measure_mono_null diff_subset hN.1, hN.2⟩, by
      intro y hy; by_cases hyM : y ∈ M
      · exact Or.inl hyM
      · exact Or.inr ⟨hy, hyM⟩⟩
  · rintro ⟨hN, N₀, hN₀, hsub⟩
    refine ⟨hN, hN₀.2.mono_left (closure_mono ?_)⟩
    intro y hy
    exact (hsub hy.1).elim (fun h => False.elim (hy.2 h)) id

def r (m : Measure X) (x : X) (M : Set X) (hxM : x ∉ M) : IdealPoint m where
  kernel := {x}
  label := x
  label_mem := mem_singleton x
  finite_outside V _ _ := (finite_singleton x).subset diff_subset
  compact := isCompact_singleton
  ideal := generatedIdeal m {x} M
  lower_bound := generatedIdeal_lower m {x} M
  upper_bound := generatedIdeal_upper m {x} M (disjoint_singleton_right.mpr hxM)

abbrev AvoidNull (m : Measure X) (x : X) := {M : Set X // m M = 0 ∧ x ∉ M}

instance avoidNull_nonempty (m : Measure X) (x : X) : Nonempty (AvoidNull m x) :=
  ⟨⟨∅, measure_empty, notMem_empty x⟩⟩

theorem r_directed (m : Measure X) (x : X) :
    Directed (· ≤ ·) (fun M : AvoidNull m x => r m x M.val M.property.2) := by
  intro M N
  refine ⟨⟨M.val ∪ N.val, measure_union_null M.property.1 N.property.1,
    fun h => h.elim M.property.2 N.property.2⟩, ?_, ?_⟩
  all_goals
    refine Or.inl ⟨rfl, Subset.rfl, fun L hL => ⟨hL.1, hL.2.mono_left
      (closure_mono (diff_subset_diff_right ?_))⟩⟩
  · exact subset_union_left
  · exact subset_union_right

theorem r_isLUB (m : Measure X) (x : X) :
    IsLUB (range (fun M : AvoidNull m x => r m x M.val M.property.2)) (IdealPoint.e m x) := by
  constructor
  · rintro p ⟨M, rfl⟩; exact le_e_label _
  · intro p hp
    let M₀ : AvoidNull m x := ⟨∅, measure_empty, notMem_empty x⟩
    have hp₀ := hp (mem_range_self M₀)
    have hx : p.label = x := kernel_antitone hp₀ p.label_mem
    have hK : p.kernel ⊆ {x} := kernel_antitone hp₀
    refine Or.inl ⟨hx.symm, hK, ?_⟩
    intro N hN
    let MN : AvoidNull m x := ⟨N, hN.1, disjoint_singleton_right.mp hN.2⟩
    apply ideal_mono (hp (mem_range_self MN))
    exact ⟨hN.1, by simp [MN]⟩

def sequenceTail (x : X) (z : ℕ → X) (n : ℕ) : Set X := insert x (z '' Ici n)

theorem sequenceTail_antitone (x : X) (z : ℕ → X) : Antitone (sequenceTail x z) :=
  fun _ _ h => insert_subset_insert (image_mono (Ici_subset_Ici.mpr h))

theorem sequenceTail_eventually_subset {x : X} {z : ℕ → X}
    (hz : Tendsto z atTop (𝓝 x)) {V : Set X} (hV : IsOpen V) (hxV : x ∈ V) :
    ∃ n, sequenceTail x z n ⊆ V := by
  obtain ⟨n, hn⟩ := eventually_atTop.mp (hz (hV.mem_nhds hxV))
  refine ⟨n, ?_⟩
  rintro y (rfl | ⟨j, hj, rfl⟩)
  · exact hxV
  · exact hn j hj

theorem sequenceTail_finite_outside {x : X} {z : ℕ → X}
    (hz : Tendsto z atTop (𝓝 x)) (n : ℕ) (V : Set X) (hV : IsOpen V) (hxV : x ∈ V) :
    (sequenceTail x z n \ V).Finite := by
  obtain ⟨k, hk⟩ := sequenceTail_eventually_subset hz hV hxV
  apply ((Finset.range k).finite_toSet.image z).subset
  rintro y ⟨hy, hyV⟩
  rcases hy with rfl | ⟨j, hj, rfl⟩
  · exact False.elim (hyV hxV)
  · refine ⟨j, Finset.mem_range.mpr ?_, rfl⟩
    by_contra h
    exact hyV (hk (mem_insert_of_mem _ (mem_image_of_mem z (Nat.le_of_not_gt h))))

def tailPoint (m : Measure X) {x : X} {z : ℕ → X} (hz : Tendsto z atTop (𝓝 x))
    (M : Set X) (hxM : x ∉ M) (hzM : ∀ n, z n ∉ M) (n : ℕ) : IdealPoint m where
  kernel := sequenceTail x z n
  label := x
  label_mem := mem_insert x _
  finite_outside := sequenceTail_finite_outside hz n
  compact := kernel_compact_of_finite_outside (mem_insert x _) (sequenceTail_finite_outside hz n)
  ideal := generatedIdeal m (sequenceTail x z n) M
  lower_bound := generatedIdeal_lower m _ M
  upper_bound := generatedIdeal_upper m _ M (disjoint_left.mpr (by
    rintro y hyM (rfl | ⟨j, hj, rfl⟩)
    · exact hxM hyM
    · exact hzM j hyM))

theorem tailPoint_monotone (m : Measure X) {x : X} {z : ℕ → X}
    (hz : Tendsto z atTop (𝓝 x)) (M : Set X) (hxM : x ∉ M) (hzM : ∀ n, z n ∉ M) :
    Monotone (tailPoint m hz M hxM hzM) := by
  intro i j hij
  refine Or.inl ⟨rfl, sequenceTail_antitone x z hij, fun N hN =>
    ⟨hN.1, hN.2.mono_right (sequenceTail_antitone x z hij)⟩⟩

theorem tailPoint_isLUB (m : Measure X) {x : X} {z : ℕ → X}
    (hz : Tendsto z atTop (𝓝 x)) (M : Set X) (hxM : x ∉ M) (hzM : ∀ n, z n ∉ M) :
    IsLUB (range (tailPoint m hz M hxM hzM)) (r m x M hxM) := by
  constructor
  · rintro p ⟨n, rfl⟩
    exact Or.inl ⟨rfl, singleton_subset_iff.mpr (mem_insert _ _),
      fun N hN => ⟨hN.1, hN.2.mono_right (singleton_subset_iff.mpr (mem_insert _ _))⟩⟩
  · intro p hp
    by_cases hx : p.label = x
    · refine Or.inl ⟨hx.symm, ?_, ?_⟩
      · intro y hy
        by_contra hyx
        have hyx' : y ≠ x := hyx
        obtain ⟨n, hn⟩ := sequenceTail_eventually_subset hz isClosed_singleton.isOpen_compl
          (by simpa using hyx'.symm)
        have : y ∈ ({y} : Set X)ᶜ := hn (kernel_antitone
          (hp (mem_range_self n)) hy)
        exact this (mem_singleton y)
      · intro N hN
        have hxV : x ∈ (closure (N \ M))ᶜ :=
          disjoint_singleton_right.mp hN.2
        obtain ⟨n, hn⟩ := sequenceTail_eventually_subset hz isClosed_closure.isOpen_compl hxV
        exact ideal_mono (hp (mem_range_self n)) ⟨hN.1,
          disjoint_left.mpr (fun y hyN hyK => hn hyK hyN)⟩
    · have hp₀ := hp (mem_range_self 0)
      have he : p = IdealPoint.e m p.label := by
        rcases hp₀ with h | h
        · exact False.elim (hx h.1.symm)
        · exact h.1
      have hpx : p.label = x := by
        by_contra hne
        obtain ⟨n, hn⟩ := sequenceTail_eventually_subset hz isClosed_singleton.isOpen_compl
          (by simpa using Ne.symm hne)
        have hpN := hp (mem_range_self n)
        have hy : p.label ∈ sequenceTail x z n := by
          exact (le_e_iff _ _).mp (he ▸ hpN)
        exact hn hy (mem_singleton p.label)
      exact False.elim (hx hpx)

variable [FirstCountableTopology X] [SecondCountableTopology X]

theorem trace_local (m : Measure X) (H : ScottOpens (IdealPoint m))
    (x : X) (M : Set X) (hxM : x ∉ M) (hr : WithScott.toScott (r m x M hxM) ∈ H) :
    ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ V \ M ⊆ trace H := by
  classical
  by_contra hlocal
  have hcl : x ∈ closure (M ∪ trace H)ᶜ := by
    rw [mem_closure_iff]
    intro V hV hxV
    by_contra hempty
    apply hlocal
    refine ⟨V, hV, hxV, ?_⟩
    rintro y ⟨hyV, hyM⟩
    by_contra hyR
    apply hempty
    exact ⟨y, hyV, fun h => h.elim hyM hyR⟩
  obtain ⟨z, hzmem, hz⟩ := mem_closure_iff_seq_limit.mp hcl
  have hzM : ∀ n, z n ∉ M := fun n h => hzmem n (Or.inl h)
  have hzR : ∀ n, z n ∉ trace H := fun n h => hzmem n (Or.inr h)
  have hacc := (scott_isOpen_iff (WithScott.toScott ⁻¹' (H : Set (WithScott (IdealPoint m))))).mp
    H.isOpen |>.2
  obtain ⟨p, hp, hpH⟩ := hacc (range_nonempty (tailPoint m hz M hxM hzM))
    (tailPoint_monotone m hz M hxM hzM).directed_le.directedOn_range
    (tailPoint_isLUB m hz M hxM hzM) hr
  obtain ⟨n, rfl⟩ := hp
  have hzn : z n ∈ (tailPoint m hz M hxM hzM n).kernel :=
    mem_insert_of_mem _ (mem_image_of_mem z (le_refl n))
  exact hzR n (kernel_subset_trace hpH hzn)

theorem trace_isOpen (m : Measure X) (H : ScottOpens (IdealPoint m)) :
    (nullTopology m).IsOpen (trace H) := by
  classical
  have hlocal : ∀ x : trace H, ∃ V : Set X, IsOpen V ∧ x.val ∈ V ∧
      ∃ M : Set X, m M = 0 ∧ x.val ∉ M ∧ V \ M ⊆ trace H := by
    intro x
    have hacc := (scott_isOpen_iff (WithScott.toScott ⁻¹' (H : Set (WithScott (IdealPoint m))))).mp
      H.isOpen |>.2
    obtain ⟨p, hp, hpH⟩ := hacc (range_nonempty (fun M : AvoidNull m x.val =>
      r m x.val M.val M.property.2)) (r_directed m x.val).directedOn_range (r_isLUB m x.val) x.property
    obtain ⟨M, rfl⟩ := hp
    obtain ⟨V, hV, hxV, hsub⟩ := trace_local m H x.val M.val M.property.2 hpH
    exact ⟨V, hV, hxV, M.val, M.property.1, M.property.2, hsub⟩
  choose V hV hxV M hM hxM hsub using hlocal
  have he : trace H = ⋃ x : trace H, V x \ M x := by
    apply Subset.antisymm
    · intro x hx; exact mem_iUnion.mpr ⟨⟨x, hx⟩, hxV ⟨x, hx⟩, hxM ⟨x, hx⟩⟩
    · exact iUnion_subset hsub
  rw [he]
  exact nullRemovedOpen_iUnion m _ (fun x => ⟨V x, hV x, M x, hM x, rfl⟩)

theorem e_continuous (m : Measure X) :
    @Continuous X (WithScott (IdealPoint m)) (nullTopology m) _
      (fun x => WithScott.toScott (IdealPoint.e m x)) :=
  continuous_def.mpr (fun U hU => trace_isOpen m ⟨U, hU⟩)

def nu [OpensMeasurableSpace X] (m : Measure X) [IsFiniteMeasure m] [m.InnerRegular] :
    Valuation (WithScott (IdealPoint m)) :=
  @Valuation.push X (nullTopology m) (WithScott (IdealPoint m)) _ (nullValuation m)
    (fun x => WithScott.toScott (IdealPoint.e m x)) (e_continuous m)

@[simp] theorem nu_apply [OpensMeasurableSpace X] (m : Measure X)
    [IsFiniteMeasure m] [m.InnerRegular] (H : ScottOpens (IdealPoint m)) :
    nu m H = m (trace H) := rfl

theorem nu_probability [OpensMeasurableSpace X] (m : Measure X)
    [IsProbabilityMeasure m] [m.InnerRegular] : (nu m).Probability := measure_univ

end CantorFubini
