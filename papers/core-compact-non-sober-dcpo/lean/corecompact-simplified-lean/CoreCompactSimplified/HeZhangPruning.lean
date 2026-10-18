import CoreCompactSimplified.HeZhangSupport
import Mathlib.SetTheory.Ordinal.FixedPointApproximants
import Mathlib.SetTheory.Cardinal.Regular
import Mathlib.Order.PartialSups
import Mathlib.Topology.Irreducible
import Mathlib.SetTheory.Ordinal.Rank

/-! The literal transfinite pruning construction in He–Zhang Theorem 4.13,
Claims 2, 3 and 7.  Density and rank growth are proved, not certificate fields. -/

set_option autoImplicit false

universe u

namespace CoreCompactSimplified.HeZhangPruning

open Set TopologicalSpace Ordinal
open scoped Cardinal
open CoreCompactNonSober

variable {P : Type u} [PartialOrder P]

local instance pruningScottTopology : TopologicalSpace P := scottTopology P

/-- The ordinary order-theoretic downward closure. -/
def down (A : Set P) : Set P := {x | ∃ y ∈ A, x ≤ y}

theorem subset_down (A : Set P) : A ⊆ down A := fun x hx ↦ ⟨x, hx, le_rfl⟩

theorem down_mono {A B : Set P} (h : A ⊆ B) : down A ⊆ down B := by
  rintro x ⟨y, hy, hxy⟩
  exact ⟨y, h hy, hxy⟩

theorem down_lower (A : Set P) : IsLowerSet (down A) := by
  rintro x y hxy ⟨z, hz, hyz⟩
  exact ⟨z, hz, hxy.trans hyz⟩

/-- The specified minimal-point seed, not an arbitrary dense surrogate. -/
def seed (K : ℕ → Set P) : Set P := ⋃ n, {x | Minimal (· ∈ K n) x}

/-- The printed successor operation. -/
def step (U : ℕ → ScottOpens P) (A : Set P) : Set P :=
  A ∩ ⋂ n, down (A ∩ (U n : Set P))

private def stepHom (U : ℕ → ScottOpens P) : Set P →o Set P where
  toFun := step U
  monotone' := by
    intro A B hAB x hx
    refine ⟨hAB hx.1, Set.mem_iInter.mpr ?_⟩
    intro n
    apply down_mono (Set.inter_subset_inter_left _ hAB)
    exact Set.mem_iInter.mp hx.2 n

/-- This fixed-point approximant is related to the source's zero, successor and
limit clauses by the exact equations below. -/
noncomputable def stage (K : ℕ → Set P) (U : ℕ → ScottOpens P)
    (α : Ordinal.{u}) : Set P := OrdinalApprox.gfpApprox (stepHom U) (seed K) α

@[simp] theorem stage_zero (K : ℕ → Set P) (U : ℕ → ScottOpens P) :
    stage K U 0 = seed K := OrdinalApprox.gfpApprox_zero _

theorem stage_add_one (K : ℕ → Set P) (U : ℕ → ScottOpens P) (α : Ordinal.{u}) :
    stage K U (α + 1) = step U (stage K U α) :=
  OrdinalApprox.gfpApprox_add_one _ (fun _ h ↦ h.1) α

theorem stage_limit (K : ℕ → Set P) (U : ℕ → ScottOpens P) {l : Ordinal.{u}}
    (hl : Order.IsSuccLimit l) :
    stage K U l = ⋂ β : Set.Iio l, stage K U β.val :=
  OrdinalApprox.gfpApprox_of_isSuccLimit _ hl

theorem stage_antitone (K : ℕ → Set P) (U : ℕ → ScottOpens P) :
    Antitone (stage K U) := OrdinalApprox.gfpApprox_anti_right _

theorem stage_subset_seed (K : ℕ → Set P) (U : ℕ → ScottOpens P) (α : Ordinal.{u}) :
    stage K U α ⊆ seed K := OrdinalApprox.gfpApprox_le _

/-- The explicit cofinal-sequence equality printed in the limit step. -/
theorem stage_limit_eq_iInter_sequence (K : ℕ → Set P) (U : ℕ → ScottOpens P)
    {l : Ordinal.{u}} (hl : Order.IsSuccLimit l) (β : ℕ → Ordinal.{u})
    (hβlt : ∀ n, β n < l) (hβcofinal : ∀ α < l, ∃ n, α ≤ β n) :
    stage K U l = ⋂ n, stage K U (β n) := by
  apply Set.Subset.antisymm
  · intro x hx
    exact Set.mem_iInter.mpr (fun n ↦ stage_antitone K U (hβlt n).le hx)
  · intro x hx
    rw [stage_limit K U hl]
    apply Set.mem_iInter.mpr
    intro δ
    obtain ⟨n, hn⟩ := hβcofinal δ.val δ.property
    exact stage_antitone K U hn (Set.mem_iInter.mp hx n)

/-- He–Zhang Claim 2: the stages are lower relative to the original seed. -/
theorem stage_relative_lower (K : ℕ → Set P) (U : ℕ → ScottOpens P) (α : Ordinal.{u}) :
    ∀ ⦃s⦄, s ∈ stage K U α → ∀ ⦃r⦄, r ∈ seed K → r ≤ s → r ∈ stage K U α := by
  induction α using Ordinal.limitRecOn with
  | zero =>
    rw [stage_zero]
    intro s hs r hr hrs
    exact hr
  | succ α ih =>
    simp only [Order.succ_eq_add_one, stage_add_one]
    intro s hs r hr hrs
    refine ⟨ih hs.1 hr hrs, Set.mem_iInter.mpr ?_⟩
    intro n
    exact down_lower _ hrs (Set.mem_iInter.mp hs.2 n)
  | limit l hl ih =>
    rw [stage_limit K U hl]
    intro s hs r hr hrs
    exact Set.mem_iInter.mpr (fun β ↦ ih β.val β.property (Set.mem_iInter.mp hs β) hr hrs)

/-- A countable ordinal admits an increasing cofinal sequence below it whenever
it is nonzero.  The limit case in Claim 3 will use this lemma. -/
theorem countable_cofinal_sequence {l : Ordinal.{u}} (hl : l < ω₁) (hpos : 0 < l) :
    ∃ β : ℕ → Ordinal.{u}, Monotone β ∧ (∀ n, β n < l) ∧
      ∀ α < l, ∃ n, α ≤ β n := by
  classical
  have hcard : l.card ≤ Cardinal.aleph0 := by
    apply Cardinal.lt_aleph_one_iff.mp
    simpa only [← Cardinal.ord_aleph, Cardinal.lt_ord] using hl
  haveI : Countable l.ToType := Cardinal.mk_le_aleph0_iff.mp (by
    simpa only [Cardinal.mk_toType] using hcard)
  haveI : Countable (Set.Iio l) := Ordinal.ToType.mk.injective.countable
  haveI : Nonempty (Set.Iio l) := ⟨⟨0, hpos⟩⟩
  obtain ⟨e, he⟩ := exists_surjective_nat (Set.Iio l)
  refine ⟨fun n ↦ (partialSups e n).val, ?_, ?_, ?_⟩
  · intro m n hmn
    exact (partialSups e).monotone hmn
  · intro n
    exact (partialSups e n).property
  · intro α hlt
    obtain ⟨n, hn⟩ := he ⟨α, hlt⟩
    refine ⟨n, ?_⟩
    simpa only [hn] using le_partialSups e n

/-- The sequence also has precisely the printed supremum at a limit ordinal. -/
theorem countable_limit_sequence {l : Ordinal.{u}} (hl : l < ω₁)
    (hlimit : Order.IsSuccLimit l) :
    ∃ β : ℕ → Ordinal.{u}, Monotone β ∧ (∀ n, β n < l) ∧
      (⨆ n, β n) = l ∧ ∀ α < l, ∃ n, α ≤ β n := by
  obtain ⟨β, hmono, hlt, hcofinal⟩ := countable_cofinal_sequence hl hlimit.bot_lt
  refine ⟨β, hmono, hlt, le_antisymm (Ordinal.iSup_le fun n ↦ (hlt n).le) ?_, hcofinal⟩
  apply le_of_forall_lt
  intro α hα
  obtain ⟨n, hn⟩ := hcofinal (Order.succ α) (hlimit.succ_lt hα)
  exact (Order.lt_succ α).trans_le (hn.trans (Ordinal.le_iSup β n))

private theorem dense_inter_open (hirr : IsIrreducible (Set.univ : Set P))
    {A : Set P} (hA : Dense A) (W : ScottOpens P) (hW : (W : Set P).Nonempty) :
    Dense (A ∩ (W : Set P)) := by
  letI : PreirreducibleSpace P := ⟨hirr.2⟩
  apply dense_iff_inter_open.mpr
  intro O hO hOne
  have hOW : (O ∩ (W : Set P)).Nonempty :=
    nonempty_preirreducible_inter hO W.isOpen hOne hW
  obtain ⟨x, hx⟩ := hA.inter_open_nonempty (O ∩ W) (hO.inter W.isOpen) hOW
  exact ⟨x, hx.1.1, hx.2, hx.1.2⟩

private theorem dense_iInter_down (hP : IsDcpo P) (hcore : ScottCoreCompact P)
    (A : ℕ → Set P) (hanti : Antitone A) (hdense : ∀ n, Dense (A n)) :
    Dense (⋂ n, down (A n)) := by
  apply dense_iff_closure_eq.mpr
  rw [HeZhangSupport.closure_iInter_antitone_lower hP hcore
    (fun n ↦ down (A n)) (fun m n hmn ↦ down_mono (hanti hmn)) (fun n ↦ down_lower (A n))]
  have hcl (n : ℕ) : closure (down (A n)) = Set.univ :=
    ((hdense n).mono (subset_down (A n))).closure_eq
  simp only [hcl, Set.iInter_univ]

/-- He–Zhang Claim 3, retaining the original minima and countable-cofinal limit
argument.  The hypotheses are precisely the elementary properties of the
compact neighborhoods chosen before the pruning construction. -/
theorem stage_dense (hP : IsDcpo P) (hcore : ScottCoreCompact P)
    (hirr : IsIrreducible (Set.univ : Set P))
    (K : ℕ → Set P) (U V : ℕ → ScottOpens P)
    (hUanti : Antitone U) (hUne : ∀ n, (U n : Set P).Nonempty)
    (hcofinal : ∀ O : ScottOpens P, (O : Set P).Nonempty → ∃ n, U n ≤ O)
    (hVne : ∀ n, (V n : Set P).Nonempty)
    (hVK : ∀ n, (V n : Set P) ⊆ K n) (hKU : ∀ n, K n ⊆ (U n : Set P))
    (hmin : ∀ n x, x ∈ K n → ∃ m, m ≤ x ∧ Minimal (· ∈ K n) m)
    (α : Ordinal.{u}) (hα : α < ω₁) : Dense (stage K U α) := by
  induction α using Ordinal.limitRecOn with
  | zero =>
    rw [stage_zero]
    apply dense_iff_inter_open.mpr
    intro O hO hOne
    obtain ⟨j, hj⟩ := hcofinal ⟨O, hO⟩ hOne
    obtain ⟨z, hz⟩ := hVne j
    obtain ⟨m, hmz, hm⟩ := hmin j z (hVK j hz)
    exact ⟨m, hj (hKU j hm.1), Set.mem_iUnion.mpr ⟨j, hm⟩⟩
  | succ α ih =>
    rw [Order.succ_eq_add_one, stage_add_one]
    have hα' : α < ω₁ := (Order.lt_succ α).trans hα
    have hD : Dense (⋂ n, down (stage K U α ∩ (U n : Set P))) :=
      dense_iInter_down hP hcore (fun n ↦ stage K U α ∩ (U n : Set P))
        (fun _ _ hmn ↦ Set.inter_subset_inter_right _ (hUanti hmn))
        (fun n ↦ dense_inter_open hirr (ih hα') (U n) (hUne n))
    apply dense_iff_inter_open.mpr
    intro O hO hOne
    obtain ⟨j, hj⟩ := hcofinal ⟨O, hO⟩ hOne
    obtain ⟨z, hz⟩ := hD.inter_open_nonempty (V j) (V j).isOpen (hVne j)
    obtain ⟨m, hmz, hm⟩ := hmin j z (hVK j hz.1)
    have hmseed : m ∈ seed K := Set.mem_iUnion.mpr ⟨j, hm⟩
    have hmA : m ∈ stage K U α := by
      obtain ⟨t, ht, hzt⟩ := Set.mem_iInter.mp hz.2 0
      exact stage_relative_lower K U α ht.1 hmseed (hmz.trans hzt)
    refine ⟨m, hj (hKU j hm.1), hmA, Set.mem_iInter.mpr ?_⟩
    intro n
    exact down_lower _ hmz (Set.mem_iInter.mp hz.2 n)
  | limit l hl ih =>
    obtain ⟨β, hβmono, hβlt, hβsup, hβcofinal⟩ := countable_limit_sequence hα hl
    have hD : Dense (⋂ n, down (stage K U (β n))) :=
      dense_iInter_down hP hcore (fun n ↦ stage K U (β n))
        (fun _ _ hmn ↦ stage_antitone K U (hβmono hmn))
        (fun n ↦ ih (β n) (hβlt n) ((hβlt n).trans hα))
    apply dense_iff_inter_open.mpr
    intro O hO hOne
    obtain ⟨j, hj⟩ := hcofinal ⟨O, hO⟩ hOne
    obtain ⟨z, hz⟩ := hD.inter_open_nonempty (V j) (V j).isOpen (hVne j)
    obtain ⟨m, hmz, hm⟩ := hmin j z (hVK j hz.1)
    have hmseed : m ∈ seed K := Set.mem_iUnion.mpr ⟨j, hm⟩
    have hmβ (n : ℕ) : m ∈ stage K U (β n) := by
      obtain ⟨r, hr, hzr⟩ := Set.mem_iInter.mp hz.2 n
      exact stage_relative_lower K U (β n) hr hmseed (hmz.trans hzr)
    refine ⟨m, hj (hKU j hm.1), ?_⟩
    rw [stage_limit_eq_iInter_sequence K U hl β hβlt hβcofinal]
    exact Set.mem_iInter.mpr hmβ

theorem stage_closure_eq_univ (hP : IsDcpo P) (hcore : ScottCoreCompact P)
    (hirr : IsIrreducible (Set.univ : Set P))
    (K : ℕ → Set P) (U V : ℕ → ScottOpens P)
    (hUanti : Antitone U) (hUne : ∀ n, (U n : Set P).Nonempty)
    (hcofinal : ∀ O : ScottOpens P, (O : Set P).Nonempty → ∃ n, U n ≤ O)
    (hVne : ∀ n, (V n : Set P).Nonempty)
    (hVK : ∀ n, (V n : Set P) ⊆ K n) (hKU : ∀ n, K n ⊆ (U n : Set P))
    (hmin : ∀ n x, x ∈ K n → ∃ m, m ≤ x ∧ Minimal (· ∈ K n) m)
    (α : Ordinal.{u}) (hα : α < ω₁) : closure (stage K U α) = Set.univ :=
  (stage_dense hP hcore hirr K U V hUanti hUne hcofinal hVne hVK hKU hmin α hα).closure_eq

/-- He–Zhang Claim 7 for a tagged presentation of the actual seed points.
The hypotheses supply only tag existence and the printed one-level relation;
the ordinal lower bound is proved from the literal pruning recursion. -/
theorem stage_rank_lower {Z : Type u} (K : ℕ → Set P) (U : ℕ → ScottOpens P)
    (point : Z → P) (level : Z → ℕ) (R : Z → Z → Prop) (hwf : WellFounded R)
    (hcover : ∀ n s, s ∈ seed K → s ∈ U n →
      ∃ z, level z = n ∧ point z = s)
    (hrel : ∀ a b, level a = level b + 1 → point b ≤ point a → R a b)
    (α : Ordinal.{u}) (z : Z) (hz : point z ∈ stage K U α) :
    α ≤ (hwf.apply z).rank := by
  induction α using Ordinal.limitRecOn generalizing z with
  | zero => exact zero_le _
  | succ α ih =>
    rw [Order.succ_eq_add_one, stage_add_one] at hz
    obtain ⟨t, ht, hzt⟩ := Set.mem_iInter.mp hz.2 (level z + 1)
    obtain ⟨w, hwlevel, hwpoint⟩ := hcover (level z + 1) t
      (stage_subset_seed K U α ht.1) ht.2
    have hwmem : point w ∈ stage K U α := hwpoint.symm ▸ ht.1
    have hstep : R w z := hrel w z hwlevel (hwpoint.symm ▸ hzt)
    have hlt : (hwf.apply w).rank < (hwf.apply z).rank :=
      Acc.rank_lt_of_rel (hwf.apply z) hstep
    exact Order.succ_le_of_lt ((ih w hwmem).trans_lt hlt)
  | limit l hl ih =>
    apply le_of_forall_lt
    intro β hβ
    have hsucc : Order.succ β < l := hl.succ_lt hβ
    have hzsucc : point z ∈ stage K U (Order.succ β) := stage_antitone K U hsucc.le hz
    exact (Order.lt_succ β).trans_le (ih (Order.succ β) hsucc z hzsucc)

/-- The source's final contradiction: density at the countable bounding ordinal
produces a point whose tagged rank is simultaneously at least and below it. -/
theorem rank_bound_contradiction {Z : Type u}
    (hP : IsDcpo P) (hcore : ScottCoreCompact P)
    (hirr : IsIrreducible (Set.univ : Set P))
    (K : ℕ → Set P) (U V : ℕ → ScottOpens P)
    (hUanti : Antitone U) (hUne : ∀ n, (U n : Set P).Nonempty)
    (hcofinal : ∀ O : ScottOpens P, (O : Set P).Nonempty → ∃ n, U n ≤ O)
    (hVne : ∀ n, (V n : Set P).Nonempty)
    (hVK : ∀ n, (V n : Set P) ⊆ K n) (hKU : ∀ n, K n ⊆ (U n : Set P))
    (hmin : ∀ n x, x ∈ K n → ∃ m, m ≤ x ∧ Minimal (· ∈ K n) m)
    (point : Z → P) (level : Z → ℕ) (R : Z → Z → Prop) (hwf : WellFounded R)
    (hcover : ∀ n s, s ∈ seed K → s ∈ U n →
      ∃ z, level z = n ∧ point z = s)
    (hrel : ∀ a b, level a = level b + 1 → point b ≤ point a → R a b)
    (γ : Ordinal.{u}) (hγ : γ < ω₁) (hbound : ∀ z, (hwf.apply z).rank < γ) : False := by
  have hdense := stage_dense hP hcore hirr K U V hUanti hUne hcofinal hVne hVK hKU hmin γ hγ
  obtain ⟨s, hs⟩ := hdense.inter_open_nonempty (U 0) (U 0).isOpen (hUne 0)
  obtain ⟨z, hzlevel, hzpoint⟩ := hcover 0 s (stage_subset_seed K U γ hs.2) hs.1
  have hz : point z ∈ stage K U γ := hzpoint.symm ▸ hs.2
  have hlower := stage_rank_lower K U point level R hwf hcover hrel γ z hz
  exact (not_lt_of_ge hlower) (hbound z)

end CoreCompactSimplified.HeZhangPruning
