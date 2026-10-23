import ZFCFubini.FilterDcpo
import Mathlib.Topology.Perfect
import Mathlib.Topology.DiscreteSubset
import Mathlib.Analysis.SpecificLimits.Basic

/-!
Countable same-kernel approximations and the full maximal trace theorem of
manuscript §3.2. The intended trace proof uses the actual J_n filters from
the source. New implementation; no assumption of trace openness is made.
-/

set_option autoImplicit false
open Set Topology TopologicalSpace
open scoped Topology
universe u

namespace ZFCFubini.FilterDcpo
variable {X : Type u} [MetricSpace X] {M : Model X}

noncomputable def shrinkingRadius (n : ℕ) : ℝ := 1 / (n + 1 : ℝ)

theorem shrinkingRadius_pos (n : ℕ) : 0 < shrinkingRadius n := by
  unfold shrinkingRadius; positivity

theorem shrinkingRadius_antitone : Antitone shrinkingRadius := by
  intro n m hnm
  apply one_div_le_one_div_of_le
  · positivity
  · exact_mod_cast Nat.add_le_add_right hnm 1

def compactNeighborhood (p : Point M) (n : ℕ) : Set X :=
  Metric.thickening (shrinkingRadius n) p.kernel

theorem compactNeighborhood_isOpen (p : Point M) (n : ℕ) : IsOpen (compactNeighborhood p n) :=
  Metric.isOpen_thickening

theorem kernel_subset_compactNeighborhood (p : Point M) (n : ℕ) :
    p.kernel ⊆ compactNeighborhood p n := Metric.self_subset_thickening (shrinkingRadius_pos n) _

theorem compactNeighborhood_mem (p : Point M) (n : ℕ) : compactNeighborhood p n ∈ p.filter :=
  p.ordinary_mem _ (compactNeighborhood_isOpen p n) (kernel_subset_compactNeighborhood p n)

theorem compactNeighborhood_antitone (p : Point M) : Antitone (compactNeighborhood p) :=
  fun _ _ h => Metric.thickening_mono (shrinkingRadius_antitone h) _

theorem compactNeighborhood_cofinal (p : Point M) {U : Set X}
    (hU : IsOpen U) (hKU : p.kernel ⊆ U) : ∃ n, compactNeighborhood p n ⊆ U := by
  obtain ⟨r, hr, hrU⟩ := p.kernel_compact.exists_thickening_subset_open hU hKU
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hr
  exact ⟨n, (Metric.thickening_mono hn.le p.kernel).trans hrU⟩

def finiteApproxGenerators (p : Point M) (S : Finset p.filter.sets) : Set (Set X) :=
  (Subtype.val '' (S : Set p.filter.sets)) ∪ Set.range (compactNeighborhood p)

theorem finiteApproxGenerators_mem (p : Point M) (S : Finset p.filter.sets) :
    ∀ U ∈ finiteApproxGenerators p S, U ∈ p.filter := by
  intro U hU
  rcases hU with hU | hU
  · obtain ⟨V, _, rfl⟩ := hU; exact V.property
  · obtain ⟨n, rfl⟩ := hU; exact compactNeighborhood_mem p n

noncomputable def finiteApproxFilter (p : Point M) (S : Finset p.filter.sets) :
    OpenFilter M.tau :=
  OpenFilter.generated (finiteApproxGenerators p S)
    (fun U hU => p.filter.isOpen U (finiteApproxGenerators_mem p S U hU))
    p.label (fun U hU => p.label_mem U (finiteApproxGenerators_mem p S U hU))

theorem finiteApproxFilter_le (p : Point M) (S : Finset p.filter.sets) :
    finiteApproxFilter p S ≤ p.filter := OpenFilter.generated_le (finiteApproxGenerators_mem p S)

theorem generator_mem_finiteApproxFilter (p : Point M) (S : Finset p.filter.sets)
    {U : Set X} (hU : U ∈ finiteApproxGenerators p S) : U ∈ finiteApproxFilter p S := by
  unfold finiteApproxFilter
  exact OpenFilter.generator_mem _ _ _ _ hU

theorem compactNeighborhood_mem_finiteApproxFilter (p : Point M) (S : Finset p.filter.sets) (n : ℕ) :
    compactNeighborhood p n ∈ finiteApproxFilter p S :=
  OpenFilter.generator_mem _ _ _ _ (Or.inr ⟨n, rfl⟩)

theorem finiteApproxFilter_kernel (p : Point M) (S : Finset p.filter.sets) :
    (finiteApproxFilter p S).kernel = p.kernel := by
  apply Set.Subset.antisymm
  · intro y hy
    by_contra hyK
    have hO : IsOpen ({y}ᶜ : Set X) := isClosed_singleton.isOpen_compl
    obtain ⟨n, hn⟩ := compactNeighborhood_cofinal p hO
      (fun z hz hzy => hyK ((Set.mem_singleton_iff.mp hzy) ▸ hz))
    exact hn (hy _ (compactNeighborhood_mem_finiteApproxFilter p S n)) (by simp)
  · exact OpenFilter.kernel_antitone (finiteApproxFilter_le p S)

theorem finiteApproxFilter_countablyBased (p : Point M) (S : Finset p.filter.sets) :
    (finiteApproxFilter p S).CountablyBased := by
  apply OpenFilter.countablyBased_generated
  exact (S.finite_toSet.image Subtype.val).countable.union (Set.countable_range _)

/-- The actual G_S points of the source; every approximation has exactly the
same kernel, label, compactness and derived-set condition as p. -/
noncomputable def finiteApprox (p : Point M) (S : Finset p.filter.sets) : Point M where
  filter := finiteApproxFilter p S
  label := p.label
  kernel_nonempty := finiteApproxFilter_kernel p S ▸ p.kernel_nonempty
  kernel_countable := finiteApproxFilter_kernel p S ▸ p.kernel_countable
  kernel_compact := finiteApproxFilter_kernel p S ▸ p.kernel_compact
  label_mem := finiteApproxFilter_kernel p S ▸ p.label_mem
  derived_subset := by
    intro y hy; rw [finiteApproxFilter_kernel] at hy; exact p.derived_subset y hy
  ordinary_mem := by
    intro U hU hKU
    rw [finiteApproxFilter_kernel] at hKU
    obtain ⟨n, hn⟩ := compactNeighborhood_cofinal p hU hKU
    exact (finiteApproxFilter p S).upward
      (compactNeighborhood_mem_finiteApproxFilter p S n) (M.ordinary_le _ hU) hn

@[simp] theorem finiteApprox_label (p : Point M) (S : Finset p.filter.sets) :
    (finiteApprox p S).label = p.label := rfl

@[simp] theorem finiteApprox_kernel (p : Point M) (S : Finset p.filter.sets) :
    (finiteApprox p S).kernel = p.kernel := finiteApproxFilter_kernel p S

theorem finiteApprox_le (p : Point M) (S : Finset p.filter.sets) : finiteApprox p S ≤ p :=
  Or.inl ⟨rfl, finiteApproxFilter_le p S⟩

theorem finiteApprox_mono (p : Point M) : Monotone (finiteApprox p) := by
  intro S T hST
  refine Or.inl ⟨rfl, ?_⟩
  change finiteApproxFilter p S ≤ finiteApproxFilter p T
  unfold finiteApproxFilter
  apply OpenFilter.generated_le
  intro U hU
  apply generator_mem_finiteApproxFilter p T
  rcases hU with hU | hU
  · obtain ⟨V, hV, rfl⟩ := hU; exact Or.inl ⟨V, hST hV, rfl⟩
  · exact Or.inr hU

theorem finiteApprox_directed (p : Point M) : Directed (· ≤ ·) (finiteApprox p) := by
  intro S T
  exact ⟨S ∪ T, finiteApprox_mono p Finset.subset_union_left,
    finiteApprox_mono p Finset.subset_union_right⟩

theorem finiteApprox_isLUB (p : Point M) : IsLUB (Set.range (finiteApprox p)) p := by
  constructor
  · rintro _ ⟨S, rfl⟩; exact finiteApprox_le p S
  · intro q hq
    have hF : p.filter ≤ q.filter := by
      intro U hU
      let V : p.filter.sets := ⟨U, hU⟩
      have hUG : U ∈ (finiteApprox p {V}).filter :=
        generator_mem_finiteApproxFilter p {V} (Or.inl ⟨V, by simp, rfl⟩)
      exact Point.filter_mono (hq (Set.mem_range_self {V})) hUG
    by_cases hx : p.label = q.label
    · exact Or.inl ⟨hx, hF⟩
    · have he := hq (Set.mem_range_self (∅ : Finset p.filter.sets))
      rcases he with ⟨h, _⟩ | ⟨h, _⟩
      · exact (hx h).elim
      · exact Or.inr ⟨h, hF⟩

/-- Source countable-filters lemma, including directedness, the actual
supremum, inclusion and exact preservation of kernels. -/
theorem countable_filters_approximation (p : Point M) :
    Directed (· ≤ ·) (finiteApprox p) ∧ IsLUB (Set.range (finiteApprox p)) p ∧
    ∀ S, (finiteApprox p S).filter.CountablyBased ∧
      (finiteApprox p S).filter ≤ p.filter ∧
      (finiteApprox p S).kernel = p.kernel ∧ (finiteApprox p S).label = p.label :=
  ⟨finiteApprox_directed p, finiteApprox_isLUB p, fun S =>
    ⟨finiteApproxFilter_countablyBased p S, finiteApproxFilter_le p S,
      finiteApprox_kernel p S, rfl⟩⟩

/-- Machine-checked encoding bridge: for an actual source point, a countable
cofinal base is equivalent to generation by a countable family of finer opens
under the source's finite-intersection/superset member predicate. -/
theorem countablyBased_iff_countablyGenerated (p : Point M) :
    p.filter.CountablyBased ↔ ∃ B : Set (Set X), B.Countable ∧
      (∀ U ∈ B, @IsOpen X M.tau U) ∧
      ∀ U : Set X, U ∈ p.filter ↔ OpenFilter.GeneratedMember (tau := M.tau) B U := by
  classical
  constructor
  · rintro ⟨a, ha, hacof⟩
    refine ⟨Set.range a, Set.countable_range a, ?_, ?_⟩
    · rintro U ⟨n, rfl⟩; exact p.filter.isOpen _ (ha n)
    · intro U
      constructor
      · intro hU
        obtain ⟨n, hn⟩ := hacof U hU
        refine ⟨p.filter.isOpen _ hU, {a n}, ?_, ?_⟩
        · intro V hV; rw [Finset.mem_singleton.mp hV]; exact Set.mem_range_self n
        · simpa only [Finset.set_biInter_singleton] using hn
      · rintro ⟨hU, S, hS, hSU⟩
        have hI := OpenFilter.finset_inter_mem p.filter S (fun V hV => by
          obtain ⟨n, rfl⟩ := hS V hV; exact ha n)
        exact p.filter.upward hI hU hSU
  · rintro ⟨B, hBc, hBo, hmem⟩
    have hBF : ∀ U ∈ B, U ∈ p.filter := by
      intro U hU
      apply (hmem U).mpr
      exact ⟨hBo U hU, {U}, by simpa⟩
    have hxB : ∀ U ∈ B, p.label ∈ U := fun U hU => p.label_mem U (hBF U hU)
    have hEq : p.filter = OpenFilter.generated B hBo p.label hxB :=
      OpenFilter.ext (Set.ext (fun U => hmem U))
    rw [hEq]
    exact OpenFilter.countablyBased_generated B hBo p.label hxB hBc

/-- Source L(V): the union of every Scott-open with trace contained in V.
No Scott continuity or preservation of joins is claimed for L. -/
noncomputable def L (M : Model X) (V : @Opens X M.tau) : ScottOpens (Point M) :=
  sSup {U : ScottOpens (Point M) | trace U ⊆ V}

theorem le_L_iff {V : @Opens X M.tau} {U : ScottOpens (Point M)} :
    U ≤ L M V ↔ trace U ⊆ V := by
  constructor
  · intro h y hy
    have hyL : WithScott.toScott (e M y) ∈ L M V := h hy
    obtain ⟨Z, hZ, hyZ⟩ := Opens.mem_sSup.mp hyL
    exact hZ hyZ
  · intro h; exact le_sSup h

theorem H_le_L (M : Model X) (V : @Opens X M.tau) : H M V ≤ L M V := by
  apply le_L_iff.mpr
  rw [trace_H]

@[simp] theorem trace_L (M : Model X) (V : @Opens X M.tau) : trace (L M V) = V := by
  apply Set.Subset.antisymm
  · exact (le_L_iff.mp (le_rfl : L M V ≤ L M V))
  · intro y hy
    apply H_le_L M V
    change @IsOpen X M.tau (V : Set X) ∧ y ∈ V
    exact ⟨@Opens.isOpen X M.tau V, hy⟩

theorem L_mono (M : Model X) : Monotone (L M) := by
  intro U V hUV
  apply le_L_iff.mpr
  rw [trace_L]
  exact hUV

theorem kernel_subset_of_mem_L (M : Model X) (V : @Opens X M.tau) {p : Point M}
    (hp : WithScott.toScott p ∈ L M V) : p.kernel ⊆ V := by
  simpa only [trace_L] using kernel_subset_trace hp

end ZFCFubini.FilterDcpo
