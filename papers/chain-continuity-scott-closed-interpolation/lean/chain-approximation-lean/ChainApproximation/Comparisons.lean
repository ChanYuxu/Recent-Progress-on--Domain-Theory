import ChainApproximation.ChainCompleteness

/-!
# Cofinality comparisons for chain approximation

Source `lem:comparisons`, equations (kappa-one), (comparison-points),
(comparison-chain), and (sup-cofinality).
-/

set_option autoImplicit false

universe u

namespace ChainApproximation

open Set Cardinal

variable {P : Type u} [PartialOrder P]

theorem kappa_one_iff (hP : IsChainContinuous P) (p : P) :
    kappa p = 1 ↔ ChainBelow p p := by
  constructor
  · intro hp
    obtain ⟨q, hq⟩ := Order.cof_eq_one_iff.mp hp
    have hpq : p ≤ q.val := (hP.section_lub p).2 (fun a ha ↦ hq ⟨a, ha⟩)
    exact q.property.mono hpq le_rfl
  · intro hp
    exact Order.cof_eq_one_iff.mpr ⟨⟨p, hp⟩, fun q ↦ q.property.le⟩

theorem kappa_regular_or_one (hP : IsChainContinuous P) (p : P) :
    kappa p = 1 ∨ Cardinal.IsRegular (kappa p) := by
  by_cases hp : kappa p = 1
  · exact Or.inl hp
  · exact Or.inr ((hP.section_hasCofinalChain p).regular hp)

theorem kappa_aleph0_le (hP : IsChainContinuous P) {p : P} (hp : ¬ ChainBelow p p) :
    Cardinal.aleph0 ≤ kappa p :=
  (hP.section_hasCofinalChain p).aleph0_le (fun h ↦ hp ((kappa_one_iff hP p).mp h))

/-- Source comparison of two points. The monotone inclusion between the two
chain-generated ideals is bounded by the cofinality mismatch lemma. -/
theorem chainBelow_of_le_kappa_ne (hP : IsChainContinuous P) {p q : P}
    (hpq : p ≤ q) (hne : kappa p ≠ kappa q) : ChainBelow p q := by
  let f : chainSection p → chainSection q := fun a ↦
    ⟨a.val, a.property.mono le_rfl hpq⟩
  have hf : Monotone f := fun _ _ hab ↦ hab
  obtain ⟨z, hz⟩ := (hP.section_hasCofinalChain p).range_bounded_of_cof_ne
    (hP.section_hasCofinalChain q) f hf hne
  have hpz : p ≤ z.val := (hP.section_lub p).2 (fun a ha ↦ hz (Set.mem_range_self ⟨a, ha⟩))
  exact z.property.mono hpz le_rfl

/-- Source comparison of a point with a chain. No greatest-element or
countability restriction on the test chain is imposed. -/
theorem exists_ge_of_le_lub_kappa_ne (hP : IsChainContinuous P)
    {p s : P} {C : Set P} (hC : NonemptyChain C) (hs : IsLUB C s)
    (hps : p ≤ s) (hne : kappa p ≠ Order.cof C) : ∃ c ∈ C, p ≤ c := by
  have hpC : p ∈ cut C := by
    rw [cut_eq_Iic hs]
    exact hps
  let f : chainSection p → lowerHull C := fun a ↦ ⟨a.val, a.property C hC hpC⟩
  have hf : Monotone f := fun _ _ hab ↦ hab
  have hcof : Order.cof (chainSection p) ≠ Order.cof (lowerHull C) := by
    rwa [cof_lowerHull hC]
  obtain ⟨z, hz⟩ := (hP.section_hasCofinalChain p).range_bounded_of_cof_ne
    (lowerHull_hasCofinalChain hC) f hf hcof
  have hpz : p ≤ z.val := (hP.section_lub p).2 (fun a ha ↦ hz (Set.mem_range_self ⟨a, ha⟩))
  obtain ⟨c, hc, hzc⟩ := z.property
  exact ⟨c, hc, hpz.trans hzc⟩

theorem kappa_eq_cof_of_not_mem (hP : IsChainContinuous P)
    {p : P} {C : Set P} (hC : NonemptyChain C) (hs : IsLUB C p) (hp : p ∉ C) :
    kappa p = Order.cof C := by
  by_contra hne
  obtain ⟨c, hc, hpc⟩ := exists_ge_of_le_lub_kappa_ne hP hC hs le_rfl hne
  exact hp ((le_antisymm hpc (hs.1 hc)) ▸ hc)

/-- The cofinal chain in the approximating section may be indexed by its
actual minimal cardinal, with strict increase when the point is not compact. -/
theorem IsChainContinuous.strictMono_section (hP : IsChainContinuous P)
    {p : P} (hp : ¬ ChainBelow p p) :
    ∃ f : CofinalIndex (kappa p) → P, StrictMono f ∧
      (∀ i, ChainBelow (f i) p) ∧ IsLUB (Set.range f) p := by
  obtain ⟨g, hg, hcof⟩ := (hP.section_hasCofinalChain p).strictMono_cofinal
    (fun h ↦ hp ((kappa_one_iff hP p).mp h))
  let f : CofinalIndex (kappa p) → P := fun i ↦ (g i).val
  refine ⟨f, fun i j hij ↦ hg hij, fun i ↦ (g i).property, ?_, ?_⟩
  · rintro _ ⟨i, rfl⟩
    exact (g i).property.le
  · intro q hq
    apply (hP.section_lub p).2
    intro a ha
    obtain ⟨_, ⟨i, rfl⟩, hai⟩ := hcof ⟨a, ha⟩
    exact (show a ≤ f i from hai).trans (hq (Set.mem_range_self _))

theorem IsChainContinuous.nat_section (hP : IsChainContinuous P)
    {p : P} (hp : kappa p = Cardinal.aleph0) :
    ∃ f : ℕ → P, Monotone f ∧ (∀ n, ChainBelow (f n) p) ∧
      (∀ a, ChainBelow a p → ∃ n, a ≤ f n) ∧ IsLUB (Set.range f) p := by
  classical
  obtain ⟨A, hA, hcard⟩ := Order.cof_eq (chainSection p)
  have hcount : A.Countable := by
    haveI : Countable A := Cardinal.mk_le_aleph0_iff.mp (hcard.trans hp).le
    exact Set.to_countable A
  have hD : NonemptyDirected (Set.univ : Set (chainSection p)) := by
    refine ⟨?_, ?_⟩
    · obtain ⟨a, ha⟩ := (hP.section_directed p).1
      exact ⟨⟨a, ha⟩, trivial⟩
    · intro a _ b _
      obtain ⟨c, hc, hac, hbc⟩ := (hP.section_directed p).2 a.val a.property b.val b.property
      exact ⟨⟨c, hc⟩, trivial, hac, hbc⟩
  obtain ⟨g, hg, _, hcof⟩ := countable_cofinal_chain hD hcount (Set.subset_univ A)
    (fun a _ ↦ hA a)
  let f : ℕ → P := fun n ↦ (g n).val
  have hcf : ∀ a, ChainBelow a p → ∃ n, a ≤ f n := by
    intro a ha
    obtain ⟨n, hn⟩ := hcof ⟨a, ha⟩ trivial
    exact ⟨n, hn⟩
  refine ⟨f, fun i j hij ↦ hg hij, fun n ↦ (g n).property, hcf, ?_, ?_⟩
  · rintro _ ⟨n, rfl⟩
    exact (g n).property.le
  · intro q hq
    apply (hP.section_lub p).2
    intro a ha
    obtain ⟨n, han⟩ := hcf a ha
    exact han.trans (hq (Set.mem_range_self _))

end ChainApproximation
