import CoreCompactNonSober.RetainedLocalizedClosure

/-!
Source-facing interfaces for the actual construction in lines 810–1054 of
the immutable 2026-10-15 manuscript. Reused legacy names in the imported
tree designate the newly adapted dyadic, label/reference recursion in this
isolated project, not a theorem imported from any older counterexample.
-/

set_option autoImplicit false

namespace CoreCompactSimplified

open Set CoreCompactNonSober CoreCompactNonSober.Ambient
  CoreCompactNonSober.Construction CoreCompactNonSober.Localization

/-- The literal zero-layer/packet union of `eq:D-definition`. -/
abbrev recursiveSubset : Set Carrier := retained

/-- Lemma `lem:insertion` (i), preserving the printed assumptions and
conclusion; the implementation additionally proves a specific tail omission. -/
theorem insertion_point (H : Set Carrier) (hH : ∀ x ∈ H, Positive x)
    (hsmall : Cardinal.mk H < lambda) (b : Carrier) (hb : Positive b)
    (V : ScottOpens Carrier) (hbV : b ∈ V) :
    ∃ s : Carrier, s ∈ V ∧ s ≤ b ∧ 0 < height s ∧ height s < 1 ∧
      ∀ x ∈ H, ¬ x ≤ s := by
  obtain ⟨s, hspos, hs1, hsb, hsV, havoid, _, _⟩ :=
    single_insertion H hH hsmall b hb V hbV
  exact ⟨s, hsV, hsb, hspos, hs1, havoid⟩

/-- Lemma `lem:insertion` (ii), with the actual dyadic row and its printed
finite-prefix domination conclusion for arbitrary directed ambient sets.
`n=0` here is the source's `r_1`. The source assumption `p∈H` is explicit. -/
theorem insertion_sequence_prescribed (H : Set Carrier) (hH : ∀ x ∈ H, Positive x)
    (hsmall : Cardinal.mk H < lambda) (p b : Carrier) (hpH : p ∈ H)
    (hp1 : height p < 1) (hpb : height p ≤ height b) :
    ∃ R : PairRow p b, Protects H R.pattern ∧ (∀ x ∈ H, ∀ n, ¬ x ≤ R.point n) ∧
      ∀ (E : Set Carrier), NonemptyDirected E →
        ∀ s : Carrier, IsLUB E s → p ≤ s →
          ∀ e₀ ∈ E, b ≤ e₀ → ∀ n, ∃ e ∈ E, R.point n ≤ e := by
  obtain ⟨R, hpattern, havoid⟩ := pair_insertion_prescribed H hH hsmall p b (hH p hpH) hp1 hpb
  refine ⟨R, hpattern, havoid, ?_⟩
  intro E hE s hs hps e₀ he₀ hbe₀ n
  have heq : sSup E = s := (isLUB_sSup E).unique hs
  exact R.finite_prefix_domination hpb E hE
    (by simpa only [heq] using hps) e₀ he₀ hbe₀ n

/-- Ordinary stronger-row interface, derived from the full prescribed
tail-selection recipe without changing the actual row chosen there. -/
theorem insertion_sequence (H : Set Carrier) (hH : ∀ x ∈ H, Positive x)
    (hsmall : Cardinal.mk H < lambda) (p b : Carrier) (hpH : p ∈ H)
    (hp1 : height p < 1) (hpb : height p ≤ height b) :
    ∃ R : PairRow p b, (∀ x ∈ H, ∀ n, ¬ x ≤ R.point n) ∧
      ∀ (E : Set Carrier), NonemptyDirected E →
        ∀ s : Carrier, IsLUB E s → p ≤ s →
          ∀ e₀ ∈ E, b ≤ e₀ → ∀ n, ∃ e ∈ E, R.point n ≤ e := by
  obtain ⟨R, _, havoid, hdom⟩ := insertion_sequence_prescribed H hH hsmall p b hpH hp1 hpb
  exact ⟨R, havoid, hdom⟩

/-- The printed conclusion of Lemma `lem:insertion` (ii), forgetting only
the extra explicit formula/cutoff fields proved by `insertion_sequence`.
Natural index `n=0` denotes the printed first term `r_1`. -/
theorem insertion_sequence_printed (H : Set Carrier) (hH : ∀ x ∈ H, Positive x)
    (hsmall : Cardinal.mk H < lambda) (p b : Carrier) (hpH : p ∈ H)
    (hp1 : height p < 1) (hpb : height p ≤ height b) :
    ∃ r : ℕ → Carrier, StrictMono r ∧ (∀ n, Positive (r n)) ∧
      IsLUB (Set.range r) p ∧ (∀ x ∈ H, ∀ n, ¬ x ≤ r n) ∧
      ∀ (E : Set Carrier), NonemptyDirected E →
        ∀ s : Carrier, IsLUB E s → p ≤ s →
          ∀ e₀ ∈ E, b ≤ e₀ → ∀ n, ∃ e ∈ E, r n ≤ e := by
  obtain ⟨R, havoid, hdom⟩ := insertion_sequence H hH hsmall p b hpH hp1 hpb
  exact ⟨R.point, R.strictMono, R.positive, R.isLUB, havoid, hdom⟩

/-- Proposition `prop:D-subdcpo`. -/
theorem recursive_subset_isSubDcpo : IsSubDcpo recursiveSubset := retained_isSubDcpo

/-- Condition (i) in Proposition `prop:two-conditions`, with its printed
order of conjunctions and all ambient points quantified. -/
theorem recursive_lowerNeighborhoodApproximation :
    LowerNeighborhoodApproximation recursiveSubset := by
  intro p V hpV
  obtain ⟨d, hdp, hdV⟩ := retained_lowerApproximation p V hpV
  exact ⟨d, hdV, hdp⟩

/-- Condition (ii), proved directly by the two-row/rational-cut route. -/
theorem recursive_commonLowerWitness : CommonLowerWitness recursiveSubset :=
  retained_commonLowerWitness

/-- Proposition `prop:two-conditions`. -/
theorem recursive_two_conditions :
    LowerNeighborhoodApproximation recursiveSubset ∧
      CommonLowerWitness recursiveSubset :=
  ⟨recursive_lowerNeighborhoodApproximation, recursive_commonLowerWitness⟩

theorem recursive_bottom_mem : (⊥ : Carrier) ∈ recursiveSubset := by
  apply zeroLayer_subset_retained
  rw [bottom_eq_bottomPoint]
  rfl

theorem recursive_top_not_mem : (⊤ : Carrier) ∉ recursiveSubset := by
  intro h
  have hlt := retained_height_lt_one h
  rw [top_eq_fullAt_one] at hlt
  exact (lt_irrefl (1 : ℝ)) hlt

theorem recursive_proper : recursiveSubset ⊂ Set.univ := retained_proper

end CoreCompactSimplified
