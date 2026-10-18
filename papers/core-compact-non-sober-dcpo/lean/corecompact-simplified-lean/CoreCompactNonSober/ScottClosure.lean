import CoreCompactNonSober.DefinitionChecks

/-!
# Directed closure stages and elementary Scott-space consequences

Source: `def:closure-stages`, `eq:stages-in-closure`, and the final
non-sobriety and compactness arguments. No counterexample object is assumed
to exist in this module.
-/

set_option autoImplicit false

universe u

namespace CoreCompactNonSober

open Set

variable {P : Type u} [PartialOrder P]

/-- The source's directed-supremum/lower-hull stages. Using `IsLUB` rather
than a chosen supremum makes the definition independent of choice of a
dcpo supremum operation; on a dcpo it is exactly the displayed definition. -/
def closureStage : ℕ → Set P → Set P
  | 0, A => lowerHull A
  | n + 1, A => lowerHull
      {p | ∃ E : Set P, E ⊆ closureStage n A ∧ NonemptyDirected E ∧ IsLUB E p}

theorem closureStage_subset_closure (n : ℕ) (A : Set P) :
    closureStage n A ⊆ @closure P (scottTopology P) A := by
  letI : TopologicalSpace P := scottTopology P
  have hc : IsScottClosed (closure A) :=
    (isClosed_scott_iff _).mp isClosed_closure
  induction n with
  | zero =>
    rintro x ⟨a, ha, hxa⟩
    exact hc.1 hxa (subset_closure ha)
  | succ n ih =>
    rintro x ⟨p, ⟨E, hE, hdir, hp⟩, hxp⟩
    have hpC : p ∈ closure A := hc.2 E (hE.trans ih) hdir p hp
    exact hc.1 hxp hpC

theorem closureStage_mono (n : ℕ) {A B : Set P} (hAB : A ⊆ B) :
    closureStage n A ⊆ closureStage n B := by
  induction n with
  | zero =>
    rintro x ⟨a, ha, hxa⟩
    exact ⟨a, hAB ha, hxa⟩
  | succ n ih =>
    rintro x ⟨p, ⟨E, hE, hdir, hp⟩, hxp⟩
    exact ⟨p, ⟨E, hE.trans ih, hdir, hp⟩, hxp⟩

theorem closureStage_subset_succ (n : ℕ) (A : Set P) :
    closureStage n A ⊆ closureStage (n + 1) A := by
  intro x hx
  refine ⟨x, ⟨{x}, ?_, ?_, ?_⟩, le_rfl⟩
  · simpa using hx
  · refine ⟨Set.singleton_nonempty x, ?_⟩
    intro a ha b hb
    have ha' : a = x := Set.mem_singleton_iff.mp ha
    have hb' : b = x := Set.mem_singleton_iff.mp hb
    subst a
    subst b
    exact ⟨x, by simp, le_rfl, le_rfl⟩
  · constructor
    · intro a ha
      exact (Set.mem_singleton_iff.mp ha).le
    · intro b hb
      exact hb (by simp)

theorem closureStage_subset_closed (n : ℕ) {A C : Set P}
    (hC : @IsClosed P (scottTopology P) C) (hAC : A ⊆ C) :
    closureStage n A ⊆ C := by
  letI : TopologicalSpace P := scottTopology P
  exact (closureStage_subset_closure n A).trans (closure_minimal hAC hC)

/-- The whole-space irreducibility/no-greatest argument of `thm:main`. -/
theorem not_scottSober_of_irreducible_univ
    (hI : @IsIrreducible P (scottTopology P) Set.univ)
    (hng : NoGreatestElement P) : ¬ ScottSober P := by
  letI : TopologicalSpace P := scottTopology P
  intro hs
  obtain ⟨p, hp, _⟩ := hs Set.univ isClosed_univ hI
  apply hng
  refine ⟨p, ?_⟩
  intro q
  have hq : q ∈ closure ({p} : Set P) := by rw [hp]; trivial
  rw [scott_closure_singleton] at hq
  exact hq

/-- Every open cover of a Scott space with a least element has a one-set
subcover, as used in `prop:ambient-properties` and `thm:main`. -/
theorem scottCompact_of_least (p : P) (hp : ∀ q : P, p ≤ q) : ScottCompact P := by
  letI : TopologicalSpace P := scottTopology P
  apply isCompact_univ_iff.mp
  apply isCompact_of_finite_subcover
  intro ι U hU hcover
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcover (Set.mem_univ p))
  refine ⟨{i}, ?_⟩
  intro q _
  have hupper : IsUpperSet (U i) := ((isOpen_scott_iff _).mp (hU i)).1
  exact Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨by simp, hupper (hp q) hi⟩⟩

end CoreCompactNonSober
