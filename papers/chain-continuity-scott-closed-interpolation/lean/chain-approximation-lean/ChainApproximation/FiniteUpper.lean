import ChainApproximation.ClosedApproximation

/-!
# Scott-closed approximation on lower-set lattices

Source `lem:finite-upper` and `cor:closed-cont`. Finite tests include the
empty finite set. The lattice is mathlib's actual `LowerSet Q`, with joins
given by unions, rather than an abstract interface carrying the conclusion.
-/

set_option autoImplicit false

universe u

namespace ChainApproximation

open Set

variable {Q : Type u} [PartialOrder Q]

def FiniteUpper (A E : Set Q) : Prop :=
  ∀ F : Finset Q, (F : Set Q) ⊆ A → ∃ q ∈ E, ∀ x ∈ F, x ≤ q

def finiteGenerators (A : LowerSet Q) : Set (LowerSet Q) :=
  {D | ∃ F : Finset Q, (F : Set Q) ⊆ A ∧ D = lowerClosure (F : Set Q)}

theorem lowerClosure_finset_mono {F G : Finset Q} (hFG : F ⊆ G) :
    lowerClosure (F : Set Q) ≤ lowerClosure (G : Set Q) := by
  apply lowerClosure_le.mpr
  exact (show (F : Set Q) ⊆ G from hFG).trans subset_lowerClosure

theorem finiteGenerators_directed (A : LowerSet Q) : NonemptyDirected (finiteGenerators A) := by
  classical
  refine ⟨⟨lowerClosure (∅ : Set Q), ∅, by simp, by simp⟩, ?_⟩
  rintro _ ⟨F, hFA, rfl⟩ _ ⟨G, hGA, rfl⟩
  refine ⟨lowerClosure ((F ∪ G : Finset Q) : Set Q), ⟨F ∪ G, ?_, rfl⟩,
    lowerClosure_finset_mono Finset.subset_union_left,
    lowerClosure_finset_mono Finset.subset_union_right⟩
  simpa only [Finset.coe_union, Set.union_subset_iff] using And.intro hFA hGA

theorem finiteGenerators_lub (A : LowerSet Q) : IsLUB (finiteGenerators A) A := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨F, hFA, rfl⟩
    exact lowerClosure_le.mpr hFA
  · intro B hB q hq
    have hF : (lowerClosure ({q} : Set Q) : LowerSet Q) ∈ finiteGenerators A :=
      ⟨{q}, by simpa using hq, by simp⟩
    exact hB hF (subset_lowerClosure (Set.mem_singleton q))

theorem finite_subset_directed_sup {D : Set (LowerSet Q)} (hD : NonemptyDirected D)
    (F : Finset Q) (hF : (F : Set Q) ⊆ (sSup D : LowerSet Q)) :
    ∃ B ∈ D, (F : Set Q) ⊆ B := by
  classical
  induction F using Finset.induction_on with
  | empty =>
    obtain ⟨B, hB⟩ := hD.1
    exact ⟨B, hB, by simp⟩
  | @insert q F hq ih =>
    obtain ⟨B, hB, hFB⟩ := ih (fun x hx ↦ hF (Finset.mem_insert_of_mem hx))
    obtain ⟨C, hC, hqC⟩ := LowerSet.mem_sSup_iff.mp (hF (Finset.mem_insert_self _ _))
    obtain ⟨E, hE, hBE, hCE⟩ := hD.2 B hB C hC
    refine ⟨E, hE, ?_⟩
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hCE hqC
    · exact hBE (hFB hx)

private def avoidingFinite (E : LowerSet Q) (F : Finset Q) : Set (LowerSet Q) :=
  {D | D ≤ E ∧ ¬ (F : Set Q) ⊆ D}

private theorem avoidingFinite_scottClosed (E : LowerSet Q) (F : Finset Q) :
    IsScottClosed (avoidingFinite E F) := by
  refine ⟨?_, ?_⟩
  · intro A B hAB hB
    exact ⟨hAB.trans hB.1, fun hFA ↦ hB.2 (hFA.trans hAB)⟩
  · intro D hDH hD s hs
    refine ⟨hs.2 (fun B hB ↦ (hDH hB).1), ?_⟩
    intro hFs
    have hFsup : (F : Set Q) ⊆ (sSup D : LowerSet Q) := by
      rwa [← hs.unique (isLUB_sSup D)]
    obtain ⟨B, hB, hFB⟩ := finite_subset_directed_sup hD F hFsup
    exact (hDH hB).2 hFB

/-- Source `lem:finite-upper`, with the stated nonempty right endpoint. -/
theorem closedBelow_iff_finiteUpper (A E : LowerSet Q) (_hE : (E : Set Q).Nonempty) :
    ClosedBelow A E ↔ FiniteUpper (A : Set Q) (E : Set Q) := by
  classical
  constructor
  · intro hAE F hFA
    by_contra hno
    have hEH : E ≤ sSup (avoidingFinite E F) := by
      intro q hq
      apply LowerSet.mem_sSup_iff.mpr
      refine ⟨LowerSet.Iic q, ⟨LowerSet.Iic_le.mpr hq, ?_⟩, le_rfl⟩
      intro hFI
      exact hno ⟨q, hq, fun x hx ↦ hFI hx⟩
    exact (hAE (avoidingFinite E F) (avoidingFinite_scottClosed E F) hEH).2 hFA
  · intro hfinite H hH hEH
    have hKH : finiteGenerators A ⊆ H := by
      rintro _ ⟨F, hFA, rfl⟩
      obtain ⟨q, hqE, hFq⟩ := hfinite F hFA
      obtain ⟨B, hBH, hqB⟩ := LowerSet.mem_sSup_iff.mp (hEH hqE)
      apply hH.1 (show lowerClosure (F : Set Q) ≤ B from ?_) hBH
      apply lowerClosure_le.mpr
      intro x hx
      exact B.lower (hFq x hx) hqB
    exact hH.2 (finiteGenerators A) hKH (finiteGenerators_directed A) A (finiteGenerators_lub A)

theorem closedBelow_principal (E : LowerSet Q) {q : Q} (hq : q ∈ E) :
    ClosedBelow (LowerSet.Iic q) E := by
  apply (closedBelow_iff_finiteUpper _ E ⟨q, hq⟩).mpr
  intro F hF
  exact ⟨q, hq, fun x hx ↦ hF hx⟩

/-- Source `cor:closed-cont`, the supremum of all beneath lower sets. -/
theorem lowerSet_closedContinuous : IsClosedContinuous (LowerSet Q) := by
  intro E
  apply le_antisymm
  · exact sSup_le (fun _ h ↦ h.le)
  · intro q hq
    exact LowerSet.mem_sSup_iff.mpr
      ⟨LowerSet.Iic q, closedBelow_principal E hq, le_rfl⟩

theorem lowerSet_closedContinuousPlus : IsClosedContinuousPlus (LowerSet Q) :=
  closedContinuous_iff_plus.mp lowerSet_closedContinuous

/-- The lower section is literally an intersection of the closed test sets,
so the continuity theorem satisfies the full source closed-ideal convention. -/
theorem closedBelow_section_scottClosed {M : Type u} [CompleteLattice M] (b : M) :
    IsScottClosed {a | ClosedBelow a b} := by
  refine ⟨?_, ?_⟩
  · intro x y hxy hy
    exact hy.mono hxy le_rfl
  · intro D hD hdir s hs H hH hbH
    exact hH.2 D (fun d hd ↦ hD hd H hH hbH) hdir s hs

end ChainApproximation
