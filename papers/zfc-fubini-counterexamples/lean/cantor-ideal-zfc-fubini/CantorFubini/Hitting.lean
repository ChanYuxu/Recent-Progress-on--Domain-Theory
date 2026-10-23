import CantorFubini.RandomCylinders

/-! Source Lemma `lem:hitting`, proved by the printed countable-base and finite
coordinate argument. All code is new; no Baire-category theorem is used. -/

set_option autoImplicit false
open Set Filter Topology TopologicalSpace MeasureTheory
open scoped ENNReal Topology BigOperators

namespace CantorFubini

def uncovered (W : Set Omega) : Set Cantor :=
  (⋃ t ∈ W, (randomOpen t : Set Cantor))ᶜ

theorem uncovered_isClosed (W : Set Omega) : IsClosed (uncovered W) :=
  (isOpen_iUnion (fun t => isOpen_iUnion (fun _ => (randomOpen t).isOpen))).isClosed_compl

theorem coordinate_notMem_uncovered {W : Set Omega} {t : Omega} (ht : t ∈ W) (n : ℕ) :
    t n ∉ uncovered W := by
  intro hn
  exact hn (mem_iUnion₂.mpr ⟨t, ht, randomOpen_contains_coordinate t n⟩)

/-- Positive measure of any set of parameters forces the union of their
random opens to have null complement. This is the actual finite-coordinate
independence argument in the manuscript. -/
theorem uncovered_null_of_positive {W : Set Omega} (hW : 0 < parameterProbability W) :
    cantorMeasure (uncovered W) = 0 := by
  by_contra hne
  have hlt : 1 - cantorMeasure (uncovered W) < 1 :=
    ENNReal.sub_lt_self (by norm_num) (by norm_num) hne
  have hb : ∀ k : ℕ, parameterProbability W ≤ (1 - cantorMeasure (uncovered W)) ^ k := by
    intro k
    rw [← finite_coordinate_avoidance (uncovered_isClosed W).measurableSet k]
    exact measure_mono (fun t ht n _ => coordinate_notMem_uncovered ht n)
  have hz : parameterProbability W ≤ 0 :=
    ge_of_tendsto' (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hlt) hb
  exact hW.not_ge hz

/-- First assertion of source Lemma `lem:hitting`: one null exceptional set
works for all points and all relatively open subsets of the positive carrier. -/
theorem hitting_dense {D : Set Omega} (hD : PositiveCarrier parameterProbability D) :
    ∃ N : Set Cantor, cantorMeasure N = 0 ∧
      ∀ x ∉ N, IsOpen {t : D | x ∈ randomOpen t.val} ∧
        Dense {t : D | x ∈ randomOpen t.val} := by
  classical
  let B : Set (Set D) := {W | W ∈ countableBasis D ∧ W.Nonempty}
  have hBc : B.Countable := (countable_countableBasis D).mono (fun _ h => h.1)
  letI : Countable B := hBc.to_subtype
  let N : Set Cantor := ⋃ W : B, uncovered (Subtype.val '' W.val)
  have hN : cantorMeasure N = 0 := by
    apply measure_iUnion_null
    intro W
    exact uncovered_null_of_positive
      (hD.2.2 W.val (isOpen_of_mem_countableBasis W.property.1) W.property.2)
  refine ⟨N, hN, ?_⟩
  intro x hx
  refine ⟨(randomOpen_incidence_isOpen x).preimage continuous_subtype_val, ?_⟩
  apply dense_iff_inter_open.mpr
  intro W hWo hWn
  obtain ⟨t, ht⟩ := hWn
  obtain ⟨V, hVb, htV, hVW⟩ := (isBasis_countableBasis D).exists_subset_of_mem_open ht hWo
  let b : B := ⟨V, hVb, ⟨t, htV⟩⟩
  have hxn : x ∉ uncovered (Subtype.val '' V) :=
    fun hn => hx (mem_iUnion.mpr ⟨b, hn⟩)
  have hcov : x ∈ ⋃ s ∈ Subtype.val '' V, (randomOpen s : Set Cantor) := by
    exact not_not.mp hxn
  obtain ⟨s, ⟨sD, hsV, rfl⟩, hxs⟩ := mem_iUnion₂.mp hcov
  exact ⟨sD, hVW hsV, hxs⟩

theorem finite_hitting_of_dense {D : Set Omega} {N : Set Cantor}
    (hd : ∀ x ∉ N, IsOpen {t : D | x ∈ randomOpen t.val} ∧
      Dense {t : D | x ∈ randomOpen t.val})
    (F : Finset Cantor) (hF : ∀ x ∈ F, x ∉ N)
    (W : Set D) (hWo : IsOpen W) (hWn : W.Nonempty) :
    ∃ t ∈ W, (F : Set Cantor) ⊆ randomOpen t.val := by
  classical
  have hdense : Dense {t : D | ∀ x ∈ F, x ∈ randomOpen t.val} := by
    induction F using Finset.induction_on with
    | empty => simpa using (dense_univ : Dense (univ : Set D))
    | @insert x F hx ih =>
        have hxN : x ∉ N := hF x (Finset.mem_insert_self _ _)
        have hFN : ∀ y ∈ F, y ∉ N := fun y hy => hF y (Finset.mem_insert_of_mem hy)
        have hi := (hd x hxN).2.inter_of_isOpen_left (ih hFN) (hd x hxN).1
        simpa only [Finset.mem_insert, forall_eq_or_imp, mem_setOf_eq, setOf_and] using hi
  obtain ⟨t, ht, hWt⟩ := hdense.exists_mem_open hWo hWn
  exact ⟨t, hWt, ht⟩

/-- Exact finite simultaneous containment consequence, including F=∅. -/
theorem hitting {D : Set Omega} (hD : PositiveCarrier parameterProbability D) :
    ∃ N : Set Cantor, cantorMeasure N = 0 ∧
      ∀ F : Finset Cantor, (∀ x ∈ F, x ∉ N) →
        ∀ W : Set D, IsOpen W → W.Nonempty →
          ∃ t ∈ W, (F : Set Cantor) ⊆ randomOpen t.val := by
  obtain ⟨N, hN, hd⟩ := hitting_dense hD
  exact ⟨N, hN, finite_hitting_of_dense hd⟩

/-- Source-exact public wrapper for both assertions of Lemma `lem:hitting`
using one and the same exceptional null set. -/
theorem source_hitting {D : Set Omega} (hD : PositiveCarrier parameterProbability D) :
    ∃ N : Set Cantor, cantorMeasure N = 0 ∧
      (∀ x ∉ N, IsOpen {t : D | x ∈ randomOpen t.val} ∧
        Dense {t : D | x ∈ randomOpen t.val}) ∧
      (∀ F : Finset Cantor, (∀ x ∈ F, x ∉ N) →
        ∀ W : Set D, IsOpen W → W.Nonempty →
          ∃ t ∈ W, (F : Set Cantor) ⊆ randomOpen t.val) := by
  obtain ⟨N, hN, hd⟩ := hitting_dense hD
  exact ⟨N, hN, hd, finite_hitting_of_dense hd⟩

end CantorFubini
