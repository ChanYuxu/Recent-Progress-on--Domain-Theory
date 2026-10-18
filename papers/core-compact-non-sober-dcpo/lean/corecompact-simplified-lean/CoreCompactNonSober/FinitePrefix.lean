import CoreCompactNonSober.AmbientBasis
import Mathlib.Order.Interval.Finset.Nat

/-!
# Finite prefixes and domination by arbitrary directed sets

Source: `lem:finite-prefix`. Only finitely many suppliers are selected;
the directed set itself is never assumed to be countable.
-/

set_option autoImplicit false

namespace CoreCompactNonSober.Ambient

open Set

abbrev PrefixIndex (M : ℕ) := ↥(Finset.Ico 2 M)

def prefixCoordinate {M : ℕ} (j : PrefixIndex M) : Coordinate :=
  ⟨j.val, (Finset.mem_Ico.mp j.property).1⟩

abbrev PrefixConfiguration (M : ℕ) :=
  (j : PrefixIndex M) → Finset (Alphabet (prefixCoordinate j))

instance prefixDataCountable : Countable (Σ M : ℕ, PrefixConfiguration M) := inferInstance

def restrictPrefix (A : Configuration) (M : ℕ) : PrefixConfiguration M :=
  fun j ↦ A (prefixCoordinate j)

def splicePrefix (M : ℕ) (A : PrefixConfiguration M) (T : Configuration) : Configuration :=
  fun j ↦ if hj : j.val < M then
    A ⟨j.val, Finset.mem_Ico.mpr ⟨j.property, hj⟩⟩ else T j

theorem finite_prefix_bound (E : Set Carrier) (hE : NonemptyDirected E)
    (p : Carrier) (hp : p ≤ sSup E) (M : ℕ) (e₀ : Carrier) (he₀ : e₀ ∈ E) :
    ∃ e ∈ E, e₀ ≤ e ∧ ∀ j : Coordinate, j.val < M →
      configuration p j ⊆ configuration e j := by
  classical
  let I := Σ j : PrefixIndex M, ↥(configuration p (prefixCoordinate j))
  have hsupplier : ∀ i : I, ∃ e ∈ E,
      i.2.val ∈ configuration e (prefixCoordinate i.1) := by
    intro i
    have hz : i.2.val ∈ configuration (sSup E) (prefixCoordinate i.1) :=
      ((le_iff _ _).mp hp).2 _ i.2.property
    exact (mem_configuration_sSup E _ _).mp hz
  choose es hes hentry using hsupplier
  let F : Finset Carrier := insert e₀ (Finset.univ.image es)
  have hFE : (F : Set Carrier) ⊆ E := by
    intro e he
    rcases Finset.mem_insert.mp he with rfl | he
    · exact he₀
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp he
      exact hes i
  obtain ⟨e, he, hbound⟩ := (nonemptyDirected_iff_finite_bounds E).mp hE F hFE
  refine ⟨e, he, hbound e₀ (Finset.mem_insert_self _ _), ?_⟩
  intro j hj z hz
  let jj : PrefixIndex M := ⟨j.val, Finset.mem_Ico.mpr ⟨j.property, hj⟩⟩
  let i : I := ⟨jj, ⟨z, hz⟩⟩
  have hesi : es i ∈ F :=
    Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
  exact ((le_iff _ _).mp (hbound (es i) hesi)).2 j (hentry i)

/-- The precise finite-prefix mechanism used for pair rows: the prefix
comes from `p`, the tail is below `b`, and the height is below that of `b`. -/
theorem finite_prefix_domination (E : Set Carrier) (hE : NonemptyDirected E)
    (p b r : Carrier) (hp : p ≤ sSup E) (e₀ : Carrier) (he₀ : e₀ ∈ E)
    (hbe₀ : b ≤ e₀) (M : ℕ) (hrheight : height r ≤ height b)
    (hrprefix : ∀ j : Coordinate, j.val < M → configuration r j ⊆ configuration p j)
    (hrtail : ∀ j : Coordinate, M ≤ j.val → configuration r j ⊆ configuration b j) :
    ∃ e ∈ E, r ≤ e := by
  obtain ⟨e, he, he₀e, hprefix⟩ := finite_prefix_bound E hE p hp M e₀ he₀
  have hbe : b ≤ e := hbe₀.trans he₀e
  refine ⟨e, he, (le_iff r e).mpr ⟨hrheight.trans ((le_iff b e).mp hbe).1, ?_⟩⟩
  intro j
  by_cases hj : j.val < M
  · exact (hrprefix j hj).trans (hprefix j hj)
  · exact (hrtail j (by omega)).trans (((le_iff b e).mp hbe).2 j)

end CoreCompactNonSober.Ambient
