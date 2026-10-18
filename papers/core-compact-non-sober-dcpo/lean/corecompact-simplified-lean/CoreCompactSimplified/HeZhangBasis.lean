import CoreCompactSimplified.HeZhangClosed

/-!
The countable decreasing open sequence and compact neighborhoods chosen at
the start of He–Zhang Theorem 4.13. Finite intersections of the enumerated
nonempty basis members are actual opens, with their nonemptiness proved from
irreducibility. No countability of the carrier is assumed.
-/

set_option autoImplicit false

universe u

namespace CoreCompactSimplified.HeZhangBasis

open Set TopologicalSpace CoreCompactNonSober

section Topological

variable {X : Type u} [TopologicalSpace X]

def finiteIntersections (B : ℕ → Opens X) : ℕ → Opens X
  | 0 => B 0
  | n + 1 => finiteIntersections B n ⊓ B (n + 1)

theorem finiteIntersections_antitone (B : ℕ → Opens X) :
    Antitone (finiteIntersections B) := by
  apply antitone_nat_of_succ_le
  intro n
  exact inf_le_left

theorem finiteIntersections_le (B : ℕ → Opens X) (n : ℕ) :
    finiteIntersections B n ≤ B n := by
  cases n with
  | zero => exact le_rfl
  | succ n => exact inf_le_right

theorem finiteIntersections_nonempty (hirr : IsIrreducible (Set.univ : Set X))
    (B : ℕ → Opens X) (hB : ∀ n, (B n : Set X).Nonempty) (n : ℕ) :
    (finiteIntersections B n : Set X).Nonempty := by
  induction n with
  | zero => exact hB 0
  | succ n ih =>
    obtain ⟨x, hx⟩ := ih
    obtain ⟨y, hy⟩ := hB (n + 1)
    obtain ⟨z, _, hz⟩ := hirr.2 (finiteIntersections B n) (B (n + 1))
      (finiteIntersections B n).isOpen (B (n + 1)).isOpen
      ⟨x, Set.mem_univ _, hx⟩ ⟨y, Set.mem_univ _, hy⟩
    exact ⟨z, hz⟩

/-- The source's enumerated nonempty basis, followed by its initial finite
intersections. The resulting sequence is cofinal among all nonempty opens. -/
theorem exists_decreasing_nonempty_opens [SecondCountableTopology X]
    (hirr : IsIrreducible (Set.univ : Set X)) :
    ∃ U : ℕ → Opens X, Antitone U ∧ (∀ n, (U n : Set X).Nonempty) ∧
      ∀ O : Opens X, (O : Set X).Nonempty → ∃ n, U n ≤ O := by
  classical
  obtain ⟨b, hbcount, hbempty, hbase⟩ := exists_countable_basis X
  have hbne : b.Nonempty := by
    obtain ⟨x, _⟩ := hirr.nonempty
    obtain ⟨V, hV, _, _⟩ := hbase.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    exact ⟨V, hV⟩
  obtain ⟨bseq, hbseq⟩ := hbcount.exists_eq_range hbne
  have hmem (n : ℕ) : bseq n ∈ b := hbseq ▸ Set.mem_range_self n
  let B : ℕ → Opens X := fun n ↦ ⟨bseq n, hbase.isOpen (hmem n)⟩
  have hBne : ∀ n, (B n : Set X).Nonempty := by
    intro n
    apply Set.nonempty_iff_ne_empty.mpr
    intro heq
    exact hbempty (heq ▸ hmem n)
  refine ⟨finiteIntersections B, finiteIntersections_antitone B,
    finiteIntersections_nonempty hirr B hBne, ?_⟩
  intro O hO
  obtain ⟨x, hx⟩ := hO
  obtain ⟨V, hVb, _, hVO⟩ := hbase.exists_subset_of_mem_open hx O.isOpen
  have hVrange : V ∈ Set.range bseq := hbseq.symm ▸ hVb
  obtain ⟨n, hn⟩ := hVrange
  refine ⟨n, (finiteIntersections_le B n).trans ?_⟩
  change bseq n ⊆ (O : Set X)
  exact hn ▸ hVO

end Topological

section Scott

variable {P : Type u} [PartialOrder P]

local instance basisScottTopology : TopologicalSpace P := scottTopology P

/-- The actual `V_n ⊆ K_n ⊆ U_n` choices supplied by the source's local
compactness hypothesis. All required compactness and minimal-point facts
are proved, rather than stored as an assumed conclusion package. -/
theorem exists_compact_neighborhoods (hlc : ScottLocallyCompact P)
    (U : ℕ → ScottOpens P) (hne : ∀ n, (U n : Set P).Nonempty) :
    ∃ (V : ℕ → ScottOpens P) (K : ℕ → Set P),
      (∀ n, (V n : Set P).Nonempty) ∧ (∀ n, (V n : Set P) ⊆ K n) ∧
      (∀ n, K n ⊆ (U n : Set P)) ∧ (∀ n, IsCompact (K n)) ∧
      (∀ n, IsSaturated (K n)) ∧
      ∀ n x, x ∈ K n → ∃ m, m ≤ x ∧ Minimal (· ∈ K n) m := by
  classical
  choose x hx using hne
  choose V K hxV hVK hKU hK hsat using fun n ↦ hlc (U n) (x n) (hx n)
  refine ⟨V, K, fun n ↦ ⟨x n, hxV n⟩, hVK, hKU, hK, hsat, ?_⟩
  intro n x hx
  exact HeZhangClosed.compact_exists_minimal_le (hK n) hx

/-- A point in all source `U_n` is greatest. Scott T0 separation is used
explicitly via the open complement of each principal lower set. -/
theorem greatest_of_mem_all (U : ℕ → ScottOpens P)
    (hcofinal : ∀ O : ScottOpens P, (O : Set P).Nonempty → ∃ n, U n ≤ O)
    {p : P} (hp : ∀ n, p ∈ U n) : ∀ x : P, x ≤ p := by
  intro x
  by_contra hxp
  let O : ScottOpens P := ⟨(Set.Iic p)ᶜ,
    (HeZhangClosed.principal_lower_isClosed p).isOpen_compl⟩
  obtain ⟨n, hn⟩ := hcofinal O ⟨x, hxp⟩
  exact (hn (hp n)) le_rfl

end Scott

end CoreCompactSimplified.HeZhangBasis
