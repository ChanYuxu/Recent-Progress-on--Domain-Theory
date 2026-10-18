import CoreCompactSimplified.HeZhangBasis
import Mathlib.Order.WellFounded

/-!
The well-foundedness argument in He–Zhang Theorem 4.13 Claim 6, separated
from the Polish presentation. It is later applied to the actual tagged sum
of principal closed sets, using its proved level and point maps.
-/

set_option autoImplicit false

universe u v

namespace CoreCompactSimplified.HeZhangOrder

open Set CoreCompactNonSober

variable {P : Type u} [PartialOrder P]

local instance orderScottTopology : TopologicalSpace P := scottTopology P

/-- A source descending chain would be an increasing chain of dcpo points
meeting successive levels of the decreasing open sequence. Its supremum
would belong to every open, contradicting the actual empty-intersection
assumption. There is no countability assumption on the dcpo itself. -/
theorem wellFounded_level_order (hP : IsDcpo P)
    (U : ℕ → ScottOpens P) (hanti : Antitone U)
    (hempty : ¬ ∃ p : P, ∀ n, p ∈ U n)
    {Z : Type v} (level : Z → ℕ) (point : Z → P)
    (hmem : ∀ z, point z ∈ U (level z)) :
    WellFounded (fun t s : Z ↦ level t = level s + 1 ∧ point s ≤ point t) := by
  apply wellFounded_iff_isEmpty_descending_chain.mpr
  constructor
  rintro ⟨a, ha⟩
  have hlevel (n : ℕ) : level (a n) = level (a 0) + n := by
    induction n with
    | zero => simp
    | succ n ih => rw [(ha n).1, ih]; omega
  have hmono : Monotone (fun n ↦ point (a n)) :=
    monotone_nat_of_le_succ (fun n ↦ (ha n).2)
  have hdir : NonemptyDirected (Set.range (fun n ↦ point (a n))) :=
    ⟨Set.range_nonempty _, hmono.directed_le.directedOn_range⟩
  obtain ⟨s, hs⟩ := hP _ hdir
  apply hempty
  refine ⟨s, ?_⟩
  intro n
  have hpn : point (a n) ∈ U n := by
    apply hanti (show n ≤ level (a n) by rw [hlevel]; omega)
    exact hmem (a n)
  exact ((isOpen_scott_iff _).mp (U n).isOpen).1
    (hs.1 (Set.mem_range_self n)) hpn

end CoreCompactSimplified.HeZhangOrder
