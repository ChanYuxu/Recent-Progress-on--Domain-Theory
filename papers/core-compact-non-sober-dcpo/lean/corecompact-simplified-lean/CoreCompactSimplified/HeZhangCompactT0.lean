import CoreCompactNonSober.TopologicalDefinitions
import Mathlib.Order.Zorn
import Mathlib.Topology.Separation.Basic

/-!
He–Zhang Lemma 4.3 for arbitrary T0 spaces, not merely Scott spaces.
The canonical order is mathlib's specializationOrder, with x ≤ y exactly
when x belongs to the closure of {y}.  The compactness/Zorn argument is
adapted from HeZhangClosed.lean (origin recorded in the audit note).
-/

set_option autoImplicit false

universe u

namespace CoreCompactSimplified.HeZhangCompactT0

open Set CoreCompactNonSober
open scoped Topology

variable {X : Type u} [TopologicalSpace X] [T0Space X]

local instance sourceSpecializationOrder : PartialOrder X := specializationOrder X

theorem specialization_le_iff (x y : X) : x ≤ y ↔ x ∈ closure ({y} : Set X) :=
  specializes_iff_mem_closure

theorem specialization_Iic_eq_closure (y : X) : Set.Iic y = closure ({y} : Set X) := by
  ext x
  exact specialization_le_iff x y

theorem open_isUpperSet {U : Set X} (hU : IsOpen U) : IsUpperSet U := by
  intro x y hxy hx
  exact (show y ⤳ x from hxy).mem_open hU hx

theorem saturated_isUpperSet {K : Set X} (hK : IsSaturated K) : IsUpperSet K := by
  intro x y hxy hx
  rw [hK] at hx ⊢
  apply Set.mem_sInter.mpr
  intro U hU
  exact open_isUpperSet hU.1 hxy (Set.mem_sInter.mp hx U hU)

/-- The source's upper-closure definition of saturation agrees with the
intersection-of-open-neighborhoods definition used by the project. -/
theorem saturated_iff_upperHull (K : Set X) : IsSaturated K ↔ upperHull K = K := by
  constructor
  · intro hK
    apply Set.Subset.antisymm
    · rintro y ⟨x, hx, hxy⟩
      exact saturated_isUpperSet hK hxy hx
    · intro x hx
      exact ⟨x, hx, le_rfl⟩
  · intro hK
    apply Set.Subset.antisymm
    · intro x hx
      exact Set.mem_sInter.mpr (fun _ hU ↦ hU.2 hx)
    · intro y hy
      by_contra hynot
      let U : Set X := (closure ({y} : Set X))ᶜ
      have hUopen : IsOpen U := isClosed_closure.isOpen_compl
      have hKU : K ⊆ U := by
        intro x hx hxy
        apply hynot
        rw [← hK]
        exact ⟨x, hx, (specialization_le_iff x y).mpr hxy⟩
      have hyU := Set.mem_sInter.mp hy U ⟨hUopen, hKU⟩
      exact hyU (subset_closure (Set.mem_singleton y))

private theorem principal_lower_isClosed (x : X) : IsClosed (Set.Iic x) := by
  rw [specialization_Iic_eq_closure]
  exact isClosed_closure

/-- Compactness supplies a minimal point below every point, with no dcpo or
Hausdorff assumption on the ambient T0 space. -/
theorem compact_exists_minimal_le {K : Set X} (hK : IsCompact K)
    {x : X} (hx : x ∈ K) : ∃ m, m ≤ x ∧ Minimal (· ∈ K) m := by
  classical
  apply @zorn_le_nonempty₀ Xᵒᵈ _ K ?_ x hx
  intro c hcK hc y hy
  have hfinite : ∀ F : Finset c, ∃ z ∈ c,
      ∀ a ∈ F, OrderDual.ofDual z ≤ OrderDual.ofDual a.val := by
    intro F
    induction F using Finset.induction_on with
    | empty => exact ⟨y, hy, by simp⟩
    | @insert a F ha ih =>
      obtain ⟨z, hz, hF⟩ := ih
      obtain ⟨w, hw, haw, hzw⟩ := hc.directedOn a.val a.property z hz
      refine ⟨w, hw, ?_⟩
      intro b hb
      rcases Finset.mem_insert.mp hb with rfl | hb
      · exact haw
      · have hwz : OrderDual.ofDual w ≤ OrderDual.ofDual z := hzw
        exact hwz.trans (hF b hb)
  obtain ⟨m, hmK, hm⟩ := hK.inter_iInter_nonempty
    (fun a : c ↦ Set.Iic (OrderDual.ofDual a.val))
    (fun a ↦ principal_lower_isClosed (OrderDual.ofDual a.val)) (by
      intro F
      obtain ⟨z, hz, hF⟩ := hfinite F
      exact ⟨z, hcK hz, Set.mem_iInter.mpr (fun a ↦
        Set.mem_iInter.mpr (fun ha ↦ hF a ha))⟩)
  exact ⟨m, hmK, fun a ha ↦ Set.mem_iInter.mp hm ⟨a, ha⟩⟩

def minimalPoints (K : Set X) : Set X := {m | Minimal (· ∈ K) m}

theorem compact_minimalPoints {K : Set X} (hK : IsCompact K) :
    IsCompact (minimalPoints K) := by
  rw [isCompact_iff_finite_subcover]
  intro ι O hO hcover
  have hKcover : K ⊆ ⋃ i, O i := by
    intro x hx
    obtain ⟨m, hmx, hm⟩ := compact_exists_minimal_le hK hx
    obtain ⟨i, hmi⟩ := Set.mem_iUnion.mp (hcover hm)
    exact Set.mem_iUnion.mpr ⟨i, open_isUpperSet (hO i) hmx hmi⟩
  obtain ⟨F, hF⟩ := hK.elim_finite_subcover O hO hKcover
  have hsubset : minimalPoints K ⊆ K := fun _ hm ↦ hm.1
  exact ⟨F, hsubset.trans hF⟩

/-- Exact He–Zhang Lemma 4.3: arbitrary T0 topology, its specialization order,
and a compact saturated set.  No ambient dcpo assumption is introduced. -/
theorem compact_saturated_minimal (K : Set X) (hK : IsCompact K)
    (hsat : IsSaturated K) :
    K = upperHull (minimalPoints K) ∧ IsCompact (minimalPoints K) := by
  constructor
  · apply Set.Subset.antisymm
    · intro x hx
      obtain ⟨m, hmx, hm⟩ := compact_exists_minimal_le hK hx
      exact ⟨m, hm, hmx⟩
    · rintro x ⟨m, hm, hmx⟩
      exact saturated_isUpperSet hsat hmx hm.1
  · exact compact_minimalPoints hK

end CoreCompactSimplified.HeZhangCompactT0
