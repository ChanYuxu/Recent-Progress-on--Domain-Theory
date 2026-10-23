import CantorFubini.SourceModel

/-! The structure with empty membership represents precisely an ordinary
nonempty lower ideal in the null-set poset, with no countable-union axiom. -/
set_option autoImplicit false
open Set MeasureTheory
namespace CantorFubini

def IsSourceNullIdeal (S : Set (Set Cantor)) : Prop :=
  S.Nonempty ∧ (∀ N ∈ S, cantorMeasure N = 0) ∧
  (∀ N ∈ S, ∀ L : Set Cantor, cantorMeasure L = 0 → L ⊆ N → L ∈ S) ∧
  (∀ N ∈ S, ∀ L ∈ S, N ∪ L ∈ S)

def nullIdealFromSource (S : Set (Set Cantor)) (h : IsSourceNullIdeal S) :
    NullIdeal cantorMeasure where
  sets := S
  empty_mem := by
    obtain ⟨N, hN⟩ := h.1
    exact h.2.2.1 N hN ∅ measure_empty (empty_subset N)
  null hN := h.2.1 _ hN
  lower hN hLN := h.2.2.1 _ hN _ (measure_mono_null hLN (h.2.1 _ hN)) hLN
  union_mem hN hL := h.2.2.2 _ hN _ hL

theorem nullIdeal_source_iff (S : Set (Set Cantor)) :
    IsSourceNullIdeal S ↔ ∃ I : NullIdeal cantorMeasure, I.sets = S := by
  constructor
  · intro h; exact ⟨nullIdealFromSource S h, rfl⟩
  · rintro ⟨I, rfl⟩
    exact ⟨⟨∅, I.empty_mem⟩, fun _ hN => I.null hN,
      fun _ hN _ _ hLN => I.lower hN hLN, fun _ hN _ hL => I.union_mem hN hL⟩

end CantorFubini
