import CoreCompactNonSober.Localization

/-!
# Finite perturbations of localization data

Source: the paragraph following `eq:lambda`.  Replacing finitely many
nonempty finite coordinate alphabets, or finitely many positive widths,
does not change the localization cardinal.

We use the equivalent tail formulation: from some cutoff onward the
coordinate alphabets are equivalent and the widths agree.  The exceptional
initial segment is filled by arbitrary singletons.  Since capture is an
eventual condition, those choices do not affect capture.
-/

set_option autoImplicit false

namespace CoreCompactNonSober.Localization

open Set Cardinal
open Ambient (Coordinate)

private noncomputable def transportTailSlalom
    {X Y : Coordinate → Type}
    [∀ j, Nonempty (Y j)] {w v : Width} (hw : ∀ j, 0 < v j)
    (N : ℕ) (e : ∀ j, N ≤ j.val → X j ≃ Y j)
    (hwidth : ∀ j, N ≤ j.val → w j = v j)
    (s : Slalom X w) : Slalom Y v where
  list j := if hj : N ≤ j.val then (s.list j).map (e j hj).toEmbedding
    else {Classical.choice (inferInstance : Nonempty (Y j))}
  bound j := by
    classical
    split_ifs with hj
    · simpa only [Finset.card_map, hwidth j hj] using s.bound j
    · simpa only [Finset.card_singleton] using hw j

private noncomputable def pullTailPoint
    {X Y : Coordinate → Type} [∀ j, Nonempty (X j)]
    (N : ℕ) (e : ∀ j, N ≤ j.val → X j ≃ Y j)
    (y : ∀ j, Y j) : ∀ j, X j := fun j ↦
  if hj : N ≤ j.val then (e j hj).symm (y j)
  else Classical.choice (inferInstance : Nonempty (X j))

private theorem transportTailSlalom_captures
    {X Y : Coordinate → Type}
    [∀ j, Nonempty (X j)] [∀ j, Nonempty (Y j)]
    {w v : Width} (hv : ∀ j, 0 < v j)
    (N : ℕ) (e : ∀ j, N ≤ j.val → X j ≃ Y j)
    (hwidth : ∀ j, N ≤ j.val → w j = v j)
    (s : Slalom X w) (y : ∀ j, Y j)
    (hs : Captures s (pullTailPoint N e y)) :
    Captures (transportTailSlalom hv N e hwidth s) y := by
  classical
  obtain ⟨M, hM⟩ := hs
  refine ⟨max M N, fun j hj ↦ ?_⟩
  have hjM : M ≤ j.val := (le_max_left M N).trans hj
  have hjN : N ≤ j.val := (le_max_right M N).trans hj
  have hmem := hM j hjM
  change y j ∈ if h : N ≤ j.val then
      (s.list j).map (e j h).toEmbedding else {_}
  rw [dif_pos hjN, Finset.mem_map]
  refine ⟨(pullTailPoint N e y) j, hmem, ?_⟩
  rw [show pullTailPoint N e y j = (e j hjN).symm (y j) by
    simp only [pullTailPoint, dif_pos hjN]]
  change (e j hjN) ((e j hjN).symm (y j)) = y j
  exact (e j hjN).apply_symm_apply (y j)

/-- Eventual coordinate equivalences and eventual equality of positive
widths induce one inequality between localization cardinals.  The finitely
many exceptional coordinates are filled by arbitrary singletons. -/
theorem loc_le_of_eventually_equiv_width
    {X Y : Coordinate → Type}
    [∀ j, Nonempty (X j)] [∀ j, Nonempty (Y j)]
    {w v : Width} (hw : ∀ j, 0 < w j) (hv : ∀ j, 0 < v j)
    (N : ℕ) (e : ∀ j, N ≤ j.val → X j ≃ Y j)
    (hwidth : ∀ j, N ≤ j.val → w j = v j) :
    loc Y v ≤ loc X w := by
  classical
  obtain ⟨F, hF, hcardF⟩ := exists_minimal_family (X := X) hw
  let t : F → Slalom Y v := fun s ↦
    transportTailSlalom hv N e hwidth s.val
  have hcapt : IsCapturing (Set.range t) := by
    intro y
    obtain ⟨s, hsF, hs⟩ := hF (pullTailPoint N e y)
    exact ⟨t ⟨s, hsF⟩, Set.mem_range_self _,
      transportTailSlalom_captures hv N e hwidth s y hs⟩
  exact (loc_le_family hcapt).trans (Cardinal.mk_range_le.trans_eq hcardF)

/-- **Finite perturbation invariance.**  Suppose all coordinate alphabets
are nonempty finite sets and all widths are positive.  If, from some cutoff
`N` onward, the alphabets are coordinatewise equivalent and the widths
agree, then the two localization dominating cardinals are equal.

This tail formulation covers arbitrary finite changes: every finite set of
exceptional natural-number coordinates is contained in an initial segment.
The proof explicitly transports a minimum capturing family in both
directions and uses only the eventual nature of `Captures`. -/
theorem loc_eq_of_eventually_equiv_width
    {X Y : Coordinate → Type}
    [∀ j, Fintype (X j)] [∀ j, Fintype (Y j)]
    [∀ j, Nonempty (X j)] [∀ j, Nonempty (Y j)]
    {w v : Width} (hw : ∀ j, 0 < w j) (hv : ∀ j, 0 < v j)
    (N : ℕ) (e : ∀ j, N ≤ j.val → X j ≃ Y j)
    (hwidth : ∀ j, N ≤ j.val → w j = v j) :
    loc X w = loc Y v := by
  apply le_antisymm
  · exact loc_le_of_eventually_equiv_width hv hw N
      (fun j hj ↦ (e j hj).symm) (fun j hj ↦ (hwidth j hj).symm)
  · exact loc_le_of_eventually_equiv_width hw hv N e hwidth

end CoreCompactNonSober.Localization
