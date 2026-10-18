import CoreCompactNonSober.Localization

/-!
# Pulling capturing families back along coordinate injections

This explicit construction is used twice in Section 4: for block alphabets
in width absorption, and for the even-coordinate alphabet pullback. Lists
on a finite exceptional prefix can be empty; capture is an eventual condition.
-/

set_option autoImplicit false

namespace CoreCompactNonSober.Localization

open Set Cardinal
open Ambient (Coordinate)

theorem extend_point {X Y : Coordinate → Type} [∀ i, Nonempty (X i)]
    {φ : Coordinate → Coordinate} (hφ : Function.Injective φ)
    (e : ∀ j, Y j ↪ X (φ j)) (y : ∀ j, Y j) :
    ∃ x : ∀ i, X i, ∀ j, x (φ j) = e j (y j) := by
  classical
  have hx : ∀ i : Coordinate, ∃ z : X i,
      ∀ j (h : φ j = i), h ▸ e j (y j) = z := by
    intro i
    by_cases hi : ∃ j, φ j = i
    · obtain ⟨j, rfl⟩ := hi
      refine ⟨e j (y j), ?_⟩
      intro k hk
      have hkj : k = j := hφ hk
      subst k
      rfl
    · exact ⟨Classical.choice (inferInstance : Nonempty (X i)),
        fun j hj ↦ False.elim (hi ⟨j, hj⟩)⟩
  choose x hx using hx
  exact ⟨x, fun j ↦ (hx (φ j) j rfl).symm⟩

noncomputable def pullbackList {X Y : Coordinate → Type} [∀ j, Fintype (Y j)]
    {φ : Coordinate → Coordinate} (e : ∀ j, Y j ↪ X (φ j))
    {w : Width} (s : Slalom X w) (j : Coordinate) : Finset (Y j) := by
  classical
  exact Finset.univ.filter (fun y ↦ e j y ∈ s.list (φ j))

theorem pullbackList_card_le {X Y : Coordinate → Type} [∀ j, Fintype (Y j)]
    {φ : Coordinate → Coordinate} (e : ∀ j, Y j ↪ X (φ j))
    {w : Width} (s : Slalom X w) (j : Coordinate) :
    (pullbackList e s j).card ≤ (s.list (φ j)).card := by
  classical
  apply Finset.card_le_card_of_injOn (e j)
  · intro y hy
    exact (Finset.mem_filter.mp hy).2
  · intro y _ z _ hyz
    exact (e j).injective hyz

noncomputable def pullback {X Y : Coordinate → Type} [∀ j, Fintype (Y j)]
    {φ : Coordinate → Coordinate} (e : ∀ j, Y j ↪ X (φ j))
    {w v : Width} (s : Slalom X w) : Slalom Y v := by
  classical
  exact {
    list := fun j ↦ if w (φ j) ≤ v j then pullbackList e s j else ∅
    bound := fun j ↦ by
      split_ifs with hj
      · exact ((pullbackList_card_le e s j).trans (s.bound (φ j))).trans hj
      · simp }

theorem pullback_family {X Y : Coordinate → Type}
    [∀ i, Nonempty (X i)] [∀ j, Fintype (Y j)]
    {φ : Coordinate → Coordinate} (hφ : Function.Injective φ)
    (hφge : ∀ j, j.val ≤ (φ j).val) (e : ∀ j, Y j ↪ X (φ j))
    {w v : Width} (hwv : ∃ N : ℕ, ∀ j, N ≤ j.val → w (φ j) ≤ v j)
    {F : Set (Slalom X w)} (hF : IsCapturing F) :
    ∃ G : Set (Slalom Y v), IsCapturing G ∧ Cardinal.mk G ≤ Cardinal.mk F := by
  classical
  let c : F → Slalom Y v := fun s ↦ pullback e s.val
  refine ⟨Set.range c, ?_, Cardinal.mk_range_le⟩
  intro y
  obtain ⟨x, hx⟩ := extend_point hφ e y
  obtain ⟨s, hs, M, hM⟩ := hF x
  obtain ⟨N, hN⟩ := hwv
  refine ⟨c ⟨s, hs⟩, Set.mem_range_self _, max M N, ?_⟩
  intro j hj
  have hjM : M ≤ j.val := (le_max_left _ _).trans hj
  have hjN : N ≤ j.val := (le_max_right _ _).trans hj
  change y j ∈ if w (φ j) ≤ v j then pullbackList e s j else ∅
  rw [if_pos (hN j hjN)]
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  rw [← hx j]
  exact hM (φ j) (hjM.trans (hφge j))

theorem loc_pullback_le {X Y : Coordinate → Type}
    [∀ i, Nonempty (X i)] [∀ j, Fintype (Y j)]
    {φ : Coordinate → Coordinate} (hφ : Function.Injective φ)
    (hφge : ∀ j, j.val ≤ (φ j).val) (e : ∀ j, Y j ↪ X (φ j))
    {w v : Width} (hw : ∀ i, 0 < w i)
    (hwv : ∃ N : ℕ, ∀ j, N ≤ j.val → w (φ j) ≤ v j) :
    loc Y v ≤ loc X w := by
  obtain ⟨F, hF, hcard⟩ := exists_minimal_family (X := X) hw
  obtain ⟨G, hG, hGF⟩ := pullback_family hφ hφge e hwv hF
  exact (loc_le_family hG).trans (hGF.trans_eq hcard)

end CoreCompactNonSober.Localization
