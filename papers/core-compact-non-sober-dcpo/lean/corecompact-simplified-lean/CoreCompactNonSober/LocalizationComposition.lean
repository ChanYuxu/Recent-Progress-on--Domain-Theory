import CoreCompactNonSober.Localization
import Mathlib.Data.Fintype.EquivFin

/-! # The composition inequality for localization cardinals

Source: `lem:composition`. Coordinate lists are enumerated and padded;
empty lists are padded using the nonemptiness of the original alphabet.
-/

set_option autoImplicit false

namespace CoreCompactNonSober.Localization

open Set Cardinal
open Ambient (Coordinate)

noncomputable def enumeration {X : Coordinate → Type} [∀ j, Nonempty (X j)]
    {g : Width} (s : Slalom X g) (j : Coordinate) (k : Fin (g j)) : X j :=
  if hk : k.val < (s.list j).card then
    ((s.list j).equivFin.symm ⟨k.val, hk⟩).val
  else Classical.choice (inferInstance : Nonempty (X j))

theorem enumeration_covers {X : Coordinate → Type} [∀ j, Nonempty (X j)]
    {g : Width} (s : Slalom X g) (j : Coordinate) (z : X j) (hz : z ∈ s.list j) :
    ∃ k : Fin (g j), enumeration s j k = z := by
  let k₀ := (s.list j).equivFin ⟨z, hz⟩
  refine ⟨⟨k₀.val, k₀.isLt.trans_le (s.bound j)⟩, ?_⟩
  unfold enumeration
  rw [dif_pos k₀.isLt]
  exact congrArg Subtype.val ((s.list j).equivFin.symm_apply_apply ⟨z, hz⟩)

noncomputable def compose {X : Coordinate → Type} [∀ j, Nonempty (X j)]
    {g h : Width} (s : Slalom X g) (t : Slalom (fun j ↦ Fin (g j)) h) :
    Slalom X h := by
  classical
  exact {
    list := fun j ↦ (t.list j).image (enumeration s j)
    bound := fun j ↦ Finset.card_image_le.trans (t.bound j) }

theorem composition {X : Coordinate → Type} [∀ j, Nonempty (X j)]
    {g h : Width} (hg : ∀ j, 0 < g j) (hh : ∀ j, 0 < h j) :
    loc X h ≤ loc X g * loc (fun j ↦ Fin (g j)) h := by
  classical
  obtain ⟨F, hF, hcardF⟩ := exists_minimal_family (X := X) hg
  obtain ⟨G, hG, hcardG⟩ := exists_minimal_family (X := fun j ↦ Fin (g j)) hh
  let c : F × G → Slalom X h := fun st ↦ compose st.1.val st.2.val
  have hcapt : IsCapturing (Set.range c) := by
    intro x
    obtain ⟨s, hsF, N, hNs⟩ := hF x
    have hr : ∀ j : Coordinate, ∃ r : Fin (g j),
        x j ∈ s.list j → enumeration s j r = x j := by
      intro j
      by_cases hx : x j ∈ s.list j
      · obtain ⟨r, hr⟩ := enumeration_covers s j (x j) hx
        exact ⟨r, fun _ ↦ hr⟩
      · exact ⟨⟨0, hg j⟩, fun h ↦ False.elim (hx h)⟩
    choose r hr using hr
    obtain ⟨t, htG, M, hMt⟩ := hG r
    refine ⟨c (⟨s, hsF⟩, ⟨t, htG⟩), Set.mem_range_self _, max N M, ?_⟩
    intro j hj
    change x j ∈ (t.list j).image (enumeration s j)
    exact Finset.mem_image.mpr ⟨r j, hMt j ((le_max_right _ _).trans hj),
      hr j (hNs j ((le_max_left _ _).trans hj))⟩
  calc
    loc X h ≤ Cardinal.mk (Set.range c) := loc_le_family hcapt
    _ ≤ Cardinal.mk (F × G) := Cardinal.mk_range_le
    _ = loc X g * loc (fun j ↦ Fin (g j)) h := by
      rw [Cardinal.mk_prod, hcardF, hcardG]
      simp

end CoreCompactNonSober.Localization
