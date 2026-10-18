import ChainApproximation.FiniteUpper

/-!
# Intrinsic interpolation criterion

Source `thm:extension` and `cor:bounded-joins`. The set `A` in the extension
property is an arbitrary nonempty subset, as in the source, and is not assumed
to be lower. A lower-closure bridge is proved before applying interpolation.
-/

set_option autoImplicit false

universe u

namespace ChainApproximation

open Set

variable {Q : Type u} [PartialOrder Q]

def DirectedExtension (Q : Type u) [PartialOrder Q] : Prop :=
  ∀ A E : Set Q, A.Nonempty → A ⊆ E → IsLowerSet E → FiniteUpper A E →
    ∃ D : Set Q, NonemptyDirected D ∧ IsLowerSet D ∧ A ⊆ D ∧ D ⊆ E

theorem finiteUpper_lowerClosure {A E : Set Q} (h : FiniteUpper A E) :
    FiniteUpper (lowerClosure A : Set Q) E := by
  classical
  intro F hF
  have hex : ∀ x : F, ∃ a ∈ A, x.val ≤ a := fun x ↦ hF x.property
  choose f hf hxf using hex
  let G : Finset Q := F.attach.image f
  have hGA : (G : Set Q) ⊆ A := by
    intro a ha
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp ha
    exact hf x
  obtain ⟨q, hq, hGq⟩ := h G hGA
  refine ⟨q, hq, ?_⟩
  intro x hx
  exact (hxf ⟨x, hx⟩).trans (hGq _ (Finset.mem_image.mpr ⟨⟨x, hx⟩, Finset.mem_attach _ _, rfl⟩))

theorem ClosedBelow.lowerSet_right_nonempty {A E : LowerSet Q} (hAE : ClosedBelow A E) :
    (E : Set Q).Nonempty := by
  apply LowerSet.coe_nonempty.mpr
  intro hE
  exact closedBelow_not_bot A (hE ▸ hAE)

theorem exists_closed_sequence (hi : Interpolates (ClosedBelow (M := LowerSet Q)))
    {A E : LowerSet Q} (hAE : ClosedBelow A E) :
    ∃ f : ℕ → LowerSet Q, f 0 = A ∧
      (∀ n, ClosedBelow (f n) (f (n + 1))) ∧ (∀ n, ClosedBelow (f n) E) := by
  classical
  let step : {B : LowerSet Q // ClosedBelow B E} → {B : LowerSet Q // ClosedBelow B E} :=
    fun B ↦ ⟨Classical.choose (hi B.val E B.property),
      (Classical.choose_spec (hi B.val E B.property)).2⟩
  let s : ℕ → {B : LowerSet Q // ClosedBelow B E} :=
    fun n ↦ Nat.rec ⟨A, hAE⟩ (fun _ B ↦ step B) n
  refine ⟨fun n ↦ (s n).val, rfl, ?_, fun n ↦ (s n).property⟩
  intro n
  exact (Classical.choose_spec (hi (s n).val E (s n).property)).1

/-- Source `thm:extension`, implication from directed extension to
interpolation, including the empty left endpoint case. -/
theorem closed_interpolates_of_extension (hext : DirectedExtension Q) :
    Interpolates (ClosedBelow (M := LowerSet Q)) := by
  classical
  intro A E hAE
  have hE := hAE.lowerSet_right_nonempty
  by_cases hA : (A : Set Q).Nonempty
  · obtain ⟨D, hD, hlD, hAD, hDE⟩ := hext A E hA hAE.le E.lower
      ((closedBelow_iff_finiteUpper A E hE).mp hAE)
    let B : LowerSet Q := ⟨D, hlD⟩
    have hB : (B : Set Q).Nonempty := hD.1
    refine ⟨B, (closedBelow_iff_finiteUpper A B hB).mpr ?_,
      (closedBelow_iff_finiteUpper B E hE).mpr ?_⟩
    · intro F hFA
      exact hD.finite_bound F (hFA.trans hAD)
    · intro F hFB
      obtain ⟨q, hq, hFq⟩ := hD.finite_bound F hFB
      exact ⟨q, hDE hq, hFq⟩
  · obtain ⟨e, he⟩ := hE
    have hAe : A ≤ LowerSet.Iic e := by
      intro a ha
      exact False.elim (hA ⟨a, ha⟩)
    refine ⟨LowerSet.Iic e, (closedBelow_iff_finiteUpper _ _ ⟨e, le_rfl⟩).mpr ?_,
      closedBelow_principal E he⟩
    intro F hF
    exact ⟨e, le_rfl, fun x hx ↦ hAe (hF hx)⟩

theorem extension_of_closed_interpolates (hi : Interpolates (ClosedBelow (M := LowerSet Q))) :
    DirectedExtension Q := by
  classical
  intro A E hA hAE hlE hfinite
  let B : LowerSet Q := ⟨E, hlE⟩
  let A₀ : LowerSet Q := lowerClosure A
  have hE : (B : Set Q).Nonempty := hA.mono hAE
  have hA₀B : ClosedBelow A₀ B :=
    (closedBelow_iff_finiteUpper A₀ B hE).mpr (finiteUpper_lowerClosure hfinite)
  obtain ⟨f, hf0, hfstep, hfB⟩ := exists_closed_sequence hi hA₀B
  have hfmono : Monotone f := monotone_nat_of_le_succ (fun n ↦ (hfstep n).le)
  let D : LowerSet Q := sSup (Set.range f)
  have hAD : A ⊆ (D : Set Q) := by
    intro a ha
    apply LowerSet.mem_sSup_iff.mpr
    refine ⟨f 0, Set.mem_range_self _, ?_⟩
    rw [hf0]
    exact subset_lowerClosure ha
  have hDE : (D : Set Q) ⊆ E := by
    change sSup (Set.range f) ≤ B
    apply sSup_le
    rintro _ ⟨n, rfl⟩
    exact (hfB n).le
  refine ⟨D, ⟨hA.mono hAD, ?_⟩, D.lower, hAD, hDE⟩
  intro a ha b hb
  obtain ⟨_, ⟨n, rfl⟩, han⟩ := LowerSet.mem_sSup_iff.mp ha
  obtain ⟨_, ⟨m, rfl⟩, hbm⟩ := LowerSet.mem_sSup_iff.mp hb
  let k := max n m
  have hak : a ∈ f k := hfmono (le_max_left _ _) han
  have hbk : b ∈ f k := hfmono (le_max_right _ _) hbm
  have hFk : ({a, b} : Set Q) ⊆ f k := by
    intro q hq
    rcases Set.mem_insert_iff.mp hq with rfl | hq
    · exact hak
    · exact Set.mem_singleton_iff.mp hq ▸ hbk
  obtain ⟨q, hq, hFq⟩ := (closedBelow_iff_finiteUpper (f k) (f (k + 1))
    (hfstep k).lowerSet_right_nonempty).mp (hfstep k) {a, b}
      (by simpa only [Finset.coe_pair] using hFk)
  exact ⟨q, LowerSet.mem_sSup_iff.mpr ⟨f (k + 1), Set.mem_range_self _, hq⟩,
    hFq a (Finset.mem_insert_self _ _), hFq b (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))⟩

/-- Source `thm:extension`, both directions with no extra condition on `A`. -/
theorem closed_interpolates_iff_extension :
    Interpolates (ClosedBelow (M := LowerSet Q)) ↔ DirectedExtension Q :=
  ⟨extension_of_closed_interpolates, closed_interpolates_of_extension⟩

def HasBoundedFiniteJoins (Q : Type u) [PartialOrder Q] : Prop :=
  ∀ F : Finset Q, F.Nonempty → BddAbove (F : Set Q) → ∃ s, IsLUB (F : Set Q) s

theorem extension_of_bounded_finite_joins (hjoins : HasBoundedFiniteJoins Q) : DirectedExtension Q := by
  classical
  intro A E hA hAE hlE hfinite
  let D : Set Q := {p | ∃ F : Finset Q, F.Nonempty ∧ (F : Set Q) ⊆ A ∧
    ∃ s, IsLUB (F : Set Q) s ∧ p ≤ s}
  have hAD : A ⊆ D := by
    intro a ha
    exact ⟨{a}, Finset.singleton_nonempty a, by simpa using ha, a, by simp, le_rfl⟩
  have hDE : D ⊆ E := by
    rintro p ⟨F, _, hFA, s, hs, hps⟩
    obtain ⟨q, hq, hFq⟩ := hfinite F hFA
    exact hlE (hps.trans (hs.2 hFq)) hq
  refine ⟨D, ⟨hA.mono hAD, ?_⟩, ?_, hAD, hDE⟩
  · rintro p ⟨F, hF, hFA, s, hs, hps⟩ q ⟨G, hG, hGA, t, ht, hqt⟩
    have hH : (F ∪ G : Finset Q).Nonempty := hF.mono Finset.subset_union_left
    have hHA : ((F ∪ G : Finset Q) : Set Q) ⊆ A := by
      simpa only [Finset.coe_union, Set.union_subset_iff] using And.intro hFA hGA
    obtain ⟨r, _, hHr⟩ := hfinite (F ∪ G) hHA
    obtain ⟨v, hv⟩ := hjoins (F ∪ G) hH ⟨r, hHr⟩
    refine ⟨v, ⟨F ∪ G, hH, hHA, v, hv, le_rfl⟩, ?_, ?_⟩
    · exact hps.trans (hs.2 (fun x hx ↦ hv.1 (Finset.mem_union_left G hx)))
    · exact hqt.trans (ht.2 (fun x hx ↦ hv.1 (Finset.mem_union_right F hx)))
  · rintro p q hpq ⟨F, hF, hFA, s, hs, hqs⟩
    exact ⟨F, hF, hFA, s, hs, hpq.trans hqs⟩

/-- Source `cor:bounded-joins`. -/
theorem closed_interpolates_of_bounded_finite_joins (hjoins : HasBoundedFiniteJoins Q) :
    Interpolates (ClosedBelow (M := LowerSet Q)) :=
  closed_interpolates_of_extension (extension_of_bounded_finite_joins hjoins)

end ChainApproximation
