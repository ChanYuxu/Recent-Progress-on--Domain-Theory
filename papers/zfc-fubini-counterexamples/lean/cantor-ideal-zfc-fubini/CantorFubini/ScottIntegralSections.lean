import CantorFubini.CentralApproximation
import CantorFubini.SourceIntegralBridge

/-! New section-integration topology lemmas. Scott lower semicontinuity in
one coordinate suffices to preserve arbitrary directed limits after
integration in the other coordinate. No product-topology identification or
centrality hypothesis occurs in these lemmas. -/

set_option autoImplicit false
open Set Topology TopologicalSpace MeasureTheory
open scoped ENNReal
universe u v w
namespace CantorFubini

section ScottSections
variable {D : Type u} [PartialOrder D]

/-- Strict-level Scott openness implies monotonicity. -/
theorem scott_lsc_monotone {g : D → ℝ≥0∞}
    (hg : IsVLSC (fun d : WithScott D => g (WithScott.ofScott d))) : Monotone g := by
  intro d d' hdd'
  apply le_of_forall_lt
  intro a ha
  exact ((scott_isOpen_iff {x : D | a < g x}).mp (hg a)).1 hdd' ha

/-- Strict-level Scott openness gives the exact pointwise value at every
existing nonempty directed least upper bound. -/
theorem scott_lsc_iSup {g : D → ℝ≥0∞}
    (hg : IsVLSC (fun d : WithScott D => g (WithScott.ofScott d)))
    {A : Set D} (hn : A.Nonempty) (hd : DirectedOn (· ≤ ·) A)
    {d : D} (hl : IsLUB A d) : (⨆ t : A, g t.val) = g d := by
  apply le_antisymm
  · exact iSup_le (fun t => scott_lsc_monotone hg (hl.1 t.property))
  · apply le_of_forall_lt
    intro a ha
    obtain ⟨t, ht, hat⟩ :=
      ((scott_isOpen_iff {x : D | a < g x}).mp (hg a)).2 hn hd hl ha
    exact hat.trans_le (le_iSup_of_le (⟨t, ht⟩ : A) le_rfl)

variable {Y : Type v} [TopologicalSpace Y]

/-- Integrating LSC sections preserves Scott lower semicontinuity in the
parameter, for an arbitrary continuous valuation on the other space. -/
theorem scott_integral_section_isVLSC (ρ : Valuation Y) (k : D → Y → ℝ≥0∞)
    (hkD : ∀ y, IsVLSC (fun d : WithScott D => k (WithScott.ofScott d) y))
    (hkY : ∀ d, IsVLSC (k d)) :
    IsVLSC (fun d : WithScott D => vIntegral ρ (k (WithScott.ofScott d))) := by
  intro a
  apply (scott_isOpen_iff {d : D | a < vIntegral ρ (k d)}).mpr
  constructor
  · intro d d' hdd' hd
    exact hd.trans_le (vIntegral_mono ρ (fun y =>
      scott_lsc_monotone (g := fun d => k d y) (hkD y) hdd'))
  · intro A hn hd d hl had
    letI : Nonempty A := hn.to_subtype
    have he : k d = fun y => ⨆ t : A, k t.val y := by
      funext y
      exact (scott_lsc_iSup (g := fun d => k d y) (hkD y) hn hd hl).symm
    have hdir : Directed (· ≤ ·) (fun t : A => k t.val) := by
      intro s t
      obtain ⟨r, hr, hsr, htr⟩ := hd s.val s.property t.val t.property
      exact ⟨⟨r, hr⟩,
        (fun y => scott_lsc_monotone (g := fun d => k d y) (hkD y) hsr),
        (fun y => scott_lsc_monotone (g := fun d => k d y) (hkD y) htr)⟩
    have hi : vIntegral ρ (k d) = ⨆ t : A, vIntegral ρ (k t.val) := by
      rw [he]
      exact vIntegral_iSup_directed ρ (fun t : A => k t.val) (fun t => hkY t.val) hdir
    change a < vIntegral ρ (k d) at had
    rw [hi] at had
    obtain ⟨t, ht⟩ := lt_iSup_iff.mp had
    exact ⟨t.val, t.property, ht⟩

end ScottSections

section UnitSections
variable {D : Type u} [PartialOrder D] {E : Type v} [PartialOrder E]

/-- The actual ENNReal encoding of every UnitInterval Scott section is LSC. -/
theorem unit_first_section_isVLSC (h : D × E → UnitInterval) (hh : ScottContinuous h)
    (e : E) : IsVLSC (fun d : WithScott D =>
      ENNReal.ofReal (h (WithScott.ofScott d, e)).val) := by
  exact isVLSC_ofReal (unit_scott_isRealLSC
    ((ScottContinuous.id.prodMk (ScottContinuous.const e)).comp hh))

theorem unit_second_section_isVLSC (h : D × E → UnitInterval) (hh : ScottContinuous h)
    (d : D) : IsVLSC (fun e : WithScott E =>
      ENNReal.ofReal (h (d, WithScott.ofScott e)).val) := by
  exact isVLSC_ofReal (unit_scott_isRealLSC
    (((ScottContinuous.const d).prodMk ScottContinuous.id).comp hh))

/-- Arbitrary partner integration of a Scott test has an LSC partial integral. -/
theorem unit_partial_vIntegral_isVLSC (h : D × E → UnitInterval)
    (hh : ScottContinuous h) (ρ : DValuation E) :
    IsVLSC (fun d : WithScott D => vIntegral ρ (fun e : WithScott E =>
      ENNReal.ofReal (h (WithScott.ofScott d, WithScott.ofScott e)).val)) := by
  exact scott_integral_section_isVLSC ρ
    (fun d e => ENNReal.ofReal (h (d, WithScott.ofScott e)).val)
    (fun e => unit_first_section_isVLSC h hh (WithScott.ofScott e))
    (unit_second_section_isVLSC h hh)

end UnitSections
end CantorFubini
