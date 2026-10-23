import ZFCFubini.TopologicalFubiniSections

/-! The integral-defined valuation on the ordinary product and uniqueness
from open rectangles. All continuity statements use arbitrary directed sets. -/

set_option autoImplicit false
open Set Topology TopologicalSpace MeasureTheory
open scoped ENNReal NNReal Classical
universe u v w
namespace ZFCFubini
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

noncomputable def topologicalProductValuation (μ : Valuation X) (hμ : μ.Subprobability)
    (ν : Valuation Y) : Valuation (X × Y) where
  mass W := choquetIntegral μ (fun x => ν (openSection W x))
  strict := by
    change choquetIntegral μ (fun _ => ν ⊥) = 0
    simp only [ν.strict, choquetIntegral_zero]
  modular U V := by
    have he : (fun x => ν (openSection U x)) + (fun x => ν (openSection V x)) =
        (fun x => ν (openSection (U ⊔ V) x)) +
          (fun x => ν (openSection (U ⊓ V) x)) := by
      funext x
      simp only [Pi.add_apply, openSection_sup, openSection_inf]
      exact ν.modular _ _
    rw [← choquetIntegral_add μ hμ (valuation_openSection_isLSC ν U)
      (valuation_openSection_isLSC ν V), he,
      choquetIntegral_add μ hμ (valuation_openSection_isLSC ν (U ⊔ V))
        (valuation_openSection_isLSC ν (U ⊓ V))]
  continuous := by
    intro A hn hd p hp
    letI : Nonempty A := hn.to_subtype
    have hAd : Directed (· ≤ ·) (fun a : A => (a : Opens (X × Y))) := by
      intro a b
      obtain ⟨c, hc, hac, hbc⟩ := hd a a.property b b.property
      exact ⟨⟨c, hc⟩, hac, hbc⟩
    have hpSup : p = ⨆ a : A, (a : Opens (X × Y)) := by
      apply hp.unique
      simpa only [Subtype.range_coe_subtype, setOf_mem_eq] using
        (isLUB_iSup (f := fun a : A => (a : Opens (X × Y))))
    have he (x : X) : ν (openSection p x) = ⨆ a : A, ν (openSection (a : Opens (X × Y)) x) := by
      rw [hpSup, openSection_iSup, ν.map_iSup]
      intro a b
      obtain ⟨c, hac, hbc⟩ := hAd a b
      exact ⟨c, openSection_mono hac x, openSection_mono hbc x⟩
    have hfd : Directed (· ≤ ·) (fun a : A => fun x => ν (openSection (a : Opens (X × Y)) x)) := by
      intro a b
      obtain ⟨c, hac, hbc⟩ := hAd a b
      exact ⟨c, fun x => ν.mono (openSection_mono hac x),
        fun x => ν.mono (openSection_mono hbc x)⟩
    have hi : choquetIntegral μ (fun x => ν (openSection p x)) =
        ⨆ a : A, choquetIntegral μ (fun x => ν (openSection (a : Opens (X × Y)) x)) := by
      simp_rw [he]
      exact choquetIntegral_iSup μ _
        (fun a => valuation_openSection_isLSC ν (a : Opens (X × Y))) hfd
    change IsLUB ((fun W => choquetIntegral μ (fun x => ν (openSection W x))) '' A)
      (choquetIntegral μ (fun x => ν (openSection p x)))
    rw [hi]
    constructor
    · rintro _ ⟨a, ha, rfl⟩
      exact le_iSup (fun a : A => choquetIntegral μ
        (fun x => ν (openSection (a : Opens (X × Y)) x))) ⟨a, ha⟩
    · intro b hb
      exact iSup_le fun a => hb ⟨a, a.property, rfl⟩

@[simp] theorem topologicalProductValuation_apply (μ : Valuation X) (hμ : μ.Subprobability)
    (ν : Valuation Y) (W : Opens (X × Y)) :
    topologicalProductValuation μ hμ ν W = choquetIntegral μ (fun x => ν (openSection W x)) := rfl

theorem topologicalProductValuation_subprobability (μ : Valuation X) (hμ : μ.Subprobability)
    (ν : Valuation Y) (hν : ν.Subprobability) :
    (topologicalProductValuation μ hμ ν).Subprobability :=
  choquetIntegral_le_one μ hμ (fun x => hν.mass_le_one _)

theorem openSection_rectangle (U : Opens X) (V : Opens Y) (x : X) :
    openSection (openRectangle (U, V)) x = if x ∈ U then V else ⊥ := by
  apply Opens.ext
  ext y
  by_cases hx : x ∈ U <;> simp [openSection, openRectangle, hx]

theorem topologicalProductValuation_rectangle (μ : Valuation X) (hμ : μ.Subprobability)
    (ν : Valuation Y) (hν : ν.Subprobability) (U : Opens X) (V : Opens Y) :
    topologicalProductValuation μ hμ ν (openRectangle (U, V)) = μ U * ν V := by
  have hc : ν V ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top (hν.mass_le_one V)
  let c : ℝ≥0 := (ν V).toNNReal
  have hcc : (c : ℝ≥0∞) = ν V := ENNReal.coe_toNNReal hc
  have he : (fun x => ν (openSection (openRectangle (U, V)) x)) =
      (U : Set X).indicator (fun _ => (c : ℝ≥0∞)) := by
    funext x
    rw [openSection_rectangle]
    by_cases hx : x ∈ U <;> simp [hx, ν.strict, hcc]
  rw [topologicalProductValuation_apply, he, choquetIntegral_indicator_nnreal, hcc, mul_comm]

theorem openRectangle_inf (a b : Opens X × Opens Y) :
    openRectangle a ⊓ openRectangle b = openRectangle (a.1 ⊓ b.1, a.2 ⊓ b.2) := by
  apply Opens.ext
  ext z
  change (z.1 ∈ a.1 ∧ z.2 ∈ a.2) ∧ (z.1 ∈ b.1 ∧ z.2 ∈ b.2) ↔
    (z.1 ∈ a.1 ∧ z.1 ∈ b.1) ∧ (z.2 ∈ a.2 ∧ z.2 ∈ b.2)
  tauto

theorem finiteRectangleUnion_inf (F : Finset (Opens X × Opens Y)) (a : Opens X × Opens Y) :
    F.sup openRectangle ⊓ openRectangle a =
      (F.image (fun b => (b.1 ⊓ a.1, b.2 ⊓ a.2))).sup openRectangle := by
  induction F using Finset.induction_on with
  | empty => simp
  | @insert b F hb ih =>
      simp only [Finset.sup_insert, Finset.image_insert, inf_sup_right, openRectangle_inf]
      rw [ih]

/-- A genuine extension theorem for subprobability valuations on the ordinary
topological product. The proof is finite modularity followed by directed
finite-subunion continuity, not a Borel measure extension. -/
theorem valuation_ext_rectangles (μ ν : Valuation (X × Y))
    (hμ : μ.Subprobability) (hν : ν.Subprobability)
    (hrect : ∀ (U : Opens X) (V : Opens Y),
      μ (openRectangle (U, V)) = ν (openRectangle (U, V))) : μ = ν := by
  have hfinite (n : ℕ) : ∀ F : Finset (Opens X × Opens Y), F.card = n →
      μ (F.sup openRectangle) = ν (F.sup openRectangle) := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro F hn
      by_cases hF : F = ∅
      · subst F
        simp [μ.strict, ν.strict]
      obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.mpr hF
      let R := F.erase a
      let S := R.image (fun b => (b.1 ⊓ a.1, b.2 ⊓ a.2))
      have hRn : R.card < n := by simpa only [R, ← hn] using Finset.card_erase_lt_of_mem ha
      have hSn : S.card < n := Finset.card_image_le.trans_lt hRn
      have hR := ih R.card hRn R rfl
      have hS := ih S.card hSn S rfl
      have hFsup : F.sup openRectangle = openRectangle a ⊔ R.sup openRectangle := by
        conv_lhs => rw [← Finset.insert_erase ha]
        exact Finset.sup_insert
      have hmin : openRectangle a ⊓ R.sup openRectangle = S.sup openRectangle := by
        rw [inf_comm, finiteRectangleUnion_inf]
      have hm := μ.modular (openRectangle a) (R.sup openRectangle)
      rw [hrect a.1 a.2, hR, ← hFsup, hmin, hS] at hm
      have hn' := ν.modular (openRectangle a) (R.sup openRectangle)
      rw [← hFsup, hmin] at hn'
      apply (ENNReal.add_left_inj (ne_top_of_le_ne_top ENNReal.one_ne_top
        (hν.mass_le_one (S.sup openRectangle)))).mp
      exact hm.symm.trans hn'
  apply Valuation.ext
  intro W
  have hfin (F : Finset (RectangleIndex W)) :
      μ (rectangleFiniteUnion W F) = ν (rectangleFiniteUnion W F) := by
    have he := hfinite (F.image Subtype.val).card (F.image Subtype.val) rfl
    simpa only [rectangleFiniteUnion, Finset.sup_image, Function.comp_def] using he
  rw [← iSup_rectangleFiniteUnion W, μ.map_iSup _ (rectangleFiniteUnion_directed W),
    ν.map_iSup _ (rectangleFiniteUnion_directed W)]
  exact iSup_congr hfin

end ZFCFubini
