import ChainApproximation.Obstruction

/-!
# Recovery of ordinary way-below and continuity

Source `lem:square`, `thm:main`, and the equivalence in `cor:strong`.
Source SHA-256: fb98ea2b95418ee17dcebaee23c905a089a32ceb56a7a8d2217ec3806d80f8d1.
The only mathematical hypotheses of the main result are directed completeness
and the source's chain-generated approximation sections.
-/

set_option autoImplicit false

universe u

namespace ChainApproximation

open Set

variable {P : Type u} [PartialOrder P]

def Square (a b : P) : Prop := RelComp ChainBelow ChainBelow a b

def squareSection (b : P) : Set P := {a | Square a b}

theorem Square.le {a b : P} (hab : Square a b) : a ≤ b := by
  obtain ⟨c, hac, hcb⟩ := hab
  exact hac.le.trans hcb.le

theorem Square.chainBelow {a b : P} (hab : Square a b) : ChainBelow a b := by
  obtain ⟨c, hac, hcb⟩ := hab
  exact hac.trans hcb

theorem Square.mono {a' a b b' : P} (haa : a' ≤ a) (hab : Square a b)
    (hbb : b ≤ b') : Square a' b' := by
  obtain ⟨c, hac, hcb⟩ := hab
  exact ⟨c, hac.mono haa le_rfl, hcb.mono le_rfl hbb⟩

theorem square_auxiliary : IsAuxiliary (Square (P := P)) :=
  ⟨fun _ _ h ↦ h.le, fun _ _ _ _ haa hab hbb ↦ hab.mono haa hbb⟩

theorem square_to_cube (hdcpo : IsDcpo P) (hP : IsChainContinuous P)
    {a d : P} (had : Square a d) :
    ∃ b c, ChainBelow a b ∧ ChainBelow b c ∧ ChainBelow c d := by
  obtain ⟨b, hab, hbd⟩ := had
  rcases adjacent_interpolates hdcpo hP hab hbd with h | h
  · obtain ⟨c, hac, hcb⟩ := h
    exact ⟨c, b, hac, hcb, hbd⟩
  · obtain ⟨c, hbc, hcd⟩ := h
    exact ⟨b, c, hab, hbc, hcd⟩

theorem square_interpolates (hdcpo : IsDcpo P) (hP : IsChainContinuous P) :
    Interpolates (Square (P := P)) := by
  intro a d had
  obtain ⟨b, c, hab, hbc, hcd⟩ := square_to_cube hdcpo hP had
  obtain ⟨p, q, hap, hpq, hqc⟩ := square_to_cube hdcpo hP ⟨b, hab, hbc⟩
  exact ⟨q, ⟨p, hap, hpq⟩, ⟨c, hqc, hcd⟩⟩

theorem square_idempotent (hdcpo : IsDcpo P) (hP : IsChainContinuous P) (a b : P) :
    RelComp Square Square a b ↔ Square a b := by
  constructor
  · rintro ⟨c, hac, hcb⟩
    exact hac.mono le_rfl hcb.le
  · exact square_interpolates hdcpo hP a b

theorem squareSection_directed (hP : IsChainContinuous P) (y : P) :
    NonemptyDirected (squareSection y) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨z, hz⟩ := (hP.section_directed y).1
    obtain ⟨a, ha⟩ := (hP.section_directed z).1
    exact ⟨a, z, ha, hz⟩
  · rintro a ⟨z, haz, hzy⟩ b ⟨w, hbw, hwy⟩
    obtain ⟨t, hty, hzt, hwt⟩ := (hP.section_directed y).2 z hzy w hwy
    have hat : ChainBelow a t := haz.mono le_rfl hzt
    have hbt : ChainBelow b t := hbw.mono le_rfl hwt
    obtain ⟨c, hct, hac, hbc⟩ := (hP.section_directed t).2 a hat b hbt
    exact ⟨c, ⟨t, hct, hty⟩, hac, hbc⟩

theorem squareSection_lower (y : P) : IsLowerSet (squareSection y) :=
  fun _ _ hab hby ↦ hby.mono hab le_rfl

theorem squareSection_lub (hP : IsChainContinuous P) (y : P) :
    IsLUB (squareSection y) y := by
  refine ⟨fun _ h ↦ h.le, ?_⟩
  intro q hq
  apply (hP.section_lub y).2
  intro z hz
  exact (hP.section_lub z).2 (fun a ha ↦ hq ⟨z, ha, hz⟩)

/-- Source Scott-open upper-section argument, expressed through the
equivalent Scott-closed complement to retain all nonempty conventions. -/
theorem square_complement_scottClosed (hdcpo : IsDcpo P) (hP : IsChainContinuous P)
    (a : P) : IsScottClosed {y | ¬ Square a y} := by
  apply (scottClosed_iff_chainClosed hdcpo _).mpr
  constructor
  · intro x y hxy hy hax
    exact hy (hax.mono le_rfl hxy)
  · intro C hCF hC s hs has
    obtain ⟨b, hab, hbs⟩ := square_interpolates hdcpo hP a s has
    obtain ⟨c, hc, hbc⟩ := (chainBelow_iff_sup hdcpo b s).mp hbs.chainBelow C hC s hs le_rfl
    exact hCF hc (hab.mono le_rfl hbc)

theorem square_wayBelow (hdcpo : IsDcpo P) (hP : IsChainContinuous P)
    {a b : P} (hab : Square a b) : WayBelow a b := by
  classical
  intro D hD s hs hbs
  by_contra hn
  have hDF : D ⊆ {y | ¬ Square a y} := by
    intro d hd had
    exact hn ⟨d, hd, had.le⟩
  exact (square_complement_scottClosed hdcpo hP a).2 D hDF hD s hs
    (hab.mono le_rfl hbs)

theorem wayBelow_square (hP : IsChainContinuous P) {a b : P}
    (hab : WayBelow a b) : Square a b := by
  obtain ⟨r, hr, har⟩ := hab (squareSection b) (squareSection_directed hP b)
    b (squareSection_lub hP b) le_rfl
  exact hr.mono har le_rfl

/-- Source `thm:main`, the exact elementwise identification. -/
theorem wayBelow_iff_square (hdcpo : IsDcpo P) (hP : IsChainContinuous P) (a b : P) :
    WayBelow a b ↔ ∃ c, ChainBelow a c ∧ ChainBelow c b :=
  ⟨wayBelow_square hP, square_wayBelow hdcpo hP⟩

theorem chainContinuous_continuous (hdcpo : IsDcpo P) (hP : IsChainContinuous P) :
    IsContinuous P := by
  refine ⟨hdcpo, ?_⟩
  intro b
  have heq : waySection b = squareSection b := by
    ext a
    exact wayBelow_iff_square hdcpo hP a b
  rw [heq]
  exact ⟨squareSection_directed hP b, squareSection_lub hP b⟩

omit [PartialOrder P] in
theorem relPower_one (T : P → P → Prop) (a b : P) : RelPower T 1 a b ↔ T a b := by
  simp [RelPower, RelComp]

theorem chainPower_add_two (hdcpo : IsDcpo P) (hP : IsChainContinuous P)
    (n : ℕ) (a b : P) : RelPower ChainBelow (n + 2) a b ↔ Square a b := by
  induction n generalizing a b with
  | zero => simp [RelPower, RelComp, Square]
  | succ n ih =>
    change (∃ c, RelPower ChainBelow (n + 2) a c ∧ ChainBelow c b) ↔ Square a b
    simp_rw [ih]
    constructor
    · rintro ⟨c, hac, hcb⟩
      exact hac.mono le_rfl hcb.le
    · intro hab
      obtain ⟨p, q, hap, hpq, hqb⟩ := square_to_cube hdcpo hP hab
      exact ⟨q, ⟨p, hap, hpq⟩, hqb⟩

theorem chainPower_stable (hdcpo : IsDcpo P) (hP : IsChainContinuous P)
    (n : ℕ) (hn : 2 ≤ n) (a b : P) : RelPower ChainBelow n a b ↔ Square a b := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  simpa only [Nat.add_comm 2 m] using chainPower_add_two hdcpo hP m a b

/-- The source main theorem with continuity and all relation powers packaged
together. There are no interpolation, matrix, or cofinality hypotheses added. -/
theorem main (hdcpo : IsDcpo P) (hP : IsChainContinuous P) :
    IsContinuous P ∧
      (∀ a b : P, WayBelow a b ↔ Square a b) ∧
      ∀ n : ℕ, 2 ≤ n → ∀ a b : P, WayBelow a b ↔ RelPower ChainBelow n a b := by
  refine ⟨chainContinuous_continuous hdcpo hP, wayBelow_iff_square hdcpo hP, ?_⟩
  intro n hn a b
  exact (wayBelow_iff_square hdcpo hP a b).trans (chainPower_stable hdcpo hP n hn a b).symm

theorem strong_iff_chainBelow_eq_wayBelow (hdcpo : IsDcpo P) (hP : IsChainContinuous P) :
    Interpolates (ChainBelow (P := P)) ↔ ∀ a b : P, ChainBelow a b ↔ WayBelow a b := by
  constructor
  · intro hi a b
    exact ⟨fun hab ↦ square_wayBelow hdcpo hP (hi a b hab), fun hab ↦ hab.chainBelow hdcpo⟩
  · intro heq a b hab
    exact (wayBelow_iff_square hdcpo hP a b).mp ((heq a b).mp hab)

/-- Source `cor:strong`, its cofinality assertion. -/
theorem chainBelow_not_wayBelow_cofinalities (hdcpo : IsDcpo P) (hP : IsChainContinuous P)
    {a b : P} (hab : ChainBelow a b) (hn : ¬ WayBelow a b) :
    kappa a = Cardinal.aleph0 ∧ kappa b = Cardinal.aleph 1 := by
  have ho := obstruction hdcpo hP hab (fun h ↦ hn (square_wayBelow hdcpo hP h))
  exact ⟨ho.1, ho.2.1⟩

end ChainApproximation
