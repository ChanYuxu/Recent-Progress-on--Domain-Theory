import CantorFubini.ValuationMonad
import CantorFubini.SourceIntegralBridge

/-! Source Corollary 6.4: the actual subprobability valuation monad is not
commutative. The two canonical double-strength morphisms are evaluated at
the paper's constructed valuations and incidence open. The proof directly
distinguishes those categorical morphisms, without an assumed Fubini criterion. -/

set_option autoImplicit false
open Set Topology TopologicalSpace CategoryTheory
open scoped ENNReal Classical

namespace CantorFubini

noncomputable def counterP : DCPO := DCPO.of P P_isDcpo
noncomputable def counterQ : DCPO := DCPO.of Q Q_isDcpo

noncomputable def counterNu : DCPO.valuations counterP :=
  ⟨nu cantorMeasure, (nu_probability cantorMeasure).subprobability⟩
noncomputable def counterEta : DCPO.valuations counterQ :=
  ⟨eta, eta_probability.subprobability⟩

noncomputable def counterIncidence : ScottOpens (DCPO.prod counterP counterQ) := incidenceOpen P

theorem counterIncidence_leftSection (p : P) :
    DCPO.leftSection counterIncidence p = evaluationOpen p := by
  apply Opens.ext
  ext H
  rfl

theorem counterIncidence_rightSection (H : Q) :
    DCPO.rightSection counterIncidence H = H := by
  apply Opens.ext
  ext p
  rfl

theorem counter_doubleLeft_value :
    ((DCPO.valuationMonadStrength.doubleLeft counterP counterQ
      (counterNu, counterEta)).val counterIncidence).toReal = q := by
  rw [DCPO.doubleLeft_apply]
  simp_rw [counterIncidence_leftSection]
  have hb := sourceIntegral_toReal counterNu
    (fun p : WithScott P => eta (evaluationOpen (WithScott.ofScott p)))
    (fun p => eta_probability.subprobability.mass_le_one _)
  change paperIntegral nuProbability (fun p : WithScott P => sectionValue (WithScott.ofScott p)) =
    (vIntegral (nu cantorMeasure) (fun p : WithScott P =>
      eta (evaluationOpen (WithScott.ofScott p)))).toReal at hb
  have hs := source_main.2.2.2.2.2.2.1
  simp_rw [incidence_inner_right] at hs
  exact hb.symm.trans hs

theorem counter_doubleRight_value :
    ((DCPO.valuationMonadStrength.doubleRight counterP counterQ
      (counterNu, counterEta)).val counterIncidence).toReal = 1 := by
  rw [DCPO.doubleRight_apply]
  simp_rw [counterIncidence_rightSection]
  have hb := sourceIntegral_toReal counterEta
    (fun H : WithScott Q => nu cantorMeasure (WithScott.ofScott H))
    (fun H => (nu_probability cantorMeasure).subprobability.mass_le_one _)
  change paperIntegral etaProbability (fun H : WithScott Q => realMass nuProbability (WithScott.ofScott H)) =
    (vIntegral eta (fun H : WithScott Q => nu cantorMeasure (WithScott.ofScott H))).toReal at hb
  have hs := source_main.2.2.2.2.2.1
  simp_rw [incidence_inner_left] at hs
  exact hb.symm.trans hs

theorem counter_doubleStrengths_ne :
    DCPO.valuationMonadStrength.doubleLeft counterP counterQ ≠
      DCPO.valuationMonadStrength.doubleRight counterP counterQ := by
  intro h
  have hv := congrArg (fun f : DCPO.prod (DCPO.valuations counterP) (DCPO.valuations counterQ) ⟶
      DCPO.valuations (DCPO.prod counterP counterQ) =>
      ((f (counterNu, counterEta)).val counterIncidence).toReal) h
  change ((DCPO.valuationMonadStrength.doubleLeft counterP counterQ
    (counterNu, counterEta)).val counterIncidence).toReal =
    ((DCPO.valuationMonadStrength.doubleRight counterP counterQ
      (counterNu, counterEta)).val counterIncidence).toReal at hv
  rw [counter_doubleLeft_value, counter_doubleRight_value] at hv
  have hq := source_main.2.2.2.2.2.2.2.2
  linarith

/-- Actual categorical noncommutativity of the constructed strong monad. -/
theorem source_monad_noncommutative :
    ¬ DCPO.valuationMonadStrength.{0}.IsCommutative := by
  intro h
  exact counter_doubleStrengths_ne (h counterP counterQ)

end CantorFubini
