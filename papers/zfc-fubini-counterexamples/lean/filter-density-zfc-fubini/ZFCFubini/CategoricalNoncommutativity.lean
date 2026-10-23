import ZFCFubini.Noncentral
import ZFCFubini.ValuationStrengthLaws

/-!
Source cor:noncentral, including its categorical conclusion. We evaluate the
two actual double-strength MORPHISMS of the proved continuous-subprobability
valuation MONAD on the literal source pair and its incidence Scott open.
This is not a new name for scalar Fubini failure: all functor, unit,
multiplication, monad and strength laws are supplied by the imported modules.
-/

set_option autoImplicit false
open Set Topology TopologicalSpace CategoryTheory
open CategoryTheory.MonoidalCategory
open scoped ENNReal Classical

namespace ZFCFubini

noncomputable def sourcePDcpo : DcpoCat := DcpoCat.of SourceP sourceP_isDcpo
noncomputable def sourceQDcpo : DcpoCat := DcpoCat.of SourceQ (completeLattice_isDcpo SourceQ)

noncomputable def sourceNuSubprob : ValuationMonad.obj sourcePDcpo :=
  ⟨sourceNu, sourceNu_probability.subprobability⟩

noncomputable def sourceEtaSubprob : ValuationMonad.obj sourceQDcpo :=
  ⟨sourceEtaValuation, sourceEta_probability.subprobability⟩

theorem source_doubleStrength_incidence :
    (ValuationMonad.strength.doubleStrength sourcePDcpo sourceQDcpo
      (sourceNuSubprob, sourceEtaSubprob)).val (incidenceOpen SourceP) = ENNReal.ofReal q := by
  rw [ValuationMonad.doubleStrength_apply]
  simpa only [sourceNuSubprob, sourceEtaSubprob, nnIncidence_value,
    incidenceOpen, incidenceSet, Set.mem_preimage, Set.mem_setOf_eq, Opens.mem_mk]
    using source_second_nn_iterated_integral

theorem source_doubleStrength'_incidence :
    (ValuationMonad.strength.doubleStrength' sourcePDcpo sourceQDcpo
      (sourceNuSubprob, sourceEtaSubprob)).val (incidenceOpen SourceP) = 1 := by
  rw [ValuationMonad.doubleStrength'_apply]
  simpa only [sourceNuSubprob, sourceEtaSubprob, nnIncidence_value,
    incidenceOpen, incidenceSet, Set.mem_preimage, Set.mem_setOf_eq, Opens.mem_mk]
    using source_first_nn_iterated_integral

/-- Inequality of the two genuine categorical arrows on specified objects. -/
theorem source_doubleStrength_ne :
    ValuationMonad.strength.doubleStrength sourcePDcpo sourceQDcpo ≠
      ValuationMonad.strength.doubleStrength' sourcePDcpo sourceQDcpo := by
  intro h
  have he := congrArg (fun k :
      ValuationMonad.obj sourcePDcpo ⊗ ValuationMonad.obj sourceQDcpo ⟶
        ValuationMonad.obj (sourcePDcpo ⊗ sourceQDcpo) =>
      (k (sourceNuSubprob, sourceEtaSubprob)).val (incidenceOpen SourceP)) h
  change (ValuationMonad.strength.doubleStrength sourcePDcpo sourceQDcpo
      (sourceNuSubprob, sourceEtaSubprob)).val (incidenceOpen SourceP) =
    (ValuationMonad.strength.doubleStrength' sourcePDcpo sourceQDcpo
      (sourceNuSubprob, sourceEtaSubprob)).val (incidenceOpen SourceP) at he
  rw [source_doubleStrength_incidence, source_doubleStrength'_incidence] at he
  have hq : q < 1 := q_bounds.2.trans_lt (by norm_num)
  have hqnn : ENNReal.ofReal q < 1 := by
    simpa only [ENNReal.ofReal_one] using
      (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 1)).mpr hq
  exact ne_of_lt hqnn he

theorem continuous_subprob_valuation_monad_not_commutative :
    ¬ CartesianMonadStrength.IsCommutative ValuationMonad.strength.{0} :=
  fun h => source_doubleStrength_ne (h sourcePDcpo sourceQDcpo)

namespace Paper

/-- Both sentences of source cor:noncentral, now including the actual monad. -/
theorem noncentral :
    (∃ (P : Type) (orderP : PartialOrder P),
      letI := orderP
      IsDcpo P ∧ ∃ μ : DValuation P, μ.Probability ∧ ¬ Central.{0, 0} μ) ∧
    ¬ CartesianMonadStrength.IsCommutative ValuationMonad.strength.{0} :=
  ⟨exists_noncentral_probability_valuation,
    continuous_subprob_valuation_monad_not_commutative⟩

end Paper
end ZFCFubini
