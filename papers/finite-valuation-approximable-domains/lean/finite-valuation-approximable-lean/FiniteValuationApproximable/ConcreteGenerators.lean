import FiniteValuationApproximable.FiniteGenerators
import FiniteValuationApproximable.FinitePolytopeHaar
import FiniteValuationApproximable.FinitePolytopeKernel

/-!
# Concrete finite generators

This module specializes the genuine finite-kernel bridge to the Haar
randomized-rounding construction.  The empty-column case is treated by an
explicit constant Dirac kernel on a singleton stage; hence no nonemptiness
hypothesis survives in the two finite-generator conclusions.
-/

set_option autoImplicit false
set_option linter.unnecessarySimpa false

universe u

namespace FiniteValuationApproximable

/-! ## The terminal kernel -/

section TerminalKernel

variable {X : Type u} [PartialOrder X] [Nonempty X] [Subsingleton X]

/-- The constant probability law on the singleton finite stage. -/
noncomputable def terminalProbabilityKernel :
    ScottContFun X (ContinuousValuation.VOne UnitStage.{u}) :=
  ContinuousValuation.probabilityKernelToFiniteVOne
    (fun _ : X => SubprobabilityVector.diracProbability (ULift.up ()))
    (AbramskyJung.Chapter2.const_scottContinuous
      (SubprobabilityVector.diracProbability (ULift.up ())).1)

/-- The unique label from the singleton stage into a subsingleton target. -/
noncomputable def terminalKernelLabel :
    ScottContFun UnitStage.{u} X where
  toFun := fun _ => Classical.choice inferInstance
  continuous := AbramskyJung.Chapter2.const_scottContinuous
    (Classical.choice inferInstance)

/-- The constant singleton kernel is exactly the Dirac unit on a
subsingleton target. -/
theorem terminalContinuousKernel_eq_unit (x : X) :
    continuousFiniteKernel UnitStage.{u}
        (terminalProbabilityKernel (X := X))
        (terminalKernelLabel (X := X)) x =
      ContinuousValuation.unit (D := X) x := by
  rw [continuousFiniteKernel_apply]
  change ContinuousValuation.pushforward
      (terminalKernelLabel (X := X))
      (ContinuousValuation.VOne.toVSub
        (ContinuousValuation.probabilityVectorToVOne
          (SubprobabilityVector.diracProbability (ULift.up ())))) =
    ContinuousValuation.dirac x
  apply le_antisymm
  · exact (ContinuousValuation.pushforward_probabilityVector_sandwich
      (SubprobabilityVector.diracProbability (ULift.up ()))
      (terminalKernelLabel (X := X))
      (fun l _ => le_of_eq (Subsingleton.elim x
        (terminalKernelLabel (X := X) l)))
      (fun l _ => le_of_eq (Subsingleton.elim
        (terminalKernelLabel (X := X) l) x))).2
  · exact (ContinuousValuation.pushforward_probabilityVector_sandwich
      (SubprobabilityVector.diracProbability (ULift.up ()))
      (terminalKernelLabel (X := X))
      (fun l _ => le_of_eq (Subsingleton.elim x
        (terminalKernelLabel (X := X) l)))
      (fun l _ => le_of_eq (Subsingleton.elim
        (terminalKernelLabel (X := X) l) x))).1

/-- Every nonempty subsingleton poset has the constant finite probability-
kernel approximation of its identity. -/
noncomputable def subsingletonFiniteKernelApproximation :
    FiniteKernelApproximation X where
  stage := fun _ => UnitStage.{u}
  probability := fun _ => terminalProbabilityKernel (X := X)
  label := fun _ => terminalKernelLabel (X := X)
  kernel_mono := by
    intro n m hnm x
    simpa only [terminalContinuousKernel_eq_unit] using
      (le_refl (ContinuousValuation.unit (D := X) x))
  kernel_below_unit := by
    intro n x
    rw [terminalContinuousKernel_eq_unit]
  kernel_pointwise_sup_unit := by
    intro x
    constructor
    · rintro _ ⟨n, rfl⟩
      simpa only [terminalContinuousKernel_eq_unit] using
        (le_refl (ContinuousValuation.unit (D := X) x))
    · intro nu hnu
      have hstage := hnu ⟨0, rfl⟩
      simpa only [terminalContinuousKernel_eq_unit] using hstage

end TerminalKernel

/-! ## Concrete kernel and generator theorems -/

/-- The concrete Haar kernel, now represented as a genuine normalized
continuous valuation, approximates the identity on every nonempty finite
monotone-table domain. -/
noncomputable def finiteMonotoneTableKernelApproximationOfNonempty
    (A P : Type u)
    [Fintype A] [PartialOrder A] [Fintype P] [PartialOrder P]
    [Nonempty A] [Nonempty P] :
    FiniteKernelApproximation (MonotoneTable A P) :=
  finitePolytopeKernelApproximation
    (finiteTableStage (A := A) (P := P))
    (finiteTableProbability (A := A) (P := P))
    (finiteTableLabel (A := A) (P := P))
    (finiteTableBeta (A := A) (P := P))
    (finiteTableAlpha (A := A) (P := P))
    (finiteTableBeta_antitone (A := A) (P := P))
    (finiteTableBeta_tendsto_zero (A := A) (P := P))
    (finiteTableBeta_succ_le_alpha (A := A) (P := P))
    (finiteTableProbability_scottContinuous (A := A) (P := P))
    (finiteTableLabel_mono (A := A) (P := P))
    (fun n x l hl =>
      (finiteTableLabel_sandwich (A := A) (P := P) n x l hl).1)
    (fun n x l hl =>
      (finiteTableLabel_sandwich (A := A) (P := P) n x l hl).2)

/-- Existence of the one-row table kernel needed by
`cor:finite-generators`, including the empty finite column poset.  Keeping
the case split in `Prop` avoids eliminating `IsEmpty ∨ Nonempty` into data. -/
theorem finiteGeneratorKernelApproximation_exists
    (Q : FinitePoset.{u}) :
    Nonempty (FiniteKernelApproximation
      (MonotoneTable UnitStage.{u} Q)) := by
  classical
  cases isEmpty_or_nonempty Q with
  | inl hQ =>
      letI := hQ
      letI : Nonempty (MonotoneTable UnitStage.{u} Q) :=
        ⟨zeroMonotoneTable⟩
      letI : Subsingleton (MonotoneTable UnitStage.{u} Q) :=
        ⟨fun x y => MonotoneTable.ext_coeff UnitStage.{u} Q
          (fun _a q => isEmptyElim q)⟩
      exact ⟨subsingletonFiniteKernelApproximation
        (X := MonotoneTable UnitStage.{u} Q)⟩
  | inr hQ =>
      letI := hQ
      letI : Nonempty UnitStage.{u} := ⟨ULift.up ()⟩
      exact ⟨finiteMonotoneTableKernelApproximationOfNonempty
        UnitStage.{u} Q⟩

/-- The selected concrete one-row kernel approximation. -/
noncomputable def finiteGeneratorKernelApproximation
    (Q : FinitePoset.{u}) :
    FiniteKernelApproximation (MonotoneTable UnitStage.{u} Q) :=
  Classical.choice (finiteGeneratorKernelApproximation_exists Q)

/-- Source corollary `cor:finite-generators`, with all concrete kernel and
finite-polytope premises discharged. -/
theorem finiteGeneratorsAreFVA :
    FiniteDoubleValuationGeneratorsAreFVA.{u} ∧
      FiniteFunctionGeneratorsAreFVA.{u} :=
  finiteGeneratorsAreFVA_of_kernel_approximations
    finiteGeneratorKernelApproximation
      (fun A P => finite_monotone_table_isFVA A.carrier P.carrier)

theorem finiteDoubleValuationGeneratorsAreFVA :
    FiniteDoubleValuationGeneratorsAreFVA.{u} :=
  finiteGeneratorsAreFVA |>.1

theorem finiteFunctionGeneratorsAreFVA :
    FiniteFunctionGeneratorsAreFVA.{u} :=
  finiteGeneratorsAreFVA |>.2

end FiniteValuationApproximable
