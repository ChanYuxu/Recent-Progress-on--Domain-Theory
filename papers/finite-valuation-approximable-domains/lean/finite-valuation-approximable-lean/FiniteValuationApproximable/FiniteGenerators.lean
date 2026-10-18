import FiniteValuationApproximable.KernelLifting
import FiniteValuationApproximable.FinitePolytope
import FiniteValuationApproximable.ContinuousValuation.Transport
import FiniteValuationApproximable.ContinuousValuation.FiniteProbability

/-!
# Finite generators from kernel lifting

This module is the acyclic glue between the genuine continuous-valuation
kernel-lifting theorem and the independently constructed finite-polytope
approximations.  It first records the one-row table representation of a
finite valuation.  It then derives exactly the two finite-generator premises
consumed by the global transfer theorems, while retaining the concrete kernel
and table-FVA inputs as explicit arguments.
-/

set_option autoImplicit false
set_option linter.unnecessarySimpa false

universe u

namespace FiniteValuationApproximable

/-! ## A one-row table is one genuine finite valuation -/

/-- The one-element finite poset used to regard a valuation as a one-row
monotone table. -/
def UnitStage : FinitePoset.{u} where
  carrier := ULift.{u} Unit
  fintype := inferInstance
  partialOrder := inferInstance

/-- Evaluation at the unique point is an order isomorphism from the
continuous function space on `UnitStage` to its codomain. -/
noncomputable def unitContFunOrderIso
    (E : Type u) [Preorder E] :
    AbramskyJung.Chapter3.ContFun UnitStage.{u} E ≃o E where
  toFun f := f (ULift.up ())
  invFun e := {
    toFun := fun _ => e
    continuous := scottContinuous_of_monotone_finite
      (fun _ _ _ => le_rfl) }
  left_inv := by
    intro f
    apply AbramskyJung.Chapter3.ContFun.ext_apply
    intro x
    rcases x with ⟨x⟩
    cases x
    rfl
  right_inv := by
    intro e
    rfl
  map_rel_iff' := by
    intro f g
    constructor
    · intro h x
      rcases x with ⟨x⟩
      cases x
      exact h
    · intro h
      exact h (ULift.up ())

/-- A one-row atomic monotone table is exactly a genuine continuous
subprobability valuation on the finite column poset. -/
noncomputable def unitMonotoneTableVSubOrderIso
    (Q : FinitePoset.{u}) :
    MonotoneTable UnitStage.{u} Q ≃o ContinuousValuation.VSub Q :=
  (continuousValuationTableOrderIso UnitStage.{u} Q).trans
    (unitContFunOrderIso (ContinuousValuation.VSub Q))

/-- The same one-row table represented by the manuscript's atomic finite
subprobability vector. -/
noncomputable def unitMonotoneTableAtomicOrderIso
    (Q : FinitePoset.{u}) :
    MonotoneTable UnitStage.{u} Q ≃o Q.VSub :=
  (unitMonotoneTableVSubOrderIso Q).trans
    (ContinuousValuation.finiteVSubOrderIso (P := Q)).symm

/-! ## Abstract finite-generator closure -/

/-- The double-valuation finite generators follow from kernel lifting on
one-row tables.  Pushforward along the representation isomorphism transports
the result to the exact atomic generator type used by `GlobalValuation`. -/
theorem finiteDoubleValuationGeneratorsAreFVA_of_kernel_approximations
    (hKernel : forall Q : FinitePoset.{u},
      FiniteKernelApproximation (MonotoneTable UnitStage.{u} Q))
    (hTableFVA : forall A P : FinitePoset.{u},
      IsFVA.{u, u} (MonotoneTable A P)) :
    FiniteDoubleValuationGeneratorsAreFVA.{u} := by
  intro Q
  have hLift : IsFVA.{u, u}
      (ContinuousValuation.VSub (MonotoneTable UnitStage.{u} Q)) :=
    kernel_lifting_vSub_isFVA_of_approximation
      (hTableFVA UnitStage.{u} Q).isFSDomain_unconditional (hKernel Q)
  let e := ContinuousValuation.pushforwardOrderIso
    (unitMonotoneTableAtomicOrderIso Q)
  exact IsFVA.retract
    (orderIsoContinuousSectionRetractionPair e.symm) hLift

/-- The finite function generators follow from the function clause of kernel
lifting.  Domain and codomain representations are transported simultaneously
by `contFunOrderIso`. -/
theorem finiteFunctionGeneratorsAreFVA_of_kernel_approximations
    (hKernel : forall Q : FinitePoset.{u},
      FiniteKernelApproximation (MonotoneTable UnitStage.{u} Q))
    (hTableFVA : forall A P : FinitePoset.{u},
      IsFVA.{u, u} (MonotoneTable A P)) :
    FiniteFunctionGeneratorsAreFVA.{u} := by
  intro P Q
  let K := hKernel P
  have hLift : IsFVA.{u, u}
      (AbramskyJung.Chapter3.ContFun
        (MonotoneTable UnitStage.{u} P) (ContinuousValuation.VSub Q)) :=
    kernel_lifting_function_isFVA_of_table_approximation
      (hTableFVA UnitStage.{u} P).isFSDomain_unconditional K Q
        (fun n => hTableFVA (K.stage n) Q)
  let e := contFunOrderIso
    (unitMonotoneTableAtomicOrderIso P)
    (ContinuousValuation.finiteVSubOrderIso (P := Q)).symm
  exact IsFVA.retract
    (orderIsoContinuousSectionRetractionPair e.symm) hLift

/-- Exact abstract form of source corollary `cor:finite-generators`.  No
concrete finite-polytope theorem is assumed under an invented declaration
name; the later specialization supplies the two displayed inputs. -/
theorem finiteGeneratorsAreFVA_of_kernel_approximations
    (hKernel : forall Q : FinitePoset.{u},
      FiniteKernelApproximation (MonotoneTable UnitStage.{u} Q))
    (hTableFVA : forall A P : FinitePoset.{u},
      IsFVA.{u, u} (MonotoneTable A P)) :
    FiniteDoubleValuationGeneratorsAreFVA.{u} ∧
      FiniteFunctionGeneratorsAreFVA.{u} :=
  ⟨finiteDoubleValuationGeneratorsAreFVA_of_kernel_approximations
      hKernel hTableFVA,
    finiteFunctionGeneratorsAreFVA_of_kernel_approximations
      hKernel hTableFVA⟩

end FiniteValuationApproximable
