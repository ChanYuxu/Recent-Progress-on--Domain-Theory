import FiniteValuationApproximable.External.Gierz
import FiniteValuationApproximable.FiniteProductContinuity

/-!
# Unconditional domain component of global function-space closure

The manuscript's global function-space transfer has two logically distinct
inputs: finite-generator closure and continuity of the ambient exponential.
The former is supplied later by the internally proved kernel-lifting theorem;
the latter is discharged here, once and for all, by the audited external
Gierz--Hofmann--Keimel--Lawson--Mislove--Scott Proposition II-2.18.

No theorem in this file assumes function-space FVA closure itself.
-/

set_option autoImplicit false

universe u

namespace FiniteValuationApproximable

/-- Once the finite function generators have been proved FVA, the global
function-space clause of `thm:global-transfer` has no remaining domain or
finite-stage premise. -/
theorem global_functionSpace_of_finite_generators
    {D E : Type u} [PartialOrder D] [PartialOrder E]
    (hFiniteFunctions : FiniteFunctionGeneratorsAreFVA.{u})
    (hD : IsFVA.{u, u} D) (hE : IsFVA.{u, u} E) :
    IsFVA.{u, u} (AbramskyJung.Chapter3.ContFun D E) :=
  global_functionSpace_conditional
    finiteStagesHaveFSApproximateIdentities
    finiteStagesAreContinuousDcpos
    hFiniteFunctions hD hE
    (fvaFunction_isContinuousDcpo hD hE)

/-- Product closure is already unconditional; together with the preceding
theorem, finite-function-generator closure yields both Cartesian operations
needed by the main theorem. -/
theorem global_product_and_function_of_finite_generators
    {D E : Type u} [PartialOrder D] [PartialOrder E]
    (hFiniteFunctions : FiniteFunctionGeneratorsAreFVA.{u})
    (hD : IsFVA.{u, u} D) (hE : IsFVA.{u, u} E) :
    IsFVA.{u, u} (D × E) ∧
      IsFVA.{u, u} (AbramskyJung.Chapter3.ContFun D E) :=
  ⟨global_product hD hE,
    global_functionSpace_of_finite_generators hFiniteFunctions hD hE⟩

end FiniteValuationApproximable
