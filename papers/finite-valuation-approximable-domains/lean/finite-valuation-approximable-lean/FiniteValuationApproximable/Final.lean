import FiniteValuationApproximable.MainTheorem
import FiniteValuationApproximable.ConcreteGenerators
import FiniteValuationApproximable.CategoricalConsequences

/-!
# Unconditional main theorem

The concrete Haar finite kernels discharge the last two generator premises of
`thm_main_objectwise_of_generators`.  This module is deliberately small so
that the final theorem's transitive axiom set can be audited directly.
-/

set_option autoImplicit false

universe u

namespace FiniteValuationApproximable

/-- The four numbered assertions of source theorem `thm:main`, with no
paper-internal premise remaining. -/
theorem thm_main_objectwise : MainTheoremObjectwise.{u} :=
  thm_main_objectwise_of_generators
    finiteFunctionGeneratorsAreFVA finiteDoubleValuationGeneratorsAreFVA

/-- The objectwise Cartesian-closure data obtained from the main theorem. -/
theorem thm_main_objectwise_cartesian_closure :
    FVAObjectwiseCartesianClosure.{u} :=
  thm_main_objectwise.objectwiseCartesianClosure

/-- The objectwise closure of both genuine continuous-valuation
constructions obtained from the main theorem. -/
theorem thm_main_valuation_object_closure :
    FVAValuationObjectClosure.{u} :=
  thm_main_objectwise.valuationObjectClosure

/-- The source theorem's final `Hence` sentence: a genuine local full
Cartesian closed category of FVA objects together with restrictions of both
continuous-valuation monads. -/
noncomputable def thm_main_categorical_consequences :
    MainTheoremCategoricalConsequences
      finiteFunctionGeneratorsAreFVA
      finiteDoubleValuationGeneratorsAreFVA :=
  thm_main_categorical_consequences_of_generators
    finiteFunctionGeneratorsAreFVA finiteDoubleValuationGeneratorsAreFVA

/-- Single propositional endpoint containing the four numbered assertions
and existence of all categorical/monadic structure asserted after them. -/
theorem thm_main :
    MainTheoremObjectwise.{u} ∧
      Nonempty (MainTheoremCategoricalConsequences
        finiteFunctionGeneratorsAreFVA
        finiteDoubleValuationGeneratorsAreFVA) :=
  ⟨thm_main_objectwise, ⟨thm_main_categorical_consequences⟩⟩

end FiniteValuationApproximable
