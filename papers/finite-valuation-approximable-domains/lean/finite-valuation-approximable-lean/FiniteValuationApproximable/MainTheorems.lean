import FiniteValuationApproximable.Final

/-!
# Source-facing main theorems

This file is the single entry point for the paper's headline theorem chain.
It deliberately restates the conclusions and gives Lean proof terms here,
rather than serving only as an import index.

The final objectwise theorem has the four clauses of `thm:main`.  The final
categorical package contains the proved Cartesian-closed structure and the
two restricted continuous-valuation monads.
-/

set_option autoImplicit false

universe u

namespace FiniteValuationApproximable

/-! ## Headline input theorems -/

/-- Source theorem `thm:finite-polytope`. -/
theorem paper_finite_polytope
    (A P : Type u)
    [Fintype A] [PartialOrder A] [Fintype P] [PartialOrder P] :
    IsFVA.{u, u} (MonotoneTable A P) := by
  exact finite_monotone_table_isFVA A P

/-- Source theorem `thm:kernel-lifting`, in its bundled approximation form. -/
theorem paper_kernel_lifting
    {X : Type u} [PartialOrder X]
    (hX : IsFSDomain X) (K : FiniteKernelApproximation X)
    (P : FinitePoset.{u})
    (hTableFVA : forall n,
      IsFVA.{u, u} (MonotoneTable (K.stage n) P)) :
    IsFVA.{u, u} (ContinuousValuation.VSub X) ∧
      IsFVA.{u, u}
        (AbramskyJung.Chapter3.ContFun X
          (ContinuousValuation.VSub P)) := by
  exact kernel_lifting_of_approximation hX K P hTableFVA

/-- Source corollary `cor:finite-generators`. -/
theorem paper_finite_generators :
    FiniteDoubleValuationGeneratorsAreFVA.{u} ∧
      FiniteFunctionGeneratorsAreFVA.{u} := by
  exact finiteGeneratorsAreFVA

/-- Product part of source theorem `thm:global-transfer`. -/
theorem paper_global_product
    {D E : Type u} [PartialOrder D] [PartialOrder E]
    (hD : IsFVA.{u, u} D) (hE : IsFVA.{u, u} E) :
    IsFVA.{u, u} (D × E) := by
  exact global_product hD hE

/-- Function-space part of source theorem `thm:global-transfer`. -/
theorem paper_global_function_space
    {D E : Type u} [PartialOrder D] [PartialOrder E]
    (hD : IsFVA.{u, u} D) (hE : IsFVA.{u, u} E) :
    IsFVA.{u, u} (AbramskyJung.Chapter3.ContFun D E) := by
  exact global_functionSpace_of_finite_generators
    finiteFunctionGeneratorsAreFVA hD hE

/-- Genuine subprobability-valuation part of the global transfer theorem. -/
theorem paper_global_vSub
    {D : Type u} [PartialOrder D] (hD : IsFVA.{u, u} D) :
    IsFVA.{u, u} (ContinuousValuation.VSub D) := by
  exact global_vSub_of_finite_double_generators
    finiteDoubleValuationGeneratorsAreFVA hD

/-- Source theorem `thm:global-Vone`. -/
theorem paper_global_vOne
    {D : Type u} [PartialOrder D] (hD : IsFVA.{u, u} D) :
    IsFVA.{u, u} (ContinuousValuation.VOne D) := by
  exact global_vOne_of_finite_double_generators
    finiteDoubleValuationGeneratorsAreFVA hD

/-! ## The four clauses of the main theorem -/

/-- Clause (i): every FVA object is pointed, countably based, and an
FS-domain. -/
theorem paper_main_clause_i : MainTheoremClauseI.{u} := by
  intro D _ hD
  exact fva_pointed_countablyBased_fs hD

/-- Clause (ii): finite generators and the terminal object are FVA, and the
class is closed under continuous retracts and binary products. -/
theorem paper_main_clause_ii : MainTheoremClauseII.{u} := by
  refine {
    finite_generators := ?_
    terminal_mem := ?_
    terminal_unique := ?_
    retract_closed := ?_
    binary_product_closed := ?_ }
  · exact finiteStage_isFVA_unconditional
  · exact terminal_isFVA
  · intro D _ f
    exact terminalMap_unique D f
  · intro D E _ _ sr hE
    exact IsFVA.retract sr hE
  · intro D E _ _ hD hE
    exact paper_global_product hD hE

/-- Clause (iii): FVA is closed under continuous function spaces. -/
theorem paper_main_clause_iii : MainTheoremClauseIII.{u} := by
  intro D E _ _ hD hE
  exact paper_global_function_space hD hE

/-- Clause (iv): FVA is closed under both genuine continuous-valuation
constructions. -/
theorem paper_main_clause_iv : MainTheoremClauseIV.{u} := by
  intro D _ hD
  exact ⟨paper_global_vSub hD, paper_global_vOne hD⟩

/-- The four numbered assertions of source theorem `thm:main`. -/
theorem paper_main_objectwise : MainTheoremObjectwise.{u} := by
  exact {
    clause_i := paper_main_clause_i
    clause_ii := paper_main_clause_ii
    clause_iii := paper_main_clause_iii
    clause_iv := paper_main_clause_iv }

/-! ## Categorical and monadic consequences -/

/-- The full FVA subcategory is Cartesian closed in the formalized
Scott-continuous-map category. -/
theorem paper_main_cartesian_closed :
    FVALocalCartesianClosed
      finiteFunctionGeneratorsAreFVA := by
  exact fvaLocalCartesianClosed finiteFunctionGeneratorsAreFVA

/-- The subprobability continuous-valuation monad restricted to FVA objects. -/
noncomputable def paper_main_vSub_monad_restriction :
    FVAKleisliMonadRestriction.{u} :=
  vSubFVAMonadRestriction finiteDoubleValuationGeneratorsAreFVA

/-- The probability continuous-valuation monad restricted to FVA objects. -/
noncomputable def paper_main_vOne_monad_restriction :
    FVAKleisliMonadRestriction.{u} :=
  vOneFVAMonadRestriction finiteDoubleValuationGeneratorsAreFVA

/-- The complete categorical `Hence` package following `thm:main`. -/
noncomputable def paper_main_categorical_consequences :
    MainTheoremCategoricalConsequences
      finiteFunctionGeneratorsAreFVA
      finiteDoubleValuationGeneratorsAreFVA where
  cartesianClosed := paper_main_cartesian_closed
  vSubRestriction := paper_main_vSub_monad_restriction
  vOneRestriction := paper_main_vOne_monad_restriction

/-- Single endpoint containing the four numbered clauses and the existence of
all categorical and monadic structure asserted after them. -/
theorem paper_main :
    MainTheoremObjectwise.{u} ∧
      Nonempty (MainTheoremCategoricalConsequences
        finiteFunctionGeneratorsAreFVA
        finiteDoubleValuationGeneratorsAreFVA) := by
  exact ⟨paper_main_objectwise,
    ⟨paper_main_categorical_consequences⟩⟩

end FiniteValuationApproximable
