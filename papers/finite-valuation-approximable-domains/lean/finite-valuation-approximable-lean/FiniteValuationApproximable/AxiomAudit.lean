import FiniteValuationApproximable.MainTheorems

/-!
# Axiom audit for the source-facing theorem chain

Run with:

```sh
lake build FiniteValuationApproximable.AxiomAudit
```

These commands ask Lean itself for the transitive axiom set of every headline
endpoint collected in `MainTheorems.lean`.
-/

namespace FiniteValuationApproximable

#print axioms paper_finite_polytope
#print axioms paper_kernel_lifting
#print axioms paper_finite_generators
#print axioms paper_global_product
#print axioms paper_global_function_space
#print axioms paper_global_vSub
#print axioms paper_global_vOne

#print axioms paper_main_clause_i
#print axioms paper_main_clause_ii
#print axioms paper_main_clause_iii
#print axioms paper_main_clause_iv
#print axioms paper_main_objectwise

#print axioms paper_main_cartesian_closed
#print axioms paper_main_vSub_monad_restriction
#print axioms paper_main_vOne_monad_restriction
#print axioms paper_main_categorical_consequences
#print axioms paper_main

end FiniteValuationApproximable

