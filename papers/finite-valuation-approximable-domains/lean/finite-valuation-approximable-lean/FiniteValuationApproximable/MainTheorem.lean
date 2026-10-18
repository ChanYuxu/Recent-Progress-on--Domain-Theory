import FiniteValuationApproximable.MainLocal
import FiniteValuationApproximable.GlobalFunction
import FiniteValuationApproximable.GlobalVOne

/-!
# Strict object-level assembly of the main theorem

This module packages the four numbered assertions of source theorem
`thm:main` in `main (17).tex` (source SHA-256
`4b2e65f0f96347bea4df7571e8993ad6e888c0ff7181c1305c5056880365ac94`):

1. every FVA object is a pointed, countably based FS-domain;
2. finite valuation generators and the terminal dcpo are FVA, and FVA is
   closed under continuous retracts and finite products;
3. FVA is closed under continuous function spaces; and
4. FVA is closed under the actual continuous `VSub` and `VOne` constructions.

The manuscript then states categorical Cartesian closedness and restriction of
the two valuation monads.  The local standalone development does not yet bundle
the required category, universal-property, natural-transformation, and monad-law
interfaces.  We therefore expose only two explicitly named *objectwise*
consequence records below.  They contain genuine closure and terminal-map data;
they are not aliases for `True` and are not advertised as categorical or monadic
theorems.
-/

set_option autoImplicit false

universe u

namespace FiniteValuationApproximable

/-! ## The four source clauses -/

/-- Object-level content of `thm:main(i)`.  Here
`IsOmegaContinuousDcpo` is the standalone API's countably based continuous-dcpo
predicate, while `IsFSDomain` supplies the FS-domain assertion. -/
def MainTheoremClauseI : Prop :=
  ∀ {D : Type u} [PartialOrder D], IsFVA.{u, u} D →
    AbramskyJung.Chapter3.HasLeastElement D ∧
      AbramskyJung.Chapter2.IsOmegaContinuousDcpo D ∧
      IsFSDomain D

/-- Object-level content of `thm:main(ii)`.  Terminal membership and its actual
unique-map property are recorded separately.  Together with binary-product
closure, the terminal field expresses closure under finite product objects
without claiming an unimplemented categorical product interface. -/
structure MainTheoremClauseII : Prop where
  finite_generators :
    ∀ P : FinitePoset.{u}, IsFVA.{u, u} P.VSub
  terminal_mem :
    IsFVA.{u, u} (emptyFinitePoset.{u}).VSub
  terminal_unique :
    ∀ (D : Type u) [Preorder D]
      (f : AbramskyJung.Chapter3.ContFun D (emptyFinitePoset.{u}).VSub),
      f = terminalMap D
  retract_closed :
    ∀ {D E : Type u} [PartialOrder D] [PartialOrder E],
      AbramskyJung.Chapter3.ContinuousSectionRetractionPair D E →
      IsFVA.{u, u} E → IsFVA.{u, u} D
  binary_product_closed :
    ∀ {D E : Type u} [PartialOrder D] [PartialOrder E],
      IsFVA.{u, u} D → IsFVA.{u, u} E → IsFVA.{u, u} (D × E)

/-- Object-level content of `thm:main(iii)`. -/
def MainTheoremClauseIII : Prop :=
  ∀ {D E : Type u} [PartialOrder D] [PartialOrder E],
    IsFVA.{u, u} D → IsFVA.{u, u} E →
      IsFVA.{u, u} (AbramskyJung.Chapter3.ContFun D E)

/-- Object-level content of `thm:main(iv)`, using the actual Scott-open
continuous-valuation types rather than finite-vector surrogates. -/
def MainTheoremClauseIV : Prop :=
  ∀ {D : Type u} [PartialOrder D], IsFVA.{u, u} D →
    IsFVA.{u, u} (ContinuousValuation.VSub D) ∧
      IsFVA.{u, u} (ContinuousValuation.VOne D)

/-- Faithful object-level package of the four numbered assertions of source
theorem `thm:main`. -/
structure MainTheoremObjectwise : Prop where
  clause_i : MainTheoremClauseI.{u}
  clause_ii : MainTheoremClauseII.{u}
  clause_iii : MainTheoremClauseIII.{u}
  clause_iv : MainTheoremClauseIV.{u}

/-! ## Honest objectwise forms of the two categorical consequences -/

/-- Exactly the object and terminal-map data locally available for the source's
Cartesian-closed consequence.  This record deliberately does **not** assert a
`Category`, categorical products, exponentials, or their universal properties. -/
structure FVAObjectwiseCartesianClosure : Prop where
  terminal_mem :
    IsFVA.{u, u} (emptyFinitePoset.{u}).VSub
  terminal_unique :
    ∀ (D : Type u) [Preorder D]
      (f : AbramskyJung.Chapter3.ContFun D (emptyFinitePoset.{u}).VSub),
      f = terminalMap D
  binary_product_closed :
    ∀ {D E : Type u} [PartialOrder D] [PartialOrder E],
      IsFVA.{u, u} D → IsFVA.{u, u} E → IsFVA.{u, u} (D × E)
  function_object_closed :
    ∀ {D E : Type u} [PartialOrder D] [PartialOrder E],
      IsFVA.{u, u} D → IsFVA.{u, u} E →
        IsFVA.{u, u} (AbramskyJung.Chapter3.ContFun D E)

/-- Exactly the object-mapping closure locally available for the source's claim
that the two valuation monads restrict.  This record does **not** assert the
units, multiplications, naturality, or monad laws. -/
structure FVAValuationObjectClosure : Prop where
  vSub_closed :
    ∀ {D : Type u} [PartialOrder D], IsFVA.{u, u} D →
      IsFVA.{u, u} (ContinuousValuation.VSub D)
  vOne_closed :
    ∀ {D : Type u} [PartialOrder D], IsFVA.{u, u} D →
      IsFVA.{u, u} (ContinuousValuation.VOne D)

/-- The objectwise Cartesian-closure data extracted from the four clauses. -/
theorem MainTheoremObjectwise.objectwiseCartesianClosure
    (h : MainTheoremObjectwise.{u}) :
    FVAObjectwiseCartesianClosure.{u} where
  terminal_mem := h.clause_ii.terminal_mem
  terminal_unique := h.clause_ii.terminal_unique
  binary_product_closed := h.clause_ii.binary_product_closed
  function_object_closed := h.clause_iii

/-- The valuation-object closure data extracted from clause (iv). -/
theorem MainTheoremObjectwise.valuationObjectClosure
    (h : MainTheoremObjectwise.{u}) :
    FVAValuationObjectClosure.{u} where
  vSub_closed := fun hD => (h.clause_iv hD).1
  vOne_closed := fun hD => (h.clause_iv hD).2

/-! ## Final assembly -/

/-- Strict object-level assembly of source theorem `thm:main`, conditional only
on the two finite-generator statements isolated by the kernel-lifting layer.

The function-space conclusion inherits the audited Gierz exponential theorem;
the actual valuation conclusions inherit the audited Jones continuity theorem.
No paper-internal theorem is assumed here. -/
theorem thm_main_objectwise_of_generators
    (hFiniteFunctions : FiniteFunctionGeneratorsAreFVA.{u})
    (hFiniteDouble : FiniteDoubleValuationGeneratorsAreFVA.{u}) :
    MainTheoremObjectwise.{u} := by
  refine {
    clause_i := ?_
    clause_ii := ?_
    clause_iii := ?_
    clause_iv := ?_ }
  · intro D _ hD
    exact fva_pointed_countablyBased_fs hD
  · refine {
      finite_generators := finiteStage_isFVA_unconditional
      terminal_mem := terminal_isFVA
      terminal_unique := ?_
      retract_closed := ?_
      binary_product_closed := ?_ }
    · intro D _ f
      exact terminalMap_unique D f
    · intro D E _ _ sr hE
      exact IsFVA.retract sr hE
    · intro D E _ _ hD hE
      exact global_product hD hE
  · intro D E _ _ hD hE
    exact global_functionSpace_of_finite_generators
      hFiniteFunctions hD hE
  · intro D _ hD
    exact ⟨global_vSub_of_finite_double_generators hFiniteDouble hD,
      global_vOne_of_finite_double_generators hFiniteDouble hD⟩

end FiniteValuationApproximable
