import FiniteValuationApproximable.ContinuousValuation.Finite
import FiniteValuationApproximable.GlobalValuation

/-!
# Transporting genuine finite valuations

The finite stages in the definition of `FVA` are atomic subprobability
vectors, whereas kernel lifting naturally produces the genuine
Jones--Plotkin continuous-valuation spaces.  This file lifts the proved
finite-poset order isomorphism through both the valuation functor and
Scott-continuous function spaces.  No representation is identified by
definitional equality.
-/

set_option autoImplicit false
set_option linter.unnecessarySimpa false

universe u

namespace FiniteValuationApproximable

open AbramskyJung.Chapter2

namespace ContinuousValuation

/-- Pushforward along an order isomorphism is itself an order isomorphism of
genuine continuous subprobability valuation spaces. -/
noncomputable def pushforwardOrderIso
    {D E : Type u} [Preorder D] [Preorder E] (e : D ≃o E) :
    VSub D ≃o VSub E where
  toFun := pushforward {
    toFun := e
    continuous := orderIso_scottContinuous e }
  invFun := pushforward {
    toFun := e.symm
    continuous := orderIso_scottContinuous e.symm }
  left_inv := by
    intro mu
    rw [pushforward_comp]
    have hcomp :
        ScottContFun.comp
            ({ toFun := e.symm
               continuous := orderIso_scottContinuous e.symm } :
              ScottContFun E D)
            ({ toFun := e
               continuous := orderIso_scottContinuous e } :
              ScottContFun D E) =
          idMap (D := D) := by
      apply ScottContFun.ext
      funext x
      exact e.symm_apply_apply x
    rw [hcomp, pushforward_idMap]
  right_inv := by
    intro mu
    rw [pushforward_comp]
    have hcomp :
        ScottContFun.comp
            ({ toFun := e
               continuous := orderIso_scottContinuous e } :
              ScottContFun D E)
            ({ toFun := e.symm
               continuous := orderIso_scottContinuous e.symm } :
              ScottContFun E D) =
          idMap (D := E) := by
      apply ScottContFun.ext
      funext x
      exact e.apply_symm_apply x
    rw [hcomp, pushforward_idMap]
  map_rel_iff' := by
    intro mu nu
    constructor
    · intro h
      let forward : ScottContFun D E := {
        toFun := e
        continuous := orderIso_scottContinuous e }
      let backward : ScottContFun E D := {
        toFun := e.symm
        continuous := orderIso_scottContinuous e.symm }
      have hleft (rho : VSub D) :
          pushforward backward (pushforward forward rho) = rho := by
        rw [pushforward_comp]
        have hcomp : ScottContFun.comp backward forward = idMap (D := D) := by
          apply ScottContFun.ext
          funext x
          exact e.symm_apply_apply x
        rw [hcomp, pushforward_idMap]
      calc
        mu = pushforward backward (pushforward forward mu) := (hleft mu).symm
        _ <= pushforward backward (pushforward forward nu) :=
          pushforward_mono_valuation backward h
        _ = nu := hleft nu
    · intro h
      exact pushforward_mono_valuation _ h

end ContinuousValuation

/-! ## Conjugating Scott-continuous function spaces -/

section FunctionTransport

variable {D D' E E' : Type u}
variable [Preorder D] [Preorder D'] [Preorder E] [Preorder E']

/-- Conjugation by order isomorphisms on the source and target is an order
isomorphism between the corresponding Scott-continuous function spaces. -/
noncomputable def contFunOrderIso
    (eD : D ≃o D') (eE : E ≃o E') :
    AbramskyJung.Chapter3.ContFun D E ≃o
      AbramskyJung.Chapter3.ContFun D' E' where
  toFun f := AbramskyJung.Chapter3.ContFun.comp
    ({ toFun := eE
       continuous := orderIso_scottContinuous eE } :
      AbramskyJung.Chapter3.ContFun E E')
    (AbramskyJung.Chapter3.ContFun.comp f
      ({ toFun := eD.symm
         continuous := orderIso_scottContinuous eD.symm } :
        AbramskyJung.Chapter3.ContFun D' D))
  invFun f := AbramskyJung.Chapter3.ContFun.comp
    ({ toFun := eE.symm
       continuous := orderIso_scottContinuous eE.symm } :
      AbramskyJung.Chapter3.ContFun E' E)
    (AbramskyJung.Chapter3.ContFun.comp f
      ({ toFun := eD
         continuous := orderIso_scottContinuous eD } :
        AbramskyJung.Chapter3.ContFun D D'))
  left_inv := by
    intro f
    apply AbramskyJung.Chapter3.ContFun.ext_apply
    intro x
    simp
  right_inv := by
    intro f
    apply AbramskyJung.Chapter3.ContFun.ext_apply
    intro x
    simp
  map_rel_iff' := by
    intro f g
    constructor
    · intro h x
      have hx := h (eD x)
      exact eE.le_iff_le.mp (by simpa using hx)
    · intro h x
      exact eE.monotone (h (eD.symm x))

/-- Specialization of `contFunOrderIso` to the two representations of
valuations on finite posets. -/
noncomputable def finiteVSubContFunOrderIso
    (P Q : FinitePoset.{u}) :
    AbramskyJung.Chapter3.ContFun P.VSub Q.VSub ≃o
      AbramskyJung.Chapter3.ContFun
        (ContinuousValuation.VSub P)
        (ContinuousValuation.VSub Q) :=
  contFunOrderIso
    (ContinuousValuation.finiteVSubOrderIso (P := P))
    (ContinuousValuation.finiteVSubOrderIso (P := Q))

end FunctionTransport

end FiniteValuationApproximable
