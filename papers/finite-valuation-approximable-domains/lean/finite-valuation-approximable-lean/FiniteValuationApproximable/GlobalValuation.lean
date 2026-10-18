import FiniteValuationApproximable.ContinuousValuation.Basic
import FiniteValuationApproximable.External.Jones
import FiniteValuationApproximable.Global
import FiniteValuationApproximable.FiniteValuation.Consequences

/-!
# Global transfer for the genuine subprobability valuation functor

This module instantiates the valuation clause of `thm:global-transfer` with
the actual Jones--Plotkin continuous-valuation type.  The only finite
generator input is named explicitly: one more valuation application to each
finite-vector stage must be FVA.  Kernel lifting discharges that input later.
-/

set_option autoImplicit false
set_option linter.unnecessarySimpa false

universe u

namespace FiniteValuationApproximable

open Set
open AbstractApproximation
open AbramskyJung.Chapter2

namespace ContinuousValuation

/-- Functoriality of pushforward, proved directly from Scott-open preimages. -/
theorem pushforward_comp
    {D E F : Type u} [Preorder D] [Preorder E] [Preorder F]
    (f : ScottContFun D E) (g : ScottContFun E F) (mu : VSub D) :
    pushforward g (pushforward f mu) =
      pushforward (ScottContFun.comp g f) mu := by
  apply VSub.ext
  intro U
  change mu (ScottOpen.preimage f f.continuous
      (ScottOpen.preimage g g.continuous U)) =
    mu (ScottOpen.preimage (ScottContFun.comp g f)
      (ScottContFun.comp g f).continuous U)
  congr 1

end ContinuousValuation

/-- The exact finite-generator premise used by the global valuation
transfer.  Its carrier is the actual continuous valuation space over the
finite-vector stage selected by an FVA factorization. -/
def FiniteDoubleValuationGeneratorsAreFVA : Prop :=
  ∀ P : FinitePoset.{u},
    IsFVA.{u, u} (ContinuousValuation.VSub P.VSub)

section ValuationApproximation

variable {X : Type u} [PartialOrder X]

/-- Applying pushforward to an FVA approximate identity produces the outer
approximate identity on the genuine valuation powerdomain.  The directed
supremum calculation is the internally proved `V_local`. -/
noncomputable def valuationPushforwardApproximateIdentity
    (A : IncreasingApproximateIdentity X) :
    IncreasingApproximateIdentity (ContinuousValuation.VSub X) where
  map n := {
    toFun := ContinuousValuation.pushforward (A.map n)
    continuous := ContinuousValuation.pushforward_scottContinuous (A.map n) }
  monotone := by
    intro m n hmn mu
    exact ContinuousValuation.pushforward_mono_map (A.monotone hmn) mu
  below_id := by
    intro n mu
    calc
      ContinuousValuation.pushforward (A.map n) mu ≤
          ContinuousValuation.pushforward
            (ContinuousValuation.idMap (D := X)) mu :=
        ContinuousValuation.pushforward_mono_map (A.below_id n) mu
      _ = mu := ContinuousValuation.pushforward_idMap mu
  pointwise_sup := by
    intro mu
    let maps : Set (ScottContFun X X) := Set.range A.map
    have hMaps : AbramskyJung.Chapter2.DirectedSet maps :=
      directedSet_range_of_monotone A.map A.monotone
    have hBelow : ∀ f ∈ maps, f ≤ ContinuousValuation.idMap := by
      intro f hf
      rcases hf with ⟨n, rfl⟩
      exact A.below_id n
    have hSup : ∀ x : X,
        AbramskyJung.Chapter2.IsSup
          ((fun f : ScottContFun X X => f x) '' maps) x := by
      intro x
      have himage :
          ((fun f : ScottContFun X X => f x) '' maps) =
            Set.range (fun n => A.map n x) := by
        ext z
        constructor
        · rintro ⟨f, ⟨n, rfl⟩, rfl⟩
          exact ⟨n, rfl⟩
        · rintro ⟨n, rfl⟩
          exact ⟨A.map n, ⟨n, rfl⟩, rfl⟩
      rw [himage]
      exact A.pointwise_sup x
    have hLocal := ContinuousValuation.V_local_identity
      hMaps hBelow hSup mu
    have hout :
        ((fun g : ScottContFun X X =>
          ContinuousValuation.pushforward g mu) '' maps) =
          Set.range (fun n =>
            ContinuousValuation.pushforward (A.map n) mu) := by
      ext z
      constructor
      · rintro ⟨g, ⟨n, rfl⟩, rfl⟩
        exact ⟨n, rfl⟩
      · rintro ⟨n, rfl⟩
        exact ⟨A.map n, ⟨n, rfl⟩, rfl⟩
    change AbramskyJung.Chapter2.IsSup
      (Set.range (fun n =>
        ContinuousValuation.pushforward (A.map n) mu)) mu
    rw [← hout]
    exact hLocal.2

/-- Pushforward of one factored approximant factors through the actual
valuation space on its finite-vector stage. -/
noncomputable def valuationPushforwardIntermediateFactorization
    (hFiniteDouble : FiniteDoubleValuationGeneratorsAreFVA.{u})
    (A : FVApproximateIdentity.{u, u} X) (n : Nat) :
    FVAIntermediateFactorization.{u, u}
      ((valuationPushforwardApproximateIdentity
        A.toIncreasingApproximateIdentity).map n) := by
  let F : FiniteValuationFactorization.{u, u, u} (A.map n) :=
    Classical.choice (A.factorable n)
  let encodeMap : ScottContFun X F.stage.VSub := {
    toFun := F.factorization.encode
    continuous := F.factorization.encode_continuous }
  let decodeMap : ScottContFun F.stage.VSub X := {
    toFun := F.factorization.decode
    continuous := F.factorization.decode_continuous }
  let stage : FVAIntermediateStage.{u} := {
    carrier := ContinuousValuation.VSub F.stage.VSub
    partialOrder := inferInstance
    isFVA := hFiniteDouble F.stage }
  refine {
    stage := stage
    factorization := {
      encode := ContinuousValuation.pushforward encodeMap
      decode := ContinuousValuation.pushforward decodeMap
      encode_continuous :=
        ContinuousValuation.pushforward_scottContinuous encodeMap
      decode_continuous :=
        ContinuousValuation.pushforward_scottContinuous decodeMap
      factor := ?_ } }
  intro mu
  rw [ContinuousValuation.pushforward_comp]
  have hcomp : ScottContFun.comp decodeMap encodeMap = A.map n := by
    apply ScottContFun.ext
    funext x
    exact F.factorization.factor x
  rw [hcomp]
  rfl

/-- Unconditional global valuation-transfer pattern once the finite double
valuation generators supplied by kernel lifting are available. -/
theorem global_vSub_of_finite_double_generators
    (hFiniteDouble : FiniteDoubleValuationGeneratorsAreFVA.{u})
    (hX : IsFVA.{u, u} X) :
    IsFVA.{u, u} (ContinuousValuation.VSub X) := by
  rcases hX.2 with ⟨A⟩
  let outer := valuationPushforwardApproximateIdentity
    A.toIncreasingApproximateIdentity
  have hDomain : IsContinuousDcpo (ContinuousValuation.VSub X) :=
    ⟨ContinuousValuation.VSub.isDcpoOrder,
      External.jones_1990_cor_5_4_vSub_continuous hX.1⟩
  apply global_Vsub_conditional
    finiteStagesHaveFSApproximateIdentities hDomain outer
  intro n
  exact ⟨valuationPushforwardIntermediateFactorization
    hFiniteDouble A n⟩

end ValuationApproximation

end FiniteValuationApproximable
