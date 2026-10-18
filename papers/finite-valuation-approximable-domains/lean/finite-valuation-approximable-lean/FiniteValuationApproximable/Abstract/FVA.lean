import FiniteValuationApproximable.Abstract.Approximation
import FiniteValuationApproximable.FiniteValuation.Basic

/-!
# Finite-valuation factorization and approximate identities

This module formalizes the source definitions `def:factorization` and
`def:FVA` from `main17-4b2e65f0f963`, together with the valuation-independent
parts of `lem:generators`, `lem:pointed`, and `cor:retract`.

The finite stages are the concrete finite subprobability vectors from
`FiniteValuation/Basic.lean`.  No general continuous-valuation powerdomain is
postulated here.  In particular, proving that every finite stage is a domain
and carries the erosion FS approximate identity remains a separate theorem,
not a field smuggled into the definition below.
-/

set_option autoImplicit false
set_option linter.unnecessarySimpa false

universe u v w

namespace FiniteValuationApproximable

open AbstractApproximation

/-- A universe-polymorphic bundled finite poset.  Bundling the carrier keeps
the existential finite stage in `FiniteValuationFactorization` first-order and
retains its `Fintype` and `PartialOrder` instances. -/
structure FinitePoset where
  carrier : Type u
  fintype : Fintype carrier
  partialOrder : PartialOrder carrier

namespace FinitePoset

instance : CoeSort FinitePoset.{u} (Type u) where
  coe P := P.carrier

instance (P : FinitePoset.{u}) : Fintype P := P.fintype

instance (P : FinitePoset.{u}) : PartialOrder P := P.partialOrder

/-- The concrete finite subprobability-valuation stage attached to `P`. -/
abbrev VSub (P : FinitePoset.{u}) : Type u :=
  SubprobabilityVector P

end FinitePoset

section Factorization

variable {D : Type u} {E : Type v} [Preorder D] [Preorder E]

/-- Source item `def_factorization`: a Scott-continuous map factors through
the concrete subprobability valuation space of some finite poset. -/
structure FiniteValuationFactorization (f : D -> E) where
  stage : FinitePoset.{w}
  factorization : ScottFactorization f stage.VSub

/-- Propositional form of finite-valuation factorability. -/
def IsFiniteValuationFactorable (f : D -> E) : Prop :=
  Nonempty (FiniteValuationFactorization.{u, v, w} f)

namespace FiniteValuationFactorization

variable {f : D -> E}

theorem continuous (F : FiniteValuationFactorization.{u, v, w} f) :
    AbramskyJung.Chapter2.ScottContinuous f :=
  F.factorization.continuous

/-- Composition on the source side preserves the finite valuation stage. -/
def precomp
    {C : Type w} [Preorder C]
    (F : FiniteValuationFactorization.{u, v, u} f)
    (g : C -> D) (hg : AbramskyJung.Chapter2.ScottContinuous g) :
    FiniteValuationFactorization.{w, v, u} (fun x => f (g x)) where
  stage := F.stage
  factorization := {
    encode := fun x => F.factorization.encode (g x)
    decode := F.factorization.decode
    encode_continuous := F.factorization.encode_continuous.comp hg
    decode_continuous := F.factorization.decode_continuous
    factor := fun x => by rw [F.factorization.factor]
  }

/-- Composition on the target side preserves the finite valuation stage. -/
def postcomp
    {C : Type w} [Preorder C]
    (F : FiniteValuationFactorization.{u, v, u} f)
    (g : E -> C) (hg : AbramskyJung.Chapter2.ScottContinuous g) :
    FiniteValuationFactorization.{u, w, u} (fun x => g (f x)) where
  stage := F.stage
  factorization := {
    encode := F.factorization.encode
    decode := fun b => g (F.factorization.decode b)
    encode_continuous := F.factorization.encode_continuous
    decode_continuous := hg.comp F.factorization.decode_continuous
    factor := fun x => by rw [F.factorization.factor]
  }

end FiniteValuationFactorization

end Factorization

section ApproximateIdentity

variable (D : Type u) [Preorder D]

/-- Source item `def_FVA`: an increasing sequence of self-maps below the
identity, with pointwise supremum the identity, each factoring through the
subprobability valuations of a finite poset. -/
structure FVApproximateIdentity
    extends IncreasingApproximateIdentity D where
  factorable : forall n : Nat,
    IsFiniteValuationFactorable.{u, u, w} (map n)

/-- The source class `FVA`: a domain equipped with a finite-valuation
approximate identity.  The domain requirement is kept in the proposition and
is not inferred merely from the existence of the factorization sequence. -/
def IsFVA [PartialOrder D] : Prop :=
  AbramskyJung.Chapter2.IsContinuousDcpo D ∧
    Nonempty (FVApproximateIdentity.{u, w} D)

namespace FVApproximateIdentity

variable {D : Type u} [Preorder D]

theorem map_continuous
    (A : FVApproximateIdentity.{u, w} D) (n : Nat) :
    AbramskyJung.Chapter2.ScottContinuous (A.map n) :=
  (A.map n).continuous

theorem map_factorable
    (A : FVApproximateIdentity.{u, w} D) (n : Nat) :
    IsFiniteValuationFactorable.{u, u, w} (A.map n) :=
  A.factorable n

end FVApproximateIdentity

end ApproximateIdentity

section FiniteStages

/-- The zero finite subprobability vector. -/
def zeroVector (P : Type u) [Fintype P] : SubprobabilityVector P where
  coeff := fun _ => 0
  coeff_nonneg := fun _ => le_rfl
  total_le_one := by simp

@[simp]
theorem zeroVector_apply (P : Type u) [Fintype P] (x : P) :
    zeroVector P x = 0 :=
  rfl

@[simp]
theorem zeroVector_mass
    (P : Type u) [Fintype P] (A : Set P) :
    (zeroVector P).mass A = 0 := by
  classical
  simp [zeroVector, SubprobabilityVector.mass]

theorem zeroVector_le
    (P : Type u) [Fintype P] [PartialOrder P]
    (p : SubprobabilityVector P) :
    zeroVector P <= p := by
  intro U
  simp [upperMass, p.mass_nonneg]

/-- The identity of a finite valuation stage factors through that same stage.
This is the factorization component of source item `lem_generators`; the
separate domain/FS assertions are supplied by the finite-stage development. -/
def finiteStageIdentityFactorization (P : FinitePoset.{u}) :
    FiniteValuationFactorization.{u, u, u}
      (fun x : P.VSub => x) where
  stage := P
  factorization := {
    encode := fun x => x
    decode := fun x => x
    encode_continuous := AbramskyJung.Chapter2.scottContinuous_id
    decode_continuous := AbramskyJung.Chapter2.scottContinuous_id
    factor := fun _ => rfl
  }

/-- The constant identity sequence is a finite-valuation approximate identity
on every finite valuation stage.  This theorem deliberately makes no claim
that the stochastic simplex has already been proved a continuous dcpo. -/
def finiteStageApproximateIdentity (P : FinitePoset.{u}) :
    FVApproximateIdentity.{u, u} P.VSub where
  map := fun _ => {
    toFun := fun x => x
    continuous := AbramskyJung.Chapter2.scottContinuous_id
  }
  monotone := fun _ _ _ _ => le_rfl
  below_id := fun _ _ => le_rfl
  pointwise_sup := by
    intro x
    simpa using AbramskyJung.Chapter2.isSup_singleton x
  factorable := fun _ => Nonempty.intro (finiteStageIdentityFactorization P)

/-- Source item `lem_generators`, with its only semantic premise exposed: once
the concrete stochastic simplex has been proved a continuous dcpo, its
constant identity factorization is an FVA witness.  The standalone
finite-valuation domain theorem is supplied separately rather than hidden in
this declaration. -/
theorem finiteStage_isFVA (P : FinitePoset.{u})
    (hP : AbramskyJung.Chapter2.IsContinuousDcpo P.VSub) :
    IsFVA.{u, u} P.VSub :=
  ⟨hP, ⟨finiteStageApproximateIdentity P⟩⟩

end FiniteStages

section Pointedness

variable {D : Type u} [Preorder D]

/-- Source item `lem_pointed`, approximation-data form: the reconstruction of
the zero valuation at any one finite stage is a least element of `D`. -/
theorem FVApproximateIdentity.hasLeastElement
    (A : FVApproximateIdentity.{u, w} D) :
    AbramskyJung.Chapter3.HasLeastElement D := by
  rcases A.factorable 0 with ⟨F⟩
  let bottom : D := F.factorization.decode (zeroVector F.stage)
  refine ⟨bottom, ?_⟩
  intro x
  calc
    bottom <= F.factorization.decode (F.factorization.encode x) :=
      F.factorization.decode_continuous.monotone
        (zeroVector_le F.stage (F.factorization.encode x))
    _ = A.map 0 x := F.factorization.factor x
    _ <= x := A.below_id 0 x

/-- Exact source-facing pointedness conclusion for an FVA object. -/
theorem IsFVA.hasLeastElement
    [PartialOrder D] (hD : IsFVA.{u, w} D) :
    AbramskyJung.Chapter3.HasLeastElement D := by
  rcases hD.2 with ⟨A⟩
  exact A.hasLeastElement

end Pointedness

section Retracts

variable {D : Type u} {E : Type v} [Preorder D] [Preorder E]

/-- Pull a finite-valuation approximate identity back along a continuous
section--retraction pair.  Each pulled-back map factors through the same
finite valuation stage as the original map. -/
def FVApproximateIdentity.pullback
    (A : FVApproximateIdentity.{v, w} E)
    (sr : AbramskyJung.Chapter3.ContinuousSectionRetractionPair D E) :
    FVApproximateIdentity.{u, w} D where
  toIncreasingApproximateIdentity :=
    A.toIncreasingApproximateIdentity.pullback sr
  factorable := by
    intro n
    rcases A.factorable n with ⟨F⟩
    exact ⟨{
      stage := F.stage
      factorization := F.factorization.pullback sr
    }⟩

/-- Source item `cor_retract`: FVA is closed under Scott-continuous retracts.
The domain component is inherited by Theorem 3.1.4, and the approximation
component by `FVApproximateIdentity.pullback`. -/
theorem IsFVA.retract
    [PartialOrder D] [PartialOrder E]
    (sr : AbramskyJung.Chapter3.ContinuousSectionRetractionPair D E)
    (hE : IsFVA.{v, w} E) : IsFVA.{u, w} D := by
  refine ⟨AbramskyJung.Chapter3.theorem_3_1_4_retract_continuous_domain
    sr hE.1, ?_⟩
  rcases hE.2 with ⟨A⟩
  exact ⟨A.pullback sr⟩

end Retracts

end FiniteValuationApproximable
