import FiniteValuationApproximable.Abstract.FVA

/-!
# Saturating finite-valuation approximate identities

This file formalizes the valuation-independent construction in part (i) of
source item `thm:saturation` (source lines 1511--1566 of
`main17-4b2e65f0f963`).  The only remaining semantic input is stated openly:
every concrete finite subprobability stage must carry an FS approximate
identity.  `FiniteValuation/Erosion.lean` is responsible for discharging that
input; it is not encoded as a field of a valuation or factorization object.

Under that input, the proof constructs the sandwiched maps
`hᵢⱼ = eᵢ ∘ qᵢⱼ ∘ pᵢ`, applies the already formalized square-refinement
lemma, and proves that every selected square still factors through the same
finite valuation stage.  Thus the result is an exact conditional form of
`thm:saturation(i)`, not an unconditional claim that the erosion theorem has
already been proved.
-/

set_option autoImplicit false
set_option linter.unnecessarySimpa false

universe u w

namespace FiniteValuationApproximable

open AbstractApproximation

abbrev ScottContFun
    (X : Type u) (Y : Type w) [Preorder X] [Preorder Y] :=
  AbramskyJung.Chapter2.ScottContFun X Y

/-- The explicit semantic premise needed by the saturation construction:
each concrete finite subprobability stage has a sequential FS approximate
identity. -/
def FiniteStagesHaveFSApproximateIdentities : Prop :=
  ∀ P : FinitePoset.{u},
    Nonempty (FSApproximateIdentity P.VSub)

/-- An FVA approximate identity all of whose members are finitely separated.
This is the data asserted to exist in `thm:saturation(i)`. -/
structure SaturatedFVApproximateIdentity
    (D : Type u) [Preorder D] extends FVApproximateIdentity.{u, w} D where
  finitelySeparated :
    ∀ n : Nat, IsFinitelySeparated (map n)

namespace SaturatedFVApproximateIdentity

variable {D : Type u} [Preorder D]

/-- Forget finite-valuation factorability, retaining the FS approximate
identity. -/
def toFSApproximateIdentity
    (A : SaturatedFVApproximateIdentity.{u, w} D) :
    FSApproximateIdentity D where
  toIncreasingApproximateIdentity :=
    A.toFVApproximateIdentity.toIncreasingApproximateIdentity
  finitelySeparated := A.finitelySeparated

end SaturatedFVApproximateIdentity

section SandwichedRefinement

variable {D : Type u} [Preorder D]
variable {f : D → D}

/-- The source construction `e ∘ q ∘ p`, bundled as a Scott-continuous map. -/
noncomputable def sandwichedMap
    (F : FiniteValuationFactorization.{u, u, w} f)
    (Q : FSApproximateIdentity F.stage.VSub) (j : Nat) :
    ScottContFun D D where
  toFun := fun x =>
    F.factorization.decode
      (Q.map j (F.factorization.encode x))
  continuous :=
    F.factorization.decode_continuous.comp
      ((Q.map j).continuous.comp F.factorization.encode_continuous)

theorem sandwichedMap_monotone
    (F : FiniteValuationFactorization.{u, u, w} f)
    (Q : FSApproximateIdentity F.stage.VSub) {j k : Nat}
    (hjk : j ≤ k) (x : D) :
    sandwichedMap F Q j x ≤ sandwichedMap F Q k x := by
  exact F.factorization.decode_continuous.monotone
    (Q.monotone hjk (F.factorization.encode x))

theorem sandwichedMap_below
    (F : FiniteValuationFactorization.{u, u, w} f)
    (Q : FSApproximateIdentity F.stage.VSub)
    (hf : ∀ x : D, f x ≤ x) (j : Nat) (x : D) :
    sandwichedMap F Q j x ≤ x := by
  calc
    sandwichedMap F Q j x ≤
        F.factorization.decode (F.factorization.encode x) :=
      F.factorization.decode_continuous.monotone
        (Q.below_id j (F.factorization.encode x))
    _ = f x := F.factorization.factor x
    _ ≤ x := hf x

theorem sandwichedMap_finitelySeparated
    (F : FiniteValuationFactorization.{u, u, w} f)
    (Q : FSApproximateIdentity F.stage.VSub)
    (hf : ∀ x : D, f x ≤ x) (j : Nat) :
    IsFinitelySeparated (sandwichedMap F Q j) := by
  apply IsFinitelySeparated.sandwich (Q.finitelySeparated j)
    F.factorization.decode_continuous.monotone
  intro x
  rw [F.factorization.factor]
  exact hf x

/-- The sandwiched map still factors through the same finite valuation stage. -/
noncomputable def sandwichedMapFactorization
    (F : FiniteValuationFactorization.{u, u, w} f)
    (Q : FSApproximateIdentity F.stage.VSub) (j : Nat) :
    FiniteValuationFactorization.{u, u, w} (sandwichedMap F Q j) where
  stage := F.stage
  factorization := {
    encode := F.factorization.encode
    decode := fun b => F.factorization.decode (Q.map j b)
    encode_continuous := F.factorization.encode_continuous
    decode_continuous :=
      F.factorization.decode_continuous.comp (Q.map j).continuous
    factor := fun _ => rfl
  }

theorem sandwichedMap_pointwise_isSup
    (F : FiniteValuationFactorization.{u, u, w} f)
    (Q : FSApproximateIdentity F.stage.VSub) (x : D) :
    AbramskyJung.Chapter2.IsSup
      (Set.range (fun j => sandwichedMap F Q j x)) (f x) := by
  have hmapped := F.factorization.decode_continuous.maps_isSup
    (Q.range_directed (F.factorization.encode x))
    (Q.pointwise_sup (F.factorization.encode x))
  have hrange :
      Set.range (fun j => sandwichedMap F Q j x) =
        F.factorization.decode ''
          Set.range (fun j => Q.map j (F.factorization.encode x)) := by
    ext y
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨Q.map j (F.factorization.encode x), ⟨j, rfl⟩, rfl⟩
    · rintro ⟨b, ⟨j, rfl⟩, rfl⟩
      exact ⟨j, rfl⟩
  rw [hrange]
  simpa only [F.factorization.factor x] using hmapped

end SandwichedRefinement

section Saturation

variable {D : Type u} [PartialOrder D]

/-- Exact conditional form of source item `thm:saturation(i)`.  Once the
finite-stage erosion theorem supplies
`FiniteStagesHaveFSApproximateIdentities`, every FVA approximate identity can
be replaced by one whose members are finitely separated while retaining
finite-valuation factorability. -/
theorem FVApproximateIdentity.saturate
    (hStages : FiniteStagesHaveFSApproximateIdentities.{w})
    (hD : AbramskyJung.Chapter2.IsContinuousDomain D)
    (A : FVApproximateIdentity.{u, w} D) :
    Nonempty (SaturatedFVApproximateIdentity.{u, w} D) := by
  let F : ∀ i : Nat,
      FiniteValuationFactorization.{u, u, w} (A.map i) :=
    fun i => Classical.choice (A.factorable i)
  let Q : ∀ i : Nat, FSApproximateIdentity (F i).stage.VSub :=
    fun i => Classical.choice (hStages (F i).stage)
  let N : NestedApproximation D := {
    outer := A.toIncreasingApproximateIdentity
    inner := fun i j => sandwichedMap (F i) (Q i) j
    inner_monotone := by
      intro i j k hjk
      intro x
      exact sandwichedMap_monotone (F i) (Q i) hjk x
    inner_below_id := by
      intro i j x
      exact sandwichedMap_below (F i) (Q i) (A.below_id i) j x
    inner_pointwise_sup := by
      intro i x
      exact sandwichedMap_pointwise_isSup (F i) (Q i) x
    inner_finitelySeparated := by
      intro i j
      exact sandwichedMap_finitelySeparated
        (F i) (Q i) (A.below_id i) j
  }
  rcases N.existsSquaredFSApproximateIdentity hD with ⟨C, hCmem⟩
  refine ⟨{
    toFVApproximateIdentity := {
      toIncreasingApproximateIdentity :=
        C.toIncreasingApproximateIdentity
      factorable := ?_
    }
    finitelySeparated := C.finitelySeparated
  }⟩
  intro n
  rcases hCmem n with ⟨⟨i, j⟩, hij⟩
  have hfactor :=
    (sandwichedMapFactorization (F i) (Q i) j).factorization.square
  refine ⟨{
    stage := (F i).stage
    factorization := ?_
  }⟩
  have hijfun :
      (fun x => sandwichedMap (F i) (Q i) j
        (sandwichedMap (F i) (Q i) j x)) = C.map n := by
    funext x
    have hx := congrArg (fun g : ScottContFun D D => g x) hij
    simpa only [N, AbstractApproximation.squareMap_apply] using hx
  rw [← hijfun]
  exact hfactor

/-- Source-facing conditional consequence of `thm:saturation(i)`. -/
theorem IsFVA.saturated
    (hStages : FiniteStagesHaveFSApproximateIdentities.{w})
    (hD : IsFVA.{u, w} D) :
    Nonempty (SaturatedFVApproximateIdentity.{u, w} D) := by
  rcases hD.2 with ⟨A⟩
  exact A.saturate hStages hD.1.hasBasis

end Saturation

end FiniteValuationApproximable
