import FiniteValuationApproximable.Abstract.FVA

/-!
# The finite-poset analogue of FVA is sequential RB

This file formalizes the active mathematical remark
`rem:finite-poset-RB` (source lines 1367--1398 of
`main17-4b2e65f0f963`) at its exact sequential core.  A self-map factors
through a finite poset if and only if it is a finite-image Scott-continuous
map; hence an increasing approximate identity of such factorizations is the
same data as a sequential RB approximate identity.

The manuscript's further identification with *countably based* RB-domains
uses the standard theorem that a countably based directed approximation can
be thinned to a sequence.  That theorem is not needed for the equivalence of
the two concrete sequential presentations proved here, and is not silently
assumed.
-/

set_option autoImplicit false
set_option linter.unnecessarySimpa false

universe u v

namespace FiniteValuationApproximable

/-- A deflation for the local, self-contained RB comparison: a
Scott-continuous finite-image map below the identity.  As in the manuscript,
idempotence is not required. -/
structure Deflation (D : Type u) [Preorder D] where
  toContFun : AbramskyJung.Chapter2.ScottContFun D D
  finite_range : (Set.range toContFun).Finite
  below : ∀ x : D, toContFun x ≤ x

namespace Deflation

variable {D : Type u} [Preorder D]

instance : CoeFun (Deflation D) (fun _ => D → D) where
  coe d := d.toContFun

instance : LE (Deflation D) where
  le d e := ∀ x, d x ≤ e x

instance : Preorder (Deflation D) where
  le_refl d x := le_rfl
  le_trans d e f hde hef x := le_trans (hde x) (hef x)

theorem scottContinuous (d : Deflation D) :
    AbramskyJung.Chapter2.ScottContinuous d :=
  d.toContFun.continuous

end Deflation

/-- Directed-family RB witness, defined locally so this manuscript has no
dependency on the separate RB-function-space project. -/
def IsRBDomain (D : Type u) [Preorder D] : Prop :=
  ∃ maps : Set (Deflation D),
    AbramskyJung.Chapter2.DirectedSet maps ∧
      ∀ x : D, AbramskyJung.Chapter2.IsSup
        ((fun d : Deflation D => d x) '' maps) x

section FinitePosetFactorization

variable {D : Type u} {E : Type v} [Preorder D] [Preorder E]

/-- Factorization of a map through an ordinary finite poset, rather than
through its subprobability-valuation space. -/
structure FinitePosetFactorization (f : D → E) where
  stage : FinitePoset.{u}
  factorization : AbstractApproximation.ScottFactorization f stage

def IsFinitePosetFactorable (f : D → E) : Prop :=
  Nonempty (FinitePosetFactorization f)

variable {f : D → D}

/-- A finite-poset factorization below the identity has finite image, hence is
a deflation in the manuscript's RB convention. -/
noncomputable def FinitePosetFactorization.toDeflation
    (F : FinitePosetFactorization f) (hbelow : ∀ x : D, f x ≤ x) :
    Deflation D where
  toContFun := {
    toFun := f
    continuous := F.factorization.continuous
  }
  finite_range := by
    apply (Set.finite_univ.image F.factorization.decode).subset
    rintro y ⟨x, rfl⟩
    exact ⟨F.factorization.encode x, Set.mem_univ _,
      F.factorization.factor x⟩
  below := hbelow

end FinitePosetFactorization

section SequentialPresentations

variable (D : Type u) [Preorder D]

/-- An increasing approximate identity whose members factor through ordinary
finite posets. -/
structure FinitePosetApproximateIdentity
    extends AbstractApproximation.IncreasingApproximateIdentity D where
  factorable : ∀ n : Nat, IsFinitePosetFactorable (map n)

/-- A sequential RB approximate identity.  Each member is already bundled as
a Scott-continuous finite-image deflation. -/
structure SequentialRBApproximateIdentity where
  map : Nat → Deflation D
  monotone : Monotone map
  pointwise_sup :
    ∀ x : D, AbramskyJung.Chapter2.IsSup
      (Set.range (fun n => map n x)) x

namespace FinitePosetApproximateIdentity

variable {D : Type u} [Preorder D]

/-- Forget the chosen finite stage and retain the induced deflation. -/
noncomputable def toSequentialRB (A : FinitePosetApproximateIdentity D) :
    SequentialRBApproximateIdentity D where
  map n := (Classical.choice (A.factorable n)).toDeflation
    (A.below_id n)
  monotone := by
    intro m n hmn x
    exact A.monotone hmn x
  pointwise_sup := A.pointwise_sup

end FinitePosetApproximateIdentity

namespace SequentialRBApproximateIdentity

variable {D : Type u} [Preorder D]

/-- Every sequential RB approximate identity is, in particular, an RB-domain
witness in the directed-family interface. -/
theorem isRBDomain (A : SequentialRBApproximateIdentity D) :
    IsRBDomain D := by
  refine ⟨Set.range A.map, ?_, ?_⟩
  · exact AbstractApproximation.directedSet_range_of_monotone
      A.map A.monotone
  · intro x
    have himage :
        (fun d : Deflation D => d x) '' Set.range A.map =
          Set.range (fun n => A.map n x) := by
      ext y
      constructor
      · rintro ⟨d, ⟨n, rfl⟩, rfl⟩
        exact ⟨n, rfl⟩
      · rintro ⟨n, rfl⟩
        exact ⟨A.map n, ⟨n, rfl⟩, rfl⟩
    rw [himage]
    exact A.pointwise_sup x

end SequentialRBApproximateIdentity

end SequentialPresentations

section DeflationImage

variable {D : Type u} [PartialOrder D]

/-- The finite image of a deflation, ordered as a subtype of its source. -/
noncomputable def deflationImageStage
    (d : Deflation D) : FinitePoset.{u} where
  carrier := {y : D // y ∈ Set.range d}
  fintype := d.finite_range.fintype
  partialOrder := inferInstance

noncomputable def deflationImageEncode
    (d : Deflation D) (x : D) : deflationImageStage d :=
  ⟨d x, ⟨x, rfl⟩⟩

noncomputable def deflationImageDecode
    (d : Deflation D) (y : deflationImageStage d) : D :=
  y.1

theorem deflationImageEncode_continuous
    (d : Deflation D) :
    AbramskyJung.Chapter2.ScottContinuous
      (deflationImageEncode d) := by
  constructor
  · intro x y hxy
    exact d.scottContinuous.monotone hxy
  · intro A x hA hx
    have hdsup := d.scottContinuous.maps_isSup hA hx
    constructor
    · intro y hy
      rcases hy with ⟨a, ha, rfl⟩
      exact d.scottContinuous.monotone (hx.1 ha)
    · intro y hy
      apply hdsup.2 y.1
      intro z hz
      rcases hz with ⟨a, ha, rfl⟩
      exact hy (a := deflationImageEncode d a) ⟨a, ha, rfl⟩

theorem deflationImageDecode_continuous
    (d : Deflation D) :
    AbramskyJung.Chapter2.ScottContinuous
      (deflationImageDecode d) := by
  constructor
  · intro x y hxy
    exact hxy
  · intro A x hA hx
    constructor
    · intro y hy
      rcases hy with ⟨a, ha, rfl⟩
      exact hx.1 ha
    · intro y hy
      have hAfinite : A.Finite := Set.toFinite A
      rcases AbramskyJung.Chapter2.DirectedSet.exists_upper_finite
          hA hAfinite
          (fun _ h => h) with ⟨m, hmA, hmUpper⟩
      have hxm : x = m := le_antisymm
        (hx.2 m hmUpper) (hx.1 hmA)
      rw [hxm]
      exact hy ⟨m, hmA, rfl⟩

/-- A deflation factors through its finite image without requiring an
idempotence equation. -/
noncomputable def deflationFinitePosetFactorization
    (d : Deflation D) :
    FinitePosetFactorization (fun x => d x) where
  stage := deflationImageStage d
  factorization := {
    encode := deflationImageEncode d
    decode := deflationImageDecode d
    encode_continuous := deflationImageEncode_continuous d
    decode_continuous := deflationImageDecode_continuous d
    factor := fun _ => rfl
  }

/-- Convert a sequential RB approximation into the finite-poset
factorization presentation. -/
noncomputable def SequentialRBApproximateIdentity.toFinitePoset
    (A : SequentialRBApproximateIdentity D) :
    FinitePosetApproximateIdentity D where
  map n := (A.map n).toContFun
  monotone := A.monotone
  below_id := fun n => (A.map n).below
  pointwise_sup := A.pointwise_sup
  factorable := fun n =>
    ⟨deflationFinitePosetFactorization (A.map n)⟩

end DeflationImage

section Equivalence

variable {D : Type u} [PartialOrder D]

/-- Exact sequential core of source remark `rem:finite-poset-RB`. -/
theorem finitePosetApproximation_iff_sequentialRB :
    Nonempty (FinitePosetApproximateIdentity D) ↔
      Nonempty (SequentialRBApproximateIdentity D) := by
  constructor
  · rintro ⟨A⟩
    exact ⟨A.toSequentialRB⟩
  · rintro ⟨A⟩
    exact ⟨A.toFinitePoset⟩

end Equivalence

end FiniteValuationApproximable
