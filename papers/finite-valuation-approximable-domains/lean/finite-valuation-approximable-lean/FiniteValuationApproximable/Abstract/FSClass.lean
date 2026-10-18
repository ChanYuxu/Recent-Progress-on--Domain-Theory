import FiniteValuationApproximable.Abstract.FiniteScott
import FiniteValuationApproximable.FiniteValuation.StageFS

/-!
# The source-level class of FS-domains

This file packages the manuscript's unpointed definition of an FS-domain:
a dcpo order equipped with a directed family of Scott-continuous endomaps,
each finitely separated from the identity, whose pointwise supremum is the
identity.  The continuous-domain property is derived from that data rather
than inserted as a separate assumption.

It also proves invariance under order isomorphism.  That transport is needed
to apply the external FS exponential theorem to the manuscript's concrete
`MonotoneTable` representation without treating a representation change as
an axiom.
-/

set_option autoImplicit false
set_option linter.unnecessarySimpa false

universe u v

namespace FiniteValuationApproximable

open Set
open AbstractApproximation

/-- Source Definition `def:FS`, expressed with the local dcpo and finite-
separation APIs. -/
def IsFSDomain (D : Type u) [Preorder D] : Prop :=
  AbramskyJung.Chapter2.IsDcpoOrder D ∧
    Nonempty (DirectedFSApproximateIdentity D)

/-- The sequential specialization used throughout the FVA construction. -/
def IsSequentialFSDomain (D : Type u) [Preorder D] : Prop :=
  AbramskyJung.Chapter2.IsDcpoOrder D ∧
    Nonempty (FSApproximateIdentity D)

namespace IsFSDomain

variable {D : Type u} [Preorder D]

theorem isDcpoOrder (hD : IsFSDomain D) :
    AbramskyJung.Chapter2.IsDcpoOrder D :=
  hD.1

theorem hasDirectedFSApproximateIdentity (hD : IsFSDomain D) :
    Nonempty (DirectedFSApproximateIdentity D) :=
  hD.2

/-- An FS-domain is a continuous dcpo; continuity follows internally from
the finite-separation witnesses. -/
theorem isContinuousDcpo (hD : IsFSDomain D) :
    AbramskyJung.Chapter2.IsContinuousDcpo D := by
  rcases hD.2 with ⟨A⟩
  exact ⟨hD.1, A.continuousDomain⟩

end IsFSDomain

namespace IsSequentialFSDomain

variable {D : Type u} [Preorder D]

theorem toIsFSDomain (hD : IsSequentialFSDomain D) : IsFSDomain D := by
  rcases hD.2 with ⟨A⟩
  exact ⟨hD.1, ⟨A.toDirected⟩⟩

theorem isOmegaContinuousDcpo (hD : IsSequentialFSDomain D) :
    AbramskyJung.Chapter2.IsOmegaContinuousDcpo D := by
  rcases hD.2 with ⟨A⟩
  exact A.omegaContinuousDcpo hD.1

end IsSequentialFSDomain

namespace AbstractApproximation
namespace FSApproximateIdentity

variable {D : Type u} [Preorder D]

theorem isSequentialFSDomain (A : FSApproximateIdentity D)
    (hD : AbramskyJung.Chapter2.IsDcpoOrder D) :
    IsSequentialFSDomain D :=
  ⟨hD, ⟨A⟩⟩

theorem isFSDomain (A : FSApproximateIdentity D)
    (hD : AbramskyJung.Chapter2.IsDcpoOrder D) :
    IsFSDomain D :=
  (A.isSequentialFSDomain hD).toIsFSDomain

end FSApproximateIdentity
end AbstractApproximation

/-! ## Transport across order isomorphisms -/

section Transport

variable {D : Type u} {E : Type v} [Preorder D] [Preorder E]

/-- Order isomorphisms preserve every existing directed supremum. -/
theorem fsOrderIso_scottContinuous (e : D ≃o E) :
    AbramskyJung.Chapter2.ScottContinuous e := by
  constructor
  · exact e.monotone
  · intro A x hA hx
    constructor
    · rintro _ ⟨a, ha, rfl⟩
      exact e.monotone (hx.1 ha)
    · intro y hy
      have hUpper : AbramskyJung.Chapter2.IsUpperBound A (e.symm y) := by
        intro a ha
        apply e.le_iff_le.mp
        simpa using hy ⟨a, ha, rfl⟩
      have hxy : x ≤ e.symm y := hx.2 (e.symm y) hUpper
      simpa using e.monotone hxy

/-- Conjugate a Scott-continuous endomap across an order isomorphism. -/
def conjugateScottContFun (e : D ≃o E)
    (f : AbramskyJung.Chapter2.ScottContFun E E) :
    AbramskyJung.Chapter2.ScottContFun D D where
  toFun x := e.symm (f (e x))
  continuous :=
    (fsOrderIso_scottContinuous e.symm).comp
      (f.continuous.comp (fsOrderIso_scottContinuous e))

theorem conjugateScottContFun_mono (e : D ≃o E) :
    Monotone (conjugateScottContFun e) := by
  intro f g hfg x
  exact e.symm.monotone (hfg (e x))

namespace AbstractApproximation
namespace DirectedFSApproximateIdentity

/-- A directed FS approximate identity transports across an order
isomorphism, including its finite separators. -/
def transport (e : D ≃o E)
    (A : DirectedFSApproximateIdentity E) :
    DirectedFSApproximateIdentity D where
  maps := conjugateScottContFun e '' A.maps
  directed := AbramskyJung.Chapter2.DirectedSet.image
    (conjugateScottContFun_mono e) A.directed
  finitelySeparated := by
    intro g hg
    rcases hg with ⟨f, hf, rfl⟩
    rcases A.finitelySeparated f hf with ⟨M, hMfinite, hM⟩
    refine ⟨e.symm '' M, hMfinite.image e.symm, ?_⟩
    intro x
    rcases hM (e x) with ⟨m, hmM, hfm, hme⟩
    refine ⟨e.symm m, ⟨m, hmM, rfl⟩, ?_, ?_⟩
    · exact e.symm.monotone hfm
    · simpa using e.symm.monotone hme
  pointwise_sup := by
    intro x
    constructor
    · rintro y ⟨g, ⟨f, hf, rfl⟩, rfl⟩
      have hle : f (e x) ≤ e x :=
        (A.pointwise_sup (e x)).1 ⟨f, hf, rfl⟩
      simpa using e.symm.monotone hle
    · intro y hy
      have hex : e x ≤ e y :=
        (A.pointwise_sup (e x)).2 (e y) (by
          rintro z ⟨f, hf, rfl⟩
          have hfy : e.symm (f (e x)) ≤ y :=
            hy ⟨conjugateScottContFun e f, ⟨f, hf, rfl⟩, rfl⟩
          simpa using e.monotone hfy)
      simpa using e.symm.monotone hex

end DirectedFSApproximateIdentity
end AbstractApproximation

/-- Directed completeness and antisymmetry transport across an order
isomorphism. -/
theorem isDcpoOrder_of_orderIso (e : D ≃o E)
    (hE : AbramskyJung.Chapter2.IsDcpoOrder E) :
    AbramskyJung.Chapter2.IsDcpoOrder D := by
  constructor
  · intro S hS
    have heS : AbramskyJung.Chapter2.DirectedSet (e '' S) :=
      AbramskyJung.Chapter2.DirectedSet.image e.monotone hS
    rcases hE.1 (e '' S) heS with ⟨y, hy⟩
    refine ⟨e.symm y, ?_⟩
    constructor
    · intro x hx
      have hxy : e x ≤ y := hy.1 ⟨x, hx, rfl⟩
      simpa using e.symm.monotone hxy
    · intro z hz
      have hyz : y ≤ e z := hy.2 (e z) (by
        rintro _ ⟨x, hx, rfl⟩
        exact e.monotone (hz hx))
      simpa using e.symm.monotone hyz
  · intro x y hxy hyx
    apply e.injective
    exact hE.2 (e x) (e y) (e.monotone hxy) (e.monotone hyx)

/-- FS-domain structure is invariant under order isomorphism. -/
theorem IsFSDomain.of_orderIso (e : D ≃o E) (hE : IsFSDomain E) :
    IsFSDomain D := by
  rcases hE.2 with ⟨A⟩
  exact ⟨isDcpoOrder_of_orderIso e hE.1, ⟨A.transport e⟩⟩

end Transport

/-! ## Internally proved base instances -/

section Instances

variable (D : Type u) [Fintype D] [PartialOrder D]

theorem finite_isFSDomain : IsFSDomain D :=
  (finiteFSApproximateIdentity D).isFSDomain (finite_isDcpoOrder D)

end Instances

namespace Erosion

variable {P : Type u} [Fintype P] [PartialOrder P]

theorem finiteSubprobability_isFSDomain :
    IsFSDomain (SubprobabilityVector P) :=
  finiteSubprobabilityFSApproximateIdentity.isFSDomain
    finiteSubprobability_isDcpoOrder

end Erosion

end FiniteValuationApproximable
