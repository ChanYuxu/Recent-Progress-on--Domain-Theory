import FiniteValuationApproximable.Abstract.CountableBasis

/-!
# FS approximate identities generate continuous domains

This module closes the abstract implication that is often left implicit in
the manuscript: once a sequential FS approximate identity has actually been
constructed, its pointwise approximation chains themselves form a raw basis.
Together with the finite-separator basis from `CountableBasis.lean`, this also
gives omega continuity without adding a separate continuity premise.
-/

set_option autoImplicit false

universe u

namespace FiniteValuationApproximable

open Set
open AbramskyJung.Chapter2

namespace AbstractApproximation
namespace FSApproximateIdentity

variable {D : Type u} [Preorder D]

/-- A sequential FS approximate identity directly supplies a continuous-domain
basis: at `x`, use the directed range `f_n(x)`, whose members are way-below
`x` by finite separation and whose supremum is `x` by the approximate-identity
law. -/
theorem continuousDomain (A : FSApproximateIdentity D) :
    AbramskyJung.Chapter2.IsContinuousDomain D := by
  refine ⟨Set.univ, ?_⟩
  intro x
  refine ⟨Set.range (fun n => A.map n x), ?_, A.range_directed x,
    A.pointwise_sup x⟩
  rintro y ⟨n, rfl⟩
  exact ⟨Set.mem_univ _,
    IsFinitelySeparated.wayBelow
      (A.map n).continuous (A.finitelySeparated n) x⟩

/-- The separator basis of an FS approximate identity is countable and is a
basis, with no caller-supplied continuity premise. -/
theorem omegaContinuousDomain (A : FSApproximateIdentity D) :
    AbramskyJung.Chapter2.IsOmegaContinuousDomain D :=
  FiniteValuationApproximable.FSApproximateIdentity.isOmegaContinuousDomain
    A A.continuousDomain

/-- If the underlying preorder is already a dcpo order, an FS approximate
identity upgrades it to an omega-continuous dcpo. -/
theorem omegaContinuousDcpo (A : FSApproximateIdentity D)
    (hD : AbramskyJung.Chapter2.IsDcpoOrder D) :
    AbramskyJung.Chapter2.IsOmegaContinuousDcpo D :=
  ⟨hD, A.omegaContinuousDomain⟩

end FSApproximateIdentity

namespace DirectedFSApproximateIdentity

variable {D : Type u} [Preorder D]

/-- The general directed-family form of an FS approximate identity also
supplies a continuous-domain basis.  This is the nonsequential counterpart of
`FSApproximateIdentity.continuousDomain` and records the foundational part of
the manuscript's directed-FVA remark without asserting its later saturation or
closure claims. -/
theorem continuousDomain (A : DirectedFSApproximateIdentity D) :
    AbramskyJung.Chapter2.IsContinuousDomain D := by
  refine ⟨Set.univ, ?_⟩
  intro x
  let evaluation : ScottContFun D D → D := fun f => f x
  have heval_mono : Monotone evaluation := by
    intro f g hfg
    exact hfg x
  refine ⟨evaluation '' A.maps, ?_,
    AbramskyJung.Chapter2.DirectedSet.image heval_mono A.directed,
    A.pointwise_sup x⟩
  rintro y ⟨f, hf, rfl⟩
  exact ⟨Set.mem_univ _,
    IsFinitelySeparated.wayBelow f.continuous (A.finitelySeparated f hf) x⟩

end DirectedFSApproximateIdentity

end AbstractApproximation

end FiniteValuationApproximable
