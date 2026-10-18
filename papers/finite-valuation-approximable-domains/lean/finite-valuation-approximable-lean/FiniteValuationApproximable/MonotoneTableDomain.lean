import FiniteValuationApproximable.MonotoneTableFlow
import FiniteValuationApproximable.Abstract.FiniteScott
import FiniteValuationApproximable.FiniteValuation.StageFS
import FiniteValuationApproximable.Global

/-!
# Domain structure and Scott flow on finite monotone tables

For finite posets `A` and `P`, this module proves the domain-theoretic steps
surrounding source equation `eq:Psi-definition`:

* monotone tables are order-isomorphic to Scott-continuous maps
  `A -> VSub(P)`;
* their pointwise order is directed complete;
* every nonnegative-time pointwise erosion map `Psi t` is Scott-continuous;
* the sequence `Psi (1/(n+1))` is an increasing approximate identity.

The stronger assertion that this function space is an *FS-domain* uses the
external FS exponential theorem cited as Gierz et al., Proposition II-2.18.
It is therefore deliberately not asserted here without that theorem.
-/

set_option autoImplicit false
set_option linter.unnecessarySimpa false

universe u v

namespace FiniteValuationApproximable

open AbstractApproximation
open Erosion

section OrderIso

variable {A : Type u} {P : Type v}
variable [Fintype A] [PartialOrder A] [Fintype P] [PartialOrder P]

/-- The source equality `M(A,P) = [A -> VSub(P)]`: on a finite source
poset every monotone map is Scott-continuous.  This is an order isomorphism,
not merely a carrier equivalence. -/
noncomputable def monotoneTableOrderIsoContFun :
    MonotoneTable A P ≃o
      AbramskyJung.Chapter3.ContFun A (SubprobabilityVector P) where
  toEquiv := {
    toFun := fun x => {
      toFun := x
      continuous := scottContinuous_of_monotone_finite
        (MonotoneTable.monotone A P x) }
    invFun := fun f => {
      toFun := f
      monotone' := f.continuous.monotone }
    left_inv := by
      intro x
      apply MonotoneTable.ext_apply
      intro a
      rfl
    right_inv := by
      intro f
      apply AbramskyJung.Chapter3.ContFun.ext_apply
      intro a
      rfl }
  map_rel_iff' := by
    intro x y
    rfl

/-- Directed completeness transports backwards across an order isomorphism. -/
theorem isDcpo_of_orderIso
    {D : Type u} {E : Type v} [Preorder D] [Preorder E]
    (e : D ≃o E) (hE : AbramskyJung.Chapter2.IsDcpo E) :
    AbramskyJung.Chapter2.IsDcpo D := by
  intro S hS
  have heS : AbramskyJung.Chapter2.DirectedSet (e '' S) :=
    AbramskyJung.Chapter2.DirectedSet.image e.monotone hS
  rcases hE (e '' S) heS with ⟨y, hy⟩
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

/-- Directed suprema in `M(A,P)` exist.  Through the preceding order
isomorphism this is precisely the pointwise dcpo structure of the continuous
function space. -/
theorem monotoneTable_isDcpoOrder :
    AbramskyJung.Chapter2.IsDcpoOrder (MonotoneTable A P) := by
  constructor
  · exact isDcpo_of_orderIso monotoneTableOrderIsoContFun
      (AbramskyJung.Chapter3.ContFun.isDcpo_of_codomain
        Erosion.finiteSubprobability_isDcpoOrder.1)
  · intro x y hxy hyx
    exact le_antisymm hxy hyx

end OrderIso

section ScottFlow

variable {A : Type u} {P : Type v}
variable [Fintype A] [PartialOrder A] [Fintype P] [PartialOrder P]

/-- Bundle one positive-time erosion map as a Scott-continuous endomap of the
finite stochastic simplex. -/
noncomputable def exactPhiContFun (t : Real) (ht0 : 0 ≤ t) :
    AbramskyJung.Chapter3.ContFun
      (SubprobabilityVector P) (SubprobabilityVector P) where
  toFun := exactPhi t
  continuous := chapter2ScottContinuous_of_scottContinuous
    (exactPhi_scott (P := P) ht0)

/-- The pointwise erosion `Psi t` is Scott-continuous on `M(A,P)` for every
nonnegative time, as claimed immediately after `eq:Psi-definition`. -/
theorem Psi_scottContinuous (t : Real) (ht0 : 0 ≤ t) :
    AbramskyJung.Chapter2.ScottContinuous
      (Psi t : MonotoneTable A P → MonotoneTable A P) := by
  let e := monotoneTableOrderIsoContFun (A := A) (P := P)
  let k := exactPhiContFun (P := P) t ht0
  let F : MonotoneTable A P → MonotoneTable A P :=
    fun x => e.symm (postcomposeContFun (A := A) k (e x))
  have hF : AbramskyJung.Chapter2.ScottContinuous F :=
    (orderIso_scottContinuous e.symm).comp
      ((postcomposeContFun_scottContinuous
          (A := A) Erosion.finiteSubprobability_isDcpoOrder.1 k).comp
        (orderIso_scottContinuous e))
  have hEq : F = Psi t := by
    funext x
    apply MonotoneTable.ext_apply
    intro a
    rfl
  rw [← hEq]
  exact hF

/-- The source's pointwise erosion sequence is an increasing approximate
identity on `M(A,P)`.  This records all order/Scott parts of
`lem:M-domain`; finite separation of the function-space maps is exactly the
remaining external FS-exponential ingredient. -/
noncomputable def monotoneTableIncreasingApproximateIdentity :
    IncreasingApproximateIdentity (MonotoneTable A P) where
  map n := {
    toFun := Psi (erosionTime n)
    continuous := Psi_scottContinuous (erosionTime n)
      (le_of_lt (erosionTime_pos n)) }
  monotone := by
    intro n m hnm x
    exact Psi_antitone_time x (le_of_lt (erosionTime_pos m))
      (erosionTime_antitone hnm)
  below_id := by
    intro n x
    exact Psi_le (erosionTime n) x
  pointwise_sup := by
    intro x
    constructor
    · intro y hy
      rcases hy with ⟨n, rfl⟩
      exact Psi_le (erosionTime n) x
    · intro y hy a
      apply (chapter2IsSup_of_isLUB (erosionTime_range_isLUB (x a))).2
      intro z hz
      rcases hz with ⟨n, rfl⟩
      exact hy ⟨n, rfl⟩ a

end ScottFlow

end FiniteValuationApproximable
