import FiniteValuationApproximable.Abstract.FSDomain

/-!
# Finite posets are FS domains

The manuscript uses two elementary finite-poset facts before applying the
external FS exponential theorem: every directed subset of a finite poset has
a greatest member, and hence every monotone map out of a finite poset is
Scott-continuous.  Both facts, together with the constant identity FS family,
are proved here inside the standalone project.
-/

set_option autoImplicit false

universe u v

namespace FiniteValuationApproximable

open Set
open AbramskyJung.Chapter2
open AbstractApproximation

/-- A monotone map out of a finite partial order preserves directed suprema,
because the directed set contains a member that is already its supremum. -/
theorem scottContinuous_of_monotone_finite
    {D : Type u} {E : Type v}
    [Fintype D] [PartialOrder D] [Preorder E]
    {f : D → E} (hf : Monotone f) :
    AbramskyJung.Chapter2.ScottContinuous f := by
  constructor
  · exact hf
  · intro A s hA hs
    have hAfin : A.Finite := Set.toFinite A
    rcases hA.exists_isSup_of_finite hAfin with ⟨m, hmA, hm⟩
    have hms : m = s := hm.unique hs
    constructor
    · rintro y ⟨a, ha, rfl⟩
      exact hf (hs.1 ha)
    · intro y hy
      have hfm : f m ≤ y := hy ⟨m, hmA, rfl⟩
      simpa [hms] using hfm

/-- Every finite partial order is a dcpo order. -/
theorem finite_isDcpoOrder (D : Type u) [Fintype D] [PartialOrder D] :
    AbramskyJung.Chapter2.IsDcpoOrder D := by
  constructor
  · intro A hA
    rcases hA.exists_isSup_of_finite (Set.toFinite A) with ⟨s, _hsA, hs⟩
    exact ⟨s, hs⟩
  · intro x y hxy hyx
    exact le_antisymm hxy hyx

/-- The constant identity sequence is an FS approximate identity on a finite
partial order; the finite separator is the entire carrier. -/
noncomputable def finiteFSApproximateIdentity
    (D : Type u) [Fintype D] [PartialOrder D] :
    FSApproximateIdentity D where
  map _ := {
    toFun := fun x => x
    continuous := scottContinuous_id }
  monotone := by
    intro _ _ _ x
    exact le_rfl
  below_id := by
    intro _ x
    exact le_rfl
  pointwise_sup := by
    intro x
    have hrange : Set.range (fun _ : Nat => x) = ({x} : Set D) := by
      ext y
      simp
    rw [hrange]
    exact isSup_singleton x
  finitelySeparated := by
    intro _
    refine ⟨Set.univ, Set.toFinite _, ?_⟩
    intro x
    exact ⟨x, Set.mem_univ x, le_rfl, le_rfl⟩

/-- Fully internal form of the source fact that every finite poset is an
omega-continuous FS dcpo. -/
theorem finite_isOmegaContinuousDcpo
    (D : Type u) [Fintype D] [PartialOrder D] :
    AbramskyJung.Chapter2.IsOmegaContinuousDcpo D :=
  (finiteFSApproximateIdentity D).omegaContinuousDcpo
    (finite_isDcpoOrder D)

end FiniteValuationApproximable
