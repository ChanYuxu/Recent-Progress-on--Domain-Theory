import Practice.DomainTheory.Papers.RBFunctionSpace.Requirements

/-!
# Extracting deflations

This file formalizes `lem:deflation-extraction` and the constant finite
upper-layer maps used immediately before it.
-/

set_option autoImplicit false
set_option linter.unnecessarySimpa false

universe u

namespace RBFunctionSpace

open Set
open AbramskyJung.Chapter2

variable {X : Type u} [PartialOrder X]

/-- The constant function `K_M` with value `(M,1)`. -/
def K (M : Set X) : AbramskyJung.Chapter3.ContFun X (EX X) where
  toFun := fun _ => EX.upper M
  continuous := by
    constructor
    · intro _ _ _
      exact le_rfl
    · intro A _ hA _
      constructor
      · intro e he
        rcases he with ⟨_, _, rfl⟩
        exact le_rfl
      · intro z hz
        rcases hA.1 with ⟨a, haA⟩
        exact hz ⟨a, haA, rfl⟩

@[simp]
theorem K_apply (M : Set X) (x : X) :
    K M x = EX.upper M :=
  rfl

/-- The first-coordinate set `B_φ(x)` from the manuscript. -/
def B (φ : AbramskyJung.Chapter3.ContFun X (EX X)) (x : X) : Set X :=
  EX.carrier (φ x)

theorem B_layer_false
    (hX : IsDomain X)
    {φ : AbramskyJung.Chapter3.ContFun X (EX X)}
    (hφQ : φ ≤ Q hX) (x : X) :
    EX.layer (φ x) = false := by
  have hle : EX.layer (φ x) ≤ false :=
    (EX.le_iff.mp (hφQ x)).2
  exact le_antisymm hle (Bool.false_le _)

theorem B_directedOrEmpty
    (hX : IsDomain X)
    {φ : AbramskyJung.Chapter3.ContFun X (EX X)}
    (hφQ : φ ≤ Q hX) (x : X) :
    DirectedOrEmpty (B φ x) :=
  EX.valid_lower (φ x) (B_layer_false hX hφQ x)

theorem B_subset_wayBelow
    (hX : IsDomain X)
    {φ : AbramskyJung.Chapter3.ContFun X (EX X)}
    (hφQ : φ ≤ Q hX) (x : X) :
    B φ x ⊆ wayBelowLower x :=
  (EX.le_iff.mp (hφQ x)).1

theorem B_subset_finite_bound
    {φ : AbramskyJung.Chapter3.ContFun X (EX X)}
    {M : Set X} (hφK : φ ≤ K M) (x : X) :
    B φ x ⊆ M :=
  (EX.le_iff.mp (hφK x)).1

/-- All data needed to extract a finite-image deflation from `φ`. -/
structure ExtractionData
    (hX : IsDomain X)
    (φ : AbramskyJung.Chapter3.ContFun X (EX X)) where
  finiteBound : Set X
  finite_finiteBound : finiteBound.Finite
  le_Q : φ ≤ Q hX
  le_K : φ ≤ K finiteBound
  nonempty_B : ∀ x : X, (B φ x).Nonempty

namespace ExtractionData

variable
    {hX : IsDomain X}
    {φ ψ : AbramskyJung.Chapter3.ContFun X (EX X)}

theorem finite_B (data : ExtractionData hX φ) (x : X) :
    (B φ x).Finite :=
  data.finite_finiteBound.subset
    (B_subset_finite_bound data.le_K x)

theorem directed_B (data : ExtractionData hX φ) (x : X) :
    DirectedSet (B φ x) := by
  rcases B_directedOrEmpty hX data.le_Q x with hEmpty | hDirected
  · exact False.elim (by
      rcases data.nonempty_B x with ⟨a, ha⟩
      simpa [hEmpty] using ha)
  · exact hDirected

theorem exists_greatest_B (data : ExtractionData hX φ) (x : X) :
    ∃ m : X, IsGreatest (B φ x) m := by
  rcases (data.directed_B x).exists_isSup_of_finite (data.finite_B x) with
    ⟨m, hmB, hmSup⟩
  exact ⟨m, hmB, hmSup.1⟩

/-- The greatest member of the finite directed set `B_φ(x)`. -/
noncomputable def point (data : ExtractionData hX φ) (x : X) : X :=
  Classical.choose (data.exists_greatest_B x)

theorem point_isGreatest (data : ExtractionData hX φ) (x : X) :
    IsGreatest (B φ x) (data.point x) :=
  Classical.choose_spec (data.exists_greatest_B x)

theorem point_mem (data : ExtractionData hX φ) (x : X) :
    data.point x ∈ B φ x :=
  (data.point_isGreatest x).1

theorem point_greatest (data : ExtractionData hX φ) (x : X)
    {a : X} (ha : a ∈ B φ x) :
    a ≤ data.point x :=
  (data.point_isGreatest x).2 ha

theorem point_monotone (data : ExtractionData hX φ) :
    Monotone data.point := by
  intro x y hxy
  apply data.point_greatest y
  exact
    (EX.le_iff.mp (φ.continuous.1 hxy)).1
      (data.point_mem x)

theorem point_below (data : ExtractionData hX φ) (x : X) :
    data.point x ≤ x :=
  prop_2_2_2_1
    ((B_subset_wayBelow hX data.le_Q x) (data.point_mem x))

theorem point_scottContinuous (data : ExtractionData hX φ) :
    AbramskyJung.Chapter2.ScottContinuous data.point := by
  constructor
  · exact data.point_monotone
  · intro A s hA hs
    constructor
    · intro y hy
      rcases hy with ⟨a, haA, rfl⟩
      exact data.point_monotone (hs.1 haA)
    · intro z hz
      have hφSup :
          IsSup (φ '' A) (φ s) :=
        φ.continuous.2 hA hs
      have hValueLe :
          requirementValue (data.point s) ≤ φ s := by
        rw [EX.le_iff]
        refine ⟨?_, Bool.false_le _⟩
        intro a ha
        have haEq : a = data.point s := by
          simpa [requirementValue] using ha
        simpa [haEq] using data.point_mem s
      have hφDir : DirectedSet (φ '' A) :=
        DirectedSet.image φ.continuous.1 hA
      rcases
          requirementValue_compact (data.point s)
            hφDir hφSup hValueLe with
        ⟨e, heImage, hValueE⟩
      rcases heImage with ⟨a, haA, rfl⟩
      have hPointMem : data.point s ∈ B φ a :=
        (EX.le_iff.mp hValueE).1 (by simp [requirementValue])
      exact le_trans
        (data.point_greatest a hPointMem)
        (hz ⟨a, haA, rfl⟩)

/-- `lem:deflation-extraction`: the deflation extracted from `φ`. -/
noncomputable def deflation (data : ExtractionData hX φ) : Deflation X where
  toContFun :=
    { toFun := data.point
      continuous := data.point_scottContinuous }
  finite_range := by
    apply data.finite_finiteBound.subset
    intro y hy
    rcases hy with ⟨x, rfl⟩
    exact
      B_subset_finite_bound data.le_K x
        (data.point_mem x)
  below := data.point_below

@[simp]
theorem deflation_apply (data : ExtractionData hX φ) (x : X) :
    data.deflation x = data.point x :=
  rfl

/-- Monotonicity clause of `lem:deflation-extraction`. -/
theorem deflation_mono
    (dataφ : ExtractionData hX φ)
    (dataψ : ExtractionData hX ψ)
    (hφψ : φ ≤ ψ) :
    dataφ.deflation ≤ dataψ.deflation := by
  intro x
  apply dataψ.point_greatest x
  exact
    (EX.le_iff.mp (hφψ x)).1
      (dataφ.point_mem x)

end ExtractionData

end RBFunctionSpace
