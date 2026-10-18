import Practice.DomainTheory.Papers.RBFunctionSpace.FiniteCover

/-!
# The universal algebraic target

This file constructs the three-point domain `V`, the product
`A_X = E_X × V`, and the function-space retraction used in
`thm:universal-target`.
-/

set_option autoImplicit false
set_option linter.unnecessarySimpa false

universe u v w

namespace RBFunctionSpace

open Set
open AbramskyJung.Chapter2

/-- The fork-shaped three-point poset `{ℓ,r,⊤}`. -/
inductive V
  | left
  | right
  | top
  deriving DecidableEq, Fintype

namespace V

def Le : V → V → Prop
  | left, left => True
  | right, right => True
  | _, top => True
  | _, _ => False

instance : LE V :=
  ⟨Le⟩

instance : PartialOrder V where
  le := (· ≤ ·)
  le_refl x := by
    cases x <;> simp [LE.le, Le]
  le_trans x y z hxy hyz := by
    cases x <;> cases y <;> cases z <;>
      simp [LE.le, Le] at hxy hyz ⊢
  le_antisymm x y hxy hyx := by
    cases x <;> cases y <;>
      simp [LE.le, Le] at hxy hyx ⊢

theorem compact (x : V) :
    Compact x := by
  intro A s hA hs hxs
  rcases hA.exists_isSup_of_finite (Set.toFinite A) with
    ⟨a, haA, haSup⟩
  exact
    ⟨a, haA,
      le_trans hxs (hs.2 a haSup.1)⟩

theorem isDcpoOrder : IsDcpoOrder V := by
  constructor
  · intro A hA
    rcases hA.exists_isSup_of_finite (Set.toFinite A) with
      ⟨a, _, haSup⟩
    exact ⟨a, haSup⟩
  · intro x y
    exact le_antisymm

theorem algebraicDomain : IsAlgebraicDomain V := by
  intro x
  refine
    ⟨({x} : Set V), ?_, directed_singleton x, isSup_singleton x⟩
  intro a ha
  have hax : a = x := by
    simpa using ha
  subst a
  exact ⟨compact x, compact x⟩

theorem isDomain : IsDomain V :=
  ⟨⟨left⟩, isDcpoOrder,
    ⟨CompactSet, algebraicDomain⟩⟩

theorem left_minimal : IsMinimalElement left := by
  intro y hy
  cases y <;> simp [LE.le, Le] at hy ⊢

theorem right_minimal : IsMinimalElement right := by
  intro y hy
  cases y <;> simp [LE.le, Le] at hy ⊢

theorem left_le_top : left ≤ top := by
  simp [LE.le, Le]

theorem right_le_top : right ≤ top := by
  simp [LE.le, Le]

theorem not_disjointUnionOfPointedDomains :
    ¬ IsDisjointUnionOfPointedDomains V := by
  intro h
  rcases h top with ⟨m, hm, hunique⟩
  have hleft : left = m :=
    hunique left ⟨left_minimal, left_le_top⟩
  have hright : right = m :=
    hunique right ⟨right_minimal, right_le_top⟩
  have : left = right :=
    hleft.trans hright.symm
  cases this

end V

/-- The manuscript's universal algebraic target `A_X`. -/
abbrev AX (X : Type u) [Preorder X] :=
  EX X × V

namespace AX

variable {X : Type u} [PartialOrder X]

theorem isDcpoOrder : IsDcpoOrder (AX X) := by
  constructor
  · exact
      AbramskyJung.Chapter3.prod_isDcpo
        EX.isDcpoOrder.1 V.isDcpoOrder.1
  · intro x y
    exact le_antisymm

theorem algebraicBasis :
    AbramskyJung.Chapter3.IsAlgebraicDomain (AX X) :=
  AbramskyJung.Chapter3.prod_algebraic_domain
    (prop_2_2_4_1 EX.algebraicDomain)
    (prop_2_2_4_1 V.algebraicDomain)

theorem algebraicDomain : IsAlgebraicDomain (AX X) :=
  basis_to_raw algebraicBasis

theorem isDomain : IsDomain (AX X) :=
  ⟨⟨(⊥, V.left)⟩, isDcpoOrder,
    ⟨CompactSet, algebraicDomain⟩⟩

theorem left_minimal :
    IsMinimalElement ((⊥, V.left) : AX X) := by
  intro y hy
  exact ⟨bot_le, V.left_minimal hy.2⟩

theorem right_minimal :
    IsMinimalElement ((⊥, V.right) : AX X) := by
  intro y hy
  exact ⟨bot_le, V.right_minimal hy.2⟩

theorem not_disjointUnionOfPointedDomains :
    ¬ IsDisjointUnionOfPointedDomains (AX X) := by
  intro h
  rcases h ((⊥, V.top) : AX X) with
    ⟨m, hm, hunique⟩
  have hleft :
      ((⊥, V.left) : AX X) = m :=
    hunique (⊥, V.left)
      ⟨left_minimal, ⟨le_rfl, V.left_le_top⟩⟩
  have hright :
      ((⊥, V.right) : AX X) = m :=
    hunique (⊥, V.right)
      ⟨right_minimal, ⟨le_rfl, V.right_le_top⟩⟩
  have hpair :
      ((⊥, V.left) : AX X) =
        ((⊥, V.right) : AX X) :=
    hleft.trans hright.symm
  have : V.left = V.right :=
    congrArg Prod.snd hpair
  cases this

/-- Projection `A_X → E_X`. -/
def projection : AbramskyJung.Chapter3.ContFun (AX X) (EX X) where
  toFun := Prod.fst
  continuous := AbramskyJung.Chapter3.prod_fst_scottContinuous

/-- Section `E_X → A_X`, choosing the left branch. -/
def sectionMap : AbramskyJung.Chapter3.ContFun (EX X) (AX X) where
  toFun := fun e => (e, V.left)
  continuous :=
    AbramskyJung.Chapter3.prod_left_section_scottContinuous V.left

@[simp]
theorem projection_section (e : EX X) :
    projection (sectionMap e) = e :=
  rfl

end AX

/-- Postcomposition by a Scott-continuous map is Scott-continuous on
function spaces when the intermediate codomain is a dcpo. -/
theorem postcompose_scottContinuous
    {D : Type u} {E : Type v} {F : Type w}
    [PartialOrder D] [PartialOrder E] [PartialOrder F]
    (hE : IsDcpo E)
    (g : AbramskyJung.Chapter3.ContFun E F) :
    AbramskyJung.Chapter2.ScottContinuous
      (fun f : AbramskyJung.Chapter3.ContFun D E =>
        AbramskyJung.Chapter3.ContFun.comp g f) := by
  constructor
  · intro f h hfh x
    exact g.continuous.1 (hfh x)
  · intro A s hA hs
    constructor
    · intro q hq
      rcases hq with ⟨f, hfA, rfl⟩
      intro x
      exact g.continuous.1 (hs.1 hfA x)
    · intro z hz x
      have hEvalSup :
          IsSup
            ((fun f : AbramskyJung.Chapter3.ContFun D E => f x) '' A)
            (s x) :=
        (AbramskyJung.Chapter3.ContFun.eval_scottContinuous hE x).2
          hA hs
      have hEvalDir :
          DirectedSet
            ((fun f : AbramskyJung.Chapter3.ContFun D E => f x) '' A) :=
        AbramskyJung.Chapter3.ContFun.eval_directed hA x
      have hMappedSup :
          IsSup
            (g ''
              ((fun f : AbramskyJung.Chapter3.ContFun D E => f x) '' A))
            (g (s x)) :=
        g.continuous.2 hEvalDir hEvalSup
      apply hMappedSup.2
      intro y hy
      rcases hy with ⟨e, he, rfl⟩
      rcases he with ⟨f, hfA, rfl⟩
      exact hz ⟨f, hfA, rfl⟩ x

namespace AX

variable {X : Type u} [PartialOrder X]

/-- Section between the two function spaces, by postcomposition. -/
def functionSection :
    AbramskyJung.Chapter3.ContFun X (EX X) →
      AbramskyJung.Chapter3.ContFun X (AX X) :=
  fun f =>
    AbramskyJung.Chapter3.ContFun.comp
      (sectionMap (X := X)) f

/-- Retraction between the two function spaces, by postcomposition. -/
def functionProjection :
    AbramskyJung.Chapter3.ContFun X (AX X) →
      AbramskyJung.Chapter3.ContFun X (EX X) :=
  fun f =>
    AbramskyJung.Chapter3.ContFun.comp
      (projection (X := X)) f

theorem functionSection_scottContinuous :
    AbramskyJung.Chapter2.ScottContinuous
      (functionSection (X := X)) :=
  postcompose_scottContinuous
    EX.isDcpoOrder.1 (sectionMap (X := X))

theorem functionProjection_scottContinuous :
    AbramskyJung.Chapter2.ScottContinuous
      (functionProjection (X := X)) :=
  postcompose_scottContinuous
    isDcpoOrder.1 (projection (X := X))

theorem functionProjection_functionSection
    (f : AbramskyJung.Chapter3.ContFun X (EX X)) :
    functionProjection (functionSection f) = f := by
  apply AbramskyJung.Chapter3.ContFun.ext_apply
  intro x
  rfl

def functionSpaceRetract :
    AbramskyJung.Chapter3.ContinuousSectionRetractionPair
      (AbramskyJung.Chapter3.ContFun X (EX X))
      (AbramskyJung.Chapter3.ContFun X (AX X)) where
  s := functionSection
  r := functionProjection
  monotone_s := functionSection_scottContinuous.1
  monotone_r := functionProjection_scottContinuous.1
  retract := functionProjection_functionSection
  continuous_s := functionSection_scottContinuous
  continuous_r := functionProjection_scottContinuous

end AX

end RBFunctionSpace
