import Practice.DomainTheory.Chapter03.NumberedItems

/-!
# Basic interfaces for the RB function-space characterization

This file supplies the source-facing notions used up to
`thm:rb-characterization` in
`Function_space_characterizations_RB_FS_intro_narrative.tex`.
-/

set_option autoImplicit false
set_option linter.unnecessarySimpa false

universe u v

namespace RBFunctionSpace

open Set
open AbramskyJung.Chapter2

/-- The manuscript's convention: a domain is a nonempty continuous dcpo. -/
def IsDomain (α : Type u) [Preorder α] : Prop :=
  Nonempty α ∧ IsContinuousDcpo α

/-- A source deflation: Scott-continuous, finite-image, and below the identity.
No idempotence condition is imposed. -/
structure Deflation (α : Type u) [Preorder α] where
  toContFun : AbramskyJung.Chapter3.ContFun α α
  finite_range : (Set.range toContFun).Finite
  below : ∀ x, toContFun x ≤ x

namespace Deflation

variable {α : Type u} [Preorder α]

instance : CoeFun (Deflation α) (fun _ => α → α) where
  coe d := d.toContFun

instance : LE (Deflation α) where
  le d e := ∀ x, d x ≤ e x

instance : Preorder (Deflation α) where
  le := (· ≤ ·)
  le_refl d x := le_rfl
  le_trans d e f hde hef x := le_trans (hde x) (hef x)

theorem scottContinuous (d : Deflation α) :
    AbramskyJung.Chapter2.ScottContinuous d :=
  d.toContFun.continuous

end Deflation

/-- Definition `def:fs-rb` (RB part): a directed approximate identity made of
finite-image deflations. -/
def IsRBDomain (α : Type u) [Preorder α] : Prop :=
  ∃ 𝒟 : Set (Deflation α),
    DirectedSet 𝒟 ∧
      ∀ x : α, IsSup ((fun d : Deflation α => d x) '' 𝒟) x

/-- The source assertion that `[X → Y]` is a continuous domain.  Directed
completeness and antisymmetry are retained rather than silently inferred. -/
def HasContinuousFunctionSpace
    (X : Type u) (Y : Type v) [Preorder X] [Preorder Y] : Prop :=
  IsContinuousDcpo (AbramskyJung.Chapter3.ContFun X Y)

/-- Scott-open subsets, ordered by inclusion. -/
def ScottOpenSet (α : Type u) [Preorder α] :=
  {U : Set α // ScottOpen U}

namespace ScottOpenSet

variable {α : Type u} [Preorder α]

instance : SetLike (ScottOpenSet α) α where
  coe U := U.1
  coe_injective' _ _ h := Subtype.ext h

instance : PartialOrder (ScottOpenSet α) :=
  inferInstanceAs (PartialOrder {U : Set α // ScottOpen U})

@[ext]
theorem ext {U V : ScottOpenSet α}
    (h : (U : Set α) = (V : Set α)) : U = V :=
  Subtype.ext h

/-- The union of a family of Scott opens, as a Scott open. -/
def sUnion (𝒰 : Set (ScottOpenSet α)) : ScottOpenSet α where
  val := ⋃ U : 𝒰, (U.1 : Set α)
  property := scottOpen_iUnion (fun U : 𝒰 => U.1.property)

theorem sUnion_isSup (𝒰 : Set (ScottOpenSet α)) :
    IsSup 𝒰 (sUnion 𝒰) := by
  constructor
  · intro U hU x hx
    change x ∈ ⋃ V : 𝒰, (V.1 : Set α)
    rw [Set.mem_iUnion]
    exact ⟨⟨U, hU⟩, hx⟩
  · intro V hV x hx
    change x ∈ ⋃ U : 𝒰, (U.1 : Set α) at hx
    rw [Set.mem_iUnion] at hx
    rcases hx with ⟨U, hxU⟩
    exact hV U.2 hxU

end ScottOpenSet

/-- Scott compactness of the whole source space, expressed by finite
Scott-open subcovers. -/
def IsScottCompact (α : Type u) [Preorder α] : Prop :=
  ∀ cover : Set (Set α),
    (∀ U ∈ cover, ScottOpen U) →
      Set.univ ⊆ ⋃₀ cover →
        ∃ finiteCover : Set (Set α),
          finiteCover ⊆ cover ∧
            finiteCover.Finite ∧
              Set.univ ⊆ ⋃₀ finiteCover

/-- Order-theoretic minimality. -/
def IsMinimalElement {α : Type u} [Preorder α] (m : α) : Prop :=
  ∀ ⦃y : α⦄, y ≤ m → m ≤ y

/-- The elementwise characterization of a disjoint union of pointed domains:
every element lies above a unique minimal element. -/
def IsDisjointUnionOfPointedDomains
    (α : Type u) [Preorder α] : Prop :=
  ∀ x : α, ∃! m : α, IsMinimalElement m ∧ m ≤ x

end RBFunctionSpace
