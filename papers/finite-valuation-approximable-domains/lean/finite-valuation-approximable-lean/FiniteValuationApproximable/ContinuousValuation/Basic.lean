import FiniteValuationApproximable.OrderTheory
import Mathlib.Data.ENNReal.Operations

/-!
# Continuous valuations on an arbitrary dcpo

This module supplies the general (not merely finite-dimensional) valuation
objects used in `main (17).tex`.  It is deliberately independent of the
Jones--Plotkin external-result module: Scott opens, valuations, directed
pointwise suprema, Dirac valuations, pushforward, and `lem:V-local` are all
constructed and proved here from their definitions.

The scalar codomain is `ENNReal`.  A subprobability valuation is a continuous
valuation whose value on the whole carrier is at most one; hence every value
is automatically finite and lies in `[0,1]`, exactly as in the manuscript.
-/

set_option autoImplicit false
set_option linter.unnecessarySimpa false

universe u v w

namespace FiniteValuationApproximable
namespace ContinuousValuation

open Set
open AbramskyJung.Chapter2
open scoped ENNReal

/-! ## Bundled Scott-open subsets -/

/-- Scott openness in the order-theoretic form used by the manuscript: an
upper set inaccessible by every existing directed supremum. -/
def IsScottOpen {D : Type u} [Preorder D] (U : Set D) : Prop :=
  IsUpperSet U ∧ ∀ ⦃A : Set D⦄ ⦃s : D⦄,
    DirectedSet A → IsSup A s → s ∈ U → ∃ x ∈ A, x ∈ U

/-- A Scott-open subset, bundled so that a valuation is an ordinary function
on a genuine ordered type. -/
structure ScottOpen (D : Type u) [Preorder D] where
  carrier : Set D
  isScottOpen : IsScottOpen carrier

namespace ScottOpen

variable {D : Type u} [Preorder D]

instance : SetLike (ScottOpen D) D where
  coe U := U.carrier
  coe_injective' := by
    intro U V h
    cases U
    cases V
    cases h
    rfl

@[ext]
theorem ext {U V : ScottOpen D} (h : (U : Set D) = (V : Set D)) : U = V :=
  SetLike.coe_injective h

instance : PartialOrder (ScottOpen D) where
  le U V := (U : Set D) ⊆ (V : Set D)
  le_refl _ := fun _ hx => hx
  le_trans _ _ _ hUV hVW := hUV.trans hVW
  le_antisymm U V hUV hVU := ext (Set.Subset.antisymm hUV hVU)

theorem upper (U : ScottOpen D) : IsUpperSet (U : Set D) :=
  U.isScottOpen.1

theorem inaccessible (U : ScottOpen D) {A : Set D} {s : D}
    (hA : DirectedSet A) (hs : IsSup A s) (hsU : s ∈ U) :
    ∃ x ∈ A, x ∈ U :=
  U.isScottOpen.2 hA hs hsU

/-- The empty Scott open. -/
def empty : ScottOpen D where
  carrier := ∅
  isScottOpen := by
    constructor
    · intro x _ hxy hx
      cases hx
    · intro A s hA hs hsU
      cases hsU

/-- The whole carrier as a Scott open. -/
def univ : ScottOpen D where
  carrier := Set.univ
  isScottOpen := by
    constructor
    · intro x y hxy hx
      trivial
    · intro A s hA hs hsU
      rcases hA.1 with ⟨x, hx⟩
      exact ⟨x, hx, Set.mem_univ x⟩

/-- Binary union of Scott opens. -/
def union (U V : ScottOpen D) : ScottOpen D where
  carrier := (U : Set D) ∪ (V : Set D)
  isScottOpen := by
    constructor
    · intro x y hxy hx
      rcases hx with hxU | hxV
      · exact Or.inl (U.upper hxy hxU)
      · exact Or.inr (V.upper hxy hxV)
    · intro A s hA hs hsUV
      rcases hsUV with hsU | hsV
      · rcases U.inaccessible hA hs hsU with ⟨x, hxA, hxU⟩
        exact ⟨x, hxA, Or.inl hxU⟩
      · rcases V.inaccessible hA hs hsV with ⟨x, hxA, hxV⟩
        exact ⟨x, hxA, Or.inr hxV⟩

/-- Binary intersection of Scott opens. -/
def inter (U V : ScottOpen D) : ScottOpen D where
  carrier := (U : Set D) ∩ (V : Set D)
  isScottOpen := by
    constructor
    · intro x y hxy hx
      exact ⟨U.upper hxy hx.1, V.upper hxy hx.2⟩
    · intro A s hA hs hsUV
      rcases U.inaccessible hA hs hsUV.1 with ⟨x, hxA, hxU⟩
      rcases V.inaccessible hA hs hsUV.2 with ⟨y, hyA, hyV⟩
      rcases hA.2 hxA hyA with ⟨z, hzA, hxz, hyz⟩
      exact ⟨z, hzA, U.upper hxz hxU, V.upper hyz hyV⟩

/-- An arbitrary union of Scott opens. -/
def sUnion (A : Set (ScottOpen D)) : ScottOpen D where
  carrier := ⋃ U ∈ A, (U : Set D)
  isScottOpen := by
    constructor
    · intro x y hxy hx
      simp only [Set.mem_iUnion] at hx ⊢
      rcases hx with ⟨U, hUA, hxU⟩
      exact ⟨U, hUA, U.upper hxy hxU⟩
    · intro B s hB hs hsA
      simp only [Set.mem_iUnion] at hsA
      rcases hsA with ⟨U, hUA, hsU⟩
      rcases U.inaccessible hB hs hsU with ⟨x, hxB, hxU⟩
      refine ⟨x, hxB, ?_⟩
      simp only [Set.mem_iUnion]
      exact ⟨U, hUA, hxU⟩

@[simp] theorem coe_empty :
    ((empty (D := D) : ScottOpen D) : Set D) = ∅ := rfl
@[simp] theorem coe_univ :
    ((univ (D := D) : ScottOpen D) : Set D) = Set.univ := rfl
@[simp] theorem coe_union (U V : ScottOpen D) :
    (union U V : Set D) = (U : Set D) ∪ (V : Set D) := rfl
@[simp] theorem coe_inter (U V : ScottOpen D) :
    (inter U V : Set D) = (U : Set D) ∩ (V : Set D) := rfl

@[simp] theorem not_mem_empty (x : D) : x ∉ (empty : ScottOpen D) := by
  change x ∉ (∅ : Set D)
  simp

@[simp] theorem mem_univ (x : D) : x ∈ (univ : ScottOpen D) := by
  change x ∈ (Set.univ : Set D)
  simp

@[simp] theorem mem_union (x : D) (U V : ScottOpen D) :
    x ∈ union U V ↔ x ∈ U ∨ x ∈ V := Iff.rfl

@[simp] theorem mem_inter (x : D) (U V : ScottOpen D) :
    x ∈ inter U V ↔ x ∈ U ∧ x ∈ V := Iff.rfl

theorem mem_sUnion_iff {A : Set (ScottOpen D)} {x : D} :
    x ∈ sUnion A ↔ ∃ U ∈ A, x ∈ U := by
  change x ∈ (⋃ U ∈ A, (U : Set D)) ↔ _
  constructor
  · intro hx
    simp only [Set.mem_iUnion] at hx
    rcases hx with ⟨U, hUA, hxU⟩
    exact ⟨U, hUA, hxU⟩
  · rintro ⟨U, hUA, hxU⟩
    simp only [Set.mem_iUnion]
    exact ⟨U, hUA, hxU⟩

theorem sUnion_isSup (A : Set (ScottOpen D)) : IsSup A (sUnion A) := by
  constructor
  · intro U hUA x hxU
    rw [show (sUnion A : Set D) = ⋃ V ∈ A, (V : Set D) by rfl,
      Set.mem_iUnion]
    refine ⟨U, ?_⟩
    rw [Set.mem_iUnion]
    exact ⟨hUA, hxU⟩
  · intro V hV x hx
    rw [show (sUnion A : Set D) = ⋃ U ∈ A, (U : Set D) by rfl,
      Set.mem_iUnion] at hx
    rcases hx with ⟨U, hx⟩
    rw [Set.mem_iUnion] at hx
    exact hV hx.1 hx.2

theorem isDcpo : IsDcpo (ScottOpen D) := by
  intro A hA
  exact ⟨sUnion A, sUnion_isSup A⟩

/-- Inverse image of a Scott open under an order-theoretically Scott-continuous
map. -/
def preimage {E : Type v} [Preorder E] (f : D → E)
    (hf : AbramskyJung.Chapter2.ScottContinuous f)
    (U : ScottOpen E) : ScottOpen D where
  carrier := f ⁻¹' (U : Set E)
  isScottOpen := by
    constructor
    · intro x y hxy hx
      exact U.upper (hf.monotone hxy) hx
    · intro A s hA hs hsf
      have hImg : DirectedSet (f '' A) := hf.image_directed hA
      have hSup : IsSup (f '' A) (f s) := hf.maps_isSup hA hs
      rcases U.inaccessible hImg hSup hsf with ⟨y, hy, hyU⟩
      rcases hy with ⟨x, hxA, rfl⟩
      exact ⟨x, hxA, hyU⟩

theorem preimage_mono_map {E : Type v} [Preorder E]
    {f g : D → E}
    (hf : AbramskyJung.Chapter2.ScottContinuous f)
    (hg : AbramskyJung.Chapter2.ScottContinuous g)
    (hfg : ∀ x, f x ≤ g x) (U : ScottOpen E) :
    preimage f hf U ≤ preimage g hg U := by
  intro x hx
  exact U.upper (hfg x) hx

theorem preimage_scottContinuous {E : Type v} [Preorder E]
    (f : D → E) (hf : AbramskyJung.Chapter2.ScottContinuous f) :
    AbramskyJung.Chapter2.ScottContinuous
      (fun U : ScottOpen E => preimage f hf U) := by
  constructor
  · intro U V hUV x hx
    exact hUV hx
  · intro A S hA hS
    constructor
    · rintro _ ⟨U, hUA, rfl⟩
      intro x hx
      exact hS.1 hUA hx
    · intro T hT x hx
      have hxSUnion : x ∈ preimage f hf (sUnion A) := by
        change f x ∈ sUnion A
        have hSS : S = sUnion A :=
          IsSup.unique hS (sUnion_isSup A)
        simpa [hSS] using hx
      rcases (mem_sUnion_iff.mp hxSUnion) with ⟨U, hUA, hxU⟩
      exact hT ⟨U, hUA, rfl⟩ hxU

end ScottOpen

/-! ## Continuous, subprobability, and probability valuations -/

/-- A continuous valuation on the Scott topology of `D`.  Monotonicity is a
consequence of the bundled Scott-continuity field. -/
structure Valuation (D : Type u) [Preorder D] where
  toFun : ScottOpen D → ℝ≥0∞
  continuous : AbramskyJung.Chapter2.ScottContinuous toFun
  strict : toFun ScottOpen.empty = 0
  modular : ∀ U V,
    toFun U + toFun V =
      toFun (ScottOpen.union U V) + toFun (ScottOpen.inter U V)

namespace Valuation

variable {D : Type u} [Preorder D]

instance : CoeFun (Valuation D) (fun _ => ScottOpen D → ℝ≥0∞) :=
  ⟨Valuation.toFun⟩

instance : PartialOrder (Valuation D) where
  le μ ν := ∀ U, μ U ≤ ν U
  le_refl _ _ := le_rfl
  le_trans _ _ _ hμν hνρ U := le_trans (hμν U) (hνρ U)
  le_antisymm μ ν hμν hνμ := by
    cases μ with
    | mk μ hμc hμs hμm =>
      cases ν with
      | mk ν hνc hνs hνm =>
        have hfun : μ = ν := funext fun U => le_antisymm (hμν U) (hνμ U)
        subst hfun
        rfl

@[ext]
theorem ext {μ ν : Valuation D} (h : ∀ U, μ U = ν U) : μ = ν :=
  le_antisymm (fun U => (h U).le) (fun U => (h U).ge)

theorem monotone (μ : Valuation D) : Monotone μ :=
  μ.continuous.monotone

theorem le_total (μ : Valuation D) (U : ScottOpen D) :
    μ U ≤ μ ScottOpen.univ :=
  μ.monotone (by intro x hx; trivial)

/-- Pointwise directed supremum of continuous valuations.  The modularity
proof uses directedness to put the two summands at one common index. -/
noncomputable def directedSup (A : Set (Valuation D)) (hA : DirectedSet A) :
    Valuation D := by
  letI : Nonempty A := hA.1.to_subtype
  refine
    { toFun := fun U => ⨆ μ : A, μ.1 U
      continuous := ?_
      strict := ?_
      modular := ?_ }
  · constructor
    · intro U V hUV
      exact iSup_mono fun μ => μ.1.monotone hUV
    · intro B S hB hS
      constructor
      · rintro _ ⟨U, hUB, rfl⟩
        exact iSup_mono fun μ => μ.1.monotone (hS.1 hUB)
      · intro y hy
        refine iSup_le fun μ => ?_
        exact (μ.1.continuous.maps_isSup hB hS).2 y (by
          rintro _ ⟨U, hUB, rfl⟩
          exact le_trans (le_iSup (fun ρ : A => ρ.1 U) μ)
            (hy ⟨U, hUB, rfl⟩))
  · apply le_antisymm
    · exact iSup_le fun μ => by rw [μ.1.strict]
    · exact bot_le
  · intro U V
    calc
      (⨆ μ : A, μ.1 U) + (⨆ μ : A, μ.1 V) =
          ⨆ μ : A, μ.1 U + μ.1 V := by
            apply ENNReal.iSup_add_iSup
            intro μ ν
            rcases hA.2 μ.2 ν.2 with ⟨ρ, hρA, hμρ, hνρ⟩
            exact ⟨⟨ρ, hρA⟩, add_le_add (hμρ U) (hνρ V)⟩
      _ = ⨆ μ : A,
          μ.1 (ScottOpen.union U V) + μ.1 (ScottOpen.inter U V) := by
            congr 1
            funext μ
            exact μ.1.modular U V
      _ = (⨆ μ : A, μ.1 (ScottOpen.union U V)) +
          (⨆ μ : A, μ.1 (ScottOpen.inter U V)) := by
            symm
            apply ENNReal.iSup_add_iSup
            intro μ ν
            rcases hA.2 μ.2 ν.2 with ⟨ρ, hρA, hμρ, hνρ⟩
            exact ⟨⟨ρ, hρA⟩,
              add_le_add (hμρ (ScottOpen.union U V))
                (hνρ (ScottOpen.inter U V))⟩

theorem directedSup_isSup (A : Set (Valuation D)) (hA : DirectedSet A) :
    IsSup A (directedSup A hA) := by
  letI : Nonempty A := hA.1.to_subtype
  constructor
  · intro μ hμA U
    exact le_iSup (fun ρ : A => ρ.1 U) ⟨μ, hμA⟩
  · intro ν hν U
    exact iSup_le fun μ => hν μ.2 U

theorem isDcpo : IsDcpo (Valuation D) := by
  intro A hA
  exact ⟨directedSup A hA, directedSup_isSup A hA⟩

end Valuation

/-- Continuous subprobability valuations. -/
def VSub (D : Type u) [Preorder D] :=
  {μ : Valuation D // μ ScottOpen.univ ≤ 1}

/-- Continuous probability valuations. -/
def VOne (D : Type u) [Preorder D] :=
  {μ : Valuation D // μ ScottOpen.univ = 1}

namespace VSub

variable {D : Type u} [Preorder D]

instance : Coe (VSub D) (Valuation D) where
  coe μ := μ.1
instance : CoeFun (VSub D) (fun _ => ScottOpen D → ℝ≥0∞) :=
  ⟨fun μ => μ.1.toFun⟩
instance : PartialOrder (VSub D) where
  le μ ν := ∀ U, μ U ≤ ν U
  le_refl _ _ := le_rfl
  le_trans _ _ _ hμν hνρ U := (hμν U).trans (hνρ U)
  le_antisymm μ ν hμν hνμ := by
    apply Subtype.ext
    exact Valuation.ext fun U => le_antisymm (hμν U) (hνμ U)

@[ext]
theorem ext {μ ν : VSub D} (h : ∀ U, μ U = ν U) : μ = ν := by
  apply Subtype.ext
  exact Valuation.ext h

theorem monotone (μ : VSub D) : Monotone μ := μ.1.monotone

theorem value_le_one (μ : VSub D) (U : ScottOpen D) : μ U ≤ 1 :=
  (μ.1.le_total U).trans μ.2

/-- The zero subprobability valuation. -/
def zero : VSub D :=
  ⟨{ toFun := fun _ => 0
     continuous := const_scottContinuous 0
     strict := rfl
     modular := by simp }, by simp⟩

instance : Zero (VSub D) := ⟨zero⟩

@[simp] theorem zero_apply (U : ScottOpen D) : (0 : VSub D) U = 0 := rfl

theorem zero_le (μ : VSub D) : (0 : VSub D) ≤ μ := by
  intro U
  exact bot_le

/-- Directed pointwise supremum in `VSub D`. -/
noncomputable def directedSup (A : Set (VSub D)) (hA : DirectedSet A) : VSub D := by
  let B : Set (Valuation D) := (fun μ : VSub D => μ.1) '' A
  have hB : DirectedSet B := by
    apply DirectedSet.image (A := A) (f := fun μ : VSub D => μ.1)
    · intro μ ν hμν U
      exact hμν U
    · exact hA
  refine ⟨Valuation.directedSup B hB, ?_⟩
  letI : Nonempty B := hB.1.to_subtype
  exact iSup_le fun μ => by
    rcases μ.2 with ⟨ν, hνA, hνμ⟩
    rw [← hνμ]
    exact ν.2

theorem directedSup_isSup (A : Set (VSub D)) (hA : DirectedSet A) :
    IsSup A (directedSup A hA) := by
  let B : Set (Valuation D) := (fun μ : VSub D => μ.1) '' A
  have hB : DirectedSet B := by
    apply DirectedSet.image (A := A) (f := fun μ : VSub D => μ.1)
    · intro μ ν hμν U
      exact hμν U
    · exact hA
  have hSupB := Valuation.directedSup_isSup B hB
  constructor
  · intro μ hμA U
    exact hSupB.1 ⟨μ, hμA, rfl⟩ U
  · intro ν hν U
    exact hSupB.2 ν.1 (by
      rintro _ ⟨μ, hμA, rfl⟩
      exact hν hμA) U

theorem isDcpo : IsDcpo (VSub D) := by
  intro A hA
  exact ⟨directedSup A hA, directedSup_isSup A hA⟩

theorem isDcpoOrder : IsDcpoOrder (VSub D) :=
  ⟨isDcpo, fun μ ν hμν hνμ => le_antisymm hμν hνμ⟩

/-- Directed suprema in `VSub` are pointwise, Jones--Plotkin Theorem 2.1,
proved here directly from the definition. -/
theorem eval_isSup {A : Set (VSub D)} {s : VSub D}
    (hA : DirectedSet A) (hs : IsSup A s) (U : ScottOpen D) :
    IsSup ((fun μ : VSub D => μ U) '' A) (s U) := by
  have ht : IsSup A (directedSup A hA) := directedSup_isSup A hA
  have hst : s = directedSup A hA := IsSup.unique hs ht
  subst hst
  let B : Set (Valuation D) := (fun μ : VSub D => μ.1) '' A
  have hB : DirectedSet B := by
    apply DirectedSet.image (A := A) (f := fun μ : VSub D => μ.1)
    · intro μ ν hμν V
      exact hμν V
    · exact hA
  letI : Nonempty B := hB.1.to_subtype
  constructor
  · rintro _ ⟨μ, hμA, rfl⟩
    exact le_iSup (fun ρ : B => ρ.1 U) ⟨μ.1, ⟨μ, hμA, rfl⟩⟩
  · intro y hy
    exact iSup_le fun ρ => by
      rcases ρ.2 with ⟨μ, hμA, hμρ⟩
      rw [← hμρ]
      exact hy ⟨μ, hμA, rfl⟩

/-- Pointwise directed bounds assemble into the supremum in `VSub`. -/
theorem isSup_of_pointwise {A : Set (VSub D)} {s : VSub D}
    (hA : DirectedSet A)
    (hs : ∀ U : ScottOpen D,
      IsSup ((fun μ : VSub D => μ U) '' A) (s U)) :
    IsSup A s := by
  constructor
  · intro μ hμA U
    exact (hs U).1 ⟨μ, hμA, rfl⟩
  · intro ν hν U
    exact (hs U).2 (ν U) (by
      rintro _ ⟨μ, hμA, rfl⟩
      exact hν hμA U)

/-- Evaluation at one Scott open is Scott-continuous because directed suprema
of valuations are pointwise. -/
theorem eval_scottContinuous (U : ScottOpen D) :
    AbramskyJung.Chapter2.ScottContinuous (fun μ : VSub D => μ U) := by
  constructor
  · intro μ ν hμν
    exact hμν U
  · intro A s hA hs
    exact eval_isSup hA hs U

end VSub

namespace VOne

variable {D : Type u} [Preorder D]

instance : Coe (VOne D) (Valuation D) where
  coe μ := μ.1
instance : CoeFun (VOne D) (fun _ => ScottOpen D → ℝ≥0∞) :=
  ⟨fun μ => μ.1.toFun⟩
instance : PartialOrder (VOne D) where
  le μ ν := ∀ U, μ U ≤ ν U
  le_refl _ _ := le_rfl
  le_trans _ _ _ hμν hνρ U := (hμν U).trans (hνρ U)
  le_antisymm μ ν hμν hνμ := by
    apply Subtype.ext
    exact Valuation.ext fun U => le_antisymm (hμν U) (hνμ U)

@[ext]
theorem ext {μ ν : VOne D} (h : ∀ U, μ U = ν U) : μ = ν := by
  apply Subtype.ext
  exact Valuation.ext h

/-- Canonical order embedding of probability valuations into subprobability
valuations. -/
def toVSub (μ : VOne D) : VSub D := ⟨μ.1, μ.2.le⟩

theorem toVSub_injective : Function.Injective (toVSub : VOne D → VSub D) := by
  intro μ ν h
  apply ext
  intro U
  exact congrArg (fun ρ : VSub D => ρ U) h

theorem toVSub_le_toVSub {μ ν : VOne D} : toVSub μ ≤ toVSub ν ↔ μ ≤ ν :=
  Iff.rfl

/-- Probability valuations also have pointwise directed suprema. -/
noncomputable def directedSup (A : Set (VOne D)) (hA : DirectedSet A) : VOne D := by
  let B : Set (Valuation D) := (fun μ : VOne D => μ.1) '' A
  have hB : DirectedSet B := by
    apply DirectedSet.image (A := A) (f := fun μ : VOne D => μ.1)
    · intro μ ν hμν U
      exact hμν U
    · exact hA
  refine ⟨Valuation.directedSup B hB, ?_⟩
  letI : Nonempty B := hB.1.to_subtype
  apply le_antisymm
  · exact iSup_le fun μ => by
      rcases μ.2 with ⟨ν, hνA, hνμ⟩
      rw [← hνμ]
      exact ν.2.le
  · rcases hA.1 with ⟨ν, hνA⟩
    have hν : (1 : ℝ≥0∞) = ν ScottOpen.univ := ν.2.symm
    rw [hν]
    exact le_iSup (fun μ : B => μ.1 ScottOpen.univ)
      ⟨ν.1, ⟨ν, hνA, rfl⟩⟩

theorem directedSup_isSup (A : Set (VOne D)) (hA : DirectedSet A) :
    IsSup A (directedSup A hA) := by
  let B : Set (Valuation D) := (fun μ : VOne D => μ.1) '' A
  have hB : DirectedSet B := by
    apply DirectedSet.image (A := A) (f := fun μ : VOne D => μ.1)
    · intro μ ν hμν U
      exact hμν U
    · exact hA
  have hSupB := Valuation.directedSup_isSup B hB
  constructor
  · intro μ hμA U
    exact hSupB.1 ⟨μ, hμA, rfl⟩ U
  · intro ν hν U
    exact hSupB.2 ν.1 (by
      rintro _ ⟨μ, hμA, rfl⟩
      exact hν hμA) U

theorem isDcpo : IsDcpo (VOne D) := by
  intro A hA
  exact ⟨directedSup A hA, directedSup_isSup A hA⟩

theorem isDcpoOrder : IsDcpoOrder (VOne D) :=
  ⟨isDcpo, fun μ ν hμν hνμ => le_antisymm hμν hνμ⟩

end VOne

/-! ## Dirac unit and pushforward -/

/-- The `{0,1}`-valued indicator of a Scott open.  Naming it separately keeps
the public API independent of the particular classical `Decidable` proof used
to elaborate membership. -/
noncomputable def openIndicator {D : Type u} [Preorder D]
    (U : ScottOpen D) (x : D) : ℝ≥0∞ := by
  classical
  exact if x ∈ U then 1 else 0

@[simp] theorem openIndicator_of_mem {D : Type u} [Preorder D]
    {U : ScottOpen D} {x : D} (hx : x ∈ U) :
    openIndicator U x = 1 := by
  classical
  simp [openIndicator, hx]

@[simp] theorem openIndicator_of_not_mem {D : Type u} [Preorder D]
    {U : ScottOpen D} {x : D} (hx : x ∉ U) :
    openIndicator U x = 0 := by
  classical
  simp [openIndicator, hx]

theorem openIndicator_le_one {D : Type u} [Preorder D]
    (U : ScottOpen D) (x : D) : openIndicator U x ≤ 1 := by
  classical
  by_cases hx : x ∈ U
  · rw [openIndicator_of_mem hx]
  · rw [openIndicator_of_not_mem hx]
    exact bot_le

/-- Scott-continuous bounded scalar functions used by the Jones integral.
The finite bound is allowed to depend on the function. -/
structure BoundedScottFunction (D : Type u) [Preorder D] where
  toFun : D → ℝ≥0∞
  continuous : AbramskyJung.Chapter2.ScottContinuous toFun
  bounded : ∃ c : ℝ≥0∞, c ≠ ⊤ ∧ ∀ x, toFun x ≤ c

namespace BoundedScottFunction

variable {D : Type u} [Preorder D]

instance : CoeFun (BoundedScottFunction D) (fun _ => D → ℝ≥0∞) :=
  ⟨BoundedScottFunction.toFun⟩

instance : PartialOrder (BoundedScottFunction D) where
  le f g := ∀ x, f x ≤ g x
  le_refl _ _ := le_rfl
  le_trans _ _ _ hfg hgh x := (hfg x).trans (hgh x)
  le_antisymm f g hfg hgf := by
    cases f with
    | mk f hfc hfb =>
      cases g with
      | mk g hgc hgb =>
        have h : f = g := funext fun x => le_antisymm (hfg x) (hgf x)
        subst h
        rfl

@[ext]
theorem ext {f g : BoundedScottFunction D} (h : ∀ x, f x = g x) : f = g :=
  le_antisymm (fun x => (h x).le) (fun x => (h x).ge)

/-- Indicator of a Scott open, as a bounded Scott-continuous scalar function. -/
noncomputable def indicator (U : ScottOpen D) : BoundedScottFunction D := by
  classical
  refine
    { toFun := openIndicator U
      continuous := ?_
      bounded := ?_ }
  · constructor
    · intro x y hxy
      by_cases hx : x ∈ U
      · have hy : y ∈ U := U.upper hxy hx
        simp [openIndicator, hx, hy]
      · simp [openIndicator, hx]
    · intro A s hA hs
      constructor
      · rintro _ ⟨x, hxA, rfl⟩
        by_cases hx : x ∈ U
        · have hsU : s ∈ U := U.upper (hs.1 hxA) hx
          simp [openIndicator, hx, hsU]
        · simp [openIndicator, hx]
      · intro y hy
        by_cases hsU : s ∈ U
        · rcases U.inaccessible hA hs hsU with ⟨x, hxA, hxU⟩
          have hOne : (1 : ℝ≥0∞) ≤ y := by
            simpa [openIndicator, hxU] using hy ⟨x, hxA, rfl⟩
          simpa [openIndicator, hsU] using hOne
        · simpa [openIndicator, hsU] using (bot_le : (0 : ℝ≥0∞) ≤ y)
  · exact ⟨1, ENNReal.one_ne_top, openIndicator_le_one U⟩

@[simp] theorem indicator_apply (U : ScottOpen D) (x : D) :
    indicator U x = openIndicator U x := rfl

end BoundedScottFunction

/-- For a valuation kernel `k` and target Scott open `U`, the scalar function
`x ↦ k x U` integrated in the Kleisli formula. -/
def kernelSection {D : Type u} {E : Type v} [Preorder D] [Preorder E]
    (k : AbramskyJung.Chapter2.ScottContFun D (VSub E))
    (U : ScottOpen E) : BoundedScottFunction D where
  toFun x := k x U
  continuous := (VSub.eval_scottContinuous U).comp k.continuous
  bounded := ⟨1, ENNReal.one_ne_top, fun x => (k x).value_le_one U⟩

@[simp] theorem kernelSection_apply
    {D : Type u} {E : Type v} [Preorder D] [Preorder E]
    (k : AbramskyJung.Chapter2.ScottContFun D (VSub E))
    (U : ScottOpen E) (x : D) : kernelSection k U x = k x U := rfl

/-- The Dirac subprobability valuation. -/
noncomputable def dirac {D : Type u} [Preorder D] (x : D) : VSub D := by
  classical
  refine ⟨
    { toFun := fun U => openIndicator U x
      continuous := ?_
      strict := openIndicator_of_not_mem (ScottOpen.not_mem_empty x)
      modular := ?_ }, ?_⟩
  · constructor
    · intro U V hUV
      by_cases hxU : x ∈ U
      · have hxV : x ∈ V := hUV hxU
        simp [openIndicator, hxU, hxV]
      · simp [openIndicator, hxU]
    · intro A S hA hS
      constructor
      · rintro _ ⟨U, hUA, rfl⟩
        by_cases hxU : x ∈ U
        · have hxS : x ∈ S := hS.1 hUA hxU
          simp [openIndicator, hxU, hxS]
        · simp [openIndicator, hxU]
      · intro y hy
        by_cases hxS : x ∈ S
        · have hSS : S = ScottOpen.sUnion A :=
            IsSup.unique hS (ScottOpen.sUnion_isSup A)
          have hxUnion : x ∈ ScottOpen.sUnion A := by simpa [← hSS] using hxS
          rcases ScottOpen.mem_sUnion_iff.mp hxUnion with ⟨U, hUA, hxU⟩
          have hOne : (1 : ℝ≥0∞) ≤ y := by
            simpa [openIndicator, hxU] using hy ⟨U, hUA, rfl⟩
          simpa [openIndicator, hxS] using hOne
        · simpa [openIndicator, hxS] using (bot_le : (0 : ℝ≥0∞) ≤ y)
  · intro U V
    by_cases hxU : x ∈ U <;> by_cases hxV : x ∈ V <;>
      simp [openIndicator, hxU, hxV]
  · exact openIndicator_le_one ScottOpen.univ x

@[simp] theorem dirac_apply {D : Type u} [Preorder D]
    (x : D) (U : ScottOpen D) :
    dirac x U = openIndicator U x := rfl

/-- The Dirac unit is Scott-continuous. -/
theorem dirac_scottContinuous {D : Type u} [Preorder D] :
    AbramskyJung.Chapter2.ScottContinuous (dirac : D → VSub D) := by
  classical
  constructor
  · intro x y hxy U
    by_cases hx : x ∈ U
    · have hy : y ∈ U := U.upper hxy hx
      simp [dirac_apply, openIndicator, hx, hy]
    · simp [dirac_apply, openIndicator, hx]
  · intro A s hA hs
    have hDir : DirectedSet (dirac '' A) :=
      hA.image (by
        intro x y hxy U
        by_cases hx : x ∈ U
        · have hy : y ∈ U := U.upper hxy hx
          simp [dirac_apply, openIndicator, hx, hy]
        · simp [dirac_apply, openIndicator, hx])
    apply VSub.isSup_of_pointwise hDir
    intro U
    constructor
    · rintro _ ⟨_, ⟨x, hxA, rfl⟩, rfl⟩
      by_cases hx : x ∈ U
      · have hsU : s ∈ U := U.upper (hs.1 hxA) hx
        simp [dirac_apply, openIndicator, hx, hsU]
      · simp [dirac_apply, openIndicator, hx]
    · intro y hy
      by_cases hsU : s ∈ U
      · rcases U.inaccessible hA hs hsU with ⟨x, hxA, hxU⟩
        have hOne : (1 : ℝ≥0∞) ≤ y := by
          simpa [dirac_apply, openIndicator, hxU] using
            hy ⟨dirac x, ⟨x, hxA, rfl⟩, rfl⟩
        simpa [dirac_apply, openIndicator, hsU] using hOne
      · simpa [dirac_apply, openIndicator, hsU] using
          (bot_le : (0 : ℝ≥0∞) ≤ y)

/-- Bundled Dirac unit. -/
noncomputable def unit {D : Type u} [Preorder D] :
    AbramskyJung.Chapter2.ScottContFun D (VSub D) where
  toFun := dirac
  continuous := dirac_scottContinuous

/-- Pushforward of a continuous subprobability valuation. -/
def pushforward {D : Type u} {E : Type v} [Preorder D] [Preorder E]
    (f : AbramskyJung.Chapter2.ScottContFun D E) (μ : VSub D) : VSub E := by
  refine ⟨
    { toFun := fun U => μ (ScottOpen.preimage f f.continuous U)
      continuous := μ.1.continuous.comp
        (ScottOpen.preimage_scottContinuous f f.continuous)
      strict := by
        simpa [ScottOpen.preimage, ScottOpen.empty] using μ.1.strict
      modular := ?_ }, ?_⟩
  · intro U V
    simpa [ScottOpen.preimage, ScottOpen.union, ScottOpen.inter] using
      μ.1.modular (ScottOpen.preimage f f.continuous U)
        (ScottOpen.preimage f f.continuous V)
  · have hpre : ScottOpen.preimage f f.continuous ScottOpen.univ =
        (ScottOpen.univ : ScottOpen D) := by
      apply ScottOpen.ext
      ext x
      rfl
    simpa [hpre] using μ.2

@[simp]
theorem pushforward_apply {D : Type u} {E : Type v} [Preorder D] [Preorder E]
    (f : AbramskyJung.Chapter2.ScottContFun D E) (μ : VSub D)
    (U : ScottOpen E) :
    pushforward f μ U = μ (ScottOpen.preimage f f.continuous U) := rfl

theorem pushforward_mono_map {D : Type u} {E : Type v}
    [Preorder D] [Preorder E]
    {f g : AbramskyJung.Chapter2.ScottContFun D E} (hfg : f ≤ g)
    (μ : VSub D) : pushforward f μ ≤ pushforward g μ := by
  intro U
  exact μ.monotone (ScottOpen.preimage_mono_map
    f.continuous g.continuous hfg U)

theorem pushforward_mono_valuation {D : Type u} {E : Type v}
    [Preorder D] [Preorder E]
    (f : AbramskyJung.Chapter2.ScottContFun D E) {μ ν : VSub D}
    (hμν : μ ≤ ν) : pushforward f μ ≤ pushforward f ν :=
  fun U => hμν _

/-- Jones 1990, Theorem 4.3 (p. 69), proved internally here: pushforward by a
fixed Scott-continuous map is Scott-continuous on valuation spaces. -/
theorem pushforward_scottContinuous {D : Type u} {E : Type v}
    [Preorder D] [Preorder E]
    (f : AbramskyJung.Chapter2.ScottContFun D E) :
    AbramskyJung.Chapter2.ScottContinuous
      (pushforward f : VSub D → VSub E) := by
  constructor
  · intro μ ν hμν
    exact pushforward_mono_valuation f hμν
  · intro A s hA hs
    constructor
    · rintro _ ⟨μ, hμA, rfl⟩ U
      exact (VSub.eval_isSup hA hs
        (ScottOpen.preimage f f.continuous U)).1 ⟨μ, hμA, rfl⟩
    · intro τ hτ U
      exact (VSub.eval_isSup hA hs
        (ScottOpen.preimage f f.continuous U)).2 (τ U) (by
          rintro _ ⟨μ, hμA, rfl⟩
          exact hτ ⟨μ, hμA, rfl⟩ U)

/-! ## The internally proved local-continuity lemma -/

/-- Preimages under a pointwise directed supremum are the directed union of
the preimages.  This is the topological core of `lem:V-local`. -/
theorem preimage_eq_sUnion_of_pointwise_isSup
    {D : Type u} {E : Type v} [Preorder D] [Preorder E]
    {A : Set (AbramskyJung.Chapter2.ScottContFun D E)}
    (hA : DirectedSet A)
    (f : AbramskyJung.Chapter2.ScottContFun D E)
    (hf : ∀ x : D,
      IsSup ((fun g : AbramskyJung.Chapter2.ScottContFun D E => g x) '' A)
        (f x))
    (U : ScottOpen E) :
    ScottOpen.preimage f f.continuous U =
      ScottOpen.sUnion
        ((fun g : AbramskyJung.Chapter2.ScottContFun D E =>
          ScottOpen.preimage g g.continuous U) '' A) := by
  apply ScottOpen.ext
  ext x
  constructor
  · intro hfxU
    have hEvalDir : DirectedSet
        ((fun g : AbramskyJung.Chapter2.ScottContFun D E => g x) '' A) :=
      hA.image (by intro g h hgh; exact hgh x)
    rcases U.inaccessible hEvalDir (hf x) hfxU with ⟨y, hy, hyU⟩
    rcases hy with ⟨g, hgA, rfl⟩
    apply ScottOpen.mem_sUnion_iff.mpr
    exact ⟨ScottOpen.preimage g g.continuous U, ⟨g, hgA, rfl⟩, hyU⟩
  · intro hx
    rcases ScottOpen.mem_sUnion_iff.mp hx with ⟨V, hxV, hx⟩
    rcases hxV with ⟨g, hgA, rfl⟩
    exact U.upper ((hf x).1 ⟨g, hgA, rfl⟩) hx

/-- Source lemma `lem:V-local`: pushforward preserves pointwise directed
suprema of Scott-continuous maps.  No Jones axiom is used. -/
theorem V_local
    {D : Type u} {E : Type v} [Preorder D] [Preorder E]
    {A : Set (AbramskyJung.Chapter2.ScottContFun D E)}
    (hA : DirectedSet A)
    (f : AbramskyJung.Chapter2.ScottContFun D E)
    (hf : ∀ x : D,
      IsSup ((fun g : AbramskyJung.Chapter2.ScottContFun D E => g x) '' A)
        (f x))
    (μ : VSub D) :
    IsSup ((fun g : AbramskyJung.Chapter2.ScottContFun D E =>
      pushforward g μ) '' A) (pushforward f μ) := by
  constructor
  · rintro _ ⟨g, hgA, rfl⟩ U
    exact pushforward_mono_map
      (fun x => (hf x).1 ⟨g, hgA, rfl⟩) μ U
  · intro τ hτ U
    let pre : AbramskyJung.Chapter2.ScottContFun D E → ScottOpen D :=
      fun g => ScottOpen.preimage g g.continuous U
    have hPreDir : DirectedSet (pre '' A) :=
      hA.image (by
        intro g h hgh
        exact ScottOpen.preimage_mono_map g.continuous h.continuous hgh U)
    have hPreSup : IsSup (pre '' A)
        (ScottOpen.preimage f f.continuous U) := by
      have hEq := preimage_eq_sUnion_of_pointwise_isSup hA f hf U
      rw [hEq]
      exact ScottOpen.sUnion_isSup (pre '' A)
    have hMassSup := μ.1.continuous.maps_isSup hPreDir hPreSup
    exact hMassSup.2 (τ U) (by
      rintro _ ⟨V, ⟨g, hgA, rfl⟩, rfl⟩
      exact hτ ⟨g, hgA, rfl⟩ U)

/-- Bundled identity map used by the identity-specialized local theorem. -/
def idMap {D : Type u} [Preorder D] :
    AbramskyJung.Chapter2.ScottContFun D D where
  toFun := fun x => x
  continuous := AbramskyJung.Chapter2.scottContinuous_id

@[simp] theorem pushforward_idMap {D : Type u} [Preorder D] (μ : VSub D) :
    pushforward (idMap (D := D)) μ = μ := by
  apply VSub.ext
  intro U
  have hpre : ScottOpen.preimage (fun x : D => x)
      AbramskyJung.Chapter2.scottContinuous_id U = U := by
    apply ScottOpen.ext
    rfl
  exact congrArg μ hpre

/-- The identity-specialized conclusion of `lem:V-local`. -/
theorem V_local_identity
    {D : Type u} [Preorder D]
    {A : Set (AbramskyJung.Chapter2.ScottContFun D D)}
    (hA : DirectedSet A)
    (hBelow : ∀ g ∈ A, g ≤ idMap)
    (hSup : ∀ x : D,
      IsSup ((fun g : AbramskyJung.Chapter2.ScottContFun D D => g x) '' A) x)
    (μ : VSub D) :
    (∀ g ∈ A, pushforward g μ ≤ μ) ∧
      IsSup ((fun g : AbramskyJung.Chapter2.ScottContFun D D =>
        pushforward g μ) '' A) μ := by
  constructor
  · intro g hgA
    simpa using pushforward_mono_map (hBelow g hgA) μ
  · simpa using V_local hA (idMap (D := D)) hSup μ

end ContinuousValuation

/-! Public manuscript notation. -/

abbrev ScottOpen (D : Type u) [Preorder D] := ContinuousValuation.ScottOpen D
abbrev ContinuousValuation (D : Type u) [Preorder D] :=
  ContinuousValuation.Valuation D
abbrev VSub (D : Type u) [Preorder D] := ContinuousValuation.VSub D
abbrev VOne (D : Type u) [Preorder D] := ContinuousValuation.VOne D
abbrev ValuationKernel (D : Type u) (E : Type v) [Preorder D] [Preorder E] :=
  AbramskyJung.Chapter2.ScottContFun D (VSub E)

end FiniteValuationApproximable
