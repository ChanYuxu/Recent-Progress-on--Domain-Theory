import Practice.DomainTheory.Topology.ScottTopology

/-!
# Finite approximation for the unit-interval retract counterexample

This file contains the source-facing order-theoretic definitions used in
`unit_interval_retracts_quasicontinuous_domains_style_matched_副本.tex`.

Source version: SHA-256
`00c59c1953e50628793d3f7a789187aa3051405999b4d72ddfbd29af41c00b04`.

The concrete sparse interval lattice is developed in a separate module.  Keeping
the definitions here makes the distinction between ordinary way-below and
finite-family way-below explicit.
-/

set_option autoImplicit false
set_option linter.unnecessarySimpa false

universe u

namespace UnitIntervalRetracts

open Set
open AbramskyJung.Chapter2

section FiniteApproximation

variable {α : Type u} [Preorder α]

/-- A member of `P^{(<ω)}`: a nonempty finite subset. -/
def FiniteFamily (α : Type u) :=
  {F : Set α // F.Finite ∧ F.Nonempty}

instance : SetLike (FiniteFamily α) α where
  coe F := F.1
  coe_injective' _ _ h := Subtype.ext h

omit [Preorder α] in
theorem FiniteFamily.finite (F : FiniteFamily α) : (F : Set α).Finite :=
  F.2.1

omit [Preorder α] in
theorem FiniteFamily.nonempty (F : FiniteFamily α) : (F : Set α).Nonempty :=
  F.2.2

/-- The paper's relation `𝒜 ≪ 𝒞` between subsets of a preorder. -/
def FamilyWayBelow (A C : Set α) : Prop :=
  ∀ ⦃D : Set α⦄ ⦃s : α⦄,
    DirectedSet D →
    IsSup D s →
    s ∈ AbramskyJung.Chapter2.upperClosure C →
    ∃ d ∈ D, d ∈ AbramskyJung.Chapter2.upperClosure A

/-- The abbreviation `𝓕 ≪ p` from the paper. -/
def FiniteWayBelow (F : FiniteFamily α) (p : α) : Prop :=
  FamilyWayBelow (F : Set α) ({p} : Set α)

/-- The finite families way below `p`. -/
def finiteApproximants (p : α) : Set (FiniteFamily α) :=
  {F | FiniteWayBelow F p}

/-- A family of sets is filtered under inclusion.  Nonemptiness is explicit. -/
def FilteredUnderInclusion (𝒰 : Set (Set α)) : Prop :=
  𝒰.Nonempty ∧
    ∀ ⦃U V : Set α⦄, U ∈ 𝒰 → V ∈ 𝒰 →
      ∃ W ∈ 𝒰, W ⊆ U ∩ V

/-- The source definition of a quasicontinuous preorder. -/
def IsQuasicontinuous (α : Type u) [Preorder α] : Prop :=
  ∀ p : α,
    let 𝒰 : Set (Set α) :=
      {U | ∃ F : FiniteFamily α, FiniteWayBelow F p ∧
        U = AbramskyJung.Chapter2.upperClosure (F : Set α)}
    FilteredUnderInclusion 𝒰 ∧
      ⋂₀ 𝒰 = AbramskyJung.Chapter2.upperClosure ({p} : Set α)

/-- The source definition of a quasialgebraic preorder. -/
def IsQuasialgebraic (α : Type u) [Preorder α] : Prop :=
  ∀ p : α,
    let 𝒰 : Set (Set α) :=
      {U | ∃ F : FiniteFamily α,
        p ∈ AbramskyJung.Chapter2.upperClosure (F : Set α) ∧
        FamilyWayBelow (F : Set α) (F : Set α) ∧
        U = AbramskyJung.Chapter2.upperClosure (F : Set α)}
    FilteredUnderInclusion 𝒰 ∧
      ⋂₀ 𝒰 = AbramskyJung.Chapter2.upperClosure ({p} : Set α)

/-- Every family way below itself generates a Scott-open upper set.  This is the
forward implication of Lemma `lem:finitely-generated-open`; finiteness is not
needed for the order-theoretic argument. -/
theorem familyWayBelow_self_scottOpen {A : Set α}
    (hA : FamilyWayBelow A A) :
    ScottOpen (AbramskyJung.Chapter2.upperClosure A) := by
  constructor
  · intro x y hy hxy hx
    exact hy (isUpperSet_upperClosure A hx hxy)
  · intro D s hD hDcompl hs hsOpen
    rcases hA hD hs hsOpen with ⟨d, hdD, hdOpen⟩
    exact hDcompl hdD hdOpen

/-- A Scott-open finitely generated upper set has its generators way below
themselves.  Again, the proof works for an arbitrary generating set. -/
theorem familyWayBelow_self_of_scottOpen {A : Set α}
    (hA : ScottOpen (AbramskyJung.Chapter2.upperClosure A)) :
    FamilyWayBelow A A := by
  intro D s hD hs hsOpen
  by_contra hmiss
  have hDcompl : D ⊆ (AbramskyJung.Chapter2.upperClosure A)ᶜ := by
    intro d hdD hdOpen
    exact hmiss ⟨d, hdD, hdOpen⟩
  exact hA.2 hD hDcompl hs hsOpen

/-- Lemma `lem:finitely-generated-open` from the paper. -/
theorem familyWayBelow_self_iff_scottOpen (F : FiniteFamily α) :
    FamilyWayBelow (F : Set α) (F : Set α) ↔
      ScottOpen (AbramskyJung.Chapter2.upperClosure (F : Set α)) :=
  ⟨familyWayBelow_self_scottOpen, familyWayBelow_self_of_scottOpen⟩

/-- Applying finite-family way-below to the directed singleton shows that the
target belongs to the generated upper set. -/
theorem mem_upperClosure_of_finiteWayBelow {F : FiniteFamily α} {p : α}
    (hF : FiniteWayBelow F p) :
    p ∈ AbramskyJung.Chapter2.upperClosure (F : Set α) := by
  rcases hF (directed_singleton p) (isSup_singleton p)
      (AbramskyJung.Chapter2.subset_upperClosure ({p} : Set α) (by simp)) with
    ⟨d, hd, hdF⟩
  have hdp : d = p := by simpa using hd
  simpa [hdp] using hdF

/-- Ordinary way-below implies the underlying order relation. -/
theorem wayBelow_le {x y : α} (hxy : x ≪ y) : x ≤ y :=
  prop_2_2_2_1 hxy

end FiniteApproximation

end UnitIntervalRetracts
