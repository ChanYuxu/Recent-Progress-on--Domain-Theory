import Practice.DomainTheory.Papers.UnitIntervalRetracts.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.Compact

/-!
# The sparse interval family

This module formalizes the literal interval skeleton from
`unit_interval_retracts_quasicontinuous_domains_style_matched_副本.tex`.
All interiors below are interiors in the subtype `X = [0,1]`, hence are
relative interiors exactly as in the source.
-/

set_option autoImplicit false
set_option linter.unnecessarySimpa false

namespace UnitIntervalRetracts

open Set Filter Topology

noncomputable section

/-- The unit interval, carrying the subtype topology and metric. -/
abbrev X := Set.Icc (0 : ℝ) 1

/-- Valid source indices `(n,k)` with `n ≥ 1` and `k ≤ 2^n`. -/
def BasicIndex :=
  {p : ℕ × ℕ // 1 ≤ p.1 ∧ p.2 ≤ 2 ^ p.1}

deriving instance Countable for BasicIndex
deriving instance DecidableEq for BasicIndex

namespace BasicIndex

def level (i : BasicIndex) : ℕ := i.1.1

def position (i : BasicIndex) : ℕ := i.1.2

theorem one_le_level (i : BasicIndex) : 1 ≤ i.level := i.2.1

theorem position_le (i : BasicIndex) : i.position ≤ 2 ^ i.level := i.2.2

/-- The index `(1,1)`, whose basic interval is all of `X`. -/
def whole : BasicIndex :=
  ⟨(1, 1), by norm_num⟩

end BasicIndex

/-- The literal endpoints `(k-1)/2^n` and `(k+1)/2^n`.  The subtraction is
performed after casting to `ℝ`; in particular, the `k=0` endpoint is negative. -/
noncomputable def basicLeft (i : BasicIndex) : ℝ :=
  ((i.position : ℝ) - 1) / (2 : ℝ) ^ i.level

noncomputable def basicRight (i : BasicIndex) : ℝ :=
  ((i.position : ℝ) + 1) / (2 : ℝ) ^ i.level

/-- Equation `eq:J-definition`, viewed as a subset of the subtype `X`. -/
def J (i : BasicIndex) : Set X :=
  Subtype.val ⁻¹' Set.Icc (basicLeft i) (basicRight i)

theorem mem_J_iff {i : BasicIndex} {x : X} :
    x ∈ J i ↔ basicLeft i ≤ (x : ℝ) ∧ (x : ℝ) ≤ basicRight i :=
  Iff.rfl

theorem isClosed_J (i : BasicIndex) : IsClosed (J i) :=
  isClosed_Icc.preimage continuous_subtype_val

theorem J_whole : J BasicIndex.whole = Set.univ := by
  ext x
  constructor
  · simp
  · intro _hx
    change basicLeft BasicIndex.whole ≤ (x : ℝ) ∧
      (x : ℝ) ≤ basicRight BasicIndex.whole
    have hx : 0 ≤ (x : ℝ) ∧ (x : ℝ) ≤ 1 := x.2
    convert hx using 1 <;>
      norm_num [basicLeft, basicRight, BasicIndex.whole, BasicIndex.level,
        BasicIndex.position]

/-- A finite intersection of source basic intervals. -/
def basicIntersection (s : Finset BasicIndex) : Set X :=
  ⋂ i ∈ (s : Set BasicIndex), J i

theorem mem_basicIntersection_iff {s : Finset BasicIndex} {x : X} :
    x ∈ basicIntersection s ↔ ∀ i ∈ s, x ∈ J i := by
  simp [basicIntersection]

theorem basicIntersection_empty :
    basicIntersection (∅ : Finset BasicIndex) = Set.univ := by
  simp [basicIntersection]

theorem basicIntersection_union (s t : Finset BasicIndex) :
    basicIntersection (s ∪ t) = basicIntersection s ∩ basicIntersection t := by
  ext x
  simp only [mem_basicIntersection_iff, Set.mem_inter_iff]
  constructor
  · intro h
    constructor
    · intro i hi
      exact h i (Finset.mem_union_left t hi)
    · intro i hi
      exact h i (Finset.mem_union_right s hi)
  · rintro ⟨hs, ht⟩ i hi
    rcases Finset.mem_union.mp hi with hi | hi
    · exact hs i hi
    · exact ht i hi

theorem isClosed_basicIntersection (s : Finset BasicIndex) :
    IsClosed (basicIntersection s) := by
  apply isClosed_biInter
  intro i _hi
  exact isClosed_J i

/-- Equation `eq:B-definition`: nondegenerate, nonempty finite intersections
of the `J_{n,k}`.  `Set.Nontrivial` is equivalent here to positive diameter;
the exact diameter formulation is recovered below. -/
def Skeleton : Set (Set X) :=
  {B | ∃ s : Finset BasicIndex,
    s.Nonempty ∧ B = basicIntersection s ∧ B.Nontrivial}

theorem Skeleton.exists_representation {B : Set X} (hB : B ∈ Skeleton) :
    ∃ s : Finset BasicIndex,
      s.Nonempty ∧ B = basicIntersection s ∧ B.Nontrivial :=
  hB

theorem Skeleton.nontrivial {B : Set X} (hB : B ∈ Skeleton) :
    B.Nontrivial :=
  (Skeleton.exists_representation hB).choose_spec.2.2

theorem Skeleton.nonempty {B : Set X} (hB : B ∈ Skeleton) :
    B.Nonempty :=
  (Skeleton.nontrivial hB).nonempty

theorem Skeleton.isClosed {B : Set X} (hB : B ∈ Skeleton) :
    IsClosed B := by
  rcases hB with ⟨s, _hs, rfl, _hB⟩
  exact isClosed_basicIntersection s

theorem Skeleton.isBounded {B : Set X} (_hB : B ∈ Skeleton) :
    Bornology.IsBounded B :=
  Metric.isBounded_iff.2 ⟨2, by
    intro x _hx y _hy
    have hx0 : 0 ≤ (x : ℝ) := x.2.1
    have hx1 : (x : ℝ) ≤ 1 := x.2.2
    have hy0 : 0 ≤ (y : ℝ) := y.2.1
    have hy1 : (y : ℝ) ≤ 1 := y.2.2
    rw [Subtype.dist_eq, Real.dist_eq]
    have hxy : |(x : ℝ) - (y : ℝ)| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith
    linarith⟩

/-- The source's positive-diameter condition, derived from the nondegenerate
form used in the representation. -/
theorem Skeleton.diam_pos {B : Set X} (hB : B ∈ Skeleton) :
    0 < Metric.diam B :=
  Metric.diam_pos (Skeleton.nontrivial hB) (Skeleton.isBounded hB)

theorem skeleton_countable : Skeleton.Countable := by
  apply (Set.countable_range (fun s : Finset BasicIndex => basicIntersection s)).mono
  intro B hB
  rcases hB with ⟨s, _hs, rfl, _h_nontrivial⟩
  exact ⟨s, rfl⟩

theorem univ_mem_skeleton : (Set.univ : Set X) ∈ Skeleton := by
  refine ⟨{BasicIndex.whole}, by simp, ?_, ?_⟩
  · simpa [basicIntersection] using J_whole.symm
  · refine ⟨⟨0, by norm_num⟩, by simp, ⟨1, by norm_num⟩, by simp, ?_⟩
    norm_num

/-- The skeleton is closed under a binary intersection whenever the result is
still nondegenerate. -/
theorem skeleton_inter_of_nontrivial {A B : Set X}
    (hA : A ∈ Skeleton) (hB : B ∈ Skeleton)
    (hAB : (A ∩ B).Nontrivial) :
    A ∩ B ∈ Skeleton := by
  rcases hA with ⟨s, hs, rfl, _⟩
  rcases hB with ⟨t, ht, rfl, _⟩
  refine ⟨s ∪ t, hs.mono (Finset.subset_union_left), ?_, ?_⟩
  · exact (basicIntersection_union s t).symm
  · simpa [basicIntersection_union] using hAB

/-- Equation `eq:P-definition`: the sparse skeleton, every singleton, and the
empty set. -/
def IsSparse (A : Set X) : Prop :=
  A ∈ Skeleton ∨ (∃ x : X, A = {x}) ∨ A = ∅

/-- The carrier `P` of the counterexample. -/
def P :=
  {A : Set X // IsSparse A}

instance : SetLike P X where
  coe A := A.1
  coe_injective' _ _ h := Subtype.ext h

theorem P.isSparse (A : P) : IsSparse (A : Set X) := A.2

/-- The source singleton layer. -/
def singleton (x : X) : P :=
  ⟨{x}, Or.inr (Or.inl ⟨x, rfl⟩)⟩

/-- The source greatest element `top = ∅`. -/
def empty : P :=
  ⟨∅, Or.inr (Or.inr rfl)⟩

/-- The source least element `bottom = X`. -/
def whole : P :=
  ⟨Set.univ, Or.inl univ_mem_skeleton⟩

/-- A skeleton member as an element of `P`. -/
def ofSkeleton {B : Set X} (hB : B ∈ Skeleton) : P :=
  ⟨B, Or.inl hB⟩

@[simp] theorem coe_singleton (x : X) : (singleton x : Set X) = {x} := rfl

@[simp] theorem coe_empty : (empty : Set X) = ∅ := rfl

@[simp] theorem coe_whole : (whole : Set X) = Set.univ := rfl

@[simp] theorem coe_ofSkeleton {B : Set X} (hB : B ∈ Skeleton) :
    (ofSkeleton hB : Set X) = B := rfl

/-- Equation `eq:reverse-order`. -/
instance : LE P where
  le A B := (B : Set X) ⊆ (A : Set X)

theorem le_def {A B : P} : A ≤ B ↔ (B : Set X) ⊆ (A : Set X) :=
  Iff.rfl

instance : PartialOrder P where
  le_refl A := Set.Subset.rfl
  le_trans _A _B _C hAB hBC := Set.Subset.trans hBC hAB
  le_antisymm A B hAB hBA := SetLike.coe_injective (Set.Subset.antisymm hBA hAB)

theorem whole_le (A : P) : whole ≤ A := by
  intro x _hx
  simp

theorem le_empty (A : P) : A ≤ empty := by
  intro x hx
  cases hx

theorem singleton_injective : Function.Injective singleton := by
  intro x y hxy
  have hsets : ({x} : Set X) = {y} := by
    simpa using congrArg (fun A : P => (A : Set X)) hxy
  simpa using Set.singleton_eq_singleton_iff.mp hsets

end

end UnitIntervalRetracts
