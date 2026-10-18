import FiniteValuationApproximable.Rounding
import FiniteValuationApproximable.Abstract.FVA

/-!
# Comparison results: finite stabilization and exact conditional boundaries

This module formalizes the parts of manuscript items `lem:finite-FVA-retract`,
`lem:valuation-convex-connected`, `prop:B5-not-FVA`, `prop:omega-bc-fva`,
`thm:category-size`, and the following countability remark that are justified
by the current concrete finite-valuation API.

The main unconditional result is the finite stabilization argument: on a
finite carrier, an increasing approximate identity attains the identity at
one common stage.  A finite-valuation factorization of that stage is therefore
a genuine Scott-continuous section--retraction pair through a concrete finite
subprobability simplex.  This is the order-theoretic content of
`lem:finite-FVA-retract`.

The module also proves the algebraic convexity of common stochastic upper
cones and the exact finite-poset calculation used in the manuscript's `B5`
argument.  It does **not** identify the coefficient topology with the Scott
topology, infer connectedness from that algebraic convexity, or conclude that
`B5` is not FVA.  Those are explicit topology boundaries.

Likewise, the countable diagonal-choice and set-theoretic category lemmas
below isolate pure internal logic.  They do **not** assert the external
classification results `BC ⊆ RB`, the cited finite-poset classification, or
any of the strict class inclusions without their witnesses.
-/

set_option autoImplicit false
set_option linter.unnecessarySimpa false

universe u v w

namespace FiniteValuationApproximable

open scoped BigOperators
open Set
open AbstractApproximation

section FiniteStabilization

variable {D : Type u} [Fintype D] [PartialOrder D]

/-- On a finite carrier, the directed pointwise range of an increasing
approximate identity contains its prescribed supremum.  This is the
pointwise stabilization step in source item `lem:finite-FVA-retract`. -/
theorem AbstractApproximation.IncreasingApproximateIdentity.exists_map_eq_of_finite
    (A : IncreasingApproximateIdentity D) (x : D) :
    ∃ n : Nat, A.map n x = x := by
  let R : Set D := Set.range (fun n => A.map n x)
  have hRfinite : R.Finite := Set.toFinite R
  obtain ⟨z, hzR, hzSup⟩ :=
    AbramskyJung.Chapter2.DirectedSet.exists_isSup_of_finite
      (A.range_directed x) hRfinite
  obtain ⟨n, rfl⟩ := hzR
  exact ⟨n, le_antisymm (A.below_id n x)
    ((A.pointwise_sup x).2 (A.map n x) hzSup.1)⟩

/-- Once one stage fixes a point, every later stage fixes it as well. -/
theorem AbstractApproximation.IncreasingApproximateIdentity.map_eq_upward
    (A : IncreasingApproximateIdentity D) (x : D) {m n : Nat}
    (hm : A.map m x = x) (hmn : m ≤ n) :
    A.map n x = x := by
  apply le_antisymm (A.below_id n x)
  calc
    x = A.map m x := hm.symm
    _ ≤ A.map n x := A.monotone hmn x

/-- Finite uniformization of the preceding pointwise stabilization: one
stage of an increasing approximate identity is literally the identity map. -/
theorem AbstractApproximation.IncreasingApproximateIdentity.exists_map_eq_id_of_finite
    (A : IncreasingApproximateIdentity D) :
    ∃ n : Nat, ∀ x : D, A.map n x = x := by
  exact exists_nat_forall_fintype
    (fun x n => A.map n x = x)
    A.exists_map_eq_of_finite
    (fun x _m _n hm hmn => A.map_eq_upward x hm hmn)

/-- A factorization of an endomap that is pointwise the identity is a genuine
Scott-continuous section--retraction pair through its middle object. -/
def AbstractApproximation.ScottFactorization.toContinuousRetractOfEqId
    {B : Type v} [Preorder B]
    {f : D → D} (F : ScottFactorization f B)
    (hfix : ∀ x : D, f x = x) :
    AbramskyJung.Chapter3.ContinuousSectionRetractionPair D B where
  s := F.encode
  r := F.decode
  monotone_s := F.encode_continuous.monotone
  monotone_r := F.decode_continuous.monotone
  retract := fun x => (F.factor x).trans (hfix x)
  continuous_s := F.encode_continuous
  continuous_r := F.decode_continuous

/-- Exact finite stabilization/retract core of source item
`lem:finite-FVA-retract`: any finite carrier equipped with an FVA approximate
identity is a Scott-continuous retract of `V_{≤1}(P)` for some finite poset
`P`.

No topology, bounded-completeness, or classification assumption is used. -/
theorem FVApproximateIdentity.exists_finiteValuationRetract_of_finite
    (A : FVApproximateIdentity.{u, w} D) :
    ∃ P : FinitePoset.{w},
      Nonempty
        (AbramskyJung.Chapter3.ContinuousSectionRetractionPair D P.VSub) := by
  obtain ⟨n, hn⟩ :=
    A.toIncreasingApproximateIdentity.exists_map_eq_id_of_finite
  obtain ⟨F⟩ := A.factorable n
  exact ⟨F.stage,
    ⟨F.factorization.toContinuousRetractOfEqId hn⟩⟩

/-- Source-facing wrapper for `lem:finite-FVA-retract` in the current API.
The continuous-dcpo component of `IsFVA` is retained, although finite
stabilization itself only uses the approximation component. -/
theorem IsFVA.exists_finiteValuationRetract_of_finite
    (hD : IsFVA.{u, w} D) :
    ∃ P : FinitePoset.{w},
      Nonempty
        (AbramskyJung.Chapter3.ContinuousSectionRetractionPair D P.VSub) := by
  obtain ⟨A⟩ := hD.2
  exact A.exists_finiteValuationRetract_of_finite

end FiniteStabilization

section ValuationConvexityCore

variable {P : Type u} [Fintype P] [PartialOrder P]

/-- The affine combination `(1-t)p+tq`, bundled back into the finite
subprobability simplex. -/
noncomputable def convexCombinationVector
    (t : Real) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (p q : SubprobabilityVector P) : SubprobabilityVector P where
  coeff x := (1 - t) * p x + t * q x
  coeff_nonneg x :=
    add_nonneg
      (mul_nonneg (sub_nonneg.mpr ht1) (p.coeff_nonneg x))
      (mul_nonneg ht0 (q.coeff_nonneg x))
  total_le_one := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    calc
      (1 - t) * (∑ x, p x) + t * (∑ x, q x) ≤
          (1 - t) * 1 + t * 1 :=
        add_le_add
          (mul_le_mul_of_nonneg_left p.total_le_one (sub_nonneg.mpr ht1))
          (mul_le_mul_of_nonneg_left q.total_le_one ht0)
      _ = 1 := by ring

@[simp]
theorem convexCombinationVector_apply
    (t : Real) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (p q : SubprobabilityVector P) (x : P) :
    convexCombinationVector t ht0 ht1 p q x =
      (1 - t) * p x + t * q x :=
  rfl

/-- Finite mass is affine in the coefficient vector. -/
theorem mass_convexCombinationVector
    (t : Real) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (p q : SubprobabilityVector P) (S : Set P) :
    (convexCombinationVector t ht0 ht1 p q).mass S =
      (1 - t) * p.mass S + t * q.mass S := by
  classical
  simp only [SubprobabilityVector.mass]
  calc
    (∑ x, if x ∈ S then convexCombinationVector t ht0 ht1 p q x else 0) =
        ∑ x, ((1 - t) * (if x ∈ S then p x else 0) +
          t * (if x ∈ S then q x else 0)) := by
      apply Finset.sum_congr rfl
      intro x _hx
      by_cases hxS : x ∈ S
      · simp [hxS]
      · simp [hxS]
    _ = (1 - t) * (∑ x, if x ∈ S then p x else 0) +
          t * (∑ x, if x ∈ S then q x else 0) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

/-- Upper-set observations, hence stochastic-order coordinates, are affine. -/
theorem upperMass_convexCombinationVector
    (t : Real) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (p q : SubprobabilityVector P) (U : UpperSet P) :
    upperMass (convexCombinationVector t ht0 ht1 p q) U =
      (1 - t) * upperMass p U + t * upperMass q U := by
  exact mass_convexCombinationVector t ht0 ht1 p q (U : Set P)

/-- The set of common stochastic upper bounds of two finite valuations. -/
def commonStochasticUpperCone
    (p q : SubprobabilityVector P) : Set (SubprobabilityVector P) :=
  {r | p ≤ r ∧ q ≤ r}

/-- Algebraic core of source item `lem:valuation-convex-connected`: common
upper-bound sets in a finite subprobability simplex are closed under every
convex combination.

This theorem asserts convexity only.  Turning it into Scott connectedness
still requires the manuscript's unformalized comparison between the Scott and
relative Euclidean topologies. -/
theorem commonStochasticUpperCone_convexCombination
    {p q r s : SubprobabilityVector P}
    (hr : r ∈ commonStochasticUpperCone p q)
    (hs : s ∈ commonStochasticUpperCone p q)
    (t : Real) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    convexCombinationVector t ht0 ht1 r s ∈
      commonStochasticUpperCone p q := by
  constructor
  · intro U
    rw [upperMass_convexCombinationVector]
    calc
      upperMass p U =
          (1 - t) * upperMass p U + t * upperMass p U := by ring
      _ ≤ (1 - t) * upperMass r U + t * upperMass s U :=
        add_le_add
          (mul_le_mul_of_nonneg_left (hr.1 U) (sub_nonneg.mpr ht1))
          (mul_le_mul_of_nonneg_left (hs.1 U) ht0)
  · intro U
    rw [upperMass_convexCombinationVector]
    calc
      upperMass q U =
          (1 - t) * upperMass q U + t * upperMass q U := by ring
      _ ≤ (1 - t) * upperMass r U + t * upperMass s U :=
        add_le_add
          (mul_le_mul_of_nonneg_left (hr.2 U) (sub_nonneg.mpr ht1))
          (mul_le_mul_of_nonneg_left (hs.2 U) ht0)

end ValuationConvexityCore

section B5CombinatorialCore

/-- The five-element poset used in source item `prop:B5-not-FVA`: `bot` is
least, `a` and `b` are incomparable, and their two incomparable minimal common
upper bounds are `c` and `d`. -/
inductive B5 where
  | bot
  | a
  | b
  | c
  | d
  deriving DecidableEq, Fintype

namespace B5

/-- Explicit order relation of the five-element bow-tie poset. -/
def orderRel : B5 → B5 → Prop
  | .bot, _ => True
  | .a, .a => True
  | .a, .c => True
  | .a, .d => True
  | .b, .b => True
  | .b, .c => True
  | .b, .d => True
  | .c, .c => True
  | .d, .d => True
  | _, _ => False

instance : LE B5 := ⟨orderRel⟩

instance : PartialOrder B5 where
  le_refl x := by cases x <;> simp [LE.le, orderRel]
  le_trans x y z := by
    cases x <;> cases y <;> cases z <;> simp_all [LE.le, orderRel]
  le_antisymm x y := by
    cases x <;> cases y <;> simp_all [LE.le, orderRel]

instance : OrderBot B5 where
  bot := .bot
  bot_le x := by cases x <;> simp [LE.le, orderRel]

/-- The concrete bundled finite poset corresponding to `B5`. -/
def finitePoset : FinitePoset where
  carrier := B5
  fintype := inferInstance
  partialOrder := inferInstance

@[simp] theorem a_le_c : B5.a ≤ B5.c := by simp [LE.le, orderRel]
@[simp] theorem b_le_c : B5.b ≤ B5.c := by simp [LE.le, orderRel]
@[simp] theorem a_le_d : B5.a ≤ B5.d := by simp [LE.le, orderRel]
@[simp] theorem b_le_d : B5.b ≤ B5.d := by simp [LE.le, orderRel]

/-- Exact common-upper-bound calculation used in the `B5` obstruction. -/
theorem commonUpper_ab_iff (x : B5) :
    B5.a ≤ x ∧ B5.b ≤ x ↔ x = B5.c ∨ x = B5.d := by
  cases x <;> simp [LE.le, orderRel]

/-- The two peaks are genuinely order-incomparable. -/
theorem peaks_incomparable :
    ¬ B5.c ≤ B5.d ∧ ¬ B5.d ≤ B5.c := by
  simp [LE.le, orderRel]

/-- Common upper bounds, in an ambient preorder, of the embedded points `a`
and `b`. -/
def commonUpperHull {E : Type v} [Preorder E] (i : B5 → E) : Set E :=
  {y | i B5.a ≤ y ∧ i B5.b ≤ y}

/-- Pure order-theoretic core of the retraction calculation in
`prop:B5-not-FVA`: under any monotone section/retraction, the common-upper hull
of the images of `a,b` maps **onto exactly** the two peaks `{c,d}`. -/
theorem retract_image_commonUpperHull
    {E : Type v} [Preorder E]
    (i : B5 → E) (r : E → B5)
    (hi : Monotone i) (hr : Monotone r)
    (hretract : ∀ x : B5, r (i x) = x) :
    r '' commonUpperHull i = ({B5.c, B5.d} : Set B5) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have ha : B5.a ≤ r y := by
      calc
        B5.a = r (i B5.a) := (hretract B5.a).symm
        _ ≤ r y := hr hy.1
    have hb : B5.b ≤ r y := by
      calc
        B5.b = r (i B5.b) := (hretract B5.b).symm
        _ ≤ r y := hr hy.2
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using
      (commonUpper_ab_iff (r y)).mp ⟨ha, hb⟩
  · intro hx
    have hx' : x = B5.c ∨ x = B5.d := by
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hx
    rcases hx' with rfl | rfl
    · refine ⟨i B5.c, ?_, hretract B5.c⟩
      exact ⟨hi a_le_c, hi b_le_c⟩
    · refine ⟨i B5.d, ?_, hretract B5.d⟩
      exact ⟨hi a_le_d, hi b_le_d⟩

/-- Continuous-retract specialization of `retract_image_commonUpperHull`.
Continuity is present because this is the exact shape produced by finite FVA
stabilization; the image equality itself uses only monotonicity. -/
theorem continuousRetract_image_commonUpperHull
    {E : Type v} [Preorder E]
    (sr : AbramskyJung.Chapter3.ContinuousSectionRetractionPair B5 E) :
    sr.r '' commonUpperHull sr.s = ({B5.c, B5.d} : Set B5) :=
  retract_image_commonUpperHull sr.s sr.r sr.monotone_s sr.monotone_r sr.retract

end B5

/-- Strongest currently justified FVA-facing prefix of `prop:B5-not-FVA`.
If `B5` were FVA, finite stabilization would produce a concrete finite
valuation stage whose common-upper hull maps exactly onto `{c,d}`.

The manuscript obtains a contradiction by showing that the hull is
Scott-connected while `{c,d}` is disconnected.  Since that topology bridge is
not yet formalized, this theorem intentionally stops at the exact image
equality and does not assert `¬ IsFVA B5`. -/
theorem b5_FVA_implies_twoPeak_retract_image
    (hB5 : IsFVA.{0, 0} B5) :
    ∃ P : FinitePoset.{0},
      ∃ sr : AbramskyJung.Chapter3.ContinuousSectionRetractionPair B5 P.VSub,
        sr.r '' B5.commonUpperHull sr.s = ({B5.c, B5.d} : Set B5) := by
  obtain ⟨P, ⟨sr⟩⟩ := hB5.exists_finiteValuationRetract_of_finite
  exact ⟨P, sr, B5.continuousRetract_image_commonUpperHull sr⟩

end B5CombinatorialCore

section CountableDirectedExtraction

variable {I : Type u} [Preorder I]

/-- Pairwise upward directedness of an index preorder.  This is the precise
choice principle used when extracting a sequence from a directed family and
a countable list of requirements. -/
def IsUpwardDirectedIndex (I : Type u) [Preorder I] : Prop :=
  ∀ i j : I, ∃ k : I, i ≤ k ∧ j ≤ k

namespace CountableRequirementChoice

variable (hdir : IsUpwardDirectedIndex I)
variable (R : Nat → I → Prop)
variable (hexists : ∀ n : Nat, ∃ i : I, R n i)

private noncomputable def witness (n : Nat) : I :=
  Classical.choose (hexists n)

private theorem witness_spec (n : Nat) : R n (witness R hexists n) :=
  Classical.choose_spec (hexists n)

private noncomputable def upper (i j : I) : I :=
  Classical.choose (hdir i j)

private theorem le_upper_left (i j : I) : i ≤ upper hdir i j :=
  (Classical.choose_spec (hdir i j)).1

private theorem le_upper_right (i j : I) : j ≤ upper hdir i j :=
  (Classical.choose_spec (hdir i j)).2

/-- Recursively combine the previous index with a witness for the next
requirement. -/
noncomputable def sequence : Nat → I
  | 0 => witness R hexists 0
  | n + 1 => upper hdir (sequence n) (witness R hexists (n + 1))

theorem sequence_le_succ (n : Nat) :
    sequence hdir R hexists n ≤ sequence hdir R hexists (n + 1) :=
  le_upper_left hdir _ _

theorem sequence_monotone : Monotone (sequence hdir R hexists) :=
  monotone_nat_of_le_succ (sequence_le_succ hdir R hexists)

/-- Countable diagonal extraction core used in the proof architecture of
`prop:omega-bc-fva`: if requirements persist upward, stage `n` satisfies all
requirements numbered at most `n`.  This does not supply the external
`BC ⊆ RB` theorem or the valuation factorization of the extracted maps. -/
theorem sequence_satisfies
    (hup : ∀ n : Nat, ∀ {i j : I}, R n i → i ≤ j → R n j) :
    ∀ {k n : Nat}, k ≤ n → R k (sequence hdir R hexists n) := by
  intro k n hkn
  induction n with
  | zero =>
      have hk : k = 0 := Nat.eq_zero_of_le_zero hkn
      subst k
      exact witness_spec R hexists 0
  | succ n ih =>
      by_cases hk : k = n + 1
      · subst k
        exact hup (n + 1) (witness_spec R hexists (n + 1))
          (le_upper_right hdir _ _)
      · exact hup k (ih (by omega)) (sequence_le_succ hdir R hexists n)

end CountableRequirementChoice

end CountableDirectedExtraction

section CategoryLogic

variable {X : Type u}

/-- Two classes are incomparable when neither includes the other. -/
def SetIncomparable (A B : Set X) : Prop :=
  ¬ A ⊆ B ∧ ¬ B ⊆ A

/-- Two explicit counterexamples establish incomparability. -/
theorem setIncomparable_of_witnesses
    {A B : Set X} {x y : X}
    (hxA : x ∈ A) (hxB : x ∉ B)
    (hyB : y ∈ B) (hyA : y ∉ A) :
    SetIncomparable A B := by
  constructor
  · intro hAB
    exact hxB (hAB hxA)
  · intro hBA
    exact hyA (hBA hyB)

/-- Pure set-theoretic assembly behind source item `thm:category-size`.

The name records the conditional boundary: every inclusion and separating
witness is an argument.  In particular this theorem does not prove or import
`BC ⊆ RB`, the finite-poset classification, or either manuscript witness. -/
theorem category_size_logic_conditional
    (BC FVA FS RB : Set X)
    (hBCFVA : BC ⊆ FVA) {bcStrict : X}
    (hbcFVA : bcStrict ∈ FVA) (hbcNotBC : bcStrict ∉ BC)
    (hFVAFS : FVA ⊆ FS) {fvaStrict : X}
    (hfvaFS : fvaStrict ∈ FS) (hfvaNotFVA : fvaStrict ∉ FVA)
    {fvaNotRb rbNotFva : X}
    (hfvaMem : fvaNotRb ∈ FVA) (hfvaNot : fvaNotRb ∉ RB)
    (hrbMem : rbNotFva ∈ RB) (hrbNot : rbNotFva ∉ FVA) :
    BC ⊂ FVA ∧ FVA ⊂ FS ∧ SetIncomparable FVA RB := by
  refine ⟨?_, ?_, ?_⟩
  · exact hBCFVA.ssubset_of_mem_notMem hbcFVA hbcNotBC
  · exact hFVAFS.ssubset_of_mem_notMem hfvaFS hfvaNotFVA
  · exact setIncomparable_of_witnesses hfvaMem hfvaNot hrbMem hrbNot

/-- Logical content of the manuscript's countability remark.  An object that
already lies in the chosen `CountablyBased` class but not in `FVA` witnesses
that its failure of FVA membership cannot be identified with failure of that
countability property.  Both semantic facts remain explicit hypotheses. -/
theorem countability_remark_logic_conditional
    (FVA CountablyBased : Set X) {x : X}
    (hxCountable : x ∈ CountablyBased) (hxNotFVA : x ∉ FVA) :
    x ∈ CountablyBased \ FVA :=
  ⟨hxCountable, hxNotFVA⟩

end CategoryLogic

end FiniteValuationApproximable
