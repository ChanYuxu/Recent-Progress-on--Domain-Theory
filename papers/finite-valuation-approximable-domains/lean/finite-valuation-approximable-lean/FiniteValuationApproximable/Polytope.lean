import FiniteValuationApproximable.FiniteValuation.Basic

/-!
# Finite monotone-valuation polytopes: order-theoretic core

This file formalizes the exact finite-dimensional prefix of the section
`Finite monotone-valuation polytopes` in `main (17).tex` (source SHA-256
`4b2e65f0f96347bea4df7571e8993ad6e888c0ff7181c1305c5056880365ac94`).

The formalized results are:

* the space `MonotoneTable A P` of monotone maps
  `A -> SubprobabilityVector P`, with its pointwise order;
* the upper-set coordinate characterization of that order;
* the upper-set order cone `UpperOrderCone P` in the ambient space
  `P -> ℝ`, its closure under the conic operations, and its pointedness;
* membership of every standard-basis and cover-transfer generator in that
  cone, hence the rigorously proved inclusion from their conic hull into the
  upper-set cone;
* the product order cone for tables and the exact difference-vector criterion;
* recovery of atomic coordinates from two upper-set coordinates, including
  the corresponding convergence implication used in the proof of
  `lem:euclidean-scott`;
* an explicit table satisfying strictly every nontrivial defining linear
  inequality, which is the finite-dimensional algebraic core of
  `lem:interior-point`.

The reverse conic-hull inclusion in `lem:cone-generators` needs a
finite-dimensional bipolar/separation theorem plus the Hasse-network
argument.  The full Euclidean-interior and Scott-topological statements also
need topology/domain APIs not introduced here.  They are intentionally not
represented by assumptions or by structures containing their conclusions.
-/

set_option autoImplicit false
set_option linter.unnecessarySimpa false

universe u v w

namespace FiniteValuationApproximable

open scoped BigOperators Classical Topology
open Set Filter

section MonotoneTables

variable (A : Type u) (P : Type v)
variable [Preorder A] [Fintype P] [PartialOrder P]

/-- The manuscript's finite monotone-valuation space `M(A,P)`: monotone maps
from `A` to finite subprobability vectors on `P`. -/
structure MonotoneTable where
  toFun : A -> SubprobabilityVector P
  monotone' : Monotone toFun

/-- Short notation matching `M(A,P)` in the source. -/
abbrev M := MonotoneTable

namespace MonotoneTable

instance : CoeFun (MonotoneTable A P) (fun _ => A -> SubprobabilityVector P) where
  coe x := x.toFun

@[simp]
theorem coe_mk (f : A -> SubprobabilityVector P) (hf : Monotone f) :
    ((MonotoneTable.mk f hf : MonotoneTable A P) : A -> SubprobabilityVector P) = f :=
  rfl

theorem monotone (x : MonotoneTable A P) : Monotone x :=
  x.monotone'

@[ext]
theorem ext_apply {x y : MonotoneTable A P} (h : forall a, x a = y a) : x = y := by
  cases x with
  | mk xf hxf =>
    cases y with
    | mk yf hyf =>
      congr
      funext a
      exact h a

theorem ext_coeff {x y : MonotoneTable A P}
    (h : forall a p, x a p = y a p) : x = y := by
  apply ext_apply
  intro a
  apply SubprobabilityVector.ext
  exact h a

/-- Pointwise stochastic comparison, as in the manuscript. -/
instance : LE (MonotoneTable A P) where
  le x y := forall a, x a <= y a

instance : Preorder (MonotoneTable A P) where
  le_refl x a := le_refl (x a)
  le_trans x y z hxy hyz a := le_trans (hxy a) (hyz a)

instance : PartialOrder (MonotoneTable A P) where
  le_antisymm x y hxy hyx := by
    apply ext_apply
    intro a
    exact le_antisymm (hxy a) (hyx a)

/-- The atomic coordinate `x_{a,p}`. -/
def atom {A : Type u} {P : Type v} [Preorder A] [Fintype P] [PartialOrder P]
    (x : MonotoneTable A P) (a : A) (p : P) : Real :=
  x a p

/-- The source functional `lambda_{a,U}(x) = x(a)(U)`. -/
noncomputable def upperCoordinate
    {A : Type u} {P : Type v} [Preorder A] [Fintype P] [PartialOrder P]
    (x : MonotoneTable A P) (a : A) (U : UpperSet P) : Real :=
  upperMass (x a) U

@[simp]
theorem atom_apply (x : MonotoneTable A P) (a : A) (p : P) :
    x.atom a p = x a p :=
  rfl

theorem le_iff_upperCoordinate {x y : MonotoneTable A P} :
    x <= y <-> forall a U, x.upperCoordinate a U <= y.upperCoordinate a U :=
  Iff.rfl

end MonotoneTable

end MonotoneTables

section UpperOrderCone

variable {P : Type v} [Fintype P] [PartialOrder P]

/-- The linear extension of upper-set mass from subprobability vectors to the
whole ambient coordinate space `P -> ℝ`. -/
noncomputable def vectorUpperMass (z : P -> Real) (U : UpperSet P) : Real :=
  ∑ p, if p ∈ (U : Set P) then z p else 0

/-- The manuscript's cone `C_P`, defined exactly by nonnegative upper-set
masses. -/
def UpperOrderCone (P : Type v) [Fintype P] [PartialOrder P] : Set (P -> Real) :=
  {z | forall U : UpperSet P, 0 <= vectorUpperMass z U}

theorem mem_upperOrderCone_iff {z : P -> Real} :
    z ∈ UpperOrderCone P <-> forall U : UpperSet P, 0 <= vectorUpperMass z U :=
  Iff.rfl

@[simp]
theorem vectorUpperMass_zero (U : UpperSet P) :
    vectorUpperMass (0 : P -> Real) U = 0 := by
  classical
  simp [vectorUpperMass]

theorem vectorUpperMass_add (z w : P -> Real) (U : UpperSet P) :
    vectorUpperMass (z + w) U = vectorUpperMass z U + vectorUpperMass w U := by
  classical
  unfold vectorUpperMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hpU : p ∈ (U : Set P) <;> simp [vectorUpperMass, hpU]

theorem vectorUpperMass_neg (z : P -> Real) (U : UpperSet P) :
    vectorUpperMass (-z) U = -vectorUpperMass z U := by
  classical
  unfold vectorUpperMass
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hpU : p ∈ (U : Set P) <;> simp [vectorUpperMass, hpU]

theorem vectorUpperMass_sub (z w : P -> Real) (U : UpperSet P) :
    vectorUpperMass (z - w) U = vectorUpperMass z U - vectorUpperMass w U := by
  rw [sub_eq_add_neg, vectorUpperMass_add, vectorUpperMass_neg]
  rfl

theorem vectorUpperMass_smul (c : Real) (z : P -> Real) (U : UpperSet P) :
    vectorUpperMass (c • z) U = c * vectorUpperMass z U := by
  classical
  unfold vectorUpperMass
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hpU : p ∈ (U : Set P) <;> simp [vectorUpperMass, hpU]

theorem zero_mem_upperOrderCone : (0 : P -> Real) ∈ UpperOrderCone P := by
  intro U
  simp

theorem add_mem_upperOrderCone {z w : P -> Real}
    (hz : z ∈ UpperOrderCone P) (hw : w ∈ UpperOrderCone P) :
    z + w ∈ UpperOrderCone P := by
  intro U
  rw [vectorUpperMass_add]
  exact add_nonneg (hz U) (hw U)

theorem nonneg_smul_mem_upperOrderCone {z : P -> Real}
    (hz : z ∈ UpperOrderCone P) {c : Real} (hc : 0 <= c) :
    c • z ∈ UpperOrderCone P := by
  intro U
  rw [vectorUpperMass_smul]
  exact mul_nonneg hc (hz U)

/-- The principal upper set generated by `p`. -/
def principalUpper (p : P) : UpperSet P :=
  ⟨Set.Ici p, isUpperSet_Ici p⟩

/-- The strict principal upper set above `p`. -/
def strictPrincipalUpper (p : P) : UpperSet P :=
  ⟨Set.Ioi p, isUpperSet_Ioi p⟩

/-- Atomic-coordinate recovery from two upper-set observations.  This is the
finite-poset identity used in the source proof of `lem:euclidean-scott`. -/
theorem vectorUpperMass_principal_eq_atom_add_strict
    (z : P -> Real) (p : P) :
    vectorUpperMass z (principalUpper p) =
      z p + vectorUpperMass z (strictPrincipalUpper p) := by
  classical
  unfold vectorUpperMass principalUpper strictPrincipalUpper
  calc
    (∑ q, if p <= q then z q else 0) =
        ∑ q, ((if q = p then z q else 0) + (if p < q then z q else 0)) := by
          apply Finset.sum_congr rfl
          intro q hq
          by_cases hpq : p <= q
          · rcases lt_or_eq_of_le hpq with hpq' | rfl
            · simp [hpq, hpq', ne_of_gt hpq']
            · simp
          · have hnlt : ¬p < q := fun hlt => hpq hlt.le
            have hne : q ≠ p := by
              intro hqp
              subst q
              exact hpq le_rfl
            simp [hpq, hnlt, hne]
    _ = (∑ q, if q = p then z q else 0) +
        ∑ q, if p < q then z q else 0 := Finset.sum_add_distrib
    _ = z p + ∑ q, if p < q then z q else 0 := by simp

theorem atom_eq_vectorUpperMass_sub_strict
    (z : P -> Real) (p : P) :
    z p = vectorUpperMass z (principalUpper p) -
      vectorUpperMass z (strictPrincipalUpper p) := by
  rw [vectorUpperMass_principal_eq_atom_add_strict]
  ring

/-- Upper-set observations separate arbitrary ambient vectors. -/
theorem vector_eq_of_vectorUpperMass_eq {z w : P -> Real}
    (h : forall U : UpperSet P, vectorUpperMass z U = vectorUpperMass w U) :
    z = w := by
  funext p
  calc
    z p = vectorUpperMass z (principalUpper p) -
        vectorUpperMass z (strictPrincipalUpper p) :=
      atom_eq_vectorUpperMass_sub_strict z p
    _ = vectorUpperMass w (principalUpper p) -
        vectorUpperMass w (strictPrincipalUpper p) := by
      rw [h (principalUpper p), h (strictPrincipalUpper p)]
    _ = w p := (atom_eq_vectorUpperMass_sub_strict w p).symm

/-- A cone is pointed when membership of both `z` and `-z` forces `z = 0`. -/
def IsPointedCone {E : Type w} [Zero E] [Neg E] (C : Set E) : Prop :=
  forall ⦃z : E⦄, z ∈ C -> -z ∈ C -> z = 0

/-- The upper-set cone `C_P` is pointed.  The proof reconstructs each atom
from the principal and strict-principal upper-set masses. -/
theorem upperOrderCone_pointed : IsPointedCone (UpperOrderCone P) := by
  intro z hz hneg
  apply vector_eq_of_vectorUpperMass_eq
  intro U
  have hzU : 0 <= vectorUpperMass z U := hz U
  have hnegU : 0 <= vectorUpperMass (-z) U := hneg U
  rw [vectorUpperMass_neg] at hnegU
  have hzero : vectorUpperMass z U = 0 := le_antisymm (by linarith) hzU
  simpa [hzero]

/-- The standard basis vector `e_p`. -/
noncomputable def standardBasis (p : P) : P -> Real :=
  fun q => if q = p then 1 else 0

@[simp]
theorem standardBasis_apply (p q : P) :
    standardBasis p q = if q = p then 1 else 0 :=
  rfl

theorem vectorUpperMass_standardBasis (p : P) (U : UpperSet P) :
    vectorUpperMass (standardBasis p) U = if p ∈ (U : Set P) then 1 else 0 := by
  classical
  unfold vectorUpperMass standardBasis
  by_cases hpU : p ∈ (U : Set P)
  · calc
      (∑ q, if q ∈ (U : Set P) then (if q = p then 1 else 0) else 0) =
          ∑ q, if q = p then (1 : Real) else 0 := by
            apply Finset.sum_congr rfl
            intro q hq
            by_cases hqp : q = p
            · subst q
              simp [hpU]
            · simp [hqp]
      _ = 1 := by simp
      _ = (if p ∈ (U : Set P) then 1 else 0) := by simp [hpU]
  · have hterm : forall q : P,
        (if q ∈ (U : Set P) then (if q = p then (1 : Real) else 0) else 0) = 0 := by
      intro q
      by_cases hqp : q = p
      · subst q
        simp [hpU]
      · simp [hqp]
    calc
      (∑ q, if q ∈ (U : Set P) then (if q = p then (1 : Real) else 0) else 0) =
          ∑ _q : P, (0 : Real) := by
            apply Finset.sum_congr rfl
            intro q hq
            exact hterm q
      _ = 0 := by simp
      _ = (if p ∈ (U : Set P) then 1 else 0) := by simp [hpU]

theorem standardBasis_mem_upperOrderCone (p : P) :
    standardBasis p ∈ UpperOrderCone P := by
  intro U
  rw [vectorUpperMass_standardBasis]
  split <;> norm_num

/-- The direction `e_q - e_p`, which moves mass upward from `p` to `q`. -/
noncomputable def transferDirection (p q : P) : P -> Real :=
  standardBasis q - standardBasis p

theorem vectorUpperMass_transferDirection (p q : P) (U : UpperSet P) :
    vectorUpperMass (transferDirection p q) U =
      (if q ∈ (U : Set P) then 1 else 0) -
        (if p ∈ (U : Set P) then 1 else 0) := by
  rw [transferDirection, vectorUpperMass_sub,
    vectorUpperMass_standardBasis, vectorUpperMass_standardBasis]

theorem transferDirection_mem_upperOrderCone {p q : P} (hpq : p <= q) :
    transferDirection p q ∈ UpperOrderCone P := by
  intro U
  rw [vectorUpperMass_transferDirection]
  by_cases hpU : p ∈ (U : Set P)
  · have hqU : q ∈ (U : Set P) := U.upper hpq hpU
    simp [hpU, hqU]
  · by_cases hqU : q ∈ (U : Set P) <;> simp [hpU, hqU]

/-- `p` is covered by `q`: this is the source relation `p \prec q`. -/
def IsCover (p q : P) : Prop :=
  p < q ∧ forall r, p < r -> r < q -> False

/-- The listed generators in equation `eq:cone-generators`. -/
def ConeGenerator (P : Type v) [Fintype P] [PartialOrder P] : Set (P -> Real) :=
  {z | (exists p, z = standardBasis p) ∨
    exists p q, IsCover p q ∧ z = transferDirection p q}

/-- An elementary, syntax-level conic hull. -/
inductive InConicHull (S : Set (P -> Real)) : (P -> Real) -> Prop
  | zero : InConicHull S 0
  | generator {z : P -> Real} : z ∈ S -> InConicHull S z
  | add {z w : P -> Real} : InConicHull S z -> InConicHull S w -> InConicHull S (z + w)
  | nonneg_smul (c : Real) {z : P -> Real} :
      0 <= c -> InConicHull S z -> InConicHull S (c • z)

/-- Every standard-basis or cover-transfer generator belongs to `C_P`. -/
theorem coneGenerator_mem_upperOrderCone {z : P -> Real}
    (hz : z ∈ ConeGenerator P) : z ∈ UpperOrderCone P := by
  rcases hz with ⟨p, rfl⟩ | ⟨p, q, hpq, rfl⟩
  · exact standardBasis_mem_upperOrderCone p
  · exact transferDirection_mem_upperOrderCone hpq.1.le

/-- The fully formalized easy inclusion of `lem:cone-generators`: the conic
hull of the displayed generators is contained in the upper-set cone. -/
theorem conicHull_generators_subset_upperOrderCone {z : P -> Real}
    (hz : InConicHull (ConeGenerator P) z) : z ∈ UpperOrderCone P := by
  induction hz with
  | zero => exact zero_mem_upperOrderCone
  | generator hz => exact coneGenerator_mem_upperOrderCone hz
  | add hz hw ihz ihw => exact add_mem_upperOrderCone ihz ihw
  | nonneg_smul c hc hz ih => exact nonneg_smul_mem_upperOrderCone ih hc

end UpperOrderCone

section TableOrderCone

variable {A : Type u} {P : Type v}
variable [Preorder A] [Fintype P] [PartialOrder P]

/-- The ambient difference vector `y - x` in `ℝ^(A × P)`, represented in
curried form. -/
def tableDifference (x y : MonotoneTable A P) : A -> P -> Real :=
  fun a p => y a p - x a p

/-- The manuscript product cone `C_{A,P} = C_P^A`. -/
def TableOrderCone (A : Type u) (P : Type v)
    [Fintype P] [PartialOrder P] : Set (A -> P -> Real) :=
  {z | forall a, z a ∈ UpperOrderCone P}

theorem tableOrderCone_pointed : IsPointedCone (TableOrderCone A P) := by
  intro z hz hneg
  funext a
  apply upperOrderCone_pointed (hz a)
  simpa [TableOrderCone] using hneg a

theorem vectorUpperMass_tableDifference
    (x y : MonotoneTable A P) (a : A) (U : UpperSet P) :
    vectorUpperMass (tableDifference x y a) U =
      upperMass (y a) U - upperMass (x a) U := by
  classical
  unfold vectorUpperMass tableDifference upperMass SubprobabilityVector.mass
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hpU : p ∈ (U : Set P) <;> simp [hpU]

/-- Exact order-cone bridge: pointwise stochastic comparison is equivalent to
membership of the coordinate difference in `C_P^A`. -/
theorem table_le_iff_difference_mem {x y : MonotoneTable A P} :
    x <= y <-> tableDifference x y ∈ TableOrderCone A P := by
  constructor
  · intro hxy a U
    rw [vectorUpperMass_tableDifference]
    exact sub_nonneg.mpr (hxy a U)
  · intro hdiff a U
    have hnonneg := hdiff a U
    rw [vectorUpperMass_tableDifference] at hnonneg
    exact sub_nonneg.mp hnonneg

end TableOrderCone

section StrictFeasibility

variable {A : Type u} {P : Type v}
variable [Fintype A] [PartialOrder A] [Fintype P] [PartialOrder P]

/-- The finite lower set used to construct a strictly order-preserving real
scale on an arbitrary finite poset. -/
noncomputable def finiteLowerSet (a : A) : Finset A :=
  Finset.univ.filter fun x => x <= a

theorem finiteLowerSet_mono {a b : A} (hab : a <= b) :
    finiteLowerSet a ⊆ finiteLowerSet b := by
  intro x hx
  simp only [finiteLowerSet, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  exact hx.trans hab

theorem finiteLowerSet_card_pos (a : A) : 0 < (finiteLowerSet a).card := by
  apply Finset.card_pos.mpr
  refine ⟨a, ?_⟩
  simp [finiteLowerSet]

theorem finiteLowerSet_card_le_card (a : A) :
    (finiteLowerSet a).card <= Fintype.card A := by
  simpa using Finset.card_le_card (Finset.subset_univ (finiteLowerSet a))

/-- Strict inclusion of lower sets along a strict comparison. -/
theorem finiteLowerSet_card_strict {a b : A} (hab : a < b) :
    (finiteLowerSet a).card < (finiteLowerSet b).card := by
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_subset_ne]
  refine ⟨finiteLowerSet_mono hab.le, ?_⟩
  intro heq
  have hb : b ∈ finiteLowerSet b := by simp [finiteLowerSet]
  have hba : b ∈ finiteLowerSet a := by simpa [heq] using hb
  have : b <= a := by simpa [finiteLowerSet] using hba
  exact (not_le_of_gt hab) this

/-- A canonical scale in `(0,1]`, strictly increasing on strict comparisons. -/
noncomputable def finiteRankScale (a : A) : Real :=
  ((finiteLowerSet a).card : Real) / (Fintype.card A + 1 : Nat)

theorem finiteRankScale_pos (a : A) : 0 < finiteRankScale a := by
  unfold finiteRankScale
  apply div_pos
  · exact_mod_cast finiteLowerSet_card_pos a
  · positivity

theorem finiteRankScale_le_one (a : A) : finiteRankScale a <= 1 := by
  unfold finiteRankScale
  apply (div_le_one (by positivity : (0 : Real) < (Fintype.card A + 1 : Nat))).2
  exact_mod_cast Nat.le_succ_of_le (finiteLowerSet_card_le_card a)

theorem finiteRankScale_mono : Monotone (finiteRankScale : A -> Real) := by
  intro a b hab
  unfold finiteRankScale
  gcongr
  exact finiteLowerSet_mono hab

theorem finiteRankScale_strict {a b : A} (hab : a < b) :
    finiteRankScale a < finiteRankScale b := by
  unfold finiteRankScale
  apply (div_lt_div_iff_of_pos_right (by positivity :
    (0 : Real) < (Fintype.card A + 1 : Nat))).2
  exact_mod_cast finiteLowerSet_card_strict hab

/-- The positive atomic coefficient of a full-support subprobability vector. -/
noncomputable def interiorBaseCoeff (P : Type v) [Fintype P] : Real :=
  1 / ((Fintype.card P : Real) + 1)

theorem interiorBaseCoeff_pos : 0 < interiorBaseCoeff P := by
  unfold interiorBaseCoeff
  positivity

theorem sum_interiorBaseCoeff_lt_one :
    (∑ _p : P, interiorBaseCoeff P) < 1 := by
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  unfold interiorBaseCoeff
  have hden : (0 : Real) < (Fintype.card P : Real) + 1 := by positivity
  have hlt : (Fintype.card P : Real) < (Fintype.card P : Real) + 1 := by linarith
  simpa [div_eq_mul_inv] using (div_lt_one hden).2 hlt

/-- A full-support vector lying strictly below the total-mass face. -/
noncomputable def interiorBaseVector (P : Type v) [Fintype P] [PartialOrder P] :
    SubprobabilityVector P where
  coeff _ := interiorBaseCoeff P
  coeff_nonneg _ := (interiorBaseCoeff_pos (P := P)).le
  total_le_one := (sum_interiorBaseCoeff_lt_one (P := P)).le

@[simp]
theorem interiorBaseVector_apply (p : P) :
    interiorBaseVector P p = interiorBaseCoeff P :=
  rfl

theorem interiorBaseVector_total_lt_one :
    (interiorBaseVector P).totalMass < 1 := by
  exact sum_interiorBaseCoeff_lt_one (P := P)

/-- Scaling by a scalar in `[0,1]` preserves the subprobability simplex. -/
noncomputable def scaleVector (c : Real) (hc0 : 0 <= c) (hc1 : c <= 1)
    (x : SubprobabilityVector P) : SubprobabilityVector P where
  coeff p := c * x p
  coeff_nonneg p := mul_nonneg hc0 (x.coeff_nonneg p)
  total_le_one := by
    change (∑ p, c * x p) <= 1
    rw [← Finset.mul_sum]
    calc
      c * (∑ p, x p) <= 1 * 1 :=
        mul_le_mul hc1 x.total_le_one x.totalMass_nonneg (by norm_num)
      _ = 1 := by norm_num

@[simp]
theorem scaleVector_apply (c : Real) (hc0 : 0 <= c) (hc1 : c <= 1)
    (x : SubprobabilityVector P) (p : P) :
    scaleVector c hc0 hc1 x p = c * x p :=
  rfl

theorem totalMass_scaleVector (c : Real) (hc0 : 0 <= c) (hc1 : c <= 1)
    (x : SubprobabilityVector P) :
    (scaleVector c hc0 hc1 x).totalMass = c * x.totalMass := by
  classical
  simp only [SubprobabilityVector.totalMass, scaleVector_apply]
  exact (Finset.mul_sum Finset.univ (fun p => x p) c).symm

theorem upperMass_scaleVector (c : Real) (hc0 : 0 <= c) (hc1 : c <= 1)
    (x : SubprobabilityVector P) (U : UpperSet P) :
    upperMass (scaleVector c hc0 hc1 x) U = c * upperMass x U := by
  classical
  unfold upperMass SubprobabilityVector.mass
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hpU : p ∈ (U : Set P) <;> simp [hpU]

theorem scaleVector_le_scaleVector {c d : Real}
    (hc0 : 0 <= c) (hc1 : c <= 1) (hd0 : 0 <= d) (hd1 : d <= 1)
    (hcd : c <= d) (x : SubprobabilityVector P) :
    scaleVector c hc0 hc1 x <= scaleVector d hd0 hd1 x := by
  intro U
  rw [upperMass_scaleVector, upperMass_scaleVector]
  exact mul_le_mul_of_nonneg_right hcd (SubprobabilityVector.mass_nonneg x U)

/-- The canonical strictly feasible table from the source proof: a fixed
full-support vector scaled by a strictly increasing finite rank. -/
noncomputable def strictFeasibleTable : MonotoneTable A P where
  toFun a := scaleVector (finiteRankScale a) (finiteRankScale_pos a).le
    (finiteRankScale_le_one a) (interiorBaseVector P)
  monotone' := by
    intro a b hab
    exact scaleVector_le_scaleVector (finiteRankScale_pos a).le
      (finiteRankScale_le_one a) (finiteRankScale_pos b).le
      (finiteRankScale_le_one b) (finiteRankScale_mono hab) (interiorBaseVector P)

/-- Strict satisfaction of every nontrivial linear inequality defining
`M(A,P)` in the ambient coordinate space. -/
def IsStrictlyFeasible (x : MonotoneTable A P) : Prop :=
  (forall a p, 0 < x a p) ∧
  (forall a, (x a).totalMass < 1) ∧
  (forall ⦃a b : A⦄, a < b -> forall U : UpperSet P,
    (U : Set P).Nonempty -> upperMass (x a) U < upperMass (x b) U)

theorem interiorBaseVector_upperMass_pos (U : UpperSet P)
    (hU : (U : Set P).Nonempty) :
    0 < upperMass (interiorBaseVector P) U := by
  classical
  unfold upperMass SubprobabilityVector.mass
  apply Finset.sum_pos'
  · intro p hp
    by_cases hpU : p ∈ (U : Set P)
    · simp [hpU, (interiorBaseCoeff_pos (P := P)).le]
    · simp [hpU]
  · obtain ⟨p, hpU⟩ := hU
    refine ⟨p, Finset.mem_univ p, ?_⟩
    simp [hpU, interiorBaseCoeff_pos (P := P)]

/-- Algebraic content of `lem:interior-point`: the defining system admits a
point with positive atoms, strict total-mass slack, and strict slack in every
nonempty upper-set comparison attached to `a < b`. -/
theorem strictFeasibleTable_isStrictlyFeasible :
    IsStrictlyFeasible (strictFeasibleTable : MonotoneTable A P) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a p
    change 0 < finiteRankScale a * interiorBaseCoeff P
    exact mul_pos (finiteRankScale_pos a) (interiorBaseCoeff_pos (P := P))
  · intro a
    change (scaleVector (finiteRankScale a) (finiteRankScale_pos a).le
      (finiteRankScale_le_one a) (interiorBaseVector P)).totalMass < 1
    rw [totalMass_scaleVector]
    calc
      finiteRankScale a * (interiorBaseVector P).totalMass <=
          1 * (interiorBaseVector P).totalMass :=
        mul_le_mul_of_nonneg_right (finiteRankScale_le_one a)
          (interiorBaseVector P).totalMass_nonneg
      _ = (interiorBaseVector P).totalMass := by ring
      _ < 1 := interiorBaseVector_total_lt_one (P := P)
  · intro a b hab U hU
    change upperMass
      (scaleVector (finiteRankScale a) (finiteRankScale_pos a).le
        (finiteRankScale_le_one a) (interiorBaseVector P)) U <
      upperMass
      (scaleVector (finiteRankScale b) (finiteRankScale_pos b).le
        (finiteRankScale_le_one b) (interiorBaseVector P)) U
    rw [upperMass_scaleVector, upperMass_scaleVector]
    exact mul_lt_mul_of_pos_right (finiteRankScale_strict hab)
      (interiorBaseVector_upperMass_pos U hU)

end StrictFeasibility

section CoordinateConvergence

variable {P : Type v} [Fintype P] [PartialOrder P]

theorem coeff_eq_upperMass_sub_strict
    (x : SubprobabilityVector P) (p : P) :
    x p = upperMass x (principalUpper p) -
      upperMass x (strictPrincipalUpper p) := by
  simpa [vectorUpperMass, upperMass, SubprobabilityVector.mass] using
    atom_eq_vectorUpperMass_sub_strict (fun q => x q) p

/-- The coordinate-convergence step in `lem:euclidean-scott`, stated for an
arbitrary filter rather than only a sequence. -/
theorem tendsto_coeff_of_tendsto_upperMass
    {I : Type w} {l : Filter I} {x : I -> SubprobabilityVector P}
    {limit : SubprobabilityVector P}
    (h : forall U : UpperSet P,
      Tendsto (fun i => upperMass (x i) U) l (nhds (upperMass limit U)))
    (p : P) :
    Tendsto (fun i => x i p) l (nhds (limit p)) := by
  have hprincipal := h (principalUpper p)
  have hstrict := h (strictPrincipalUpper p)
  simpa only [coeff_eq_upperMass_sub_strict] using hprincipal.sub hstrict

variable {A : Type u} [Preorder A]

/-- Table version of atomic-coordinate recovery. -/
theorem table_atom_eq_upperCoordinate_sub_strict
    (x : MonotoneTable A P) (a : A) (p : P) :
    x.atom a p = x.upperCoordinate a (principalUpper p) -
      x.upperCoordinate a (strictPrincipalUpper p) := by
  exact coeff_eq_upperMass_sub_strict (x a) p

/-- Upper-set coordinate convergence of monotone tables implies convergence
of every ambient Euclidean coordinate. -/
theorem tendsto_table_atom_of_tendsto_upperCoordinate
    {I : Type w} {l : Filter I} {x : I -> MonotoneTable A P}
    {limit : MonotoneTable A P}
    (h : forall a U,
      Tendsto (fun i => (x i).upperCoordinate a U) l
        (nhds (limit.upperCoordinate a U)))
    (a : A) (p : P) :
    Tendsto (fun i => (x i).atom a p) l (nhds (limit.atom a p)) := by
  have hprincipal := h a (principalUpper p)
  have hstrict := h a (strictPrincipalUpper p)
  simpa only [table_atom_eq_upperCoordinate_sub_strict] using hprincipal.sub hstrict

end CoordinateConvergence

end FiniteValuationApproximable
