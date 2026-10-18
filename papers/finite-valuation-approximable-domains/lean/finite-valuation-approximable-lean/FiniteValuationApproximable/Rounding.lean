import FiniteValuationApproximable.Polytope
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.Convex.Topology

/-!
# Monotone randomized grid rounding: exact algebraic prefix

This module formalizes the measure-free core of the manuscript section
`Monotone randomized grid rounding` (source SHA-256
`4b2e65f0f96347bea4df7571e8993ad6e888c0ff7181c1305c5056880365ac94`).

The exact results proved here are:

* coordinatewise floor rounding with remainder in `[0,1)`, the zonotope
  support identity, and finiteness of the set of all possible rounded integer
  vectors for fixed input;
* a quantitative local-cell lemma: away from a floor boundary, sufficiently
  small coordinate perturbations do not change the rounded vector;
* the modulo-one rotation/carry identities used by the source coupling;
* a deterministic monotone-coupling theorem for any cone closed under
  addition and nonnegative scaling, including the full floor algebra of the
  coupling construction;
* the affine-interior lemma in an arbitrary real normed vector space;
* the finite coupling implication from an order-supported joint mass table to
  stochastic order.

The source's coefficient continuity still requires putting Lebesgue measure
on the input cube, proving the boundary hyperplanes null by Fubini, and using
dominated convergence.  Likewise, equality of the laws before and after the
modulo-one rotation requires measure-preservation of that rotation.  Those
measure-theoretic claims are not asserted here.  In addition, deriving the
coefficient decomposition used by the deterministic coupling from the sole
hypothesis `z' - z ∈ C_{A,P}` requires the reverse inclusion in the cone
generator theorem, which `Polytope.lean` explicitly leaves open.  The source's
`p_eps` kernel can therefore only be reached here through its exact finite
support, order-coupling, and affine-interior ingredients; it is not presented
as a completed probability kernel or as Scott-continuous.
-/

set_option autoImplicit false
set_option linter.unnecessarySimpa false

universe u v w

namespace FiniteValuationApproximable

open scoped BigOperators Classical Topology
open Set Filter

section CoordinateFloor

variable {I : Type u} {J : Type v}
variable [Fintype I] [Fintype J]

/-- Membership in the half-open unit cube `[0,1)^I`. -/
def InUnitCube (x : I -> Real) : Prop :=
  forall i, 0 <= x i ∧ x i < 1

/-- Membership in the closed unit cube `[0,1]^I`. -/
def InClosedUnitCube (x : I -> Real) : Prop :=
  forall i, 0 <= x i ∧ x i <= 1

/-- Coordinatewise coercion of an integer vector. -/
def castIntVector (l : I -> Int) : I -> Real :=
  fun i => (l i : Real)

/-- Coordinatewise floor. -/
noncomputable def floorVector (x : I -> Real) : I -> Int :=
  fun i => ⌊x i⌋

/-- The shift `sum_j s_j xi_j` in the random-rounding formula.  Directions
are integral, as they are for the standard basis and Hasse roots. -/
noncomputable def roundingShiftSum (s : J -> Real) (xi : J -> I -> Int) : I -> Real :=
  fun i => ∑ j, s j * (xi j i : Real)

/-- The real vector immediately before coordinatewise flooring. -/
noncomputable def roundingArgument
    (z u : I -> Real) (s : J -> Real) (xi : J -> I -> Int) : I -> Real :=
  fun i => z i - u i - roundingShiftSum s xi i

/-- The deterministic value `Q_z(u,s)`. -/
noncomputable def randomizedFloor
    (z u : I -> Real) (s : J -> Real) (xi : J -> I -> Int) : I -> Int :=
  floorVector (roundingArgument z u s xi)

/-- Fractional remainder after applying `randomizedFloor`. -/
noncomputable def roundingRemainder
    (z u : I -> Real) (s : J -> Real) (xi : J -> I -> Int) : I -> Real :=
  fun i => Int.fract (roundingArgument z u s xi i)

theorem roundingRemainder_mem_unitCube
    (z u : I -> Real) (s : J -> Real) (xi : J -> I -> Int) :
    InUnitCube (roundingRemainder z u s xi) := by
  intro i
  exact ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩

/-- A witness-level presentation of the zonotope
`sum_i [0,2e_i] + sum_j [0,xi_j]`.  Splitting the first coefficient into two
unit-cube vectors matches the `U + theta` decomposition in the source. -/
def InRoundingZonotope (xi : J -> I -> Int) (x : I -> Real) : Prop :=
  exists u theta : I -> Real,
    InClosedUnitCube u ∧ InClosedUnitCube theta ∧
    (exists t : J -> Real, InClosedUnitCube t ∧
      forall i, x i = u i + theta i + ∑ j, t j * (xi j i : Real))

/-- Deterministic support identity underlying part (i) of
`lem:rounding-law`. -/
theorem rounding_support_mem_zonotope
    {z u : I -> Real} {s : J -> Real} {xi : J -> I -> Int}
    (hu : InUnitCube u) (hs : InUnitCube s) :
    InRoundingZonotope xi
      (z - castIntVector (randomizedFloor z u s xi)) := by
  refine ⟨u, roundingRemainder z u s xi, ?_, ?_, ?_⟩
  · intro i
    exact ⟨(hu i).1, (hu i).2.le⟩
  · intro i
    exact ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩
  · refine ⟨s, ?_, ?_⟩
    · intro j
      exact ⟨(hs j).1, (hs j).2.le⟩
    · intro i
      change z i - (⌊roundingArgument z u s xi i⌋ : Real) =
        u i + Int.fract (roundingArgument z u s xi i) +
          ∑ j, s j * (xi j i : Real)
      have hfract := Int.floor_add_fract (roundingArgument z u s xi i)
      simp only [roundingArgument, roundingShiftSum] at hfract ⊢
      linarith

/-- All possible deterministic outcomes as the unit-cube inputs vary. -/
def RoundingOutcomeSet (z : I -> Real) (xi : J -> I -> Int) : Set (I -> Int) :=
  {l | exists u s, InUnitCube u ∧ InUnitCube s ∧ randomizedFloor z u s xi = l}

theorem outcome_mem_zonotope {z : I -> Real} {xi : J -> I -> Int}
    {l : I -> Int} (hl : l ∈ RoundingOutcomeSet z xi) :
    InRoundingZonotope xi (z - castIntVector l) := by
  rcases hl with ⟨u, s, hu, hs, rfl⟩
  exact rounding_support_mem_zonotope hu hs

/-- Coordinate radius controlling all direction shifts. -/
noncomputable def directionRadius (xi : J -> I -> Int) (i : I) : Real :=
  ∑ j, |(xi j i : Real)|

theorem directionRadius_nonneg (xi : J -> I -> Int) (i : I) :
    0 <= directionRadius xi i := by
  exact Finset.sum_nonneg fun j hj => abs_nonneg _

theorem abs_roundingShiftSum_le_directionRadius
    {s : J -> Real} (hs : InUnitCube s) (xi : J -> I -> Int) (i : I) :
    |roundingShiftSum s xi i| <= directionRadius xi i := by
  classical
  calc
    |roundingShiftSum s xi i| <= ∑ j, |s j * (xi j i : Real)| := by
      exact Finset.abs_sum_le_sum_abs _ _
    _ <= ∑ j, |(xi j i : Real)| := by
      apply Finset.sum_le_sum
      intro j hj
      rw [abs_mul, abs_of_nonneg (hs j).1]
      simpa using mul_le_mul_of_nonneg_right (hs j).2.le
        (abs_nonneg (xi j i : Real))
    _ = directionRadius xi i := rfl

theorem roundingArgument_bounds
    {z u : I -> Real} {s : J -> Real} {xi : J -> I -> Int}
    (hu : InUnitCube u) (hs : InUnitCube s) (i : I) :
    z i - 1 - directionRadius xi i <= roundingArgument z u s xi i ∧
      roundingArgument z u s xi i <= z i + directionRadius xi i := by
  have habs := abs_roundingShiftSum_le_directionRadius hs xi i
  have hlower : -directionRadius xi i <= roundingShiftSum s xi i :=
    (neg_le_of_abs_le habs)
  have hupper : roundingShiftSum s xi i <= directionRadius xi i :=
    le_trans (le_abs_self _) habs
  simp only [roundingArgument]
  constructor <;> linarith [(hu i).1, (hu i).2]

/-- Integer lower bound for all possible rounded values in one coordinate. -/
noncomputable def roundingLowerBound
    (z : I -> Real) (xi : J -> I -> Int) (i : I) : Int :=
  ⌊z i - 1 - directionRadius xi i⌋

/-- Integer upper bound for all possible rounded values in one coordinate. -/
noncomputable def roundingUpperBound
    (z : I -> Real) (xi : J -> I -> Int) (i : I) : Int :=
  ⌊z i + directionRadius xi i⌋

theorem randomizedFloor_mem_bounds
    {z u : I -> Real} {s : J -> Real} {xi : J -> I -> Int}
    (hu : InUnitCube u) (hs : InUnitCube s) (i : I) :
    roundingLowerBound z xi i <= randomizedFloor z u s xi i ∧
      randomizedFloor z u s xi i <= roundingUpperBound z xi i := by
  rcases roundingArgument_bounds hu hs i with ⟨hlower, hupper⟩
  exact ⟨Int.floor_mono hlower, Int.floor_mono hupper⟩

/-- The set of all possible outcomes is finite.  Consequently, any law
obtained by putting a probability measure on the input cube has finite
support. -/
theorem roundingOutcomeSet_finite
    (z : I -> Real) (xi : J -> I -> Int) :
    (RoundingOutcomeSet z xi).Finite := by
  let box : forall i : I, Set Int :=
    fun i => Set.Icc (roundingLowerBound z xi i) (roundingUpperBound z xi i)
  have hbox : (Set.pi Set.univ box).Finite :=
    Set.Finite.pi fun i => Set.finite_Icc _ _
  apply hbox.subset
  intro l hl
  rcases hl with ⟨u, s, hu, hs, hround⟩
  subst l
  intro i hi
  exact randomizedFloor_mem_bounds hu hs i

/-- Changing only the input point translates the pre-floor argument by the
same coordinate change. -/
theorem roundingArgument_change_input
    (z w u : I -> Real) (s : J -> Real) (xi : J -> I -> Int) (i : I) :
    roundingArgument w u s xi i =
      roundingArgument z u s xi i + (w i - z i) := by
  simp [roundingArgument]
  ring

/-- Quantitative local constancy of the deterministic floor away from its
boundary hyperplanes.  This is the pointwise ingredient used before DCT in
part (ii) of `lem:rounding-law`. -/
theorem randomizedFloor_eq_of_coordinate_perturbation
    {z w u : I -> Real} {s : J -> Real} {xi : J -> I -> Int}
    (hperturb : forall i,
      |w i - z i| < min
        (roundingArgument z u s xi i - randomizedFloor z u s xi i)
        ((randomizedFloor z u s xi i : Real) + 1 - roundingArgument z u s xi i)) :
    randomizedFloor w u s xi = randomizedFloor z u s xi := by
  funext i
  apply Int.floor_eq_iff.mpr
  have hright : roundingArgument z u s xi i <
      (randomizedFloor z u s xi i : Real) + 1 :=
    Int.lt_floor_add_one _
  have habs := hperturb i
  have habsleft : -(min
        (roundingArgument z u s xi i - randomizedFloor z u s xi i)
        ((randomizedFloor z u s xi i : Real) + 1 - roundingArgument z u s xi i)) <
      w i - z i := (neg_lt_of_abs_lt habs)
  have habsright : w i - z i < min
        (roundingArgument z u s xi i - randomizedFloor z u s xi i)
        ((randomizedFloor z u s xi i : Real) + 1 - roundingArgument z u s xi i) :=
    lt_of_abs_lt habs
  rw [roundingArgument_change_input z]
  constructor
  · have hminleft : min
        (roundingArgument z u s xi i - randomizedFloor z u s xi i)
        ((randomizedFloor z u s xi i : Real) + 1 - roundingArgument z u s xi i) <=
        roundingArgument z u s xi i - randomizedFloor z u s xi i := min_le_left _ _
    linarith
  · have hminright : min
        (roundingArgument z u s xi i - randomizedFloor z u s xi i)
        ((randomizedFloor z u s xi i : Real) + 1 - roundingArgument z u s xi i) <=
        (randomizedFloor z u s xi i : Real) + 1 - roundingArgument z u s xi i :=
      min_le_right _ _
    linarith

end CoordinateFloor

section ModOneRotation

variable {J : Type v} [Fintype J]

/-- The shifted uniform coordinate `(s + fract beta) mod 1`. -/
noncomputable def rotatedUnitShift (beta s : J -> Real) : J -> Real :=
  fun j => Int.fract (s j + Int.fract (beta j))

/-- The integral carry `floor beta + floor (s + fract beta)`. -/
noncomputable def integerCarry (beta s : J -> Real) : J -> Int :=
  fun j => ⌊beta j⌋ + ⌊s j + Int.fract (beta j)⌋

theorem rotatedUnitShift_mem_unitCube (beta s : J -> Real) :
    InUnitCube (rotatedUnitShift beta s) := by
  intro j
  exact ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩

/-- Exact scalar identity behind `S + theta = S' + delta`, with the integer
part of `beta` included. -/
theorem beta_add_shift_sub_rotated_eq_carry
    (beta s : J -> Real) (j : J) :
    beta j + s j - rotatedUnitShift beta s j = (integerCarry beta s j : Real) := by
  have hbeta := Int.floor_add_fract (beta j)
  have hshift := Int.floor_add_fract (s j + Int.fract (beta j))
  simp only [rotatedUnitShift, integerCarry, Int.cast_add] at hbeta hshift ⊢
  linarith

theorem integerCarry_nonneg {beta s : J -> Real}
    (hbeta : forall j, 0 <= beta j) (hs : forall j, 0 <= s j) (j : J) :
    0 <= integerCarry beta s j := by
  unfold integerCarry
  exact add_nonneg (Int.floor_nonneg.mpr (hbeta j))
    (Int.floor_nonneg.mpr (add_nonneg (hs j) (Int.fract_nonneg _)))

end ModOneRotation

section DeterministicConeCoupling

variable {I : Type u} {J : Type v} [Fintype I] [Fintype J]

/-- Standard coordinate basis in an arbitrary finite coordinate type. -/
noncomputable def coordinateBasis (i : I) : I -> Real :=
  fun k => if k = i then 1 else 0

/-- Real difference of two integer grid vectors. -/
def realGridDifference (l m : I -> Int) : I -> Real :=
  fun i => (m i - l i : Int)

/-- Integral direction accumulated from all carries. -/
noncomputable def integerDirectionShift
    (xi : J -> I -> Int) (beta s : J -> Real) : I -> Int :=
  fun i => ∑ j, integerCarry beta s j * xi j i

/-- Integral directions, coerced to the ambient real coordinate space. -/
def castIntDirection (x : I -> Int) : I -> Real :=
  fun i => (x i : Real)

theorem cast_integerDirectionShift
    (xi : J -> I -> Int) (beta s : J -> Real) :
    castIntDirection (integerDirectionShift xi beta s) =
      ∑ j, (integerCarry beta s j : Real) • castIntDirection (xi j) := by
  funext i
  simp [castIntDirection, integerDirectionShift]

/-- A finite sum remains in any set containing zero and closed under
addition. -/
theorem finite_sum_mem_of_zero_add_closed
    {C : Set (I -> Real)} (hzero : (0 : I -> Real) ∈ C)
    (hadd : forall ⦃x y : I -> Real⦄, x ∈ C -> y ∈ C -> x + y ∈ C)
    (f : J -> I -> Real) (hf : forall j, f j ∈ C) :
    (∑ j, f j) ∈ C := by
  classical
  induction (Finset.univ : Finset J) using Finset.induction_on with
  | empty => simpa using hzero
  | @insert j s hjs ih =>
      rw [Finset.sum_insert hjs]
      exact hadd (hf j) ih

theorem sum_smul_coordinateBasis (c : I -> Real) :
    (∑ i, c i • coordinateBasis i) = c := by
  classical
  funext k
  simp [coordinateBasis]

theorem nonnegative_coordinateVector_mem_cone
    {C : Set (I -> Real)}
    (hzero : (0 : I -> Real) ∈ C)
    (hadd : forall ⦃x y : I -> Real⦄, x ∈ C -> y ∈ C -> x + y ∈ C)
    (hsmul : forall ⦃x : I -> Real⦄, x ∈ C ->
      forall ⦃c : Real⦄, 0 <= c -> c • x ∈ C)
    (hbasis : forall i, coordinateBasis i ∈ C)
    {c : I -> Real} (hc : forall i, 0 <= c i) : c ∈ C := by
  rw [← sum_smul_coordinateBasis c]
  apply finite_sum_mem_of_zero_add_closed hzero hadd
  intro i
  exact hsmul (hbasis i) (hc i)

/-- The displayed zonotope is contained in any cone containing all coordinate
basis vectors and all listed integral directions. -/
theorem roundingZonotope_mem_cone
    {C : Set (I -> Real)}
    (hzero : (0 : I -> Real) ∈ C)
    (hadd : forall ⦃x y : I -> Real⦄, x ∈ C -> y ∈ C -> x + y ∈ C)
    (hsmul : forall ⦃x : I -> Real⦄, x ∈ C ->
      forall ⦃c : Real⦄, 0 <= c -> c • x ∈ C)
    (hbasis : forall i, coordinateBasis i ∈ C)
    {xi : J -> I -> Int} (hxi : forall j, castIntDirection (xi j) ∈ C)
    {x : I -> Real} (hx : InRoundingZonotope xi x) : x ∈ C := by
  rcases hx with ⟨u, theta, hu, htheta, t, ht, hx⟩
  have huC : u ∈ C :=
    nonnegative_coordinateVector_mem_cone hzero hadd hsmul hbasis fun i => (hu i).1
  have hthetaC : theta ∈ C :=
    nonnegative_coordinateVector_mem_cone hzero hadd hsmul hbasis fun i => (htheta i).1
  have hshiftC : (∑ j, t j • castIntDirection (xi j)) ∈ C := by
    apply finite_sum_mem_of_zero_add_closed hzero hadd
    intro j
    exact hsmul (hxi j) (ht j).1
  have heq : x = u + theta + ∑ j, t j • castIntDirection (xi j) := by
    funext i
    simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      castIntDirection]
    exact hx i
  rw [heq]
  exact hadd (hadd huC hthetaC) hshiftC

theorem floor_increment_nonneg (w alpha : I -> Real)
    (halpha : forall i, 0 <= alpha i) (i : I) :
    0 <= (⌊w i + alpha i⌋ - ⌊w i⌋ : Int) := by
  exact sub_nonneg.mpr (Int.floor_mono (le_add_of_nonneg_right (halpha i)))

/-- Exact coordinate decomposition of the floor difference after an integral
translation and a nonnegative coordinate translation. -/
theorem coupled_floor_difference_eq
    (w alpha : I -> Real) (m : I -> Int) :
    realGridDifference (floorVector w)
      (floorVector (fun i => w i + (m i : Real) + alpha i)) =
      castIntDirection m +
        ∑ i, ((⌊w i + alpha i⌋ - ⌊w i⌋ : Int) : Real) • coordinateBasis i := by
  classical
  funext k
  change ((⌊w k + (m k : Real) + alpha k⌋ - ⌊w k⌋ : Int) : Real) =
    (m k : Real) +
      (∑ i, ((⌊w i + alpha i⌋ - ⌊w i⌋ : Int) : Real) • coordinateBasis i) k
  rw [show w k + (m k : Real) + alpha k = (w k + alpha k) + (m k : Real) by ring]
  simp [realGridDifference, floorVector, castIntDirection, coordinateBasis,
    Int.floor_add_intCast]
  ring

/-- Cone membership of the deterministic coupled floor difference. -/
theorem coupled_floor_difference_mem_cone
    {C : Set (I -> Real)}
    (hzero : (0 : I -> Real) ∈ C)
    (hadd : forall ⦃x y : I -> Real⦄, x ∈ C -> y ∈ C -> x + y ∈ C)
    (hsmul : forall ⦃x : I -> Real⦄, x ∈ C ->
      forall ⦃c : Real⦄, 0 <= c -> c • x ∈ C)
    (hbasis : forall i, coordinateBasis i ∈ C)
    {w alpha : I -> Real} {m : I -> Int}
    (hm : castIntDirection m ∈ C) (halpha : forall i, 0 <= alpha i) :
    realGridDifference (floorVector w)
      (floorVector (fun i => w i + (m i : Real) + alpha i)) ∈ C := by
  rw [coupled_floor_difference_eq]
  apply hadd hm
  apply finite_sum_mem_of_zero_add_closed hzero hadd
  intro i
  apply hsmul (hbasis i)
  exact_mod_cast floor_increment_nonneg w alpha halpha i

/-- Algebraic identity relating the two pre-floor arguments in the source
coupling. -/
theorem coupled_roundingArguments_eq
    {z z' u : I -> Real} {s beta : J -> Real}
    {coordinateAlpha : I -> Real} {xi : J -> I -> Int}
    (hz : forall i, z' i - z i = coordinateAlpha i +
      ∑ j, beta j * (xi j i : Real)) (i : I) :
    roundingArgument z' u (rotatedUnitShift beta s) xi i =
      roundingArgument z u s xi i +
        (integerDirectionShift xi beta s i : Real) + coordinateAlpha i := by
  have hterm : forall j,
      beta j * (xi j i : Real) + s j * (xi j i : Real) -
          rotatedUnitShift beta s j * (xi j i : Real) =
        (integerCarry beta s j : Real) * (xi j i : Real) := by
    intro j
    rw [← beta_add_shift_sub_rotated_eq_carry beta s j]
    ring
  have hsum :
      (∑ j, beta j * (xi j i : Real)) +
          (∑ j, s j * (xi j i : Real)) -
          (∑ j, rotatedUnitShift beta s j * (xi j i : Real)) =
        ∑ j, (integerCarry beta s j : Real) * (xi j i : Real) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    exact hterm j
  simp only [roundingArgument, roundingShiftSum]
  rw [show z' i = z i + coordinateAlpha i +
      ∑ j, beta j * (xi j i : Real) by linarith [hz i]]
  change _ = _ + ((∑ j, integerCarry beta s j * xi j i : Int) : Real) + _
  norm_cast at hsum ⊢
  linarith

/-- Deterministic part of `prop:rounding-monotone`.  It includes the full
modulo-one/carry construction and proves that the paired integer outputs are
ordered by `C`.  The omitted probabilistic step is precisely that the rotated
shift has the same joint uniform law as the original shift. -/
theorem deterministic_rounding_coupling_mem_cone
    {C : Set (I -> Real)}
    (hzero : (0 : I -> Real) ∈ C)
    (hadd : forall ⦃x y : I -> Real⦄, x ∈ C -> y ∈ C -> x + y ∈ C)
    (hsmul : forall ⦃x : I -> Real⦄, x ∈ C ->
      forall ⦃c : Real⦄, 0 <= c -> c • x ∈ C)
    (hbasis : forall i, coordinateBasis i ∈ C)
    {z z' u : I -> Real} {s beta : J -> Real} {alpha : I -> Real}
    {xi : J -> I -> Int}
    (hxi : forall j, castIntDirection (xi j) ∈ C)
    (hz : forall i, z' i - z i = alpha i +
      ∑ j, beta j * (xi j i : Real))
    (halpha : forall i, 0 <= alpha i)
    (hbeta : forall j, 0 <= beta j) (hs : forall j, 0 <= s j) :
    realGridDifference (randomizedFloor z u s xi)
      (randomizedFloor z' u (rotatedUnitShift beta s) xi) ∈ C := by
  have hcarry : forall j, 0 <= (integerCarry beta s j : Real) := by
    intro j
    exact_mod_cast integerCarry_nonneg hbeta hs j
  have hm : castIntDirection (integerDirectionShift xi beta s) ∈ C := by
    rw [cast_integerDirectionShift]
    apply finite_sum_mem_of_zero_add_closed hzero hadd
    intro j
    exact hsmul (hxi j) (hcarry j)
  have hargs : roundingArgument z' u (rotatedUnitShift beta s) xi =
      fun i => roundingArgument z u s xi i +
        (integerDirectionShift xi beta s i : Real) + alpha i := by
    funext i
    exact coupled_roundingArguments_eq hz i
  change realGridDifference (floorVector (roundingArgument z u s xi))
      (floorVector (roundingArgument z' u (rotatedUnitShift beta s) xi)) ∈ C
  rw [hargs]
  exact coupled_floor_difference_mem_cone hzero hadd hsmul hbasis hm halpha

end DeterministicConeCoupling

section FlatTableCone

variable {A : Type u} {P : Type v}
variable [Fintype A] [Fintype P] [PartialOrder P]

/-- The table cone `C_{A,P}` in the manuscript's flattened coordinate space
`ℝ^(A × P)`. -/
def FlatTableOrderCone (A : Type u) (P : Type v)
    [Fintype P] [PartialOrder P] : Set (A × P -> Real) :=
  {x | forall a, (fun p => x (a, p)) ∈ UpperOrderCone P}

theorem zero_mem_flatTableOrderCone :
    (0 : A × P -> Real) ∈ FlatTableOrderCone A P := by
  intro a
  simpa using (zero_mem_upperOrderCone : (0 : P -> Real) ∈ UpperOrderCone P)

theorem add_mem_flatTableOrderCone {x y : A × P -> Real}
    (hx : x ∈ FlatTableOrderCone A P) (hy : y ∈ FlatTableOrderCone A P) :
    x + y ∈ FlatTableOrderCone A P := by
  intro a
  exact add_mem_upperOrderCone (hx a) (hy a)

theorem nonneg_smul_mem_flatTableOrderCone {x : A × P -> Real}
    (hx : x ∈ FlatTableOrderCone A P) {c : Real} (hc : 0 <= c) :
    c • x ∈ FlatTableOrderCone A P := by
  intro a
  exact nonneg_smul_mem_upperOrderCone (hx a) hc

theorem flatTableOrderCone_pointed :
    IsPointedCone (FlatTableOrderCone A P) := by
  intro x hx hneg
  funext ap
  obtain ⟨a, p⟩ := ap
  have hrowneg : -(fun q => x (a, q)) ∈ UpperOrderCone P := by
    simpa [FlatTableOrderCone] using hneg a
  have hrowzero := upperOrderCone_pointed (hx a) hrowneg
  have hp := congrFun hrowzero p
  simpa using hp

/-- Every flattened standard coordinate direction belongs to `C_{A,P}`. -/
theorem coordinateBasis_mem_flatTableOrderCone (i : A × P) :
    coordinateBasis i ∈ FlatTableOrderCone A P := by
  rcases i with ⟨ia, ip⟩
  intro a
  by_cases ha : a = ia
  · subst a
    convert standardBasis_mem_upperOrderCone ip using 1
    funext p
    simp [coordinateBasis, standardBasis]
  · convert (zero_mem_upperOrderCone : (0 : P -> Real) ∈ UpperOrderCone P) using 1
    funext p
    have hpair : (a, p) ≠ (ia, ip) := by
      intro h
      exact ha (Prod.mk.inj h).1
    simp [coordinateBasis, hpair]

/-- Integer standard coordinate vector. -/
noncomputable def intCoordinateBasis (i : A × P) : A × P -> Int :=
  fun k => if k = i then 1 else 0

theorem castIntDirection_intCoordinateBasis (i : A × P) :
    castIntDirection (intCoordinateBasis i) = coordinateBasis i := by
  funext k
  simp [castIntDirection, intCoordinateBasis, coordinateBasis]

/-- Integral copy of the cover-root direction in row `a`. -/
noncomputable def flatTransferDirection (a : A) (p q : P) : A × P -> Int :=
  intCoordinateBasis (a, q) - intCoordinateBasis (a, p)

/-- Every upward transfer direction in one row belongs to the flattened table
cone.  Cover relations are the special case used by the source enumeration. -/
theorem cast_flatTransferDirection_mem_flatTableOrderCone
    (a : A) {p q : P} (hpq : p <= q) :
    castIntDirection (flatTransferDirection a p q) ∈ FlatTableOrderCone A P := by
  intro b
  by_cases hba : b = a
  · subst b
    convert transferDirection_mem_upperOrderCone hpq using 1
    funext r
    simp [castIntDirection, flatTransferDirection, intCoordinateBasis,
      transferDirection, standardBasis]
  · convert (zero_mem_upperOrderCone : (0 : P -> Real) ∈ UpperOrderCone P) using 1
    funext r
    simp [castIntDirection, flatTransferDirection, intCoordinateBasis, hba]

/-- Zonotope inclusion specialized to the manuscript's flattened table cone. -/
theorem roundingZonotope_mem_flatTableOrderCone
    {J : Type w} [Fintype J] {xi : J -> A × P -> Int}
    (hxi : forall j, castIntDirection (xi j) ∈ FlatTableOrderCone A P)
    {x : A × P -> Real} (hx : InRoundingZonotope xi x) :
    x ∈ FlatTableOrderCone A P := by
  exact roundingZonotope_mem_cone zero_mem_flatTableOrderCone
    (@add_mem_flatTableOrderCone A P _ _ _)
    (@nonneg_smul_mem_flatTableOrderCone A P _ _ _)
    coordinateBasis_mem_flatTableOrderCone hxi hx

/-- Cone order on the integer grid, without installing a competing global
order instance on function types. -/
def FlatGridLE (l m : A × P -> Int) : Prop :=
  realGridDifference l m ∈ FlatTableOrderCone A P

theorem flatGridLE_refl (l : A × P -> Int) : FlatGridLE l l := by
  have hzero : realGridDifference l l = 0 := by
    funext i
    simp [realGridDifference]
  rw [FlatGridLE, hzero]
  exact zero_mem_flatTableOrderCone

theorem flatGridLE_trans {l m n : A × P -> Int}
    (hlm : FlatGridLE l m) (hmn : FlatGridLE m n) : FlatGridLE l n := by
  have hadd : realGridDifference l n =
      realGridDifference l m + realGridDifference m n := by
    funext i
    simp only [realGridDifference, Pi.add_apply]
    push_cast
    ring
  rw [FlatGridLE, hadd]
  exact add_mem_flatTableOrderCone hlm hmn

theorem flatGridLE_antisymm {l m : A × P -> Int}
    (hlm : FlatGridLE l m) (hml : FlatGridLE m l) : l = m := by
  have hneg : -realGridDifference l m ∈ FlatTableOrderCone A P := by
    rw [FlatGridLE] at hml
    have heq : -realGridDifference l m = realGridDifference m l := by
      funext i
      simp only [realGridDifference, Pi.neg_apply]
      push_cast
      ring
    rw [heq]
    exact hml
  have hzero := flatTableOrderCone_pointed hlm hneg
  funext i
  have hi := congrFun hzero i
  change ((m i - l i : Int) : Real) = (0 : Real) at hi
  have hint : m i - l i = 0 := by
    exact_mod_cast hi
  omega

end FlatTableCone

section ScaledGridSupport

variable {I : Type u} {J : Type v} [Fintype I] [Fintype J]

/-- Coordinatewise scalar division. -/
noncomputable def divideVector (z : I -> Real) (h : Real) : I -> Real :=
  fun i => z i / h

/-- The scaled grid difference `z - h l` occurring in equation
`eq:grid-below`. -/
def scaledGridDifference (z : I -> Real) (h : Real) (l : I -> Int) : I -> Real :=
  z - h • castIntVector l

theorem scaledGridDifference_eq_smul
    {z : I -> Real} {h : Real} (hh : h ≠ 0) (l : I -> Int) :
    scaledGridDifference z h l =
      h • (divideVector z h - castIntVector l) := by
  funext i
  simp only [scaledGridDifference, divideVector, castIntVector, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul]
  field_simp

/-- Exact support-to-order implication used in `prop:p-kernel`.  It is stated
for an arbitrary cone and isolates the only missing input from the full law:
membership of the integer outcome in the deterministic outcome set. -/
theorem scaled_grid_below_of_rounding_outcome
    {C : Set (I -> Real)}
    (hsmul : forall ⦃x : I -> Real⦄, x ∈ C ->
      forall ⦃c : Real⦄, 0 <= c -> c • x ∈ C)
    {z : I -> Real} {h : Real} (hh : 0 < h)
    {xi : J -> I -> Int} {l : I -> Int}
    (hzonotope : forall q, InRoundingZonotope xi q -> q ∈ C)
    (hl : l ∈ RoundingOutcomeSet (divideVector z h) xi) :
    scaledGridDifference z h l ∈ C := by
  rw [scaledGridDifference_eq_smul hh.ne']
  apply hsmul _ hh.le
  exact hzonotope _ (outcome_mem_zonotope hl)

/-- `eq:grid-below` specialized to the flattened table cone. -/
theorem scaled_grid_below_flatTableOrderCone
    {A : Type u} {P : Type v} [Fintype A] [Fintype P] [PartialOrder P]
    {J : Type w} [Fintype J]
    {z : A × P -> Real} {h : Real} (hh : 0 < h)
    {xi : J -> A × P -> Int}
    (hxi : forall j, castIntDirection (xi j) ∈ FlatTableOrderCone A P)
    {l : A × P -> Int}
    (hl : l ∈ RoundingOutcomeSet (divideVector z h) xi) :
    scaledGridDifference z h l ∈ FlatTableOrderCone A P := by
  exact scaled_grid_below_of_rounding_outcome
    (@nonneg_smul_mem_flatTableOrderCone A P _ _ _) hh
    (fun q hq => roundingZonotope_mem_flatTableOrderCone hxi hq) hl

/-- The finite carrier on which the rounding law at a fixed input lives. -/
def RoundingOutcome (z : I -> Real) (xi : J -> I -> Int) :=
  {l : I -> Int // l ∈ RoundingOutcomeSet z xi}

noncomputable instance roundingOutcomeFintype
    (z : I -> Real) (xi : J -> I -> Int) : Fintype (RoundingOutcome z xi) :=
  (roundingOutcomeSet_finite z xi).fintype

end ScaledGridSupport

section FiniteProbabilityKernels

open SubprobabilityVector

variable {X : Type u} {L : Type v} [Fintype L] [PartialOrder L]

/-- Package nonnegative weights of total mass one as a finite probability
vector. -/
noncomputable def probabilityVectorOfWeights
    (weight : L -> Real) (hnonneg : forall l, 0 <= weight l)
    (htotal : (∑ l, weight l) = 1) : ProbabilityVector L := by
  let p : SubprobabilityVector L :=
    { coeff := weight
      coeff_nonneg := hnonneg
      total_le_one := htotal.le }
  exact ⟨p, htotal⟩

@[simp]
theorem probabilityVectorOfWeights_apply
    (weight : L -> Real) (hnonneg : forall l, 0 <= weight l)
    (htotal : (∑ l, weight l) = 1) (l : L) :
    (probabilityVectorOfWeights weight hnonneg htotal).1 l = weight l :=
  rfl

/-- A finite probability kernel, at the coefficient-vector level used in the
manuscript. -/
abbrev FiniteProbabilityKernel (X : Type u) (L : Type v)
    [Fintype L] := X -> ProbabilityVector L

/-- Build the coefficient kernel once nonnegativity and normalization of the
weights have been established. -/
noncomputable def probabilityKernelOfWeights
    (weight : X -> L -> Real)
    (hnonneg : forall x l, 0 <= weight x l)
    (htotal : forall x, (∑ l, weight x l) = 1) :
    FiniteProbabilityKernel X L :=
  fun x => probabilityVectorOfWeights (weight x) (hnonneg x) (htotal x)

/-- The precise Euclidean-continuity property available without introducing a
topology on the bundled probability-vector subtype. -/
def KernelCoefficientwiseContinuous [TopologicalSpace X]
    (k : FiniteProbabilityKernel X L) : Prop :=
  forall l, Continuous fun x => (k x).1 l

theorem probabilityKernelOfWeights_coefficientwiseContinuous
    [TopologicalSpace X] (weight : X -> L -> Real)
    (hnonneg : forall x l, 0 <= weight x l)
    (htotal : forall x, (∑ l, weight x l) = 1)
    (hcontinuous : forall l, Continuous fun x => weight x l) :
    KernelCoefficientwiseContinuous
      (probabilityKernelOfWeights weight hnonneg htotal) := by
  intro l
  simpa [probabilityKernelOfWeights] using hcontinuous l

/-- A finite monotone coupling: a nonnegative joint mass table with the stated
marginals and support contained in the order relation. -/
structure DiscreteMonotoneCoupling (mu nu : ProbabilityVector L) where
  joint : L -> L -> Real
  joint_nonneg : forall x y, 0 <= joint x y
  left_marginal : forall x, (∑ y, joint x y) = mu.1 x
  right_marginal : forall y, (∑ x, joint x y) = nu.1 y
  ordered_support : forall x y, 0 < joint x y -> x <= y

/-- The finite coupling implication used at the end of
`prop:rounding-monotone`: an order-supported coupling implies stochastic
comparison on every upper set. -/
theorem DiscreteMonotoneCoupling.stochasticLE
    {mu nu : ProbabilityVector L} (gamma : DiscreteMonotoneCoupling mu nu) :
    mu.1 <= nu.1 := by
  intro U
  unfold upperMass SubprobabilityVector.mass
  calc
    (∑ x, if x ∈ (U : Set L) then mu.1 x else 0) =
        ∑ x, ∑ y, if x ∈ (U : Set L) then gamma.joint x y else 0 := by
          apply Finset.sum_congr rfl
          intro x hx
          by_cases hxU : x ∈ (U : Set L)
          · simp [hxU, gamma.left_marginal x]
          · simp [hxU]
    _ <= ∑ x, ∑ y, if y ∈ (U : Set L) then gamma.joint x y else 0 := by
          apply Finset.sum_le_sum
          intro x hx
          apply Finset.sum_le_sum
          intro y hy
          by_cases hxU : x ∈ (U : Set L)
          · by_cases hyU : y ∈ (U : Set L)
            · simp [hxU, hyU]
            · have hnotpos : ¬0 < gamma.joint x y := by
                intro hpos
                exact hyU (U.upper (gamma.ordered_support x y hpos) hxU)
              have hzero : gamma.joint x y = 0 :=
                le_antisymm (le_of_not_gt hnotpos) (gamma.joint_nonneg x y)
              simp [hxU, hyU, hzero]
          · by_cases hyU : y ∈ (U : Set L)
            · simp [hxU, hyU, gamma.joint_nonneg x y]
            · simp [hxU, hyU]
    _ = ∑ y, if y ∈ (U : Set L) then nu.1 y else 0 := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro y hy
          by_cases hyU : y ∈ (U : Set L)
          · simp [hyU, gamma.right_marginal y]
          · simp [hyU]

end FiniteProbabilityKernels

section AffineInterior

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace Real E]

/-- `lem:affine-interior`, proved in the natural generality of real normed
vector spaces. -/
theorem affine_interior
    {K : Set E} (hK : Convex Real K) {x u v : E} {epsilon r : Real}
    (hx : x ∈ K) (hepsilon : 0 < epsilon) (hepsilon_one : epsilon <= 1)
    (hball : Metric.ball u r ⊆ interior K)
    (hv : ‖v‖ < epsilon * r) :
    (1 - epsilon) • x + epsilon • u + v ∈ interior K := by
  have hepsilon_ne : epsilon ≠ 0 := ne_of_gt hepsilon
  let y : E := u + epsilon⁻¹ • v
  have hdiv : ‖v‖ / epsilon < r := by
    apply (div_lt_iff₀ hepsilon).2
    nlinarith
  have hyball : y ∈ Metric.ball u r := by
    rw [Metric.mem_ball, dist_eq_norm]
    change ‖u + epsilon⁻¹ • v - u‖ < r
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hepsilon)]
    simpa [div_eq_mul_inv, mul_comm] using hdiv
  have hy : y ∈ interior K := hball hyball
  have hcombo : (1 - epsilon) • x + epsilon • y ∈ interior K :=
    hK.combo_self_interior_mem_interior hx hy
      (sub_nonneg.mpr hepsilon_one) hepsilon (by ring)
  simpa [y, smul_add, smul_smul, hepsilon_ne, add_assoc] using hcombo

end AffineInterior

end FiniteValuationApproximable
