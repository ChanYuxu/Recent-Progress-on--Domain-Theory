import FiniteValuationApproximable.FinitePolytope
import FiniteValuationApproximable.RoundingTable
import FiniteValuationApproximable.RoundingMeasure
import FiniteValuationApproximable.MainLocal

/-!
# The concrete Haar finite-polytope approximation

This module closes the analytic interfaces left visible in
`FinitePolytope.lean`.  For nonempty finite `A` and `P`, it constructs the
finite grid, its Haar randomized-rounding weights, the order-supported
couplings, and the coefficientwise sequential limit.  Empty cases are
terminal and are discharged through `subsingleton_isFVA`.
-/

set_option autoImplicit false
set_option linter.unnecessarySimpa false

universe u

namespace FiniteValuationApproximable

open scoped Classical BigOperators Topology ENNReal MeasureTheory
open Set Filter Function MeasureTheory
open SubprobabilityVector
open AbstractApproximation
open Erosion

section Parameters

variable {A P : Type u}
variable [Fintype A] [PartialOrder A] [Fintype P] [PartialOrder P]
variable [Nonempty A] [Nonempty P]

/-- A fixed starting erosion scale, strictly between zero and one. -/
noncomputable def finiteTableEpsilon0 : Real := 1 / 4

/-- The positive finite-poset loss constant. -/
theorem erosionConstant_pos : 0 < erosionConstant (P := P) := by
  unfold erosionConstant
  have hcard : 0 < Fintype.card P := Fintype.card_pos
  positivity

/-- The scalar constant occurring in the lower flow sandwich. -/
noncomputable def finiteTableScaleConstant : Real :=
  geometricScaleConstant (erosionConstant (P := P))
    (tableMeshCoefficient (A := A) (P := P))
    (tableRoundingBound (A := A) (P := P))

theorem finiteTableScaleConstant_pos :
    0 < finiteTableScaleConstant (A := A) (P := P) := by
  unfold finiteTableScaleConstant
  exact geometricScaleConstant_pos erosionConstant_pos
    (tableMeshCoefficient_pos (A := A) (P := P)).le
    (tableRoundingBound_pos (A := A) (P := P)).le

/-- One explicit geometric ratio satisfying both manuscript restrictions. -/
noncomputable def finiteTableTheta : Real :=
  1 / (2 * (1 + erosionConstant (P := P) *
    finiteTableScaleConstant (A := A) (P := P)))

theorem finiteTableTheta_pos :
    0 < finiteTableTheta (A := A) (P := P) := by
  have hK := erosionConstant_pos (P := P)
  have hC := finiteTableScaleConstant_pos (A := A) (P := P)
  unfold finiteTableTheta
  exact div_pos (by norm_num)
    (mul_pos (by norm_num) (by nlinarith [mul_pos hK hC]))

theorem finiteTableTheta_lt_one :
    finiteTableTheta (A := A) (P := P) < 1 := by
  have hK := erosionConstant_pos (P := P)
  have hC := finiteTableScaleConstant_pos (A := A) (P := P)
  unfold finiteTableTheta
  rw [one_div]
  have hden : 1 < 2 * (1 + erosionConstant (P := P) *
      finiteTableScaleConstant (A := A) (P := P)) := by
    nlinarith
  exact inv_lt_one_of_one_lt₀ hden

theorem finiteTableTheta_lt_interleave :
    finiteTableTheta (A := A) (P := P) <
      1 / (erosionConstant (P := P) *
        finiteTableScaleConstant (A := A) (P := P)) := by
  have hK := erosionConstant_pos (P := P)
  have hC := finiteTableScaleConstant_pos (A := A) (P := P)
  have hKC : 0 < erosionConstant (P := P) *
      finiteTableScaleConstant (A := A) (P := P) := mul_pos hK hC
  apply (div_lt_div_iff₀ (by positivity :
      0 < 2 * (1 + erosionConstant (P := P) *
        finiteTableScaleConstant (A := A) (P := P))) hKC).2
  nlinarith

/-- The inward-mixing scale used at stage `n`. -/
noncomputable def finiteTableEpsilon (n : Nat) : Real :=
  geometricEpsilon finiteTableEpsilon0
    (finiteTableTheta (A := A) (P := P)) n

/-- The integer grid mesh used at stage `n`. -/
noncomputable def finiteTableMesh (n : Nat) : Real :=
  geometricMesh finiteTableEpsilon0
    (finiteTableTheta (A := A) (P := P))
    (tableMeshCoefficient (A := A) (P := P)) n

theorem finiteTableEpsilon_pos (n : Nat) :
    0 < finiteTableEpsilon (A := A) (P := P) n := by
  exact geometricEpsilon_pos (by norm_num [finiteTableEpsilon0])
    finiteTableTheta_pos n

theorem finiteTableEpsilon_le_one (n : Nat) :
    finiteTableEpsilon (A := A) (P := P) n <= 1 := by
  have htheta0 := (finiteTableTheta_pos (A := A) (P := P)).le
  have htheta1 := (finiteTableTheta_lt_one (A := A) (P := P)).le
  have hpow : finiteTableTheta (A := A) (P := P) ^ n <= 1 :=
    pow_le_one₀ htheta0 htheta1
  unfold finiteTableEpsilon geometricEpsilon finiteTableEpsilon0
  nlinarith [pow_nonneg htheta0 n]

theorem finiteTableMesh_pos (n : Nat) :
    0 < finiteTableMesh (A := A) (P := P) n := by
  exact geometricMesh_pos (by norm_num [finiteTableEpsilon0])
    finiteTableTheta_pos tableMeshCoefficient_pos n

end Parameters

section ConcreteLaw

variable {A P : Type u}
variable [Fintype A] [PartialOrder A] [Fintype P] [PartialOrder P]
variable [Nonempty A] [Nonempty P]

/-- The finite grid carrier at stage `n`. -/
noncomputable def finiteTableStage (n : Nat) : FinitePoset.{u} :=
  scaledTableGridFinitePoset (A := A) (P := P)
    (finiteTableMesh (A := A) (P := P) n)
    (finiteTableMesh_pos (A := A) (P := P) n)

/-- The normalized affine input to integer randomized rounding. -/
noncomputable def finiteTableNormalizedInput (n : Nat)
    (x : MonotoneTable A P) : A × P -> Real :=
  divideVector
    (affineTableCoefficients
      (finiteTableEpsilon (A := A) (P := P) n) x
      (strictFeasibleTable : MonotoneTable A P))
    (finiteTableMesh (A := A) (P := P) n)

/-- Total encoding of integer outcomes in the stage carrier. -/
noncomputable def finiteTableEncode (n : Nat) :
    (A × P -> Int) -> finiteTableStage (A := A) (P := P) n :=
  scaledTableGridEncode (finiteTableMesh (A := A) (P := P) n)

/-- The genuine Haar fibre mass of a finite grid label. -/
noncomputable def finiteTableWeight (n : Nat) (x : MonotoneTable A P)
    (l : finiteTableStage (A := A) (P := P) n) : Real :=
  encodedHaarRoundingWeight
    (finiteTableEncode (A := A) (P := P) n)
    (finiteTableNormalizedInput (A := A) (P := P) n x)
    (tableRoundingDirections (A := A) (P := P)) l

/-- The monotone table represented by one finite grid label. -/
noncomputable def finiteTableGrid (n : Nat)
    (l : finiteTableStage (A := A) (P := P) n) : MonotoneTable A P :=
  scaledTableGridEmbedding
    (finiteTableMesh (A := A) (P := P) n) l

theorem finiteTableWeight_nonneg (n : Nat) (x : MonotoneTable A P)
    (l : finiteTableStage (A := A) (P := P) n) :
    0 <= finiteTableWeight (A := A) (P := P) n x l := by
  exact encodedHaarRoundingWeight_nonneg _ _ _ _

theorem finiteTableWeight_sum_eq_one (n : Nat) (x : MonotoneTable A P) :
    (∑ l, finiteTableWeight (A := A) (P := P) n x l) = 1 := by
  exact encodedHaarRoundingWeight_sum_eq_one _ _ _

theorem finiteTableGrid_mono (n : Nat) :
    Monotone (finiteTableGrid (A := A) (P := P) n) := by
  exact scaledTableGridEmbedding_mono
    (finiteTableMesh_pos (A := A) (P := P) n).le

/-- Every deterministic outcome of the concrete law is a valid point of its
finite grid carrier; this is where the internally proved interior ball and
the explicit zonotope radius are used. -/
theorem finiteTableOutcome_valid (n : Nat) (x : MonotoneTable A P)
    {q : A × P -> Int}
    (hq : q ∈ RoundingOutcomeSet
      (finiteTableNormalizedInput (A := A) (P := P) n x)
      (tableRoundingDirections (A := A) (P := P))) :
    IsScaledTableGridPoint (A := A) (P := P)
      (finiteTableMesh (A := A) (P := P) n) q := by
  simpa only [finiteTableNormalizedInput, finiteTableMesh, finiteTableEpsilon,
      geometricMesh] using
    (roundingOutcome_isScaledTableGridPoint
      x (strictFeasibleTable : MonotoneTable A P)
      (finiteTableEpsilon_pos (A := A) (P := P) n)
      (finiteTableEpsilon_le_one (A := A) (P := P) n)
      (tableMeshCoefficient_pos (A := A) (P := P))
      (tableRoundingBound_pos (A := A) (P := P)).le
      (tableMeshCoefficient_mul_bound_lt_radius (A := A) (P := P))
      (tableInteriorRadius_ball (A := A) (P := P))
      (tableRoundingDirections (A := A) (P := P))
      (fun q hq => tableRoundingZonotope_norm_le
        (A := A) (P := P) (q := q) hq) hq)

theorem finiteTableEncode_val_of_outcome (n : Nat) (x : MonotoneTable A P)
    {q : A × P -> Int}
    (hq : q ∈ RoundingOutcomeSet
      (finiteTableNormalizedInput (A := A) (P := P) n x)
      (tableRoundingDirections (A := A) (P := P))) :
    (finiteTableEncode (A := A) (P := P) n q).1 = q := by
  exact scaledTableGridEncode_val_of_mem _
    (finiteTableOutcome_valid (A := A) (P := P) n x hq)

/-- Positive Haar mass gives the raw lower and upper coordinate errors needed
by the flow sandwich. -/
theorem finiteTableWeight_pos_coordinate_errors
    (n : Nat) (x : MonotoneTable A P)
    (l : finiteTableStage (A := A) (P := P) n)
    (hl : 0 < finiteTableWeight (A := A) (P := P) n x l) :
    forall a U,
      x.upperCoordinate a U -
          geometricLowerError finiteTableEpsilon0
            (finiteTableTheta (A := A) (P := P))
            (tableMeshCoefficient (A := A) (P := P))
            (tableRoundingBound (A := A) (P := P)) n <=
        (finiteTableGrid (A := A) (P := P) n l).upperCoordinate a U ∧
      (finiteTableGrid (A := A) (P := P) n l).upperCoordinate a U <=
        x.upperCoordinate a U +
          geometricUpperError finiteTableEpsilon0
            (finiteTableTheta (A := A) (P := P)) n := by
  have hl' : 0 <
      (encodedHaarRoundingProbability
        (finiteTableEncode (A := A) (P := P) n)
        (finiteTableNormalizedInput (A := A) (P := P) n x)
        (tableRoundingDirections (A := A) (P := P))).1 l := by
    simpa [finiteTableWeight, encodedHaarRoundingProbability,
      encodedHaarRoundingWeight] using hl
  rcases encodedHaarRoundingProbability_pos_support
      (finiteTableEncode (A := A) (P := P) n)
      (finiteTableNormalizedInput (A := A) (P := P) n x)
      (tableRoundingDirections (A := A) (P := P)) hl' with
    ⟨q, hq, hencode⟩
  have hqvalid := finiteTableOutcome_valid (A := A) (P := P) n x hq
  have hqeq : q = l.1 := by
    have hval := congrArg Subtype.val hencode
    rw [finiteTableEncode_val_of_outcome n x hq] at hval
    exact hval
  subst q
  have herr := scaledTableGridEmbedding_coordinate_errors_of_outcome
    x (strictFeasibleTable : MonotoneTable A P)
    (finiteTableEpsilon_pos (A := A) (P := P) n)
    (tableMeshCoefficient_pos (A := A) (P := P))
    (tableRoundingBound_pos (A := A) (P := P)).le
    (tableRoundingDirections (A := A) (P := P))
    (cast_flatStrictTransferDirection_mem_cone (A := A) (P := P))
    (fun q hq a U => tableRoundingZonotope_upperMass_le
      (A := A) (P := P) (q := q) hq a U)
  simpa [finiteTableGrid, finiteTableMesh, finiteTableEpsilon,
    geometricMesh, geometricLowerError, geometricUpperError] using herr l hq

/-- At a fixed stage, the concrete Haar law is sequentially continuous in
all atomic coefficients. -/
theorem finiteTableWeight_sequentiallyContinuous (n : Nat) :
    TableKernelSequentiallyContinuous
      (finitePolytopeKernelOfWeights
        (finiteTableStage (A := A) (P := P))
        (finiteTableWeight (A := A) (P := P))
        (finiteTableWeight_nonneg (A := A) (P := P))
        (finiteTableWeight_sum_eq_one (A := A) (P := P)) n) := by
  intro q x hq l
  apply encodedHaarRoundingWeight_tendsto
  rintro ⟨a, p⟩
  unfold finiteTableNormalizedInput divideVector affineTableCoefficients
    tableCoefficients finiteTableMesh geometricMesh finiteTableEpsilon
  exact (((tendsto_const_nhds.mul (hq a p)).add tendsto_const_nhds).div_const _)

/-! ### Haar-translation monotone coupling -/

/-- The normalized affine displacement of two ordered tables lies in the
flattened table cone. -/
theorem finiteTableNormalizedInput_difference_mem
    (n : Nat) {x y : MonotoneTable A P} (hxy : x <= y) :
    (fun i =>
      finiteTableNormalizedInput (A := A) (P := P) n y i -
        finiteTableNormalizedInput (A := A) (P := P) n x i) ∈
      FlatTableOrderCone A P := by
  let d : A × P -> Real := fun i => tableDifference x y i.1 i.2
  have hd : d ∈ FlatTableOrderCone A P := by
    intro a
    exact (table_le_iff_difference_mem.mp hxy) a
  have hepsilon1 := finiteTableEpsilon_le_one (A := A) (P := P) n
  have hmesh := finiteTableMesh_pos (A := A) (P := P) n
  have hs := nonneg_smul_mem_flatTableOrderCone hd
    (div_nonneg (sub_nonneg.mpr hepsilon1) hmesh.le)
  convert hs using 1
  funext i
  rcases i with ⟨a, p⟩
  simp only [finiteTableNormalizedInput, divideVector,
    affineTableCoefficients, tableCoefficients, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, d, tableDifference]
  field_simp [hmesh.ne']
  ring

/-- The concrete encoded Haar laws at ordered inputs admit an
order-supported coupling.  Unlike the total encoder in isolation, this proof
first verifies that both coupled outputs lie in the valid grid carrier, so
the unreachable fallback branch is never used. -/
theorem finiteTableEncodedMonotoneCoupling
    (n : Nat) {x y : MonotoneTable A P} (hxy : x <= y) :
    Nonempty (DiscreteMonotoneCoupling
      (encodedHaarRoundingProbability
        (finiteTableEncode (A := A) (P := P) n)
        (finiteTableNormalizedInput (A := A) (P := P) n x)
        (tableRoundingDirections (A := A) (P := P)))
      (encodedHaarRoundingProbability
        (finiteTableEncode (A := A) (P := P) n)
        (finiteTableNormalizedInput (A := A) (P := P) n y)
        (tableRoundingDirections (A := A) (P := P)))) := by
  let z := finiteTableNormalizedInput (A := A) (P := P) n x
  let z' := finiteTableNormalizedInput (A := A) (P := P) n y
  let xi := tableRoundingDirections (A := A) (P := P)
  obtain ⟨alpha, beta, halpha, hbeta, hdecomp⟩ :=
    flatTableOrderCone_exists_coordinates
      (finiteTableNormalizedInput_difference_mem
        (A := A) (P := P) n hxy)
  let mu : Measure
      (HaarRoundingInput (A × P) (FlatStrictTransferIndex A P)) :=
    (haarRoundingInputProbability (A × P)
      (FlatStrictTransferIndex A P) : Measure _)
  let Q : HaarRoundingInput (A × P) (FlatStrictTransferIndex A P) ->
      finiteTableStage (A := A) (P := P) n :=
    encodedHaarRandomizedFloor
      (finiteTableEncode (A := A) (P := P) n) z xi
  let R : HaarRoundingInput (A × P) (FlatStrictTransferIndex A P) ->
      finiteTableStage (A := A) (P := P) n :=
    encodedHaarRandomizedFloor
      (finiteTableEncode (A := A) (P := P) n) z' xi
  let T : HaarRoundingInput (A × P) (FlatStrictTransferIndex A P) ->
      HaarRoundingInput (A × P) (FlatStrictTransferIndex A P) :=
    shiftHaarRoundingInput beta
  refine ⟨?_⟩
  apply finiteLawMonotoneCoupling mu Q R
    (measurableSet_encodedHaarRandomizedFloor_fiber
      (finiteTableEncode (A := A) (P := P) n) z xi)
    (measurableSet_encodedHaarRandomizedFloor_fiber
      (finiteTableEncode (A := A) (P := P) n) z' xi)
    T (measurePreserving_shiftHaarRoundingInput beta)
  intro omega
  let q := haarRandomizedFloor z xi omega
  let r := haarRandomizedFloor z' xi (T omega)
  have hqout : q ∈ RoundingOutcomeSet z xi := by
    exact haarRandomizedFloor_mem_outcomeSet z xi omega
  have hrout : r ∈ RoundingOutcomeSet z' xi := by
    exact haarRandomizedFloor_mem_outcomeSet z' xi (T omega)
  have hqvalid : IsScaledTableGridPoint (A := A) (P := P)
      (finiteTableMesh (A := A) (P := P) n) q := by
    apply finiteTableOutcome_valid (A := A) (P := P) n x
    simpa only [z] using hqout
  have hrvalid : IsScaledTableGridPoint (A := A) (P := P)
      (finiteTableMesh (A := A) (P := P) n) r := by
    apply finiteTableOutcome_valid (A := A) (P := P) n y
    simpa only [z'] using hrout
  dsimp only [Q, R, encodedHaarRandomizedFloor]
  change finiteTableEncode (A := A) (P := P) n q <=
    finiteTableEncode (A := A) (P := P) n r
  apply scaledTableGridEncode_le_of_mem
    (finiteTableMesh (A := A) (P := P) n) hqvalid hrvalid
  have hz (i : A × P) : z' i - z i = alpha i +
      ∑ j, beta j * (xi j i : Real) := by
    simpa only [z, z', xi, tableRoundingDirections] using hdecomp i
  change realGridDifference q r ∈ FlatTableOrderCone A P
  have hdet := deterministic_rounding_coupling_mem_cone
    (C := FlatTableOrderCone A P)
    (z := z) (z' := z') (u := haarInputU omega)
    (s := haarInputS omega) (beta := beta) (alpha := alpha) (xi := xi)
    zero_mem_flatTableOrderCone
    (@add_mem_flatTableOrderCone A P _ _ _)
    (@nonneg_smul_mem_flatTableOrderCone A P _ _ _)
    coordinateBasis_mem_flatTableOrderCone
    (cast_flatStrictTransferDirection_mem_cone (A := A) (P := P))
    hz halpha hbeta
    (fun j => (haarInputS_mem_unitCube omega j).1)
  simpa [q, r, xi, T, haarRandomizedFloor,
    shiftHaarRoundingInput_u, shiftHaarRoundingInput_s] using hdet

/-- Raw-weight presentation of the concrete monotone coupling, exactly in
the format consumed by the finite-polytope closure theorem. -/
theorem finiteTableWeightMonotoneCoupling
    (n : Nat) {x y : MonotoneTable A P} (hxy : x <= y) :
    Nonempty (DiscreteMonotoneCoupling
      (finitePolytopeKernelOfWeights
        (finiteTableStage (A := A) (P := P))
        (finiteTableWeight (A := A) (P := P))
        (finiteTableWeight_nonneg (A := A) (P := P))
        (finiteTableWeight_sum_eq_one (A := A) (P := P)) n x)
      (finitePolytopeKernelOfWeights
        (finiteTableStage (A := A) (P := P))
        (finiteTableWeight (A := A) (P := P))
        (finiteTableWeight_nonneg (A := A) (P := P))
        (finiteTableWeight_sum_eq_one (A := A) (P := P)) n y)) := by
  simpa only [finitePolytopeKernelOfWeights, probabilityKernelOfWeights,
    finiteTableWeight, encodedHaarRoundingProbability_eq_probabilityVectorOfWeights]
    using finiteTableEncodedMonotoneCoupling (A := A) (P := P) n hxy

end ConcreteLaw

section ConcreteApproximation

variable {A P : Type u}
variable [Fintype A] [PartialOrder A] [Fintype P] [PartialOrder P]
variable [Nonempty A] [Nonempty P]

/-- The lower erosion scale in the concrete sandwich. -/
noncomputable def finiteTableBeta (n : Nat) : Real :=
  geometricBeta finiteTableEpsilon0
    (finiteTableTheta (A := A) (P := P))
    (erosionConstant (P := P))
    (tableMeshCoefficient (A := A) (P := P))
    (tableRoundingBound (A := A) (P := P)) n

/-- The label erosion time in the concrete sandwich. -/
noncomputable def finiteTableLabelTime (n : Nat) : Real :=
  geometricLabelTime finiteTableEpsilon0
    (finiteTableTheta (A := A) (P := P)) n

/-- The upper erosion scale in the concrete sandwich. -/
noncomputable def finiteTableAlpha (n : Nat) : Real :=
  geometricAlpha finiteTableEpsilon0
    (finiteTableTheta (A := A) (P := P))
    (erosionConstant (P := P)) n

/-- The concrete atomic probability kernel. -/
noncomputable def finiteTableProbability (n : Nat) :
    MonotoneTable A P ->
      ProbabilityVector (finiteTableStage (A := A) (P := P) n) :=
  finitePolytopeKernelOfWeights
    (finiteTableStage (A := A) (P := P))
    (finiteTableWeight (A := A) (P := P))
    (finiteTableWeight_nonneg (A := A) (P := P))
    (finiteTableWeight_sum_eq_one (A := A) (P := P)) n

/-- The concrete finite label map. -/
noncomputable def finiteTableLabel (n : Nat) :
    finiteTableStage (A := A) (P := P) n -> MonotoneTable A P :=
  finitePolytopeGridLabelAt
    (finiteTableStage (A := A) (P := P))
    (finiteTableGrid (A := A) (P := P))
    (finiteTableLabelTime (A := A) (P := P)) n

theorem finiteTableBeta_nonneg (n : Nat) :
    0 <= finiteTableBeta (A := A) (P := P) n := by
  unfold finiteTableBeta
  exact geometricBeta_nonneg
    (by norm_num [finiteTableEpsilon0])
    (finiteTableTheta_pos (A := A) (P := P)).le
    (erosionConstant_pos (P := P))
    (tableMeshCoefficient_pos (A := A) (P := P)).le
    (tableRoundingBound_pos (A := A) (P := P)).le n

theorem finiteTableLabelTime_nonneg (n : Nat) :
    0 <= finiteTableLabelTime (A := A) (P := P) n := by
  unfold finiteTableLabelTime
  exact geometricLabelTime_nonneg
    (by norm_num [finiteTableEpsilon0])
    (finiteTableTheta_pos (A := A) (P := P)).le n

theorem finiteTableAlpha_nonneg (n : Nat) :
    0 <= finiteTableAlpha (A := A) (P := P) n := by
  unfold finiteTableAlpha
  exact geometricAlpha_nonneg
    (by norm_num [finiteTableEpsilon0])
    (finiteTableTheta_pos (A := A) (P := P)).le
    (erosionConstant_pos (P := P)).le n

theorem finiteTableBeta_tendsto_zero :
    Tendsto (finiteTableBeta (A := A) (P := P)) atTop (nhds 0) := by
  unfold finiteTableBeta
  exact geometricBeta_tendsto_zero
    (finiteTableTheta_pos (A := A) (P := P)).le
    (finiteTableTheta_lt_one (A := A) (P := P))

theorem finiteTableBeta_succ_le_alpha (n : Nat) :
    finiteTableBeta (A := A) (P := P) (n + 1) <=
      finiteTableAlpha (A := A) (P := P) n := by
  unfold finiteTableBeta finiteTableAlpha
  apply geometricBeta_succ_le_alpha
    (by norm_num [finiteTableEpsilon0])
    (finiteTableTheta_pos (A := A) (P := P)).le
    (erosionConstant_pos (P := P))
    (tableMeshCoefficient_pos (A := A) (P := P)).le
    (tableRoundingBound_pos (A := A) (P := P)).le
  · simpa only [finiteTableScaleConstant] using
      (finiteTableTheta_lt_interleave (A := A) (P := P))

/-- The concrete lower erosion scales decrease with the stage index. -/
theorem finiteTableBeta_antitone :
    Antitone (finiteTableBeta (A := A) (P := P)) := by
  apply antitone_nat_of_succ_le
  intro n
  unfold finiteTableBeta geometricBeta
  rw [geometricEpsilon_succ]
  have hepsilon : 0 <= geometricEpsilon finiteTableEpsilon0
      (finiteTableTheta (A := A) (P := P)) n :=
    geometricEpsilon_nonneg (by norm_num [finiteTableEpsilon0])
      (finiteTableTheta_pos (A := A) (P := P)).le n
  have htheta := (finiteTableTheta_lt_one (A := A) (P := P)).le
  have hinner : finiteTableTheta (A := A) (P := P) *
      geometricEpsilon finiteTableEpsilon0
        (finiteTableTheta (A := A) (P := P)) n <=
      geometricEpsilon finiteTableEpsilon0
        (finiteTableTheta (A := A) (P := P)) n := by
    have h := mul_le_mul_of_nonneg_right htheta hepsilon
    simpa using h
  exact mul_le_mul_of_nonneg_left hinner
    (geometricScaleConstant_pos
      (erosionConstant_pos (P := P))
      (tableMeshCoefficient_pos (A := A) (P := P)).le
      (tableRoundingBound_pos (A := A) (P := P)).le).le

theorem finiteTableProbability_scottContinuous (n : Nat) :
    AbramskyJung.Chapter2.ScottContinuous
      (fun x : MonotoneTable A P =>
        (finiteTableProbability (A := A) (P := P) n x).1) := by
  unfold finiteTableProbability
  exact probabilityKernel_scottContinuous_of_couplings_of_sequential _
    (fun x y hxy =>
      finiteTableWeightMonotoneCoupling (A := A) (P := P) n hxy)
    (finiteTableWeight_sequentiallyContinuous (A := A) (P := P) n)

theorem finiteTableLabel_mono (n : Nat) :
    Monotone (finiteTableLabel (A := A) (P := P) n) := by
  unfold finiteTableLabel
  exact finitePolytopeGridLabelAt_mono
    (finiteTableStage (A := A) (P := P))
    (finiteTableGrid (A := A) (P := P))
    (finiteTableLabelTime (A := A) (P := P))
    (finiteTableGrid_mono (A := A) (P := P)) n

/-- The exact support sandwich for the concrete Haar kernel and labels. -/
theorem finiteTableLabel_sandwich
    (n : Nat) (x : MonotoneTable A P)
    (l : finiteTableStage (A := A) (P := P) n)
    (hl : 0 < finiteTableProbability (A := A) (P := P) n x l) :
    Psi (finiteTableBeta (A := A) (P := P) n) x <=
        finiteTableLabel (A := A) (P := P) n l ∧
      finiteTableLabel (A := A) (P := P) n l <=
        Psi (finiteTableAlpha (A := A) (P := P) n) x := by
  have hlWeight : 0 < finiteTableWeight (A := A) (P := P) n x l := by
    simpa [finiteTableProbability] using hl
  have herr := finiteTableWeight_pos_coordinate_errors
    (A := A) (P := P) n x l hlWeight
  have hs := gridLabel_sandwich_of_coordinate_error
    x (finiteTableGrid (A := A) (P := P) n l)
    (finiteTableBeta_nonneg (A := A) (P := P) n)
    (finiteTableLabelTime_nonneg (A := A) (P := P) n)
    (finiteTableAlpha_nonneg (A := A) (P := P) n)
    (fun a U => (herr a U).1) (fun a U => (herr a U).2)
    (geometric_lower_scale_identity finiteTableEpsilon0
      (finiteTableTheta (A := A) (P := P))
      (erosionConstant (P := P))
      (tableMeshCoefficient (A := A) (P := P))
      (tableRoundingBound (A := A) (P := P)) n).le
    (geometric_upper_scale_identity finiteTableEpsilon0
      (finiteTableTheta (A := A) (P := P))
      (erosionConstant (P := P))
      (erosionConstant_pos (P := P)).ne' n).le
  simpa [finiteTableBeta, finiteTableLabelTime, finiteTableAlpha,
    finiteTableLabel, geometricLowerError, geometricUpperError] using hs

/-- The explicit finite-valuation approximate identity produced by the
concrete Haar grids.  Its fields expose the requested monotonicity, identity
upper bound, pointwise supremum, and finite factorization witnesses. -/
noncomputable def finiteMonotoneTableFVApproximateIdentity :
    FVApproximateIdentity.{u, u} (MonotoneTable A P) :=
  finitePolytopeFVApproximateIdentity_at
    (finiteTableStage (A := A) (P := P))
    (finiteTableProbability (A := A) (P := P))
    (finiteTableLabel (A := A) (P := P))
    (finiteTableBeta (A := A) (P := P))
    (finiteTableAlpha (A := A) (P := P))
    (finiteTableBeta_nonneg (A := A) (P := P))
    (finiteTableBeta_tendsto_zero (A := A) (P := P))
    (finiteTableBeta_succ_le_alpha (A := A) (P := P))
    (finiteTableProbability_scottContinuous (A := A) (P := P))
    (finiteTableLabel_mono (A := A) (P := P))
    (fun n x l hl =>
      (finiteTableLabel_sandwich (A := A) (P := P) n x l hl).1)
    (fun n x l hl =>
      (finiteTableLabel_sandwich (A := A) (P := P) n x l hl).2)

theorem finiteMonotoneTableFVApproximation_monotone :
    Monotone
      (finiteMonotoneTableFVApproximateIdentity (A := A) (P := P)).map :=
  (finiteMonotoneTableFVApproximateIdentity (A := A) (P := P)).monotone

theorem finiteMonotoneTableFVApproximation_below_id (n : Nat)
    (x : MonotoneTable A P) :
    (finiteMonotoneTableFVApproximateIdentity
      (A := A) (P := P)).map n x <= x :=
  (finiteMonotoneTableFVApproximateIdentity
    (A := A) (P := P)).below_id n x

theorem finiteMonotoneTableFVApproximation_pointwise_sup
    (x : MonotoneTable A P) :
    AJIsSup
      (Set.range (fun n =>
        (finiteMonotoneTableFVApproximateIdentity
          (A := A) (P := P)).map n x)) x :=
  (finiteMonotoneTableFVApproximateIdentity
    (A := A) (P := P)).pointwise_sup x

theorem finite_monotone_table_isFVA_of_nonempty :
    IsFVA.{u, u} (MonotoneTable A P) :=
  ⟨monotoneTable_isContinuousDcpo,
    ⟨finiteMonotoneTableFVApproximateIdentity (A := A) (P := P)⟩⟩

end ConcreteApproximation

/-! ## Terminal theorem, including empty finite posets -/

/-- Source theorem `thm:finite-polytope`: the monotone-table domain on any
two finite posets is finite-valuation approximable. -/
theorem finite_monotone_table_isFVA
    (A P : Type u)
    [Fintype A] [PartialOrder A] [Fintype P] [PartialOrder P] :
    IsFVA.{u, u} (MonotoneTable A P) := by
  classical
  cases isEmpty_or_nonempty A with
  | inl hA =>
      letI := hA
      letI : Nonempty (MonotoneTable A P) := ⟨zeroMonotoneTable⟩
      letI : Subsingleton (MonotoneTable A P) :=
        ⟨fun x y => MonotoneTable.ext_apply A P
          (fun a => isEmptyElim a)⟩
      exact subsingleton_isFVA (MonotoneTable A P)
  | inr hA =>
      letI := hA
      cases isEmpty_or_nonempty P with
      | inl hP =>
          letI := hP
          letI : Nonempty (MonotoneTable A P) := ⟨zeroMonotoneTable⟩
          letI : Subsingleton (MonotoneTable A P) :=
            ⟨fun x y => MonotoneTable.ext_coeff A P
              (fun _a p => isEmptyElim p)⟩
          exact subsingleton_isFVA (MonotoneTable A P)
      | inr hP =>
          letI := hP
          exact finite_monotone_table_isFVA_of_nonempty (A := A) (P := P)

end FiniteValuationApproximable
