import FiniteValuationApproximable.Rounding
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Measure.FiniteMeasurePi
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Typeclasses.NoAtoms
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Indicator

/-!
# Probability laws for monotone randomized rounding

This module supplies the measure-theoretic layer of the manuscript's
randomized grid rounding.  It deliberately keeps the probability space and
the finite output carrier visible.  The first section proves, for any finite
measurable law, normalization and the order-supported coupling construction
used later for the concrete Haar-uniform rounding inputs.
-/

set_option autoImplicit false
set_option linter.unnecessarySimpa false

universe u v w

namespace FiniteValuationApproximable

open scoped Classical BigOperators ENNReal MeasureTheory
open Set Function Filter MeasureTheory
open SubprobabilityVector

/-! ## Finite laws and measure-preserving couplings -/

section FiniteLaws

variable {Omega : Type u} {L : Type v}
variable [MeasurableSpace Omega] [Fintype L] [PartialOrder L]

/-- The real mass of one fibre of a finite-valued random variable. -/
noncomputable def finiteLawWeight (mu : Measure Omega) (Q : Omega -> L) (l : L) : Real :=
  mu.real (Q ⁻¹' {l})

theorem finiteLawWeight_nonneg (mu : Measure Omega) (Q : Omega -> L) (l : L) :
    0 <= finiteLawWeight mu Q l :=
  ENNReal.toReal_nonneg

/-- Fibre masses of a finite-valued random variable sum to one on a
probability space.  Asking for measurable fibres avoids installing an
unrelated measurable-space instance on an order-theoretic finite carrier. -/
theorem finiteLawWeight_sum_eq_one (mu : Measure Omega) [IsProbabilityMeasure mu]
    (Q : Omega -> L) (hQ : forall l, MeasurableSet (Q ⁻¹' {l})) :
    (∑ l, finiteLawWeight mu Q l) = 1 := by
  have hsum := sum_measureReal_preimage_singleton
    (μ := mu) (f := Q) (Finset.univ : Finset L)
    (fun l hl => hQ l) (h := fun l hl => measure_ne_top mu _)
  simpa [finiteLawWeight] using hsum

/-- The normalized finite probability vector induced by a measurable finite
random variable. -/
noncomputable def finiteLawProbabilityVector (mu : Measure Omega)
    [IsProbabilityMeasure mu] (Q : Omega -> L)
    (hQ : forall l, MeasurableSet (Q ⁻¹' {l})) : ProbabilityVector L :=
  probabilityVectorOfWeights (finiteLawWeight mu Q)
    (finiteLawWeight_nonneg mu Q) (finiteLawWeight_sum_eq_one mu Q hQ)

@[simp]
theorem finiteLawProbabilityVector_apply (mu : Measure Omega)
    [IsProbabilityMeasure mu] (Q : Omega -> L)
    (hQ : forall l, MeasurableSet (Q ⁻¹' {l})) (l : L) :
    (finiteLawProbabilityVector mu Q hQ).1 l = finiteLawWeight mu Q l :=
  rfl

/-- Positive coefficient mass supplies an actual sample in the corresponding
fibre. -/
theorem finiteLawWeight_pos_has_sample (mu : Measure Omega) (Q : Omega -> L)
    {l : L} (hl : 0 < finiteLawWeight mu Q l) :
    exists omega, Q omega = l := by
  have hne : mu (Q ⁻¹' {l}) ≠ 0 := by
    intro hzero
    simp [finiteLawWeight, Measure.real, hzero] at hl
  rcases nonempty_of_measure_ne_zero hne with ⟨omega, homega⟩
  exact ⟨omega, by simpa using homega⟩

/-- A measure-preserving deterministic coupling produces a finite monotone
coupling of its two finite laws.  This is the reusable probability-theoretic
closure step behind `prop:rounding-monotone`; all order work stays in the
pointwise hypothesis `hord`. -/
noncomputable def finiteLawMonotoneCoupling
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (Q R : Omega -> L)
    (hQ : forall l, MeasurableSet (Q ⁻¹' {l}))
    (hR : forall l, MeasurableSet (R ⁻¹' {l}))
    (T : Omega -> Omega) (hT : MeasurePreserving T mu mu)
    (hord : forall omega, Q omega <= R (T omega)) :
    DiscreteMonotoneCoupling
      (finiteLawProbabilityVector mu Q hQ)
      (finiteLawProbabilityVector mu R hR) where
  joint x y :=
    (mu.restrict (Q ⁻¹' {x})).real
      ((fun omega => R (T omega)) ⁻¹' {y})
  joint_nonneg x y := ENNReal.toReal_nonneg
  left_marginal x := by
    let A : Set Omega := Q ⁻¹' {x}
    let S : Omega -> L := fun omega => R (T omega)
    have hS (y : L) : MeasurableSet (S ⁻¹' {y}) := by
      exact hT.measurable (hR y)
    have hsum := sum_measureReal_preimage_singleton
      (μ := mu.restrict A) (f := S) (Finset.univ : Finset L)
      (fun y hy => hS y)
      (h := fun y hy => measure_ne_top (mu.restrict A) _)
    simpa [A, S, finiteLawProbabilityVector, finiteLawWeight] using hsum
  right_marginal y := by
    let B : Set Omega := (fun omega => R (T omega)) ⁻¹' {y}
    have hB : MeasurableSet B := by
      exact hT.measurable (hR y)
    have hsum := sum_measureReal_preimage_singleton
      (μ := mu.restrict B) (f := Q) (Finset.univ : Finset L)
      (fun x hx => hQ x)
      (h := fun x hx => measure_ne_top (mu.restrict B) _)
    calc
      (∑ x, (mu.restrict (Q ⁻¹' {x})).real B) =
          (∑ x, (mu.restrict B).real (Q ⁻¹' {x})) := by
            apply Finset.sum_congr rfl
            intro x hx
            simp only [Measure.real, Measure.restrict_apply hB,
              Measure.restrict_apply (hQ x), inter_comm]
      _ = mu.real B := by
        simpa using hsum
      _ = mu.real (R ⁻¹' {y}) := by
        exact hT.measureReal_preimage (hR y).nullMeasurableSet
      _ = (finiteLawProbabilityVector mu R hR).1 y := by
        rfl
  ordered_support x y hxy := by
    let A : Set Omega := Q ⁻¹' {x}
    let B : Set Omega := (fun omega => R (T omega)) ⁻¹' {y}
    have hB : MeasurableSet B := by
      exact hT.measurable (hR y)
    have hne : mu (B ∩ A) ≠ 0 := by
      intro hzero
      have hz : (mu.restrict A).real B = 0 := by
        simp [Measure.real, Measure.restrict_apply hB, hzero]
      exact (ne_of_gt hxy) hz
    rcases nonempty_of_measure_ne_zero hne with ⟨omega, homegaB, homegaA⟩
    have hQomega : Q omega = x := by simpa [A] using homegaA
    have hRomega : R (T omega) = y := by simpa [B] using homegaB
    simpa [hQomega, hRomega] using hord omega

end FiniteLaws

/-! ## Haar-uniform circle inputs -/

abbrev UnitAddCircle := AddCircle (1 : Real)

/-- The canonical representative of a point of `R / Z` in `[0,1)`. -/
noncomputable def unitRepresentative (x : UnitAddCircle) : Real :=
  (AddCircle.equivIco (1 : Real) 0 x : Real)

theorem unitRepresentative_mem_Ico (x : UnitAddCircle) :
    unitRepresentative x ∈ Ico (0 : Real) 1 := by
  simpa [unitRepresentative] using (AddCircle.equivIco (1 : Real) 0 x).property

theorem unitRepresentative_mem_unit (x : UnitAddCircle) :
    0 <= unitRepresentative x ∧ unitRepresentative x < 1 :=
  unitRepresentative_mem_Ico x

theorem measurable_unitRepresentative : Measurable unitRepresentative := by
  exact measurable_subtype_coe.comp
    (AddCircle.measurableEquivIco (1 : Real) 0).measurable

@[simp]
theorem unitRepresentative_coe (x : Real) :
    unitRepresentative (x : UnitAddCircle) = Int.fract x := by
  change ((AddCircle.equivIco (1 : Real) 0
    (QuotientAddGroup.mk x : UnitAddCircle)).1 : Real) = Int.fract x
  simpa using (AddCircle.coe_equivIco_mk_apply (p := (1 : Real)) x)

/-- Addition on `R / Z`, expressed through the canonical `[0,1)`
representative. -/
theorem unitRepresentative_add_coe (b : Real) (x : UnitAddCircle) :
    unitRepresentative ((b : UnitAddCircle) + x) =
      Int.fract (b + unitRepresentative x) := by
  have hx : ((unitRepresentative x : Real) : UnitAddCircle) = x := by
    exact AddCircle.coe_equivIco
  have hadd : ((b + unitRepresentative x : Real) : UnitAddCircle) =
      (b : UnitAddCircle) + x := by
    rw [AddCircle.coe_add, hx]
  rw [← hadd, unitRepresentative_coe]

/-- Independent Haar-uniform coordinates for the two random cubes appearing
in `Q_z(U,S)`. -/
abbrev HaarRoundingInput (I : Type u) (J : Type v) :=
  (I -> UnitAddCircle) × (J -> UnitAddCircle)

noncomputable def unitCircleProbability : ProbabilityMeasure UnitAddCircle :=
  ⟨AddCircle.haarAddCircle, inferInstance⟩

theorem unitCircleProbability_singleton (x : UnitAddCircle) :
    (unitCircleProbability : Measure UnitAddCircle) {x} = 0 := by
  have h := AddCircle.volume_closedBall (T := (1 : Real)) (x := x) 0
  rw [Metric.closedBall_zero, AddCircle.volume_eq_smul_haarAddCircle] at h
  simpa [unitCircleProbability] using h

noncomputable instance unitCircleProbability_noAtoms :
    NoAtoms (unitCircleProbability : Measure UnitAddCircle) :=
  ⟨unitCircleProbability_singleton⟩

noncomputable def unitCirclePiProbability (K : Type u) [Fintype K] :
    ProbabilityMeasure (K -> UnitAddCircle) :=
  ProbabilityMeasure.pi (fun _ => unitCircleProbability)

noncomputable def haarRoundingInputProbability
    (I : Type u) (J : Type v) [Fintype I] [Fintype J] :
    ProbabilityMeasure (HaarRoundingInput I J) :=
  (unitCirclePiProbability I).prod (unitCirclePiProbability J)

/-- The real `[0,1)` coordinates represented by the first Haar block. -/
noncomputable def haarInputU {I : Type u} {J : Type v}
    (omega : HaarRoundingInput I J) : I -> Real :=
  fun i => unitRepresentative (omega.1 i)

/-- The real `[0,1)` coordinates represented by the second Haar block. -/
noncomputable def haarInputS {I : Type u} {J : Type v}
    (omega : HaarRoundingInput I J) : J -> Real :=
  fun j => unitRepresentative (omega.2 j)

theorem haarInputU_mem_unitCube {I : Type u} {J : Type v}
    (omega : HaarRoundingInput I J) : InUnitCube (haarInputU omega) := by
  intro i
  exact unitRepresentative_mem_unit (omega.1 i)

theorem haarInputS_mem_unitCube {I : Type u} {J : Type v}
    (omega : HaarRoundingInput I J) : InUnitCube (haarInputS omega) := by
  intro j
  exact unitRepresentative_mem_unit (omega.2 j)

theorem measurable_haarInputU {I : Type u} {J : Type v} [Fintype I] [Fintype J] :
    Measurable (haarInputU : HaarRoundingInput I J -> I -> Real) := by
  apply measurable_pi_iff.mpr
  intro i
  exact measurable_unitRepresentative.comp
    ((measurable_pi_apply i).comp measurable_fst)

theorem measurable_haarInputS {I : Type u} {J : Type v} [Fintype I] [Fintype J] :
    Measurable (haarInputS : HaarRoundingInput I J -> J -> Real) := by
  apply measurable_pi_iff.mpr
  intro j
  exact measurable_unitRepresentative.comp
    ((measurable_pi_apply j).comp measurable_snd)

/-- The manuscript's deterministic `Q_z(U,S)`, now sampled from a genuine
product Haar probability space. -/
noncomputable def haarRandomizedFloor
    {I : Type u} {J : Type v} [Fintype I] [Fintype J]
    (z : I -> Real) (xi : J -> I -> Int)
    (omega : HaarRoundingInput I J) : I -> Int :=
  randomizedFloor z (haarInputU omega) (haarInputS omega) xi

theorem measurable_haarRandomizedFloor
    {I : Type u} {J : Type v} [Fintype I] [Fintype J]
    (z : I -> Real) (xi : J -> I -> Int) :
    Measurable (haarRandomizedFloor z xi) := by
  apply measurable_pi_iff.mpr
  intro i
  apply Measurable.floor
  exact (measurable_const.sub
    ((measurable_pi_apply i).comp measurable_haarInputU)).sub
    (Finset.measurable_sum _ fun j hj =>
      ((measurable_pi_apply j).comp measurable_haarInputS).mul_const (xi j i : Real))

theorem haarRandomizedFloor_mem_outcomeSet
    {I : Type u} {J : Type v} [Fintype I] [Fintype J]
    (z : I -> Real) (xi : J -> I -> Int)
    (omega : HaarRoundingInput I J) :
    haarRandomizedFloor z xi omega ∈ RoundingOutcomeSet z xi := by
  exact ⟨haarInputU omega, haarInputS omega,
    haarInputU_mem_unitCube omega, haarInputS_mem_unitCube omega, rfl⟩

/-! ### Modulo-one translation preserves the full input law -/

/-- Translate only the `S` block by the fractional parts of `beta`. -/
noncomputable def shiftHaarRoundingInput
    {I : Type u} {J : Type v} (beta : J -> Real)
    (omega : HaarRoundingInput I J) : HaarRoundingInput I J :=
  (omega.1, fun j => ((Int.fract (beta j) : Real) : UnitAddCircle) + omega.2 j)

theorem shiftHaarRoundingInput_u
    {I : Type u} {J : Type v} (beta : J -> Real)
    (omega : HaarRoundingInput I J) :
    haarInputU (shiftHaarRoundingInput beta omega) = haarInputU omega :=
  rfl

theorem shiftHaarRoundingInput_s
    {I : Type u} {J : Type v} (beta : J -> Real)
    (omega : HaarRoundingInput I J) :
    haarInputS (shiftHaarRoundingInput beta omega) =
      rotatedUnitShift beta (haarInputS omega) := by
  funext j
  simp only [haarInputS, shiftHaarRoundingInput, rotatedUnitShift]
  rw [unitRepresentative_add_coe]
  congr 1
  ring

theorem measurePreserving_unitCircle_add (c : UnitAddCircle) :
    MeasurePreserving (fun x : UnitAddCircle => c + x)
      (unitCircleProbability : Measure UnitAddCircle)
      (unitCircleProbability : Measure UnitAddCircle) := by
  simpa [unitCircleProbability] using
    (measurePreserving_add_left AddCircle.haarAddCircle c)

theorem measurePreserving_unitCirclePi_add
    {K : Type u} [Fintype K] (c : K -> UnitAddCircle) :
    MeasurePreserving (fun x k => c k + x k)
      (unitCirclePiProbability K : Measure (K -> UnitAddCircle))
      (unitCirclePiProbability K : Measure (K -> UnitAddCircle)) := by
  simpa [unitCirclePiProbability, unitCircleProbability] using
    (measurePreserving_pi
      (fun _ : K => (AddCircle.haarAddCircle : Measure UnitAddCircle))
      (fun _ : K => (AddCircle.haarAddCircle : Measure UnitAddCircle))
      (fun k => measurePreserving_add_left AddCircle.haarAddCircle (c k)))

theorem measurePreserving_shiftHaarRoundingInput
    {I : Type u} {J : Type v} [Fintype I] [Fintype J]
    (beta : J -> Real) :
    MeasurePreserving (shiftHaarRoundingInput (I := I) beta)
      (haarRoundingInputProbability I J : Measure (HaarRoundingInput I J))
      (haarRoundingInputProbability I J : Measure (HaarRoundingInput I J)) := by
  let c : J -> UnitAddCircle :=
    fun j => ((Int.fract (beta j) : Real) : UnitAddCircle)
  have hprod := MeasurePreserving.prod
    (MeasurePreserving.id
      (unitCirclePiProbability I : Measure (I -> UnitAddCircle)))
    (measurePreserving_unitCirclePi_add c)
  change MeasurePreserving
    (Prod.map id (fun x j =>
      ((Int.fract (beta j) : Real) : UnitAddCircle) + x j))
    ((unitCirclePiProbability I : Measure (I -> UnitAddCircle)).prod
      (unitCirclePiProbability J : Measure (J -> UnitAddCircle)))
    ((unitCirclePiProbability I : Measure (I -> UnitAddCircle)).prod
      (unitCirclePiProbability J : Measure (J -> UnitAddCircle)))
  simpa [c] using hprod

/-! ### Null floor boundaries -/

/-- One real pre-floor coordinate on the Haar input space. -/
noncomputable def haarRoundingArgument
    {I : Type u} {J : Type v} [Fintype I] [Fintype J]
    (z : I -> Real) (xi : J -> I -> Int) (i : I)
    (omega : HaarRoundingInput I J) : Real :=
  roundingArgument z (haarInputU omega) (haarInputS omega) xi i

theorem measurable_haarRoundingArgument
    {I : Type u} {J : Type v} [Fintype I] [Fintype J]
    (z : I -> Real) (xi : J -> I -> Int) (i : I) :
    Measurable (haarRoundingArgument z xi i) := by
  exact (measurable_const.sub
    ((measurable_pi_apply i).comp measurable_haarInputU)).sub
    (Finset.measurable_sum _ fun j hj =>
      ((measurable_pi_apply j).comp measurable_haarInputS).mul_const (xi j i : Real))

/-- Inputs at which coordinate `i` lies on an integral floor boundary. -/
def haarRoundingBoundary
    {I : Type u} {J : Type v} [Fintype I] [Fintype J]
    (z : I -> Real) (xi : J -> I -> Int) (i : I) :
    Set (HaarRoundingInput I J) :=
  {omega | exists k : Int, haarRoundingArgument z xi i omega = (k : Real)}

theorem measurableSet_haarRoundingBoundary
    {I : Type u} {J : Type v} [Fintype I] [Fintype J]
    (z : I -> Real) (xi : J -> I -> Int) (i : I) :
    MeasurableSet (haarRoundingBoundary z xi i) := by
  have heq : haarRoundingBoundary z xi i =
      ⋃ k : Int, {omega | haarRoundingArgument z xi i omega = (k : Real)} := by
    ext omega
    simp [haarRoundingBoundary]
  rw [heq]
  exact MeasurableSet.iUnion fun k =>
    measurableSet_eq_fun (measurable_haarRoundingArgument z xi i) measurable_const

/-- Every integral floor-boundary hyperplane has zero product Haar measure.
The proof conditions on the `S` block; for fixed `S` each integral boundary
is contained in a singleton of the independent `U_i` circle coordinate. -/
theorem measure_haarRoundingBoundary_zero
    {I : Type u} {J : Type v} [Fintype I] [Fintype J]
    (z : I -> Real) (xi : J -> I -> Int) (i : I) :
    (haarRoundingInputProbability I J : Measure (HaarRoundingInput I J))
      (haarRoundingBoundary z xi i) = 0 := by
  let muU : Measure (I -> UnitAddCircle) :=
    (unitCirclePiProbability I : Measure (I -> UnitAddCircle))
  let muS : Measure (J -> UnitAddCircle) :=
    (unitCirclePiProbability J : Measure (J -> UnitAddCircle))
  let B := haarRoundingBoundary z xi i
  have hB : MeasurableSet B := measurableSet_haarRoundingBoundary z xi i
  have hswapmeas : MeasurableSet (Prod.swap ⁻¹' B) := measurable_swap hB
  have hswapzero : muS.prod muU (Prod.swap ⁻¹' B) = 0 := by
    apply Measure.measure_prod_null_of_ae_null hswapmeas
    refine Filter.Eventually.of_forall fun s => ?_
    let K : Int -> Set (I -> UnitAddCircle) := fun k =>
      {u | u i = ((z i -
        roundingShiftSum (fun j => unitRepresentative (s j)) xi i - (k : Real) : Real) :
          UnitAddCircle)}
    have hsection : Prod.mk s ⁻¹' (Prod.swap ⁻¹' B) ⊆ ⋃ k, K k := by
      intro u hu
      change exists k : Int,
        haarRoundingArgument z xi i (u, s) = (k : Real) at hu
      rcases hu with ⟨k, hk⟩
      refine Set.mem_iUnion.mpr ⟨k, ?_⟩
      change u i = ((z i -
        roundingShiftSum (fun j => unitRepresentative (s j)) xi i - (k : Real) : Real) :
          UnitAddCircle)
      have hreal : unitRepresentative (u i) =
          z i - roundingShiftSum (fun j => unitRepresentative (s j)) xi i - (k : Real) := by
        have hsarg : haarInputS (u, s) = fun j => unitRepresentative (s j) := rfl
        simp only [haarRoundingArgument] at hk
        rw [hsarg] at hk
        simp only [roundingArgument, haarInputU] at hk
        linarith
      have hcoe : ((unitRepresentative (u i) : Real) : UnitAddCircle) = u i := by
        exact AddCircle.coe_equivIco
      rw [hreal] at hcoe
      exact hcoe.symm
    have hKzero (k : Int) : muU (K k) = 0 := by
      have hhyper := Measure.pi_hyperplane
        (fun _ : I => (unitCircleProbability : Measure UnitAddCircle)) i
        ((z i - roundingShiftSum (fun j => unitRepresentative (s j)) xi i -
          (k : Real) : Real) : UnitAddCircle)
      simpa [muU, unitCirclePiProbability] using hhyper
    exact measure_mono_null hsection (measure_iUnion_null hKzero)
  change muU.prod muS B = 0
  calc
    muU.prod muS B =
        muU.prod muS (Prod.swap ⁻¹' (Prod.swap ⁻¹' B)) := by
          congr 1
    _ = muS.prod muU (Prod.swap ⁻¹' B) := by
      exact (Measure.measurePreserving_swap (μ := muU) (ν := muS)).measure_preimage
        hswapmeas.nullMeasurableSet
    _ = 0 := hswapzero

/-- Simultaneously in all coordinates, a Haar input avoids every integral
floor boundary almost surely.  Finiteness of `I` is important here: this is
the single full-measure set on which all later coordinatewise stability
arguments are carried out. -/
theorem ae_forall_not_mem_haarRoundingBoundary
    {I : Type u} {J : Type v} [Fintype I] [Fintype J]
    (z : I -> Real) (xi : J -> I -> Int) :
    ∀ᵐ omega ∂(haarRoundingInputProbability I J :
        Measure (HaarRoundingInput I J)),
      forall i, omega ∉ haarRoundingBoundary z xi i := by
  let B : Set (HaarRoundingInput I J) :=
    ⋃ i, haarRoundingBoundary z xi i
  have hB : (haarRoundingInputProbability I J :
      Measure (HaarRoundingInput I J)) B = 0 := by
    exact measure_iUnion_null fun i => measure_haarRoundingBoundary_zero z xi i
  filter_upwards [compl_mem_ae_iff.mpr hB] with omega homega
  intro i hi
  exact homega (Set.mem_iUnion.mpr ⟨i, hi⟩)

/-- Away from the null boundary set, coordinatewise convergence of the input
point makes the entire finite integer rounding vector eventually constant.
This is the almost-everywhere stability assertion used in the source proof
of sequential continuity of the randomized law. -/
theorem ae_haarRandomizedFloor_eventually_eq_of_tendsto
    {I : Type u} {J : Type v} [Fintype I] [Fintype J]
    (q : Nat -> I -> Real) (z : I -> Real) (xi : J -> I -> Int)
    (hq : forall i, Tendsto (fun n => q n i) atTop (nhds (z i))) :
    ∀ᵐ omega ∂(haarRoundingInputProbability I J :
        Measure (HaarRoundingInput I J)),
      ∀ᶠ n in atTop,
        haarRandomizedFloor (q n) xi omega =
          haarRandomizedFloor z xi omega := by
  filter_upwards [ae_forall_not_mem_haarRoundingBoundary z xi] with omega hboundary
  have hcoordinate (i : I) :
      ∀ᶠ n in atTop,
        |q n i - z i| < min
          (haarRoundingArgument z xi i omega -
            haarRandomizedFloor z xi omega i)
          ((haarRandomizedFloor z xi omega i : Real) + 1 -
            haarRoundingArgument z xi i omega) := by
    let a : Real := haarRoundingArgument z xi i omega
    let k : Int := haarRandomizedFloor z xi omega i
    have hk : k = ⌊a⌋ := by
      simp [k, a, haarRandomizedFloor, randomizedFloor, floorVector,
        haarRoundingArgument]
    have hne : a ≠ (k : Real) := by
      intro hak
      exact hboundary i ⟨k, hak⟩
    have hleft : 0 < a - (k : Real) := sub_pos.mpr <| by
      rw [hk]
      exact (Int.floor_le a).lt_of_ne hne.symm
    have hright : 0 < (k : Real) + 1 - a := sub_pos.mpr <| by
      rw [hk]
      exact Int.lt_floor_add_one a
    have hmargin : 0 < min (a - (k : Real)) ((k : Real) + 1 - a) :=
      lt_min hleft hright
    have hdiff : Tendsto (fun n => |q n i - z i|) atTop (nhds 0) := by
      have hz : Tendsto (fun _ : Nat => z i) atTop (nhds (z i)) :=
        tendsto_const_nhds
      simpa using ((hq i).sub hz).abs
    have hball : Metric.ball (0 : Real)
        (min (a - (k : Real)) ((k : Real) + 1 - a)) ∈ nhds (0 : Real) :=
      Metric.ball_mem_nhds _ hmargin
    filter_upwards [hdiff.eventually hball] with n hn
    simpa [a, k, Metric.mem_ball, Real.dist_eq] using hn
  filter_upwards [(Finset.univ.eventually_all).mpr
      (fun i hi => hcoordinate i)] with n hn
  apply randomizedFloor_eq_of_coordinate_perturbation
  intro i
  simpa [haarRandomizedFloor, haarRoundingArgument] using
    hn i (Finset.mem_univ i)

/-! ## Finite encoded rounding kernels -/

section EncodedRounding

variable {I : Type u} {J : Type v} {L : Type w}
variable [Fintype I] [Fintype J] [Fintype L] [PartialOrder L]

/-- Encode the integer rounding output in a fixed finite carrier.  In the
finite-polytope construction the encoder is the inclusion into the stage's
finite bounding box. -/
noncomputable def encodedHaarRandomizedFloor
    (encode : (I -> Int) -> L) (z : I -> Real) (xi : J -> I -> Int)
    (omega : HaarRoundingInput I J) : L :=
  encode (haarRandomizedFloor z xi omega)

theorem measurableSet_encodedHaarRandomizedFloor_fiber
    (encode : (I -> Int) -> L) (z : I -> Real) (xi : J -> I -> Int)
    (l : L) :
    MeasurableSet (encodedHaarRandomizedFloor encode z xi ⁻¹' {l}) := by
  let target : Set (I -> Int) := encode ⁻¹' {l}
  have htarget : MeasurableSet target := Set.to_countable target |>.measurableSet
  exact measurable_haarRandomizedFloor z xi htarget

/-- Raw real coefficient of one encoded Haar-rounding outcome.  This is the
`weight` interface expected by the finite-polytope closure theorem. -/
noncomputable def encodedHaarRoundingWeight
    (encode : (I -> Int) -> L) (z : I -> Real) (xi : J -> I -> Int)
    (l : L) : Real :=
  finiteLawWeight
    (haarRoundingInputProbability I J : Measure (HaarRoundingInput I J))
    (encodedHaarRandomizedFloor encode z xi) l

theorem encodedHaarRoundingWeight_nonneg
    (encode : (I -> Int) -> L) (z : I -> Real) (xi : J -> I -> Int)
    (l : L) :
    0 <= encodedHaarRoundingWeight encode z xi l :=
  finiteLawWeight_nonneg _ _ _

theorem encodedHaarRoundingWeight_sum_eq_one
    (encode : (I -> Int) -> L) (z : I -> Real) (xi : J -> I -> Int) :
    (∑ l, encodedHaarRoundingWeight encode z xi l) = 1 := by
  exact finiteLawWeight_sum_eq_one
    (haarRoundingInputProbability I J : Measure (HaarRoundingInput I J))
    (encodedHaarRandomizedFloor encode z xi)
    (measurableSet_encodedHaarRandomizedFloor_fiber encode z xi)

/-- Every individual encoded rounding coefficient is sequentially continuous
in all input coordinates.  The proof is exactly the measure-theoretic closure
of the source argument: null floor boundaries give almost-everywhere eventual
indicator equality, and finite-measure indicator convergence gives convergence
of the fibre measures. -/
theorem encodedHaarRoundingWeight_tendsto
    (encode : (I -> Int) -> L) (q : Nat -> I -> Real)
    (z : I -> Real) (xi : J -> I -> Int)
    (hq : forall i, Tendsto (fun n => q n i) atTop (nhds (z i)))
    (l : L) :
    Tendsto (fun n => encodedHaarRoundingWeight encode (q n) xi l)
      atTop (nhds (encodedHaarRoundingWeight encode z xi l)) := by
  let mu : Measure (HaarRoundingInput I J) :=
    (haarRoundingInputProbability I J : Measure (HaarRoundingInput I J))
  let A : Set (HaarRoundingInput I J) :=
    encodedHaarRandomizedFloor encode z xi ⁻¹' {l}
  let As : Nat -> Set (HaarRoundingInput I J) := fun n =>
    encodedHaarRandomizedFloor encode (q n) xi ⁻¹' {l}
  have hA : MeasurableSet A := by
    exact measurableSet_encodedHaarRandomizedFloor_fiber encode z xi l
  have hAs (n : Nat) : MeasurableSet (As n) := by
    exact measurableSet_encodedHaarRandomizedFloor_fiber encode (q n) xi l
  have hlim : ∀ᵐ omega ∂mu,
      ∀ᶠ n in atTop, omega ∈ As n ↔ omega ∈ A := by
    filter_upwards [ae_haarRandomizedFloor_eventually_eq_of_tendsto
      q z xi hq] with omega homega
    filter_upwards [homega] with n hn
    simp only [As, A, Set.mem_preimage, Set.mem_singleton_iff,
      encodedHaarRandomizedFloor]
    rw [hn]
  have hmeasure : Tendsto (fun n => mu (As n)) atTop (nhds (mu A)) :=
    tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure
      atTop hA hAs hlim
  have hreal := (ENNReal.tendsto_toReal (measure_ne_top mu A)).comp hmeasure
  simpa [encodedHaarRoundingWeight, finiteLawWeight, Measure.real, mu, As, A]
    using hreal

/-- The genuine finite probability law of the encoded Haar rounding. -/
noncomputable def encodedHaarRoundingProbability
    (encode : (I -> Int) -> L) (z : I -> Real) (xi : J -> I -> Int) :
    ProbabilityVector L :=
  finiteLawProbabilityVector
    (haarRoundingInputProbability I J : Measure (HaarRoundingInput I J))
    (encodedHaarRandomizedFloor encode z xi)
    (measurableSet_encodedHaarRandomizedFloor_fiber encode z xi)

/-- The bundled probability vector is exactly the vector obtained from the
raw weights above.  This equality lets downstream finite-polytope code use
the measure construction without unfolding proof fields. -/
theorem encodedHaarRoundingProbability_eq_probabilityVectorOfWeights
    (encode : (I -> Int) -> L) (z : I -> Real) (xi : J -> I -> Int) :
    encodedHaarRoundingProbability encode z xi =
      probabilityVectorOfWeights (encodedHaarRoundingWeight encode z xi)
        (encodedHaarRoundingWeight_nonneg encode z xi)
        (encodedHaarRoundingWeight_sum_eq_one encode z xi) := by
  apply Subtype.ext
  apply SubprobabilityVector.ext
  intro l
  rfl

@[simp]
theorem encodedHaarRoundingProbability_apply
    (encode : (I -> Int) -> L) (z : I -> Real) (xi : J -> I -> Int)
    (l : L) :
    (encodedHaarRoundingProbability encode z xi).1 l =
      (haarRoundingInputProbability I J : Measure (HaarRoundingInput I J)).real
      (encodedHaarRandomizedFloor encode z xi ⁻¹' {l}) :=
  rfl

/-- Bundled form of coefficient continuity, ready to discharge the
`TableKernelSequentiallyContinuous` coefficient goal after choosing the
finite carrier and encoder at a fixed stage. -/
theorem encodedHaarRoundingProbability_tendsto
    (encode : (I -> Int) -> L) (q : Nat -> I -> Real)
    (z : I -> Real) (xi : J -> I -> Int)
    (hq : forall i, Tendsto (fun n => q n i) atTop (nhds (z i)))
    (l : L) :
    Tendsto
      (fun n => (encodedHaarRoundingProbability encode (q n) xi).1 l)
      atTop
      (nhds ((encodedHaarRoundingProbability encode z xi).1 l)) := by
  simpa [encodedHaarRoundingProbability, encodedHaarRoundingWeight] using
    encodedHaarRoundingWeight_tendsto encode q z xi hq l

/-- Positive encoded mass is supported by an actual deterministic rounding
outcome, hence by `RoundingOutcomeSet`. -/
theorem encodedHaarRoundingProbability_pos_support
    (encode : (I -> Int) -> L) (z : I -> Real) (xi : J -> I -> Int)
    {l : L} (hl : 0 < (encodedHaarRoundingProbability encode z xi).1 l) :
    exists q, q ∈ RoundingOutcomeSet z xi ∧ encode q = l := by
  have hl' : 0 < finiteLawWeight
      (haarRoundingInputProbability I J : Measure (HaarRoundingInput I J))
      (encodedHaarRandomizedFloor encode z xi) l := by
    simpa [encodedHaarRoundingProbability] using hl
  rcases finiteLawWeight_pos_has_sample
      (haarRoundingInputProbability I J : Measure (HaarRoundingInput I J))
      (encodedHaarRandomizedFloor encode z xi) hl' with ⟨omega, homega⟩
  exact ⟨haarRandomizedFloor z xi omega,
    haarRandomizedFloor_mem_outcomeSet z xi omega, homega⟩

/-- If the finite encoder comes with a decoder which is exact on every
rounding outcome, positive mass puts the decoded label in the deterministic
outcome set. -/
theorem encodedHaarRoundingProbability_pos_decoded_mem
    (encode : (I -> Int) -> L) (decode : L -> I -> Int)
    (z : I -> Real) (xi : J -> I -> Int)
    (hdecode : forall q, q ∈ RoundingOutcomeSet z xi -> decode (encode q) = q)
    {l : L} (hl : 0 < (encodedHaarRoundingProbability encode z xi).1 l) :
    decode l ∈ RoundingOutcomeSet z xi := by
  rcases encodedHaarRoundingProbability_pos_support encode z xi hl with
    ⟨q, hq, hencode⟩
  rw [← hencode, hdecode q hq]
  exact hq

/-- The fixed-carrier probability kernel obtained from the Haar rounding
law. -/
noncomputable def encodedHaarRoundingKernel
    (encode : (I -> Int) -> L) (xi : J -> I -> Int) :
    FiniteProbabilityKernel (I -> Real) L :=
  fun z => encodedHaarRoundingProbability encode z xi

/-- Haar invariance closes the probabilistic half of the manuscript's
monotone-rounding argument.  The only remaining input is the already proved
deterministic cone comparison, transported through the finite encoder. -/
noncomputable def encodedHaarRoundingMonotoneCoupling
    (encode : (I -> Int) -> L)
    {C : Set (I -> Real)}
    (hzero : (0 : I -> Real) ∈ C)
    (hadd : forall ⦃x y : I -> Real⦄, x ∈ C -> y ∈ C -> x + y ∈ C)
    (hsmul : forall ⦃x : I -> Real⦄, x ∈ C ->
      forall ⦃c : Real⦄, 0 <= c -> c • x ∈ C)
    (hbasis : forall i, coordinateBasis i ∈ C)
    {z z' : I -> Real} {beta : J -> Real} {alpha : I -> Real}
    {xi : J -> I -> Int}
    (hxi : forall j, castIntDirection (xi j) ∈ C)
    (hz : forall i, z' i - z i = alpha i +
      ∑ j, beta j * (xi j i : Real))
    (halpha : forall i, 0 <= alpha i)
    (hbeta : forall j, 0 <= beta j)
    (hencode : forall q r, realGridDifference q r ∈ C -> encode q <= encode r) :
    DiscreteMonotoneCoupling
      (encodedHaarRoundingProbability encode z xi)
      (encodedHaarRoundingProbability encode z' xi) := by
  let mu : Measure (HaarRoundingInput I J) :=
    (haarRoundingInputProbability I J : Measure (HaarRoundingInput I J))
  let Q : HaarRoundingInput I J -> L := encodedHaarRandomizedFloor encode z xi
  let R : HaarRoundingInput I J -> L := encodedHaarRandomizedFloor encode z' xi
  let T : HaarRoundingInput I J -> HaarRoundingInput I J :=
    shiftHaarRoundingInput beta
  apply finiteLawMonotoneCoupling mu Q R
    (measurableSet_encodedHaarRandomizedFloor_fiber encode z xi)
    (measurableSet_encodedHaarRandomizedFloor_fiber encode z' xi)
    T (measurePreserving_shiftHaarRoundingInput beta)
  intro omega
  apply hencode
  have hdet := deterministic_rounding_coupling_mem_cone
    (z := z) (z' := z') (u := haarInputU omega)
    (s := haarInputS omega) (beta := beta) (alpha := alpha) (xi := xi)
    hzero hadd hsmul hbasis hxi hz halpha hbeta
      (fun j => (haarInputS_mem_unitCube omega j).1)
  simpa [Q, R, T, encodedHaarRandomizedFloor, haarRandomizedFloor,
    shiftHaarRoundingInput_u, shiftHaarRoundingInput_s] using hdet

/-- Raw-weight presentation of `encodedHaarRoundingMonotoneCoupling`.  Its
two marginals are literally the `probabilityVectorOfWeights` terms used by
`finitePolytopeKernelOfWeights`, so this is the direct coupling interface for
`finite_polytope_isFVA_of_randomized_grid_coordinate_errors`. -/
noncomputable def encodedHaarRoundingWeightMonotoneCoupling
    (encode : (I -> Int) -> L)
    {C : Set (I -> Real)}
    (hzero : (0 : I -> Real) ∈ C)
    (hadd : forall ⦃x y : I -> Real⦄, x ∈ C -> y ∈ C -> x + y ∈ C)
    (hsmul : forall ⦃x : I -> Real⦄, x ∈ C ->
      forall ⦃c : Real⦄, 0 <= c -> c • x ∈ C)
    (hbasis : forall i, coordinateBasis i ∈ C)
    {z z' : I -> Real} {beta : J -> Real} {alpha : I -> Real}
    {xi : J -> I -> Int}
    (hxi : forall j, castIntDirection (xi j) ∈ C)
    (hz : forall i, z' i - z i = alpha i +
      ∑ j, beta j * (xi j i : Real))
    (halpha : forall i, 0 <= alpha i)
    (hbeta : forall j, 0 <= beta j)
    (hencode : forall q r, realGridDifference q r ∈ C -> encode q <= encode r) :
    DiscreteMonotoneCoupling
      (probabilityVectorOfWeights (encodedHaarRoundingWeight encode z xi)
        (encodedHaarRoundingWeight_nonneg encode z xi)
        (encodedHaarRoundingWeight_sum_eq_one encode z xi))
      (probabilityVectorOfWeights (encodedHaarRoundingWeight encode z' xi)
        (encodedHaarRoundingWeight_nonneg encode z' xi)
        (encodedHaarRoundingWeight_sum_eq_one encode z' xi)) := by
  rw [← encodedHaarRoundingProbability_eq_probabilityVectorOfWeights,
    ← encodedHaarRoundingProbability_eq_probabilityVectorOfWeights]
  exact encodedHaarRoundingMonotoneCoupling encode hzero hadd hsmul hbasis
    hxi hz halpha hbeta hencode

end EncodedRounding

end FiniteValuationApproximable
