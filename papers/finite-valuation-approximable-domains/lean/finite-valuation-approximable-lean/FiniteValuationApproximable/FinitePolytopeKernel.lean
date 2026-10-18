import FiniteValuationApproximable.KernelLifting
import FiniteValuationApproximable.FinitePolytope
import FiniteValuationApproximable.ContinuousValuation.FiniteProbability

/-!
# Genuine finite kernels from finite-polytope rounding data

This module is the representation bridge between the discrete randomized
rounding kernels constructed for finite monotone tables and the genuine
Jones--Plotkin probability kernels consumed by `KernelLifting`.  All
approximation laws are derived from the support-wise `Psi` sandwich; no
continuous-valuation law is added as a premise.
-/

set_option autoImplicit false
set_option linter.unnecessarySimpa false

universe u

namespace FiniteValuationApproximable

open Set Filter
open Erosion
open SubprobabilityVector
open AbstractApproximation

section FinitePolytopeKernel

variable {A P : Type u}
variable [Fintype A] [PartialOrder A] [Fintype P] [PartialOrder P]

variable (L : Nat -> FinitePoset.{u})
variable (p : forall n,
  MonotoneTable A P -> ProbabilityVector (L n))
variable (y : forall n, L n -> MonotoneTable A P)

/-- The genuine normalized kernel obtained from a Scott-continuous atomic
probability kernel. -/
noncomputable def finitePolytopeVOneKernel
    (hp : forall n, AbramskyJung.Chapter2.ScottContinuous
      (fun x : MonotoneTable A P => (p n x).1))
    (n : Nat) :
    ScottContFun (MonotoneTable A P)
      (ContinuousValuation.VOne (L n)) :=
  ContinuousValuation.probabilityKernelToFiniteVOne (p n) (hp n)

/-- A monotone label map out of a finite stage is Scott-continuous. -/
def finitePolytopeLabelContFun
    (hy : forall n, Monotone (y n)) (n : Nat) :
    ScottContFun (L n) (MonotoneTable A P) where
  toFun := y n
  continuous := scottContinuous_of_monotone_finite (hy n)

/-- The genuine subprobability kernel induced by the discrete rounding law
and its labels. -/
noncomputable def genuineFinitePolytopeKernel
    (hp : forall n, AbramskyJung.Chapter2.ScottContinuous
      (fun x : MonotoneTable A P => (p n x).1))
    (hy : forall n, Monotone (y n)) (n : Nat) :
    ScottContFun (MonotoneTable A P)
      (ContinuousValuation.VSub (MonotoneTable A P)) :=
  continuousFiniteKernel (L n)
    (finitePolytopeVOneKernel L p hp n)
    (finitePolytopeLabelContFun L y hy n)

omit [Fintype A] in
/-- The support-wise discrete sandwich transports exactly to the genuine
pushforward valuation kernel. -/
theorem genuineFinitePolytopeKernel_sandwich
    (beta alpha : Nat -> Real)
    (hp : forall n, AbramskyJung.Chapter2.ScottContinuous
      (fun x : MonotoneTable A P => (p n x).1))
    (hy : forall n, Monotone (y n))
    (hlower : forall n x l, 0 < p n x l ->
      Psi (beta n) x <= y n l)
    (hupper : forall n x l, 0 < p n x l ->
      y n l <= Psi (alpha n) x)
    (n : Nat) (x : MonotoneTable A P) :
    ContinuousValuation.dirac (Psi (beta n) x) <=
        genuineFinitePolytopeKernel L p y hp hy n x ∧
      genuineFinitePolytopeKernel L p y hp hy n x <=
        ContinuousValuation.dirac (Psi (alpha n) x) := by
  rw [genuineFinitePolytopeKernel, continuousFiniteKernel_apply]
  change ContinuousValuation.dirac (Psi (beta n) x) <=
      ContinuousValuation.pushforward
        (finitePolytopeLabelContFun L y hy n)
        (ContinuousValuation.VOne.toVSub
          (ContinuousValuation.probabilityVectorToVOne (p n x))) ∧
    ContinuousValuation.pushforward
        (finitePolytopeLabelContFun L y hy n)
        (ContinuousValuation.VOne.toVSub
          (ContinuousValuation.probabilityVectorToVOne (p n x))) <=
      ContinuousValuation.dirac (Psi (alpha n) x)
  exact ContinuousValuation.pushforward_probabilityVector_sandwich
    (p n x) (finitePolytopeLabelContFun L y hy n)
      (hlower n x) (hupper n x)

/-- An antitone real sequence converging to zero is pointwise nonnegative. -/
theorem antitone_tendsto_zero_nonneg
    (beta : Nat -> Real) (hbetaAntitone : Antitone beta)
    (hbeta : Tendsto beta atTop (nhds 0)) (n : Nat) :
    0 <= beta n :=
  hbetaAntitone.le_of_tendsto hbeta n

/-- A Scott-continuous discrete probability kernel, monotone finite labels,
and the parametric `Psi` sandwich determine a genuine finite probability-
kernel approximation of the identity on `M(A,P)`. -/
noncomputable def finitePolytopeKernelApproximation
    (beta alpha : Nat -> Real)
    (hbetaAntitone : Antitone beta)
    (hbeta : Tendsto beta atTop (nhds 0))
    (hinterleave : forall n, beta (n + 1) <= alpha n)
    (hp : forall n, AbramskyJung.Chapter2.ScottContinuous
      (fun x : MonotoneTable A P => (p n x).1))
    (hy : forall n, Monotone (y n))
    (hlower : forall n x l, 0 < p n x l ->
      Psi (beta n) x <= y n l)
    (hupper : forall n x l, 0 < p n x l ->
      y n l <= Psi (alpha n) x) :
    FiniteKernelApproximation (MonotoneTable A P) where
  stage := L
  probability := finitePolytopeVOneKernel L p hp
  label := finitePolytopeLabelContFun L y hy
  kernel_mono := by
    apply monotone_nat_of_le_succ
    intro n x
    have hn := genuineFinitePolytopeKernel_sandwich
      L p y beta alpha hp hy hlower hupper n x
    have hnext := genuineFinitePolytopeKernel_sandwich
      L p y beta alpha hp hy hlower hupper (n + 1) x
    have hflow : Psi (alpha n) x <= Psi (beta (n + 1)) x :=
      Psi_antitone_time x
        (antitone_tendsto_zero_nonneg beta hbetaAntitone hbeta (n + 1))
        (hinterleave n)
    exact le_trans hn.2 (le_trans
      (ContinuousValuation.dirac_scottContinuous.monotone hflow)
      hnext.1)
  kernel_below_unit := by
    intro n x
    have hn := genuineFinitePolytopeKernel_sandwich
      L p y beta alpha hp hy hlower hupper n x
    exact le_trans hn.2
      (ContinuousValuation.dirac_scottContinuous.monotone
        (Psi_le (alpha n) x))
  kernel_pointwise_sup_unit := by
    intro x
    have hbeta0 : forall n, 0 <= beta n :=
      antitone_tendsto_zero_nonneg beta hbetaAntitone hbeta
    constructor
    · rintro _ ⟨n, rfl⟩
      have hn := genuineFinitePolytopeKernel_sandwich
        L p y beta alpha hp hy hlower hupper n x
      exact le_trans hn.2
        (ContinuousValuation.dirac_scottContinuous.monotone
          (Psi_le (alpha n) x))
    · intro nu hnu
      have hPsiMono : Monotone (fun n => Psi (beta n) x) := by
        intro n m hnm
        exact Psi_antitone_time x (hbeta0 m) (hbetaAntitone hnm)
      have hPsiDir : AbramskyJung.Chapter2.DirectedSet
          (Set.range (fun n => Psi (beta n) x)) :=
        directedSet_range_of_monotone _ hPsiMono
      have hPsiSup := Psi_range_isSup_of_tendsto_zero
        beta hbeta0 hbeta x
      have hDiracSup :=
        ContinuousValuation.dirac_scottContinuous.maps_isSup
          hPsiDir hPsiSup
      apply hDiracSup.2 nu
      rintro _ ⟨z, ⟨n, rfl⟩, rfl⟩
      exact le_trans
        (genuineFinitePolytopeKernel_sandwich
          L p y beta alpha hp hy hlower hupper n x).1
        (hnu ⟨n, rfl⟩)

end FinitePolytopeKernel

end FiniteValuationApproximable
