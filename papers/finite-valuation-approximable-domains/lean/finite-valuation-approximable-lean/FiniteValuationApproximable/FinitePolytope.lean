import FiniteValuationApproximable.MonotoneTableDomain
import FiniteValuationApproximable.FiniteValuation.Kernel
import FiniteValuationApproximable.FiniteValuation.Consequences
import FiniteValuationApproximable.Rounding
import FiniteValuationApproximable.External.Gierz

/-!
# Finite-polytope kernel approximations

This module supplies the domain-theoretic and finite-valuation part of source
items `prop:kernel-sandwich`, `prop:finite-kernels`, and
`thm:finite-polytope` in `main (17).tex` (source SHA-256
`4b2e65f0f96347bea4df7571e8993ad6e888c0ff7181c1305c5056880365ac94`).

The genuinely analytic construction of the randomized kernels `p_eps` is
kept as an explicit input: for every scale it must provide a Scott-continuous
map into normalized finite valuations and support-wise label bounds.  From
those exact inputs, this file proves rather than assumes that

* barycentric reconstruction is Scott-continuous;
* the resulting maps `d_n` are increasing and below the identity;
* their pointwise supremum is the identity;
* every `d_n` factors through `VSub(L_n)`; and
* consequently `M(A,P)` is FVA once its externally cited continuous-domain
  premise is supplied.

No declaration in this file assumes `prop:finite-kernels` or
`thm:finite-polytope`, and no structure field contains either conclusion.
-/

set_option autoImplicit false
set_option linter.unnecessarySimpa false

universe u v w

namespace FiniteValuationApproximable

open scoped Classical BigOperators Topology
open Set Filter
open SubprobabilityVector
open AbstractApproximation
open Erosion

abbrev AJDirectedSet {D : Type u} [Preorder D] :=
  AbramskyJung.Chapter2.DirectedSet (α := D)

abbrev AJIsSup {D : Type u} [Preorder D] :=
  AbramskyJung.Chapter2.IsSup (α := D)

/-! ## Directed limits of finite barycentres -/

section DirectedLimits

variable {L : Type u} [Fintype L] [PartialOrder L]

/-- A specified directed supremum in a finite stochastic simplex admits a
sequence from the directed set converging in every atomic coefficient.  This
is the sequential bridge needed to prove continuity of finite integration. -/
theorem exists_coeff_tendsto_sequence_of_isSup
    (S : Set (SubprobabilityVector L)) (mu : SubprobabilityVector L)
    (hS : AJDirectedSet S) (hmu : AJIsSup S mu) :
    exists q : Nat -> SubprobabilityVector L,
      (forall n, q n ∈ S) ∧
        forall l : L, Tendsto (fun n => q n l) atTop (nhds (mu l)) := by
  let delta : Nat -> Real := fun n => 1 / ((n : Real) + 1)
  have hdelta_pos (n : Nat) : 0 < delta n := by
    dsimp only [delta]
    positivity
  have hdelta_tendsto : Tendsto delta atTop (nhds 0) := by
    simpa only [delta] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := Real))
  have happ (n : Nat) :
      exists q, q ∈ S ∧ forall U : UpperSet L,
        upperMass mu U - delta n < upperMass q U :=
    directedUpperMassApproximation S mu hS.1 hS.2
      (isLUB_of_chapter2IsSup hmu) (delta n) (hdelta_pos n)
  choose q hqS hqclose using happ
  refine ⟨q, hqS, ?_⟩
  have hmass_tendsto (U : UpperSet L) :
      Tendsto (fun n => upperMass (q n) U) atTop
        (nhds (upperMass mu U)) := by
    have hlower :
        Tendsto (fun n => upperMass mu U - delta n) atTop
          (nhds (upperMass mu U)) := by
      simpa using tendsto_const_nhds.sub hdelta_tendsto
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlower
      tendsto_const_nhds
      (fun n => le_of_lt (hqclose n U))
      (fun n => hmu.1 (hqS n) U)
  intro l
  exact tendsto_coeff_of_tendsto_upperMass hmass_tendsto l

/-- Finite weighted sums commute with coefficientwise sequential limits. -/
theorem tendsto_weightedSum_of_tendsto_coeff
    {q : Nat -> SubprobabilityVector L} {mu : SubprobabilityVector L}
    (hcoeff : forall l : L,
      Tendsto (fun n => q n l) atTop (nhds (mu l)))
    (g : L -> Real) :
    Tendsto (fun n => weightedSum (q n) g) atTop
      (nhds (weightedSum mu g)) := by
  unfold weightedSum
  apply tendsto_finset_sum Finset.univ
  intro l hl
  exact (hcoeff l).mul_const (g l)

end DirectedLimits

/-! ## The minimal analytic interface for the randomized kernel -/

section AnalyticKernel

variable {A : Type u} {P : Type v} {L : Type w}
variable [Fintype A] [PartialOrder A] [Fintype P] [PartialOrder P]
variable [Fintype L] [PartialOrder L]

/-- Evaluation of a finite monotone table at one source point preserves every
existing directed supremum. -/
theorem monotoneTable_eval_scottContinuous (a : A) :
    AbramskyJung.Chapter2.ScottContinuous
      (fun x : MonotoneTable A P => x a) := by
  let e := monotoneTableOrderIsoContFun (A := A) (P := P)
  have heval : AbramskyJung.Chapter2.ScottContinuous
      (fun f : AbramskyJung.Chapter3.ContFun A
        (SubprobabilityVector P) => f a) :=
    AbramskyJung.Chapter3.ContFun.eval_scottContinuous
      Erosion.finiteSubprobability_isDcpoOrder.1 a
  have hcomp := heval.comp (orderIso_scottContinuous e)
  simpa [e] using hcomp

/-- A directed supremum of finite monotone tables admits a sequence from the
directed set converging in every ambient atomic coordinate.  Finiteness of
`A` lets one choose one directed upper bound that simultaneously approximates
all rows at each accuracy. -/
theorem exists_table_coeff_tendsto_sequence_of_isSup
    (S : Set (MonotoneTable A P)) (x : MonotoneTable A P)
    (hS : AJDirectedSet S) (hx : AJIsSup S x) :
    exists q : Nat -> MonotoneTable A P,
      (forall n, q n ∈ S) ∧
        forall a p, Tendsto (fun n => q n a p) atTop (nhds (x a p)) := by
  let delta : Nat -> Real := fun n => 1 / ((n : Real) + 1)
  have hdelta_pos (n : Nat) : 0 < delta n := by
    dsimp only [delta]
    positivity
  have hdelta_tendsto : Tendsto delta atTop (nhds 0) := by
    simpa only [delta] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := Real))
  have hrowSup (a : A) :
      AJIsSup ((fun z : MonotoneTable A P => z a) '' S) (x a) :=
    (monotoneTable_eval_scottContinuous a).maps_isSup hS hx
  have hrowDirected (a : A) :
      AJDirectedSet ((fun z : MonotoneTable A P => z a) '' S) :=
    AbramskyJung.Chapter2.DirectedSet.image
      (fun (z1 z2 : MonotoneTable A P) (h : z1 <= z2) => h a) hS
  have hpoint (n : Nat) (a : A) :
      exists q, q ∈ S ∧ forall U : UpperSet P,
        upperMass (x a) U - delta n < upperMass (q a) U := by
    rcases directedUpperMassApproximation
        ((fun z : MonotoneTable A P => z a) '' S) (x a)
        (hrowDirected a).1 (hrowDirected a).2
        (isLUB_of_chapter2IsSup (hrowSup a))
        (delta n) (hdelta_pos n) with
      ⟨qa, ⟨q, hqS, rfl⟩, hqclose⟩
    exact ⟨q, hqS, hqclose⟩
  choose q0 hq0S hq0close using hpoint
  have hsimultaneous (n : Nat) :
      exists q, q ∈ S ∧ forall a U,
        upperMass (x a) U - delta n < upperMass (q a) U := by
    have hDirectedOn : DirectedOn (fun z1 z2 : MonotoneTable A P => z1 <= z2) S := by
      intro z1 hz1 z2 hz2
      exact hS.2 hz1 hz2
    letI : Nonempty {q : MonotoneTable A P // q ∈ S} :=
      ⟨⟨Classical.choose hS.1, Classical.choose_spec hS.1⟩⟩
    let candidates : Finset {q : MonotoneTable A P // q ∈ S} :=
      Finset.univ.image fun a : A => ⟨q0 n a, hq0S n a⟩
    rcases hDirectedOn.directed_val.finset_le candidates with ⟨z, hz⟩
    refine ⟨z.1, z.2, ?_⟩
    intro a U
    have hq0z : q0 n a <= z.1 :=
      hz ⟨q0 n a, hq0S n a⟩
        (Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩)
    exact (hq0close n a U).trans_le (hq0z a U)
  choose q hqS hqclose using hsimultaneous
  refine ⟨q, hqS, ?_⟩
  have hmass_tendsto (a : A) (U : UpperSet P) :
      Tendsto (fun n => upperMass (q n a) U) atTop
        (nhds (upperMass (x a) U)) := by
    have hlower :
        Tendsto (fun n => upperMass (x a) U - delta n) atTop
          (nhds (upperMass (x a) U)) := by
      simpa using tendsto_const_nhds.sub hdelta_tendsto
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlower
      tendsto_const_nhds
      (fun n => le_of_lt (hqclose n a U))
      (fun n => hx.1 (hqS n) a U)
  intro a p
  exact tendsto_coeff_of_tendsto_upperMass (hmass_tendsto a) p

/-- The exact analytic residue of the dominated-convergence argument in
`lem:rounding-law`: coordinatewise convergence of inputs implies convergence
of every coefficient of the finite rounding law.  This says neither
monotonicity nor Scott continuity and contains no approximation conclusion. -/
def TableKernelSequentiallyContinuous
    (p : MonotoneTable A P -> ProbabilityVector L) : Prop :=
  forall (q : Nat -> MonotoneTable A P) (x : MonotoneTable A P),
    (forall a r, Tendsto (fun n => q n a r) atTop (nhds (x a r))) ->
      forall l, Tendsto (fun n => p (q n) l) atTop (nhds (p x l))

/-- An order-supported finite coupling gives monotonicity of the associated
probability kernel. -/
theorem probabilityKernel_mono_of_couplings
    (p : MonotoneTable A P -> ProbabilityVector L)
    (hcouple : forall x y, x <= y ->
      Nonempty (DiscreteMonotoneCoupling (p x) (p y))) :
    Monotone (fun x => (p x).1) := by
  intro x y hxy
  rcases hcouple x y hxy with ⟨gamma⟩
  exact gamma.stochasticLE

/-- The two standard outputs of the randomized-rounding measure calculation
are sufficient for Scott continuity: modulo-one invariance supplies monotone
couplings, while dominated convergence supplies sequential coefficient
continuity.  Directed compactness of the finite table polytope is proved
internally above. -/
theorem probabilityKernel_scottContinuous_of_couplings_of_sequential
    (p : MonotoneTable A P -> ProbabilityVector L)
    (hcouple : forall x y, x <= y ->
      Nonempty (DiscreteMonotoneCoupling (p x) (p y)))
    (hseq : TableKernelSequentiallyContinuous p) :
    AbramskyJung.Chapter2.ScottContinuous (fun x => (p x).1) := by
  have hpmono : Monotone (fun x => (p x).1) :=
    probabilityKernel_mono_of_couplings p hcouple
  constructor
  · exact hpmono
  · intro S x hS hx
    rcases exists_table_coeff_tendsto_sequence_of_isSup S x hS hx with
      ⟨q, hqS, hqcoeff⟩
    have hpcoeff (l : L) :
        Tendsto (fun n => p (q n) l) atTop (nhds (p x l)) :=
      hseq q x hqcoeff l
    have hpmass (U : UpperSet L) :
        Tendsto (fun n => upperMass (p (q n)).1 U) atTop
          (nhds (upperMass (p x).1 U)) := by
      have h := Erosion.tendsto_upperMass_of_tendsto_coeff hpcoeff U
      simpa [upperMass, SubprobabilityVector.mass] using h
    constructor
    · rintro _ ⟨z, hzS, rfl⟩
      exact hpmono (hx.1 hzS)
    · intro b hb U
      have hle (n : Nat) : upperMass (p (q n)).1 U <= upperMass b U :=
        hb ⟨q n, hqS n, rfl⟩ U
      exact le_of_tendsto' (hpmass U) hle

end AnalyticKernel

/-! ## Scott continuity of finite barycentric reconstruction -/

section BarycenterContinuity

variable {L : Type u} {A : Type v} {P : Type w}
variable [Fintype L] [PartialOrder L]
variable [Preorder A] [Fintype P] [PartialOrder P]

/-- Upper-set mass of a finite Kleisli mixture is the weighted sum of the
upper-set masses of its components. -/
theorem upperMass_finiteBind
    (mu : SubprobabilityVector L)
    (k : L -> SubprobabilityVector P) (U : UpperSet P) :
    upperMass (finiteBind mu k) U =
      weightedSum mu (fun l => upperMass (k l) U) := by
  classical
  let indicator : P -> Real := fun p => if p ∈ (U : Set P) then 1 else 0
  have h := weightedSum_finiteBind mu k indicator
  simpa [indicator, weightedSum, upperMass, SubprobabilityVector.mass,
    Finset.sum_mul, mul_ite] using h

/-- Every monotone finite-label barycentric reconstruction preserves existing
directed suprema.  This closes the Scott-continuity assertion for `e_eps`
without appealing to Euclidean topology. -/
theorem tableBarycenter_scottContinuous
    (y : L -> MonotoneTable A P) (hy : Monotone y) :
    AbramskyJung.Chapter2.ScottContinuous
      (fun mu : SubprobabilityVector L => tableBarycenter mu y) := by
  constructor
  · exact tableBarycenter_mono hy
  · intro S mu hS hmu
    rcases exists_coeff_tendsto_sequence_of_isSup S mu hS hmu with
      ⟨q, hqS, hqcoeff⟩
    constructor
    · rintro _ ⟨nu, hnuS, rfl⟩
      exact tableBarycenter_mono hy (hmu.1 hnuS)
    · intro b hb a U
      let g : L -> Real := fun l => upperMass (y l a) U
      have htend :
          Tendsto (fun n => weightedSum (q n) g) atTop
            (nhds (weightedSum mu g)) :=
        tendsto_weightedSum_of_tendsto_coeff hqcoeff g
      have hle (n : Nat) :
          weightedSum (q n) g <= upperMass (b a) U := by
        have htable : tableBarycenter (q n) y <= b :=
          hb ⟨q n, hqS n, rfl⟩
        have hmass := htable a U
        change upperMass (finiteBind (q n) (fun l => y l a)) U <=
          upperMass (b a) U at hmass
        rw [upperMass_finiteBind] at hmass
        simpa [g] using hmass
      have hlimit : weightedSum mu g <= upperMass (b a) U :=
        le_of_tendsto' htend hle
      change upperMass (finiteBind mu (fun l => y l a)) U <=
        upperMass (b a) U
      rw [upperMass_finiteBind]
      simpa [g] using hlimit

end BarycenterContinuity

/-! ## Geometric interleaving and finite-valuation factorization -/

section KernelSequence

variable {A : Type u} {P : Type v}
variable [Fintype A] [PartialOrder A] [Fintype P] [PartialOrder P]

/-- The larger erosion time used for the lower sandwich at stage `n`.
Using every third erosion time leaves an intermediate time for the concrete
grid label and still interleaves with `finitePolytopeAlpha`. -/
noncomputable def finitePolytopeBeta (n : Nat) : Real :=
  erosionTime (3 * n)

/-- The intermediate erosion time used in the concrete grid label
`y_n(l) = Psi(labelTime n, grid_n(l))`. -/
noncomputable def finitePolytopeLabelTime (n : Nat) : Real :=
  erosionTime (3 * n + 1)

/-- The smaller erosion time used for the upper sandwich at stage `n`. -/
noncomputable def finitePolytopeAlpha (n : Nat) : Real :=
  erosionTime (3 * n + 2)

theorem finitePolytopeBeta_pos (n : Nat) : 0 < finitePolytopeBeta n :=
  erosionTime_pos (3 * n)

theorem finitePolytopeLabelTime_pos (n : Nat) :
    0 < finitePolytopeLabelTime n :=
  erosionTime_pos (3 * n + 1)

theorem finitePolytopeAlpha_pos (n : Nat) : 0 < finitePolytopeAlpha n :=
  erosionTime_pos (3 * n + 2)

/-- Within one stage, the lower-sandwich erosion time is the larger one. -/
theorem finitePolytopeAlpha_le_beta (n : Nat) :
    finitePolytopeAlpha n <= finitePolytopeBeta n := by
  exact erosionTime_antitone (by omega)

/-- The next lower-sandwich time lies below the current upper-sandwich time.
This is the exact interleaving inequality that makes the approximants
increasing. -/
theorem finitePolytopeBeta_succ_le_alpha (n : Nat) :
    finitePolytopeBeta (n + 1) <= finitePolytopeAlpha n := by
  exact erosionTime_antitone (by omega)

/-- More generally, every strictly later lower time lies below the current
upper time. -/
theorem finitePolytopeBeta_le_alpha_of_lt {n m : Nat} (hnm : n < m) :
    finitePolytopeBeta m <= finitePolytopeAlpha n := by
  exact erosionTime_antitone (by omega)

variable (L : Nat -> FinitePoset.{w})
variable (p : forall n, MonotoneTable A P -> ProbabilityVector (L n))
variable (y : forall n, L n -> MonotoneTable A P)

/-- The concrete barycentric map `d_n = e_n p_n`. -/
noncomputable def finitePolytopeApproximant (n : Nat) :
    MonotoneTable A P -> MonotoneTable A P :=
  finiteTableApproximant (p n) (y n)

@[simp]
theorem finitePolytopeApproximant_apply (n : Nat) (x : MonotoneTable A P) :
    finitePolytopeApproximant L p y n x =
      tableBarycenter (p n x).1 (y n) :=
  rfl

/-- Exact one-stage sandwich obtained from support-wise label bounds. -/
theorem finitePolytopeApproximant_sandwich
    (hlower : forall n x l, 0 < p n x l ->
      Psi (finitePolytopeBeta n) x <= y n l)
    (hupper : forall n x l, 0 < p n x l ->
      y n l <= Psi (finitePolytopeAlpha n) x)
    (n : Nat) (x : MonotoneTable A P) :
    Psi (finitePolytopeBeta n) x <=
        finitePolytopeApproximant L p y n x ∧
      finitePolytopeApproximant L p y n x <=
        Psi (finitePolytopeAlpha n) x := by
  exact finiteTableApproximant_sandwich (p n) (y n)
    (Psi (finitePolytopeBeta n)) (Psi (finitePolytopeAlpha n))
    (hlower n) (hupper n) x

/-- Parametric one-stage form used by the manuscript's geometric epsilon
scales. -/
theorem finitePolytopeApproximant_sandwich_at
    (beta alpha : Nat -> Real)
    (hlower : forall n x l, 0 < p n x l ->
      Psi (beta n) x <= y n l)
    (hupper : forall n x l, 0 < p n x l ->
      y n l <= Psi (alpha n) x)
    (n : Nat) (x : MonotoneTable A P) :
    Psi (beta n) x <= finitePolytopeApproximant L p y n x ∧
      finitePolytopeApproximant L p y n x <= Psi (alpha n) x := by
  exact finiteTableApproximant_sandwich (p n) (y n)
    (Psi (beta n)) (Psi (alpha n)) (hlower n) (hupper n) x

/-- Scott continuity of `d_n`, by composition of the analytic encoding `p_n`
with the internally proved continuous finite barycentre. -/
theorem finitePolytopeApproximant_scottContinuous
    (hp : forall n, AbramskyJung.Chapter2.ScottContinuous
      (fun x : MonotoneTable A P => (p n x).1))
    (hy : forall n, Monotone (y n)) (n : Nat) :
    AbramskyJung.Chapter2.ScottContinuous
      (finitePolytopeApproximant L p y n) := by
  exact (tableBarycenter_scottContinuous (y n) (hy n)).comp (hp n)

/-- The displayed factorization of `d_n` through `VSub(L_n)`.  The encoder
is the normalized finite kernel `p_n`; the decoder is finite barycentric
reconstruction. -/
noncomputable def finitePolytopeApproximantFactorization
    (hp : forall n, AbramskyJung.Chapter2.ScottContinuous
      (fun x : MonotoneTable A P => (p n x).1))
    (hy : forall n, Monotone (y n)) (n : Nat) :
    FiniteValuationFactorization.{max u v, max u v, w}
      (finitePolytopeApproximant L p y n) where
  stage := L n
  factorization := {
    encode := fun x => (p n x).1
    decode := fun mu => tableBarycenter mu (y n)
    encode_continuous := hp n
    decode_continuous := tableBarycenter_scottContinuous (y n) (hy n)
    factor := fun _ => rfl
  }

/-- The kernel sandwich produces the full finite-valuation approximate
identity asserted in `prop:finite-kernels`: monotonicity, the identity upper
bound, pointwise supremum, and every finite-stage factorization are proved
here from the displayed hypotheses. -/
noncomputable def finitePolytopeFVApproximateIdentity
    (hp : forall n, AbramskyJung.Chapter2.ScottContinuous
      (fun x : MonotoneTable A P => (p n x).1))
    (hy : forall n, Monotone (y n))
    (hlower : forall n x l, 0 < p n x l ->
      Psi (finitePolytopeBeta n) x <= y n l)
    (hupper : forall n x l, 0 < p n x l ->
      y n l <= Psi (finitePolytopeAlpha n) x) :
    FVApproximateIdentity.{max u v, w} (MonotoneTable A P) where
  map n := {
    toFun := finitePolytopeApproximant L p y n
    continuous := finitePolytopeApproximant_scottContinuous L p y hp hy n
  }
  monotone := by
    intro n m hnm x
    by_cases heq : n = m
    · subst m
      exact le_rfl
    · have hlt : n < m := lt_of_le_of_ne hnm heq
      have hn := finitePolytopeApproximant_sandwich L p y hlower hupper n x
      have hm := finitePolytopeApproximant_sandwich L p y hlower hupper m x
      exact le_trans hn.2 (le_trans
        (Psi_antitone_time x (finitePolytopeBeta_pos m).le
          (finitePolytopeBeta_le_alpha_of_lt hlt)) hm.1)
  below_id := by
    intro n x
    exact le_trans
      (finitePolytopeApproximant_sandwich L p y hlower hupper n x).2
      (Psi_le (finitePolytopeAlpha n) x)
  pointwise_sup := by
    intro x
    constructor
    · rintro _ ⟨n, rfl⟩
      exact le_trans
        (finitePolytopeApproximant_sandwich L p y hlower hupper n x).2
        (Psi_le (finitePolytopeAlpha n) x)
    · intro z hz
      apply (monotoneTableIncreasingApproximateIdentity.pointwise_sup x).2 z
      rintro _ ⟨n, rfl⟩
      have hindex : n <= 3 * n := by omega
      have hflow :
          Psi (erosionTime n) x <= Psi (finitePolytopeBeta n) x :=
        Psi_antitone_time x (finitePolytopeBeta_pos n).le
          (erosionTime_antitone hindex)
      exact le_trans hflow (le_trans
        (finitePolytopeApproximant_sandwich L p y hlower hupper n x).1
        (hz ⟨n, rfl⟩))
  factorable := by
    intro n
    exact ⟨finitePolytopeApproximantFactorization L p y hp hy n⟩

/-- Source-facing conditional form of `thm:finite-polytope`.  The first
premise is precisely the continuous-domain component of the externally cited
FS-exponential result; the remaining premises are the analytic `p_n` kernel
construction.  All finite-valuation and limiting conclusions are internal. -/
theorem finite_polytope_isFVA_of_kernel_sandwich
    (hDomain : AbramskyJung.Chapter2.IsContinuousDcpo
      (MonotoneTable A P))
    (hp : forall n, AbramskyJung.Chapter2.ScottContinuous
      (fun x : MonotoneTable A P => (p n x).1))
    (hy : forall n, Monotone (y n))
    (hlower : forall n x l, 0 < p n x l ->
      Psi (finitePolytopeBeta n) x <= y n l)
    (hupper : forall n x l, 0 < p n x l ->
      y n l <= Psi (finitePolytopeAlpha n) x) :
    IsFVA.{max u v, w} (MonotoneTable A P) :=
  ⟨hDomain,
    ⟨finitePolytopeFVApproximateIdentity L p y hp hy hlower hupper⟩⟩

/-- Variant matching the exact output of Gierz et al. II-2.18: an actual FS
approximate identity plus the already proved dcpo structure supplies the
continuous-domain premise, after which the kernel construction gives FVA. -/
theorem finite_polytope_isFVA_of_FS_and_kernel_sandwich
    (hFS : Nonempty (FSApproximateIdentity (MonotoneTable A P)))
    (hp : forall n, AbramskyJung.Chapter2.ScottContinuous
      (fun x : MonotoneTable A P => (p n x).1))
    (hy : forall n, Monotone (y n))
    (hlower : forall n x l, 0 < p n x l ->
      Psi (finitePolytopeBeta n) x <= y n l)
    (hupper : forall n x l, 0 < p n x l ->
      y n l <= Psi (finitePolytopeAlpha n) x) :
    IsFVA.{max u v, w} (MonotoneTable A P) := by
  rcases hFS with ⟨F⟩
  exact finite_polytope_isFVA_of_kernel_sandwich L p y
    ⟨monotoneTable_isDcpoOrder, F.continuousDomain⟩
    hp hy hlower hupper

/-! ### Parametric source scales -/

/-- Any nonnegative erosion-time sequence tending to zero has pointwise
supremum the identity on the monotone-table domain. -/
theorem Psi_range_isSup_of_tendsto_zero
    (beta : Nat -> Real) (hbeta0 : forall n, 0 <= beta n)
    (hbeta : Tendsto beta atTop (nhds 0))
    (x : MonotoneTable A P) :
    AJIsSup (Set.range fun n => Psi (beta n) x) x := by
  constructor
  · rintro _ ⟨n, rfl⟩
    exact Psi_le (beta n) x
  · intro b hb a U
    let K : Real := erosionConstant (P := P)
    have hlinear :
        Tendsto (fun n => x.upperCoordinate a U - K * beta n) atTop
          (nhds (x.upperCoordinate a U)) := by
      have hmul : Tendsto (fun n => K * beta n) atTop (nhds 0) := by
        simpa using tendsto_const_nhds.mul hbeta
      simpa using tendsto_const_nhds.sub hmul
    have hmax :
        Tendsto (fun n => max (x.upperCoordinate a U - K * beta n) 0)
          atTop (nhds (x.upperCoordinate a U)) := by
      have hm := hlinear.max (tendsto_const_nhds : Tendsto (fun _ : Nat => (0 : Real))
        atTop (nhds 0))
      have hx0 : 0 <= x.upperCoordinate a U :=
        SubprobabilityVector.mass_nonneg (x a) U
      rw [max_eq_left hx0] at hm
      exact hm
    have hle (n : Nat) :
        max (x.upperCoordinate a U - K * beta n) 0 <=
          upperMass (b a) U := by
      exact le_trans (Psi_two_sided x a U (hbeta0 n)).1
        (hb ⟨n, rfl⟩ a U)
    exact le_of_tendsto' hmax hle

/-- Parametric version of `prop:finite-kernels`.  It matches the source's
geometric epsilon scales directly: only nonnegativity, convergence to zero,
and the interleaving inequality `beta_(n+1) <= alpha_n` are required. -/
noncomputable def finitePolytopeFVApproximateIdentity_at
    (beta alpha : Nat -> Real)
    (hbeta0 : forall n, 0 <= beta n)
    (hbeta : Tendsto beta atTop (nhds 0))
    (hinterleave : forall n, beta (n + 1) <= alpha n)
    (hp : forall n, AbramskyJung.Chapter2.ScottContinuous
      (fun x : MonotoneTable A P => (p n x).1))
    (hy : forall n, Monotone (y n))
    (hlower : forall n x l, 0 < p n x l -> Psi (beta n) x <= y n l)
    (hupper : forall n x l, 0 < p n x l -> y n l <= Psi (alpha n) x) :
    FVApproximateIdentity.{max u v, w} (MonotoneTable A P) where
  map n := {
    toFun := finitePolytopeApproximant L p y n
    continuous := finitePolytopeApproximant_scottContinuous L p y hp hy n
  }
  monotone := by
    intro n m hnm x
    have hstep : forall k,
        finitePolytopeApproximant L p y k x <=
          finitePolytopeApproximant L p y (k + 1) x := by
      intro k
      have hk := finitePolytopeApproximant_sandwich_at L p y beta alpha
        hlower hupper k x
      have hks := finitePolytopeApproximant_sandwich_at L p y beta alpha
        hlower hupper (k + 1) x
      exact le_trans hk.2 (le_trans
        (Psi_antitone_time x (hbeta0 (k + 1)) (hinterleave k)) hks.1)
    exact (monotone_nat_of_le_succ hstep) hnm
  below_id := by
    intro n x
    exact le_trans
      (finitePolytopeApproximant_sandwich_at L p y beta alpha
        hlower hupper n x).2
      (Psi_le (alpha n) x)
  pointwise_sup := by
    intro x
    constructor
    · rintro _ ⟨n, rfl⟩
      exact le_trans
        (finitePolytopeApproximant_sandwich_at L p y beta alpha
          hlower hupper n x).2
        (Psi_le (alpha n) x)
    · intro z hz
      apply (Psi_range_isSup_of_tendsto_zero beta hbeta0 hbeta x).2 z
      rintro _ ⟨n, rfl⟩
      exact le_trans
        (finitePolytopeApproximant_sandwich_at L p y beta alpha
          hlower hupper n x).1
        (hz ⟨n, rfl⟩)
  factorable := by
    intro n
    exact ⟨finitePolytopeApproximantFactorization L p y hp hy n⟩

/-- Parametric FVA conclusion, with the finite-polytope domain theorem kept
as the separately audited input. -/
theorem finite_polytope_isFVA_of_kernel_sandwich_at
    (beta alpha : Nat -> Real)
    (hbeta0 : forall n, 0 <= beta n)
    (hbeta : Tendsto beta atTop (nhds 0))
    (hinterleave : forall n, beta (n + 1) <= alpha n)
    (hDomain : AbramskyJung.Chapter2.IsContinuousDcpo (MonotoneTable A P))
    (hp : forall n, AbramskyJung.Chapter2.ScottContinuous
      (fun x : MonotoneTable A P => (p n x).1))
    (hy : forall n, Monotone (y n))
    (hlower : forall n x l, 0 < p n x l -> Psi (beta n) x <= y n l)
    (hupper : forall n x l, 0 < p n x l -> y n l <= Psi (alpha n) x) :
    IsFVA.{max u v, w} (MonotoneTable A P) :=
  ⟨hDomain, ⟨finitePolytopeFVApproximateIdentity_at L p y beta alpha
    hbeta0 hbeta hinterleave hp hy hlower hupper⟩⟩

end KernelSequence

/-! ## Concrete coefficient kernels and flow labels -/

section ConcreteKernel

variable {A : Type u} {P : Type v}
variable [Fintype A] [PartialOrder A] [Fintype P] [PartialOrder P]

/-- The manuscript's `p_n`, constructed from its displayed finite family of
coefficients.  Nonnegativity and total mass one are exactly the two elementary
measure-law obligations; no order or approximation property is bundled into
this definition. -/
noncomputable def finitePolytopeKernelOfWeights
    (L : Nat -> FinitePoset.{w})
    (weight : forall n, MonotoneTable A P -> L n -> Real)
    (hnonneg : forall n x l, 0 <= weight n x l)
    (htotal : forall n x, (∑ l, weight n x l) = 1)
    (n : Nat) : MonotoneTable A P -> ProbabilityVector (L n) :=
  probabilityKernelOfWeights (weight n) (hnonneg n) (htotal n)

@[simp]
theorem finitePolytopeKernelOfWeights_apply
    (L : Nat -> FinitePoset.{w})
    (weight : forall n, MonotoneTable A P -> L n -> Real)
    (hnonneg : forall n x l, 0 <= weight n x l)
    (htotal : forall n x, (∑ l, weight n x l) = 1)
    (n : Nat) (x : MonotoneTable A P) (l : L n) :
    finitePolytopeKernelOfWeights L weight hnonneg htotal n x l =
      weight n x l :=
  rfl

/-- Equation `eq:labels` at arbitrary source scales: apply the pointwise
erosion flow to the concrete finite grid table. -/
noncomputable def finitePolytopeGridLabelAt
    (L : Nat -> FinitePoset.{w})
    (grid : forall n, L n -> MonotoneTable A P)
    (labelTime : Nat -> Real)
    (n : Nat) (l : L n) : MonotoneTable A P :=
  Psi (labelTime n) (grid n l)

/-- Equation `eq:labels` specialized to the canonical interleaved scales. -/
noncomputable def finitePolytopeGridLabel
    (L : Nat -> FinitePoset.{w})
    (grid : forall n, L n -> MonotoneTable A P)
    (n : Nat) (l : L n) : MonotoneTable A P :=
  finitePolytopeGridLabelAt L grid finitePolytopeLabelTime n l

@[simp]
theorem finitePolytopeGridLabel_apply
    (L : Nat -> FinitePoset.{w})
    (grid : forall n, L n -> MonotoneTable A P)
    (n : Nat) (l : L n) (a : A) :
    finitePolytopeGridLabel L grid n l a =
      exactPhi (finitePolytopeLabelTime n) (grid n l a) :=
  rfl

@[simp]
theorem finitePolytopeGridLabelAt_apply
    (L : Nat -> FinitePoset.{w})
    (grid : forall n, L n -> MonotoneTable A P)
    (labelTime : Nat -> Real)
    (n : Nat) (l : L n) (a : A) :
    finitePolytopeGridLabelAt L grid labelTime n l a =
      exactPhi (labelTime n) (grid n l a) :=
  rfl

/-- The concrete label map is monotone whenever the finite grid embedding is
monotone in the cone-induced order. -/
theorem finitePolytopeGridLabel_mono
    (L : Nat -> FinitePoset.{w})
    (grid : forall n, L n -> MonotoneTable A P)
    (hgrid : forall n, Monotone (grid n)) (n : Nat) :
    Monotone (finitePolytopeGridLabel L grid n) :=
  (Psi_mono (finitePolytopeLabelTime n)).comp (hgrid n)

theorem finitePolytopeGridLabelAt_mono
    (L : Nat -> FinitePoset.{w})
    (grid : forall n, L n -> MonotoneTable A P)
    (labelTime : Nat -> Real)
    (hgrid : forall n, Monotone (grid n)) (n : Nat) :
    Monotone (finitePolytopeGridLabelAt L grid labelTime n) :=
  (Psi_mono (labelTime n)).comp (hgrid n)

/-- The source's flow-sandwich calculation isolated from the random law.
Coordinate error bounds for one supported grid point, together with the two
displayed scalar inequalities, imply the exact order sandwich for its
concrete label. -/
theorem gridLabel_sandwich_of_coordinate_error
    (x gridPoint : MonotoneTable A P)
    {beta labelTime alpha lowerError upperError : Real}
    (hbeta0 : 0 <= beta) (hlabel0 : 0 <= labelTime)
    (halpha0 : 0 <= alpha)
    (hlower : forall a U,
      x.upperCoordinate a U - lowerError <=
        gridPoint.upperCoordinate a U)
    (hupper : forall a U,
      gridPoint.upperCoordinate a U <=
        x.upperCoordinate a U + upperError)
    (hbeta : lowerError + erosionConstant (P := P) * labelTime <= beta)
    (hlabel : upperError + erosionConstant (P := P) * alpha <= labelTime) :
    Psi beta x <= Psi labelTime gridPoint ∧
      Psi labelTime gridPoint <= Psi alpha x := by
  constructor
  · intro a U
    have hxupper := (Psi_two_sided x a U hbeta0).2
    have hgridlower := (Psi_two_sided gridPoint a U hlabel0).1
    have hscalar :
        x.upperCoordinate a U - beta <=
          gridPoint.upperCoordinate a U -
            erosionConstant (P := P) * labelTime := by
      linarith [hlower a U]
    exact le_trans hxupper (le_trans (max_le_max hscalar le_rfl) hgridlower)
  · intro a U
    have hgridupper := (Psi_two_sided gridPoint a U hlabel0).2
    have hxlower := (Psi_two_sided x a U halpha0).1
    have hscalar :
        gridPoint.upperCoordinate a U - labelTime <=
          x.upperCoordinate a U - erosionConstant (P := P) * alpha := by
      linarith [hupper a U]
    exact le_trans hgridupper (le_trans (max_le_max hscalar le_rfl) hxlower)

end ConcreteKernel

/-! ## Source-facing closure using the audited external FS theorem -/

section SourceClosure

variable {A P : Type u}
variable [Fintype A] [PartialOrder A] [Fintype P] [PartialOrder P]

/-- `thm:finite-polytope`, reduced to the two standard analytic facts about
the concrete randomized rounding law and the support-wise geometric label
sandwich.  The domain premise has been discharged by the audited external
Gierz II-2.18 theorem; couplings and dominated-convergence continuity are
converted internally into Scott continuity, and all approximation/FVA fields
are then proved by `finitePolytopeFVApproximateIdentity`. -/
theorem finite_polytope_isFVA_of_rounding_interfaces
    (L : Nat -> FinitePoset.{u})
    (p : forall n, MonotoneTable A P -> ProbabilityVector (L n))
    (y : forall n, L n -> MonotoneTable A P)
    (hcouple : forall n x z, x <= z ->
      Nonempty (DiscreteMonotoneCoupling (p n x) (p n z)))
    (hseq : forall n, TableKernelSequentiallyContinuous (p n))
    (hy : forall n, Monotone (y n))
    (hlower : forall n x l, 0 < p n x l ->
      Psi (finitePolytopeBeta n) x <= y n l)
    (hupper : forall n x l, 0 < p n x l ->
      y n l <= Psi (finitePolytopeAlpha n) x) :
    IsFVA.{u, u} (MonotoneTable A P) := by
  let hp : forall n, AbramskyJung.Chapter2.ScottContinuous
      (fun x : MonotoneTable A P => (p n x).1) :=
    fun n => probabilityKernel_scottContinuous_of_couplings_of_sequential
      (p n) (hcouple n) (hseq n)
  exact finite_polytope_isFVA_of_kernel_sandwich L p y
    monotoneTable_isContinuousDcpo hp hy hlower hupper

/-- Parametric-scale version used by the manuscript's geometric epsilon
sequence. -/
theorem finite_polytope_isFVA_of_rounding_interfaces_at
    (beta alpha : Nat -> Real)
    (hbeta0 : forall n, 0 <= beta n)
    (hbeta : Tendsto beta atTop (nhds 0))
    (hinterleave : forall n, beta (n + 1) <= alpha n)
    (L : Nat -> FinitePoset.{u})
    (p : forall n, MonotoneTable A P -> ProbabilityVector (L n))
    (y : forall n, L n -> MonotoneTable A P)
    (hcouple : forall n x z, x <= z ->
      Nonempty (DiscreteMonotoneCoupling (p n x) (p n z)))
    (hseq : forall n, TableKernelSequentiallyContinuous (p n))
    (hy : forall n, Monotone (y n))
    (hlower : forall n x l, 0 < p n x l -> Psi (beta n) x <= y n l)
    (hupper : forall n x l, 0 < p n x l -> y n l <= Psi (alpha n) x) :
    IsFVA.{u, u} (MonotoneTable A P) := by
  let hp : forall n, AbramskyJung.Chapter2.ScottContinuous
      (fun x : MonotoneTable A P => (p n x).1) :=
    fun n => probabilityKernel_scottContinuous_of_couplings_of_sequential
      (p n) (hcouple n) (hseq n)
  exact finite_polytope_isFVA_of_kernel_sandwich_at L p y beta alpha
    hbeta0 hbeta hinterleave monotoneTable_isContinuousDcpo
    hp hy hlower hupper

/-- Fully displayed `p_n`/`y_n` version of the preceding theorem.  The
remaining hypotheses are exactly separated into:

1. nonnegativity and normalization of the rounding weights;
2. the order-supported coupling supplied by modulo-one invariance;
3. coefficient convergence supplied by the null-boundary/DCT argument; and
4. the support-wise geometric flow sandwich.

None of these hypotheses mentions monotonicity of `d_n`, its supremum,
factorability, FVA, or the final theorem. -/
theorem finite_polytope_isFVA_of_randomized_grid_weights
    (L : Nat -> FinitePoset.{u})
    (weight : forall n, MonotoneTable A P -> L n -> Real)
    (hnonneg : forall n x l, 0 <= weight n x l)
    (htotal : forall n x, (∑ l, weight n x l) = 1)
    (grid : forall n, L n -> MonotoneTable A P)
    (hgrid : forall n, Monotone (grid n))
    (hcouple : forall n x z, x <= z -> Nonempty
      (DiscreteMonotoneCoupling
        (finitePolytopeKernelOfWeights L weight hnonneg htotal n x)
        (finitePolytopeKernelOfWeights L weight hnonneg htotal n z)))
    (hseq : forall n, TableKernelSequentiallyContinuous
      (finitePolytopeKernelOfWeights L weight hnonneg htotal n))
    (hlower : forall n x l, 0 < weight n x l ->
      Psi (finitePolytopeBeta n) x <=
        finitePolytopeGridLabel L grid n l)
    (hupper : forall n x l, 0 < weight n x l ->
      finitePolytopeGridLabel L grid n l <=
        Psi (finitePolytopeAlpha n) x) :
    IsFVA.{u, u} (MonotoneTable A P) := by
  let p := finitePolytopeKernelOfWeights L weight hnonneg htotal
  let y := finitePolytopeGridLabel L grid
  apply finite_polytope_isFVA_of_rounding_interfaces L p y
    hcouple hseq (finitePolytopeGridLabel_mono L grid hgrid)
  · intro n x l hpos
    apply hlower n x l
    simpa [p] using hpos
  · intro n x l hpos
    apply hupper n x l
    simpa [p] using hpos

/-- Source-scale closure from raw coordinate error bounds.  This theorem
derives the label sandwich through `gridLabel_sandwich_of_coordinate_error`,
so the geometric premise no longer mentions the labelled maps or any
finite-kernel/FVA conclusion. -/
theorem finite_polytope_isFVA_of_randomized_grid_coordinate_errors
    (beta labelTime alpha : Nat -> Real)
    (hbeta0 : forall n, 0 <= beta n)
    (hlabel0 : forall n, 0 <= labelTime n)
    (halpha0 : forall n, 0 <= alpha n)
    (hbetaTendsto : Tendsto beta atTop (nhds 0))
    (hinterleave : forall n, beta (n + 1) <= alpha n)
    (L : Nat -> FinitePoset.{u})
    (weight : forall n, MonotoneTable A P -> L n -> Real)
    (hnonneg : forall n x l, 0 <= weight n x l)
    (htotal : forall n x, (∑ l, weight n x l) = 1)
    (grid : forall n, L n -> MonotoneTable A P)
    (hgrid : forall n, Monotone (grid n))
    (hcouple : forall n x z, x <= z -> Nonempty
      (DiscreteMonotoneCoupling
        (finitePolytopeKernelOfWeights L weight hnonneg htotal n x)
        (finitePolytopeKernelOfWeights L weight hnonneg htotal n z)))
    (hseq : forall n, TableKernelSequentiallyContinuous
      (finitePolytopeKernelOfWeights L weight hnonneg htotal n))
    (lowerError upperError : Nat -> Real)
    (hsupportLower : forall n x l, 0 < weight n x l -> forall a U,
      x.upperCoordinate a U - lowerError n <=
        (grid n l).upperCoordinate a U)
    (hsupportUpper : forall n x l, 0 < weight n x l -> forall a U,
      (grid n l).upperCoordinate a U <=
        x.upperCoordinate a U + upperError n)
    (hbetaScale : forall n,
      lowerError n + erosionConstant (P := P) * labelTime n <= beta n)
    (hlabelScale : forall n,
      upperError n + erosionConstant (P := P) * alpha n <= labelTime n) :
    IsFVA.{u, u} (MonotoneTable A P) := by
  let p := finitePolytopeKernelOfWeights L weight hnonneg htotal
  let y := finitePolytopeGridLabelAt L grid labelTime
  apply finite_polytope_isFVA_of_rounding_interfaces_at beta alpha
    hbeta0 hbetaTendsto hinterleave L p y hcouple hseq
    (finitePolytopeGridLabelAt_mono L grid labelTime hgrid)
  · intro n x l hpos
    have hwpos : 0 < weight n x l := by simpa [p] using hpos
    exact (gridLabel_sandwich_of_coordinate_error x (grid n l)
      (hbeta0 n) (hlabel0 n) (halpha0 n)
      (hsupportLower n x l hwpos) (hsupportUpper n x l hwpos)
      (hbetaScale n) (hlabelScale n)).1
  · intro n x l hpos
    have hwpos : 0 < weight n x l := by simpa [p] using hpos
    exact (gridLabel_sandwich_of_coordinate_error x (grid n l)
      (hbeta0 n) (hlabel0 n) (halpha0 n)
      (hsupportLower n x l hwpos) (hsupportUpper n x l hwpos)
      (hbetaScale n) (hlabelScale n)).2

end SourceClosure

end FiniteValuationApproximable
