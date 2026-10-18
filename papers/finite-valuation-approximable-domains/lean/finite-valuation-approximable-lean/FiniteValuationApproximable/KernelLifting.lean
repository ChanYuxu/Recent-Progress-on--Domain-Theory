import FiniteValuationApproximable.ContinuousValuation.Monad
import FiniteValuationApproximable.ContinuousValuation.Finite
import FiniteValuationApproximable.ContinuousValuation.VOneRetract
import FiniteValuationApproximable.ContinuousValuation.Transport
import FiniteValuationApproximable.Abstract.FSClass
import FiniteValuationApproximable.Abstract.Saturation
import FiniteValuationApproximable.External.Gierz

/-!
# Lifting finite probability kernels to continuous valuations

This module formalizes source theorem `thm:kernel-lifting` from
`main (17).tex`.  The construction uses the genuine Jones--Plotkin
continuous-valuation types.  In particular, the intermediate object in the
valuation clause is the actual `ContinuousValuation.VSub L`, transported to
the manuscript's finite-vector stage only through the proved order
isomorphism `ContinuousValuation.finiteVSubOrderIso`.
-/

set_option autoImplicit false
set_option linter.unnecessarySimpa false

universe u

namespace FiniteValuationApproximable

open Set
open AbstractApproximation

/-! ## The finite kernel and its Kleisli extension -/

section Kernel

variable {X : Type u} [PartialOrder X]

/-- Forget normalization in a Scott-continuous probability kernel. -/
def probabilityKernelToVSub (L : FinitePoset.{u})
    (p : ScottContFun X (ContinuousValuation.VOne L)) :
    ScottContFun X (ContinuousValuation.VSub L) where
  toFun x := ContinuousValuation.VOne.toVSub (p x)
  continuous :=
    ContinuousValuation.vOneInclusion_scottContinuous.comp p.continuous

/-- The source kernel
`kappa = VOne(y) p`, represented in the subprobability monad.  Defining it as
the corresponding Kleisli composite makes its later factorization an exact
instance of associativity. -/
noncomputable def continuousFiniteKernel
    (L : FinitePoset.{u})
    (p : ScottContFun X (ContinuousValuation.VOne L))
    (y : ScottContFun L X) :
    ScottContFun X (ContinuousValuation.VSub X) :=
  ContinuousValuation.kleisliCompose
    (probabilityKernelToVSub L p)
    (AbramskyJung.Chapter2.ScottContFun.comp
      (ContinuousValuation.unit (D := X)) y)

/-- Pointwise, `finiteProbabilityKernel` is exactly pushforward of the
finite probability law along the label map. -/
@[simp]
theorem continuousFiniteKernel_apply
    (L : FinitePoset.{u})
    (p : ScottContFun X (ContinuousValuation.VOne L))
    (y : ScottContFun L X) (x : X) :
    continuousFiniteKernel L p y x =
      ContinuousValuation.pushforward y
        (ContinuousValuation.VOne.toVSub (p x)) := by
  rw [continuousFiniteKernel,
    ContinuousValuation.kleisliCompose_apply,
    ContinuousValuation.bind_unit_comp_eq_pushforward]
  rfl

/-- Reusable source data for a finite probability-kernel approximation of
the Dirac unit.  Concrete finite-polytope constructions can export these six
fields without depending on either lifting conclusion. -/
structure FiniteKernelApproximation (X : Type u) [PartialOrder X] where
  stage : Nat -> FinitePoset.{u}
  probability : forall n,
    ScottContFun X (ContinuousValuation.VOne (stage n))
  label : forall n, ScottContFun (stage n) X
  kernel_mono : Monotone
    (fun n => continuousFiniteKernel (stage n) (probability n) (label n))
  kernel_below_unit : forall n,
    continuousFiniteKernel (stage n) (probability n) (label n) <=
      ContinuousValuation.unit (D := X)
  kernel_pointwise_sup_unit : forall x,
    IsSup
      (Set.range
        (fun n => continuousFiniteKernel (stage n) (probability n) (label n) x))
      (ContinuousValuation.unit (D := X) x)

/-- `T = kappa^dagger`, the endomap of the genuine continuous-valuation
powerdomain used in part (i) of `thm:kernel-lifting`. -/
noncomputable def liftedValuationMap
    (L : FinitePoset.{u})
    (p : ScottContFun X (ContinuousValuation.VOne L))
    (y : ScottContFun L X) :
    ScottContFun (ContinuousValuation.VSub X)
      (ContinuousValuation.VSub X) where
  toFun := ContinuousValuation.bind (continuousFiniteKernel L p y)
  continuous :=
    ContinuousValuation.bind_scottContinuous_input
      (continuousFiniteKernel L p y)

/-- Kleisli associativity factors `T` through the actual valuation space
`VSub L`; the proved finite-poset order isomorphism then transports that
factorization to the concrete finite-vector stage required by `IsFVA`. -/
noncomputable def liftedValuationMapFactorization
    (L : FinitePoset.{u})
    (p : ScottContFun X (ContinuousValuation.VOne L))
    (y : ScottContFun L X) :
    FiniteValuationFactorization.{u, u, u}
      (liftedValuationMap L p y) where
  stage := L
  factorization := {
    encode := fun mu =>
      (ContinuousValuation.finiteVSubOrderIso (P := L)).symm
        (ContinuousValuation.bind (probabilityKernelToVSub L p) mu)
    decode := fun v =>
      ContinuousValuation.pushforward y
        (ContinuousValuation.finiteVSubOrderIso (P := L) v)
    encode_continuous :=
      (fsOrderIso_scottContinuous
        (ContinuousValuation.finiteVSubOrderIso (P := L)).symm).comp
          (ContinuousValuation.bind_scottContinuous_input
            (probabilityKernelToVSub L p))
    decode_continuous :=
      (ContinuousValuation.pushforward_scottContinuous y).comp
        (fsOrderIso_scottContinuous
          (ContinuousValuation.finiteVSubOrderIso (P := L)))
    factor := by
      intro mu
      simp only [OrderIso.apply_symm_apply]
      rw [← ContinuousValuation.bind_unit_comp_eq_pushforward y]
      simpa [liftedValuationMap, continuousFiniteKernel] using
        ContinuousValuation.bind_assoc
        (probabilityKernelToVSub L p)
        (AbramskyJung.Chapter2.ScottContFun.comp
          (ContinuousValuation.unit (D := X)) y) mu }

end Kernel

/-! ## Part (i): `VSub X` is FVA -/

section ValuationLifting

variable {X : Type u} [PartialOrder X]

/-- The continuous-domain component for `VSub X`: directed completeness is
internal, while preservation of continuous domains is precisely the audited
Jones (1990), Corollary 5.4 boundary. -/
theorem vSub_isContinuousDcpo_of_isFSDomain (hX : IsFSDomain X) :
    AbramskyJung.Chapter2.IsContinuousDcpo
      (ContinuousValuation.VSub X) :=
  ⟨ContinuousValuation.VSub.isDcpoOrder,
    External.jones_1990_cor_5_4_vSub_continuous hX.isContinuousDcpo⟩

/-- The Kleisli extensions of an increasing finite-kernel approximation form
an increasing approximate identity on the genuine `VSub X`. -/
noncomputable def liftedValuationIncreasingApproximateIdentity
    (L : Nat -> FinitePoset.{u})
    (p : forall n, ScottContFun X (ContinuousValuation.VOne (L n)))
    (y : forall n, ScottContFun (L n) X)
    (hkappaMono : Monotone (fun n => continuousFiniteKernel (L n) (p n) (y n)))
    (hkappaBelow : forall n,
      continuousFiniteKernel (L n) (p n) (y n) <=
        ContinuousValuation.unit (D := X))
    (hkappaSup : forall x,
      IsSup (Set.range (fun n => continuousFiniteKernel (L n) (p n) (y n) x))
        (ContinuousValuation.unit (D := X) x)) :
    IncreasingApproximateIdentity (ContinuousValuation.VSub X) where
  map n := liftedValuationMap (L n) (p n) (y n)
  monotone := by
    intro m n hmn mu
    exact ContinuousValuation.bind_mono_kernel (hkappaMono hmn) mu
  below_id := by
    intro n mu
    calc
      liftedValuationMap (L n) (p n) (y n) mu <=
          ContinuousValuation.bind (ContinuousValuation.unit (D := X)) mu :=
        ContinuousValuation.bind_mono_kernel (hkappaBelow n) mu
      _ = mu := ContinuousValuation.bind_unit mu
  pointwise_sup := by
    intro mu
    let K : Nat -> ScottContFun X (ContinuousValuation.VSub X) :=
      fun n => continuousFiniteKernel (L n) (p n) (y n)
    have hKmono : Monotone K := hkappaMono
    have hKdir : DirectedSet (Set.range K) :=
      directedSet_range_of_monotone K hKmono
    have hKbelow : forall k, k ∈ Set.range K ->
        k <= ContinuousValuation.unit (D := X) := by
      intro k hk
      rcases hk with ⟨n, rfl⟩
      exact hkappaBelow n
    have hKsup (x : X) :
        IsSup
          ((fun k : ScottContFun X (ContinuousValuation.VSub X) => k x) ''
            Set.range K)
          (ContinuousValuation.unit (D := X) x) := by
      have hevalRange :
          ((fun k : ScottContFun X (ContinuousValuation.VSub X) => k x) ''
              Set.range K) =
            Set.range (fun n => K n x) := by
        ext z
        constructor
        · rintro ⟨k, ⟨n, rfl⟩, rfl⟩
          exact ⟨n, rfl⟩
        · rintro ⟨n, rfl⟩
          exact ⟨K n, ⟨n, rfl⟩, rfl⟩
      rw [hevalRange]
      simpa [K] using hkappaSup x
    have hlocal := ContinuousValuation.bind_local_unit
      hKdir hKbelow hKsup mu
    have hbindRange :
        Set.range (fun n => liftedValuationMap (L n) (p n) (y n) mu) =
          ((fun k : ScottContFun X (ContinuousValuation.VSub X) =>
              ContinuousValuation.bind k mu) '' Set.range K) := by
      ext nu
      constructor
      · rintro ⟨n, rfl⟩
        exact ⟨K n, ⟨n, rfl⟩, rfl⟩
      · rintro ⟨k, ⟨n, rfl⟩, rfl⟩
        exact ⟨n, rfl⟩
    rw [hbindRange]
    exact hlocal.2

/-- The approximate identity from the preceding theorem factors stagewise
through the concrete finite valuation vectors, with no replacement of the
actual continuous-valuation monad by a finite surrogate. -/
noncomputable def liftedValuationFVApproximateIdentity
    (L : Nat -> FinitePoset.{u})
    (p : forall n, ScottContFun X (ContinuousValuation.VOne (L n)))
    (y : forall n, ScottContFun (L n) X)
    (hkappaMono : Monotone (fun n => continuousFiniteKernel (L n) (p n) (y n)))
    (hkappaBelow : forall n,
      continuousFiniteKernel (L n) (p n) (y n) <=
        ContinuousValuation.unit (D := X))
    (hkappaSup : forall x,
      IsSup (Set.range (fun n => continuousFiniteKernel (L n) (p n) (y n) x))
        (ContinuousValuation.unit (D := X) x)) :
    FVApproximateIdentity.{u, u} (ContinuousValuation.VSub X) where
  toIncreasingApproximateIdentity :=
    liftedValuationIncreasingApproximateIdentity L p y
      hkappaMono hkappaBelow hkappaSup
  factorable := fun n =>
    ⟨liftedValuationMapFactorization (L n) (p n) (y n)⟩

/-- Part (i) of source theorem `thm:kernel-lifting`: a finite probability
kernel approximation of the Dirac unit on an FS-domain lifts to an actual
finite-valuation approximation of `VSub X`. -/
theorem kernel_lifting_vSub_isFVA
    (hX : IsFSDomain X)
    (L : Nat -> FinitePoset.{u})
    (p : forall n, ScottContFun X (ContinuousValuation.VOne (L n)))
    (y : forall n, ScottContFun (L n) X)
    (hkappaMono : Monotone (fun n => continuousFiniteKernel (L n) (p n) (y n)))
    (hkappaBelow : forall n,
      continuousFiniteKernel (L n) (p n) (y n) <=
        ContinuousValuation.unit (D := X))
    (hkappaSup : forall x,
      IsSup (Set.range (fun n => continuousFiniteKernel (L n) (p n) (y n) x))
        (ContinuousValuation.unit (D := X) x)) :
    IsFVA.{u, u} (ContinuousValuation.VSub X) :=
  ⟨vSub_isContinuousDcpo_of_isFSDomain hX,
    ⟨liftedValuationFVApproximateIdentity L p y
      hkappaMono hkappaBelow hkappaSup⟩⟩

/-- Bundled form of part (i). -/
theorem kernel_lifting_vSub_isFVA_of_approximation
    (hX : IsFSDomain X) (K : FiniteKernelApproximation X) :
    IsFVA.{u, u} (ContinuousValuation.VSub X) :=
  kernel_lifting_vSub_isFVA hX K.stage K.probability K.label
    K.kernel_mono K.kernel_below_unit K.kernel_pointwise_sup_unit

end ValuationLifting

/-! ## Part (ii): continuous functions into `VSub P` -/

section FunctionLifting

variable {X : Type u} [PartialOrder X]

/-- Finite monotone tables, whose rows are atomic vectors, are order
isomorphic to genuine continuous-valuation kernels on the finite source. -/
noncomputable def continuousValuationTableOrderIso
    (A P : FinitePoset.{u}) :
    MonotoneTable A P ≃o
      AbramskyJung.Chapter3.ContFun A (ContinuousValuation.VSub P) :=
  (monotoneTableOrderIsoContFun (A := A) (P := P)).trans
    (contFunOrderIso (OrderIso.refl A)
      (ContinuousValuation.finiteVSubOrderIso (P := P)))

/-- Kleisli postcomposition by a fixed input kernel is Scott-continuous in
the output kernel.  This is the function-space form of Jones locality. -/
theorem kleisliPostcompose_scottContinuous
    {D E F : Type u} [Preorder D] [Preorder E] [Preorder F]
    (q : ScottContFun D (ContinuousValuation.VSub E)) :
    AbramskyJung.Chapter2.ScottContinuous
      (fun k : ScottContFun E (ContinuousValuation.VSub F) =>
        ContinuousValuation.kleisliCompose q k) := by
  constructor
  · intro k l hkl x
    exact ContinuousValuation.bind_mono_kernel hkl (q x)
  · intro K s hK hs
    constructor
    · rintro _ ⟨k, hk, rfl⟩ x
      exact ContinuousValuation.bind_mono_kernel (hs.1 hk) (q x)
    · intro g hg x
      have hpoint (e : E) :
          IsSup
            ((fun k : ScottContFun E (ContinuousValuation.VSub F) => k e) '' K)
            (s e) :=
        (AbramskyJung.Chapter3.ContFun.eval_scottContinuous
          ContinuousValuation.VSub.isDcpo e).maps_isSup hK hs
      have hlocal := ContinuousValuation.bind_local hK s hpoint (q x)
      apply hlocal.2 (g x)
      rintro _ ⟨k, hk, rfl⟩
      exact hg ⟨k, hk, rfl⟩ x

/-- Sampling a continuous valuation-valued function on the finite label set,
expressed in the manuscript's atomic table representation. -/
noncomputable def sampleFiniteKernelFunctionMap
    (L P : FinitePoset.{u}) (y : ScottContFun L X) :
    ScottContFun
      (AbramskyJung.Chapter3.ContFun X (ContinuousValuation.VSub P))
      (MonotoneTable L P) where
  toFun f := (continuousValuationTableOrderIso L P).symm
    (AbramskyJung.Chapter3.ContFun.comp f y)
  continuous :=
    (fsOrderIso_scottContinuous
      (continuousValuationTableOrderIso L P).symm).comp
        (precomposeContFun_scottContinuous
          (C := ContinuousValuation.VSub P)
          ContinuousValuation.VSub.isDcpo y)

/-- Reconstruction evaluates a sampled finite kernel against the probability
kernel `p`. -/
noncomputable def reconstructFiniteKernelFunctionMap
    (L P : FinitePoset.{u})
    (p : ScottContFun X (ContinuousValuation.VOne L)) :
    ScottContFun (MonotoneTable L P)
      (AbramskyJung.Chapter3.ContFun X (ContinuousValuation.VSub P)) where
  toFun v := ContinuousValuation.kleisliCompose
    (probabilityKernelToVSub L p)
    (continuousValuationTableOrderIso L P v)
  continuous :=
    (kleisliPostcompose_scottContinuous
      (F := P) (probabilityKernelToVSub L p)).comp
        (fsOrderIso_scottContinuous
          (continuousValuationTableOrderIso L P))

/-- The manuscript's function-space approximant
`A_n(f)(x) = f^dagger(kappa_n(x))`. -/
noncomputable def functionKernelApproximant
    (L P : FinitePoset.{u})
    (p : ScottContFun X (ContinuousValuation.VOne L))
    (y : ScottContFun L X) :
    ScottContFun
      (AbramskyJung.Chapter3.ContFun X (ContinuousValuation.VSub P))
      (AbramskyJung.Chapter3.ContFun X (ContinuousValuation.VSub P)) :=
  AbramskyJung.Chapter2.ScottContFun.comp
    (reconstructFiniteKernelFunctionMap L P p)
    (sampleFiniteKernelFunctionMap L P y)

@[simp]
theorem functionKernelApproximant_apply
    (L P : FinitePoset.{u})
    (p : ScottContFun X (ContinuousValuation.VOne L))
    (y : ScottContFun L X)
    (f : AbramskyJung.Chapter3.ContFun X (ContinuousValuation.VSub P))
    (x : X) :
    functionKernelApproximant L P p y f x =
      ContinuousValuation.bind f (continuousFiniteKernel L p y x) := by
  change ContinuousValuation.bind
      (continuousValuationTableOrderIso L P
        ((continuousValuationTableOrderIso L P).symm
          (AbramskyJung.Chapter3.ContFun.comp f y)))
      (probabilityKernelToVSub L p x) = _
  rw [OrderIso.apply_symm_apply, continuousFiniteKernel_apply,
    ← ContinuousValuation.bind_unit_comp_eq_pushforward y,
    ContinuousValuation.bind_assoc]
  congr 1
  apply AbramskyJung.Chapter3.ContFun.ext_apply
  intro l
  change f (y l) = ContinuousValuation.bind f
    (ContinuousValuation.dirac (y l))
  exact (ContinuousValuation.bind_dirac f (y l)).symm

/-- The function-space approximants inherit monotonicity, boundedness by the
identity, and convergence from the underlying finite probability kernels. -/
noncomputable def functionKernelIncreasingApproximateIdentity
    (P : FinitePoset.{u})
    (L : Nat -> FinitePoset.{u})
    (p : forall n, ScottContFun X (ContinuousValuation.VOne (L n)))
    (y : forall n, ScottContFun (L n) X)
    (hkappaMono : Monotone (fun n => continuousFiniteKernel (L n) (p n) (y n)))
    (hkappaBelow : forall n,
      continuousFiniteKernel (L n) (p n) (y n) <=
        ContinuousValuation.unit (D := X))
    (hkappaSup : forall x,
      IsSup (Set.range (fun n => continuousFiniteKernel (L n) (p n) (y n) x))
        (ContinuousValuation.unit (D := X) x)) :
    IncreasingApproximateIdentity
      (AbramskyJung.Chapter3.ContFun X (ContinuousValuation.VSub P)) where
  map n := functionKernelApproximant (L n) P (p n) (y n)
  monotone := by
    intro m n hmn f x
    rw [functionKernelApproximant_apply,
      functionKernelApproximant_apply]
    exact ContinuousValuation.bind_mono_input f (hkappaMono hmn x)
  below_id := by
    intro n f x
    rw [functionKernelApproximant_apply]
    calc
      ContinuousValuation.bind f
          (continuousFiniteKernel (L n) (p n) (y n) x) <=
          ContinuousValuation.bind f
            (ContinuousValuation.unit (D := X) x) :=
        ContinuousValuation.bind_mono_input f (hkappaBelow n x)
      _ = f x := by
        change ContinuousValuation.bind f (ContinuousValuation.dirac x) = f x
        exact ContinuousValuation.bind_dirac f x
  pointwise_sup := by
    intro f
    constructor
    · rintro _ ⟨n, rfl⟩ x
      rw [functionKernelApproximant_apply]
      calc
        ContinuousValuation.bind f
            (continuousFiniteKernel (L n) (p n) (y n) x) <=
            ContinuousValuation.bind f
              (ContinuousValuation.unit (D := X) x) :=
          ContinuousValuation.bind_mono_input f (hkappaBelow n x)
        _ = f x := by
          change ContinuousValuation.bind f (ContinuousValuation.dirac x) = f x
          exact ContinuousValuation.bind_dirac f x
    · intro g hg x
      have hKdir : DirectedSet
          (Set.range
            (fun n => continuousFiniteKernel (L n) (p n) (y n) x)) :=
        directedSet_range_of_monotone _
          (fun _m _n hmn => hkappaMono hmn x)
      have hbindSup :=
        (ContinuousValuation.bind_scottContinuous_input f).maps_isSup
          hKdir (hkappaSup x)
      have hleast :
          ContinuousValuation.bind f
              (ContinuousValuation.unit (D := X) x) <= g x := by
        apply hbindSup.2 (g x)
        rintro _ ⟨mu, ⟨n, rfl⟩, rfl⟩
        have hn := hg ⟨n, rfl⟩ x
        simpa only [functionKernelApproximant_apply] using hn
      calc
        f x = ContinuousValuation.bind f
            (ContinuousValuation.dirac x) :=
          (ContinuousValuation.bind_dirac f x).symm
        _ = ContinuousValuation.bind f
            (ContinuousValuation.unit (D := X) x) := rfl
        _ <= g x := hleast

/-- At stage `n`, the function approximant factors through the FVA table
`M(L_n,P)` by sampling and Kleisli reconstruction. -/
noncomputable def functionKernelIntermediateFactorization
    (L P : FinitePoset.{u})
    (p : ScottContFun X (ContinuousValuation.VOne L))
    (y : ScottContFun L X)
    (hTableFVA : IsFVA.{u, u} (MonotoneTable L P)) :
    FVAIntermediateFactorization.{u, u}
      (functionKernelApproximant L P p y) where
  stage := {
    carrier := MonotoneTable L P
    partialOrder := inferInstance
    isFVA := hTableFVA }
  factorization := {
    encode := sampleFiniteKernelFunctionMap L P y
    decode := reconstructFiniteKernelFunctionMap L P p
    encode_continuous := (sampleFiniteKernelFunctionMap L P y).continuous
    decode_continuous := (reconstructFiniteKernelFunctionMap L P p).continuous
    factor := fun _ => rfl }

/-- The function-space kernel approximation, retaining exactly the one
finite-polytope input needed at every sampled table stage. -/
noncomputable def functionKernelIntermediateApproximateIdentity
    (P : FinitePoset.{u})
    (L : Nat -> FinitePoset.{u})
    (p : forall n, ScottContFun X (ContinuousValuation.VOne (L n)))
    (y : forall n, ScottContFun (L n) X)
    (hkappaMono : Monotone (fun n => continuousFiniteKernel (L n) (p n) (y n)))
    (hkappaBelow : forall n,
      continuousFiniteKernel (L n) (p n) (y n) <=
        ContinuousValuation.unit (D := X))
    (hkappaSup : forall x,
      IsSup (Set.range (fun n => continuousFiniteKernel (L n) (p n) (y n) x))
        (ContinuousValuation.unit (D := X) x))
    (hTableFVA : forall n, IsFVA.{u, u} (MonotoneTable (L n) P)) :
    FVAIntermediateApproximateIdentity.{u, u}
      (AbramskyJung.Chapter3.ContFun X (ContinuousValuation.VSub P)) where
  toIncreasingApproximateIdentity :=
    functionKernelIncreasingApproximateIdentity P L p y
      hkappaMono hkappaBelow hkappaSup
  factorable := fun n =>
    ⟨functionKernelIntermediateFactorization
      (L n) P (p n) (y n) (hTableFVA n)⟩

/-- Genuine valuations on a finite poset are an FS-domain, by transport from
the internally constructed finite atomic simplex. -/
theorem finiteVSub_isFSDomain (P : FinitePoset.{u}) :
    IsFSDomain (ContinuousValuation.VSub P) := by
  apply IsFSDomain.of_orderIso
    (ContinuousValuation.finiteVSubOrderIso (P := P)).symm
  exact Erosion.finiteSubprobability_isFSDomain (P := P)

/-- Part (ii), with its finite-table input shown explicitly.  The source
theorem is obtained below by discharging this input with
`finite_monotone_table_isFVA`. -/
theorem kernel_lifting_function_isFVA_of_table
    (hX : IsFSDomain X)
    (P : FinitePoset.{u})
    (L : Nat -> FinitePoset.{u})
    (p : forall n, ScottContFun X (ContinuousValuation.VOne (L n)))
    (y : forall n, ScottContFun (L n) X)
    (hkappaMono : Monotone (fun n => continuousFiniteKernel (L n) (p n) (y n)))
    (hkappaBelow : forall n,
      continuousFiniteKernel (L n) (p n) (y n) <=
        ContinuousValuation.unit (D := X))
    (hkappaSup : forall x,
      IsSup (Set.range (fun n => continuousFiniteKernel (L n) (p n) (y n) x))
        (ContinuousValuation.unit (D := X) x))
    (hTableFVA : forall n, IsFVA.{u, u} (MonotoneTable (L n) P)) :
    IsFVA.{u, u}
      (AbramskyJung.Chapter3.ContFun X (ContinuousValuation.VSub P)) := by
  let intermediate := functionKernelIntermediateApproximateIdentity
    P L p y hkappaMono hkappaBelow hkappaSup hTableFVA
  have hFunctionFS : IsFSDomain
      (AbramskyJung.Chapter3.ContFun X (ContinuousValuation.VSub P)) :=
    External.gierz_II_2_18_fs_exponential hX (finiteVSub_isFSDomain P)
  have hFunctionDomain := hFunctionFS.isContinuousDcpo
  exact ⟨hFunctionDomain,
    FVAIntermediateApproximateIdentity.flatten
      intermediate finiteStagesHaveFSApproximateIdentities
        hFunctionDomain.hasBasis⟩

/-- Bundled form of part (ii), still exposing only the finite-table theorem
that belongs to the independent finite-polytope development. -/
theorem kernel_lifting_function_isFVA_of_table_approximation
    (hX : IsFSDomain X) (K : FiniteKernelApproximation X)
    (P : FinitePoset.{u})
    (hTableFVA : forall n,
      IsFVA.{u, u} (MonotoneTable (K.stage n) P)) :
    IsFVA.{u, u}
      (AbramskyJung.Chapter3.ContFun X (ContinuousValuation.VSub P)) :=
  kernel_lifting_function_isFVA_of_table hX P
    K.stage K.probability K.label K.kernel_mono
      K.kernel_below_unit K.kernel_pointwise_sup_unit hTableFVA

/-- Both clauses of source theorem `thm:kernel-lifting`, at one finite target
`P`, from the shared bundled kernel data. -/
theorem kernel_lifting_of_approximation
    (hX : IsFSDomain X) (K : FiniteKernelApproximation X)
    (P : FinitePoset.{u})
    (hTableFVA : forall n,
      IsFVA.{u, u} (MonotoneTable (K.stage n) P)) :
    IsFVA.{u, u} (ContinuousValuation.VSub X) ∧
      IsFVA.{u, u}
        (AbramskyJung.Chapter3.ContFun X (ContinuousValuation.VSub P)) :=
  ⟨kernel_lifting_vSub_isFVA_of_approximation hX K,
    kernel_lifting_function_isFVA_of_table_approximation
      hX K P hTableFVA⟩

end FunctionLifting

end FiniteValuationApproximable
