import FiniteValuationApproximable.External.Jones

/-!
# The Jones continuous-valuation monad: derived API

The source-audited Jones integral, directed monotone convergence, and Kleisli
laws are exposed through `External/Jones.lean`, whose declarations are now
all internally proved.  Kernel monotonicity and directed kernel locality are
also proved below; no axiom is introduced here.
-/

set_option autoImplicit false

universe u v w

namespace FiniteValuationApproximable
namespace ContinuousValuation

open Set
open AbramskyJung.Chapter2
open scoped ENNReal

/-- Public name for the Jones integral boundary. -/
noncomputable def integral {D : Type u} [Preorder D]
    (μ : VSub D) (f : BoundedScottFunction D) : ℝ≥0∞ :=
  External.jonesIntegral μ f

@[simp] theorem integral_indicator {D : Type u} [Preorder D]
    (μ : VSub D) (U : ScottOpen D) :
    integral μ (BoundedScottFunction.indicator U) = μ U := by
  exact External.jonesIntegral_indicator μ U

theorem integral_mono {D : Type u} [Preorder D]
    (μ : VSub D) {f g : BoundedScottFunction D} (hfg : f ≤ g) :
    integral μ f ≤ integral μ g := by
  exact External.jonesIntegral_mono μ hfg

/-- Kleisli extension (bind) for continuous subprobability valuations. -/
noncomputable def bind
    {D : Type u} {E : Type v} [Preorder D] [Preorder E]
    (k : ScottContFun D (VSub E)) (μ : VSub D) : VSub E :=
  External.jonesKleisli k μ

@[simp] theorem bind_apply
    {D : Type u} {E : Type v} [Preorder D] [Preorder E]
    (k : ScottContFun D (VSub E)) (μ : VSub D) (U : ScottOpen E) :
    bind k μ U = integral μ (kernelSection k U) := by
  exact External.jonesKleisli_apply k μ U

/-- Bind by a fixed kernel is Scott-continuous in its input valuation. -/
theorem bind_scottContinuous_input
    {D : Type u} {E : Type v} [Preorder D] [Preorder E]
    (k : ScottContFun D (VSub E)) :
    AbramskyJung.Chapter2.ScottContinuous (bind k) := by
  exact External.jonesKleisli_scottContinuous_input k

theorem bind_mono_input
    {D : Type u} {E : Type v} [Preorder D] [Preorder E]
    (k : ScottContFun D (VSub E)) {μ ν : VSub D} (hμν : μ ≤ ν) :
    bind k μ ≤ bind k ν :=
  (bind_scottContinuous_input k).monotone hμν

/-- Evaluation sections inherit the pointwise order on kernels. -/
theorem kernelSection_mono_kernel
    {D : Type u} {E : Type v} [Preorder D] [Preorder E]
    {k l : ScottContFun D (VSub E)} (hkl : k ≤ l) (U : ScottOpen E) :
    kernelSection k U ≤ kernelSection l U :=
  fun x => hkl x U

/-- Kernel monotonicity is derived from the defining integral formula and
monotonicity of the Jones integral. -/
theorem bind_mono_kernel
    {D : Type u} {E : Type v} [Preorder D] [Preorder E]
    {k l : ScottContFun D (VSub E)} (hkl : k ≤ l) (μ : VSub D) :
    bind k μ ≤ bind l μ := by
  intro U
  rw [bind_apply, bind_apply]
  exact integral_mono μ (kernelSection_mono_kernel hkl U)

/-- A directed family of kernels induces a directed family of scalar
sections at every target Scott open. -/
theorem kernelSection_directed
    {D : Type u} {E : Type v} [Preorder D] [Preorder E]
    {A : Set (ScottContFun D (VSub E))} (hA : DirectedSet A)
    (U : ScottOpen E) :
    DirectedSet ((fun k : ScottContFun D (VSub E) =>
      kernelSection k U) '' A) :=
  hA.image (by
    intro k l hkl
    exact kernelSection_mono_kernel hkl U)

/-- Pointwise suprema of kernels are pointwise suprema of their scalar
sections.  The final evaluation step uses the internally proved pointwise
dcpo structure of `VSub`. -/
theorem kernelSection_pointwise_isSup
    {D : Type u} {E : Type v} [Preorder D] [Preorder E]
    {A : Set (ScottContFun D (VSub E))} (hA : DirectedSet A)
    (k : ScottContFun D (VSub E))
    (hk : ∀ x : D,
      IsSup ((fun l : ScottContFun D (VSub E) => l x) '' A) (k x))
    (U : ScottOpen E) (x : D) :
    IsSup
      ((fun f : BoundedScottFunction D => f x) ''
        ((fun l : ScottContFun D (VSub E) => kernelSection l U) '' A))
      (kernelSection k U x) := by
  have hEvalDir : DirectedSet
      ((fun l : ScottContFun D (VSub E) => l x) '' A) :=
    ScottContFun.eval_directed hA x
  have hMass := VSub.eval_isSup hEvalDir (hk x) U
  constructor
  · rintro _ ⟨_, ⟨l, hlA, rfl⟩, rfl⟩
    simpa only [kernelSection_apply] using
      hMass.1 ⟨l x, ⟨l, hlA, rfl⟩, rfl⟩
  · intro y hy
    exact hMass.2 y (by
      rintro _ ⟨_, ⟨l, hlA, rfl⟩, rfl⟩
      simpa only [kernelSection_apply] using
        hy ⟨kernelSection l U, ⟨l, hlA, rfl⟩, rfl⟩)

/-- Coordinate form of Kleisli locality.  This is exactly Jones's directed
monotone convergence theorem applied to the sections `x ↦ k x U`. -/
theorem bind_eval_isSup
    {D : Type u} {E : Type v} [Preorder D] [Preorder E]
    {A : Set (ScottContFun D (VSub E))} (hA : DirectedSet A)
    (k : ScottContFun D (VSub E))
    (hk : ∀ x : D,
      IsSup ((fun l : ScottContFun D (VSub E) => l x) '' A) (k x))
    (μ : VSub D) (U : ScottOpen E) :
    IsSup ((fun l : ScottContFun D (VSub E) => bind l μ U) '' A)
      (bind k μ U) := by
  have hDMC := External.jones_1990_thm_3_13_DMC
    (kernelSection_directed hA U) (kernelSection k U)
    (kernelSection_pointwise_isSup hA k hk U) μ
  simpa only [Set.image_image, Function.comp_apply, bind, integral,
    External.jonesKleisli_apply] using hDMC

/-- Kleisli-locality for a directed pointwise supremum of valuation kernels.
This is a derived theorem, not an external boundary. -/
theorem bind_local
    {D : Type u} {E : Type v} [Preorder D] [Preorder E]
    {A : Set (ScottContFun D (VSub E))} (hA : DirectedSet A)
    (k : ScottContFun D (VSub E))
    (hk : ∀ x : D,
      IsSup ((fun l : ScottContFun D (VSub E) => l x) '' A) (k x))
    (μ : VSub D) :
    IsSup ((fun l : ScottContFun D (VSub E) => bind l μ) '' A)
      (bind k μ) := by
  have hBindDir : DirectedSet
      ((fun l : ScottContFun D (VSub E) => bind l μ) '' A) :=
    hA.image (by
      intro l m hlm
      exact bind_mono_kernel hlm μ)
  apply VSub.isSup_of_pointwise hBindDir
  intro U
  have hEval := bind_eval_isSup hA k hk μ U
  constructor
  · rintro _ ⟨_, ⟨l, hlA, rfl⟩, rfl⟩
    exact hEval.1 ⟨l, hlA, rfl⟩
  · intro y hy
    exact hEval.2 y (by
      rintro _ ⟨l, hlA, rfl⟩
      exact hy ⟨bind l μ, ⟨l, hlA, rfl⟩, rfl⟩)

@[simp] theorem bind_dirac
    {D : Type u} {E : Type v} [Preorder D] [Preorder E]
    (k : ScottContFun D (VSub E)) (x : D) :
    bind k (dirac x) = k x := by
  exact External.jonesKleisli_dirac k x

@[simp] theorem bind_unit
    {D : Type u} [Preorder D] (μ : VSub D) :
    bind (unit (D := D)) μ = μ := by
  exact External.jonesKleisli_unit μ

/-- Jones Kleisli composition, exposed without strengthening its source
boundary. -/
noncomputable def kleisliCompose
    {D : Type u} {E : Type v} {F : Type w}
    [Preorder D] [Preorder E] [Preorder F]
    (k : ScottContFun D (VSub E)) (l : ScottContFun E (VSub F)) :
    ScottContFun D (VSub F) :=
  External.jonesKleisliCompose k l

@[simp] theorem kleisliCompose_apply
    {D : Type u} {E : Type v} {F : Type w}
    [Preorder D] [Preorder E] [Preorder F]
    (k : ScottContFun D (VSub E)) (l : ScottContFun E (VSub F)) (x : D) :
    kleisliCompose k l x = bind l (k x) := rfl

theorem bind_assoc
    {D : Type u} {E : Type v} {F : Type w}
    [Preorder D] [Preorder E] [Preorder F]
    (k : ScottContFun D (VSub E)) (l : ScottContFun E (VSub F))
    (μ : VSub D) :
    bind l (bind k μ) = bind (kleisliCompose k l) μ := by
  exact External.jonesKleisli_assoc k l μ

/-- Functorial pushforward factors through the Kleisli extension of
`unit ∘ f`; this is the final law of Jones (1990), Theorem 4.5. -/
theorem bind_unit_comp_eq_pushforward
    {D : Type u} {E : Type v} [Preorder D] [Preorder E]
    (f : ScottContFun D E) (μ : VSub D) :
    bind (ScottContFun.comp (unit (D := E)) f) μ = pushforward f μ := by
  exact External.jonesKleisli_unit_comp_eq_pushforward f μ

/-- Identity-specialized Kleisli locality.  The upper-bound half follows from
derived kernel monotonicity; the supremum half follows from `bind_local` and
the Jones unit law. -/
theorem bind_local_unit
    {D : Type u} [Preorder D]
    {A : Set (ScottContFun D (VSub D))} (hA : DirectedSet A)
    (hBelow : ∀ l ∈ A, l ≤ unit (D := D))
    (hSup : ∀ x : D,
      IsSup ((fun l : ScottContFun D (VSub D) => l x) '' A)
        (unit (D := D) x))
    (μ : VSub D) :
    (∀ l ∈ A, bind l μ ≤ μ) ∧
      IsSup ((fun l : ScottContFun D (VSub D) => bind l μ) '' A) μ := by
  constructor
  · intro l hlA
    calc
      bind l μ ≤ bind (unit (D := D)) μ :=
        bind_mono_kernel (hBelow l hlA) μ
      _ = μ := bind_unit μ
  · simpa only [bind_unit] using
      bind_local hA (unit (D := D)) hSup μ

end ContinuousValuation
end FiniteValuationApproximable
