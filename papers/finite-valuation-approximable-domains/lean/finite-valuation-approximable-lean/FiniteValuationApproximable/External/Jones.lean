import FiniteValuationApproximable.ContinuousValuation.JonesContinuity

/-!
# Internally proved Jones--Plotkin/Jones source API

This module retains source-facing names for results and constructions from
the original continuous-valuation literature.  Every declaration is now an
alias or theorem over the internal implementation; the module introduces no
axiom.  In particular, it does **not** assume the manuscript's kernel-lifting
theorem, any FVA closure theorem, the global transfer theorem, or the main
Jung--Tix theorem.

Primary sources checked against the scans:

* C. Jones and G. D. Plotkin, *A Probabilistic Powerdomain of Evaluations*,
  LICS 1989, pp. 186--195: Theorem 2.1 (printed p. 187), Theorems 3.1 and
  3.3 (printed p. 188), and the Kleisli construction in Section 4
  (printed pp. 188--189).
* C. Jones, *Probabilistic Non-determinism*, PhD thesis / LFCS Report
  ECS-LFCS-90-105, 1990: Directed Monotone Convergence, Theorem 3.13
  (printed p. 54); functorial pushforward, Theorem 4.3 (printed p. 69);
  the Kleisli triple/monad laws, Theorem 4.5 (printed pp. 71--72); and
  preservation of continuous ipos, Corollary 5.4 (printed p. 95).

Pushforward, its Scott continuity, pointwise directed suprema of valuations,
Dirac continuity, and `lem:V-local` are proved internally in
`ContinuousValuation/Basic.lean`, so no external constant is introduced for
those facts.
-/

set_option autoImplicit false

universe u v w

namespace FiniteValuationApproximable
namespace External

open scoped ENNReal
open AbramskyJung.Chapter2
open ContinuousValuation

/-- Jones--Plotkin (1989), Section 3, pp. 187--188: the internally constructed
lower integral of a bounded Scott-continuous scalar function. -/
noncomputable def jonesIntegral {D : Type u} [Preorder D] :
    VSub D → BoundedScottFunction D → ℝ≥0∞ :=
  ContinuousValuation.jonesLowerIntegral

/-- Jones--Plotkin (1989), Section 3, p. 188: integration of the indicator of
an open set recovers the valuation. -/
theorem jonesIntegral_indicator {D : Type u} [Preorder D]
    (μ : VSub D) (U : ScottOpen D) :
    jonesIntegral μ (BoundedScottFunction.indicator U) = μ U := by
  exact ContinuousValuation.JonesLowerIntegral.indicator μ U

/-- Monotonicity of the Jones integral, part of the Section 3 integration
calculus (Jones--Plotkin 1989, pp. 187--188). -/
theorem jonesIntegral_mono {D : Type u} [Preorder D]
    (μ : VSub D) {f g : BoundedScottFunction D} (hfg : f ≤ g) :
    jonesIntegral μ f ≤ jonesIntegral μ g := by
  exact ContinuousValuation.JonesLowerIntegral.mono μ hfg

/-- Jones (1990), Theorem 3.13, p. 54 (also Jones--Plotkin 1989,
Theorem 3.1, p. 188): directed monotone convergence in the integrand. -/
theorem jones_1990_thm_3_13_DMC
    {D : Type u} [Preorder D]
    {A : Set (BoundedScottFunction D)}
    (hA : DirectedSet A) (f : BoundedScottFunction D)
    (hf : ∀ x : D,
      IsSup ((fun g : BoundedScottFunction D => g x) '' A) (f x))
    (μ : VSub D) :
    IsSup ((fun g : BoundedScottFunction D => jonesIntegral μ g) '' A)
      (jonesIntegral μ f) := by
  exact ContinuousValuation.JonesLowerIntegral.directed_mono_convergence_integrand
    hA f hf μ

/-- Jones--Plotkin (1989), Theorem 3.3, p. 188: directed monotone
convergence in the valuation argument. -/
theorem jonesPlotkin_1989_thm_3_3
    {D : Type u} [Preorder D]
    {A : Set (VSub D)} (hA : DirectedSet A) (s : VSub D)
    (hs : IsSup A s) (f : BoundedScottFunction D) :
    IsSup ((fun μ : VSub D => jonesIntegral μ f) '' A)
      (jonesIntegral s f) := by
  exact ContinuousValuation.JonesLowerIntegral.directed_mono_convergence_valuation
    hA s hs f

/-- Jones (1990), Theorem 4.5, pp. 71--72: the Kleisli extension constructed
by integrating each target-open coordinate of a valuation kernel. -/
noncomputable def jonesKleisli
    {D : Type u} {E : Type v} [Preorder D] [Preorder E] :
    AbramskyJung.Chapter2.ScottContFun D (VSub E) → VSub D → VSub E :=
  ContinuousValuation.jonesKleisli

/-- Defining evaluation formula for Jones's Kleisli extension, Theorem 4.5,
pp. 71--72. -/
theorem jonesKleisli_apply
    {D : Type u} {E : Type v} [Preorder D] [Preorder E]
    (k : AbramskyJung.Chapter2.ScottContFun D (VSub E))
    (μ : VSub D) (U : ScottOpen E) :
    jonesKleisli k μ U = jonesIntegral μ (kernelSection k U) := by
  rfl

/-- The Kleisli extension is a morphism in the input valuation; this is part
of the well-defined Kleisli triple in Jones (1990), Theorem 4.5. -/
theorem jonesKleisli_scottContinuous_input
    {D : Type u} {E : Type v} [Preorder D] [Preorder E]
    (k : AbramskyJung.Chapter2.ScottContFun D (VSub E)) :
    AbramskyJung.Chapter2.ScottContinuous (jonesKleisli k) := by
  exact ContinuousValuation.jonesKleisli_scottContinuous_input k

/-- First Kleisli unit law, Jones (1990), Theorem 4.5, p. 72. -/
theorem jonesKleisli_dirac
    {D : Type u} {E : Type v} [Preorder D] [Preorder E]
    (k : AbramskyJung.Chapter2.ScottContFun D (VSub E)) (x : D) :
    jonesKleisli k (ContinuousValuation.dirac x) = k x := by
  exact ContinuousValuation.jonesKleisli_dirac k x

/-- Second Kleisli unit law, Jones (1990), Theorem 4.5, p. 72. -/
theorem jonesKleisli_unit
    {D : Type u} [Preorder D] (μ : VSub D) :
    jonesKleisli (ContinuousValuation.unit (D := D)) μ = μ := by
  exact ContinuousValuation.jonesKleisli_unit μ

/-- Kleisli composition kernel.  Its Scott continuity follows from the
input-continuity component of Jones's Theorem 4.5. -/
noncomputable def jonesKleisliCompose
    {D : Type u} {E : Type v} {F : Type w}
    [Preorder D] [Preorder E] [Preorder F]
    (k : AbramskyJung.Chapter2.ScottContFun D (VSub E))
    (l : AbramskyJung.Chapter2.ScottContFun E (VSub F)) :
    AbramskyJung.Chapter2.ScottContFun D (VSub F) :=
  ContinuousValuation.jonesKleisliCompose k l

/-- Kleisli associativity, Jones (1990), Theorem 4.5, p. 72. -/
theorem jonesKleisli_assoc
    {D : Type u} {E : Type v} {F : Type w}
    [Preorder D] [Preorder E] [Preorder F]
    (k : AbramskyJung.Chapter2.ScottContFun D (VSub E))
    (l : AbramskyJung.Chapter2.ScottContFun E (VSub F))
    (μ : VSub D) :
    jonesKleisli l (jonesKleisli k μ) =
      jonesKleisli (jonesKleisliCompose k l) μ := by
  exact ContinuousValuation.jonesKleisli_assoc k l μ

/-- The functor action is the Kleisli extension of `unit ∘ f`, the final
identity in Jones (1990), Theorem 4.5, p. 72.  This is the exact map-factor
law used later; it does not mention FVA or kernel lifting. -/
theorem jonesKleisli_unit_comp_eq_pushforward
    {D : Type u} {E : Type v} [Preorder D] [Preorder E]
    (f : AbramskyJung.Chapter2.ScottContFun D E) (μ : VSub D) :
    jonesKleisli
      (AbramskyJung.Chapter2.ScottContFun.comp
        (ContinuousValuation.unit (D := E)) f) μ =
      ContinuousValuation.pushforward f μ := by
  exact ContinuousValuation.jonesKleisli_unit_comp_eq_pushforward f μ

/-- Jones (1990), Corollary 5.4, p. 95: if `D` is a continuous ipo, then
its continuous subprobability-valuation ipo is continuous.  The result is now
proved internally from certified finite atomic approximants; this declaration
is retained only as the source-facing theorem name used by the manuscript. -/
theorem jones_1990_cor_5_4_vSub_continuous
    {D : Type u} [PartialOrder D]
    (hD : AbramskyJung.Chapter2.IsContinuousDcpo D) :
    AbramskyJung.Chapter2.IsContinuousDomain (VSub D) := by
  exact ContinuousValuation.JonesCertificate.vSub_isContinuousDomain hD.2

end External
end FiniteValuationApproximable
