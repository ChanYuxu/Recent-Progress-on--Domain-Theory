import ZFCFubini.TopologicalFubini
import ZFCFubini.CompactScottProduct
import ZFCFubini.SourceValuation

/-! The actual compact-pushforward centrality background and its specified
source stages. Intrinsic order-product Scott topology is connected to the
ordinary mixed product only by the proved compact lifting theorem. -/

set_option autoImplicit false
open Set Topology TopologicalSpace MeasureTheory
open scoped ENNReal
universe u v w
namespace ZFCFubini

/-- Compact Hausdorff pushforwards are central against partners in an arbitrary
universe. This proves the existing `Central`, not a replacement predicate. -/
theorem compact_push_central {X : Type w} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    {P : Type u} [PartialOrder P] (μ : Valuation X) (hμ : μ.Subprobability)
    (g : X → WithScott P) (hg : Continuous g) : Central.{u,v} (μ.push g hg) := by
  refine ⟨hμ, ?_⟩
  intro Q _ hQ ν hν h hh h1
  let L (p : P) (q : WithScott Q) : ℝ≥0∞ := h (p, WithScott.ofScott q)
  have hL (p : P) : IsLSC (L p) := by
    exact scott_isLSC (((ScottContinuous.const p).prodMk ScottContinuous.id).comp hh)
  have hLp (q : WithScott Q) : ScottContinuous (fun p => L p q) :=
    (ScottContinuous.id.prodMk (ScottContinuous.const (WithScott.ofScott q))).comp hh
  have hInner : IsLSC (fun p : WithScott P =>
      choquetIntegral ν (fun q => h (WithScott.ofScott p, WithScott.ofScott q))) :=
    scott_isLSC (choquetIntegral_scottContinuous_param ν L hL hLp)
  let H (z : X × WithScott Q) : ℝ≥0∞ := h (WithScott.ofScott (g z.1), WithScott.ofScott z.2)
  have hH : IsLSC H := (scott_isLSC hh).comp _ (compact_scott_prod_continuous g hg)
  rw [choquetIntegral_push μ g hg _ hInner]
  calc
    choquetIntegral μ (fun x => choquetIntegral ν
        (fun q => h (WithScott.ofScott (g x), WithScott.ofScott q))) =
        choquetIntegral ν (fun q => choquetIntegral μ (fun x => H (x, q))) :=
      topological_valuation_fubini μ hμ ν hν H hH
    _ = choquetIntegral ν (fun q => choquetIntegral (μ.push g hg)
        (fun p => h (WithScott.ofScott p, WithScott.ofScott q))) := by
      congr 1
      funext q
      exact (choquetIntegral_push μ g hg _ (scott_isLSC
        ((ScottContinuous.id.prodMk (ScottContinuous.const (WithScott.ofScott q))).comp hh))).symm

/-- Every literal manuscript stage η_M is central, with no restriction on the
universe of the partner dcpo. The actual source map and actual Haar product
valuation are the witnesses. -/
theorem sourceStageEta_central (M : NullSet) : Central.{0,v} (sourceStageEta M) :=
  compact_push_central (radonValuation parameterMeasure)
    (radonValuation_probability parameterMeasure).subprobability
    (sourceFamily M) (sourceFamily_continuous M)

end ZFCFubini
