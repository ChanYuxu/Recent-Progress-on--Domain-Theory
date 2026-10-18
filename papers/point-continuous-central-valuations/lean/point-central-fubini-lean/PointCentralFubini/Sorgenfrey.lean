import PointCentralFubini.SourceStatements
import PointCentralFubini.Normalization
import PointCentralFubini.InnerSkeleton
import PointCentralFubini.MeasureIncidence
import PointCentralFubini.SmythDcpo
set_option autoImplicit false
open Set Topology TopologicalSpace MeasureTheory
open scoped ENNReal
universe u v
namespace PointCentralFubini

/-- The upper Vietoris topology on the concrete reverse-inclusion carrier. -/
@[implicit_reducible] def sorgenfreyUpperVietoris : TopologicalSpace SorgenfreySmyth :=
  TopologicalSpace.generateFrom {G | ∃ U : Opens Sorgenfrey,
    G = {K | ((OrderDual.ofDual K : NonemptyCompacts Sorgenfrey) : Set Sorgenfrey) ⊆ U}}

/-- Verified cited fact: Xu--Yang, arXiv:2003.06542v1, Example 5.18(4),
using Theorem 5.8; nonempty compact sets are saturated in this Hausdorff space. -/
axiom xuYang_sorgenfrey_scott :
  Topology.scott SorgenfreySmyth Set.univ = sorgenfreyUpperVietoris

/-- The cited dcpo assertion, now proved internally by compact intersection.
The existing declaration name is retained for compatibility. -/
theorem xuYang_sorgenfrey_dcpo : IsDcpo SorgenfreySmyth :=
  nonemptyCompacts_reverse_isDcpo Sorgenfrey

/-- Verified cited FPR Proposition 4.3, restricted to the finite tau-smooth
Borel measures used in Section 4. The measurable space is explicitly Borel. -/
axiom fpr_measure_integral (X : Type u) [TopologicalSpace X]
    (m : TauMeasure X) (f : X → ℝ≥0∞) (hf : IsLSC f) :
    integral m.toValuation f = @lintegral X (borel X) m.measure f

/-- The full Vietoris to Scott identity, using the located topology theorem. -/
theorem vietorisToScott_continuous : Continuous vietorisToScott := by
  change @Continuous SorgenfreyVietoris SorgenfreySmyth inferInstance
    (Topology.scott SorgenfreySmyth Set.univ) OrderDual.toDual
  rw [xuYang_sorgenfrey_scott]
  apply continuous_generateFrom_iff.mpr
  rintro G ⟨U,rfl⟩
  exact NonemptyCompacts.isOpen_subsets_of_isOpen U.isOpen

/-- Conditional assembly of source Theorem 4.7, retained as a general interface.
`SorgenfreyFubini.lean` supplies the actual proved manuscript dependencies. -/
theorem sorgenfrey_fubini_of_dependencies
    (hinc : MeasureSourceIncidenceStatement.{0})
    (hlift : FullVietorisLiftStatement)
    (hobs : ExtremalObservablesStatement)
    (hskeleton : SorgenfreyInnerSkeletonStatement) :
    SorgenfreyFubiniStatement.{v} := by
  obtain ⟨lower,upper,hlow,hup,hcont,hgen,hfirst⟩ := hobs
  letI : FirstCountableTopology SorgenfreyVietoris := hfirst
  apply fubini_of_finite SorgenfreySmyth
  intro μ hμ
  apply central_of_incidence μ
  apply incidence_of_finite_tests μ
  intro ξ hξ
  obtain ⟨m,hm⟩ := hlift μ hμ
  obtain ⟨C,hC⟩ := hskeleton m
  let f := vietorisToScott
  have hf : Continuous f := vietorisToScott_continuous
  have hpush : m.toValuation.push f hf = μ := by
    ext U; exact hm U
  let t : ScottOpens SorgenfreySmyth → Opens SorgenfreyVietoris := Opens.comap ⟨f,hf⟩
  have ht : ScottContinuous t := ScottContinuous.of_map_sSup (by
    intro A _ _
    simp [t,sSup_image])
  let ts : WithScott (ScottOpens SorgenfreySmyth) → WithScott (Opens SorgenfreyVietoris) :=
    fun U => WithScott.toScott (t (WithScott.ofScott U))
  have hts : Continuous ts := (scott_continuous_iff t).mp ht
  let η := ξ.push ts hts
  have hη : η.Finite := ξ.finite_push hξ ts hts
  have hid := (hinc SorgenfreyVietoris m C hC η hη).2
  have hleft : integral η (fun U => m.measure ((WithScott.ofScott U : Opens SorgenfreyVietoris) : Set SorgenfreyVietoris)) =
      integral ξ (fun U => μ (WithScott.ofScott U)) := by
    change integral (ξ.push ts hts) (fun U => m.toValuation (WithScott.ofScott U)) = _
    rw [integral_push ξ ts hts _ (scott_isLSC m.toValuation.continuous)]
    apply integral_congr ξ; intro U
    exact hm (WithScott.ofScott U)
  have hpoint : ∀ K : SorgenfreyVietoris,
      η (pointOpen K) = ξ (neighbourhoodMap SorgenfreySmyth (OrderDual.toDual K)) := by
    intro K
    change ξ (Opens.comap ⟨ts,hts⟩ (pointOpen K)) = _
    congr 1
  have hg : IsLSC (fun K : SorgenfreyVietoris => η (pointOpen K)) := by
    have he : (fun K : SorgenfreyVietoris => η (pointOpen K)) =
      (fun K => ξ (neighbourhoodMap SorgenfreySmyth (WithScott.ofScott K))) ∘ f := by
      funext K; exact hpoint K
    rw [he]
    exact (scott_isLSC ((neighbourhoodMap_scott SorgenfreySmyth).comp ξ.continuous)).comp hf
  have hright : @lintegral SorgenfreyVietoris (borel SorgenfreyVietoris) m.measure
      (fun K => η (pointOpen K)) =
      integral μ (fun K => ξ (neighbourhoodMap SorgenfreySmyth (WithScott.ofScott K))) := by
    rw [← fpr_measure_integral SorgenfreyVietoris m _ hg,← hpush]
    let g : WithScott SorgenfreySmyth → ℝ≥0∞ :=
      fun K => ξ (neighbourhoodMap SorgenfreySmyth (WithScott.ofScott K))
    change integral m.toValuation (fun K => η (pointOpen K)) = integral (m.toValuation.push f hf) g
    rw [integral_push m.toValuation f hf g
      (scott_isLSC ((neighbourhoodMap_scott SorgenfreySmyth).comp ξ.continuous))]
    exact integral_congr m.toValuation hpoint
  exact hleft.symm.trans (hid.trans hright)

/-- Two-argument assembly interface, using the proved Lemmas 4.5 and 4.6.
The canonical Theorem 4.7 supplies proofs of both arguments. -/
theorem sorgenfrey_fubini_of_measure_dependencies
    (hinc : MeasureSourceIncidenceStatement.{0})
    (hlift : FullVietorisLiftStatement) : SorgenfreyFubiniStatement.{v} :=
  sorgenfrey_fubini_of_dependencies hinc hlift extremal_observables sorgenfrey_inner_skeleton
end PointCentralFubini
