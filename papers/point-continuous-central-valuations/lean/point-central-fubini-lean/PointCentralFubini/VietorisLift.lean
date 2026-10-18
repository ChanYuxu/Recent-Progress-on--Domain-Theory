import PointCentralFubini.Sorgenfrey
import PointCentralFubini.SorgenfreyCompactification
import PointCentralFubini.HyperspaceEmbedding
import PointCentralFubini.RadonConcentration
import PointCentralFubini.MeasureTransport

/-! Full Vietoris lifting in source Lemma 4.4. The only new literature boundary
is the explicitly cited AJK compact ordered extension theorem. -/
set_option autoImplicit false
open Set Topology TopologicalSpace MeasureTheory
universe v
namespace PointCentralFubini

abbrev SorgenfreyCompactHyperspace := CompactOrder SorgenfreyCompactification

def sorgenfreyVietorisEmbedding : SorgenfreyVietoris → SorgenfreyCompactHyperspace :=
  compactMap sorgenfreyCompactificationMap sorgenfreyCompactificationMap_embedding.continuous

theorem sorgenfreyVietorisEmbedding_embedding : IsEmbedding sorgenfreyVietorisEmbedding :=
  compactMap_full_embedding sorgenfreyCompactificationMap_embedding

def sorgenfreyScottEmbedding : WithScott SorgenfreySmyth → SorgenfreyCompactHyperspace :=
  fun K => sorgenfreyVietorisEmbedding (WithScott.ofScott K)

theorem sorgenfreyScottEmbedding_inducing :
    @IsInducing (WithScott SorgenfreySmyth) SorgenfreyCompactHyperspace inferInstance
      (upwardTopology SorgenfreyCompactHyperspace) sorgenfreyScottEmbedding := by
  change @IsInducing SorgenfreySmyth SorgenfreyCompactHyperspace
    (Topology.scott SorgenfreySmyth univ) (upwardTopology SorgenfreyCompactHyperspace)
    (compactMap sorgenfreyCompactificationMap sorgenfreyCompactificationMap_embedding.continuous)
  rw [xuYang_sorgenfrey_scott,upwardVietoris_eq_upperVietoris]
  exact compactMap_upper_inducing sorgenfreyCompactificationMap_embedding.isInducing

theorem sorgenfreyScottEmbedding_range :
    range sorgenfreyScottEmbedding = range sorgenfreyVietorisEmbedding := by
  ext K
  constructor
  · rintro ⟨L,rfl⟩
    exact ⟨WithScott.ofScott L,rfl⟩
  · rintro ⟨L,rfl⟩
    exact ⟨WithScott.toScott (OrderDual.toDual L),rfl⟩

/-- Source contract: `lem:full-vietoris-lift` (lemma 4.4).
Version: SHA-256 `134da69fa816824e5fefcb93a4e77a8cd5158c8aaab5ffd288ece2372e55d4e6`.
Locator: `source/manuscript.tex`, lines 483--489; no PDF was supplied.
Formalization status: `proved`; human review is pending.

Strict source TeX:
```latex
\begin{lemma}\label{lem:full-vietoris-lift}
For every finite $\mu\in\Val(D)$, there is a finite $\tau$-smooth Borel measure $m$ on $D_{\mathrm V}$ such that
\begin{equation}\label{eq:vietoris-measure-lift}
 m(\mathcal U)=\mu(\mathcal U)
 \qquad(\mathcal U\in\sigma(D)).
\end{equation}
\end{lemma}
```
-/
theorem full_vietoris_lift : FullVietorisLiftStatement := by
  intro μ hμ
  let E := SorgenfreyCompactHyperspace
  let k := sorgenfreyScottEmbedding
  have hk : @Continuous (WithScott SorgenfreySmyth) E inferInstance
      (upwardTopology E) k := by
    letI : TopologicalSpace E := upwardTopology E
    exact sorgenfreyScottEmbedding_inducing.continuous
  let ν : @Valuation E (upwardTopology E) :=
    @Valuation.push (WithScott SorgenfreySmyth) inferInstance E (upwardTopology E) μ k hk
  have hν : @Valuation.Finite E (upwardTopology E) ν := hμ
  obtain ⟨M,hM⟩ := ajk_compact_ordered_extension E ν hν
  have hupper : IsUpperSet (range k) := by
    rw [sorgenfreyScottEmbedding_range]
    exact compactMap_range_upper sorgenfreyCompactificationMap_embedding
  have hfull := radon_complement_range_null k hk μ hupper M hM
  have hfull' : ∀ B : Set E, MeasurableSet[borel E] B →
      B ⊆ (range sorgenfreyVietorisEmbedding)ᶜ → M.toTauMeasure.measure B = 0 := by
    simpa only [k,sorgenfreyScottEmbedding_range,FiniteRadonMeasure.toTauMeasure_measure]
      using hfull
  obtain ⟨m,hm⟩ := fullOuterTrace_transport sorgenfreyVietorisEmbedding
    sorgenfreyVietorisEmbedding_embedding M.toTauMeasure hfull'
  refine ⟨m,?_⟩
  intro U
  have hambient : ∃ V : Set E, IsOpen[upwardTopology E] V ∧
      sorgenfreyScottEmbedding ⁻¹' V = (U : Set (WithScott SorgenfreySmyth)) := by
    letI : TopologicalSpace E := upwardTopology E
    exact sorgenfreyScottEmbedding_inducing.isOpen_iff.mp U.isOpen
  obtain ⟨V,hV,hpre⟩ := hambient
  let W : @Opens E (upwardTopology E) := by
    letI : TopologicalSpace E := upwardTopology E
    exact ⟨V,hV⟩
  have hB : MeasurableSet[borel E] V := by
    letI : MeasurableSpace E := borel E
    letI : BorelSpace E := ⟨rfl⟩
    exact hV.1.measurableSet
  have hraw : vietorisToScott ⁻¹' (U : Set (WithScott SorgenfreySmyth)) =
      sorgenfreyVietorisEmbedding ⁻¹' V := by
    ext K
    change (vietorisToScott K ∈ U) ↔
      (vietorisToScott K ∈ sorgenfreyScottEmbedding ⁻¹' V)
    rw [hpre]
    rfl
  rw [hraw,hm V hB,FiniteRadonMeasure.toTauMeasure_measure]
  refine (hM W).trans ?_
  apply congrArg μ
  exact Opens.ext hpre

end PointCentralFubini
