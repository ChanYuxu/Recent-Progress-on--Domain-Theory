import CHFubini.Noncentral
import CHFubini.ProductNonOpen

/-! Source-facing interfaces for the numbered claims. All fixed-source
statements use the same proved CH sequence, trace measure and random maps as
the main theorem. Generic lemmas remain separately available with their exact
stated hypotheses. The three questions and the categorical monad boundary are
not installed as axioms or asserted as completed theorems.
-/
set_option autoImplicit false
open Set Topology TopologicalSpace MeasureTheory
open scoped ENNReal
universe v
namespace CHFubini

/-- Lemma 3.1; injectivity additionally records the preceding construction. -/
theorem paper_A_properties (hCH : CH) :
    Function.Injective (paperSequence hCH) ∧
    (∀ B : Set UnitAddCircle, MeasurableSet B → volume B = 0 → ∃ β,
      range (paperSequence hCH) ∩ B ⊆ initialSegment (paperSequence hCH) β ∧
      (range (paperSequence hCH) ∩ B).Countable) ∧
    (∀ C : Set UnitAddCircle, IsCompact C → 0 < volume C →
      (range (paperSequence hCH) ∩ C).Nonempty) ∧
    (∀ E : Set UnitAddCircle, MeasurableSet E →
      (range (paperSequence hCH) ∩ E).Countable → volume E = 0) := paperSequence_spec hCH

/-- Lemma 3.2. -/
theorem paper_source_properties (hCH : CH) :
    T2Space (PaperSource hCH) ∧ FirstCountableTopology (PaperSource hCH) ∧
    (∀ C : Set (PaperSource hCH), C.Countable → ∃ β, C ⊆ sourceInitial (paperSequence hCH) β) ∧
    Continuous (@SourcePoint.val UnitAddCircle (paperSequence hCH)) :=
  ⟨inferInstance,inferInstance,source_countable_initial_containment _,source_val_continuous _⟩

/-- Lemma 3.3, sandwich statement. -/
theorem paper_ordinary_representative (hCH : CH) {U : Set (PaperSource hCH)} (hU : IsOpen U) :
    ∃ O : Set UnitAddCircle, IsOpen O ∧ ∃ β,
      sourceBase (paperSequence hCH) O β ⊆ U ∧ U ⊆ SourcePoint.val ⁻¹' O :=
  source_ordinary_representative _ hU

/-- Lemma 3.3, countable-deletion statement for already-open U only. -/
theorem paper_countable_deletion (hCH : CH) {U : Set (PaperSource hCH)} (hU : IsOpen U) :
    ∃ O : Set UnitAddCircle, ∃ C : Set (PaperSource hCH),
      IsOpen O ∧ C.Countable ∧ C ⊆ SourcePoint.val ⁻¹' O ∧
      U = SourcePoint.val ⁻¹' O \ C :=
  source_countable_deletion _ hU

/-- Lemma 3.3, arbitrary-family assertion; no countability on I. -/
theorem paper_union_representative (hCH : CH) {I : Type v}
    (U : I → Set (PaperSource hCH)) (O : I → Set UnitAddCircle)
    (β : I → OmegaOneStage) (hO : ∀ i, IsOpen (O i))
    (hlo : ∀ i, sourceBase (paperSequence hCH) (O i) (β i) ⊆ U i)
    (hup : ∀ i, U i ⊆ SourcePoint.val ⁻¹' O i) :
    ∃ σ, sourceBase (paperSequence hCH) (⋃ i, O i) σ ⊆ ⋃ i, U i ∧
      (⋃ i, U i) ⊆ SourcePoint.val ⁻¹' (⋃ i, O i) :=
  ordinary_union_representative _ U O β hO hlo hup

/-- Proposition 3.4: the exact sigma-algebra and actual measure. -/
theorem paper_source_measure (hCH : CH) :
    borel (PaperSource hCH) = (borel UnitAddCircle).comap (@SourcePoint.val UnitAddCircle (paperSequence hCH)) ∧
    IsProbabilityMeasure (paperSourceMeasure hCH) ∧
    ∀ B : Set UnitAddCircle, MeasurableSet B →
      paperSourceMeasure hCH (SourcePoint.val ⁻¹' B) = volume B :=
  ⟨source_borel_eq_comap _,paperSourceMeasure_spec hCH⟩

/-- Proposition 3.5, retaining the actual measure restriction. -/
theorem paper_alpha_continuous (hCH : CH) :
    (paperAlpha hCH).Probability ∧ ScottContinuous (paperAlpha hCH).mass ∧
    ∀ U : Opens (PaperSource hCH), paperAlpha hCH U = paperSourceMeasure hCH (U : Set _) :=
  ⟨paperAlpha_probability hCH,(paperAlpha hCH).continuous,fun _ => rfl⟩

/-- Proposition 4.1: R, every F_beta, and the actual stage pushforwards. -/
theorem paper_random_continuous (hCH : CH) (ε : ℝ) :
    Continuous (fun s : PaperOmega => WithScott.toScott
      (randomOpen SourcePoint.val (source_val_continuous (paperSequence hCH)) (circleRadius ε) s)) ∧
    (∀ β, Continuous (sourceStage (paperSequence hCH) (circleRadius ε) β)) ∧
    ∀ β, (stageValuation volume (paperSequence hCH) (circleRadius ε) β).Probability :=
  ⟨randomOpen_continuous _ _ _,sourceStage_continuous _ _,stageValuation_probability volume _ _⟩

/-- Lemma 4.3, including its stated consequence for countable increasing
unions. Full Scott continuity is proved independently, not assumed here. -/
theorem paper_psi_countable (hCH : CH) (ε : ℝ) (hε : 0 < ε) :
    Monotone (sourcePsi (paperSequence hCH) (circleRadius ε)) ∧
    sourcePsi (paperSequence hCH) (circleRadius ε) ⊥ = ⊥ ∧
    sourcePsi (paperSequence hCH) (circleRadius ε) ⊤ = ⊤ ∧
    (∀ H K, sourcePsi (paperSequence hCH) (circleRadius ε) (H ⊔ K) =
      sourcePsi (paperSequence hCH) (circleRadius ε) H ⊔ sourcePsi (paperSequence hCH) (circleRadius ε) K) ∧
    (∀ H K, sourcePsi (paperSequence hCH) (circleRadius ε) (H ⊓ K) =
      sourcePsi (paperSequence hCH) (circleRadius ε) H ⊓ sourcePsi (paperSequence hCH) (circleRadius ε) K) ∧
    (∀ H : ℕ → ScottOpens (PaperL hCH), sourcePsi (paperSequence hCH) (circleRadius ε) (⨆ n, H n) =
      ⨆ n, sourcePsi (paperSequence hCH) (circleRadius ε) (H n)) ∧
    ∀ H : ℕ → ScottOpens (PaperL hCH), Monotone H →
      paperRho hCH ε hε (⨆ n, H n) = ⨆ n, paperRho hCH ε hε (H n) :=
  ⟨sourcePsi_mono _ _,sourcePsi_empty _ _,sourcePsi_univ _ _,
    sourcePsi_union _ _,sourcePsi_inter _ _,sourcePsi_countable_union _ _,
    fun H hH => (paperRho hCH ε hε).map_iSup H hH.directed_le⟩

/-- Lemma 4.4 on the actual compact metric product probability space. -/
theorem paper_positive_carrier {B : Set PaperOmega} (hB : MeasurableSet B) (hpos : 0 < paperLaw B) :
    ∃ D : Set PaperOmega, D ⊆ B ∧ PositiveCarrier paperLaw D := by
  letI : Measure.InnerRegular paperLaw := productLaw_innerRegular volume
  exact positive_compact_carrier paperLaw hB hpos

/-- Lemma 4.5. -/
theorem paper_dense_incidence {ε : ℝ} (hε : 0 < ε)
    {D : Set PaperOmega} (hD : PositiveCarrier paperLaw D) :
    ∃ N : Set UnitAddCircle, MeasurableSet N ∧ volume N = 0 ∧ ∀ t ∉ N,
      IsOpen {s : D | t ∈ randomBallUnion (circleRadius ε) s.val} ∧
      Dense {s : D | t ∈ randomBallUnion (circleRadius ε) s.val} :=
  dense_random_ball_incidence volume _ (circleRadius_pos hε) hD

/-- Lemma 4.6, retaining its full dense-G_delta statement. The carrier stage
depends on D but not on any Scott test. -/
theorem paper_carrier_stabilization (hCH : CH) {ε : ℝ} (hε : 0 < ε)
    {D : Set PaperOmega} (hD : PositiveCarrier paperLaw D) :
    ∃ β₀ : OmegaOneStage, ∀ β, β₀ ≤ β → ∃ G : Set D, Dense G ∧ IsGδ G ∧
      G ⊆ {s : D | sourceStage (paperSequence hCH) (circleRadius ε) β s.val =
        sourceStage (paperSequence hCH) (circleRadius ε) β₀ s.val} := by
  refine tail_maps_carrier_stabilization (sourceInitial (paperSequence hCH))
    (sourceInitial_mono _) (sourceInitial_countable _) (source_countable_initial_containment _)
    (fun s => {x : PaperSource hCH | x.val ∈ randomBallUnion (circleRadius ε) s})
    (sourceStage (paperSequence hCH) (circleRadius ε))
    (fun V => ((WithScott.ofScott V : PaperL hCH) : Set (PaperSource hCH))) ?_
    (sourceStage_decode _ _) hD.2.1 ?_
  · intro U V h
    apply WithScott.ofScott.injective
    exact Opens.ext h
  · obtain ⟨N,hN,hN0,hgood⟩ := paper_dense_incidence hε hD
    exact ⟨{x : PaperSource hCH | x.val ∈ N},paperNullTrace hCH N hN hN0,
      fun x hx => hgood x.val hx⟩

/-- Proposition 4.7, arbitrary set-indexed family. -/
theorem paper_null_defect (hCH : CH) (ε : ℝ) (hε : 0 < ε)
    {I : Type v} (H : I → ScottOpens (PaperL hCH)) :
    paperLaw ((sourcePsi (paperSequence hCH) (circleRadius ε) (⨆ i, H i) : Set _) \
      ⋃ i, (sourcePsi (paperSequence hCH) (circleRadius ε) (H i) : Set _)) = 0 :=
  source_null_defect volume _ (paperNullTrace hCH) _ (circleRadius_pos hε) H

/-- Theorem 4.8; no countable-cofinality condition. -/
theorem paper_rho_continuous (hCH : CH) (ε : ℝ) (hε : 0 < ε) :
    (paperRho hCH ε hε).Probability ∧ ScottContinuous (paperRho hCH ε hε).mass :=
  ⟨paperRho_probability hCH ε hε,(paperRho hCH ε hε).continuous⟩

/-- Remark 4.9's mathematical equality, not a general infimum theorem. -/
theorem paper_rho_eq_inf_stages (hCH : CH) (ε : ℝ) (hε : 0 < ε)
    (H : ScottOpens (PaperL hCH)) :
    paperRho hCH ε hε H = ⨅ β, stageValuation volume (paperSequence hCH) (circleRadius ε) β H :=
  limitingValuation_eq_inf_stages volume _ (paperNullTrace hCH) _ (circleRadius_pos hε) H

/-- Proposition 4.10, with its exact construction and all numerical tests. -/
theorem paper_exact_tests (hCH : CH) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    (∀ x : PaperSource hCH, paperRho hCH ε hε (pointOpen x) = ENNReal.ofReal (qEpsilon ε)) ∧
    0 < intervalLength ε 0 ∧ intervalLength ε 0 ≤ qEpsilon ε ∧
    qEpsilon ε ≤ ε ∧ ε < 1 ∧
    (∀ r : ℝ≥0∞, paperRho hCH ε hε (massTest (paperAlpha hCH) r) = if r < 1 then 1 else 0) ∧
    ∀ r : ℝ≥0∞, 1 ≤ r → massTest (paperAlpha hCH) r = ⊥ := by
  obtain ⟨hlow,_,hup,_⟩ := qEpsilon_bounds hε hε1
  exact ⟨rho_point_value hε hε1 _ (paperNullTrace hCH),intervalLength_pos hε 0,
    hlow,hup,hε1,rho_massTest_value volume _ (paperNullTrace hCH) _ (circleRadius_pos hε)
      (paperAlpha hCH) (paperAlpha_probability hCH) (paperAlpha_stage_mass hCH ε),
    fun _ hr => massTest_empty _ (paperAlpha_probability hCH) hr⟩

/-- Lemma 5.1. -/
theorem paper_compact_countable (hCH : CH) {C : Set (PaperSource hCH)} (hC : IsCompact C) :
    C.Countable := source_compact_countable _ hC

/-- Lemma 5.2's consequence for the actual source. Its generic assertion is
compact_countable_decreasing_outer_base, which has no extra separation premise. -/
theorem paper_compact_outer_base (hCH : CH) (C : Set (PaperSource hCH)) (hC : IsCompact C) :
    ∃ N : ℕ → Set (PaperSource hCH), IsDecreasingOuterBase C N :=
  compact_countable_decreasing_outer_base C hC (paper_compact_countable hCH hC)

/-- Theorem 5.4; in particular L's well-filteredness does not use a false
claim that all complete lattices are Scott sober. -/
theorem paper_vietoris_scott (hCH : CH) :
    (inferInstance : TopologicalSpace (WithScott (PaperP hCH))) = upperVietorisTopology (PaperSource hCH) ∧
    FirstCountableTopology (WithScott (PaperP hCH)) ∧ IsSober (WithScott (PaperP hCH)) ∧
    IsWellFiltered (WithScott (PaperP hCH)) ∧ IsWellFiltered (WithScott (PaperL hCH)) := by
  obtain ⟨_,heq,hfirst,hsober,hwell⟩ := source_smyth_properties (paperSequence hCH)
  exact ⟨heq,hfirst,hsober,hwell,opens_scott_isWellFiltered _⟩

/-- Proposition 6.1 on the full intrinsic order-product Scott topology. -/
theorem paper_W_scott_open (hCH : CH) :
    IsOpen (paperW hCH : Set (WithScott (PaperP hCH × PaperL hCH))) := (paperW hCH).isOpen

/-- Proposition 6.2, including its exact singleton value. -/
theorem paper_g_continuous (hCH : CH) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    ScottContinuous (fun C : PaperP hCH => paperRho hCH ε hε (rightSection (paperW hCH) C)) ∧
    ∀ x : PaperSource hCH, paperRho hCH ε hε
      (rightSection (paperW hCH) (WithScott.ofScott (singletonMap x))) = ENNReal.ofReal (qEpsilon ε) := by
  refine ⟨source_g_profile_scott _,?_⟩
  intro x
  unfold paperW
  rw [rightSection_incidence_eq_compactNeighborhood,compactNeighborhood_singleton_eq_pointOpen]
  exact rho_point_value hε hε1 _ (paperNullTrace hCH) x

/-- Corollary 6.4's strengthened assertion for both specified valuations. -/
theorem paper_both_noncentral (hCH : CH) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    ¬ Central.{0,0} (paperMu hCH) ∧ ¬ Central.{0,0} (paperRho hCH ε hε) := by
  have hq : ENNReal.ofReal (qEpsilon ε) < 1 := by
    rw [ENNReal.ofReal_lt_one]
    exact (qEpsilon_bounds hε hε1).2.2.2
  exact noncentral_pair_of_indicator_integrals (source_smyth_properties (paperSequence hCH)).1
    (completeLattice_isDcpo (PaperL hCH)) _ _ (paperMu_probability hCH).subprobability
    (paperRho_probability hCH ε hε).subprobability (paperW hCH)
    (source_first_iterated_integral hε _ (paperNullTrace hCH) _ (paperAlpha_probability hCH) (paperAlpha_stage_mass hCH ε))
    (source_second_iterated_integral hε hε1 _ (paperNullTrace hCH) _ (paperAlpha_probability hCH)) (ne_of_lt hq)

/-- The main theorem's numerical equalities for the fixed named witnesses,
so readers can inspect the construction directly rather than just an existential. -/
theorem paper_main_integrals (hCH : CH) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    choquetIntegral (paperRho hCH ε hε)
      (fun V => choquetIntegral (paperMu hCH)
        (indicator (leftSection (paperW hCH) (WithScott.ofScott V)))) = 1 ∧
    choquetIntegral (paperMu hCH)
      (fun C => choquetIntegral (paperRho hCH ε hε)
        (indicator (rightSection (paperW hCH) (WithScott.ofScott C)))) = ENNReal.ofReal (qEpsilon ε) :=
  ⟨source_first_iterated_integral hε _ (paperNullTrace hCH) _
    (paperAlpha_probability hCH) (paperAlpha_stage_mass hCH ε),
    source_second_iterated_integral hε hε1 _ (paperNullTrace hCH) _ (paperAlpha_probability hCH)⟩

/-- Corollary 6.5. Same W, both topologies explicitly supplied on the same
underlying order product. The proof is a direct topological proof, not an
unproved appeal to ordinary-product Fubini. -/
theorem paper_product_topology_strict (hCH : CH) :
    IsOpen (paperW hCH : Set (WithScott (PaperP hCH × PaperL hCH))) ∧
    ¬ @IsOpen (PaperP hCH × PaperL hCH)
      (inferInstance : TopologicalSpace (WithScott (PaperP hCH) × WithScott (PaperL hCH)))
      (paperW hCH : Set (WithScott (PaperP hCH × PaperL hCH))) ∧
    (show TopologicalSpace (PaperP hCH × PaperL hCH) from
      (inferInstance : TopologicalSpace (WithScott (PaperP hCH × PaperL hCH)))) <
    (show TopologicalSpace (PaperP hCH × PaperL hCH) from
      (inferInstance : TopologicalSpace (WithScott (PaperP hCH) × WithScott (PaperL hCH)))) := by
  letI : NoAtoms (volume : Measure UnitAddCircle) := unitCircle_volume_noAtoms
  letI : Measure.InnerRegular (volume : Measure UnitAddCircle) := unitCircle_volume_innerRegular
  exact ⟨paper_W_scott_open hCH,
    source_incidence_not_product_open volume (paperSequence hCH) (paperSourceMeasure hCH) (paperSourceMeasure_spec hCH).2,
    source_orderProductScott_strictly_finer volume (paperSequence hCH) (paperSourceMeasure hCH) (paperSourceMeasure_spec hCH).2⟩

end CHFubini
