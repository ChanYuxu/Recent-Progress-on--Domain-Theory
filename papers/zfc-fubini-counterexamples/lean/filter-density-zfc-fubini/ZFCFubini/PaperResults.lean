import ZFCFubini.MainTheorem
import ZFCFubini.DensityProbability

/-! Public, source-facing interfaces for the numbered results through the
main theorem. Internal generic helpers are instantiated on the literal model.
The two final source items still have separately disclosed background scope. -/

set_option autoImplicit false
open Set TopologicalSpace MeasureTheory Topology
open scoped ENNReal
universe u v
namespace ZFCFubini.Paper
open FilterDcpo

theorem density :
    (∀ U : Set Circle, @IsOpen Circle densityTopology U ↔ DensityOpen U) ∧
    (∀ U : @Opens Circle densityTopology, densityValuation U = volume (U : Set Circle)) ∧
    ScottContinuous (@Valuation.mass Circle densityTopology densityValuation) ∧
    @Valuation.Probability Circle densityTopology densityValuation :=
  ⟨densityTopology_isOpen_iff, densityValuation_apply,
    @Valuation.continuous Circle densityTopology densityValuation,
    densityValuation_probability⟩

theorem radon {X : Type u} [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ] [μ.InnerRegular] :
    (∀ {I : Type v} [Nonempty I] (V : I → Opens X), Directed (· ≤ ·) V →
      μ ((⨆ i, V i : Opens X) : Set X) = ⨆ i, μ (V i : Set X)) ∧
    (∀ E : Set X, MeasurableSet E → 0 < μ E →
      ∃ D : Set X, D ⊆ E ∧ PositiveCarrier μ D) := radon_compact_metric μ

theorem dcpo :
    IsDcpo SourceP ∧
    (∀ p : SourceP, (∀ q : SourceP, p ≤ q → q = p) ↔ ∃ y, p = e circleModel y) ∧
    (∀ (p : SourceP) (y : Circle), p ≤ e circleModel y ↔ y ∈ p.kernel) ∧
    (∀ (A : Set SourceP), DirectedOn (· ≤ ·) A →
      ∀ p ∈ A, ∀ q ∈ A, p.label ≠ q.label → ∃ r ∈ A, ∀ s ∈ A, s ≤ r) :=
  ⟨sourceP_isDcpo, maximal_iff, le_e_iff,
    fun _ hd _ hp _ hq hne => directed_different_labels_has_greatest hd hp hq hne⟩

theorem fixed_label_sup {I : Type u} [Nonempty I] (p : I → SourceP)
    (hd : Directed (· ≤ ·) p) (x : Circle) (hx : ∀ i, (p i).label = x) :
    IsLUB (Set.range p) (sameLabelSup p hd x hx) ∧
    (∀ U : Set Circle, U ∈ (sameLabelSup p hd x hx).filter ↔ ∃ i, U ∈ (p i).filter) ∧
    (sameLabelSup p hd x hx).kernel = ⋂ i, (p i).kernel :=
  ⟨sameLabelSup_isLUB p hd x hx, mem_filter_sameLabelSup p hd x hx,
    kernel_sameLabelSup p hd x hx⟩

/-- The complete printed proposition, including its fixed-label formula. -/
theorem dcpo_full :
    IsDcpo SourceP ∧
    (∀ p : SourceP, (∀ q : SourceP, p ≤ q → q = p) ↔ ∃ y, p = e circleModel y) ∧
    (∀ (p : SourceP) (y : Circle), p ≤ e circleModel y ↔ y ∈ p.kernel) ∧
    (∀ (A : Set SourceP), DirectedOn (· ≤ ·) A →
      ∀ p ∈ A, ∀ q ∈ A, p.label ≠ q.label → ∃ r ∈ A, ∀ s ∈ A, s ≤ r) ∧
    (∀ {I : Type u} [Nonempty I] (p : I → SourceP) (hd : Directed (· ≤ ·) p)
      (x : Circle) (hx : ∀ i, (p i).label = x),
      IsLUB (Set.range p) (sameLabelSup p hd x hx) ∧
      (∀ U : Set Circle, U ∈ (sameLabelSup p hd x hx).filter ↔ ∃ i, U ∈ (p i).filter) ∧
      (sameLabelSup p hd x hx).kernel = ⋂ i, (p i).kernel) :=
  ⟨dcpo.1, dcpo.2.1, dcpo.2.2.1, dcpo.2.2.2, fixed_label_sup⟩

theorem H_ordinary_eq_density_H (U : Opens Circle) :
    H_ordinary circleModel U = H circleModel
      (@Opens.mk Circle densityTopology U (ordinary_isOpen_densityTopology U.isOpen)) := rfl

theorem gluing (S : Set SourceP) :
    IsOpen (WithScott.ofScott ⁻¹' S) ↔
      (∀ x : Circle, IsOpen {p : WithScott (Branch circleModel x) | (WithScott.ofScott p).val ∈ S}) ∧
      (∀ p ∈ S, ∀ y ∈ p.kernel, e circleModel y ∈ S) := isOpen_gluing_iff circleModel S

theorem HU :
    (∀ U : @Opens Circle densityTopology,
      IsOpen (H circleModel U : Set (WithScott SourceP)) ∧ trace (H circleModel U) = U) ∧
    (∀ (U : Opens Circle) (p : SourceP), WithScott.toScott p ∈ H_ordinary circleModel U ↔
      p.kernel ⊆ U) ∧ ScottContinuous (H_ordinary circleModel) :=
  ⟨fun U => ⟨(H circleModel U).isOpen, trace_H circleModel U⟩,
    mem_H_ordinary_iff_kernel_subset circleModel, ordinaryH_scottContinuous circleModel⟩

theorem countable_filters (p : SourceP) :
    Directed (· ≤ ·) (finiteApprox p) ∧ IsLUB (Set.range (finiteApprox p)) p ∧
    ∀ S, (∃ B : Set (Set Circle), B.Countable ∧
      (∀ U ∈ B, @IsOpen Circle densityTopology U) ∧
      ∀ U : Set Circle, U ∈ (finiteApprox p S).filter ↔
        OpenFilter.GeneratedMember (tau := densityTopology) B U) ∧
      (finiteApprox p S).filter ≤ p.filter ∧ (finiteApprox p S).kernel = p.kernel ∧
        (finiteApprox p S).label = p.label := by
  obtain ⟨hd, hs, hS⟩ := countable_filters_approximation p
  exact ⟨hd, hs, fun S => ⟨(countablyBased_iff_countablyGenerated (finiteApprox p S)).mp (hS S).1,
    (hS S).2⟩⟩

theorem trace_topology :
    (∀ H : SourceQ, @IsOpen Circle densityTopology (trace H)) ∧
    (∃ eMax : @Homeomorph Circle (maximalSet circleModel) densityTopology inferInstance,
      ∀ y, (eMax y).val = WithScott.toScott (e circleModel y)) :=
  ⟨trace_isOpen, maximalHomeomorph circleModel, maximalHomeomorph_apply circleModel⟩

theorem nu : sourceNu.Probability ∧ ScottContinuous sourceNu.mass ∧
    ∀ H : SourceQ, sourceNu H = volume (trace H) :=
  ⟨sourceNu_probability, sourceNu.continuous, sourceNu_apply⟩

theorem finite_truncation (x : Circle) (N : Opens Circle) (hxN : x ∈ N) :
    (∀ A : Set Circle, (N : Set Circle) ⊆ A →
      IsOpen {p : WithScott (Branch circleModel x) | (WithScott.ofScott p).val.kernel ⊆ A}) ∧
    Directed (· ≤ ·) (branchTruncation circleModel x N hxN) ∧
    (⨆ F : Finset Circle, branchTruncation circleModel x N hxN F) = ⊤ :=
  ⟨kernelSubset_branch_isOpen circleModel x N hxN,
    branchTruncation_directed circleModel x N hxN, branchTruncation_cover circleModel x N hxN⟩

theorem random_continuity :
    Continuous (fun t : Omega => WithScott.toScott (randomOpen t)) ∧
    (∀ C : SourceQ, Continuous (fun t : Omega =>
      WithScott.toScott (H_ordinary circleModel (randomOpen t) ⊔ C))) ∧
    (∀ K : Set Circle, IsCompact K → IsOpen {t : Omega | K ⊆ randomOpen t}) :=
  ⟨randomOpen_continuous, fun C => randomOpen_scott_sup_continuous
    (H_ordinary circleModel) (ordinaryH_scottContinuous circleModel) C,
    fun _ hK => randomOpen_compact_containment_isOpen hK⟩

theorem stabilization :
    (∀ A : ScottOpens SourceQ, ∃ M0 : NullSet, ∀ M, M0 ≤ M →
      {t | WithScott.toScott (sourceG M t) ∈ A} = (sourcePsi A : Set Omega)) ∧
    Monotone sourcePsi ∧ sourcePsi ⊥ = ⊥ ∧ sourcePsi ⊤ = ⊤ ∧
    (∀ A B, sourcePsi (A ⊓ B) = sourcePsi A ⊓ sourcePsi B) ∧
    (∀ {I : Type u} [Countable I] (A : I → ScottOpens SourceQ),
      sourcePsi (⨆ i, A i) = ⨆ i, sourcePsi (A i)) :=
  ⟨sourcePsi_stabilization, sourcePsi_mono, sourcePsi_bot, sourcePsi_top,
    sourcePsi_inf, fun A => sourcePsi_iSup A⟩

theorem hitting {D : Set Omega} (hD : PositiveCarrier parameterMeasure D) :
    ∃ N : NullSet,
      (∀ y ∉ (N : Set Circle), IsOpen {t : D | y ∈ randomOpen t.val} ∧
        Dense {t : D | y ∈ randomOpen t.val}) ∧
      (∀ F : Set Circle, F.Finite → Disjoint F (N : Set Circle) →
        ∀ W : Set D, IsOpen W → W.Nonempty → ∃ t ∈ W, F ⊆ randomOpen t.val) := hitting_source hD

noncomputable def hittingNull {D : Set Omega} (hD : PositiveCarrier parameterMeasure D) : NullSet :=
  Classical.choose (hitting hD)

theorem hittingNull_finite {D : Set Omega} (hD : PositiveCarrier parameterMeasure D)
    (F : Finset Circle) (hF : ∀ y ∈ F, y ∉ (hittingNull hD).val)
    (W : Set D) (hWo : IsOpen W) (hWn : W.Nonempty) :
    ∃ t ∈ W, (F : Set Circle) ⊆ randomOpen t.val :=
  (Classical.choose_spec (hitting hD)).2 F F.finite_toSet
    (Set.disjoint_left.mpr (fun y hy hyN => hF y hy hyN)) W hWo hWn

theorem same_trace {D : Set Omega} (hD : PositiveCarrier parameterMeasure D)
    (M0 : NullSet) (hNM0 : hittingNull hD ≤ M0)
    (Z H B : SourceQ) (hZH : Z ≤ H) (htr : trace Z = trace H)
    (havoid : trace H ⊆ M0.valᶜ) (A : ScottOpens SourceQ) (W : Set D) (hW : IsOpen W)
    (hstart : ∃ t ∈ W, WithScott.toScott (H_ordinary circleModel (randomOpen t.val) ⊔ B ⊔ H) ∈ A) :
    ∃ s ∈ W, WithScott.toScott (H_ordinary circleModel (randomOpen s.val) ⊔ B ⊔ Z) ∈ A :=
  same_trace_comparison circleModel randomOpen randomOpen_continuous D (hittingNull hD).val M0.val
    hNM0 (hittingNull_finite hD) Z H B hZH htr havoid A W hW hstart

theorem index_comparison {D : Set Omega} (hD : PositiveCarrier parameterMeasure D)
    (M0 : NullSet) (hNM0 : hittingNull hD ≤ M0) (M : NullSet) (hM0M : M0 ≤ M)
    (A : ScottOpens SourceQ)
    (hstart : (D ∩ {t | WithScott.toScott (sourceG M0 t) ∈ A}).Nonempty) :
    (D ∩ {t | WithScott.toScott (sourceG M t) ∈ A}).Nonempty := by
  obtain ⟨t, htD, htA⟩ := hstart
  obtain ⟨s, hs⟩ := source_index_comparison M0 M hNM0 hM0M (hittingNull_finite hD) A
    ⟨⟨t, htD⟩, htA⟩
  exact ⟨s.val, s.property, hs⟩

theorem arbitrary_unions {I : Type u} (A : I → ScottOpens SourceQ) :
    parameterMeasure ((sourcePsi (⨆ i, A i) : Set Omega) \
      ⋃ i, (sourcePsi (A i) : Set Omega)) = 0 := source_arbitrary_unions A

theorem eta_continuous : sourceEtaValuation.Probability ∧ ScottContinuous sourceEtaValuation.mass ∧
    ∀ A : ScottOpens SourceQ, sourceEtaValuation A = parameterMeasure (sourcePsi A : Set Omega) :=
  ⟨sourceEta_probability, sourceEtaValuation.continuous, sourceEta_apply⟩

theorem evaluation : ScottContinuous (incidence SourceP) ∧
    ∀ p : SourceP, IsOpen (evaluationOpen p : Set (WithScott SourceQ)) :=
  ⟨incidence_scottContinuous SourceP, fun p => (evaluationOpen p).isOpen⟩

theorem sections :
    (∀ p : SourceP, sourceEtaValuation (evaluationOpen p) =
      parameterMeasure {t | p.kernel ⊆ randomOpen t}) ∧
    ScottContinuous sourceFUnit ∧
    (∀ y : Circle, (sourceFUnit (e circleModel y)).val = q) ∧
    q = sourceQ ∧ 0 < q ∧ q ≤ 1 / 64 :=
  ⟨sourceEta_evaluation, sourceFUnit_scottContinuous, sourceFReal_maximal,
    q_source, q_bounds.1, q_bounds.2⟩

theorem main : MainStatement := main_theorem

theorem Q_isDcpo : IsDcpo SourceQ := completeLattice_isDcpo SourceQ

end ZFCFubini.Paper
