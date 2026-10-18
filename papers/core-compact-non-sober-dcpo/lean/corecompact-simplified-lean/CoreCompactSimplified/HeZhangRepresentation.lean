import CoreCompactSimplified.HeZhangRepresentationPolish
import Mathlib.Topology.Sequences

/-!
The actual Polish tagged sum Z in He--Zhang Theorem 4.13.

The n,j summand is Min Q_(K_j) intersect Diamond U_n in the literal
complement-pullback Lawson topology of Scott-closed sets. The projection is
the actual subtype map. The relation requires exactly a successor first
index and inclusion of the represented principal lower sets in the printed
direction; neither a proxy countable carrier nor a stored conclusion is used.

An auxiliary direct closed-preimage proof is retained. The final source-facing
closedness theorem instead follows the printed sequential argument: both tags
eventually stabilize, the actual projections converge, and the closed order
contains their limit. Polish metrizability then turns sequential closedness
into closedness.
-/

set_option autoImplicit false

universe u

namespace CoreCompactSimplified.HeZhangRepresentation

open Set TopologicalSpace CoreCompactNonSober HeZhangLawson
open scoped Topology

noncomputable section

variable {P : Type u} [PartialOrder P]

local instance representationScottTopologyP : TopologicalSpace P := scottTopology P
local instance representationClosedLawsonTopologyP : TopologicalSpace (ScottCloseds P) :=
  closedLawsonTopology P

/-- The exact summand E_(n,j) in the source. -/
def taggedCell (U : ℕ → ScottOpens P) (K : ℕ → Set P) (n j : ℕ) :
    Set (ScottCloseds P) :=
  {A | Minimal (· ∈ hitting (K j)) A} ∩ diamond (U n)

/-- Nested topological sums with the source's two natural-number tags. -/
abbrev Tag (U : ℕ → ScottOpens P) (K : ℕ → Set P) :=
  Σ n : ℕ, Σ j : ℕ, taggedCell U K n j

@[implicit_reducible] def tagTopology (U : ℕ → ScottOpens P) (K : ℕ → Set P) :
    TopologicalSpace (Tag U K) := inferInstance

def taggedProjection (U : ℕ → ScottOpens P) (K : ℕ → Set P)
    (t : Tag U K) : ScottCloseds P := t.2.2.val

def taggedRelation (U : ℕ → ScottOpens P) (K : ℕ → Set P)
    (t s : Tag U K) : Prop :=
  t.1 = s.1 + 1 ∧ taggedProjection U K s ≤ taggedProjection U K t

/-- The source's notation (n,j,↓x), constructed from an actual minimal
point x in K_j intersect U_n. -/
def tagOfPoint (U : ℕ → ScottOpens P) (K : ℕ → Set P)
    (n j : ℕ) (x : P) (hmin : Minimal (· ∈ K j) x) (hxU : x ∈ U n) : Tag U K :=
  ⟨n, j, ⟨principal x, (minimal_hitting_iff _).mpr ⟨x, hmin, rfl⟩,
    (Set.ext_iff.mp (principal_preimage_diamond (U n)) x).mpr hxU⟩⟩

@[simp] theorem taggedProjection_tagOfPoint (U : ℕ → ScottOpens P) (K : ℕ → Set P)
    (n j : ℕ) (x : P) (hmin : Minimal (· ∈ K j) x) (hxU : x ∈ U n) :
    taggedProjection U K (tagOfPoint U K n j x hmin hxU) = principal x := rfl

theorem taggedCell_isGdelta (hcore : ScottCoreCompact P) (hsecond : ScottSecondCountable P)
    (U : ℕ → ScottOpens P) (K : ℕ → Set P) (hK : ∀ j, IsCompact (K j)) (n j : ℕ) :
    IsGδ (taggedCell U K n j) :=
  (hitting_minimal_isGdelta hcore hsecond (hK j)).inter (diamond_isOpen (U n)).isGδ

theorem taggedCell_polish (hcore : ScottCoreCompact P) (hsecond : ScottSecondCountable P)
    (U : ℕ → ScottOpens P) (K : ℕ → Set P) (hK : ∀ j, IsCompact (K j)) (n j : ℕ) :
    PolishSpace (taggedCell U K n j) := by
  letI : PolishSpace (ScottCloseds P) := closedLawson_polish hcore hsecond
  exact polishSpace_of_isGdelta (taggedCell_isGdelta hcore hsecond U K hK n j)

theorem tag_polish (hcore : ScottCoreCompact P) (hsecond : ScottSecondCountable P)
    (U : ℕ → ScottOpens P) (K : ℕ → Set P) (hK : ∀ j, IsCompact (K j)) :
    @PolishSpace (Tag U K) (tagTopology U K) := by
  letI : ∀ n j, PolishSpace (taggedCell U K n j) :=
    fun n j ↦ taggedCell_polish hcore hsecond U K hK n j
  letI : ∀ n, PolishSpace (Σ j : ℕ, taggedCell U K n j) :=
    fun _ ↦ countableSum_polish
  exact countableSum_polish

theorem taggedProjection_continuous (U : ℕ → ScottOpens P) (K : ℕ → Set P) :
    @Continuous (Tag U K) (ScottCloseds P) (tagTopology U K) (closedLawsonTopology P)
      (taggedProjection U K) := by
  exact continuous_sigma fun _ ↦ continuous_sigma fun _ ↦ continuous_subtype_val

theorem taggedLevel_continuous (U : ℕ → ScottOpens P) (K : ℕ → Set P) :
    @Continuous (Tag U K) ℕ (tagTopology U K) inferInstance (fun t ↦ t.1) :=
  continuous_sigma fun _ ↦ continuous_const

theorem taggedCompactIndex_continuous (U : ℕ → ScottOpens P) (K : ℕ → Set P) :
    @Continuous (Tag U K) ℕ (tagTopology U K) inferInstance (fun t ↦ t.2.1) :=
  continuous_sigma fun _ ↦ continuous_sigma fun _ ↦ continuous_const

/-- Every actual tag represents the source's unique endpoint s in Min K_j ∩ U_n. -/
theorem tagged_exists_principal (U : ℕ → ScottOpens P) (K : ℕ → Set P)
    (t : Tag U K) :
    ∃ x : P, Minimal (· ∈ K t.2.1) x ∧ x ∈ U t.1 ∧
      principal x = taggedProjection U K t := by
  obtain ⟨x, hx, heq⟩ := (minimal_hitting_iff t.2.2.val).mp t.2.2.property.1
  refine ⟨x, hx, ?_, heq⟩
  have hdiamond : principal x ∈ diamond (U t.1) := by
    rw [heq]
    exact t.2.2.property.2
  change x ∈ principal ⁻¹' diamond (U t.1) at hdiamond
  rwa [principal_preimage_diamond] at hdiamond

def taggedPoint (U : ℕ → ScottOpens P) (K : ℕ → Set P) (t : Tag U K) : P :=
  (tagged_exists_principal U K t).choose

theorem taggedPoint_spec (U : ℕ → ScottOpens P) (K : ℕ → Set P) (t : Tag U K) :
    Minimal (· ∈ K t.2.1) (taggedPoint U K t) ∧ taggedPoint U K t ∈ U t.1 ∧
      principal (taggedPoint U K t) = taggedProjection U K t :=
  (tagged_exists_principal U K t).choose_spec

theorem taggedPoint_unique (U : ℕ → ScottOpens P) (K : ℕ → Set P) (t : Tag U K)
    (x : P) (hx : principal x = taggedProjection U K t) : x = taggedPoint U K t :=
  principal.injective (hx.trans (taggedPoint_spec U K t).2.2.symm)

@[simp] theorem taggedPoint_tagOfPoint (U : ℕ → ScottOpens P) (K : ℕ → Set P)
    (n j : ℕ) (x : P) (hmin : Minimal (· ∈ K j) x) (hxU : x ∈ U n) :
    taggedPoint U K (tagOfPoint U K n j x hmin hxU) = x :=
  (taggedPoint_unique U K (tagOfPoint U K n j x hmin hxU) x rfl).symm

theorem taggedRelation_iff_points (U : ℕ → ScottOpens P) (K : ℕ → Set P)
    (t s : Tag U K) :
    taggedRelation U K t s ↔ t.1 = s.1 + 1 ∧ taggedPoint U K s ≤ taggedPoint U K t := by
  unfold taggedRelation
  rw [← (taggedPoint_spec U K s).2.2, ← (taggedPoint_spec U K t).2.2]
  exact and_congr_right fun _ ↦ principal.le_iff_le

/-- The relation itself is closed on the actual Polish sum, including its
discrete successor-index requirement. This expands the source Claim 6
closedness argument, rather than dropping its index condition. -/
theorem taggedRelation_isClosed (hcore : ScottCoreCompact P)
    (U : ℕ → ScottOpens P) (K : ℕ → Set P) :
    @IsClosed (Tag U K × Tag U K)
      (@instTopologicalSpaceProd (Tag U K) (Tag U K) (tagTopology U K) (tagTopology U K))
      {p | taggedRelation U K p.1 p.2} := by
  letI : OrderClosedTopology (ScottCloseds P) := closedLawson_orderClosed hcore
  have hsucc : Continuous (fun n : ℕ ↦ n + 1) := continuous_of_discreteTopology
  have hlevel : IsClosed {p : Tag U K × Tag U K | p.1.1 = p.2.1 + 1} :=
    isClosed_eq ((taggedLevel_continuous U K).comp continuous_fst)
      (hsucc.comp ((taggedLevel_continuous U K).comp continuous_snd))
  have horder : IsClosed {p : Tag U K × Tag U K |
      taggedProjection U K p.2 ≤ taggedProjection U K p.1} :=
    isClosed_le ((taggedProjection_continuous U K).comp continuous_snd)
      ((taggedProjection_continuous U K).comp continuous_fst)
  exact hlevel.inter horder

/-- Both natural-number indices eventually equal those of the limit, as
claimed in the original proof using the clopen summands. -/
theorem taggedIndices_eventually_constant (U : ℕ → ScottOpens P) (K : ℕ → Set P)
    {a : ℕ → Tag U K} {x : Tag U K}
    (ha : Filter.Tendsto a Filter.atTop (𝓝 x)) :
    ∃ N : ℕ, ∀ m, N ≤ m → (a m).1 = x.1 ∧ (a m).2.1 = x.2.1 := by
  have hlevel := ((taggedLevel_continuous U K).tendsto x).comp ha
  have hindex := ((taggedCompactIndex_continuous U K).tendsto x).comp ha
  have hl : ∀ᶠ m in Filter.atTop, (a m).1 = x.1 := by
    simpa only [Set.mem_singleton_iff] using
      hlevel.eventually ((isOpen_discrete {x.1}).mem_nhds (mem_singleton x.1))
  have hj : ∀ᶠ m in Filter.atTop, (a m).2.1 = x.2.1 := by
    simpa only [Set.mem_singleton_iff] using
      hindex.eventually ((isOpen_discrete {x.2.1}).mem_nhds (mem_singleton x.2.1))
  exact Filter.eventually_atTop.mp (hl.and hj)

/-- The source's sequential-limit step, including eventual stabilization of
both n and j tags and convergence of the actual principal-closed projections. -/
theorem taggedRelation_limit_source (hcore : ScottCoreCompact P)
    (U : ℕ → ScottOpens P) (K : ℕ → Set P)
    {a b : ℕ → Tag U K} {x y : Tag U K}
    (ha : Filter.Tendsto a Filter.atTop (𝓝 x))
    (hb : Filter.Tendsto b Filter.atTop (𝓝 y))
    (hrel : ∀ m, taggedRelation U K (a m) (b m)) :
    taggedRelation U K x y := by
  letI : OrderClosedTopology (ScottCloseds P) := closedLawson_orderClosed hcore
  obtain ⟨Na, hNa⟩ := taggedIndices_eventually_constant U K ha
  obtain ⟨Nb, hNb⟩ := taggedIndices_eventually_constant U K hb
  let N := max Na Nb
  obtain ⟨hax, _haj⟩ := hNa N (le_max_left _ _)
  obtain ⟨hby, _hbj⟩ := hNb N (le_max_right _ _)
  refine ⟨?_, ?_⟩
  · simpa only [hax, hby] using (hrel N).1
  · have hpa : Filter.Tendsto (fun m ↦ taggedProjection U K (a m))
        Filter.atTop (𝓝 (taggedProjection U K x)) :=
      ((taggedProjection_continuous U K).tendsto x).comp ha
    have hpb : Filter.Tendsto (fun m ↦ taggedProjection U K (b m))
        Filter.atTop (𝓝 (taggedProjection U K y)) :=
      ((taggedProjection_continuous U K).tendsto y).comp hb
    exact isClosed_le_prod.mem_of_tendsto (hpb.prodMk_nhds hpa)
      (Filter.Eventually.of_forall fun m ↦ (hrel m).2)

theorem taggedRelation_isSeqClosed_source (hcore : ScottCoreCompact P)
    (U : ℕ → ScottOpens P) (K : ℕ → Set P) :
    @IsSeqClosed (Tag U K × Tag U K)
      (@instTopologicalSpaceProd (Tag U K) (Tag U K) (tagTopology U K) (tagTopology U K))
      {p | taggedRelation U K p.1 p.2} := by
  intro a x hrel hlim
  exact taggedRelation_limit_source hcore U K
    (continuous_fst.tendsto x |>.comp hlim)
    (continuous_snd.tendsto x |>.comp hlim) hrel

/-- The actual source-facing closedness proof used for the rank application:
sequential closedness above, followed by Polish metrizability. The direct
preimage auxiliary theorem is not a dependency of this theorem. -/
theorem taggedRelation_isClosed_source (hcore : ScottCoreCompact P)
    (hsecond : ScottSecondCountable P) (U : ℕ → ScottOpens P) (K : ℕ → Set P)
    (hK : ∀ j, IsCompact (K j)) :
    @IsClosed (Tag U K × Tag U K)
      (@instTopologicalSpaceProd (Tag U K) (Tag U K) (tagTopology U K) (tagTopology U K))
      {p | taggedRelation U K p.1 p.2} := by
  letI : PolishSpace (Tag U K) := tag_polish hcore hsecond U K hK
  exact (taggedRelation_isSeqClosed_source hcore U K).isClosed

end

end CoreCompactSimplified.HeZhangRepresentation
