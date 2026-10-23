import CHFubini.EventStabilization
import Mathlib.MeasureTheory.Measure.EverywherePos
import Mathlib.Topology.Baire.LocallyCompactRegular

/-!
Candidate implementation of manuscript `lem:positive-carrier`.

The proof uses mathlib's `everywherePosSubset`, whose full-measure and
compactness theorems prove the required geometric carrier. It does not take
carrier existence as an assumption. The proof route is equivalent but is not
a line-by-line transcription of the source's countable-base deletion proof.
-/

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal

namespace CHFubini

universe u v w z

/-- The source's positive ambient mass condition for every nonempty relatively
open subset of a compact carrier. The relative set is measured through its
specified inclusion into the ambient measurable space. -/
def PositiveCarrier {X : Type u} [TopologicalSpace X] [MeasurableSpace X]
    (μ : Measure X) (D : Set X) : Prop :=
  D.Nonempty ∧ IsCompact D ∧
    ∀ W : Set D, IsOpen W → W.Nonempty → 0 < μ (Subtype.val '' W)

/-- Mathlib's neighborhood formulation implies the source's exact relative
open-set formulation. -/
theorem isEverywherePos_relatively_open_pos
    {X : Type u} [TopologicalSpace X] [MeasurableSpace X]
    {μ : Measure X} {D : Set X} (hD : μ.IsEverywherePos D)
    {W : Set D} (ho : IsOpen W) (hn : W.Nonempty) :
    0 < μ (Subtype.val '' W) := by
  obtain ⟨O, hO, rfl⟩ := isOpen_induced_iff.mp ho
  obtain ⟨x, hx⟩ := hn
  rw [Subtype.image_preimage_val]
  exact hD x.1 x.2 (D ∩ O) (inter_mem_nhdsWithin D (hO.mem_nhds hx))

/-- Source `lem:positive-carrier`, with general inner regular ambient measure.
The source compact metrizable probability space satisfies the displayed
standard measure and separation assumptions. -/
theorem positive_compact_carrier
    {X : Type u} [TopologicalSpace X] [T2Space X]
    [MeasurableSpace X] [OpensMeasurableSpace X]
    (μ : Measure X) [μ.InnerRegular] {B : Set X}
    (hB : MeasurableSet B) (hpos : 0 < μ B) :
    ∃ D : Set X, D ⊆ B ∧ PositiveCarrier μ D := by
  obtain ⟨K, hKB, hKc, hKpos⟩ := hB.exists_lt_isCompact hpos
  let D : Set X := μ.everywherePosSubset K
  have hKm : MeasurableSet K := hKc.isClosed.measurableSet
  have hDae : D =ᵐ[μ] K := μ.everywherePosSubset_ae_eq hKm
  have hDpos : 0 < μ D := by rw [hDae.measure_eq]; exact hKpos
  have hEP : μ.IsEverywherePos D := μ.isEverywherePos_everywherePosSubset hKm
  refine ⟨D, (μ.everywherePosSubset_subset K).trans hKB,
    nonempty_of_measure_ne_zero hDpos.ne', hKc.everywherePosSubset, ?_⟩
  intro W hW hn
  exact isEverywherePos_relatively_open_pos hEP hW hn

/-- The actual tail-union construction has a carrier stage. The only
geometric input is the preceding dense-incidence lemma, restricted to the
source set `A`: its exceptional points form a countable subset of `A`.

The map `decode` permits the codomain to be a bundled lattice of opens;
injectivity prevents any replacement by a quotient or surrogate map.
-/
theorem tail_maps_carrier_stabilization
    {I : Type u} [Preorder I]
    {X : Type v} [TopologicalSpace X] [T2Space X]
    {A : Type w} {Y : Type z}
    (initial : I → Set A) (hmono : Monotone initial)
    (hcount : ∀ β, (initial β).Countable)
    (hcapture : ∀ N : Set A, N.Countable → ∃ β₀ : I, N ⊆ initial β₀)
    (R : X → Set A) (F : I → X → Y)
    (decode : Y → Set A) (hinj : Function.Injective decode)
    (hF : ∀ β s, decode (F β s) = (initial β)ᶜ ∪ R s)
    {D : Set X} (hDc : IsCompact D)
    (hincidence : ∃ N : Set A, N.Countable ∧ ∀ a ∉ N,
      IsOpen {s : D | a ∈ R s.1} ∧ Dense {s : D | a ∈ R s.1}) :
    ∃ β₀ : I, ∀ β, β₀ ≤ β →
      ∃ G : Set D, Dense G ∧ IsGδ G ∧
        G ⊆ {s : D | F β s.1 = F β₀ s.1} := by
  letI : CompactSpace D := isCompact_iff_compactSpace.mp hDc
  obtain ⟨N, hN, hinc⟩ := hincidence
  obtain ⟨β₀, hNβ₀⟩ := hcapture N hN
  refine ⟨β₀, fun β hβ => ?_⟩
  let C : Set A := initial β \ initial β₀
  have hC : C.Countable := (hcount β).mono diff_subset
  have hT : (initial β₀)ᶜ = (initial β)ᶜ ∪ C := by
    ext a
    have hsub := hmono hβ
    simp only [mem_compl_iff, mem_union, C, mem_diff]
    constructor
    · intro ha
      by_cases hab : a ∈ initial β
      · exact Or.inr ⟨hab, ha⟩
      · exact Or.inl hab
    · rintro (ha | ⟨_, ha⟩)
      · exact fun ha₀ => ha (hsub ha₀)
      · exact ha
  have ho (a : A) (ha : a ∈ C) : IsOpen {s : D | a ∈ R s.1} :=
    (hinc a (fun haN => ha.2 (hNβ₀ haN))).1
  have hd (a : A) (ha : a ∈ C) : Dense {s : D | a ∈ R s.1} :=
    (hinc a (fun haN => ha.2 (hNβ₀ haN))).2
  obtain ⟨G, hGd, hGg, hGeq⟩ :=
    tail_union_agreement_contains_dense_Gdelta hT hC (fun s : D => R s.1) ho hd
  refine ⟨G, hGd, hGg, fun s hs => hinj ?_⟩
  rw [hF, hF]
  exact hGeq hs

/-- The measure conclusion of `prop:null-defect`, derived for the actual
tail-union maps, not assumed from a record storing the desired law.

This helper exposes one remaining upstream bridge: `hincidence` is exactly
the dense random-incidence result plus the CH source set's null-trace
property. The source-facing theorem must instantiate that bridge from its
proved random-open construction; this conditional helper is not by itself a
claim that the paper's proposition has been fully formalized.
-/
theorem tail_map_arbitrary_union_defect_null
    {I : Type u} [SemilatticeSup I] (hI : CountablyBounded I)
    {X : Type v} [TopologicalSpace X] [T2Space X] [SecondCountableTopology X]
    [MeasurableSpace X] [OpensMeasurableSpace X]
    {A : Type w} {Y : Type z}
    (μ : Measure X) [μ.InnerRegular]
    (initial : I → Set A) (hmono : Monotone initial)
    (hcount : ∀ β, (initial β).Countable)
    (hcapture : ∀ N : Set A, N.Countable → ∃ β₀ : I, N ⊆ initial β₀)
    (R : X → Set A) (F : I → X → Y)
    (decode : Y → Set A) (hinj : Function.Injective decode)
    (hF : ∀ β s, decode (F β s) = (initial β)ᶜ ∪ R s)
    (hincidence : ∀ D : Set X, PositiveCarrier μ D →
      ∃ N : Set A, N.Countable ∧ ∀ a ∉ N,
        IsOpen {s : D | a ∈ R s.1} ∧ Dense {s : D | a ∈ R s.1})
    {J : Type*} (H : J → Set Y)
    (ho : ∀ β j, IsOpen (F β ⁻¹' H j))
    (ha : ∀ j, Antitone (fun β => F β ⁻¹' H j)) :
    μ (limitPreimage F (⋃ j, H j) \ ⋃ j, limitPreimage F (H j)) = 0 := by
  have hoUnion (β : I) : IsOpen (F β ⁻¹' ⋃ j, H j) := by
    rw [preimage_iUnion]
    exact isOpen_iUnion (ho β)
  have haUnion : Antitone (fun β => F β ⁻¹' ⋃ j, H j) := by
    intro β γ hβγ s hs
    obtain ⟨j, hj⟩ := mem_iUnion.mp hs
    exact mem_iUnion.mpr ⟨j, ha j hβγ hj⟩
  have hoLim : IsOpen (limitPreimage F (⋃ j, H j)) :=
    limitPreimage_isOpen hI F _ haUnion hoUnion
  have hoTests (j : J) : IsOpen (limitPreimage F (H j)) :=
    limitPreimage_isOpen hI F _ (ha j) (fun β => ho β j)
  let B : Set X := limitPreimage F (⋃ j, H j) \ ⋃ j, limitPreimage F (H j)
  have hBm : MeasurableSet B :=
    hoLim.measurableSet.diff (isOpen_iUnion hoTests).measurableSet
  change μ B = 0
  by_contra hB
  obtain ⟨D, hDB, hD⟩ := positive_compact_carrier μ hBm (pos_iff_ne_zero.mpr hB)
  obtain ⟨β₀, hβ₀⟩ := tail_maps_carrier_stabilization initial hmono hcount hcapture
    R F decode hinj hF hD.2.1 (hincidence D hD)
  have hCarrier : ∃ β₀ : I, ∀ β, β₀ ≤ β →
      Dense {s : D | F β s.1 = F β₀ s.1} := by
    refine ⟨β₀, fun β hβ => ?_⟩
    obtain ⟨G, hGd, _, hGeq⟩ := hβ₀ β hβ
    exact hGd.mono hGeq
  have hStable : ∀ j, ∃ σ : I, ∀ β, σ ≤ β →
      F β ⁻¹' H j = limitPreimage F (H j) :=
    fun j => limitPreimage_eventually_eq hI F (H j) (ha j) (fun β => ho β j)
  exact hD.1.ne_empty (carrier_defect_empty F H D ho hStable hCarrier hDB)

end CHFubini

#print axioms CHFubini.positive_compact_carrier
#print axioms CHFubini.tail_maps_carrier_stabilization
#print axioms CHFubini.tail_map_arbitrary_union_defect_null

