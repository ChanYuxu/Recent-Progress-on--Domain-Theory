import CoreCompactSimplified.HeZhangRepresentationBasic
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.GDelta.MetrizableSpace

/-!
Polish-space background and source Claim 5 in the proof of He--Zhang
Theorem 4.13. The G-delta proof uses the printed H_r compact subsets of M²,
their compact second-coordinate projections, and the exact countable union
of nonminimal points. Positive integers r are encoded by n+1.

The cited Lemma 4.10 is proved by a closed diagonal embedding into the
countable product of the open sets in a G-delta presentation. Its internal
proof is not specified in the paper; no stronger hypothesis is used here.
-/

set_option autoImplicit false

universe u v

namespace CoreCompactSimplified.HeZhangRepresentation

open Set TopologicalSpace CoreCompactNonSober HeZhangLawson
open scoped Topology

noncomputable section

/-- The cited background Lemma 4.9, with a compatible metrizable topology. -/
theorem compact_metrizable_polish {X : Type u} [TopologicalSpace X]
    [CompactSpace X] [MetrizableSpace X] : PolishSpace X := by
  letI : MetricSpace X := metrizableSpaceMetric X
  infer_instance

theorem compactMetric_polish {X : Type u} [MetricSpace X] [CompactSpace X] :
    PolishSpace X := compact_metrizable_polish

/-- The cited Lemma 4.10: a G-delta subspace of a Polish space is Polish. -/
theorem polishSpace_of_isGdelta {X : Type u} [TopologicalSpace X] [PolishSpace X]
    {s : Set X} (hs : IsGδ s) : PolishSpace s := by
  obtain ⟨U, hUopen, hsU⟩ := hs.eq_iInter_nat
  let Y : ℕ → Type u := fun n ↦ U n
  letI : ∀ n, TopologicalSpace (Y n) := fun _ ↦ inferInstance
  letI : ∀ n, PolishSpace (Y n) := fun n ↦ (hUopen n).polishSpace
  letI : PolishSpace (∀ n, Y n) := by infer_instance
  have hxU : ∀ x : s, ∀ n, x.val ∈ U n := by
    intro x n
    exact mem_iInter.mp ((Set.ext_iff.mp hsU x.val).mp x.property) n
  let f : s → ∀ n, Y n := fun x n ↦ ⟨x.val, hxU x n⟩
  let g : (∀ n, Y n) → X := fun y ↦ (y 0).val
  have hf : Continuous f := continuous_pi fun n ↦
    continuous_subtype_val.subtype_mk (fun x ↦ hxU x n)
  have hg : Continuous g := continuous_subtype_val.comp (continuous_apply 0)
  have hfemb : Topology.IsEmbedding f :=
    Topology.IsEmbedding.of_comp hf hg (show Topology.IsEmbedding (g ∘ f) from
      Topology.IsEmbedding.subtypeVal)
  have hrange : range f = ⋂ n : ℕ, {y : ∀ n, Y n | (y n).val = (y 0).val} := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact mem_iInter.mpr fun _ ↦ rfl
    · intro hy
      have hxy : (y 0).val ∈ s := by
        rw [hsU]
        apply mem_iInter.mpr
        intro n
        exact (mem_iInter.mp hy n) ▸ (y n).property
      refine ⟨⟨(y 0).val, hxy⟩, ?_⟩
      funext n
      apply Subtype.ext
      exact (mem_iInter.mp hy n).symm
  have hclosed : IsClosed (range f) := by
    rw [hrange]
    apply isClosed_iInter
    intro n
    exact isClosed_eq (continuous_subtype_val.comp (continuous_apply n))
      (continuous_subtype_val.comp (continuous_apply 0))
  exact (show Topology.IsClosedEmbedding f from ⟨hfemb, hclosed⟩).polishSpace

/-- The countable topological sum from the cited background Lemma 4.11. -/
theorem countableSum_polish {ι : Type v} [Countable ι] {X : ι → Type u}
    [∀ i, TopologicalSpace (X i)] [∀ i, PolishSpace (X i)] :
    PolishSpace (Σ i, X i) := by infer_instance

theorem natSum_polish {X : ℕ → Type u}
    [∀ n, TopologicalSpace (X n)] [∀ n, PolishSpace (X n)] :
    PolishSpace (Σ n, X n) := countableSum_polish

section OrderedMetric

variable {M : Type u} [MetricSpace M] [PartialOrder M] [OrderClosedTopology M]

/-- The printed H_r construction. The parameter n represents r=n+1≥1. -/
def separatedLowerPairs (Q : Set M) (n : ℕ) : Set (M × M) :=
  ((Q ×ˢ Q) ∩ {p | p.1 ≤ p.2}) ∩ {p | 1 / (n + 1 : ℝ) ≤ dist p.1 p.2}

def lowerPairImage (Q : Set M) (n : ℕ) : Set M :=
  Prod.snd '' separatedLowerPairs Q n

theorem separatedLowerPairs_isCompact {Q : Set M} (hQ : IsCompact Q) (n : ℕ) :
    IsCompact (separatedLowerPairs Q n) := by
  exact ((hQ.prod hQ).inter_right isClosed_le_prod).inter_right
    (isClosed_dist_ge (1 / (n + 1 : ℝ)))

theorem lowerPairImage_isClosed {Q : Set M} (hQ : IsCompact Q) (n : ℕ) :
    IsClosed (lowerPairImage Q n) :=
  ((separatedLowerPairs_isCompact hQ n).image continuous_snd).isClosed

end OrderedMetric

section ScottRepresentation

variable {P : Type u} [PartialOrder P]

local instance representationPolishScottTopologyP : TopologicalSpace P := scottTopology P
local instance representationPolishClosedLawsonTopologyP : TopologicalSpace (ScottCloseds P) :=
  closedLawsonTopology P

theorem closedLawson_polish (hcore : ScottCoreCompact P) (hsecond : ScottSecondCountable P) :
    PolishSpace (ScottCloseds P) := by
  obtain ⟨hc, _, _, hm⟩ := closedLawson_compact_hausdorff_metrizable hcore hsecond
  letI : CompactSpace (ScottCloseds P) := hc
  letI : MetrizableSpace (ScottCloseds P) := hm
  exact compact_metrizable_polish

/-- Source Claim 5, including the printed choice of a principal closed set
at a minimal point of K. All H_r/projection identities are proved on the
actual hitting subset Q_K of the actual pullback Lawson space. -/
theorem hitting_minimal_isGdelta (hcore : ScottCoreCompact P)
    (hsecond : ScottSecondCountable P) {K : Set P} (hK : IsCompact K) :
    IsGδ {A : ScottCloseds P | Minimal (· ∈ hitting K) A} := by
  obtain ⟨hc, _, _, hm⟩ := closedLawson_compact_hausdorff_metrizable hcore hsecond
  letI : CompactSpace (ScottCloseds P) := hc
  letI : MetrizableSpace (ScottCloseds P) := hm
  letI : MetricSpace (ScottCloseds P) := metrizableSpaceMetric _
  letI : OrderClosedTopology (ScottCloseds P) := closedLawson_orderClosed hcore
  have hQcompact : IsCompact (hitting K) := hitting_isCompact hcore hsecond hK
  have hnonmin : hitting K \ {A | Minimal (· ∈ hitting K) A} =
      ⋃ n : ℕ, lowerPairImage (hitting K) n := by
    ext A
    constructor
    · rintro ⟨⟨a, haA, haK⟩, hAnot⟩
      obtain ⟨k, hka, hkmin⟩ := HeZhangClosed.compact_exists_minimal_le hK haK
      have hkA : k ∈ A := ((isClosed_scott_iff _).mp A.isClosed).1 hka haA
      have hkQ : principal k ∈ hitting K := ⟨k, le_rfl, hkmin.1⟩
      have hkminQ : Minimal (· ∈ hitting K) (principal k) :=
        (minimal_hitting_iff _).mpr ⟨k, hkmin, rfl⟩
      have hne : principal k ≠ A := by
        intro heq
        exact hAnot (heq ▸ hkminQ)
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (dist_pos.mpr hne)
      apply mem_iUnion.mpr
      refine ⟨n, ⟨(principal k, A), ?_, rfl⟩⟩
      exact ⟨⟨⟨hkQ, ⟨a, haA, haK⟩⟩, (principal_le_closed_iff _ _).mpr hkA⟩, hn.le⟩
    · intro hA
      obtain ⟨n, ⟨⟨B, A'⟩, ⟨⟨⟨hBQ, hAQ⟩, hBA⟩, hdist⟩, rfl⟩⟩ := mem_iUnion.mp hA
      refine ⟨hAQ, ?_⟩
      intro hmin
      have heq : A' = B := hmin.eq_of_ge hBQ hBA
      have hpos : (0 : ℝ) < 1 / (n + 1 : ℝ) := by positivity
      change 1 / (n + 1 : ℝ) ≤ dist B A' at hdist
      rw [heq, dist_self] at hdist
      exact (not_le_of_gt hpos) hdist
  have hmin : {A : ScottCloseds P | Minimal (· ∈ hitting K) A} =
      hitting K ∩ ⋂ n : ℕ, (lowerPairImage (hitting K) n)ᶜ := by
    rw [← compl_iUnion, ← hnonmin]
    ext A
    simp only [mem_setOf_eq, mem_inter_iff, mem_compl_iff, mem_diff]
    exact ⟨fun h ↦ ⟨h.1, fun hn ↦ hn.2 h⟩,
      fun ⟨hA, hn⟩ ↦ by_contra fun hnot ↦ hn ⟨hA, hnot⟩⟩
  rw [hmin]
  exact (hitting_isClosed hK).isGδ.inter
    (IsGδ.iInter_of_isOpen fun n ↦ (lowerPairImage_isClosed hQcompact n).isOpen_compl)

end ScottRepresentation

end

end CoreCompactSimplified.HeZhangRepresentation
