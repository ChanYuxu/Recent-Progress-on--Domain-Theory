import CoreCompactSimplified.HeZhangOrder
import CoreCompactSimplified.HeZhangRepresentation
import CoreCompactSimplified.HeZhangPruning
import CoreCompactSimplified.HeZhangRank
import CoreCompactSimplified.ExternalStatements

/-!
He–Zhang Theorem 4.13, on the actual source objects and proof route.

An irreducible Scott-closed subset is first made an inherited dcpo. Its
nonempty countable basis supplies the decreasing U_n and actual compact
neighborhoods K_n. The literal minimal-point seed and its ordinal pruning
are represented in the literal Polish tagged sum of principal closed sets.
The source's well-founded relation has a proved countable rank bound; the
dense pruning stage at that ordinal contradicts the proved rank lower bound.

No external theorem proposition, rank bound, constructed-dcpo existence or
conclusion package is assumed in the public theorem below.
-/

set_option autoImplicit false

universe u

namespace CoreCompactSimplified.HeZhang

open Set TopologicalSpace CoreCompactNonSober Ordinal
open HeZhangRepresentation
open scoped Cardinal

noncomputable section

variable {P : Type u} [PartialOrder P]

local instance proofScottTopology : TopologicalSpace P := scottTopology P

/-- Every original seed point in U_n has its actual principal-ideal tag.
The point decoded from that tag is proved to be that same seed point. -/
theorem source_tag_cover (U : ℕ → ScottOpens P) (K : ℕ → Set P) :
    ∀ n s, s ∈ HeZhangPruning.seed K → s ∈ U n →
      ∃ z : Tag U K, z.1 = n ∧ taggedPoint U K z = s := by
  intro n s hs hsU
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hs
  have hQ : Minimal (· ∈ hitting (K j)) (principal s) :=
    (minimal_hitting_iff _).mpr ⟨s, hj, rfl⟩
  have hdiamond : principal s ∈ diamond (U n) := by
    change s ∈ principal ⁻¹' diamond (U n)
    rw [principal_preimage_diamond]
    exact hsU
  let z : Tag U K := ⟨n, j, ⟨principal s, hQ, hdiamond⟩⟩
  exact ⟨z, rfl, (taggedPoint_unique U K z s rfl).symm⟩

theorem source_relation_wellFounded (hP : IsDcpo P)
    (U : ℕ → ScottOpens P) (K : ℕ → Set P) (hanti : Antitone U)
    (hempty : ¬ ∃ p : P, ∀ n, p ∈ U n) : WellFounded (taggedRelation U K) := by
  have h := HeZhangOrder.wellFounded_level_order hP U hanti hempty
    (fun z : Tag U K ↦ z.1) (taggedPoint U K)
    (fun z ↦ (taggedPoint_spec U K z).2.1)
  exact h.mono (fun t s hts ↦ (taggedRelation_iff_points U K t s).mp hts)

/-- Source Claim 6. The rank bound is proved for the actual Polish sum and
the actual relation; it is not a free parameter at the final application. -/
theorem source_rank_bound (hP : IsDcpo P) (hcore : ScottCoreCompact P)
    (hsecond : ScottSecondCountable P) (U : ℕ → ScottOpens P) (K : ℕ → Set P)
    (hK : ∀ j, IsCompact (K j)) (hanti : Antitone U)
    (hempty : ¬ ∃ p : P, ∀ n, p ∈ U n) :
    ∃ γ : Ordinal.{u}, γ < ω₁ ∧
      ∀ z, ((source_relation_wellFounded hP U K hanti hempty).apply z).rank < γ := by
  letI : TopologicalSpace (Tag U K) := tagTopology U K
  letI : PolishSpace (Tag U K) := tag_polish hcore hsecond U K hK
  exact HeZhangRank.closed_polish_rank_bounded (taggedRelation U K)
    (taggedRelation_isClosed_source hcore hsecond U K hK)
    (source_relation_wellFounded hP U K hanti hempty)

/-- Source Claim 7 with all tag-coverage and relation bridges discharged on
the actual source tagged sum. The proved inequality even holds for all
ordinals, not only the countable ordinals used in the printed proof. -/
theorem source_stage_rank_lower (hP : IsDcpo P)
    (U : ℕ → ScottOpens P) (K : ℕ → Set P) (hanti : Antitone U)
    (hempty : ¬ ∃ p : P, ∀ n, p ∈ U n)
    (α : Ordinal.{u}) (z : Tag U K)
    (hz : taggedPoint U K z ∈ HeZhangPruning.stage K U α) :
    α ≤ ((source_relation_wellFounded hP U K hanti hempty).apply z).rank :=
  HeZhangPruning.stage_rank_lower K U (taggedPoint U K) (fun z ↦ z.1)
    (taggedRelation U K) (source_relation_wellFounded hP U K hanti hempty)
    (source_tag_cover U K)
    (fun a b hl hp ↦ (taggedRelation_iff_points U K a b).mpr ⟨hl, hp⟩) α z hz

/-- The source proof inside the inherited irreducible closed dcpo: the
intersection of the chosen nonempty opens cannot be empty, and hence a
greatest element exists. -/
theorem irreducible_has_greatest (hP : IsDcpo P) (hlc : ScottLocallyCompact P)
    (hsecond : ScottSecondCountable P)
    (hirr : IsIrreducible (Set.univ : Set P)) : ∃ p : P, ∀ x : P, x ≤ p := by
  classical
  letI : SecondCountableTopology P := hsecond
  have hcore : ScottCoreCompact P := hlc.isCoreCompact
  obtain ⟨U, hanti, hUne, hcofinal⟩ :=
    HeZhangBasis.exists_decreasing_nonempty_opens hirr
  by_contra hnogreatest
  have hempty : ¬ ∃ p : P, ∀ n, p ∈ U n := by
    rintro ⟨p, hp⟩
    exact hnogreatest ⟨p, HeZhangBasis.greatest_of_mem_all U hcofinal hp⟩
  obtain ⟨V, K, hVne, hVK, hKU, hK, _, hmin⟩ :=
    HeZhangBasis.exists_compact_neighborhoods hlc U hUne
  obtain ⟨γ, hγ, hbound⟩ := source_rank_bound hP hcore hsecond U K hK hanti hempty
  have hdense : Dense (HeZhangPruning.stage K U γ) := dense_iff_closure_eq.mpr
    (HeZhangPruning.stage_closure_eq_univ hP hcore hirr K U V hanti hUne
      hcofinal hVne hVK hKU hmin γ hγ)
  obtain ⟨s, hs⟩ := hdense.inter_open_nonempty (U 0) (U 0).isOpen (hUne 0)
  obtain ⟨z, _, hzpoint⟩ := source_tag_cover U K 0 s
    (HeZhangPruning.stage_subset_seed K U γ hs.2) hs.1
  have hz : taggedPoint U K z ∈ HeZhangPruning.stage K U γ := hzpoint.symm ▸ hs.2
  have hrank := source_stage_rank_lower hP U K hanti hempty γ z hz
  exact (not_lt_of_ge hrank) (hbound z)

/-- He–Zhang Theorem 4.13, with precisely the dcpo, local compactness and
second-countability hypotheses. In particular, continuity, coherence,
well-filteredness and meet-continuity are not added. -/
theorem theorem_4_13 (hP : IsDcpo P) (hlc : ScottLocallyCompact P)
    (hsecond : ScottSecondCountable P) : ScottSober P := by
  intro F hF hirr
  have hFd := HeZhangClosed.closed_isDcpo hP hF
  have hFlc := HeZhangClosed.closed_locallyCompact hP hF hlc
  have hFsecond := HeZhangClosed.closed_secondCountable hP hF hsecond
  have hFirr := HeZhangClosed.closed_irreducible_univ hP hF hirr
  obtain ⟨p, hp⟩ := irreducible_has_greatest hFd hFlc hFsecond hFirr
  have hF_eq : closure ({p.val} : Set P) = F := by
    rw [scott_closure_singleton]
    apply Set.Subset.antisymm
    · intro x hxp
      exact ((isClosed_scott_iff _).mp hF).1 hxp p.property
    · intro x hx
      exact hp ⟨x, hx⟩
  refine ⟨p.val, hF_eq, ?_⟩
  intro q hq
  rw [scott_closure_singleton] at hq
  have hqF : q ∈ F := hq ▸ (show q ∈ Set.Iic q from le_rfl)
  apply le_antisymm
  · exact hp ⟨q, hqF⟩
  · have hpF : p.val ∈ Set.Iic q := hq.symm ▸ p.property
    exact hpF

/-- The previously unproved external proposition, now supplied with an
actual universe-polymorphic proof. This declaration has no extra premise. -/
theorem secondCountableLocallyCompactDcpoSobriety :
    SecondCountableLocallyCompactDcpoSobriety.{u} := by
  intro P order hP hsecond hlc
  exact theorem_4_13 hP hlc hsecond

end

end CoreCompactSimplified.HeZhang
