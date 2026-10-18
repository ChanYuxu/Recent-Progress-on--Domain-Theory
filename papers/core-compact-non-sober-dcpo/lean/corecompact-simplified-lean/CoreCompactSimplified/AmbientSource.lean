import CoreCompactSimplified.SourceDefinitions
import CoreCompactSimplified.CoreCompactLattice
import CoreCompactNonSober.AmbientMeetContinuity
import CoreCompactNonSober.AmbientLocalCompactness

/-! Source-facing ambient definitions and the exact real-infimum formulas.
The finite-set encoding is related explicitly to all subsets of the paper's
one-based alphabets; cardinalities of complements, hence capacities, agree. -/

set_option autoImplicit false

namespace CoreCompactSimplified

open Set TopologicalSpace CoreCompactNonSober CoreCompactNonSober.Ambient

noncomputable instance paperAlphabetFintype (j : Coordinate) : Fintype (PaperAlphabet j) :=
  Fintype.ofEquiv (Alphabet j) (alphabetLabelEquiv j)

noncomputable def paperSubsetEquiv (j : Coordinate) :
    Finset (Alphabet j) ≃ Set (PaperAlphabet j) :=
  (alphabetLabelEquiv j).finsetCongr.trans Fintype.finsetEquivSet

@[simp] theorem paperSubsetEquiv_mem (j : Coordinate) (A : Finset (Alphabet j))
    (z : Alphabet j) : alphabetLabelEquiv j z ∈ paperSubsetEquiv j A ↔ z ∈ A := by
  classical
  change alphabetLabelEquiv j z ∈ A.map (alphabetLabelEquiv j).toEmbedding ↔ z ∈ A
  simp

theorem paperSubsetEquiv_subset_iff (j : Coordinate) (A B : Finset (Alphabet j)) :
    paperSubsetEquiv j A ⊆ paperSubsetEquiv j B ↔ A ⊆ B := by
  constructor
  · intro h z hz
    exact (paperSubsetEquiv_mem j B z).mp (h ((paperSubsetEquiv_mem j A z).mpr hz))
  · intro h z hz
    obtain ⟨a, rfl⟩ := (alphabetLabelEquiv j).surjective z
    exact (paperSubsetEquiv_mem j B a).mpr (h ((paperSubsetEquiv_mem j A a).mp hz))

noncomputable def paperHoleCount (j : Coordinate) (A : Set (PaperAlphabet j)) : ℕ := by
  classical
  exact (Finset.univ \ A.toFinset).card

theorem paperHoleCount_relabel (j : Coordinate) (A : Finset (Alphabet j)) :
    paperHoleCount j (paperSubsetEquiv j A) = holeCount j A := by
  classical
  have heq : (Finset.univ \ (paperSubsetEquiv j A).toFinset) =
      (Finset.univ \ A).map (alphabetLabelEquiv j).toEmbedding := by
    ext z
    obtain ⟨a, rfl⟩ := (alphabetLabelEquiv j).surjective z
    simp only [Finset.mem_sdiff, Finset.mem_univ, Set.mem_toFinset, true_and,
      paperSubsetEquiv_mem]
    simp
  rw [paperHoleCount, heq, Finset.card_map]
  rfl

noncomputable def paperCapacity (j : Coordinate) (A : Set (PaperAlphabet j)) : ℝ :=
  max 0 (1 - (1 / (j.val : ℝ)) * Real.logb 2 (1 + (paperHoleCount j A : ℝ)))

@[simp] theorem paperCapacity_relabel (j : Coordinate) (A : Finset (Alphabet j)) :
    paperCapacity j (paperSubsetEquiv j A) = capacity j A := by
  rw [paperCapacity, paperHoleCount_relabel]
  rfl

abbrev PaperConfiguration := (j : Coordinate) → Set (PaperAlphabet j)

noncomputable def paperConfigurationEquiv : Configuration ≃ PaperConfiguration :=
  Equiv.piCongrRight fun j ↦ paperSubsetEquiv j

/-- The printed `c(A) = inf_j c_j(A_j)`, as an actual real infimum. -/
noncomputable def configurationCapacity (A : Configuration) : ℝ :=
  sInf (Set.range (fun j : Coordinate ↦ capacity j (A j)))

private theorem capacity_range_bddBelow (A : Configuration) :
    BddBelow (Set.range (fun j : Coordinate ↦ capacity j (A j))) :=
  ⟨0, by rintro _ ⟨j, rfl⟩; exact capacity_nonneg j (A j)⟩

theorem le_configurationCapacity_iff (A : Configuration) (t : ℝ) :
    t ≤ configurationCapacity A ↔ ∀ j : Coordinate, t ≤ capacity j (A j) := by
  constructor
  · intro h j
    exact h.trans (csInf_le (capacity_range_bddBelow A) ⟨j, rfl⟩)
  · intro h
    apply le_csInf (Set.range_nonempty (fun j : Coordinate ↦ capacity j (A j)))
    rintro _ ⟨j, rfl⟩
    exact h j

theorem configurationCapacity_bounds (A : Configuration) :
    0 ≤ configurationCapacity A ∧ configurationCapacity A ≤ 1 := by
  refine ⟨(le_configurationCapacity_iff A 0).mpr (fun j ↦ capacity_nonneg j (A j)), ?_⟩
  let j : Coordinate := ⟨2, le_rfl⟩
  exact ((le_configurationCapacity_iff A _).mp le_rfl j).trans (capacity_le_one j (A j))

theorem configurationCapacity_mono : Monotone configurationCapacity := by
  intro A B hAB
  apply (le_configurationCapacity_iff B _).mpr
  intro j
  exact ((le_configurationCapacity_iff A _).mp le_rfl j).trans (capacity_monotone j (hAB j))

theorem carrier_capacity_iff (t : Height) (A : Configuration) :
    (∀ j : Coordinate, (t : ℝ) ≤ capacity j (A j)) ↔ (t : ℝ) ≤ configurationCapacity A :=
  (le_configurationCapacity_iff A t).symm

def PaperCarrier := {p : Height × PaperConfiguration //
  ∀ j : Coordinate, (p.1 : ℝ) ≤ paperCapacity j (p.2 j)}

instance : PartialOrder PaperCarrier := inferInstanceAs
  (PartialOrder {p : Height × PaperConfiguration //
    ∀ j : Coordinate, (p.1 : ℝ) ≤ paperCapacity j (p.2 j)})

/-- All one-based paper configurations, with precisely the printed capacity
constraints and product order, are represented by the Lean ambient carrier. -/
noncomputable def paperCarrierOrderIso : Carrier ≃o PaperCarrier where
  toFun p := ⟨(p.val.1, paperConfigurationEquiv p.val.2), by
    intro j
    change height p ≤ paperCapacity j (paperSubsetEquiv j (configuration p j))
    rw [paperCapacity_relabel]
    exact p.property j⟩
  invFun q := ⟨(q.val.1, paperConfigurationEquiv.symm q.val.2), by
    intro j
    have hq := q.property j
    have heq := paperCapacity_relabel j ((paperSubsetEquiv j).symm (q.val.2 j))
    rw [(paperSubsetEquiv j).apply_symm_apply] at heq
    exact heq ▸ hq⟩
  left_inv p := by
    apply Subtype.ext
    exact Prod.ext rfl (paperConfigurationEquiv.symm_apply_apply p.val.2)
  right_inv q := by
    apply Subtype.ext
    exact Prod.ext rfl (paperConfigurationEquiv.apply_symm_apply q.val.2)
  map_rel_iff' := by
    intro p q
    change ((p.val.1 ≤ q.val.1) ∧
      ∀ j, paperSubsetEquiv j (configuration p j) ⊆ paperSubsetEquiv j (configuration q j)) ↔
      (height p ≤ height q ∧ ∀ j, configuration p j ⊆ configuration q j)
    simp only [paperSubsetEquiv_subset_iff]
    rfl

theorem capacityHeight_iInf_real (A : Configuration) :
    ((⨅ j : Coordinate, capacityHeight j (A j) : Height) : ℝ) = configurationCapacity A := by
  rw [Set.Icc.coe_iInf (by norm_num : (0 : ℝ) ≤ 1)]
  rfl

/-- The literal nonempty-family real-height formula in `eq:meet`. -/
theorem height_sInf_real (E : Set Carrier) (hE : E.Nonempty) :
    height (sInf E) = min (sInf (height '' E)) (configurationCapacity (meetConfiguration E)) := by
  rw [sInf_eq_meet]
  change ((meetHeight E : Height) : ℝ) = _
  change min ((sInf ((fun p : Carrier ↦ p.val.1) '' E) : Height) : ℝ)
    ((⨅ j : Coordinate, capacityHeight j (meetConfiguration E j) : Height) : ℝ) = _
  rw [Set.Icc.coe_sInf (by norm_num : (0 : ℝ) ≤ 1) (hE.image _), capacityHeight_iInf_real]
  rw [Set.image_image]
  rfl

/-- Literal intersection-membership formula, including the nonempty-family
case from the source and with the usual empty-intersection convention. -/
theorem mem_configuration_sInf (E : Set Carrier) (j : Coordinate) (z : Alphabet j) :
    z ∈ configuration (sInf E) j ↔ ∀ p ∈ E, z ∈ configuration p j := by
  rw [configuration_sInf]
  constructor
  · intro hz p hp
    exact (sInf_le (Set.mem_image_of_mem (fun p : Carrier ↦ configuration p j) hp)) hz
  · intro hz
    have hsubset : ({z} : Finset (Alphabet j)) ≤
        sInf ((fun p : Carrier ↦ configuration p j) '' E) := by
      apply le_sInf
      rintro _ ⟨p, hp, rfl⟩ a ha
      have heq : a = z := Finset.mem_singleton.mp ha
      exact heq ▸ hz p hp
    exact hsubset (Finset.mem_singleton_self z)

/-- All assertions in `lem:lattice`, exposing the concrete complete lattice,
the formulas for arbitrary nonempty families, and the auxiliary topology.
The order remains the literal height/configuration product order (`le_iff`). -/
theorem lattice :
    Nonempty (CompleteLattice Carrier) ∧
    (∀ E : Set Carrier, E.Nonempty → height (sSup E) = sSup (height '' E)) ∧
    (∀ (E : Set Carrier) (j : Coordinate) (z : Alphabet j),
      z ∈ configuration (sSup E) j ↔ ∃ p ∈ E, z ∈ configuration p j) ∧
    (∀ E : Set Carrier, E.Nonempty → height (sInf E) =
      min (sInf (height '' E)) (configurationCapacity (meetConfiguration E))) ∧
    (∀ (E : Set Carrier) (j : Coordinate) (z : Alphabet j),
      z ∈ configuration (sInf E) j ↔ ∀ p ∈ E, z ∈ configuration p j) ∧
    (⊥ : Carrier) = bottomPoint ∧
    (⊤ : Carrier) = fullAt ⟨1, by norm_num, le_rfl⟩ ∧
    IsClosed {p : Height × Configuration | ∀ j, (p.1 : ℝ) ≤ capacity j (p.2 j)} ∧
    @CompactSpace Carrier auxiliaryTopology ∧
    @MetrizableSpace Carrier auxiliaryTopology ∧ @T2Space Carrier auxiliaryTopology ∧
    @IsClosed (Carrier × Carrier)
      (@instTopologicalSpaceProd Carrier Carrier auxiliaryTopology auxiliaryTopology)
      {p | p.1 ≤ p.2} ∧
    @Continuous (Carrier × Carrier) Carrier
      (@instTopologicalSpaceProd Carrier Carrier auxiliaryTopology auxiliaryTopology)
      auxiliaryTopology (fun p ↦ p.1 ⊔ p.2) ∧
    @Continuous (Carrier × Carrier) Carrier
      (@instTopologicalSpaceProd Carrier Carrier auxiliaryTopology auxiliaryTopology)
      auxiliaryTopology (fun p ↦ p.1 ⊓ p.2) :=
  ⟨⟨inferInstance⟩, height_sSup, mem_configuration_sSup, height_sInf_real,
    mem_configuration_sInf, bottom_eq_bottomPoint, top_eq_fullAt_one, carrier_isClosed,
    inferInstance, inferInstance, inferInstance, isClosed_le_prod,
    continuous_sup, continuous_inf⟩

/-- The general cited implication is applied to the actual ambient complete
lattice. No custom axiom or extra continuity assumption on `L` is used. -/
theorem ambient_sober : ScottSober Carrier :=
  coreCompact_completeLattice_sober Ambient.scottCoreCompact

theorem loss (j : Coordinate) (A B : Finset (Alphabet j)) (z : Alphabet j) :
    (0 ≤ capacity j A - capacity j (A \ {z}) ∧
      capacity j A - capacity j (A \ {z}) ≤ 1 / (j.val : ℝ)) ∧
    (0 ≤ min (capacity j A) (capacity j B) - capacity j (A ∩ B) ∧
      min (capacity j A) (capacity j B) - capacity j (A ∩ B) ≤ 1 / (j.val : ℝ)) :=
  ⟨capacity_deletion_loss j A z, capacity_intersection_loss j A B⟩

/-- Both statements in the source lemma `lem:scott-ambient`. -/
theorem scott_ambient :
    (∀ U : Set Carrier, @IsOpen Carrier (scottTopology Carrier) U ↔
      @IsOpen Carrier auxiliaryTopology U ∧ IsUpperSet U) ∧
    (∀ x : Carrier, ∀ E : Set Carrier, NonemptyDirected E →
      x ⊓ sSup E = sSup ((fun y : Carrier ↦ x ⊓ y) '' E)) :=
  ⟨isOpen_scott_iff_aux_open_upper, Ambient.inf_sSup⟩

/-- The full topological conclusion and exact printed basis of
`prop:ambient-properties`. -/
theorem ambient_properties :
    ScottCompact Carrier ∧ ScottSecondCountable Carrier ∧
    ScottLocallyCompact Carrier ∧ ScottCoreCompact Carrier ∧ ScottSober Carrier ∧
    (Set.range printedBasicSet).Countable ∧
    @IsTopologicalBasis Carrier (scottTopology Carrier) (Set.range printedBasicSet) :=
  ⟨Ambient.scottCompact, Ambient.scottSecondCountable, Ambient.scottLocallyCompact,
    Ambient.scottCoreCompact, ambient_sober, printedBasicFamily_countable,
    printedBasic_isTopologicalBasis⟩

end CoreCompactSimplified
