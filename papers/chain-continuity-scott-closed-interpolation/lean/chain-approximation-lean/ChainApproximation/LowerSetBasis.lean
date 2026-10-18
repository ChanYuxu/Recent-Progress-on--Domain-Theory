import ChainApproximation.FiniteUpper

/-!
# Compact and countable bases of lower-set lattices

Source preliminaries and Sections 4.2 and 4.5. Algebraicity, countable basis,
chain continuity, and relation equality are proved as separate properties.
-/

set_option autoImplicit false

universe u

namespace ChainApproximation

open Set

def Compact {P : Type u} [PartialOrder P] (p : P) : Prop := WayBelow p p

def IsAlgebraic (P : Type u) [PartialOrder P] : Prop :=
  IsDcpo P ∧ ∀ p : P, NonemptyDirected {a | Compact a ∧ a ≤ p} ∧
    IsLUB {a | Compact a ∧ a ≤ p} p

def IsBasis {P : Type u} [PartialOrder P] (B : Set P) : Prop :=
  ∀ p : P, NonemptyDirected (B ∩ waySection p) ∧ IsLUB (B ∩ waySection p) p

def IsCountablyBased (P : Type u) [PartialOrder P] : Prop :=
  IsContinuous P ∧ ∃ B : Set P, B.Countable ∧ IsBasis B

/-- The complete distributive law, with arbitrary dependent families of
indices at the carrier universe. This is a property of the given lattice. -/
def IsCompletelyDistributive (M : Type u) [CompleteLattice M] : Prop :=
  ∀ (ι : Type u) (κ : ι → Type u) (f : ∀ i, κ i → M),
    (⨅ i, ⨆ j, f i j) = ⨆ g : (∀ i, κ i), ⨅ i, f i (g i)

variable {Q : Type u} [PartialOrder Q]

theorem lowerSet_completelyDistributive : IsCompletelyDistributive (LowerSet Q) := by
  intro ι κ f
  exact iInf_iSup_eq

theorem finiteGenerator_wayBelow (F : Finset Q) {E : LowerSet Q} (hFE : (F : Set Q) ⊆ E) :
    WayBelow (lowerClosure (F : Set Q)) E := by
  intro D hD s hs hEs
  have hFsup : (F : Set Q) ⊆ (sSup D : LowerSet Q) := by
    rw [← hs.unique (isLUB_sSup D)]
    exact hFE.trans hEs
  obtain ⟨B, hB, hFB⟩ := finite_subset_directed_sup hD F hFsup
  exact ⟨B, hB, lowerClosure_le.mpr hFB⟩

theorem finiteGenerator_compact (F : Finset Q) : Compact (lowerClosure (F : Set Q)) :=
  finiteGenerator_wayBelow F subset_lowerClosure

theorem wayBelow_iff_finiteGenerator_le (A E : LowerSet Q) :
    WayBelow A E ↔ ∃ F : Finset Q, (F : Set Q) ⊆ E ∧ A ≤ lowerClosure (F : Set Q) := by
  constructor
  · intro hAE
    obtain ⟨_, ⟨F, hFE, rfl⟩, hAF⟩ := hAE (finiteGenerators E) (finiteGenerators_directed E)
      E (finiteGenerators_lub E) le_rfl
    exact ⟨F, hFE, hAF⟩
  · rintro ⟨F, hFE, hAF⟩
    exact (finiteGenerator_wayBelow F hFE).mono hAF le_rfl

theorem compact_iff_finitely_generated (A : LowerSet Q) :
    Compact A ↔ ∃ F : Finset Q, (F : Set Q) ⊆ A ∧ A = lowerClosure (F : Set Q) := by
  constructor
  · intro hA
    obtain ⟨F, hFA, hAF⟩ := (wayBelow_iff_finiteGenerator_le A A).mp hA
    exact ⟨F, hFA, le_antisymm hAF (lowerClosure_le.mpr hFA)⟩
  · rintro ⟨F, _, rfl⟩
    exact finiteGenerator_compact F

theorem finiteGenerators_eq_compact_section (E : LowerSet Q) :
    finiteGenerators E = {A | Compact A ∧ A ≤ E} := by
  ext A
  constructor
  · rintro ⟨F, hFE, rfl⟩
    exact ⟨finiteGenerator_compact F, lowerClosure_le.mpr hFE⟩
  · rintro ⟨hA, hAE⟩
    obtain ⟨F, hFA, hEq⟩ := (compact_iff_finitely_generated A).mp hA
    exact ⟨F, hFA.trans hAE, hEq⟩

theorem lowerSet_algebraic : IsAlgebraic (LowerSet Q) := by
  refine ⟨completeLattice_dcpo, ?_⟩
  intro E
  rw [← finiteGenerators_eq_compact_section]
  exact ⟨finiteGenerators_directed E, finiteGenerators_lub E⟩

theorem lowerSet_continuous : IsContinuous (LowerSet Q) := by
  classical
  refine ⟨completeLattice_dcpo, ?_⟩
  intro E
  constructor
  · refine ⟨⟨lowerClosure ((∅ : Finset Q) : Set Q), finiteGenerator_wayBelow ∅ (by simp)⟩, ?_⟩
    intro A hA B hB
    obtain ⟨F, hFE, hAF⟩ := (wayBelow_iff_finiteGenerator_le A E).mp hA
    obtain ⟨G, hGE, hBG⟩ := (wayBelow_iff_finiteGenerator_le B E).mp hB
    have hH : ((F ∪ G : Finset Q) : Set Q) ⊆ E := by
      simpa only [Finset.coe_union, Set.union_subset_iff] using And.intro hFE hGE
    exact ⟨lowerClosure ((F ∪ G : Finset Q) : Set Q), finiteGenerator_wayBelow _ hH,
      hAF.trans (lowerClosure_finset_mono Finset.subset_union_left),
      hBG.trans (lowerClosure_finset_mono Finset.subset_union_right)⟩
  · refine ⟨fun _ h ↦ h.le, ?_⟩
    intro B hB
    apply (finiteGenerators_lub E).2
    rintro _ ⟨F, hFE, rfl⟩
    exact hB (finiteGenerator_wayBelow F hFE)

def generatedBasis (Q : Type u) [PartialOrder Q] : Set (LowerSet Q) :=
  Set.range (fun F : Finset Q ↦ lowerClosure (F : Set Q))

theorem generatedBasis_section (E : LowerSet Q) :
    generatedBasis Q ∩ waySection E = finiteGenerators E := by
  ext A
  constructor
  · rintro ⟨⟨F, rfl⟩, hFE⟩
    exact ⟨F, subset_lowerClosure.trans hFE.le, rfl⟩
  · rintro ⟨F, hFE, rfl⟩
    exact ⟨Set.mem_range_self F, finiteGenerator_wayBelow F hFE⟩

theorem generatedBasis_isBasis : IsBasis (generatedBasis Q) := by
  intro E
  rw [generatedBasis_section]
  exact ⟨finiteGenerators_directed E, finiteGenerators_lub E⟩

theorem lowerSet_countablyBased [Countable Q] : IsCountablyBased (LowerSet Q) :=
  ⟨lowerSet_continuous, generatedBasis Q, Set.countable_range _, generatedBasis_isBasis⟩

theorem finiteGenerators_countable [Countable Q] (E : LowerSet Q) : (finiteGenerators E).Countable :=
  (Set.countable_range (fun F : Finset Q ↦ lowerClosure (F : Set Q))).mono
    (by rintro _ ⟨F, _, rfl⟩; exact Set.mem_range_self F)

theorem lowerSet_nat_approximation [Countable Q] (E : LowerSet Q) :
    ∃ f : ℕ → LowerSet Q, Monotone f ∧ (∀ n, f n ∈ finiteGenerators E) ∧
      IsLUB (Set.range f) E := by
  obtain ⟨f, hf, hmem, hcof⟩ := countable_directed_cofinal_chain (finiteGenerators_directed E)
    (finiteGenerators_countable E)
  refine ⟨f, hf, hmem, ?_, ?_⟩
  · rintro _ ⟨n, rfl⟩
    exact (finiteGenerators_lub E).1 (hmem n)
  · intro B hB
    apply (finiteGenerators_lub E).2
    intro A hA
    obtain ⟨n, hAn⟩ := hcof A hA
    exact hAn.trans (hB (Set.mem_range_self _))

theorem lowerSet_chainBelow_iff_wayBelow [Countable Q] (A E : LowerSet Q) :
    ChainBelow A E ↔ WayBelow A E := by
  refine ⟨fun hAE ↦ ?_, fun hAE ↦ hAE.chainBelow completeLattice_dcpo⟩
  obtain ⟨f, hf, hmem, hLub⟩ := lowerSet_nat_approximation E
  obtain ⟨_, ⟨n, rfl⟩, hAn⟩ := (chainBelow_iff_sup completeLattice_dcpo A E).mp hAE
    (Set.range f) ⟨Set.range_nonempty _, hf.isChain_range⟩ E hLub le_rfl
  obtain ⟨F, hFE, hEq⟩ := hmem n
  exact (finiteGenerator_wayBelow F hFE).mono (hEq ▸ hAn) le_rfl

theorem lowerSet_chainContinuous [Countable Q] : IsChainContinuous (LowerSet Q) := by
  intro E
  obtain ⟨f, hf, hmem, hLub⟩ := lowerSet_nat_approximation E
  have hsect : chainSection E = lowerHull (Set.range f) := by
    ext A
    constructor
    · intro hAE
      exact (chainBelow_iff_sup completeLattice_dcpo A E).mp hAE
        (Set.range f) ⟨Set.range_nonempty _, hf.isChain_range⟩ E hLub le_rfl
    · rintro ⟨_, ⟨n, rfl⟩, hAn⟩
      obtain ⟨F, hFE, hEq⟩ := hmem n
      exact ((finiteGenerator_wayBelow F hFE).mono (hEq ▸ hAn) le_rfl).chainBelow completeLattice_dcpo
  refine ⟨⟨Set.range f, ⟨Set.range_nonempty _, hf.isChain_range⟩, hsect⟩, ?_⟩
  have heq : chainSection E = waySection E := by
    ext A
    exact lowerSet_chainBelow_iff_wayBelow A E
  rw [heq]
  exact (lowerSet_continuous.2 E).2

theorem lowerSet_chain_interpolates [Countable Q] : Interpolates (ChainBelow (P := LowerSet Q)) := by
  intro A E hAE
  obtain ⟨F, hFE, hAF⟩ := (wayBelow_iff_finiteGenerator_le A E).mp
    ((lowerSet_chainBelow_iff_wayBelow A E).mp hAE)
  exact ⟨lowerClosure (F : Set Q),
    ((finiteGenerator_compact F).mono hAF le_rfl).chainBelow completeLattice_dcpo,
    (finiteGenerator_wayBelow F hFE).chainBelow completeLattice_dcpo⟩

theorem finite_lowerSet_wayBelow {A E : LowerSet Q} (hA : (A : Set Q).Finite) (hAE : A ≤ E) :
    WayBelow A E := by
  have hEq : lowerClosure (hA.toFinset : Set Q) = A := by
    rw [Set.Finite.coe_toFinset]
    exact LowerSet.lowerClosure A
  rw [← hEq]
  apply finiteGenerator_wayBelow
  simpa only [Set.Finite.coe_toFinset] using hAE

theorem lowerClosure_finite_of_principal_finite (hprincipal : ∀ q : Q, (Set.Iic q).Finite)
    (F : Finset Q) : (lowerClosure (F : Set Q) : Set Q).Finite := by
  rw [coe_lowerClosure]
  exact F.finite_toSet.biUnion (fun q _ ↦ hprincipal q)

theorem lowerSet_wayBelow_iff_finite (hprincipal : ∀ q : Q, (Set.Iic q).Finite)
    (A E : LowerSet Q) : WayBelow A E ↔ A ≤ E ∧ (A : Set Q).Finite := by
  constructor
  · intro hAE
    obtain ⟨F, _, hAF⟩ := (wayBelow_iff_finiteGenerator_le A E).mp hAE
    exact ⟨hAE.le, (lowerClosure_finite_of_principal_finite hprincipal F).subset hAF⟩
  · rintro ⟨hAE, hA⟩
    exact finite_lowerSet_wayBelow hA hAE

end ChainApproximation
