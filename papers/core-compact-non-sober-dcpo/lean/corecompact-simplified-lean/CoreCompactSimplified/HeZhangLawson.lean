import CoreCompactSimplified.HeZhangLawsonBasic

/-!
He--Zhang Lemma 4.6, arXiv:2610.17759v1, Section 4:
the Lawson space of the open-set lattice of a second-countable core-compact
space is compact and metrizable.

We follow the printed finite-union basis argument. `finiteBasisUnion F` is
the paper's `V_F`. The complements of their principal upper sets form a
countable *subbasis* for the lower topology. The printed Claim 2 calls this
family a base but proves the subbasis assertion; finite intersections below
make the omitted basis step explicit. No source hypothesis is strengthened.
-/

set_option autoImplicit false

universe u

namespace CoreCompactSimplified.HeZhangLawson

open Set TopologicalSpace CoreCompactNonSober Filter
open scoped Topology

noncomputable section

variable {X : Type u} [TopologicalSpace X] [SecondCountableTopology X]

/-- The countable topological basis, recorded as actual open sets. -/
def basicOpens : Set (Opens X) :=
  {U | (U : Set X) ∈ countableBasis X}

theorem basicOpens_countable : (basicOpens (X := X)).Countable :=
  (countable_countableBasis X).preimage SetLike.coe_injective

instance basicOpens_countableType : Countable (basicOpens (X := X)) :=
  (basicOpens_countable (X := X)).to_subtype

local instance : DecidableEq (basicOpens (X := X)) := Classical.decEq _

/-- The exact finite unions `V_F` in the proof of Lemma 4.6. The empty
finite union is retained, so the directed families are nonempty. -/
def finiteBasisUnion (F : Finset (basicOpens (X := X))) : Opens X :=
  F.sup Subtype.val

theorem finiteBasisUnion_coe (F : Finset (basicOpens (X := X))) :
    (finiteBasisUnion F : Set X) = ⋃ B ∈ F, (B.val : Set X) := by
  simp [finiteBasisUnion, Finset.sup_eq_iSup]

theorem finiteBasisUnion_empty : finiteBasisUnion (X := X) ∅ = ⊥ := rfl

theorem finiteBasisUnion_union (F G : Finset (basicOpens (X := X))) :
    finiteBasisUnion (F ∪ G) = finiteBasisUnion F ⊔ finiteBasisUnion G := by
  classical
  exact Finset.sup_union

theorem basicOpens_covers (U : Opens X) {x : X} (hx : x ∈ U) :
    ∃ B : basicOpens (X := X), x ∈ (B.val : Set X) ∧ B.val ≤ U := by
  obtain ⟨V, hVB, hxV, hVU⟩ :=
    (isBasis_countableBasis X).exists_subset_of_mem_open hx U.isOpen
  exact ⟨⟨⟨V, isOpen_of_mem_countableBasis hVB⟩, hVB⟩, hxV, hVU⟩

/-- All finite unions below `U` form the directed union used in Claim 1. -/
theorem finiteBasisUnionsBelow_directed_lub (U : Opens X) :
    NonemptyDirected {V : Opens X |
      ∃ F : Finset (basicOpens (X := X)), finiteBasisUnion F = V ∧ V ≤ U} ∧
    IsLUB {V : Opens X |
      ∃ F : Finset (basicOpens (X := X)), finiteBasisUnion F = V ∧ V ≤ U} U := by
  classical
  constructor
  · constructor
    · exact ⟨⊥, ∅, rfl, bot_le⟩
    · rintro V ⟨F, rfl, hFU⟩ W ⟨G, rfl, hGU⟩
      refine ⟨finiteBasisUnion (X := X) (F ∪ G), ⟨F ∪ G, rfl, ?_⟩, ?_, ?_⟩
      · rw [finiteBasisUnion_union]
        exact sup_le hFU hGU
      · rw [finiteBasisUnion_union]
        exact le_sup_left
      · rw [finiteBasisUnion_union]
        exact le_sup_right
  · constructor
    · rintro V ⟨_, _, hVU⟩
      exact hVU
    · intro W hW x hxU
      obtain ⟨B, hxB, hBU⟩ := basicOpens_covers U hxU
      have hsingleton : finiteBasisUnion {B} = B.val := Finset.sup_singleton
      have hBW : B.val ≤ W := hW ⟨{B}, hsingleton, hBU⟩
      exact hBW hxB

/-- The interpolation and finite-subcover step from Claim 1. -/
theorem exists_finiteBasisUnion_between (hX : IsCoreCompact X)
    {V U : Opens X} (hVU : OpenWayBelow V U) :
    ∃ F : Finset (basicOpens (X := X)),
      OpenWayBelow V (finiteBasisUnion F) ∧ OpenWayBelow (finiteBasisUnion F) U := by
  obtain ⟨W, hVW, hWU⟩ := openWayBelow_interpolate hX hVU
  obtain ⟨A, hVA, hAW⟩ := openWayBelow_interpolate hX hVW
  obtain ⟨hdir, hlub⟩ := finiteBasisUnionsBelow_directed_lub W
  obtain ⟨B, ⟨F, rfl, hFW⟩, hAF⟩ := hAW _ hdir.1 hdir.2
    (le_of_eq ((isLUB_sSup _).unique hlub).symm)
  exact ⟨F, openWayBelow_mono le_rfl hVA hAF,
    openWayBelow_mono hFW hWU le_rfl⟩

/-- The finite-union approximants have supremum `U`, exactly as in Claim 2. -/
theorem finiteBasisUnion_wayBelow_lub (hX : IsCoreCompact X) (U : Opens X) :
    IsLUB {V : Opens X |
      ∃ F : Finset (basicOpens (X := X)), finiteBasisUnion F = V ∧ OpenWayBelow V U} U := by
  constructor
  · rintro V ⟨_, _, hVU⟩
    exact hVU.le
  · intro W hW x hxU
    obtain ⟨V, hxV, hVU⟩ := hX U x hxU
    obtain ⟨F, hVF, hFU⟩ := exists_finiteBasisUnion_between hX hVU
    exact (hW ⟨F, rfl, hFU⟩) (hVF.le hxV)

def scottFiniteUnionBasis : Set (Set (Opens X)) :=
  range (fun F : Finset (basicOpens (X := X)) ↦
    {U : Opens X | OpenWayBelow (finiteBasisUnion F) U})

theorem scottFiniteUnionBasis_countable : (scottFiniteUnionBasis (X := X)).Countable :=
  countable_range _

/-- He--Zhang Lemma 4.6, Claim 1. -/
theorem scottFiniteUnionBasis_isTopologicalBasis (hX : IsCoreCompact X) :
    @IsTopologicalBasis (Opens X) (Topology.scott (Opens X) univ)
      (scottFiniteUnionBasis (X := X)) := by
  letI : TopologicalSpace (Opens X) := Topology.scott (Opens X) univ
  have hcont : IsContinuousDcpo (Opens X) := coreCompact_iff_continuous_opens.mp hX
  apply isTopologicalBasis_of_isOpen_of_nhds
  · rintro S ⟨F, rfl⟩
    convert isOpen_wayAbove hcont (finiteBasisUnion F) using 1
    ext U
    exact openWayBelow_iff_elementWayBelow _ _
  · intro U S hUS hS
    obtain ⟨V, hVU, hVS⟩ := ((isOpen_scott_iff S).mp hS).2
      {V : Opens X | ElementWayBelow V U} (hcont.2 U).1 U (hcont.2 U).2 hUS
    obtain ⟨F, hVF, hFU⟩ := exists_finiteBasisUnion_between hX
      ((openWayBelow_iff_elementWayBelow _ _).mpr hVU)
    refine ⟨{W : Opens X | OpenWayBelow (finiteBasisUnion F) W}, ⟨F, rfl⟩, hFU, ?_⟩
    intro W hFW
    exact ((isOpen_scott_iff S).mp hS).1 (hVF.le.trans hFW.le) hVS

def lowerFiniteUnionSubbasis : Set (Set (Opens X)) :=
  range (fun F : Finset (basicOpens (X := X)) ↦ (Ici (finiteBasisUnion F))ᶜ)

theorem lowerFiniteUnionSubbasis_countable :
    (lowerFiniteUnionSubbasis (X := X)).Countable := countable_range _

/-- The explicit intersection identity established in the printed Claim 2. -/
theorem principalUpper_eq_inter_finiteBasisUnions (hX : IsCoreCompact X) (U : Opens X) :
    Ici U = ⋂ F : Finset (basicOpens (X := X)),
      ⋂ (_ : OpenWayBelow (finiteBasisUnion F) U), Ici (finiteBasisUnion F) := by
  ext W
  simp only [mem_Ici, mem_iInter]
  constructor
  · intro hUW F hFU
    exact hFU.le.trans hUW
  · intro h
    apply (finiteBasisUnion_wayBelow_lub hX U).2
    rintro V ⟨F, rfl, hFU⟩
    exact h F hFU

/-- Claim 2 proves a countable subbasis; the subsequent finite-intersection
basis theorem below records the necessary omitted basis completion. -/
theorem lower_eq_generateFrom_finiteUnionSubbasis (hX : IsCoreCompact X) :
    Topology.lower (Opens X) = generateFrom (lowerFiniteUnionSubbasis (X := X)) := by
  apply le_antisymm
  · apply le_generateFrom_iff_subset_isOpen.mpr
    rintro S ⟨F, rfl⟩
    exact isOpen_generateFrom_of_mem ⟨finiteBasisUnion F, rfl⟩
  · letI : TopologicalSpace (Opens X) := generateFrom (lowerFiniteUnionSubbasis (X := X))
    apply le_generateFrom
    rintro S ⟨U, rfl⟩
    rw [principalUpper_eq_inter_finiteBasisUnions hX U]
    simp only [compl_iInter]
    apply isOpen_iUnion
    intro F
    apply isOpen_iUnion
    intro _
    exact isOpen_generateFrom_of_mem ⟨F, rfl⟩

def lawsonFiniteUnionSubbasis : Set (Set (Opens X)) :=
  lowerFiniteUnionSubbasis (X := X) ∪ scottFiniteUnionBasis (X := X)

theorem lawsonFiniteUnionSubbasis_countable :
    (lawsonFiniteUnionSubbasis (X := X)).Countable :=
  lowerFiniteUnionSubbasis_countable.union scottFiniteUnionBasis_countable

theorem lawson_eq_generateFrom_finiteUnionSubbasis (hX : IsCoreCompact X) :
    Topology.lawson (Opens X) = generateFrom (lawsonFiniteUnionSubbasis (X := X)) := by
  have hsc : Topology.scott (Opens X) univ =
      generateFrom (scottFiniteUnionBasis (X := X)) :=
    @IsTopologicalBasis.eq_generateFrom _ (Topology.scott (Opens X) univ) _
      (scottFiniteUnionBasis_isTopologicalBasis hX)
  rw [lawsonFiniteUnionSubbasis, generateFrom_union,
    ← lower_eq_generateFrom_finiteUnionSubbasis hX, ← hsc]
  rfl

/-- The actual basis is obtained by finite intersections of the countable
subbasis, making the source's terminology correction mathematically explicit. -/
theorem lawson_finiteIntersectionBasis (hX : IsCoreCompact X) :
    @IsTopologicalBasis (Opens X) (Topology.lawson (Opens X))
      ((fun f : Set (Set (Opens X)) ↦ ⋂₀ f) ''
        {f | f.Finite ∧ f ⊆ lawsonFiniteUnionSubbasis (X := X)}) := by
  letI : TopologicalSpace (Opens X) := Topology.lawson (Opens X)
  exact isTopologicalBasis_of_subbasis (lawson_eq_generateFrom_finiteUnionSubbasis hX)

theorem lawson_finiteIntersectionBasis_countable :
    (((fun f : Set (Set (Opens X)) ↦ ⋂₀ f) ''
      {f | f.Finite ∧ f ⊆ lawsonFiniteUnionSubbasis (X := X)})).Countable :=
  (countable_setOf_finite_subset lawsonFiniteUnionSubbasis_countable).image _

theorem opensLawson_secondCountable (hX : IsCoreCompact X) :
    @SecondCountableTopology (Opens X) (Topology.lawson (Opens X)) := by
  rw [lawson_eq_generateFrom_finiteUnionSubbasis hX]
  exact SecondCountableTopology.mk' lawsonFiniteUnionSubbasis_countable

/-- Compact Hausdorff second-countable spaces are metrizable: the cited
He--Zhang Lemma 4.5, as a direct application of mathlib's Urysohn theorem. -/
theorem compactHausdorff_secondCountable_metrizable
    {Y : Type u} [TopologicalSpace Y] [CompactSpace Y] [T2Space Y]
    [SecondCountableTopology Y] : MetrizableSpace Y := by infer_instance

/-- The full biconditional in the cited Lemma 4.5. Compactness is used in
the converse; no general assertion that every metric space is second countable
is made. -/
theorem compactHausdorff_metrizable_iff_secondCountable
    {Y : Type u} [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] :
    MetrizableSpace Y ↔ SecondCountableTopology Y := by
  constructor
  · intro hY
    letI : MetrizableSpace Y := hY
    infer_instance
  · intro hY
    letI : SecondCountableTopology Y := hY
    exact compactHausdorff_secondCountable_metrizable

/-- The cited metric-space background Lemma 4.7, in fact valid already
for a pseudometric space. -/
theorem isClosed_dist_ge {Y : Type u} [PseudoMetricSpace Y] (r : ℝ) :
    IsClosed {p : Y × Y | r ≤ dist p.1 p.2} :=
  isClosed_le continuous_const (continuous_fst.dist continuous_snd)

theorem metric_isClosed_dist_ge {Y : Type u} [MetricSpace Y] (r : ℝ) :
    IsClosed {p : Y × Y | r ≤ dist p.1 p.2} := isClosed_dist_ge r

/-- He--Zhang Lemma 4.6 in its stronger ordinary-topological-space interface.
Specializing `X` to a Scott space gives the printed dcpo statement. -/
theorem opensLawson_compact_hausdorff_metrizable (hX : IsCoreCompact X) :
    @CompactSpace (Opens X) (Topology.lawson (Opens X)) ∧
    @T2Space (Opens X) (Topology.lawson (Opens X)) ∧
    @SecondCountableTopology (Opens X) (Topology.lawson (Opens X)) ∧
    @MetrizableSpace (Opens X) (Topology.lawson (Opens X)) := by
  letI : TopologicalSpace (Opens X) := Topology.lawson (Opens X)
  letI : CompactSpace (Opens X) := lawson_compactSpace
  letI : T2Space (Opens X) := lawson_t2Space (coreCompact_iff_continuous_opens.mp hX)
  letI : SecondCountableTopology (Opens X) := opensLawson_secondCountable hX
  exact ⟨inferInstance, inferInstance, inferInstance,
    compactHausdorff_secondCountable_metrizable⟩

/-- Source-facing Lemma 4.6 with the printed dcpo, core-compact Scott-space,
and second-countable Scott-space hypotheses. The dcpo hypothesis is retained
even though the open-lattice proof above works for arbitrary spaces. -/
theorem scottOpens_lawson_compact_hausdorff_metrizable
    {P : Type u} [PartialOrder P] (_hP : IsDcpo P)
    (hcore : ScottCoreCompact P) (hsecond : ScottSecondCountable P) :
    @SecondCountableTopology (ScottOpens P) (Topology.lawson (ScottOpens P)) ∧
    @CompactSpace (ScottOpens P) (Topology.lawson (ScottOpens P)) ∧
    @T2Space (ScottOpens P) (Topology.lawson (ScottOpens P)) ∧
    @MetrizableSpace (ScottOpens P) (Topology.lawson (ScottOpens P)) := by
  letI : TopologicalSpace P := scottTopology P
  letI : SecondCountableTopology P := hsecond
  obtain ⟨hcompact, ht2, hcount, hmetric⟩ :=
    opensLawson_compact_hausdorff_metrizable hcore
  exact ⟨hcount, hcompact, ht2, hmetric⟩

end

end CoreCompactSimplified.HeZhangLawson
