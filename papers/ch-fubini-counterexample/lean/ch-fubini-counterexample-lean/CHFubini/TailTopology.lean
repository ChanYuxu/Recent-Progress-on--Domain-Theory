import CHFubini.EventStabilization
import CHFubini.OrdinalStages
import Mathlib.Topology.Separation.Hausdorff

/-! The actual tail refinement from Section 3.2. The open sets are generated
by ordinary ambient opens intersected with ordinal tails. In particular this
does NOT declare arbitrary countable deletions of ambient opens to be open.
The points are the range of the specified sequence with proof fields erased;
`SourcePoint.val` is a proved injection into the ambient space.
-/

set_option autoImplicit false
open Set Topology TopologicalSpace Filter
universe u
namespace CHFubini

def zeroStage : OmegaOneStage := ⟨0, Ordinal.omega_pos 1⟩
instance : Nonempty OmegaOneStage := ⟨zeroStage⟩

structure SourcePoint {X : Type u} (a : OmegaOneStage → X) where
  val : X
  mem_range : val ∈ Set.range a

theorem SourcePoint.val_injective {X : Type u} (a : OmegaOneStage → X) :
    Function.Injective (@SourcePoint.val X a) := by
  rintro ⟨x,hx⟩ ⟨y,hy⟩ h
  cases h
  rfl

def pointAt {X : Type u} (a : OmegaOneStage → X) (γ : OmegaOneStage) : SourcePoint a :=
  ⟨a γ, Set.mem_range_self γ⟩

noncomputable def sourceIndex {X : Type u} {a : OmegaOneStage → X}
    (x : SourcePoint a) : OmegaOneStage := Classical.choose x.mem_range

theorem sourceIndex_spec {X : Type u} {a : OmegaOneStage → X} (x : SourcePoint a) :
    a (sourceIndex x) = x.val := Classical.choose_spec x.mem_range

@[simp] theorem sourceIndex_pointAt {X : Type u} {a : OmegaOneStage → X}
    (ha : Function.Injective a) (γ : OmegaOneStage) : sourceIndex (pointAt a γ) = γ :=
  ha (sourceIndex_spec _)

def sourceTail {X : Type u} (a : OmegaOneStage → X) (β : OmegaOneStage) :
    Set (SourcePoint a) := {x | β ≤ sourceIndex x}

def sourceInitial {X : Type u} (a : OmegaOneStage → X) (β : OmegaOneStage) :
    Set (SourcePoint a) := {x | sourceIndex x < β}

theorem sourceInitial_mono {X : Type u} (a : OmegaOneStage → X) :
    Monotone (sourceInitial a) := fun _ _ hβγ _ hx => hx.trans_le hβγ

theorem sourceInitial_countable {X : Type u} (a : OmegaOneStage → X)
    (β : OmegaOneStage) : (sourceInitial a β).Countable := by
  letI : Countable (Iio β) := (omegaOneStage_Iio_countable β).to_subtype
  let f : sourceInitial a β → Iio β := fun x => ⟨sourceIndex x.val,x.property⟩
  have hf : Function.Injective f := by
    intro x y h
    have hi : sourceIndex x.val = sourceIndex y.val := congrArg Subtype.val h
    apply Subtype.ext
    apply SourcePoint.val_injective a
    rw [← sourceIndex_spec x.val,← sourceIndex_spec y.val,hi]
  letI : Countable (sourceInitial a β) := hf.countable
  exact Set.to_countable _

theorem source_countable_initial_containment {X : Type u} (a : OmegaOneStage → X)
    (C : Set (SourcePoint a)) (hC : C.Countable) :
    ∃ β : OmegaOneStage, C ⊆ sourceInitial a β := by
  obtain ⟨β,hβ⟩ := omegaOneStage_countable_strict_bound
    (sourceIndex '' C) (hC.image sourceIndex)
  exact ⟨β,fun x hx => hβ _ (mem_image_of_mem sourceIndex hx)⟩

theorem sourceTail_eq_initial_compl {X : Type u} (a : OmegaOneStage → X)
    (β : OmegaOneStage) : sourceTail a β = (sourceInitial a β)ᶜ := by
  ext x
  change (β ≤ sourceIndex x) ↔ ¬ sourceIndex x < β
  exact not_lt.symm

def sourceBase {X : Type u} (a : OmegaOneStage → X) (O : Set X)
    (β : OmegaOneStage) : Set (SourcePoint a) := {x | x.val ∈ O ∧ β ≤ sourceIndex x}

/-- The base description of the generated topology, with all topology axioms
proved explicitly. Its equality with `generateFrom` is established below. -/
noncomputable instance sourceTopology {X : Type u} [TopologicalSpace X]
    (a : OmegaOneStage → X) : TopologicalSpace (SourcePoint a) where
  IsOpen U := ∀ x ∈ U, ∃ O : Set X, IsOpen O ∧ ∃ β : OmegaOneStage,
    x ∈ sourceBase a O β ∧ sourceBase a O β ⊆ U
  isOpen_univ := by
    intro x _
    refine ⟨univ,isOpen_univ,zeroStage,⟨mem_univ _,?_⟩,subset_univ _⟩
    change (0 : Ordinal) ≤ (sourceIndex x).val
    exact bot_le
  isOpen_inter := by
    intro U V hU hV x hx
    obtain ⟨O,hO,β,hxO,hOU⟩ := hU x hx.1
    obtain ⟨G,hG,γ,hxG,hGV⟩ := hV x hx.2
    refine ⟨O ∩ G,hO.inter hG,max β γ,⟨⟨hxO.1,hxG.1⟩,max_le hxO.2 hxG.2⟩,?_⟩
    intro y hy
    exact ⟨hOU ⟨hy.1.1,(le_max_left β γ).trans hy.2⟩,
      hGV ⟨hy.1.2,(le_max_right β γ).trans hy.2⟩⟩
  isOpen_sUnion := by
    intro S hS x hx
    obtain ⟨U,hUS,hxU⟩ := hx
    obtain ⟨O,hO,β,hxO,hOU⟩ := hS U hUS x hxU
    exact ⟨O,hO,β,hxO,fun y hy => mem_sUnion.mpr ⟨U,hUS,hOU hy⟩⟩

theorem sourceBase_isOpen {X : Type u} [TopologicalSpace X]
    (a : OmegaOneStage → X) {O : Set X} (hO : IsOpen O) (β : OmegaOneStage) :
    IsOpen (sourceBase a O β) := fun _ hx => ⟨O,hO,β,hx,Subset.rfl⟩

theorem sourceTail_isOpen {X : Type u} [TopologicalSpace X]
    (a : OmegaOneStage → X) (β : OmegaOneStage) : IsOpen (sourceTail a β) := by
  simpa [sourceBase,sourceTail] using sourceBase_isOpen a isOpen_univ β

def sourceBasis {X : Type u} [TopologicalSpace X] (a : OmegaOneStage → X) :
    Set (Set (SourcePoint a)) := {B | ∃ O : Set X, IsOpen O ∧ ∃ β, B = sourceBase a O β}

theorem sourceBasis_isTopologicalBasis {X : Type u} [TopologicalSpace X]
    (a : OmegaOneStage → X) : IsTopologicalBasis (sourceBasis a) := by
  apply isTopologicalBasis_of_isOpen_of_nhds
  · rintro B ⟨O,hO,β,rfl⟩
    exact sourceBase_isOpen a hO β
  · intro x U hx hU
    obtain ⟨O,hO,β,hxO,hOU⟩ := hU x hx
    exact ⟨sourceBase a O β,⟨O,hO,β,rfl⟩,hxO,hOU⟩

/-- Exact bridge to the source's generated-base definition of τ. -/
theorem sourceTopology_eq_generateFrom {X : Type u} [TopologicalSpace X]
    (a : OmegaOneStage → X) :
    sourceTopology a = generateFrom (sourceBasis a) :=
  (sourceBasis_isTopologicalBasis a).eq_generateFrom

/-- The source's identity/forgetful map to the ordinary ambient topology. -/
theorem source_val_continuous {X : Type u} [TopologicalSpace X]
    (a : OmegaOneStage → X) : Continuous (@SourcePoint.val X a) := by
  apply continuous_def.mpr
  intro O hO x hx
  refine ⟨O,hO,zeroStage,⟨hx,?_⟩,fun _ hy => hy.1⟩
  change (0 : Ordinal) ≤ (sourceIndex x).val
  exact bot_le

instance source_t2 {X : Type u} [TopologicalSpace X] [T2Space X]
    (a : OmegaOneStage → X) : T2Space (SourcePoint a) :=
  T2Space.of_injective_continuous (SourcePoint.val_injective a) (source_val_continuous a)

/-- Lemma 3.2's first-countability: at x only the single tail T_index(x) is
needed, together with an ordinary countable ambient base. No countable global
base for the refined topology is assumed. -/
instance source_firstCountable {X : Type u} [TopologicalSpace X]
    [SecondCountableTopology X] (a : OmegaOneStage → X) :
    FirstCountableTopology (SourcePoint a) := by
  constructor
  intro x
  have hb : (𝓝 x).HasBasis
      (fun b : countableBasis X => x.val ∈ (b.val : Set X))
      (fun b : countableBasis X => sourceBase a b.val (sourceIndex x)) := by
    constructor
    intro U
    constructor
    · intro hU
      obtain ⟨V,hVU,hV,hxV⟩ := mem_nhds_iff.mp hU
      obtain ⟨O,hO,β,hxO,hOV⟩ := hV x hxV
      obtain ⟨B,hB,hxB,hBO⟩ :=
        (isBasis_countableBasis X).exists_subset_of_mem_open hxO.1 hO
      refine ⟨⟨B,hB⟩,hxB,?_⟩
      intro y hy
      exact hVU (hOV ⟨hBO hy.1,hxO.2.trans hy.2⟩)
    · rintro ⟨b,hxb,hbU⟩
      exact mem_of_superset
        ((sourceBase_isOpen a ((isBasis_countableBasis X).isOpen b.property)
          (sourceIndex x)).mem_nhds ⟨hxb,le_rfl⟩) hbU
  exact hb.isCountablyGenerated

end CHFubini
