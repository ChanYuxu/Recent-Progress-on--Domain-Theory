import CHFubini.SourceRepresentatives
import CHFubini.Sobriety
import CHFubini.WellFiltered
import CHFubini.Choquet

/-! The specified P=Q(A), singleton pushforward mu, Scott-product witness W,
and its two profiles. None of these witnesses is replaced by an arbitrary
isomorphic dcpo or an assumed Fubini failure.
-/

set_option autoImplicit false
open Set Topology TopologicalSpace MeasureTheory
open scoped ENNReal
universe u
namespace CHFubini

abbrev SourceSmyth {X : Type u} [TopologicalSpace X] (a : OmegaOneStage → X) :=
  Smyth (SourcePoint a)

theorem source_smyth_properties {X : Type u} [TopologicalSpace X]
    [T2Space X] [SecondCountableTopology X] (a : OmegaOneStage → X) :
    IsDcpo (SourceSmyth a) ∧
    (inferInstance : TopologicalSpace (WithScott (SourceSmyth a))) =
      upperVietorisTopology (SourcePoint a) ∧
    FirstCountableTopology (WithScott (SourceSmyth a)) ∧
    IsSober (WithScott (SourceSmyth a)) ∧ IsWellFiltered (WithScott (SourceSmyth a)) := by
  have hc : ∀ C : NonemptyCompacts (SourcePoint a), (C : Set _).Countable :=
    fun C => source_compact_countable a C.isCompact
  obtain ⟨heq,hfirst⟩ := smyth_scott_eq_upperVietoris_and_firstCountable hc
  have hs : IsSober (WithScott (SourceSmyth a)) := scottSmyth_sober_of_countable_compacts hc
  exact ⟨smyth_isDcpo _,heq,hfirst,hs,sober_isWellFiltered hs⟩

theorem sourceSingleton_continuous {X : Type u} [TopologicalSpace X]
    [T2Space X] [SecondCountableTopology X] (a : OmegaOneStage → X) :
    Continuous (@singletonMap (SourcePoint a) _) :=
  singletonMap_continuous_of_countable_compacts
    (fun C => source_compact_countable a C.isCompact)

/-- The paper's actual singleton pushforward, equation (5.4). -/
noncomputable def sourceMu {X : Type u} [TopologicalSpace X]
    [T2Space X] [SecondCountableTopology X] (a : OmegaOneStage → X)
    (α : Valuation (SourcePoint a)) : DValuation (SourceSmyth a) :=
  α.push singletonMap (sourceSingleton_continuous a)

theorem sourceMu_probability {X : Type u} [TopologicalSpace X]
    [T2Space X] [SecondCountableTopology X] (a : OmegaOneStage → X)
    (α : Valuation (SourcePoint a)) (hα : α.Probability) :
    (sourceMu a α).Probability := hα.push _ _

theorem sourceMu_box {X : Type u} [TopologicalSpace X]
    [T2Space X] [SecondCountableTopology X] (a : OmegaOneStage → X)
    (α : Valuation (SourcePoint a)) (V : Opens (SourcePoint a)) :
    sourceMu a α (boxOpen V) = α V := by
  change α (Opens.comap ⟨singletonMap,sourceSingleton_continuous a⟩ (boxOpen V)) = α V
  congr 1
  apply Opens.ext
  ext x
  change ({x} : Set _) ⊆ V ↔ x ∈ V
  exact singleton_subset_iff

@[simp] theorem leftSection_incidence_eq_box {X : Type u}
    [TopologicalSpace X] [T2Space X] (V : Opens X) :
    leftSection (@incidenceOpen X _ _) V = boxOpen V := by
  apply Opens.ext
  rfl

@[simp] theorem rightSection_incidence_eq_compactNeighborhood {X : Type u}
    [TopologicalSpace X] [T2Space X] (C : Smyth X) :
    rightSection (@incidenceOpen X _ _) C = compactNeighborhood C := by
  apply Opens.ext
  rfl

theorem source_f_profile {X : Type u} [TopologicalSpace X]
    [T2Space X] [SecondCountableTopology X] (a : OmegaOneStage → X)
    (α : Valuation (SourcePoint a)) :
    (fun V : Opens (SourcePoint a) => sourceMu a α (leftSection incidenceOpen V)) = α.mass := by
  funext V
  rw [leftSection_incidence_eq_box,sourceMu_box]

theorem source_f_profile_scott {X : Type u} [TopologicalSpace X]
    [T2Space X] [SecondCountableTopology X] (a : OmegaOneStage → X)
    (α : Valuation (SourcePoint a)) :
    ScottContinuous (fun V : Opens (SourcePoint a) => sourceMu a α (leftSection incidenceOpen V)) := by
  rw [source_f_profile]
  exact α.continuous

theorem source_g_profile_scott {X : Type u} [TopologicalSpace X]
    [T2Space X] (ρ : DValuation (Opens X)) :
    ScottContinuous (fun C : Smyth X => ρ (rightSection incidenceOpen C)) := by
  simp only [rightSection_incidence_eq_compactNeighborhood]
  exact compactProfile_scottContinuous ρ.mass ρ.continuous

end CHFubini
