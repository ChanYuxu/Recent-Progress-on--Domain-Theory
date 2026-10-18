import PointCentralFubini.Countable
import PointCentralFubini.Scott
set_option autoImplicit false
open Set Topology TopologicalSpace
universe u v
namespace PointCentralFubini

/-- The general order-coinitial clause in source corollary 3.3. -/
theorem coinitial_valuation_pointContinuous (P : Type u) [PartialOrder P]
    (_hP : IsDcpo P) (hP : CountablyCoinitialOpens P) (μ : DValuation P) :
    PointContinuous μ := by
  apply valuation_pointContinuous_of_countable_saturations _ μ
  intro U
  obtain ⟨A,hAc,hAU,hco⟩ := hP U
  refine ⟨WithScott.toScott '' A,hAc.image _,?_⟩
  apply subset_antisymm
  · intro x hx
    exact hx U (by rintro _ ⟨a,ha,rfl⟩; exact hAU a ha)
  · intro x hx V hAV
    obtain ⟨a,ha,hax⟩ := hco (WithScott.ofScott x) hx
    have hav : WithScott.toScott a ∈ V := hAV (mem_image_of_mem _ ha)
    exact (Topology.IsScott.isUpperSet_of_isOpen (D := Set.univ) V.isOpen) hax hav

/-- Exact countable-dcpo wrapper, with the source dcpo hypothesis preserved. -/
theorem countable_dcpo_pointContinuous (P : Type u) [PartialOrder P] [Countable P]
    (_hP : IsDcpo P) (μ : DValuation P) : PointContinuous μ := by
  letI : Countable (WithScott P) := Countable.of_equiv P WithScott.toScott
  exact countable_valuation_pointContinuous μ

/-- Source corollary 2.5 as an explicit proof obligation. This is NOT a theorem
constant. Its discharge needs JLMZ plus normalization and approximation. -/
def PointCentralStatement : Prop :=
  ∀ (P : Type u) [PartialOrder P], IsDcpo P →
    ∀ μ : DValuation P, PointContinuous μ → Central.{u,v} μ

/-- Exact source corollary 3.3 including its extended Fubini conclusion. -/
def CountableFubiniStatement : Prop :=
  ∀ (P : Type u) [PartialOrder P] [Countable P], IsDcpo P → FubiniObject.{u,v} P

/-- Checked final inference; the unresolved cited-theorem extension is visible. -/
theorem countable_fubini_of_pointCentral (hpc : PointCentralStatement.{u,v}) :
    CountableFubiniStatement.{u,v} := by
  intro P _ _ hP μ
  exact hpc P hP μ (countable_dcpo_pointContinuous P hP μ)

theorem coinitial_fubini_of_pointCentral (hpc : PointCentralStatement.{u,v})
    (P : Type u) [PartialOrder P] (hP : IsDcpo P) (hco : CountablyCoinitialOpens P) :
    FubiniObject.{u,v} P := by
  intro μ
  exact hpc P hP μ (coinitial_valuation_pointContinuous P hP hco μ)
end PointCentralFubini
