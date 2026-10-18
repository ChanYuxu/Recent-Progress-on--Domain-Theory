import PointCentralFubini.SourceStatements
import PointCentralFubini.Fatou
import PointCentralFubini.OpenFubini
import Mathlib.Topology.Sequences

/-! Measure restriction, support, and lower semicontinuity used in Proposition 4.2.
The incidence equality itself remains a separate proof obligation. -/
set_option autoImplicit false
open Set Topology TopologicalSpace MeasureTheory Filter
open scoped ENNReal
universe u
namespace PointCentralFubini
attribute [local instance] Classical.propDecidable

namespace TauMeasure
variable {X : Type u} [TopologicalSpace X]

/-- Source equation `eq:borel-restriction-valuation`. Finiteness permits
cancellation of the complementary mass when proving Scott continuity. -/
noncomputable def restrict (m : TauMeasure X) (B : Set X)
    (hB : MeasurableSet[borel X] B) : TauMeasure X := by
  letI : MeasurableSpace X := borel X
  letI : BorelSpace X := ⟨rfl⟩
  refine ⟨m.measure.restrict B,?_,?_⟩
  · rw [Measure.restrict_apply MeasurableSet.univ,univ_inter]
    exact ne_top_of_le_ne_top m.finite (measure_mono (subset_univ B))
  · have hf : ScottContinuous (fun U : Opens X => m.measure ((U : Set X) ∩ B)) := by
      intro A hn hd p hp
      constructor
      · rintro z ⟨U,hU,rfl⟩
        exact measure_mono (inter_subset_inter_left B (hp.1 hU))
      · intro z hz
        have hfin : m.measure ((p : Set X) \ B) ≠ ⊤ :=
          ne_top_of_le_ne_top m.finite (measure_mono (subset_univ _))
        apply (ENNReal.add_le_add_iff_right hfin).mp
        calc
          m.measure ((p : Set X) ∩ B) + m.measure ((p : Set X) \ B) =
              m.measure (p : Set X) := measure_inter_add_diff _ hB
          _ ≤ z + m.measure ((p : Set X) \ B) := (m.directed_opens hn hd hp).2 (by
            rintro y ⟨U,hU,rfl⟩
            change m.measure (U : Set X) ≤ _
            rw [← measure_inter_add_diff (U : Set X) hB]
            exact add_le_add (hz (mem_image_of_mem _ hU))
              (measure_mono (diff_subset_diff_left (hp.1 hU))))
    have he : (fun U : Opens X => m.measure.restrict B (U : Set X)) =
        (fun U : Opens X => m.measure ((U : Set X) ∩ B)) :=
      funext (fun U => Measure.restrict_apply U.isOpen.measurableSet)
    exact he.symm ▸ hf

@[simp] theorem restrict_apply (m : TauMeasure X) (B : Set X)
    (hB : MeasurableSet[borel X] B) (U : Opens X) :
    (m.restrict B hB).measure (U : Set X) = m.measure ((U : Set X) ∩ B) := by
  letI : MeasurableSpace X := borel X
  letI : BorelSpace X := ⟨rfl⟩
  exact Measure.restrict_apply U.isOpen.measurableSet

/-- The union of all open null sets. Tau-smoothness, rather than countability
of the ambient topology, proves that this open union is null. -/
def nullOpen (m : TauMeasure X) : Opens X := sSup {U | m.measure (U : Set X) = 0}

theorem nullOpen_null (m : TauMeasure X) : m.measure (m.nullOpen : Set X) = 0 := by
  have hn : {U : Opens X | m.measure (U : Set X) = 0}.Nonempty :=
    ⟨⊥,measure_empty⟩
  have hd : DirectedOn (· ≤ ·) {U : Opens X | m.measure (U : Set X) = 0} := by
    intro U hU V hV
    exact ⟨U ⊔ V,measure_union_null hU hV,le_sup_left,le_sup_right⟩
  change m.toValuation (sSup _) = 0
  rw [m.toValuation.map_sSup hn hd]
  apply le_antisymm _ bot_le
  apply iSup_le; intro U; apply iSup_le; intro hU
  exact hU.le

def support (m : TauMeasure X) : Set X := (m.nullOpen : Set X)ᶜ

theorem support_compl_null (m : TauMeasure X) : m.measure m.supportᶜ = 0 := by
  simpa only [support,compl_compl] using m.nullOpen_null

theorem mem_support_iff (m : TauMeasure X) (x : X) :
    x ∈ m.support ↔ ∀ U : Opens X, x ∈ U → 0 < m.measure (U : Set X) := by
  change x ∉ (sSup {U : Opens X | m.measure (U : Set X) = 0} : Opens X) ↔ _
  rw [Opens.mem_sSup]
  constructor
  · intro hx U hxU
    exact lt_of_not_ge (fun h => hx ⟨U,nonpos_iff_eq_zero.mp h,hxU⟩)
  · rintro hx ⟨U,hU,hxU⟩
    exact (ne_of_gt (hx U hxU)) hU
end TauMeasure

namespace Valuation
variable {X : Type u} [TopologicalSpace X]

noncomputable def dirac (x : X) : Valuation X := by
  classical
  refine ⟨fun U => if x ∈ U then 1 else 0,by simp,?_,?_⟩
  · intro U V
    by_cases hU : x ∈ U <;> by_cases hV : x ∈ V <;> simp [hU,hV]
  · exact (isLSC_scott_iff (indicator (pointOpen x))).mp (indicator_isLSC (pointOpen x))

@[simp] theorem dirac_apply (x : X) (U : Opens X) :
    dirac x U = if x ∈ U then 1 else 0 := by
  rfl

theorem integral_dirac_evaluation (η : DValuation (Opens X)) (x : X) :
    integral η (fun U => dirac x (WithScott.ofScott U)) = η (pointOpen x) := by
  convert integral_indicator η (pointOpen x) using 1

end Valuation

theorem dirac_le_liminf_of_tendsto {X : Type u} [TopologicalSpace X]
    {x : X} {s : ℕ → X} (hs : Tendsto s atTop (𝓝 x)) (U : Opens X) :
    Valuation.dirac x U ≤ ⨆ N : ℕ, ⨅ n ≥ N, Valuation.dirac (s n) U := by
  classical
  by_cases hx : x ∈ U
  · obtain ⟨N,hN⟩ := eventually_atTop.mp (hs.eventually (U.isOpen.mem_nhds hx))
    rw [Valuation.dirac_apply,if_pos hx]
    apply le_iSup_of_le N
    apply le_iInf; intro n
    apply le_iInf; intro hn
    change (1 : ℝ≥0∞) ≤ if s n ∈ U then 1 else 0
    rw [if_pos (show s n ∈ U from hN n hn)]
  · simp only [Valuation.dirac_apply,if_neg hx,zero_le]

/-- The sequential Fatou argument in the first paragraph of Proposition 4.2.
No measure extension for η and no product measurability are used. -/
theorem incidence_evaluation_le_liminf {X : Type u} [TopologicalSpace X]
    (η : DValuation (Opens X)) {x : X} {s : ℕ → X} (hs : Tendsto s atTop (𝓝 x)) :
    η (pointOpen x) ≤ ⨆ N : ℕ, ⨅ n ≥ N, η (pointOpen (s n)) := by
  have h := scott_fatou (Opens X) (completeLattice_isDcpo _) η
    (Valuation.dirac x).mass (fun n => (Valuation.dirac (s n)).mass)
    (Valuation.dirac x).continuous (fun n => (Valuation.dirac (s n)).continuous)
    (dirac_le_liminf_of_tendsto hs)
  simpa only [Valuation.integral_dirac_evaluation] using h

/-- The lower-semicontinuity conclusion of source Proposition 4.2. It in fact
does not need the inner skeleton or the finiteness of η. -/
theorem incidence_evaluation_isLSC {X : Type u} [TopologicalSpace X]
    [FirstCountableTopology X] (η : DValuation (Opens X)) :
    IsLSC (fun x => η (pointOpen x)) := by
  intro r
  have hc : IsClosed {x : X | η (pointOpen x) ≤ r} := by
    apply IsSeqClosed.isClosed
    intro s x hs hx
    apply (incidence_evaluation_le_liminf η hx).trans
    apply iSup_le; intro N
    exact (iInf_le_of_le N (iInf_le _ le_rfl)).trans (hs N)
  convert hc.isOpen_compl using 1
  ext x; simp

theorem incidence_evaluation_le_mass {X : Type u} [TopologicalSpace X]
    (η : DValuation (Opens X)) (x : X) : η (pointOpen x) ≤ η ⊤ :=
  η.mono le_top

theorem incidence_evaluation_ne_top {X : Type u} [TopologicalSpace X]
    (η : DValuation (Opens X)) (hη : η.Finite) (x : X) : η (pointOpen x) ≠ ⊤ :=
  ne_top_of_le_ne_top hη (incidence_evaluation_le_mass η x)

theorem incidence_evaluation_borel_measurable {X : Type u} [TopologicalSpace X]
    [FirstCountableTopology X] (η : DValuation (Opens X)) :
    @Measurable X ℝ≥0∞ (borel X) (borel ℝ≥0∞) (fun x => η (pointOpen x)) := by
  letI : MeasurableSpace X := borel X
  letI : BorelSpace X := ⟨rfl⟩
  have h : LowerSemicontinuous (fun x => η (pointOpen x)) :=
    lowerSemicontinuous_iff_isOpen_preimage.mpr (incidence_evaluation_isLSC η)
  exact h.measurable

end PointCentralFubini
