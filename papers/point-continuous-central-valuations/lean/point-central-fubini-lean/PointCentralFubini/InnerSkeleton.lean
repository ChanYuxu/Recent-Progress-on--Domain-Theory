import PointCentralFubini.ExtremalObservations
import PointCentralFubini.MeasureSkeleton
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite

/-! Source Lemma 4.6: atoms of the observations and a coarser countable topology. -/
set_option autoImplicit false
open Set Topology TopologicalSpace MeasureTheory
open scoped ENNReal
universe u v
namespace PointCentralFubini

theorem innerSkeleton_of_countable_observations {X : Type u} [t : TopologicalSpace X]
    {I : Type v} [Countable I] (γ : I → X → ObservationCodomain)
    (hγ : ∀ i, Continuous (γ i))
    (htop : t = ⨅ i, induced (γ i) inferInstance) (m : TauMeasure X) :
    ∃ C : Set (Opens X), InnerSkeleton m C := by
  classical
  letI : MeasurableSpace X := borel X
  letI : BorelSpace X := ⟨rfl⟩
  letI : MeasurableSpace ObservationCodomain := borel ObservationCodomain
  letI : BorelSpace ObservationCodomain := ⟨rfl⟩
  letI : IsFiniteMeasure m.measure := ⟨m.finite.lt_top⟩
  let A : I → Set Sorgenfrey := fun i => {a | 0 < m.measure (γ i ⁻¹' {Sum.inl a})}
  have hA : ∀ i, (A i).Countable := by
    intro i
    exact Measure.countable_meas_pos_of_disjoint_iUnion
      (fun a => ((isClosed_singleton : IsClosed ({Sum.inl a} : Set ObservationCodomain)).preimage
        (hγ i)).measurableSet)
      (fun a b hab => Disjoint.preimage (γ i) (disjoint_singleton.mpr (Sum.inl_injective.ne hab)))
  letI : ∀ i, Countable (A i) := fun i => (hA i).to_subtype
  let B₀ : Set (Set X) :=
    (⋃ i, range (fun pq : ℚ × ℚ => γ i ⁻¹' (Sum.inl '' Ioo (pq.1 : Sorgenfrey) (pq.2 : Sorgenfrey)))) ∪
    (⋃ i, range (fun aq : A i × ℚ => γ i ⁻¹' (Sum.inl '' Ico aq.1.val (aq.2 : Sorgenfrey)))) ∪
    range (fun i => γ i ⁻¹' {Sum.inr ()})
  have hBc : B₀.Countable :=
    ((countable_iUnion fun _ => countable_range _).union
      (countable_iUnion fun _ => countable_range _)).union (countable_range _)
  let t₀ := generateFrom B₀
  have hsecond : @SecondCountableTopology X t₀ := SecondCountableTopology.mk' hBc
  letI : TopologicalSpace X := t
  have hcoarse : t ≤ t₀ := by
    apply le_generateFrom
    rintro U ((hU | hU) | ⟨i,rfl⟩)
    · obtain ⟨i,hU⟩ := mem_iUnion.mp hU
      obtain ⟨pq,rfl⟩ := hU
      exact (isOpenMap_inl _ ((sorgenfrey_isOpen_Ioi _).inter
        (sorgenfrey_isOpen_Iio _))).preimage (hγ i)
    · obtain ⟨i,hU⟩ := mem_iUnion.mp hU
      obtain ⟨aq,rfl⟩ := hU
      exact (isOpenMap_inl _ (sorgenfrey_isOpen_Ico _ _)).preimage (hγ i)
    · exact (observation_basis.isOpen (Or.inr rfl)).preimage (hγ i)
  have hIoo : ∀ (i : I) (a b : Sorgenfrey),
      IsOpen[t₀] (γ i ⁻¹' (Sum.inl '' Ioo a b)) := by
    intro i a b
    letI : TopologicalSpace X := t₀
    apply isOpen_iff_forall_mem_open.mpr
    rintro x ⟨z,hz,hzx⟩
    obtain ⟨p,hap,hpz⟩ := exists_rat_btwn hz.1
    obtain ⟨q,hzq,hqb⟩ := exists_rat_btwn hz.2
    refine ⟨γ i ⁻¹' (Sum.inl '' Ioo (p : Sorgenfrey) (q : Sorgenfrey)),?_,?_,?_⟩
    · rintro y ⟨w,hw,hwy⟩
      exact ⟨w,⟨hap.trans hw.1,hw.2.trans hqb⟩,hwy⟩
    · exact isOpen_generateFrom_of_mem (Or.inl (Or.inl (mem_iUnion.mpr
        ⟨i,mem_range_self (p,q)⟩)))
    · exact ⟨z,⟨hpz,hzq⟩,hzx⟩
  have hIco : ∀ (i : I) (a : Sorgenfrey), a ∈ A i → ∀ b : Sorgenfrey,
      IsOpen[t₀] (γ i ⁻¹' (Sum.inl '' Ico a b)) := by
    intro i a ha b
    letI : TopologicalSpace X := t₀
    apply isOpen_iff_forall_mem_open.mpr
    rintro x ⟨z,hz,hzx⟩
    obtain ⟨q,hzq,hqb⟩ := exists_rat_btwn hz.2
    refine ⟨γ i ⁻¹' (Sum.inl '' Ico a (q : Sorgenfrey)),?_,?_,?_⟩
    · rintro y ⟨w,hw,hwy⟩
      exact ⟨w,⟨hw.1,hw.2.trans hqb⟩,hwy⟩
    · exact isOpen_generateFrom_of_mem (Or.inl (Or.inr (mem_iUnion.mpr
        ⟨i,⟨((⟨a,ha⟩ : A i),q),rfl⟩⟩)))
    · exact ⟨z,⟨hz.1,hzq⟩,hzx⟩
  let S : Set (Set X) := ⋃ i, preimage (γ i) '' observationIntervals
  have hSgen : t = generateFrom S := by
    rw [htop]
    simp only [S,generateFrom_iUnion,← induced_generateFrom_eq,
      ← observation_basis.eq_generateFrom]
  have hS : ∀ U ∈ S, ∃ V, IsOpen[t₀] V ∧ V ⊆ U ∧ m.measure U = m.measure V := by
    intro U hU
    obtain ⟨i,hU⟩ := mem_iUnion.mp hU
    obtain ⟨V,hV,rfl⟩ := hU
    rcases hV with ⟨a,b,rfl⟩ | hV
    · by_cases ha : a ∈ A i
      · exact ⟨_,hIco i a ha b,Subset.rfl,rfl⟩
      · refine ⟨γ i ⁻¹' (Sum.inl '' Ioo a b),hIoo i a b,
          preimage_mono (image_mono Ioo_subset_Ico_self),?_⟩
        have hn : m.measure (γ i ⁻¹' {Sum.inl a}) = 0 :=
          nonpos_iff_eq_zero.mp (not_lt.mp ha)
        symm
        apply measure_eq_measure_of_null_diff (preimage_mono (image_mono Ioo_subset_Ico_self))
        apply measure_mono_null (t := γ i ⁻¹' {Sum.inl a}) _ hn
        rintro x ⟨⟨z,hz,hzx⟩,hx⟩
        have hza : z = a := le_antisymm (le_of_not_gt (fun h => hx ⟨z,⟨h,hz.2⟩,hzx⟩)) hz.1
        exact hza ▸ hzx.symm
    · rcases hV with rfl
      exact ⟨_,isOpen_generateFrom_of_mem (Or.inr (mem_range_self i)),Subset.rfl,rfl⟩
  apply m.innerSkeleton_of_coarser t₀ hcoarse hsecond
  intro U
  exact m.same_mass_open_of_generated t₀ hcoarse S hSgen hS U U.isOpen

/-- Source contract: `lem:inner-skeleton` (lemma 4.6).
Version: SHA-256 `134da69fa816824e5fefcb93a4e77a8cd5158c8aaab5ffd288ece2372e55d4e6`.
Locator: `source/manuscript.tex`, lines 576--578; no PDF was supplied.
Formalization status: `proved`; human review is pending.

Strict source TeX:
```latex
\begin{lemma}\label{lem:inner-skeleton}
Let $X=D_{\mathrm V}$ and let $m$ be a finite $\tau$-smooth Borel measure on $X$. There is a countable family $\mathcal C\subseteq\OO(X)$ satisfying \eqref{eq:countable-inner-approximation}.
\end{lemma}
```
-/
theorem sorgenfrey_inner_skeleton : SorgenfreyInnerSkeletonStatement := by
  intro m
  let γ : RationalFragment ⊕ RationalFragment → SorgenfreyVietoris → ObservationCodomain :=
    Sum.elim lowerObservation upperObservation
  apply innerSkeleton_of_countable_observations γ _ _ m
  · rintro (C | C)
    · exact lowerObservation_continuous C
    · exact upperObservation_continuous C
  · exact extremalTopology_eq.trans (by
      simp only [γ,iInf_sum,Sum.elim_inl,Sum.elim_inr,extremalTopology])

end PointCentralFubini
