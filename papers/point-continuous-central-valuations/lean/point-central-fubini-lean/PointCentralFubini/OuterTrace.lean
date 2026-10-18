import PointCentralFubini.SourceStatements
import PointCentralFubini.ValuationLimits
set_option autoImplicit false
open Set Topology TopologicalSpace MeasureTheory Function
open scoped ENNReal BigOperators
universe u
namespace PointCentralFubini

private theorem trace_borel_repr {E : Type u} [TopologicalSpace E] {A : Set E}
    {S : Set A} (hS : MeasurableSet[borel A] S) :
    ∃ B : Set E, MeasurableSet[borel E] B ∧ Subtype.val ⁻¹' B = S := by
  change MeasurableSet[@borel A (TopologicalSpace.induced (Subtype.val : A → E) inferInstance)] S at hS
  rw [borel_comap] at hS
  exact hS

/-- The well-definedness step of source lemma 4.3. No measurability of A. -/
theorem fullOuter_trace_mono {E : Type u} [TopologicalSpace E] (M : TauMeasure E) (A : Set E)
    (hfull : ∀ B : Set E, MeasurableSet[borel E] B → B ⊆ Aᶜ → M.measure B = 0)
    {B C : Set E} (hB : MeasurableSet[borel E] B) (hC : MeasurableSet[borel E] C)
    (htr : (Subtype.val : A → E) ⁻¹' B ⊆ Subtype.val ⁻¹' C) : M.measure B ≤ M.measure C := by
  have hnull : M.measure (B \ C) = 0 := by
    apply hfull _ (hB.diff hC)
    intro x hx hxA
    exact hx.2 (htr (a := ⟨x,hxA⟩) hx.1)
  calc
    M.measure B ≤ M.measure (C ∪ (B \ C)) := measure_mono (by intro x hx; by_cases hxc : x ∈ C <;> simp [hx,hxc])
    _ ≤ M.measure C + M.measure (B \ C) := measure_union_le _ _
    _ = M.measure C := by rw [hnull,add_zero]

/-- Countable additivity of the full-outer trace, constructed by measurable
representatives and disjointization, as in the supplied proof. -/
theorem exists_fullOuter_trace_measure {E : Type u} [TopologicalSpace E]
    (M : TauMeasure E) (A : Set E)
    (hfull : ∀ B : Set E, MeasurableSet[borel E] B → B ⊆ Aᶜ → M.measure B = 0) :
    ∃ m : @Measure A (borel A), ∀ B : Set E, MeasurableSet[borel E] B →
      m (Subtype.val ⁻¹' B) = M.measure B := by
  classical
  letI : MeasurableSpace E := borel E
  letI : MeasurableSpace A := borel A
  have hwell : ∀ B C : Set E, MeasurableSet B → MeasurableSet C →
      (Subtype.val : A → E) ⁻¹' B = Subtype.val ⁻¹' C → M.measure B = M.measure C := by
    intro B C hB hC he
    exact le_antisymm (fullOuter_trace_mono M A hfull hB hC he.le)
      (fullOuter_trace_mono M A hfull hC hB he.ge)
  let rep : ∀ S : Set A, MeasurableSet S → Set E := fun S hS => (trace_borel_repr hS).choose
  have hrep : ∀ S hS, MeasurableSet (rep S hS) ∧ Subtype.val ⁻¹' (rep S hS) = S :=
    fun S hS => (trace_borel_repr hS).choose_spec
  let mass : ∀ S : Set A, MeasurableSet S → ℝ≥0∞ := fun S hS => M.measure (rep S hS)
  have hm : ∀ B : Set E, MeasurableSet B → ∀ (S : Set A) (hS : MeasurableSet S),
      Subtype.val ⁻¹' B = S → mass S hS = M.measure B := by
    intro B hB S hS he
    exact hwell _ _ (hrep S hS).1 hB ((hrep S hS).2.trans he.symm)
  have hm0 : mass ∅ MeasurableSet.empty = 0 := by
    rw [hm ∅ MeasurableSet.empty ∅ MeasurableSet.empty (by simp),measure_empty]
  have hmU : ∀ {S : ℕ → Set A} (hs : ∀ n, MeasurableSet (S n)),
      Pairwise (Disjoint on S) → mass (⋃ n, S n) (.iUnion hs) = ∑' n, mass (S n) (hs n) := by
    intro S hs hd
    let B : ℕ → Set E := fun n => rep (S n) (hs n)
    have hB : ∀ n, MeasurableSet (B n) := fun n => (hrep (S n) (hs n)).1
    have htB : ∀ n, (Subtype.val : A → E) ⁻¹' B n = S n := fun n => (hrep (S n) (hs n)).2
    have htC : ∀ n, (Subtype.val : A → E) ⁻¹' disjointed B n = S n := by
      intro n
      rw [disjointed_eq_inter_compl]
      ext x
      simp only [mem_preimage,mem_inter_iff,mem_iInter,mem_compl_iff]
      constructor
      · intro hx
        have hx' : x ∈ (Subtype.val : A → E) ⁻¹' B n := hx.1
        rw [htB n] at hx'; exact hx'
      · intro hx
        refine ⟨?_,?_⟩
        · change x ∈ (Subtype.val : A → E) ⁻¹' B n
          rw [htB n]; exact hx
        · intro j hj hxj
          have hxj' : x ∈ (Subtype.val : A → E) ⁻¹' B j := hxj
          rw [htB j] at hxj'
          exact Set.disjoint_left.mp (hd (ne_of_lt hj)) hxj' hx
    have htunion : (Subtype.val : A → E) ⁻¹' (⋃ n, disjointed B n) = ⋃ n, S n := by
      simp_rw [preimage_iUnion,htC]
    rw [hm _ (.iUnion (MeasurableSet.disjointed hB)) _ (.iUnion hs) htunion,
      measure_iUnion (disjoint_disjointed B) (MeasurableSet.disjointed hB)]
    apply tsum_congr; intro n
    exact (hm _ (MeasurableSet.disjointed hB n) _ (hs n) (htC n)).symm
  let m : Measure A := Measure.ofMeasurable mass hm0 (fun {f} hf hd => hmU hf hd)
  refine ⟨m,?_⟩
  intro B hB
  have htr : MeasurableSet ((Subtype.val : A → E) ⁻¹' B) := by
    exact continuous_subtype_val.borel_measurable hB
  rw [show m (Subtype.val ⁻¹' B) = mass (Subtype.val ⁻¹' B) htr from Measure.ofMeasurable_apply _ htr]
  exact hm B hB _ htr rfl

private theorem directed_finset_upper {α : Type u} [PartialOrder α] {S : Set α}
    (hn : S.Nonempty) (hd : DirectedOn (· ≤ ·) S) (F : Finset S) :
    ∃ U ∈ S, ∀ i ∈ F, i.val ≤ U := by
  classical
  induction F using Finset.induction_on with
  | empty => obtain ⟨U,hU⟩ := hn; exact ⟨U,hU,by simp⟩
  | @insert i F hi ih =>
    obtain ⟨U,hU,hFU⟩ := ih
    obtain ⟨V,hV,hiV,hUV⟩ := hd i i.property U hU
    refine ⟨V,hV,?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact hiV
    · exact (hFU j hj).trans hUV

/-- Source contract: `lem:full-outer-trace` (lemma 4.3).
Version: SHA-256 `134da69fa816824e5fefcb93a4e77a8cd5158c8aaab5ffd288ece2372e55d4e6`.
Locator: `source/manuscript.tex`, lines 462--468; no PDF was supplied.
Formalization status: `proved`; human review is pending.

Strict source TeX:
```latex
\begin{lemma}\label{lem:full-outer-trace}
Let $M$ be a finite $\tau$-smooth Borel measure on a space $E$, and let $A\subseteq E$. Suppose that every Borel subset of $E\setminus A$ is $M$-null. Then
\begin{equation}\label{eq:full-outer-trace}
 m(A\cap B)=M(B)\qquad(B\subseteq E\text{ Borel})
\end{equation}
defines a finite $\tau$-smooth Borel measure on the subspace $A$.
\end{lemma}
```
-/
theorem full_outer_trace : FullOuterTraceStatement.{u} := by
  classical
  intro E _ M A hfull
  letI : MeasurableSpace E := borel E
  letI : BorelSpace E := ⟨rfl⟩
  letI : MeasurableSpace A := borel A
  letI : BorelSpace A := ⟨rfl⟩
  obtain ⟨m,hm⟩ := exists_fullOuter_trace_measure M A hfull
  have hlift : ∀ U : Opens A, ∃ V : Opens E, Subtype.val ⁻¹' (V : Set E) = (U : Set A) := by
    intro U
    obtain ⟨V,hV,hVU⟩ := isOpen_induced_iff.mp U.isOpen
    exact ⟨⟨V,hV⟩,hVU⟩
  choose V hV using hlift
  have hfin : m univ ≠ ⊤ := by
    have he := hm univ MeasurableSet.univ
    simp only [preimage_univ] at he
    rw [he]; exact M.finite
  refine ⟨⟨m,hfin,?_⟩,hm⟩
  apply ScottContinuous.of_map_sSup
  intro S hn hd
  let W : Opens E := ⨆ i : S, V i.val
  have hW : Subtype.val ⁻¹' (W : Set E) = ((sSup S : Opens A) : Set A) := by
    ext x
    constructor
    · intro hx
      obtain ⟨i,hi⟩ := Opens.mem_iSup.mp (show x.val ∈ (⨆ i : S, V i.val : Opens E) from hx)
      apply Opens.mem_sSup.mpr
      refine ⟨i.val,i.property,?_⟩
      change x ∈ (i.val : Set A)
      rw [← hV i.val]
      exact hi
    · intro hx
      obtain ⟨U,hU,hxU⟩ := Opens.mem_sSup.mp (show x ∈ (sSup S : Opens A) from hx)
      apply Opens.mem_iSup.mpr
      refine ⟨⟨U,hU⟩,?_⟩
      change x ∈ (Subtype.val : A → E) ⁻¹' (V U : Set E)
      rw [hV U]; exact hxU
  let F : Finset S → Opens E := fun s => s.sup (fun i => V i.val)
  have hFmono : Monotone F := fun s t hst => Finset.sup_mono hst
  have hFW : (⨆ s, F s) = W := by
    apply le_antisymm
    · apply iSup_le; intro s; apply Finset.sup_le; intro i hi; exact le_iSup (fun i : S => V i.val) i
    · apply iSup_le; intro i
      calc
        V i.val = F {i} := by simp [F]
        _ ≤ ⨆ s, F s := le_iSup F {i}
  haveI : Nonempty S := hn.to_subtype
  have hmassW : M.measure (W : Set E) = ⨆ s, M.measure (F s : Set E) := by
    rw [← hFW]
    exact M.toValuation.map_iSup F hFmono.directed_le
  apply le_antisymm
  · change m ((sSup S : Opens A) : Set A) ≤ _
    rw [← hW,hm W W.isOpen.measurableSet,hmassW]
    apply iSup_le; intro s
    obtain ⟨U,hU,hupper⟩ := directed_finset_upper hn hd s
    have hsub : Subtype.val ⁻¹' (F s : Set E) ⊆ (U : Set A) := by
      intro x hx
      change x.val ∈ s.sup (fun i => V i.val) at hx
      have ht : Subtype.val ⁻¹' (F s : Set E) = ((s.sup (fun i => i.val) : Opens A) : Set A) := by
        ext x; simp [F,Finset.sup_eq_iSup,hV]
      have hle : s.sup (fun i => i.val) ≤ U := Finset.sup_le hupper
      have hx' : x ∈ (Subtype.val : A → E) ⁻¹' (F s : Set E) := hx
      rw [ht] at hx'
      exact hle hx' 
    calc
      M.measure (F s : Set E) = m (Subtype.val ⁻¹' (F s : Set E)) := (hm _ (F s).isOpen.measurableSet).symm
      _ ≤ m (U : Set A) := measure_mono hsub
      _ ≤ sSup ((fun U : Opens A => m (U : Set A)) '' S) := le_sSup (mem_image_of_mem _ hU)
  · apply sSup_le; rintro z ⟨U,hU,rfl⟩
    apply measure_mono
    intro x hx
    exact Opens.mem_sSup.mpr ⟨U,hU,hx⟩
end PointCentralFubini
