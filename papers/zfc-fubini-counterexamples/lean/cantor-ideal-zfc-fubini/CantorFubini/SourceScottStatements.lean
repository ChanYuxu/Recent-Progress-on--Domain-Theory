import CantorFubini.SecondValuation
import Mathlib.Order.ScottContinuity.Complete

/-! New source-facing wrappers for the literal Cantor null-ideal model.
The binders retain ordinary subsets with explicit openness and finite-set
conditions where the manuscript uses those, while `Opens` packages exactly
the same data for the complete open-set lattices. -/

set_option autoImplicit false
open Set Topology TopologicalSpace MeasureTheory
universe u
namespace CantorFubini
open IdealPoint

theorem B_preserves_directed_union {I : Type u} [Nonempty I]
    (O : I → Set Cantor) (hO : ∀ i, IsOpen (O i)) (hd : Directed (· ⊆ ·) O) :
    B cantorMeasure ⟨⋃ i, O i, isOpen_iUnion hO⟩ =
      ⨆ i, B cantorMeasure ⟨O i, hO i⟩ := by
  let U : I → Opens Cantor := fun i => ⟨O i, hO i⟩
  have hdU : Directed (· ≤ ·) U := hd
  have he := (B_scottContinuous cantorMeasure).map_sSup
    (range_nonempty U) hdU.directedOn_range
  rw [← range_comp, sSup_range, sSup_range] at he
  have hsup : (⨆ i, U i) = (⟨⋃ i, O i, isOpen_iUnion hO⟩ : Opens Cantor) := by
    apply Opens.ext
    rw [Opens.coe_iSup]
    rfl
  rw [hsup] at he
  exact he

/-- All assertions of source Lemma `lem:basic-opens`, with its ordinary-open
and null-set binders. Directed unions range over arbitrary nonempty indices. -/
theorem source_basic_opens (O : Set Cantor) (hO : IsOpen O)
    (M : Set Cantor) (hM : cantorMeasure M = 0) :
    IsOpen (B cantorMeasure ⟨O, hO⟩ : Set (WithScott (IdealPoint cantorMeasure))) ∧
    IsOpen (A cantorMeasure M hM : Set (WithScott (IdealPoint cantorMeasure))) ∧
    trace (B cantorMeasure ⟨O, hO⟩) = O ∧
    trace (A cantorMeasure M hM) = Mᶜ ∧
    (∀ {I : Type u} [Nonempty I] (U : I → Set Cantor) (hU : ∀ i, IsOpen (U i)),
      Directed (· ⊆ ·) U →
        B cantorMeasure ⟨⋃ i, U i, isOpen_iUnion hU⟩ =
          ⨆ i, B cantorMeasure ⟨U i, hU i⟩) ∧
    (∀ (N : Set Cantor) (hN : cantorMeasure N = 0),
      M ⊆ N → A cantorMeasure N hN ≤ A cantorMeasure M hM) ∧
    (∀ p : IdealPoint cantorMeasure,
      WithScott.toScott p ∈ B cantorMeasure ⟨O, hO⟩ ↔ p.kernel ⊆ O) ∧
    (∀ p : IdealPoint cantorMeasure,
      WithScott.toScott p ∈ A cantorMeasure M hM ↔ M ∈ p.ideal.sets) :=
  ⟨(B cantorMeasure ⟨O, hO⟩).isOpen, (A cantorMeasure M hM).isOpen,
    trace_B cantorMeasure ⟨O, hO⟩, trace_A cantorMeasure M hM,
    fun U hU hd => B_preserves_directed_union U hU hd,
    (fun N hN hMN => A_antitone cantorMeasure hM hN hMN),
    mem_B cantorMeasure ⟨O, hO⟩, mem_A cantorMeasure M hM⟩

/-- Source Proposition `prop:dcpo`, including all its maximality, mixed-label
and literal fixed-label supremum assertions. Supremum in the induced branch
and in the ambient dcpo are both exposed. -/
theorem source_dcpo :
    IsDcpo (IdealPoint cantorMeasure) ∧
    (∀ p : IdealPoint cantorMeasure,
      (∀ q, p ≤ q → q = p) ↔ ∃ y, p = IdealPoint.e cantorMeasure y) ∧
    (∀ (p : IdealPoint cantorMeasure) (y : Cantor),
      p ≤ IdealPoint.e cantorMeasure y ↔ y ∈ p.kernel) ∧
    (∀ (D : Set (IdealPoint cantorMeasure)), D.Nonempty → DirectedOn (· ≤ ·) D →
      (∃ p ∈ D, ∃ q ∈ D, p.label ≠ q.label) → ∃ r ∈ D, ∀ s ∈ D, s ≤ r) ∧
    (∀ (x : Cantor) (D : Set (Branch cantorMeasure x))
      (hn : D.Nonempty) (hd : DirectedOn (· ≤ ·) D),
      IsLUB D (branchSup hn hd) ∧
      IsLUB (Subtype.val '' D) (branchSup hn hd).val ∧
      (branchSup hn hd).val.label = x ∧
      (branchSup hn hd).val.kernel = ⋂ p : D, p.val.val.kernel ∧
      (branchSup hn hd).val.ideal.sets = ⋃ p : D, p.val.val.ideal.sets) := by
  refine ⟨IdealPoint.isDcpo cantorMeasure, IdealPoint.maximal_iff,
    IdealPoint.le_e_iff, ?_, ?_⟩
  · intro D _ hd hdiff
    obtain ⟨p, hp, q, hq, hne⟩ := hdiff
    exact directed_different_labels_has_greatest hd hp hq hne
  · intro x D hn hd
    exact ⟨branchSup_isLUB hn hd, branchSup_isLUB_ambient hn hd,
      (branchSup hn hd).property, kernel_branchSup hn hd, ideal_branchSup hn hd⟩

/-- Source Lemma `lem:gluing` with the full intrinsic Scott topology on `P`
and on each induced component, for an arbitrary subset `H`. -/
theorem source_gluing (H : Set (IdealPoint cantorMeasure)) :
    IsOpen (WithScott.ofScott ⁻¹' H) ↔
      (∀ x : Cantor, IsOpen {p : WithScott (Branch cantorMeasure x) |
        (WithScott.ofScott p).val ∈ H}) ∧
      (∀ p ∈ H, ∀ y ∈ p.kernel, IdealPoint.e cantorMeasure y ∈ H) :=
  isOpen_gluing_iff cantorMeasure H

/-- Source Lemma `lem:finite-restriction`, retaining the printed finite
subset binder and the directed/restricted cover of the entire component. -/
theorem source_finite_restriction (x : Cantor) (V : Set Cantor) (hV : IsOpen V)
    (hxV : x ∈ V) (F : Set Cantor) (_hF : F.Finite) :
    IsOpen {p : WithScott (Branch cantorMeasure x) |
      (WithScott.ofScott p).val.kernel ⊆ V ∪ F} ∧
    Directed (· ≤ ·) (branchTruncation cantorMeasure x ⟨V, hV⟩ hxV) ∧
    (⨆ E : Finset Cantor, branchTruncation cantorMeasure x ⟨V, hV⟩ hxV E) = ⊤ ∧
    (∀ H : ScottOpens (IdealPoint cantorMeasure),
      branchRestriction cantorMeasure x H =
        ⨆ E : TraceFinset H, branchRestriction cantorMeasure x H ⊓
          branchTruncation cantorMeasure x ⟨V, hV⟩ hxV E.val) :=
  ⟨kernelSubset_branch_isOpen cantorMeasure x ⟨V, hV⟩ hxV (V ∪ F) subset_union_left,
    branchTruncation_directed cantorMeasure x ⟨V, hV⟩ hxV,
    branchTruncation_cover cantorMeasure x ⟨V, hV⟩ hxV,
    fun H => restricted_branch_cover cantorMeasure x ⟨V, hV⟩ hxV H⟩

end CantorFubini
