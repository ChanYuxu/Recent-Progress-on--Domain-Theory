import ChainApproximation.LowerSetBasis
import Mathlib.ModelTheory.Substructures

/-!
# Actual finitary algebras and their substructure lattices

Support for source `thm:sharp`. A first-order language indexes its operations
by natural-number arities. All closures and substructures below are the real
mathlib constructions. Local finiteness and the Jonsson property are stated
on carriers; no approximation or interpolation conclusion is assumed.
-/

set_option autoImplicit false

universe u

namespace ChainApproximation
namespace Algebra

open Set Cardinal FirstOrder
open FirstOrder.Language

variable {L : FirstOrder.Language.{u, u}} {M : Type u} [L.Structure M]

def LocallyFinite (L : FirstOrder.Language.{u, u}) (M : Type u) [L.Structure M] : Prop :=
  ∀ F : Finset M, (Substructure.closure L (F : Set M) : Set M).Finite

def Jonsson (L : FirstOrder.Language.{u, u}) (M : Type u) [L.Structure M] : Prop :=
  Infinite M ∧ Countable (Σ n, L.Functions n) ∧
    ∀ S : L.Substructure M, Cardinal.mk S = Cardinal.mk M → S = ⊤

def finiteSubstructures (B : L.Substructure M) : Set (L.Substructure M) :=
  {S | (S : Set M).Finite ∧ S ≤ B}

theorem finite_subset_directed_sup {D : Set (L.Substructure M)} (hD : NonemptyDirected D)
    (F : Finset M) (hF : (F : Set M) ⊆ (sSup D : L.Substructure M)) :
    ∃ B ∈ D, (F : Set M) ⊆ B := by
  classical
  induction F using Finset.induction_on with
  | empty =>
    obtain ⟨B, hB⟩ := hD.1
    exact ⟨B, hB, by simp⟩
  | @insert q F hq ih =>
    obtain ⟨B, hB, hFB⟩ := ih (fun x hx ↦ hF (Finset.mem_insert_of_mem hx))
    obtain ⟨C, hC, hqC⟩ := (Substructure.mem_sSup_of_directedOn hD.1 hD.2).mp
      (hF (Finset.mem_insert_self _ _))
    obtain ⟨E, hE, hBE, hCE⟩ := hD.2 B hB C hC
    refine ⟨E, hE, ?_⟩
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hCE hqC
    · exact hBE (hFB hx)

theorem finite_wayBelow {S B : L.Substructure M} (hS : (S : Set M).Finite) (hSB : S ≤ B) :
    WayBelow S B := by
  intro D hD s hs hBs
  have hF : (hS.toFinset : Set M) ⊆ (sSup D : L.Substructure M) := by
    rw [← hs.unique (isLUB_sSup D), Set.Finite.coe_toFinset]
    exact hSB.trans hBs
  obtain ⟨C, hC, hSC⟩ := finite_subset_directed_sup hD hS.toFinset hF
  exact ⟨C, hC, by simpa only [Set.Finite.coe_toFinset] using hSC⟩

theorem finite_compact {S : L.Substructure M} (hS : (S : Set M).Finite) : Compact S :=
  finite_wayBelow hS le_rfl

theorem finiteSubstructures_directed (hLF : LocallyFinite L M) (B : L.Substructure M) :
    NonemptyDirected (finiteSubstructures B) := by
  classical
  refine ⟨⟨Substructure.closure L ((∅ : Finset M) : Set M), hLF ∅,
    Substructure.closure_le.mpr (by simp)⟩, ?_⟩
  rintro S ⟨hS, hSB⟩ T ⟨hT, hTB⟩
  let hF := hS.union hT
  let F : Finset M := hF.toFinset
  have hFB : (F : Set M) ⊆ B := by
    rw [Set.Finite.coe_toFinset]
    exact Set.union_subset hSB hTB
  refine ⟨Substructure.closure L (F : Set M), ⟨hLF F, Substructure.closure_le.mpr hFB⟩, ?_, ?_⟩
  · intro x hx
    apply Substructure.subset_closure
    rw [Set.Finite.coe_toFinset]
    exact Or.inl hx
  · intro x hx
    apply Substructure.subset_closure
    rw [Set.Finite.coe_toFinset]
    exact Or.inr hx

theorem finiteSubstructures_lub (hLF : LocallyFinite L M) (B : L.Substructure M) :
    IsLUB (finiteSubstructures B) B := by
  refine ⟨fun _ h ↦ h.2, ?_⟩
  intro C hC x hx
  have hxB : ({x} : Set M) ⊆ B := Set.singleton_subset_iff.mpr hx
  have hgen : Substructure.closure L ({x} : Set M) ∈ finiteSubstructures B := by
    refine ⟨?_, Substructure.closure_le.mpr hxB⟩
    simpa only [Finset.coe_singleton] using hLF {x}
  exact hC hgen (Substructure.subset_closure (Set.mem_singleton x))

theorem wayBelow_iff_finite (hLF : LocallyFinite L M) (S B : L.Substructure M) :
    WayBelow S B ↔ S ≤ B ∧ (S : Set M).Finite := by
  constructor
  · intro hSB
    obtain ⟨T, hT, hST⟩ := hSB (finiteSubstructures B) (finiteSubstructures_directed hLF B)
      B (finiteSubstructures_lub hLF B) le_rfl
    exact ⟨hSB.le, hT.1.subset hST⟩
  · rintro ⟨hSB, hS⟩
    exact finite_wayBelow hS hSB

theorem finiteSubstructures_eq_compact (hLF : LocallyFinite L M) (B : L.Substructure M) :
    finiteSubstructures B = {S | Compact S ∧ S ≤ B} := by
  ext S
  constructor
  · rintro ⟨hS, hSB⟩
    exact ⟨finite_compact hS, hSB⟩
  · rintro ⟨hS, hSB⟩
    exact ⟨((wayBelow_iff_finite hLF S S).mp hS).2, hSB⟩

theorem algebraic (hLF : LocallyFinite L M) : IsAlgebraic (L.Substructure M) := by
  refine ⟨completeLattice_dcpo, ?_⟩
  intro B
  rw [← finiteSubstructures_eq_compact hLF B]
  exact ⟨finiteSubstructures_directed hLF B, finiteSubstructures_lub hLF B⟩

theorem proper_countable (hJ : Jonsson L M) (hcard : Cardinal.mk M = Cardinal.aleph 1)
    {B : L.Substructure M} (hB : B ≠ ⊤) : (B : Set M).Countable := by
  apply Cardinal.le_aleph0_iff_set_countable.mp
  apply Cardinal.lt_aleph_one_iff.mp
  have hle : Cardinal.mk B ≤ Cardinal.mk M := Cardinal.mk_subtype_le _
  have hne : Cardinal.mk B ≠ Cardinal.mk M := fun h ↦ hB (hJ.2.2 B h)
  exact (lt_of_le_of_ne hle hne).trans_eq hcard

theorem named_constant_nonempty (c : L.Constants) (B : L.Substructure M) :
    (B : Set M).Nonempty := ⟨c, B.constants_mem c⟩

end Algebra
end ChainApproximation
