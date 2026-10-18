import ChainApproximation.AlgebraChains
import ChainApproximation.Main

/-!
# The sharp Jónsson-algebra example

This module formalizes source `thm:sharp` conditionally on the locally finite
Jónsson algebra fixed in the theorem statement. The separate classical
existence input is tracked as an external source obligation; it is not assumed
as a Lean axiom here.
-/

set_option autoImplicit false

universe u

namespace ChainApproximation
namespace Algebra

open Set Cardinal FirstOrder
open FirstOrder.Language

variable {L : FirstOrder.Language.{u, u}} {M : Type u} [L.Structure M]

theorem chainBelow_top_iff_proper (hJ : Jonsson L M)
    (hcard : Cardinal.mk M = Cardinal.aleph 1) (c : L.Constants)
    (S : L.Substructure M) : ChainBelow S ⊤ ↔ S ≠ ⊤ := by
  constructor
  · intro hS htop
    subst S
    exact top_not_chainBelow_self hJ hcard hS
  · exact proper_chainBelow_top hJ hcard c

theorem proper_chainSection_generated (hLF : LocallyFinite L M)
    (hJ : Jonsson L M) (hcard : Cardinal.mk M = Cardinal.aleph 1)
    (c : L.Constants) (B : L.Substructure M) (hB : B ≠ ⊤) :
    IsChainGeneratedIdeal (chainSection B) ∧ IsLUB (chainSection B) B := by
  obtain ⟨f, hf, hfin, hLub⟩ :=
    countable_nat_approximation hLF c B (proper_countable hJ hcard hB)
  have hchain : NonemptyChain (Set.range f) :=
    ⟨Set.range_nonempty f, hf.isChain_range⟩
  have heq : chainSection B = lowerHull (Set.range f) := by
    ext S
    constructor
    · intro hSB
      exact (chainBelow_iff_sup completeLattice_dcpo S B).mp hSB
        (Set.range f) hchain B hLub le_rfl
    · rintro ⟨_, ⟨n, rfl⟩, hSn⟩
      exact (chainBelow_proper_iff_finite hLF hJ hcard c S B hB).mpr
        ⟨hSn.trans (hfin n).2, (hfin n).1.subset hSn⟩
  refine ⟨⟨Set.range f, hchain, heq⟩, ?_⟩
  rw [heq]
  constructor
  · rintro S ⟨_, ⟨n, rfl⟩, hSn⟩
    exact hSn.trans (hfin n).2
  · intro T hT
    apply hLub.2
    rintro S ⟨n, rfl⟩
    exact hT ⟨f n, Set.mem_range_self n, le_rfl⟩

theorem top_chainSection_generated (hJ : Jonsson L M)
    (hcard : Cardinal.mk M = Cardinal.aleph 1) (c : L.Constants) :
    IsChainGeneratedIdeal (chainSection (⊤ : L.Substructure M)) ∧
      IsLUB (chainSection (⊤ : L.Substructure M)) ⊤ := by
  obtain ⟨f, hf, hproper, hLub, hcof⟩ := aleph_one_top_approximation hJ hcard
  haveI : Nonempty (CofinalIndex (Cardinal.aleph 1 : Cardinal.{u})) :=
    Cardinal.mk_ne_zero_iff.mp (by
      rw [cofinalIndex_card]
      exact Cardinal.isRegular_aleph_one.ne_zero)
  have hchain : NonemptyChain (Set.range f) :=
    ⟨Set.range_nonempty f, hf.isChain_range⟩
  have heq : chainSection (⊤ : L.Substructure M) = lowerHull (Set.range f) := by
    ext S
    constructor
    · intro hS
      obtain ⟨a, ha⟩ := hcof S ((chainBelow_top_iff_proper hJ hcard c S).mp hS)
      exact ⟨f a, Set.mem_range_self a, ha⟩
    · rintro ⟨_, ⟨a, rfl⟩, hSa⟩
      apply (chainBelow_top_iff_proper hJ hcard c S).mpr
      intro htop
      exact hproper a (top_le_iff.mp (htop ▸ hSa))
  refine ⟨⟨Set.range f, hchain, heq⟩, ?_⟩
  rw [heq]
  constructor
  · exact fun _ _ ↦ le_top
  · intro T hT
    apply hLub.2
    rintro S ⟨a, rfl⟩
    exact hT ⟨f a, Set.mem_range_self a, le_rfl⟩

/-- The subalgebra lattice in source `thm:sharp` is chain-continuous. -/
theorem chainContinuous (hLF : LocallyFinite L M) (hJ : Jonsson L M)
    (hcard : Cardinal.mk M = Cardinal.aleph 1) (c : L.Constants) :
    IsChainContinuous (L.Substructure M) := by
  intro B
  by_cases hB : B = ⊤
  · subst B
    exact top_chainSection_generated hJ hcard c
  · exact proper_chainSection_generated hLF hJ hcard c B hB

theorem exists_infinite_countable_proper (hJ : Jonsson L M)
    (hcard : Cardinal.mk M = Cardinal.aleph 1) :
    ∃ B : L.Substructure M,
      (B : Set M).Infinite ∧ (B : Set M).Countable ∧ B ≠ ⊤ := by
  classical
  letI : Infinite M := hJ.1
  letI : Countable (Σ n, L.Functions n) := hJ.2.1
  let e : ℕ ↪ M := Infinite.natEmbedding M
  let B : L.Substructure M := Substructure.closure L (Set.range e)
  have hcount : (B : Set M).Countable := by
    simpa only [B] using (Set.countable_range e).substructure_closure L
  have hinf : (B : Set M).Infinite := by
    apply (Set.infinite_range_of_injective e.injective).mono
    exact Substructure.subset_closure
  exact ⟨B, hinf, hcount, countable_substructure_ne_top hcard hcount⟩

theorem chainBelow_not_interpolates (hLF : LocallyFinite L M)
    (hJ : Jonsson L M) (hcard : Cardinal.mk M = Cardinal.aleph 1)
    (c : L.Constants) :
    ¬ Interpolates (ChainBelow (P := L.Substructure M)) := by
  obtain ⟨B, hBinf, _, hBproper⟩ := exists_infinite_countable_proper hJ hcard
  have hBtop : ChainBelow B (⊤ : L.Substructure M) :=
    (chainBelow_top_iff_proper hJ hcard c B).mpr hBproper
  intro hinterp
  obtain ⟨C, hBC, hCtop⟩ := hinterp B ⊤ hBtop
  have hCproper := (chainBelow_top_iff_proper hJ hcard c C).mp hCtop
  exact hBinf ((chainBelow_proper_iff_finite hLF hJ hcard c B C hCproper).mp hBC).2

/-- All displayed conclusions of source `thm:sharp`, for the algebra fixed in
its statement. The final witness proves strictness of the relation inclusion. -/
theorem sharp (hLF : LocallyFinite L M) (hJ : Jonsson L M)
    (hcard : Cardinal.mk M = Cardinal.aleph 1) (c : L.Constants) :
    IsDcpo (L.Substructure M) ∧
    IsChainContinuous (L.Substructure M) ∧
    (∀ S B : L.Substructure M, B ≠ ⊤ →
      (ChainBelow S B ↔ S ≤ B ∧ (S : Set M).Finite)) ∧
    (∀ S : L.Substructure M, ChainBelow S ⊤ ↔ S ≠ ⊤) ∧
    (∀ S B : L.Substructure M,
      WayBelow S B ↔ S ≤ B ∧ (S : Set M).Finite) ∧
    (∀ S B : L.Substructure M, WayBelow S B ↔ Square S B) ∧
    (∀ S B : L.Substructure M, WayBelow S B → ChainBelow S B) ∧
    (∃ S B : L.Substructure M, ChainBelow S B ∧ ¬ WayBelow S B) ∧
    ¬ Interpolates (ChainBelow (P := L.Substructure M)) := by
  have hchain := chainContinuous hLF hJ hcard c
  have hdcpo : IsDcpo (L.Substructure M) := completeLattice_dcpo
  have hproper := fun S B hB ↦ chainBelow_proper_iff_finite hLF hJ hcard c S B hB
  have htop := chainBelow_top_iff_proper hJ hcard c
  have hway := wayBelow_iff_finite hLF
  have hsquare := wayBelow_iff_square hdcpo hchain
  have hsub : ∀ S B : L.Substructure M, WayBelow S B → ChainBelow S B :=
    fun _ _ h ↦ h.chainBelow hdcpo
  obtain ⟨B, hBinf, _, hBproper⟩ := exists_infinite_countable_proper hJ hcard
  have hstrict : ChainBelow B (⊤ : L.Substructure M) ∧ ¬ WayBelow B ⊤ := by
    refine ⟨(htop B).mpr hBproper, ?_⟩
    intro hwayB
    exact hBinf ((hway B ⊤).mp hwayB).2
  exact ⟨hdcpo, hchain, hproper, htop, hway, hsquare, hsub,
    ⟨B, ⊤, hstrict⟩, chainBelow_not_interpolates hLF hJ hcard c⟩

end Algebra
end ChainApproximation
