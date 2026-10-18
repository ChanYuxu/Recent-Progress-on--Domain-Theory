import ChainApproximation.AlgebraBasics

/-! # Countable subalgebras and the aleph-one chain of generated subalgebras -/

set_option autoImplicit false

universe u

namespace ChainApproximation
namespace Algebra

open Set Cardinal FirstOrder
open FirstOrder.Language

variable {L : FirstOrder.Language.{u, u}} {M : Type u} [L.Structure M]

theorem countable_nat_approximation (hLF : LocallyFinite L M) (c : L.Constants)
    (B : L.Substructure M) (hB : (B : Set M).Countable) :
    ∃ f : ℕ → L.Substructure M, Monotone f ∧
      (∀ n, (f n : Set M).Finite ∧ f n ≤ B) ∧ IsLUB (Set.range f) B := by
  classical
  haveI : Nonempty B := (named_constant_nonempty c B).to_subtype
  haveI : Countable B := hB.to_subtype
  obtain ⟨e, he⟩ := exists_surjective_nat B
  let F : ℕ → Finset M := fun n ↦ (Finset.range n).image (fun i ↦ (e i).val)
  let f : ℕ → L.Substructure M := fun n ↦ Substructure.closure L (F n : Set M)
  have hFB : ∀ n, (F n : Set M) ⊆ B := by
    intro n x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact (e i).property
  have hfB : ∀ n, (f n : Set M).Finite ∧ f n ≤ B :=
    fun n ↦ ⟨hLF (F n), Substructure.closure_le.mpr (hFB n)⟩
  refine ⟨f, ?_, hfB, ?_, ?_⟩
  · intro n m hnm
    apply Substructure.closure_mono
    exact Finset.image_subset_image (Finset.range_mono hnm)
  · rintro _ ⟨n, rfl⟩
    exact (hfB n).2
  · intro C hC x hx
    obtain ⟨n, hn⟩ := he ⟨x, hx⟩
    apply hC (Set.mem_range_self (n + 1))
    apply Substructure.subset_closure
    exact Finset.mem_image.mpr ⟨n, Finset.mem_range.mpr (Nat.lt_succ_self n),
      congrArg Subtype.val hn⟩

/-- Source proper-section equation in `thm:sharp`. -/
theorem chainBelow_proper_iff_finite (hLF : LocallyFinite L M) (hJ : Jonsson L M)
    (hcard : Cardinal.mk M = Cardinal.aleph 1) (c : L.Constants)
    (S B : L.Substructure M) (hB : B ≠ ⊤) :
    ChainBelow S B ↔ S ≤ B ∧ (S : Set M).Finite := by
  constructor
  · intro hSB
    obtain ⟨f, hf, hmem, hLub⟩ := countable_nat_approximation hLF c B (proper_countable hJ hcard hB)
    obtain ⟨_, ⟨n, rfl⟩, hSn⟩ := (chainBelow_iff_sup completeLattice_dcpo S B).mp hSB
      (Set.range f) ⟨Set.range_nonempty _, hf.isChain_range⟩ B hLub le_rfl
    exact ⟨hSB.le, (hmem n).1.subset hSn⟩
  · rintro ⟨hSB, hS⟩
    exact (finite_wayBelow hS hSB).chainBelow completeLattice_dcpo

theorem carrier_not_countable (hcard : Cardinal.mk M = Cardinal.aleph 1) : ¬ Countable M := by
  intro hM
  have hle : Cardinal.mk M ≤ Cardinal.aleph0 := Cardinal.mk_le_aleph0_iff.mpr hM
  rw [hcard] at hle
  exact Cardinal.aleph0_lt_aleph_one.not_ge hle

theorem countable_substructure_ne_top (hcard : Cardinal.mk M = Cardinal.aleph 1)
    {B : L.Substructure M} (hB : (B : Set M).Countable) : B ≠ ⊤ := by
  intro hEq
  rw [hEq, Substructure.coe_top] at hB
  exact carrier_not_countable hcard (Set.countable_univ_iff.mp hB)

/-- The supremum of a countable nonempty chain of countable substructures is
countable. This is the finitary directed-union step used in `thm:sharp`. -/
theorem countable_sSup_of_countable_chain {C : Set (L.Substructure M)}
    (hC : NonemptyChain C) (hCC : C.Countable)
    (hmem : ∀ B ∈ C, (B : Set M).Countable) :
    ((sSup C : L.Substructure M) : Set M).Countable := by
  haveI : Countable C := hCC.to_subtype
  have heq : ((sSup C : L.Substructure M) : Set M) =
      ⋃ B : C, (B.val : Set M) := by
    ext x
    change x ∈ (sSup C : L.Substructure M) ↔ _
    rw [Substructure.mem_sSup_of_directedOn hC.1 hC.2.directedOn]
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨B, hBC, hxB⟩
      exact ⟨⟨B, hBC⟩, hxB⟩
    · rintro ⟨B, hxB⟩
      exact ⟨B.val, B.property, hxB⟩
  rw [heq]
  exact Set.countable_iUnion (fun B ↦ hmem B.val B.property)

/-- Every proper subalgebra is chain-below the top subalgebra. The proof
formalizes the source's countable-cofinal-subchain contradiction. -/
theorem proper_chainBelow_top (hJ : Jonsson L M)
    (hcard : Cardinal.mk M = Cardinal.aleph 1) (c : L.Constants)
    {B : L.Substructure M} (hB : B ≠ ⊤) : ChainBelow B ⊤ := by
  rw [chainBelow_iff_sup completeLattice_dcpo]
  intro C hC s hs htops
  have hst : s = ⊤ := top_unique htops
  subst s
  by_cases ht : (⊤ : L.Substructure M) ∈ C
  · exact ⟨⊤, ht, le_top⟩
  have hproper : ∀ E ∈ C, E ≠ (⊤ : L.Substructure M) := by
    intro E hEC hE
    exact ht (hE ▸ hEC)
  haveI : Nonempty B := (named_constant_nonempty c B).to_subtype
  have hBcount : (B : Set M).Countable := proper_countable hJ hcard hB
  haveI : Countable B := hBcount.to_subtype
  have hsup : sSup C = (⊤ : L.Substructure M) := (isLUB_sSup C).unique hs
  have hex : ∀ x : B, ∃ E, E ∈ C ∧ x.val ∈ E := by
    intro x
    apply (Substructure.mem_sSup_of_directedOn hC.1 hC.2.directedOn).mp
    rw [hsup]
    show x.val ∈ (⊤ : L.Substructure M)
    exact trivial
  choose g hgC hxg using hex
  change ∃ E ∈ C, B ≤ E
  by_contra hnone
  push Not at hnone
  let A : Set (L.Substructure M) := Set.range g
  have hAC : A ⊆ C := by
    rintro _ ⟨x, rfl⟩
    exact hgC x
  have hAchain : NonemptyChain A :=
    ⟨Set.range_nonempty g, hC.2.mono hAC⟩
  have hcof : ∀ E ∈ C, ∃ F ∈ A, E ≤ F := by
    intro E hEC
    have hnle : ¬ B ≤ E := hnone E hEC
    obtain ⟨x, hxB, hxE⟩ := SetLike.not_le_iff_exists.mp hnle
    let xb : B := ⟨x, hxB⟩
    refine ⟨g xb, Set.mem_range_self _, ?_⟩
    rcases hC.2.total hEC (hgC xb) with hEF | hFE
    · exact hEF
    · exact False.elim (hxE (hFE (hxg xb)))
  have hAsup : sSup A = (⊤ : L.Substructure M) := by
    apply le_antisymm le_top
    rw [← hsup]
    apply sSup_le
    intro E hEC
    obtain ⟨F, hFA, hEF⟩ := hcof E hEC
    exact hEF.trans (le_sSup hFA)
  have hcount : ((sSup A : L.Substructure M) : Set M).Countable :=
    countable_sSup_of_countable_chain hAchain (Set.countable_range g)
      (fun E hEA ↦ proper_countable hJ hcard (hproper E (hAC hEA)))
  rw [hAsup, Substructure.coe_top] at hcount
  exact carrier_not_countable hcard (Set.countable_univ_iff.mp hcount)

/-- A chain of countably generated, proper subalgebras has supremum top and
is cofinal among all proper subalgebras. This uses real language closure. -/
theorem aleph_one_top_approximation (hJ : Jonsson L M)
    (hcard : Cardinal.mk M = Cardinal.aleph 1) :
    ∃ f : CofinalIndex (Cardinal.aleph 1 : Cardinal.{u}) → L.Substructure M,
      Monotone f ∧ (∀ a, f a ≠ ⊤) ∧ IsLUB (Set.range f) ⊤ ∧
        ∀ B : L.Substructure M, B ≠ ⊤ → ∃ a, B ≤ f a := by
  classical
  haveI : Countable (Σ n, L.Functions n) := hJ.2.1
  let I : Type u := CofinalIndex (Cardinal.aleph 1 : Cardinal.{u})
  haveI : Nonempty I := Cardinal.mk_ne_zero_iff.mp (by
    rw [cofinalIndex_card]
    exact Cardinal.isRegular_aleph_one.ne_zero)
  haveI : NoMaxOrder I := Cardinal.noMaxOrder (Cardinal.aleph0_le_aleph 1)
  let e : I ≃ M := Classical.choice
    (Cardinal.eq.mp ((cofinalIndex_card (Cardinal.aleph 1 : Cardinal.{u})).trans hcard.symm))
  let f : I → L.Substructure M := fun a ↦ Substructure.closure L (e '' Set.Iio a)
  have hfmono : Monotone f := fun a b hab ↦ Substructure.closure_mono
    (Set.image_mono (Set.Iio_subset_Iio hab))
  have hfcount : ∀ a, (f a : Set M).Countable := by
    intro a
    have hinit : (Set.Iio a).Countable := Cardinal.le_aleph0_iff_set_countable.mp
      (Cardinal.lt_aleph_one_iff.mp (cofinalIndex_initial_small (Cardinal.aleph 1) a))
    simpa only [f] using (hinit.image e).substructure_closure L
  have hfproper : ∀ a, f a ≠ ⊤ := fun a ↦ countable_substructure_ne_top hcard (hfcount a)
  have hI : HasCofinalChain I :=
    ⟨Set.univ, ⟨Set.univ_nonempty, fun _ _ _ _ _ ↦ le_total _ _⟩, IsCofinal.univ⟩
  have hIcof : Order.cof I = Cardinal.aleph 1 := regular_cofinalIndex_cof Cardinal.isRegular_aleph_one
  refine ⟨f, hfmono, hfproper, ⟨?_, ?_⟩, ?_⟩
  · exact fun _ _ ↦ le_top
  · intro B hB x _
    obtain ⟨a, hax⟩ := e.surjective x
    obtain ⟨b, hab⟩ := exists_gt a
    apply hB (Set.mem_range_self b)
    apply Substructure.subset_closure
    exact ⟨a, hab, hax⟩
  · intro B hB
    have hcount := proper_countable hJ hcard hB
    have hidx : (e.symm '' (B : Set M)).Countable := hcount.image e.symm
    have hsmall : Cardinal.mk (e.symm '' (B : Set M)) < Order.cof I := by
      rw [hIcof]
      exact (Cardinal.le_aleph0_iff_set_countable.mpr hidx).trans_lt Cardinal.aleph0_lt_aleph_one
    obtain ⟨a, ha⟩ := hI.small_bounded (e.symm '' (B : Set M)) hsmall
    obtain ⟨b, hab⟩ := exists_gt a
    refine ⟨b, ?_⟩
    intro x hx
    apply Substructure.subset_closure
    exact ⟨e.symm x, (ha ⟨x, hx, rfl⟩).trans_lt hab, e.apply_symm_apply x⟩

theorem top_not_chainBelow_self (hJ : Jonsson L M)
    (hcard : Cardinal.mk M = Cardinal.aleph 1) :
    ¬ ChainBelow (⊤ : L.Substructure M) ⊤ := by
  obtain ⟨f, hf, hproper, hLub, _⟩ := aleph_one_top_approximation hJ hcard
  haveI : Nonempty (CofinalIndex (Cardinal.aleph 1 : Cardinal.{u})) :=
    Cardinal.mk_ne_zero_iff.mp (by
    rw [cofinalIndex_card]
    exact Cardinal.isRegular_aleph_one.ne_zero)
  intro htop
  obtain ⟨_, ⟨a, rfl⟩, hta⟩ := (chainBelow_iff_sup completeLattice_dcpo ⊤ ⊤).mp htop
    (Set.range f) ⟨Set.range_nonempty _, hf.isChain_range⟩ ⊤ hLub le_rfl
  exact hproper a (top_le_iff.mp hta)

end Algebra
end ChainApproximation
