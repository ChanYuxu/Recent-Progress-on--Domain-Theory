import ChainApproximation.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Pairing
import Mathlib.SetTheory.Cardinal.Arithmetic

/-!
# Finite and countable directed-set support

These are proved support lemmas for the source's countable union argument
and the full Iwamura/Markowsky completeness bridge. No cofinal-chain
existence for an arbitrary directed set is assumed.
-/

set_option autoImplicit false

universe u

namespace ChainApproximation

open Set Cardinal

variable {P : Type u} [PartialOrder P]

theorem NonemptyDirected.finite_bound {D : Set P} (hD : NonemptyDirected D)
    (F : Finset P) (hF : (F : Set P) ⊆ D) : ∃ d ∈ D, ∀ x ∈ F, x ≤ d := by
  classical
  induction F using Finset.induction_on with
  | empty =>
    obtain ⟨d, hd⟩ := hD.1
    exact ⟨d, hd, by simp⟩
  | @insert x F hx ih =>
    obtain ⟨d, hd, hFd⟩ := ih (fun a ha ↦ hF (Finset.mem_insert_of_mem ha))
    obtain ⟨e, he, hxe, hde⟩ := hD.2 x (hF (Finset.mem_insert_self _ _)) d hd
    refine ⟨e, he, ?_⟩
    intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact hxe
    · exact (hFd a ha).trans hde

private noncomputable def cumulativeSub {D : Set P} (hD : NonemptyDirected D)
    (a : ℕ → P) (ha : ∀ n, a n ∈ D) : ℕ → D
  | 0 => ⟨a 0, ha 0⟩
  | n + 1 =>
    let h := hD.2 (cumulativeSub hD a ha n).val (cumulativeSub hD a ha n).property
      (a (n + 1)) (ha (n + 1))
    ⟨Classical.choose h, (Classical.choose_spec h).1⟩

noncomputable def cumulative {D : Set P} (hD : NonemptyDirected D)
    (a : ℕ → P) (ha : ∀ n, a n ∈ D) (n : ℕ) : P := (cumulativeSub hD a ha n).val

theorem cumulative_mem {D : Set P} (hD : NonemptyDirected D)
    (a : ℕ → P) (ha : ∀ n, a n ∈ D) (n : ℕ) : cumulative hD a ha n ∈ D :=
  (cumulativeSub hD a ha n).property

theorem cumulative_step {D : Set P} (hD : NonemptyDirected D)
    (a : ℕ → P) (ha : ∀ n, a n ∈ D) (n : ℕ) :
    cumulative hD a ha n ≤ cumulative hD a ha (n + 1) := by
  exact (Classical.choose_spec (hD.2 (cumulativeSub hD a ha n).val
    (cumulativeSub hD a ha n).property (a (n + 1)) (ha (n + 1)))).2.1

theorem le_cumulative {D : Set P} (hD : NonemptyDirected D)
    (a : ℕ → P) (ha : ∀ n, a n ∈ D) (n : ℕ) : a n ≤ cumulative hD a ha n := by
  cases n with
  | zero => exact le_rfl
  | succ n =>
    exact (Classical.choose_spec (hD.2 (cumulativeSub hD a ha n).val
      (cumulativeSub hD a ha n).property (a (n + 1)) (ha (n + 1)))).2.2

theorem cumulative_monotone {D : Set P} (hD : NonemptyDirected D)
    (a : ℕ → P) (ha : ∀ n, a n ∈ D) : Monotone (cumulative hD a ha) :=
  monotone_nat_of_le_succ (cumulative_step hD a ha)

theorem countable_cofinal_chain {D A : Set P} (hD : NonemptyDirected D)
    (hA : A.Countable) (hAD : A ⊆ D) (hcof : ∀ d ∈ D, ∃ a ∈ A, d ≤ a) :
    ∃ a : ℕ → P, Monotone a ∧ (∀ n, a n ∈ D) ∧
      ∀ d ∈ D, ∃ n, d ≤ a n := by
  classical
  have hne : A.Nonempty := by
    obtain ⟨d, hd⟩ := hD.1
    obtain ⟨a, ha, _⟩ := hcof d hd
    exact ⟨a, ha⟩
  haveI : Nonempty A := hne.to_subtype
  haveI : Countable A := hA.to_subtype
  obtain ⟨e, he⟩ := exists_surjective_nat A
  let b : ℕ → P := fun n ↦ (e n).val
  have hb : ∀ n, b n ∈ D := fun n ↦ hAD (e n).property
  refine ⟨cumulative hD b hb, cumulative_monotone hD b hb,
    cumulative_mem hD b hb, ?_⟩
  intro d hd
  obtain ⟨a, ha, hda⟩ := hcof d hd
  obtain ⟨n, hn⟩ := he ⟨a, ha⟩
  refine ⟨n, hda.trans ?_⟩
  have hbn : b n = a := congrArg Subtype.val hn
  simpa only [hbn] using le_cumulative hD b hb n

theorem countable_directed_cofinal_chain {D : Set P} (hD : NonemptyDirected D)
    (hcount : D.Countable) :
    ∃ a : ℕ → P, Monotone a ∧ (∀ n, a n ∈ D) ∧ ∀ d ∈ D, ∃ n, d ≤ a n :=
  countable_cofinal_chain hD hcount Set.Subset.rfl (fun d hd ↦ ⟨d, hd, le_rfl⟩)

theorem isLUB_of_cofinal_range {D : Set P} {a : ℕ → P} {s : P}
    (ha : ∀ n, a n ∈ D) (hcof : ∀ d ∈ D, ∃ n, d ≤ a n)
    (hs : IsLUB (Set.range a) s) : IsLUB D s := by
  constructor
  · intro d hd
    obtain ⟨n, hdn⟩ := hcof d hd
    exact hdn.trans (hs.1 (Set.mem_range_self n))
  · intro p hp
    apply hs.2
    rintro _ ⟨n, rfl⟩
    exact hp (ha n)

private def previousChoices {I : Type u} [PartialOrder I]
    (s : Finset I) (rec : ∀ t : Finset I, t ⊂ s → I) : Set I :=
  {x | ∃ (t : Finset I) (ht : t ⊂ s), x = rec t ht}

private theorem previousChoices_finite {I : Type u} [PartialOrder I]
    (s : Finset I) (rec : ∀ t : Finset I, t ⊂ s → I) :
    (previousChoices s rec).Finite := by
  classical
  have hT : ({t : Finset I | t ⊂ s} : Set (Finset I)).Finite :=
    s.ssubsets.finite_toSet.subset (fun _ ht ↦ Finset.mem_ssubsets.mpr ht)
  haveI : Fintype {t : Finset I // t ⊂ s} := hT.fintype
  have heq : previousChoices s rec = Set.range (fun t : {t : Finset I // t ⊂ s} ↦ rec t.val t.property) := by
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨⟨t, ht⟩, rfl⟩
    · rintro ⟨t, rfl⟩
      exact ⟨t.val, t.property, rfl⟩
  rw [heq]
  exact Set.finite_range _

private noncomputable def coherentStep {I : Type u} [PartialOrder I]
    (hI : NonemptyDirected (Set.univ : Set I)) (s : Finset I)
    (rec : ∀ t : Finset I, t ⊂ s → I) : I :=
  Classical.choose (hI.finite_bound
    ((s.finite_toSet.union (previousChoices_finite s rec)).toFinset)
    (by simp))

private theorem coherentStep_spec {I : Type u} [PartialOrder I]
    (hI : NonemptyDirected (Set.univ : Set I)) (s : Finset I)
    (rec : ∀ t : Finset I, t ⊂ s → I) :
    (∀ i ∈ s, i ≤ coherentStep hI s rec) ∧
      ∀ t : Finset I, ∀ ht : t ⊂ s, rec t ht ≤ coherentStep hI s rec := by
  classical
  have h := Classical.choose_spec (hI.finite_bound
    ((s.finite_toSet.union (previousChoices_finite s rec)).toFinset) (by simp))
  constructor
  · intro i hi
    apply h.2 i
    simpa only [Set.Finite.mem_toFinset] using (show i ∈ (s : Set I) ∪ previousChoices s rec from Or.inl hi)
  · intro t ht
    apply h.2 (rec t ht)
    simpa only [Set.Finite.mem_toFinset] using
      (show rec t ht ∈ (s : Set I) ∪ previousChoices s rec from Or.inr ⟨t, ht, rfl⟩)

noncomputable def coherentUpper {I : Type u} [PartialOrder I]
    (hI : NonemptyDirected (Set.univ : Set I)) : Finset I → I :=
  Finset.strongInduction (fun s rec ↦ coherentStep hI s rec)

theorem le_coherentUpper {I : Type u} [PartialOrder I]
    (hI : NonemptyDirected (Set.univ : Set I)) {s : Finset I} {i : I} (hi : i ∈ s) :
    i ≤ coherentUpper hI s := by
  rw [show coherentUpper hI s = coherentStep hI s (fun t _ ↦ coherentUpper hI t) by
    rw [coherentUpper, Finset.strongInduction_eq]]
  exact (coherentStep_spec hI s _).1 i hi

theorem coherentUpper_monotone {I : Type u} [PartialOrder I]
    (hI : NonemptyDirected (Set.univ : Set I)) : Monotone (coherentUpper hI) := by
  intro s t hst
  by_cases heq : s = t
  · subst s
    exact le_rfl
  · have hsub : s ⊂ t := Finset.ssubset_iff_subset_ne.mpr ⟨hst, heq⟩
    rw [show coherentUpper hI t = coherentStep hI t (fun r _ ↦ coherentUpper hI r) by
      rw [coherentUpper, Finset.strongInduction_eq]]
    exact (coherentStep_spec hI t (fun r _ ↦ coherentUpper hI r)).2 s hsub

theorem mk_finset_le_max (I : Type u) : Cardinal.mk (Finset I) ≤ max (Cardinal.mk I) Cardinal.aleph0 := by
  cases finite_or_infinite I with
  | inl h =>
    letI := h
    exact Cardinal.mk_le_aleph0.trans (le_max_right _ _)
  | inr h =>
    letI := h
    rw [Cardinal.mk_finset_of_infinite]
    exact le_max_left _ _

end ChainApproximation
