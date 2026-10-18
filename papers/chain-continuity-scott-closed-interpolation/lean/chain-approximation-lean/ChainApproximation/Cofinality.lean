import ChainApproximation.DirectedTools
import Mathlib.SetTheory.Cardinal.Regular
import Mathlib.SetTheory.Ordinal.Basic

/-!
# Cofinality of posets admitting cofinal chains

Source: `lem:regularity` and the support for `lem:mismatch`.
`Order.cof` is the genuine minimum cardinal of cofinal subsets.
The initial-segment bound does not presume regularity; regularity is
derived after constructing a cofinal strictly increasing ordinal chain.
-/

set_option autoImplicit false

universe u

namespace ChainApproximation

open Set Cardinal

variable {P : Type u} [PartialOrder P]

def HasCofinalChain (P : Type u) [PartialOrder P] : Prop :=
  ∃ C : Set P, NonemptyChain C ∧ IsCofinal C

@[reducible] noncomputable def chainLinearOrder (C : Set P) (hC : IsChain (· ≤ ·) C) : LinearOrder C where
  toPartialOrder := inferInstance
  le_total x y := hC.total x.property y.property
  toDecidableLE := Classical.decRel _

theorem cof_subtype_eq {C : Set P} (hC : IsCofinal C) : Order.cof C = Order.cof P := by
  classical
  apply le_antisymm
  · obtain ⟨A, hA, hcard⟩ := Order.cof_eq P
    have hex : ∀ a : A, ∃ c : C, a.val ≤ c.val := by
      intro a
      obtain ⟨c, hc, hac⟩ := hC a.val
      exact ⟨⟨c, hc⟩, hac⟩
    choose f hf using hex
    have hF : IsCofinal (Set.range f) := by
      intro c
      obtain ⟨a, ha, hca⟩ := hA c.val
      exact ⟨f ⟨a, ha⟩, Set.mem_range_self _, hca.trans (hf ⟨a, ha⟩)⟩
    exact (Order.cof_le hF).trans (Cardinal.mk_range_le.trans_eq hcard)
  · obtain ⟨A, hA, hcard⟩ := Order.cof_eq C
    have hF : IsCofinal (Subtype.val '' A : Set P) := by
      intro p
      obtain ⟨c, hc, hpc⟩ := hC p
      obtain ⟨a, ha, hca⟩ := hA ⟨c, hc⟩
      exact ⟨a.val, ⟨a, ha, rfl⟩, hpc.trans hca⟩
    exact (Order.cof_le hF).trans (Cardinal.mk_image_le.trans_eq hcard)

theorem HasCofinalChain.nonempty (hP : HasCofinalChain P) : Nonempty P := by
  obtain ⟨C, hC, _⟩ := hP
  obtain ⟨c, _⟩ := hC.1
  exact ⟨c⟩

theorem HasCofinalChain.directed (hP : HasCofinalChain P) :
    NonemptyDirected (Set.univ : Set P) := by
  obtain ⟨C, hC, hcof⟩ := hP
  refine ⟨hC.1.mono (Set.subset_univ _), ?_⟩
  intro a _ b _
  obtain ⟨c, hc, hac⟩ := hcof a
  obtain ⟨d, hd, hbd⟩ := hcof b
  obtain ⟨e, _, hce, hde⟩ := hC.2.directedOn c hc d hd
  exact ⟨e, trivial, hac.trans hce, hbd.trans hde⟩

/-- Bounding small subsets uses minimal cofinality and a cofinal chain,
not an unproved regularity assumption. -/
theorem HasCofinalChain.small_bounded (hP : HasCofinalChain P)
    (A : Set P) (hA : Cardinal.mk A < Order.cof P) : BddAbove A := by
  classical
  obtain ⟨C, hC, hcof⟩ := hP
  have hex : ∀ a : A, ∃ c : P, c ∈ C ∧ a.val ≤ c := fun a ↦ hcof a.val
  choose f hf hle using hex
  have hnot : ¬ IsCofinal (Set.range f) := by
    intro hF
    exact not_le_of_gt hA ((Order.cof_le hF).trans Cardinal.mk_range_le)
  obtain ⟨p, hp⟩ := not_forall.mp hnot
  obtain ⟨c, hc, hpc⟩ := hcof p
  refine ⟨c, ?_⟩
  intro a ha
  have hfa : ¬ p ≤ f ⟨a, ha⟩ := fun h ↦ hp ⟨_, Set.mem_range_self _, h⟩
  rcases hC.2.total (hf ⟨a, ha⟩) hc with hfc | hcf
  · exact (hle ⟨a, ha⟩).trans hfc
  · exact False.elim (hfa (hpc.trans hcf))

theorem HasCofinalChain.aleph0_le (hP : HasCofinalChain P)
    (hne : Order.cof P ≠ 1) : Cardinal.aleph0 ≤ Order.cof P := by
  obtain ⟨C, hC, hcof⟩ := hP
  letI : LinearOrder C := chainLinearOrder C hC.2
  haveI : Nonempty C := hC.1.to_subtype
  rw [← cof_subtype_eq hcof] at hne ⊢
  apply Order.aleph0_le_cof_iff.mpr
  have hzero := Order.cof_ne_zero (α := C)
  exact lt_of_le_of_ne (Cardinal.one_le_iff_ne_zero.mpr hzero) (Ne.symm hne)

theorem HasCofinalChain.exists_gt (hP : HasCofinalChain P)
    (hne : Order.cof P ≠ 1) (p : P) : ∃ q : P, p < q := by
  by_contra hnone
  apply hne
  apply Order.cof_eq_one_iff.mpr
  refine ⟨p, ?_⟩
  intro q
  obtain ⟨r, _, hpr, hqr⟩ := hP.directed.2 p trivial q trivial
  have hrp : r ≤ p := by
    by_contra hrp
    exact hnone ⟨r, lt_iff_le_not_ge.mpr ⟨hpr, hrp⟩⟩
  exact hqr.trans hrp

abbrev CofinalIndex (κ : Cardinal.{u}) := κ.ord.ToType

theorem cofinalIndex_card (κ : Cardinal.{u}) : Cardinal.mk (CofinalIndex κ) = κ :=
  Cardinal.mk_ord_toType κ

theorem cofinalIndex_initial_small (κ : Cardinal.{u}) (α : CofinalIndex κ) :
    Cardinal.mk (Set.Iio α) < κ := by
  have hinit : Cardinal.ord (Cardinal.mk (CofinalIndex κ)) =
      Ordinal.type (fun (a b : CofinalIndex κ) ↦ a < b) := by
    rw [cofinalIndex_card]
    exact (Ordinal.type_toType κ.ord).symm
  simpa only [cofinalIndex_card] using Cardinal.mk_Iio_lt α hinit

omit [PartialOrder P] in
theorem card_insert_range_lt {I : Type u} [LinearOrder I] {κ : Cardinal.{u}}
    (hκ : Cardinal.aleph0 ≤ κ) (hI : Cardinal.mk I < κ) (f : I → P) (p : P) :
    Cardinal.mk (insert p (Set.range f) : Set P) < κ := by
  calc
    Cardinal.mk (insert p (Set.range f) : Set P) ≤ 1 + Cardinal.mk (Set.range f) := by
      simpa only [Set.singleton_union, Cardinal.mk_singleton] using
        Cardinal.mk_union_le ({p} : Set P) (Set.range f)
    _ ≤ max (Cardinal.mk I) 1 + max (Cardinal.mk I) 1 :=
      add_le_add (le_max_right _ _) (Cardinal.mk_range_le.trans (le_max_left _ _))
    _ < κ := by
      by_cases hinf : Cardinal.aleph0 ≤ max (Cardinal.mk I) 1
      · rw [Cardinal.add_eq_self hinf]
        exact max_lt hI (Cardinal.one_lt_aleph0.trans_le hκ)
      · have hfin : max (Cardinal.mk I) 1 < Cardinal.aleph0 := lt_of_not_ge hinf
        exact (Cardinal.add_lt_aleph0 hfin hfin).trans_le hκ

theorem IsChainContinuous.section_hasCofinalChain (hP : IsChainContinuous P) (p : P) :
    HasCofinalChain (chainSection p) := by
  obtain ⟨C, hC, hCI, hcof, _⟩ := hP.exists_chain p
  let B : Set (chainSection p) := Subtype.val ⁻¹' C
  have hne : B.Nonempty := by
    obtain ⟨c, hc⟩ := hC.1
    exact ⟨⟨c, hCI hc⟩, hc⟩
  have hchain : IsChain (· ≤ ·) B := by
    intro a ha b hb _
    exact hC.2.total ha hb
  refine ⟨B, ⟨hne, hchain⟩, ?_⟩
  intro a
  obtain ⟨c, hc, hac⟩ := hcof a.val a.property
  exact ⟨⟨c, hCI hc⟩, hc, hac⟩

private theorem cofinalStep_exists (hP : HasCofinalChain P) (hne : Order.cof P ≠ 1)
    (a : CofinalIndex (Order.cof P) → P) (i : CofinalIndex (Order.cof P))
    (rec : ∀ j, j < i → P) :
    ∃ q : P, a i ≤ q ∧ ∀ j (hji : j < i), rec j hji < q := by
  let g : Set.Iio i → P := fun j ↦ rec j.val j.property
  obtain ⟨p, hp⟩ := hP.small_bounded (insert (a i) (Set.range g))
    (card_insert_range_lt (hP.aleph0_le hne)
      (cofinalIndex_initial_small (Order.cof P) i) g (a i))
  obtain ⟨q, hpq⟩ := hP.exists_gt hne p
  refine ⟨q, (hp (Set.mem_insert _ _)).trans hpq.le, ?_⟩
  intro j hji
  exact (hp (Set.mem_insert_of_mem _ (Set.mem_range_self ⟨j, hji⟩))).trans_lt hpq

private noncomputable def cofinalSequence (hP : HasCofinalChain P)
    (hne : Order.cof P ≠ 1) (a : CofinalIndex (Order.cof P) → P) :
    CofinalIndex (Order.cof P) → P :=
  wellFounded_lt.fix (fun i rec ↦ Classical.choose (cofinalStep_exists hP hne a i rec))

private theorem cofinalSequence_spec (hP : HasCofinalChain P)
    (hne : Order.cof P ≠ 1) (a : CofinalIndex (Order.cof P) → P)
    (i : CofinalIndex (Order.cof P)) :
    a i ≤ cofinalSequence hP hne a i ∧
      ∀ j, j < i → cofinalSequence hP hne a j < cofinalSequence hP hne a i := by
  have h := Classical.choose_spec (cofinalStep_exists hP hne a i
    (fun j _ ↦ cofinalSequence hP hne a j))
  convert h using 1 <;>
    rw [show cofinalSequence hP hne a i = Classical.choose (cofinalStep_exists hP hne a i
      (fun j _ ↦ cofinalSequence hP hne a j)) by
      rw [cofinalSequence, WellFounded.fix_eq]]

/-- The strictly increasing cofinal sequence asserted in source
`lem:regularity`; its construction precedes the regularity conclusion. -/
theorem HasCofinalChain.strictMono_cofinal (hP : HasCofinalChain P)
    (hne : Order.cof P ≠ 1) :
    ∃ f : CofinalIndex (Order.cof P) → P, StrictMono f ∧ IsCofinal (Set.range f) := by
  classical
  obtain ⟨A, hA, hcard⟩ := Order.cof_eq P
  let e : CofinalIndex (Order.cof P) ≃ A :=
    Classical.choice (Cardinal.eq.mp ((cofinalIndex_card _).trans hcard.symm))
  let a : CofinalIndex (Order.cof P) → P := fun i ↦ (e i).val
  refine ⟨cofinalSequence hP hne a, ?_, ?_⟩
  · intro i j hij
    exact (cofinalSequence_spec hP hne a j).2 i hij
  · intro p
    obtain ⟨b, hb, hpb⟩ := hA p
    let i := e.symm ⟨b, hb⟩
    refine ⟨cofinalSequence hP hne a i, Set.mem_range_self _, hpb.trans ?_⟩
    have hai : a i = b := congrArg Subtype.val (e.apply_symm_apply ⟨b, hb⟩)
    simpa only [hai] using (cofinalSequence_spec hP hne a i).1

theorem cof_eq_of_strictMono_cofinal {I : Type u} [LinearOrder I]
    {f : I → P} (hf : StrictMono f) (hcof : IsCofinal (Set.range f)) :
    Order.cof I = Order.cof P := by
  classical
  apply le_antisymm
  · obtain ⟨A, hA, hcard⟩ := Order.cof_eq P
    have hex : ∀ a : A, ∃ i, a.val ≤ f i := by
      intro a
      obtain ⟨_, ⟨i, rfl⟩, hai⟩ := hcof a.val
      exact ⟨i, hai⟩
    choose g hg using hex
    have hG : IsCofinal (Set.range g) := by
      intro i
      obtain ⟨a, ha, hia⟩ := hA (f i)
      exact ⟨g ⟨a, ha⟩, Set.mem_range_self _, hf.le_iff_le.mp (hia.trans (hg ⟨a, ha⟩))⟩
    exact (Order.cof_le hG).trans (Cardinal.mk_range_le.trans_eq hcard)
  · obtain ⟨A, hA, hcard⟩ := Order.cof_eq I
    have hF : IsCofinal (f '' A) := by
      intro p
      obtain ⟨_, ⟨i, rfl⟩, hpi⟩ := hcof p
      obtain ⟨j, hj, hij⟩ := hA i
      exact ⟨f j, ⟨j, hj, rfl⟩, hpi.trans (hf.monotone hij)⟩
    exact (Order.cof_le hF).trans (Cardinal.mk_image_le.trans_eq hcard)

/-- Source `lem:regularity`, including regularity of the minimal cofinal
cardinal. Cofinality one is left as the explicit greatest-element case. -/
theorem HasCofinalChain.regular (hP : HasCofinalChain P) (hne : Order.cof P ≠ 1) :
    Cardinal.IsRegular (Order.cof P) := by
  obtain ⟨f, hf, hcof⟩ := hP.strictMono_cofinal hne
  have heq : (Order.cof P).ord.cof = Order.cof P := by
    rw [← Ordinal.cof_toType]
    exact cof_eq_of_strictMono_cofinal hf hcof
  exact ⟨hP.aleph0_le hne, heq.ge⟩

theorem chain_subtype_hasCofinalChain {C : Set P} (hC : NonemptyChain C) :
    HasCofinalChain C := by
  refine ⟨Set.univ, ⟨?_, ?_⟩, IsCofinal.univ⟩
  · obtain ⟨c, hc⟩ := hC.1
    exact ⟨⟨c, hc⟩, trivial⟩
  · intro a _ b _ _
    exact hC.2.total a.property b.property

/-- Source `lem:mismatch`. The proof uses the two possible cardinal
inequalities and does not assume that arbitrary directed sets have cofinal chains. -/
theorem HasCofinalChain.chain_bounded_of_cof_ne (hP : HasCofinalChain P)
    {C : Set P} (hC : NonemptyChain C) (hne : Order.cof C ≠ Order.cof P) :
    BddAbove C := by
  classical
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · obtain ⟨A, hA, hcard⟩ := Order.cof_eq C
    obtain ⟨p, hp⟩ := hP.small_bounded (Subtype.val '' A)
      (Cardinal.mk_image_le.trans_lt (hcard.trans_lt hlt))
    refine ⟨p, ?_⟩
    intro c hc
    obtain ⟨a, ha, hca⟩ := hA ⟨c, hc⟩
    exact (show c ≤ a.val from hca).trans (hp ⟨a, ha, rfl⟩)
  · by_contra hbound
    obtain ⟨A, hA, hcard⟩ := Order.cof_eq P
    have hex : ∀ a : A, ∃ c : C, ¬ c.val ≤ a.val := by
      intro a
      by_contra hn
      push Not at hn
      exact hbound ⟨a.val, fun c hc ↦ hn ⟨c, hc⟩⟩
    choose g hg using hex
    obtain ⟨c, hc⟩ := (chain_subtype_hasCofinalChain hC).small_bounded (Set.range g)
      (Cardinal.mk_range_le.trans_lt (hcard.trans_lt hgt))
    obtain ⟨a, ha, hca⟩ := hA c.val
    exact hg ⟨a, ha⟩ ((show (g ⟨a, ha⟩).val ≤ c.val from
      hc (Set.mem_range_self _)).trans hca)

/-- A useful strengthened form of the mismatch lemma: a monotone image
between two posets with cofinal chains is bounded when cofinalities differ. -/
theorem HasCofinalChain.range_bounded_of_cof_ne {Q : Type u} [PartialOrder Q]
    (hP : HasCofinalChain P) (hQ : HasCofinalChain Q)
    (f : P → Q) (hf : Monotone f) (hne : Order.cof P ≠ Order.cof Q) :
    BddAbove (Set.range f) := by
  classical
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · obtain ⟨A, hA, hcard⟩ := Order.cof_eq P
    obtain ⟨q, hq⟩ := hQ.small_bounded (f '' A)
      (Cardinal.mk_image_le.trans_lt (hcard.trans_lt hlt))
    refine ⟨q, ?_⟩
    rintro _ ⟨p, rfl⟩
    obtain ⟨a, ha, hpa⟩ := hA p
    exact (hf hpa).trans (hq ⟨a, ha, rfl⟩)
  · by_contra hbound
    obtain ⟨A, hA, hcard⟩ := Order.cof_eq Q
    have hex : ∀ a : A, ∃ p : P, ¬ f p ≤ a.val := by
      intro a
      by_contra hn
      push Not at hn
      exact hbound ⟨a.val, by rintro _ ⟨p, rfl⟩; exact hn p⟩
    choose g hg using hex
    obtain ⟨p, hp⟩ := hP.small_bounded (Set.range g)
      (Cardinal.mk_range_le.trans_lt (hcard.trans_lt hgt))
    obtain ⟨a, ha, hpa⟩ := hA (f p)
    exact hg ⟨a, ha⟩ ((hf (hp (Set.mem_range_self _))).trans hpa)

theorem lowerHull_hasCofinalChain {C : Set P} (hC : NonemptyChain C) :
    HasCofinalChain (lowerHull C) := by
  let B : Set (lowerHull C) := Subtype.val ⁻¹' C
  refine ⟨B, ⟨?_, ?_⟩, ?_⟩
  · obtain ⟨c, hc⟩ := hC.1
    exact ⟨⟨c, c, hc, le_rfl⟩, hc⟩
  · intro a ha b hb _
    exact hC.2.total ha hb
  · rintro ⟨p, c, hc, hpc⟩
    exact ⟨⟨c, c, hc, le_rfl⟩, hc, hpc⟩

theorem cof_lowerHull {C : Set P} (_hC : NonemptyChain C) :
    Order.cof (lowerHull C) = Order.cof C := by
  classical
  apply le_antisymm
  · obtain ⟨A, hA, hcard⟩ := Order.cof_eq C
    let f : C → lowerHull C := fun c ↦ ⟨c.val, c.val, c.property, le_rfl⟩
    have hcof : IsCofinal (f '' A) := by
      rintro ⟨p, c, hc, hpc⟩
      obtain ⟨a, ha, hca⟩ := hA ⟨c, hc⟩
      exact ⟨f a, ⟨a, ha, rfl⟩, hpc.trans hca⟩
    exact (Order.cof_le hcof).trans (Cardinal.mk_image_le.trans_eq hcard)
  · obtain ⟨A, hA, hcard⟩ := Order.cof_eq (lowerHull C)
    have hex : ∀ a : A, ∃ c : C, a.val.val ≤ c.val := by
      intro a
      obtain ⟨c, hc, hac⟩ := a.val.property
      exact ⟨⟨c, hc⟩, hac⟩
    choose f hf using hex
    have hcof : IsCofinal (Set.range f) := by
      intro c
      obtain ⟨a, ha, hca⟩ := hA ⟨c.val, c.val, c.property, le_rfl⟩
      exact ⟨f ⟨a, ha⟩, Set.mem_range_self _,
        (show c.val ≤ a.val from hca).trans (hf ⟨a, ha⟩)⟩
    exact (Order.cof_le hcof).trans (Cardinal.mk_range_le.trans_eq hcard)

theorem HasCofinalChain.enumerate (_hP : HasCofinalChain P) :
    ∃ f : CofinalIndex (Order.cof P) → P, IsCofinal (Set.range f) := by
  classical
  obtain ⟨A, hA, hcard⟩ := Order.cof_eq P
  let e : CofinalIndex (Order.cof P) ≃ A :=
    Classical.choice (Cardinal.eq.mp ((cofinalIndex_card _).trans hcard.symm))
  refine ⟨fun i ↦ (e i).val, ?_⟩
  intro p
  obtain ⟨a, ha, hpa⟩ := hA p
  refine ⟨(e (e.symm ⟨a, ha⟩)).val, Set.mem_range_self _, ?_⟩
  simpa only [e.apply_symm_apply] using hpa

end ChainApproximation
