import ChainApproximation.LongChains
import Mathlib.SetTheory.Cardinal.Arithmetic

/-!
# The non-dcpo precontinuity counterexample

This is the poset from source `thm:precontinuous-counterexample`: finite
subsets of an initial ordinal of cardinality `aleph 1`, the special points
`u_{xi,alpha}`, and a greatest point.
-/

set_option autoImplicit false

namespace ChainApproximation
namespace PrecontinuousExample

open Set Cardinal

abbrev I := CofinalIndex (Cardinal.aleph 1 : Cardinal.{0})

noncomputable instance : Nonempty I := Cardinal.mk_ne_zero_iff.mp (by
  rw [cofinalIndex_card]
  exact Cardinal.isRegular_aleph_one.ne_zero)

noncomputable instance : Infinite I := Cardinal.aleph0_le_mk_iff.mp (by
  rw [cofinalIndex_card]
  exact Cardinal.aleph0_le_aleph 1)

noncomputable instance : NoMaxOrder I :=
  Cardinal.noMaxOrder (Cardinal.aleph0_le_aleph 1)

/-- The source indices `xi < alpha < omega_1`, with `alpha` infinite. -/
structure UpperIndex where
  xi : I
  alpha : I
  xi_lt : xi < alpha
  infinite_Iio : (Set.Iio alpha).Infinite

def UpperIndex.support (u : UpperIndex) : Set I := Set.Iio u.alpha \ {u.xi}

/-- Finite points, special upper points, and the greatest point. -/
inductive Point
  | fin : Finset I → Point
  | upper : UpperIndex → Point
  | top : Point

def Point.LE : Point → Point → Prop
  | .fin G, .fin H => G ⊆ H
  | .fin G, .upper u => (G : Set I) ⊆ u.support
  | .fin _, .top => True
  | .upper u, .upper v => u = v
  | .upper _, .top => True
  | .top, .top => True
  | _, _ => False

instance : LE Point := ⟨Point.LE⟩

@[simp] theorem fin_le_fin {G H : Finset I} : Point.fin G ≤ Point.fin H ↔ G ⊆ H := Iff.rfl
@[simp] theorem fin_le_upper {G : Finset I} {u : UpperIndex} :
    Point.fin G ≤ Point.upper u ↔ (G : Set I) ⊆ u.support := Iff.rfl
@[simp] theorem fin_le_top (G : Finset I) : Point.fin G ≤ Point.top := trivial
@[simp] theorem upper_le_upper {u v : UpperIndex} :
    Point.upper u ≤ Point.upper v ↔ u = v := Iff.rfl
@[simp] theorem upper_le_top (u : UpperIndex) : Point.upper u ≤ Point.top := trivial
@[simp] theorem top_le_top : Point.top ≤ Point.top := trivial
@[simp] theorem upper_not_le_fin (u : UpperIndex) (G : Finset I) :
    ¬ Point.upper u ≤ Point.fin G := by simp [LE.le, Point.LE]
@[simp] theorem top_not_le_fin (G : Finset I) : ¬ Point.top ≤ Point.fin G := by
  simp [LE.le, Point.LE]
@[simp] theorem top_not_le_upper (u : UpperIndex) : ¬ Point.top ≤ Point.upper u := by
  simp [LE.le, Point.LE]

instance : PartialOrder Point where
  le_refl x := by
    cases x <;> simp [LE.le, Point.LE]
  le_trans a b c hab hbc := by
    cases a with
    | fin A =>
      cases b with
      | fin B =>
        cases c with
        | fin C => exact fun x hx ↦ hbc (hab hx)
        | upper u => exact fun x hx ↦ hbc (hab hx)
        | top => trivial
      | upper u =>
        cases c with
        | fin C => contradiction
        | upper v => simpa only [upper_le_upper] using hbc ▸ hab
        | top => trivial
      | top =>
        cases c with
        | fin C => contradiction
        | upper u => contradiction
        | top => trivial
    | upper u =>
      cases b with
      | fin B => contradiction
      | upper v =>
        cases c with
        | fin C => contradiction
        | upper w => exact Eq.trans hab hbc
        | top => trivial
      | top =>
        cases c with
        | fin C => contradiction
        | upper v => contradiction
        | top => trivial
    | top =>
      cases b with
      | fin B => contradiction
      | upper u => contradiction
      | top =>
        cases c with
        | fin C => contradiction
        | upper u => contradiction
        | top => trivial
  le_antisymm a b hab hba := by
    cases a with
    | fin A =>
      cases b with
      | fin B => exact congrArg Point.fin (Finset.Subset.antisymm hab hba)
      | upper u => contradiction
      | top => contradiction
    | upper u =>
      cases b with
      | fin B => contradiction
      | upper v => exact congrArg Point.upper hab
      | top => contradiction
    | top =>
      cases b with
      | fin B => contradiction
      | upper u => contradiction
      | top => rfl

instance : OrderTop Point where
  top := Point.top
  le_top x := by cases x <;> simp

def bot : Point := Point.fin ∅

theorem bot_le (x : Point) : bot ≤ x := by
  cases x <;> simp [bot, UpperIndex.support]

theorem I_hasCofinalChain : HasCofinalChain I :=
  ⟨Set.univ, ⟨Set.univ_nonempty, fun _ _ _ _ _ ↦ le_total _ _⟩, IsCofinal.univ⟩

theorem I_cof : Order.cof I = Cardinal.aleph 1 :=
  regular_cofinalIndex_cof Cardinal.isRegular_aleph_one

theorem countable_bounded {S : Set I} (hS : S.Countable) : BddAbove S := by
  apply I_hasCofinalChain.small_bounded S
  rw [I_cof]
  exact (Cardinal.le_aleph0_iff_set_countable.mpr hS).trans_lt
    Cardinal.aleph0_lt_aleph_one

/-- A countable set lies strictly below an index whose initial segment is
infinite. The extra infinite range supplies the source condition `omega ≤ alpha`. -/
theorem exists_strict_upper_with_infinite_Iio {S : Set I} (hS : S.Countable) :
    ∃ alpha : I, S ⊆ Set.Iio alpha ∧ (Set.Iio alpha).Infinite := by
  classical
  let e : ℕ ↪ I := Infinite.natEmbedding I
  let A : Set I := S ∪ Set.range e
  have hA : A.Countable := hS.union (Set.countable_range e)
  obtain ⟨b, hb⟩ := countable_bounded hA
  obtain ⟨alpha, hba⟩ := exists_gt b
  refine ⟨alpha, ?_, ?_⟩
  · intro x hx
    exact (hb (Or.inl hx)).trans_lt hba
  · apply (Set.infinite_range_of_injective e.injective).mono
    intro x hx
    exact (hb (Or.inr hx)).trans_lt hba

/-- Two distinct special upper points above every finite subset of a
countable set. -/
theorem exists_two_upper_indices {S : Set I} (hS : S.Countable) :
    ∃ u v : UpperIndex, u ≠ v ∧ S ⊆ u.support ∧ S ⊆ v.support := by
  obtain ⟨a, hSa, haInf⟩ := exists_strict_upper_with_infinite_Iio hS
  obtain ⟨xi0, haxi0⟩ := exists_gt a
  obtain ⟨xi1, hxi0xi1⟩ := exists_gt xi0
  obtain ⟨beta, hxi1beta⟩ := exists_gt xi1
  have haBeta : a < beta := haxi0.trans (hxi0xi1.trans hxi1beta)
  have hBetaInf : (Set.Iio beta).Infinite := haInf.mono (Set.Iio_subset_Iio haBeta.le)
  let u : UpperIndex := ⟨xi0, beta, hxi0xi1.trans hxi1beta, hBetaInf⟩
  let v : UpperIndex := ⟨xi1, beta, hxi1beta, hBetaInf⟩
  refine ⟨u, v, ?_, ?_, ?_⟩
  · intro huv
    have := congrArg UpperIndex.xi huv
    exact hxi0xi1.ne this
  · intro x hx
    exact ⟨(hSa hx).trans haBeta, ne_of_lt ((hSa hx).trans haxi0)⟩
  · intro x hx
    exact ⟨(hSa hx).trans haBeta,
      ne_of_lt (((hSa hx).trans haxi0).trans hxi0xi1)⟩

def finiteMembers (C : Set Point) : Set (Finset I) :=
  {G | Point.fin G ∈ C}

def finiteUnion (C : Set Point) : Set I :=
  {x | ∃ G : Finset I, Point.fin G ∈ C ∧ x ∈ G}

theorem finiteMembers_countable {C : Set Point} (hC : IsChain (· ≤ ·) C) :
    (finiteMembers C).Countable := by
  let cardMap : finiteMembers C → ℕ := fun G ↦ G.val.card
  have hinj : Function.Injective cardMap := by
    intro G H hcard
    apply Subtype.ext
    rcases hC.total G.property H.property with hGH | hHG
    · exact Finset.eq_of_subset_of_card_le hGH hcard.ge
    · exact (Finset.eq_of_subset_of_card_le hHG hcard.le).symm
  haveI : Countable (finiteMembers C) := hinj.countable
  exact Set.to_countable (finiteMembers C)

theorem finiteUnion_countable {C : Set Point} (hC : IsChain (· ≤ ·) C) :
    (finiteUnion C).Countable := by
  let A := finiteMembers C
  have hA : A.Countable := finiteMembers_countable hC
  have heq : finiteUnion C = ⋃ G : A, (G.val : Set I) := by
    ext x
    simp only [finiteUnion, Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨G, hGC, hxG⟩
      exact ⟨⟨G, hGC⟩, hxG⟩
    · rintro ⟨G, hxG⟩
      exact ⟨G.val, G.property, hxG⟩
  rw [heq]
  haveI : Countable A := hA.to_subtype
  exact Set.countable_iUnion (fun G ↦ G.val.finite_toSet.countable)

theorem exists_greatest_of_nonfinite_mem {C : Set Point} (hC : NonemptyChain C)
    {p : Point} (hpC : p ∈ C) (hp : ∀ G : Finset I, p ≠ Point.fin G) :
    ∃ q, IsGreatest C q := by
  by_cases htop : (⊤ : Point) ∈ C
  · exact ⟨⊤, htop, fun _ _ ↦ le_top⟩
  cases p with
  | fin G => exact False.elim (hp G rfl)
  | top => exact False.elim (htop hpC)
  | upper u =>
      refine ⟨Point.upper u, hpC, ?_⟩
      intro q hqC
      cases q with
      | fin G =>
          rcases hC.2.total hqC hpC with h | h
          · exact h
          · exact False.elim (upper_not_le_fin u G h)
      | upper v =>
          rcases hC.2.total hqC hpC with h | h
          · exact h
          · exact (show u = v from h).symm
      | top => exact False.elim (htop hqC)

theorem all_fin_of_no_greatest {C : Set Point} (hC : NonemptyChain C)
    (hng : ¬ ∃ q, IsGreatest C q) {p : Point} (hpC : p ∈ C) :
    ∃ G : Finset I, p = Point.fin G := by
  by_contra hp
  push Not at hp
  exact hng (exists_greatest_of_nonfinite_mem hC hpC hp)

theorem finite_subset_union_bounded {C : Set Point} (hC : NonemptyChain C)
    (hfin : ∀ p ∈ C, ∃ G : Finset I, p = Point.fin G)
    (G : Finset I) (hG : (G : Set I) ⊆ finiteUnion C) :
    ∃ H : Finset I, Point.fin H ∈ C ∧ G ⊆ H := by
  classical
  induction G using Finset.induction_on with
  | empty =>
      obtain ⟨p, hpC⟩ := hC.1
      obtain ⟨H, rfl⟩ := hfin p hpC
      exact ⟨H, hpC, Finset.empty_subset H⟩
  | @insert x G hx ih =>
      have hsub : (G : Set I) ⊆ finiteUnion C := fun y hy ↦
        hG (Finset.mem_insert_of_mem hy)
      obtain ⟨H, hHC, hGH⟩ := ih hsub
      obtain ⟨K, hKC, hxK⟩ := hG (Finset.mem_insert_self x G)
      rcases hC.2.total hHC hKC with hHK | hKH
      · refine ⟨K, hKC, ?_⟩
        exact Finset.insert_subset hxK (fun y hy ↦ hHK (hGH hy))
      · refine ⟨H, hHC, ?_⟩
        exact Finset.insert_subset (hKH hxK) hGH

theorem greatest_cut_eq_lowerHull {C : Set Point} {g : Point} (hg : IsGreatest C g) :
    cut C = lowerHull C := by
  have hLub : IsLUB C g := ⟨fun _ h ↦ hg.2 h, fun q hq ↦ hq hg.1⟩
  rw [cut_eq_Iic hLub]
  ext x
  constructor
  · intro hx
    exact ⟨g, hg.1, hx⟩
  · rintro ⟨c, hc, hxc⟩
    exact hxc.trans (hg.2 hc)

theorem exists_separating_upper {S : Set I} (hS : S.Countable) (G : Finset I)
    (hGS : ¬ (G : Set I) ⊆ S) :
    ∃ u : UpperIndex, S ⊆ u.support ∧ ¬ (G : Set I) ⊆ u.support := by
  classical
  obtain ⟨eta, hetaG, hetaS⟩ := Set.not_subset.mp hGS
  have hA : (S ∪ (G : Set I)).Countable := hS.union G.finite_toSet.countable
  obtain ⟨alpha, hAlpha, hInf⟩ := exists_strict_upper_with_infinite_Iio hA
  let u : UpperIndex :=
    ⟨eta, alpha, hAlpha (Or.inr hetaG), hInf⟩
  refine ⟨u, ?_, ?_⟩
  · intro x hx
    change x < alpha ∧ x ∉ ({eta} : Set I)
    refine ⟨hAlpha (Or.inl hx), ?_⟩
    simp only [Set.mem_singleton_iff]
    intro hxe
    exact hetaS (hxe ▸ hx)
  · intro hG
    exact (hG hetaG).2 rfl

/-- Source equation `C^delta = downarrow C` for a chain without a greatest
member. -/
theorem nongreatest_cut_eq_lowerHull {C : Set Point} (hC : NonemptyChain C)
    (hng : ¬ ∃ q, IsGreatest C q) : cut C = lowerHull C := by
  apply Set.Subset.antisymm
  · intro p hp
    have hfin : ∀ q ∈ C, ∃ G : Finset I, q = Point.fin G :=
      fun q hq ↦ all_fin_of_no_greatest hC hng hq
    let S := finiteUnion C
    have hScount : S.Countable := finiteUnion_countable hC.2
    have member_subset_union : ∀ {G : Finset I}, Point.fin G ∈ C → (G : Set I) ⊆ S := by
      intro G hGC x hx
      exact ⟨G, hGC, hx⟩
    have upper_of_support : ∀ u : UpperIndex, S ⊆ u.support →
        Point.upper u ∈ upperBounds C := by
      intro u hSu q hqC
      obtain ⟨G, rfl⟩ := hfin q hqC
      exact fun x hx ↦ hSu (member_subset_union hqC hx)
    cases p with
    | fin G =>
        have hGS : (G : Set I) ⊆ S := by
          by_contra hn
          obtain ⟨u, hSu, hGu⟩ := exists_separating_upper hScount G hn
          exact hGu (hp (upper_of_support u hSu))
        obtain ⟨H, hHC, hGH⟩ := finite_subset_union_bounded hC hfin G hGS
        exact ⟨Point.fin H, hHC, hGH⟩
    | upper w =>
        obtain ⟨u, v, huv, hSu, hSv⟩ := exists_two_upper_indices hScount
        have hwu : w = u := hp (upper_of_support u hSu)
        have hwv : w = v := hp (upper_of_support v hSv)
        exact False.elim (huv (hwu.symm.trans hwv))
    | top =>
        obtain ⟨u, _, _, hSu, _⟩ := exists_two_upper_indices hScount
        exact False.elim (top_not_le_upper u (hp (upper_of_support u hSu)))
  · exact lowerHull_subset_cut C

/-- Source equation `C^delta = downarrow C` for every nonempty chain. -/
theorem chain_cut_eq_lowerHull (C : Set Point) (hC : NonemptyChain C) :
    cut C = lowerHull C := by
  by_cases hg : ∃ q, IsGreatest C q
  · obtain ⟨q, hq⟩ := hg
    exact greatest_cut_eq_lowerHull hq
  · exact nongreatest_cut_eq_lowerHull hC hg

theorem chainBelow_iff_le (x y : Point) : ChainBelow x y ↔ x ≤ y := by
  constructor
  · exact ChainBelow.le
  · intro hxy C hC hy
    rw [chain_cut_eq_lowerHull C hC] at hy
    exact lowerHull_isLower C hxy hy

theorem chainBelowSup_iff_le (x y : Point) : ChainBelowSup x y ↔ x ≤ y := by
  constructor
  · intro h
    obtain ⟨z, hz, hxz⟩ := h {y} (singleton_chain y) y isLUB_singleton le_rfl
    simpa only [Set.mem_singleton_iff.mp hz] using hxz
  · intro hxy C hC s hs hys
    have hsC : s ∈ lowerHull C := by
      rw [← chain_cut_eq_lowerHull C hC, cut_eq_Iic hs]
      show s ≤ s
      exact le_rfl
    exact lowerHull_isLower C (hxy.trans hys) hsC

theorem chain_lub_mem {C : Set Point} (hC : NonemptyChain C) {s : Point}
    (hs : IsLUB C s) : s ∈ C := by
  have hsLower : s ∈ lowerHull C := by
    rw [← chain_cut_eq_lowerHull C hC, cut_eq_Iic hs]
    show s ≤ s
    exact le_rfl
  obtain ⟨c, hc, hsc⟩ := hsLower
  exact (le_antisymm hsc (hs.1 hc)) ▸ hc

theorem chainSection_eq_Iic (y : Point) : chainSection y = Set.Iic y := by
  ext x
  exact chainBelow_iff_le x y

theorem chainSupSection_eq_Iic (y : Point) : chainSupSection y = Set.Iic y := by
  ext x
  exact chainBelowSup_iff_le x y

theorem Iic_chainGenerated (y : Point) : IsChainGeneratedIdeal (Set.Iic y) := by
  refine ⟨{y}, singleton_chain y, ?_⟩
  ext x
  simp only [lowerHull, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · exact fun h ↦ ⟨y, rfl, h⟩
  · rintro ⟨a, rfl, h⟩
    exact h

theorem chainContinuous : IsChainContinuous Point := by
  intro y
  rw [chainSection_eq_Iic]
  exact ⟨Iic_chainGenerated y, isLUB_Iic⟩

theorem chainContinuousSup : IsChainContinuousSup Point := by
  intro y
  rw [chainSupSection_eq_Iic]
  exact ⟨Iic_chainGenerated y, isLUB_Iic⟩

theorem chainBelow_interpolates : Interpolates (ChainBelow (P := Point)) := by
  intro a b hab
  exact ⟨a, (chainBelow_iff_le a a).mpr le_rfl, hab⟩

theorem chainBelowSup_interpolates : Interpolates (ChainBelowSup (P := Point)) := by
  intro a b hab
  exact ⟨a, (chainBelowSup_iff_le a a).mpr le_rfl, hab⟩

theorem strong_chainContinuous : IsStrongChainContinuous Point :=
  ⟨chainContinuous, chainBelow_interpolates⟩

theorem strong_chainContinuousSup : IsStrongChainContinuousSup Point :=
  ⟨chainContinuousSup, chainBelowSup_interpolates⟩

def finiteFamily (T : Set I) : Set Point :=
  {p | ∃ G : Finset I, (G : Set I) ⊆ T ∧ p = Point.fin G}

@[simp] theorem fin_mem_finiteFamily {T : Set I} {G : Finset I} :
    Point.fin G ∈ finiteFamily T ↔ (G : Set I) ⊆ T := by
  constructor
  · rintro ⟨H, hHT, hEq⟩
    cases hEq
    exact hHT
  · intro hGT
    exact ⟨G, hGT, rfl⟩

@[simp] theorem upper_not_mem_finiteFamily {T : Set I} (u : UpperIndex) :
    Point.upper u ∉ finiteFamily T := by
  rintro ⟨G, _, h⟩
  contradiction

@[simp] theorem top_not_mem_finiteFamily {T : Set I} :
    Point.top ∉ finiteFamily T := by
  rintro ⟨G, _, h⟩
  contradiction

theorem finiteFamily_directed (T : Set I) : NonemptyDirected (finiteFamily T) := by
  classical
  constructor
  · exact ⟨Point.fin ∅, by simp⟩
  · intro p hp q hq
    obtain ⟨G, hGT, rfl⟩ := hp
    obtain ⟨H, hHT, rfl⟩ := hq
    refine ⟨Point.fin (G ∪ H), ?_, ?_, ?_⟩
    · refine ⟨G ∪ H, ?_, rfl⟩
      intro x hx
      rcases Finset.mem_union.mp hx with hxG | hxH
      · exact hGT hxG
      · exact hHT hxH
    · exact Finset.subset_union_left
    · exact Finset.subset_union_right

theorem I_not_countable : ¬ Countable I := by
  intro hI
  have hle : Cardinal.mk I ≤ Cardinal.aleph0 := Cardinal.mk_le_aleph0_iff.mpr hI
  rw [cofinalIndex_card] at hle
  exact Cardinal.aleph0_lt_aleph_one.not_ge hle

theorem Iio_countable (alpha : I) : (Set.Iio alpha).Countable := by
  apply Cardinal.le_aleph0_iff_set_countable.mp
  exact Cardinal.lt_aleph_one_iff.mp
    (cofinalIndex_initial_small (Cardinal.aleph 1 : Cardinal.{0}) alpha)

theorem upperBounds_finiteFamily {T : Set I} (hT : ¬ T.Countable) :
    upperBounds (finiteFamily T) = ({⊤} : Set Point) := by
  ext p
  constructor
  · intro hp
    cases p with
    | fin G =>
        have hTG : T ⊆ (G : Set I) := by
          intro x hxT
          have hx := hp (show Point.fin {x} ∈ finiteFamily T by
            exact fin_mem_finiteFamily.mpr (by
              simpa only [Finset.coe_singleton] using Set.singleton_subset_iff.mpr hxT))
          exact hx (Finset.mem_singleton_self x)
        exact False.elim (hT (G.finite_toSet.countable.mono hTG))
    | upper u =>
        have hTsupport : T ⊆ u.support := by
          intro x hxT
          have hx := hp (show Point.fin {x} ∈ finiteFamily T by
            exact fin_mem_finiteFamily.mpr (by
              simpa only [Finset.coe_singleton] using Set.singleton_subset_iff.mpr hxT))
          exact hx (Finset.mem_singleton_self x)
        have hsupport : u.support.Countable :=
          (Iio_countable u.alpha).mono (Set.diff_subset)
        exact False.elim (hT (hsupport.mono hTsupport))
    | top => exact Set.mem_singleton ⊤
  · intro hp
    have hpTop : p = ⊤ := Set.mem_singleton_iff.mp hp
    subst p
    exact fun _ _ ↦ le_top

theorem cut_finiteFamily_eq_univ {T : Set I} (hT : ¬ T.Countable) :
    cut (finiteFamily T) = Set.univ := by
  rw [cut, upperBounds_finiteFamily hT]
  ext p
  simp only [Set.mem_univ, iff_true]
  intro q hq
  simpa only [Set.mem_singleton_iff.mp hq] using (le_top : p ≤ (⊤ : Point))

theorem finiteFamily_lub_top {T : Set I} (hT : ¬ T.Countable) :
    IsLUB (finiteFamily T) (⊤ : Point) := by
  constructor
  · exact fun _ _ ↦ le_top
  · intro p hp
    have : p ∈ ({⊤} : Set Point) := by
      rw [← upperBounds_finiteFamily hT]
      exact hp
    exact Set.mem_singleton_iff.mp this ▸ le_rfl

theorem compl_finset_not_countable (G : Finset I) :
    ¬ ((G : Set I)ᶜ).Countable := by
  intro hcomp
  have huniv : (Set.univ : Set I).Countable := by
    rw [← Set.union_compl_self (G : Set I)]
    exact G.finite_toSet.countable.union hcomp
  exact I_not_countable (Set.countable_univ_iff.mp huniv)

theorem nonempty_fin_not_lowerHull_compl {G : Finset I} (hG : G.Nonempty) :
    Point.fin G ∉ lowerHull (finiteFamily ((G : Set I)ᶜ)) := by
  obtain ⟨x, hxG⟩ := hG
  rintro ⟨p, hp, hGp⟩
  obtain ⟨H, hHT, rfl⟩ := hp
  have hxH : x ∈ H := hGp hxG
  exact hHT hxH hxG

theorem nonfinite_not_lowerHull (T : Set I) (p : Point)
    (hp : ∀ G : Finset I, p ≠ Point.fin G) :
    p ∉ lowerHull (finiteFamily T) := by
  rintro ⟨q, hq, hpq⟩
  obtain ⟨G, _, rfl⟩ := hq
  cases p with
  | fin H => exact (hp H rfl).elim
  | upper u => exact upper_not_le_fin u G hpq
  | top => exact top_not_le_fin G hpq

theorem fin_not_directedBelow_top {G : Finset I} (hG : G.Nonempty) :
    ¬ DirectedBelow (Point.fin G) (⊤ : Point) := by
  intro hbelow
  let T : Set I := (G : Set I)ᶜ
  have hT : ¬ T.Countable := compl_finset_not_countable G
  have hcut : (⊤ : Point) ∈ cut (finiteFamily T) := by
    rw [cut_finiteFamily_eq_univ hT]
    trivial
  exact nonempty_fin_not_lowerHull_compl hG
    (hbelow (finiteFamily T) (finiteFamily_directed T) hcut)

theorem fin_not_wayBelow_top {G : Finset I} (hG : G.Nonempty) :
    ¬ WayBelow (Point.fin G) (⊤ : Point) := by
  intro hbelow
  let T : Set I := (G : Set I)ᶜ
  have hT : ¬ T.Countable := compl_finset_not_countable G
  exact nonempty_fin_not_lowerHull_compl hG
    (hbelow (finiteFamily T) (finiteFamily_directed T) ⊤
      (finiteFamily_lub_top hT) le_rfl)

theorem nonfinite_not_directedBelow_top {p : Point}
    (hp : ∀ G : Finset I, p ≠ Point.fin G) :
    ¬ DirectedBelow p (⊤ : Point) := by
  intro hbelow
  have hT : ¬ (Set.univ : Set I).Countable := fun h ↦
    I_not_countable (Set.countable_univ_iff.mp h)
  have hcut : (⊤ : Point) ∈ cut (finiteFamily (Set.univ : Set I)) := by
    rw [cut_finiteFamily_eq_univ hT]
    trivial
  exact nonfinite_not_lowerHull Set.univ p hp
    (hbelow _ (finiteFamily_directed Set.univ) hcut)

theorem nonfinite_not_wayBelow_top {p : Point}
    (hp : ∀ G : Finset I, p ≠ Point.fin G) :
    ¬ WayBelow p (⊤ : Point) := by
  intro hbelow
  have hT : ¬ (Set.univ : Set I).Countable := fun h ↦
    I_not_countable (Set.countable_univ_iff.mp h)
  exact nonfinite_not_lowerHull Set.univ p hp
    (hbelow _ (finiteFamily_directed Set.univ) ⊤
      (finiteFamily_lub_top hT) le_rfl)

theorem bot_directedBelow_top : DirectedBelow bot (⊤ : Point) := by
  intro D hD _
  obtain ⟨d, hd⟩ := hD.1
  exact ⟨d, hd, bot_le d⟩

theorem bot_wayBelow_top : WayBelow bot (⊤ : Point) := by
  intro D hD _ _ _
  obtain ⟨d, hd⟩ := hD.1
  exact ⟨d, hd, bot_le d⟩

theorem directedSection_top : directedSection (⊤ : Point) = {bot} := by
  ext p
  constructor
  · intro hp
    cases p with
    | fin G =>
        by_cases hG : G.Nonempty
        · exact False.elim (fin_not_directedBelow_top hG hp)
        · have : G = ∅ := Finset.not_nonempty_iff_eq_empty.mp hG
          subst G
          rfl
    | upper u =>
        exact False.elim (nonfinite_not_directedBelow_top
          (fun G h ↦ Point.noConfusion h) hp)
    | top =>
        exact False.elim (nonfinite_not_directedBelow_top
          (fun G h ↦ Point.noConfusion h) hp)
  · intro hp
    have hpbot : p = bot := Set.mem_singleton_iff.mp hp
    subst p
    exact bot_directedBelow_top

theorem waySection_top : waySection (⊤ : Point) = {bot} := by
  ext p
  constructor
  · intro hp
    cases p with
    | fin G =>
        by_cases hG : G.Nonempty
        · exact False.elim (fin_not_wayBelow_top hG hp)
        · have : G = ∅ := Finset.not_nonempty_iff_eq_empty.mp hG
          subst G
          rfl
    | upper u =>
        exact False.elim (nonfinite_not_wayBelow_top
          (fun G h ↦ Point.noConfusion h) hp)
    | top =>
        exact False.elim (nonfinite_not_wayBelow_top
          (fun G h ↦ Point.noConfusion h) hp)
  · intro hp
    have hpbot : p = bot := Set.mem_singleton_iff.mp hp
    subst p
    exact bot_wayBelow_top

theorem bot_ne_top : bot ≠ (⊤ : Point) := by
  intro h
  contradiction

theorem not_directedPredistributive : ¬ IsDirectedPredistributive Point := by
  intro h
  have htop := h (⊤ : Point)
  rw [directedSection_top] at htop
  exact bot_ne_top (isLUB_singleton.unique htop)

theorem not_directedPredistributiveSup : ¬ IsDirectedPredistributiveSup Point := by
  intro h
  have htop := h (⊤ : Point)
  rw [waySection_top] at htop
  exact bot_ne_top (isLUB_singleton.unique htop)

theorem not_directedPrecontinuous : ¬ IsDirectedPrecontinuous Point :=
  fun h ↦ not_directedPredistributive h.1

theorem not_directedPrecontinuousSup : ¬ IsDirectedPrecontinuousSup Point :=
  fun h ↦ not_directedPredistributiveSup h.1

theorem not_chainComplete : ¬ IsChainComplete Point := by
  classical
  let e : ℕ ↪ I := Infinite.natEmbedding I
  let f : ℕ → Point := fun n ↦ Point.fin ((Finset.range n).image e)
  have hf : Monotone f := by
    intro n m hnm
    exact Finset.image_subset_image (Finset.range_mono hnm)
  let C : Set Point := Set.range f
  have hC : NonemptyChain C := ⟨Set.range_nonempty f, hf.isChain_range⟩
  intro hcomplete
  obtain ⟨s, hs⟩ := hcomplete C hC
  obtain ⟨n, rfl⟩ := chain_lub_mem hC hs
  have hle : f (n + 1) ≤ f n := hs.1 (Set.mem_range_self (n + 1))
  have hmem : e n ∈ (Finset.range (n + 1)).image e :=
    Finset.mem_image.mpr ⟨n, Finset.mem_range.mpr (Nat.lt_succ_self n), rfl⟩
  have hnot : e n ∉ (Finset.range n).image e := by
    intro h
    obtain ⟨m, hm, hem⟩ := Finset.mem_image.mp h
    have hmn : m = n := e.injective hem
    subst m
    exact Nat.lt_irrefl n (Finset.mem_range.mp hm)
  exact hnot (hle hmem)

def Code := Finset I ⊕ ((I × I) ⊕ PUnit)

def encode : Point → Code
  | .fin G => Sum.inl G
  | .upper u => Sum.inr (Sum.inl (u.xi, u.alpha))
  | .top => Sum.inr (Sum.inr PUnit.unit)

theorem encode_injective : Function.Injective encode := by
  intro p q h
  cases p with
  | fin G =>
      cases q with
      | fin H => exact congrArg Point.fin (Sum.inl.inj h)
      | upper v => simp [encode] at h
      | top => simp [encode] at h
  | top =>
      cases q with
      | fin H => simp [encode] at h
      | upper v =>
          have hi : (Sum.inr PUnit.unit : (I × I) ⊕ PUnit) =
              Sum.inl (v.xi, v.alpha) := Sum.inr.inj h
          exact False.elim (Sum.inr_ne_inl hi)
      | top => rfl
  | upper u =>
      cases q with
      | fin H => simp [encode] at h
      | top =>
          have hi : (Sum.inl (u.xi, u.alpha) : (I × I) ⊕ PUnit) =
              Sum.inr PUnit.unit := Sum.inr.inj h
          exact False.elim (Sum.inl_ne_inr hi)
      | upper v =>
          have huv : (u.xi, u.alpha) = (v.xi, v.alpha) :=
            Sum.inl.inj (Sum.inr.inj h)
          cases u with
          | mk uxi ualpha uhlt uhInf =>
              cases v with
              | mk vxi valpha hvlt hvInf =>
                  simp only [Prod.mk.injEq] at huv
                  cases huv.1
                  cases huv.2
                  rfl

theorem cardinality : Cardinal.mk Point = Cardinal.aleph 1 := by
  apply le_antisymm
  · calc
      Cardinal.mk Point ≤ Cardinal.mk Code := Cardinal.mk_le_of_injective encode_injective
      _ = Cardinal.aleph 1 := by
        simp only [Code, Cardinal.mk_sum, Cardinal.lift_id, Cardinal.mk_finset_of_infinite,
          Cardinal.mk_prod, cofinalIndex_card, Cardinal.mk_eq_one]
        rw [Cardinal.mul_eq_self (Cardinal.aleph0_le_aleph 1)]
        rw [Cardinal.add_eq_left (Cardinal.aleph0_le_aleph 1)
          (Cardinal.one_le_aleph0.trans (Cardinal.aleph0_le_aleph 1))]
        rw [Cardinal.add_eq_self (Cardinal.aleph0_le_aleph 1)]
  · rw [← cofinalIndex_card (Cardinal.aleph 1 : Cardinal.{0})]
    exact Cardinal.mk_le_of_injective (fun i j h ↦ Finset.singleton_inj.mp (Point.fin.inj h))

/-- Full source `thm:precontinuous-counterexample`, with both approximation
conventions and the final failure of chain completeness. -/
theorem precontinuous_counterexample :
    Cardinal.mk Point = Cardinal.aleph 1 ∧
    IsStrongChainContinuous Point ∧
    IsStrongChainContinuousSup Point ∧
    ¬ IsDirectedPredistributive Point ∧
    ¬ IsDirectedPredistributiveSup Point ∧
    ¬ IsDirectedPrecontinuous Point ∧
    ¬ IsDirectedPrecontinuousSup Point ∧
    ¬ IsChainComplete Point :=
  ⟨cardinality, strong_chainContinuous, strong_chainContinuousSup,
    not_directedPredistributive, not_directedPredistributiveSup,
    not_directedPrecontinuous, not_directedPrecontinuousSup, not_chainComplete⟩

end PrecontinuousExample
end ChainApproximation
