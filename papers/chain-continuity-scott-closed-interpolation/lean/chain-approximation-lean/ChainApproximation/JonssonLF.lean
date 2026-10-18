import ChainApproximation.AlgebraExpansion
import Mathlib.Order.OrderIsoNat
import Mathlib.Data.Finset.Max
import Mathlib.Tactic

/-!
# A locally finite Jónsson algebra of cardinality `ℵ₁`

This gives a direct ZFC proof of the precise existence claim used before the
manuscript's sharpness theorem. It recursively chooses compatible enumerations
of countable initial segments, so finite generated subalgebras stay finite.
It proves the paper's needed consequence by a different route from Devlin's
general reduction theorem; that general theorem is not asserted here.
-/

set_option autoImplicit false

namespace ChainApproximation

namespace CompatibleEnumeration

variable {X : Type}

structure Chain (X : Type) where
  base : X ≃ ℕ
  B : ℕ → Finset X
  mono : Monotone B
  cover : ∀ x : X, ∃ n, x ∈ B n

variable (d : Chain X)

private noncomputable def rank (x : X) : ℕ := by
  classical
  exact Nat.find (d.cover x)

private theorem rank_mem (x : X) : x ∈ d.B (rank d x) := by
  classical
  exact Nat.find_spec (d.cover x)

private theorem rank_le_of_mem (n : ℕ) {x : X} (hx : x ∈ d.B n) :
    rank d x ≤ n := by
  classical
  exact Nat.find_le hx

private theorem mem_of_rank_le (n : ℕ) {x : X} (hx : rank d x ≤ n) :
    x ∈ d.B n := d.mono hx (rank_mem d x)

private noncomputable def bound (n : ℕ) : ℕ := (d.B n).sup d.base + 1

private noncomputable def offset : ℕ → ℕ
  | 0 => 0
  | n + 1 => offset n + bound d n

private theorem offset_succ (n : ℕ) : offset d (n + 1) = offset d n + bound d n := rfl

private theorem offset_mono : Monotone (offset d) := by
  exact monotone_nat_of_le_succ (fun n => by simp [offset_succ])

private noncomputable def code (x : X) : ℕ := offset d (rank d x) + d.base x

private theorem code_lower (x : X) : offset d (rank d x) ≤ code d x :=
  Nat.le_add_right _ _

private theorem code_upper (x : X) : code d x < offset d (rank d x + 1) := by
  have hmem := rank_mem d x
  have hle : d.base x ≤ (d.B (rank d x)).sup d.base := Finset.le_sup hmem
  simp only [code, offset_succ, bound]
  omega

private theorem code_rank_mono {x y : X} (h : code d x ≤ code d y) :
    rank d x ≤ rank d y := by
  by_contra hn
  have hlt : rank d y + 1 ≤ rank d x := by omega
  have ho := offset_mono d hlt
  have hx := code_lower d x
  have hy := code_upper d y
  omega

private theorem code_injective : Function.Injective (code d) := by
  intro x y hxy
  have hrank : rank d x = rank d y := by
    exact le_antisymm
      (code_rank_mono d (le_of_eq hxy))
      (code_rank_mono d (le_of_eq hxy.symm))
  have hbase : d.base x = d.base y := by
    unfold code at hxy
    rw [hrank] at hxy
    omega
  exact d.base.injective hbase

private noncomputable def codeEquivRange : X ≃ Set.range (code d) :=
  Equiv.ofBijective (fun x => (⟨code d x, ⟨x, rfl⟩⟩ : Set.range (code d)))
    ⟨by
      intro x y h
      exact code_injective d (congrArg Subtype.val h), by
      intro y
      obtain ⟨x, hx⟩ := y.2
      exact ⟨x, Subtype.ext hx⟩⟩

private noncomputable def compatibleEquiv : X ≃ ℕ := by
  haveI : Infinite X := d.base.infinite_iff.mpr inferInstance
  haveI : Infinite (Set.range (code d)) :=
    (Set.infinite_range_of_injective (code_injective d)).to_subtype
  exact (codeEquivRange d).trans (Nat.Subtype.orderIsoOfNat (Set.range (code d))).symm.toEquiv

private theorem code_le_of_compatibleEquiv_le {x y : X}
    (h : compatibleEquiv d x ≤ compatibleEquiv d y) : code d x ≤ code d y := by
  haveI : Infinite X := d.base.infinite_iff.mpr inferInstance
  haveI : Infinite (Set.range (code d)) :=
    (Set.infinite_range_of_injective (code_injective d)).to_subtype
  let o := Nat.Subtype.orderIsoOfNat (Set.range (code d))
  have ho := o.monotone h
  have heq (z : X) : o (compatibleEquiv d z) = codeEquivRange d z := by
    simp [compatibleEquiv, o]
  rw [heq x, heq y] at ho
  exact ho

theorem predecessor_mem (n : ℕ) {x : X} (hx : x ∈ d.B n) :
    (compatibleEquiv d).symm (Nat.pred (compatibleEquiv d x)) ∈ d.B n := by
  let y := (compatibleEquiv d).symm (Nat.pred (compatibleEquiv d x))
  have hcode : code d y ≤ code d x := by
    apply code_le_of_compatibleEquiv_le d
    simpa only [y, Equiv.apply_symm_apply] using Nat.pred_le (compatibleEquiv d x)
  exact mem_of_rank_le d n ((code_rank_mono d hcode).trans (rank_le_of_mem d n hx))

def IsClosed (f : X → X → X) (B : Finset X) : Prop :=
  ∀ x ∈ B, ∀ y ∈ B, f x y ∈ B

section LocallyFinite

structure HullData (X : Type) where
  f : X → X → X
  base : X ≃ ℕ
  localFinite : ∀ F : Finset X, ∃ B : Finset X, F ⊆ B ∧ IsClosed f B

variable (h : HullData X)

private noncomputable def hull (F : Finset X) : Finset X :=
  Classical.choose (h.localFinite F)

private theorem subset_hull (F : Finset X) : F ⊆ hull h F :=
  (Classical.choose_spec (h.localFinite F)).1

private theorem hull_closed (F : Finset X) : IsClosed h.f (hull h F) :=
  (Classical.choose_spec (h.localFinite F)).2

variable [DecidableEq X]

private noncomputable def finiteChain : ℕ → Finset X
  | 0 => hull h {h.base.symm 0}
  | n + 1 => hull h (finiteChain n ∪ {h.base.symm (n + 1)})

private theorem finiteChain_mono_step (n : ℕ) :
    finiteChain h n ⊆ finiteChain h (n + 1) := by
  rw [finiteChain]
  exact Finset.Subset.trans Finset.subset_union_left (subset_hull h _)

private theorem finiteChain_mono : Monotone (finiteChain h) :=
  monotone_nat_of_le_succ (finiteChain_mono_step h)

private theorem finiteChain_closed (n : ℕ) : IsClosed h.f (finiteChain h n) := by
  cases n with
  | zero => exact hull_closed h _
  | succ n => exact hull_closed h _

private theorem finiteChain_contains_base (n : ℕ) :
    h.base.symm n ∈ finiteChain h n := by
  cases n with
  | zero =>
      exact subset_hull h _ (Finset.mem_singleton_self _)
  | succ n =>
      rw [finiteChain]
      apply subset_hull h _
      exact Finset.mem_union_right _ (Finset.mem_singleton_self _)

private theorem finiteChain_cover (x : X) :
    ∃ n, x ∈ finiteChain h n := by
  refine ⟨h.base x, ?_⟩
  simpa only [Equiv.symm_apply_apply] using finiteChain_contains_base h (h.base x)

private noncomputable def compatibleChain : Chain X :=
  ⟨h.base, finiteChain h, finiteChain_mono h, finiteChain_cover h⟩

theorem exists_compatible_predecessor :
    ∃ e : X ≃ ℕ, ∀ F : Finset X, ∃ B : Finset X,
      F ⊆ B ∧ IsClosed h.f B ∧
        ∀ x ∈ B, e.symm (Nat.pred (e x)) ∈ B := by
  let d := compatibleChain h
  refine ⟨compatibleEquiv d, fun F => ?_⟩
  let n : ℕ := F.sup h.base
  refine ⟨d.B n, ?_, ?_, ?_⟩
  · intro x hx
    have hcode : h.base x ≤ n := Finset.le_sup hx
    have hbase : x ∈ d.B (h.base x) := by
      change x ∈ finiteChain h (h.base x)
      simpa only [Equiv.symm_apply_apply] using
        finiteChain_contains_base h (h.base x)
    exact d.mono hcode hbase
  · exact finiteChain_closed h n
  · intro x hx
    exact predecessor_mem d n hx

end LocallyFinite

theorem exists_compatible_predecessor_classical (f : X → X → X) (base : X ≃ ℕ)
    (hLF : ∀ F : Finset X, ∃ B : Finset X, F ⊆ B ∧ IsClosed f B) :
    ∃ e : X ≃ ℕ, ∀ F : Finset X, ∃ B : Finset X,
      F ⊆ B ∧ IsClosed f B ∧
        ∀ x ∈ B, e.symm (Nat.pred (e x)) ∈ B := by
  classical
  exact exists_compatible_predecessor
    (h := ⟨f, base, hLF⟩)

def extendOp (f : X → X → X) (p : X → X) : Option X → Option X → Option X
  | some x, some y => some (f x y)
  | some x, none => some (p x)
  | none, _ => none

theorem onePointExtension_finiteHull [Nonempty X] (f : X → X → X) (p : X → X)
    (hHull : ∀ F : Finset X, ∃ B : Finset X,
      F ⊆ B ∧ IsClosed f B ∧ ∀ x ∈ B, p x ∈ B) :
    ∀ F : Finset (Option X), ∃ C : Finset (Option X),
      F ⊆ C ∧ IsClosed (extendOp f p) C := by
  classical
  intro F
  let x₀ : X := Classical.choice inferInstance
  let lower : Finset X := F.image (fun z => z.getD x₀)
  obtain ⟨B, hFB, hfB, hpB⟩ := hHull lower
  let C : Finset (Option X) := B.image some ∪ {none}
  refine ⟨C, ?_, ?_⟩
  · intro z hz
    cases z with
    | none => simp [C]
    | some x =>
      have hx : x ∈ lower := Finset.mem_image.mpr ⟨some x, hz, rfl⟩
      have hxB := hFB hx
      simp [C, hxB]
  · intro z hz w hw
    cases z with
    | none => simp [extendOp, C]
    | some x =>
      have hxB : x ∈ B := by simpa [C] using hz
      cases w with
      | none => simp [extendOp, C, hpB x hxB]
      | some y =>
        have hyB : y ∈ B := by simpa [C] using hw
        simp [extendOp, C, hfB x hxB y hyB]

end CompatibleEnumeration

namespace JonssonLF

open ChainApproximation
open Set FirstOrder FirstOrder.Language Cardinal

abbrev I := CofinalIndex (Cardinal.aleph 1 : Cardinal.{0})
abbrev EnumAt (y : I) := (Iio y).Infinite → Iio y ≃ ℕ

noncomputable def rawPred {y : I} (e : EnumAt y) (hy : (Iio y).Infinite) (x : Iio y) : Iio y :=
  (e hy).symm (Nat.pred ((e hy) x))

noncomputable def lowerOp (y : I) (rec : ∀ z : I, z < y → EnumAt z)
    (x z : Iio y) : Iio y := by
  classical
  by_cases hxz : x.1 < z.1
  · by_cases hzinf : (Iio z.1).Infinite
    · let w : Iio z.1 := rawPred (rec z.1 z.2) hzinf ⟨x.1, hxz⟩
      exact ⟨w.1, by change w.1 < y; exact lt_trans w.2 z.2⟩
    · exact x
  · exact x

theorem Iio_countable (y : I) : (Iio y).Countable := by
  apply Cardinal.le_aleph0_iff_set_countable.mp
  exact Cardinal.lt_aleph_one_iff.mp
    (cofinalIndex_initial_small (Cardinal.aleph 1 : Cardinal.{0}) y)

noncomputable def baseEnum (y : I) (hy : (Iio y).Infinite) : Iio y ≃ ℕ := by
  letI : Countable (Iio y) := (Iio_countable y).to_subtype
  letI : Infinite (Iio y) := hy.to_subtype
  exact Classical.choice (inferInstance : Nonempty (Iio y ≃ ℕ))

noncomputable def enumStep (y : I) (rec : ∀ z : I, z < y → EnumAt z) : EnumAt y := by
  intro hy
  let f := lowerOp y rec
  let b := baseEnum y hy
  by_cases hLF : ∀ F : Finset (Iio y), ∃ B : Finset (Iio y),
      F ⊆ B ∧ CompatibleEnumeration.IsClosed f B
  · exact Classical.choose
      (CompatibleEnumeration.exists_compatible_predecessor_classical f b hLF)
  · exact b

noncomputable def enumAt : ∀ y : I, EnumAt y :=
  wellFounded_lt.fix enumStep

theorem enumAt_eq (y : I) :
    enumAt y = enumStep y (fun z _ => enumAt z) := by
  rw [enumAt, WellFounded.fix_eq]

theorem enumAt_compatible (y : I) (hy : (Iio y).Infinite)
    (hLF : ∀ F : Finset (Iio y), ∃ B : Finset (Iio y),
      F ⊆ B ∧ CompatibleEnumeration.IsClosed
        (lowerOp y (fun z _ => enumAt z)) B) :
    ∀ F : Finset (Iio y), ∃ B : Finset (Iio y),
      F ⊆ B ∧ CompatibleEnumeration.IsClosed
        (lowerOp y (fun z _ => enumAt z)) B ∧
      ∀ x ∈ B, rawPred (enumAt y) hy x ∈ B := by
  have h := Classical.choose_spec
    (CompatibleEnumeration.exists_compatible_predecessor_classical
      (lowerOp y (fun z _ => enumAt z)) (baseEnum y hy) hLF)
  rw [enumAt_eq]
  simpa only [enumStep, dif_pos hLF, rawPred] using h

noncomputable def op (x y : I) : I := by
  classical
  exact if hxy : x < y then
    if hy : (Iio y).Infinite then (rawPred (enumAt y) hy ⟨x, hxy⟩).1 else x
  else x

theorem lowerOp_eq (y : I) (x z : Iio y) :
    (lowerOp y (fun t _ => enumAt t) x z).1 = op x.1 z.1 := by
  classical
  by_cases hxz : x.1 < z.1
  · by_cases hzinf : (Iio z.1).Infinite
    · simp [lowerOp, op, hxz, hzinf, rawPred]
    · simp [lowerOp, op, hxz, hzinf]
  · simp [lowerOp, op, hxz]

theorem op_le_max (x y : I) : op x y ≤ max x y := by
  classical
  by_cases hxy : x < y
  · by_cases hy : (Iio y).Infinite
    · have hlt : (rawPred (enumAt y) hy ⟨x, hxy⟩).1 < y :=
        (rawPred (enumAt y) hy ⟨x, hxy⟩).2
      have hop : op x y = (rawPred (enumAt y) hy ⟨x, hxy⟩).1 := by
        simp [op, hxy, hy]
      rw [hop]
      exact hlt.le.trans (le_max_right x y)
    · simp [op, hxy, hy]
  · simp [op, hxy]

noncomputable def opIic (y : I) (x z : Iic y) : Iic y :=
  ⟨op x.1 z.1, by
    change op x.1 z.1 ≤ y
    exact (op_le_max x.1 z.1).trans (max_le x.2 z.2)⟩

def HullIic (y : I) : Prop :=
  ∀ F : Finset (Iic y), ∃ B : Finset (Iic y),
    F ⊆ B ∧ CompatibleEnumeration.IsClosed (opIic y) B

theorem lowerOp_from_previous (y : I)
    (hprev : ∀ z : I, z < y → HullIic z) :
    ∀ F : Finset (Iio y), ∃ B : Finset (Iio y),
      F ⊆ B ∧ CompatibleEnumeration.IsClosed
        (lowerOp y (fun z _ => enumAt z)) B := by
  classical
  intro F
  by_cases hF : F.Nonempty
  · let m : Iio y := F.max' hF
    let incl : Iic m.1 → Iio y := fun z =>
      ⟨z.1, by change z.1 < y; exact lt_of_le_of_lt z.2 m.2⟩
    let F' : Finset (Iic m.1) := F.attach.image (fun x =>
      (⟨x.1.1, Finset.le_max' F x.1 x.2⟩ : Iic m.1))
    obtain ⟨B', hFB', hB'⟩ := hprev m.1 m.2 F'
    refine ⟨B'.image incl, ?_, ?_⟩
    · intro x hx
      let a : Iic m.1 := ⟨x.1, Finset.le_max' F x hx⟩
      have ha : a ∈ F' := Finset.mem_image.mpr
        ⟨⟨x, hx⟩, Finset.mem_attach F ⟨x, hx⟩, rfl⟩
      have hab : a ∈ B' := hFB' ha
      have hEq : incl a = x := Subtype.ext rfl
      exact hEq ▸ Finset.mem_image.mpr ⟨a, hab, rfl⟩
    · intro x hx z hz
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hz
      have hab := hB' a ha b hb
      have hEq : lowerOp y (fun t _ => enumAt t) (incl a) (incl b) =
          incl (opIic m.1 a b) := by
        apply Subtype.ext
        exact lowerOp_eq y (incl a) (incl b)
      rw [hEq]
      exact Finset.mem_image.mpr ⟨opIic m.1 a b, hab, rfl⟩
  · refine ⟨∅, ?_, ?_⟩
    · simp [Finset.not_nonempty_iff_eq_empty.mp hF]
    · intro x hx
      simp at hx

end JonssonLF
namespace TransportScratch

open Set

variable {α β : Type*}

def IsClosed (f : α → α → α) (B : Finset α) : Prop :=
  ∀ x ∈ B, ∀ y ∈ B, f x y ∈ B

def transportOp (e : α ≃ β) (f : α → α → α) : β → β → β :=
  fun x y => e (f (e.symm x) (e.symm y))

theorem finiteHull_transport (e : α ≃ β) (f : α → α → α)
    (h : ∀ F : Finset α, ∃ B : Finset α, F ⊆ B ∧ IsClosed f B) :
    ∀ G : Finset β, ∃ C : Finset β, G ⊆ C ∧ IsClosed (transportOp e f) C := by
  classical
  intro G
  obtain ⟨B, hFB, hB⟩ := h (G.image e.symm)
  refine ⟨B.image e, ?_, ?_⟩
  · intro x hx
    apply Finset.mem_image.mpr
    refine ⟨e.symm x, hFB ?_, e.apply_symm_apply x⟩
    exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
  · intro x hx y hy
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
    simpa [transportOp] using (Finset.mem_image.mpr ⟨f a b, hB a ha b hb, rfl⟩ : e (f a b) ∈ B.image e)

variable {I : Type*} [LinearOrder I]

def optionIioEquivIic (y : I) : Option (Iio y) ≃ Iic y where
  toFun
    | none => ⟨y, le_rfl⟩
    | some x => ⟨x.1, le_of_lt x.2⟩
  invFun z := if h : z.1 = y then none else some ⟨z.1, lt_of_le_of_ne z.2 h⟩
  left_inv := by
    intro z
    cases z with
    | none => simp
    | some x =>
      have hx : x.1 ≠ y := ne_of_lt x.2
      simp [hx]
  right_inv := by
    intro z
    apply Subtype.ext
    by_cases h : z.1 = y
    · simp [h]
    · simp [h]

end TransportScratch

namespace JonssonLF

open ChainApproximation
open Set FirstOrder FirstOrder.Language Cardinal

theorem opIic_transport (y : I) (hy : (Iio y).Infinite) :
    opIic y = TransportScratch.transportOp
      (TransportScratch.optionIioEquivIic y)
      (CompatibleEnumeration.extendOp
        (lowerOp y (fun z _ => enumAt z)) (rawPred (enumAt y) hy)) := by
  funext a b
  let e := TransportScratch.optionIioEquivIic y
  obtain ⟨u, rfl⟩ := e.surjective a
  obtain ⟨v, rfl⟩ := e.surjective b
  cases u with
  | none =>
      cases v with
      | none =>
          apply Subtype.ext
          simp [e, opIic, op, TransportScratch.transportOp,
            CompatibleEnumeration.extendOp, TransportScratch.optionIioEquivIic]
      | some z =>
          apply Subtype.ext
          have hnot : ¬ y < z.1 := not_lt_of_ge (le_of_lt z.2)
          simp [e, opIic, op, hnot, TransportScratch.transportOp,
            CompatibleEnumeration.extendOp, TransportScratch.optionIioEquivIic]
  | some x =>
      have hx : x.1 < y := x.2
      have hne : x.1 ≠ y := ne_of_lt hx
      cases v with
      | none =>
          apply Subtype.ext
          simp [e, opIic, op, hx, hne, hy, TransportScratch.transportOp,
            CompatibleEnumeration.extendOp, TransportScratch.optionIioEquivIic, rawPred]
          rfl
      | some z =>
          apply Subtype.ext
          have hz : z.1 < y := z.2
          have hnz : z.1 ≠ y := ne_of_lt hz
          simpa [e, opIic, hne, hnz, TransportScratch.transportOp,
            CompatibleEnumeration.extendOp, TransportScratch.optionIioEquivIic] using
            (lowerOp_eq y x z).symm

theorem allHull : ∀ y : I, HullIic y := by
  intro y
  refine wellFounded_lt.induction y ?_
  intro y ih
  classical
  by_cases hy : (Iio y).Infinite
  · letI : Infinite (Iio y) := hy.to_subtype
    letI : Nonempty (Iio y) := inferInstance
    have hLower := lowerOp_from_previous y ih
    have hGood := enumAt_compatible y hy hLower
    have hOption := CompatibleEnumeration.onePointExtension_finiteHull
      (lowerOp y (fun z _ => enumAt z)) (rawPred (enumAt y) hy) hGood
    have hTrans := TransportScratch.finiteHull_transport
      (TransportScratch.optionIioEquivIic y)
      (CompatibleEnumeration.extendOp
        (lowerOp y (fun z _ => enumAt z)) (rawPred (enumAt y) hy)) hOption
    intro F
    rw [opIic_transport y hy]
    exact hTrans F
  · haveI : Finite (Iio y) := (Set.not_infinite.mp hy).to_subtype
    haveI : Finite (Iic y) :=
      Finite.of_equiv (Option (Iio y)) (TransportScratch.optionIioEquivIic y)
    letI : Fintype (Iic y) := Fintype.ofFinite _
    intro F
    refine ⟨Finset.univ, Finset.subset_univ _, ?_⟩
    intro x hx z hz
    exact Finset.mem_univ _

theorem globalFiniteHull : ∀ F : Finset I, ∃ B : Finset I,
    F ⊆ B ∧ CompatibleEnumeration.IsClosed op B := by
  classical
  intro F
  by_cases hF : F.Nonempty
  · let m : I := F.max' hF
    let F' : Finset (Iic m) := F.attach.image (fun x =>
      (⟨x.1, Finset.le_max' F x.1 x.2⟩ : Iic m))
    obtain ⟨B', hFB', hB'⟩ := allHull m F'
    refine ⟨B'.image Subtype.val, ?_, ?_⟩
    · intro x hx
      let a : Iic m := ⟨x, Finset.le_max' F x hx⟩
      have ha : a ∈ F' := Finset.mem_image.mpr
        ⟨⟨x, hx⟩, Finset.mem_attach F ⟨x, hx⟩, rfl⟩
      exact Finset.mem_image.mpr ⟨a, hFB' ha, rfl⟩
    · intro x hx z hz
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hz
      exact Finset.mem_image.mpr ⟨opIic m a b, hB' a ha b hb, rfl⟩
  · refine ⟨∅, ?_, ?_⟩
    · simp [Finset.not_nonempty_iff_eq_empty.mp hF]
    · intro x hx
      simp at hx

end JonssonLF

namespace JonssonLF

open ChainApproximation
open Set FirstOrder FirstOrder.Language Cardinal

noncomputable instance : Nonempty I := Cardinal.mk_ne_zero_iff.mp (by
  rw [cofinalIndex_card]
  exact Cardinal.isRegular_aleph_one.ne_zero)

noncomputable instance : Infinite I := Cardinal.aleph0_le_mk_iff.mp (by
  rw [cofinalIndex_card]
  exact Cardinal.aleph0_le_aleph 1)

def binaryLanguage : FirstOrder.Language :=
  ⟨fun n => PLift (n = 2), fun _ => Empty⟩

@[reducible] noncomputable def binaryStructure : binaryLanguage.Structure I where
  funMap := by
    intro n h xs
    rcases h with ⟨h⟩
    subst n
    exact op (xs 0) (xs 1)
  RelMap := by
    intro n r
    cases r

noncomputable instance : binaryLanguage.Structure I := binaryStructure

theorem binaryLanguage_countable : Countable (Σ n, binaryLanguage.Functions n) := by
  letI (n : ℕ) : Countable (binaryLanguage.Functions n) := by
    change Countable (PLift (n = 2))
    infer_instance
  infer_instance

theorem locallyFinite : ChainApproximation.Algebra.LocallyFinite binaryLanguage I := by
  intro F
  obtain ⟨B, hFB, hB⟩ := globalFiniteHull F
  let S : binaryLanguage.Substructure I := {
    carrier := (B : Set I)
    fun_mem := by
      intro n fn xs hxs
      rcases fn with ⟨hn⟩
      subst n
      change op (xs 0) (xs 1) ∈ B
      exact hB (xs 0) (hxs 0) (xs 1) (hxs 1)
  }
  have hF : (F : Set I) ⊆ S := by
    intro x hx
    exact hFB hx
  have hcl : FirstOrder.Language.Substructure.closure binaryLanguage (F : Set I) ≤ S :=
    FirstOrder.Language.Substructure.closure_le.mpr hF
  exact B.finite_toSet.subset hcl

theorem op_mem (S : binaryLanguage.Substructure I) {x y : I}
    (hx : x ∈ S) (hy : y ∈ S) : op x y ∈ S := by
  have h := S.fun_mem (PLift.up (rfl : 2 = 2)) ![x, y] (by
    intro i
    fin_cases i <;> simp_all)
  change op x y ∈ S at h
  exact h

end JonssonLF

namespace JonssonLF

open ChainApproximation
open Set FirstOrder FirstOrder.Language Cardinal

theorem I_hasCofinalChain : HasCofinalChain I :=
  ⟨Set.univ, ⟨Set.univ_nonempty, fun _ _ _ _ _ ↦ le_total _ _⟩, IsCofinal.univ⟩

theorem I_cof : Order.cof I = Cardinal.aleph 1 :=
  regular_cofinalIndex_cof Cardinal.isRegular_aleph_one

theorem countable_bounded {S : Set I} (hS : S.Countable) : BddAbove S := by
  apply I_hasCofinalChain.small_bounded S
  rw [I_cof]
  exact (Cardinal.le_aleph0_iff_set_countable.mpr hS).trans_lt
    Cardinal.aleph0_lt_aleph_one

theorem nat_pred_closed_infinite (T : Set ℕ) (hT : T.Infinite)
    (hpred : ∀ n ∈ T, Nat.pred n ∈ T) : T = Set.univ := by
  ext n
  constructor
  · intro _
    trivial
  · intro _
    obtain ⟨m, hm, hnm⟩ := hT.exists_gt n
    have hdown : ∀ k m : ℕ, k ≤ m → m ∈ T → k ∈ T := by
      intro k m hkm
      induction hkm with
      | refl => exact id
      | @step m hkm ih =>
        intro hm1
        exact ih (by simpa only [Nat.pred_succ] using hpred (m + 1) hm1)
    exact hdown n m hnm.le hm

theorem closed_contains_initial (S : binaryLanguage.Substructure I) (y : I)
    (hy : y ∈ S) (hiy : (Iio y).Infinite)
    (hT : ({x : Iio y | x.1 ∈ S} : Set (Iio y)).Infinite) :
    (Iio y : Set I) ⊆ S := by
  let e := enumAt y hiy
  let T : Set (Iio y) := {x | x.1 ∈ S}
  let N : Set ℕ := e '' T
  have hN : N.Infinite := hT.image e.injective.injOn
  have hNpred : ∀ n ∈ N, Nat.pred n ∈ N := by
    intro n hn
    obtain ⟨x, hx, rfl⟩ := hn
    let z : Iio y := rawPred (enumAt y) hiy x
    have hz : z ∈ T := by
      change z.1 ∈ S
      have hf : op x.1 y ∈ S := op_mem S hx hy
      have heq : op x.1 y = z.1 := by
        unfold op
        have hxy : x.1 < y := x.2
        rw [dif_pos hxy, dif_pos hiy]
      exact heq ▸ hf
    refine ⟨z, hz, ?_⟩
    simp [z, rawPred, e]
  have hfull : N = Set.univ := nat_pred_closed_infinite N hN hNpred
  intro x hxy
  let xx : Iio y := ⟨x, hxy⟩
  have hmem : e xx ∈ N := by rw [hfull]; trivial
  obtain ⟨z, hz, heq⟩ := hmem
  have hzx : z = xx := e.injective heq
  change xx ∈ T
  exact hzx ▸ hz

theorem Iic_countable (y : I) : (Iic y).Countable := by
  rw [← Set.Iio_insert]
  exact (Iio_countable y).insert y

theorem uncountable_unbounded {S : Set I} (hS : ¬ S.Countable) : ¬ BddAbove S := by
  intro hb
  obtain ⟨y, hy⟩ := hb
  apply hS
  exact (Iic_countable y).mono hy

theorem uncountable_substructure_top (S : binaryLanguage.Substructure I)
    (hS : ¬ (S : Set I).Countable) : S = ⊤ := by
  have hSinfinite : (S : Set I).Infinite := by
    intro hfinite
    exact hS hfinite.countable
  obtain ⟨T, hTS, hTcountable, hTinfinite⟩ := hSinfinite.exists_subset_countable_infinite
  obtain ⟨b, hb⟩ := countable_bounded hTcountable
  have hSunbounded : ¬ BddAbove (S : Set I) := uncountable_unbounded hS
  ext x
  constructor
  · intro _
    trivial
  · intro _
    obtain ⟨y, hy, hxy⟩ := (not_bddAbove_iff.mp hSunbounded) (max x b)
    have hby : b < y := lt_of_le_of_lt (le_max_right x b) hxy
    have hxy' : x < y := lt_of_le_of_lt (le_max_left x b) hxy
    have hiy : (Iio y).Infinite := by
      apply hTinfinite.mono
      intro t ht
      exact (hb ht).trans_lt hby
    letI : Infinite T := hTinfinite.to_subtype
    let e : T ↪ Iio y := {
      toFun := fun t => ⟨t.1, (hb t.2).trans_lt hby⟩
      inj' := by intro a c hac; exact Subtype.ext (congrArg (fun z : Iio y => z.val) hac) }
    have hsub : Set.range e ⊆ ({z : Iio y | z.1 ∈ S} : Set (Iio y)) := by
      rintro z ⟨t, rfl⟩
      exact hTS t.2
    have hTiy : ({z : Iio y | z.1 ∈ S} : Set (Iio y)).Infinite :=
      (Set.infinite_range_of_injective e.injective).mono hsub
    exact closed_contains_initial S y hy hiy hTiy hxy'

theorem jonsson : Algebra.Jonsson binaryLanguage I := by
  refine ⟨inferInstance, binaryLanguage_countable, ?_⟩
  intro S hcard
  apply uncountable_substructure_top S
  intro hS
  have hle : Cardinal.mk S ≤ Cardinal.aleph0 :=
    Cardinal.mk_le_aleph0_iff.mpr hS.to_subtype
  rw [hcard, cofinalIndex_card] at hle
  exact Cardinal.aleph0_lt_aleph_one.not_ge hle


end JonssonLF

namespace JonssonLF

open ChainApproximation Cardinal FirstOrder

theorem exists_locallyFinite_jonsson_aleph_one :
    ∃ (L : FirstOrder.Language.{0, 0}) (M : Type)
      (str : L.Structure M),
      Cardinal.mk M = Cardinal.aleph 1 ∧
        @ChainApproximation.Algebra.LocallyFinite L M str ∧
        @ChainApproximation.Algebra.Jonsson L M str := by
  refine ⟨binaryLanguage, I, binaryStructure,
    cofinalIndex_card (Cardinal.aleph 1 : Cardinal.{0}), ?_, ?_⟩
  · exact locallyFinite
  · exact jonsson

end JonssonLF

end ChainApproximation
