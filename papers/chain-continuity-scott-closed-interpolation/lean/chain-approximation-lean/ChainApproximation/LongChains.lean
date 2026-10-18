import ChainApproximation.Cofinality

/-! # Strict chains shorter than the cofinality of a chain-generated ideal -/

set_option autoImplicit false

universe u

namespace ChainApproximation

open Set Cardinal

variable {P : Type u} [PartialOrder P]

theorem HasCofinalChain.strictMono_above_of_lt (hP : HasCofinalChain P)
    {ν : Cardinal.{u}} (hν : Cardinal.aleph0 ≤ ν) (hνP : ν < Order.cof P) (p : P) :
    ∃ f : CofinalIndex ν → P, StrictMono f ∧ ∀ a, p ≤ f a := by
  classical
  have hex : ∀ a : CofinalIndex ν, ∀ rec : (∀ j, j < a → P),
      ∃ q : P, p ≤ q ∧ ∀ j (hja : j < a), rec j hja < q := by
    intro a rec
    let g : Set.Iio a → P := fun j ↦ rec j.val j.property
    obtain ⟨r, hr⟩ := hP.small_bounded (insert p (Set.range g))
      ((card_insert_range_lt hν (cofinalIndex_initial_small ν a) g p).trans hνP)
    obtain ⟨q, hrq⟩ := hP.exists_gt
      (ne_of_gt (Cardinal.one_lt_aleph0.trans_le hν |>.trans hνP)) r
    exact ⟨q, (hr (Set.mem_insert _ _)).trans hrq.le, fun j hja ↦
      (hr (Set.mem_insert_of_mem _ (Set.mem_range_self (f := g) ⟨j, hja⟩))).trans_lt hrq⟩
  choose step hstep using hex
  let f : CofinalIndex ν → P := wellFounded_lt.fix step
  have hspec (a : CofinalIndex ν) : p ≤ f a ∧ ∀ j, j < a → f j < f a := by
    have h := hstep a (fun j _ ↦ f j)
    have heq : f a = step a (fun j _ ↦ f j) := by
      exact WellFounded.fix_eq wellFounded_lt step a
    rwa [← heq] at h
  exact ⟨f, fun a b hab ↦ (hspec b).2 a hab, fun a ↦ (hspec a).1⟩

theorem cof_range_strictMono {I : Type u} [LinearOrder I] {f : I → P} (hf : StrictMono f) :
    Order.cof (Set.range f) = Order.cof I := by
  let g : I → Set.range f := fun i ↦ ⟨f i, Set.mem_range_self i⟩
  have hg : StrictMono g := fun i j hij ↦ hf hij
  have hcof : IsCofinal (Set.range g) := by
    rintro ⟨_, i, rfl⟩
    exact ⟨g i, Set.mem_range_self _, le_rfl⟩
  exact (cof_eq_of_strictMono_cofinal hg hcof).symm

theorem strictMono_lub_not_mem {I : Type u} [LinearOrder I] [NoMaxOrder I]
    {f : I → P} (hf : StrictMono f) {p : P} (hp : IsLUB (Set.range f) p) :
    p ∉ Set.range f := by
  rintro ⟨i, rfl⟩
  obtain ⟨j, hij⟩ := exists_gt i
  exact not_le_of_gt (hf hij) (hp.1 (Set.mem_range_self j))

theorem regular_cofinalIndex_cof {ν : Cardinal.{u}} (hν : Cardinal.IsRegular ν) :
    Order.cof (CofinalIndex ν) = ν :=
  (Ordinal.cof_toType ν.ord).trans hν.cof_ord

end ChainApproximation
