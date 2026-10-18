import ChainApproximation.Comparisons

/-!
# The transfinite matrix construction in `prop:obstruction`

Rows live in nested chain-generated ideals. Each new entry bounds one seed,
all earlier entries of the same row, and the immediately preceding entry in
the same column. Neither completeness of the individual ideals nor a chain
cofinal in their union is assumed.
-/

set_option autoImplicit false

universe u

namespace ChainApproximation

open Set Cardinal

variable {P : Type u} [PartialOrder P]

section Construction

variable (I : ℕ → Set P) (hI : ∀ n, HasCofinalChain (I n))
  (hnest : ∀ n, I n ⊆ I (n + 1)) (κ : Cardinal.{u})
  (hκ : Cardinal.aleph0 ≤ κ) (hcard : ∀ n, Order.cof (I n) = κ)
  (b : ∀ n, CofinalIndex κ → I n)

include hI hκ hcard in
private theorem rowCap_exists (a : CofinalIndex κ)
    (rec : ∀ j, j < a → ∀ n, I n) (n : ℕ) :
    ∃ q : I n, b n a ≤ q ∧ ∀ j (hja : j < a), rec j hja n ≤ q := by
  let f : Set.Iio a → I n := fun j ↦ rec j.val j.property n
  have hsmall : Cardinal.mk (insert (b n a) (Set.range f) : Set (I n)) < Order.cof (I n) := by
    rw [hcard n]
    exact card_insert_range_lt hκ (cofinalIndex_initial_small κ a) f (b n a)
  obtain ⟨q, hq⟩ := (hI n).small_bounded (insert (b n a) (Set.range f)) hsmall
  exact ⟨q, hq (Set.mem_insert _ _), fun j hja ↦
    hq (Set.mem_insert_of_mem _ (Set.mem_range_self (f := f) ⟨j, hja⟩))⟩

private noncomputable def rowCap (a : CofinalIndex κ)
    (rec : ∀ j, j < a → ∀ n, I n) (n : ℕ) : I n :=
  Classical.choose (rowCap_exists I hI κ hκ hcard b a rec n)

private theorem rowCap_spec (a : CofinalIndex κ)
    (rec : ∀ j, j < a → ∀ n, I n) (n : ℕ) :
    b n a ≤ rowCap I hI κ hκ hcard b a rec n ∧
      ∀ j (hja : j < a), rec j hja n ≤ rowCap I hI κ hκ hcard b a rec n :=
  Classical.choose_spec (rowCap_exists I hI κ hκ hcard b a rec n)

private noncomputable def combine (n : ℕ) (q : I (n + 1)) (p : I n) : I (n + 1) :=
  let h := (hI (n + 1)).directed.2 q trivial
    (⟨p.val, hnest n p.property⟩ : I (n + 1)) trivial
  ⟨(Classical.choose h).val, (Classical.choose h).property⟩

private theorem combine_spec (n : ℕ) (q : I (n + 1)) (p : I n) :
    q.val ≤ (combine I hI hnest n q p).val ∧ p.val ≤ (combine I hI hnest n q p).val := by
  have h := Classical.choose_spec ((hI (n + 1)).directed.2 q trivial
    (⟨p.val, hnest n p.property⟩ : I (n + 1)) trivial)
  exact ⟨h.2.1, h.2.2⟩

private noncomputable def row (a : CofinalIndex κ)
    (rec : ∀ j, j < a → ∀ n, I n) : ∀ n, I n
  | 0 => rowCap I hI κ hκ hcard b a rec 0
  | n + 1 => combine I hI hnest n (rowCap I hI κ hκ hcard b a rec (n + 1))
      (row a rec n)

private theorem cap_le_row (a : CofinalIndex κ)
    (rec : ∀ j, j < a → ∀ n, I n) (n : ℕ) :
    (rowCap I hI κ hκ hcard b a rec n).val ≤ (row I hI hnest κ hκ hcard b a rec n).val := by
  cases n with
  | zero => exact le_rfl
  | succ n => exact (combine_spec I hI hnest n _ _).1

private theorem row_step (a : CofinalIndex κ)
    (rec : ∀ j, j < a → ∀ n, I n) (n : ℕ) :
    (row I hI hnest κ hκ hcard b a rec n).val ≤
      (row I hI hnest κ hκ hcard b a rec (n + 1)).val :=
  (combine_spec I hI hnest n _ _).2

private noncomputable def matrixRow : CofinalIndex κ → ∀ n, I n :=
  wellFounded_lt.fix (fun a rec ↦ row I hI hnest κ hκ hcard b a rec)

private theorem matrixRow_eq (a : CofinalIndex κ) :
    matrixRow I hI hnest κ hκ hcard b a =
      row I hI hnest κ hκ hcard b a (fun j _ ↦ matrixRow I hI hnest κ hκ hcard b j) := by
  rw [matrixRow, WellFounded.fix_eq]

include hI hnest hκ hcard in
/-- The exact matrix inequalities used by the manuscript. The construction
is independent of the cofinality of the ambient countable sequence. -/
theorem exists_monotone_matrix :
    ∃ e : ℕ → CofinalIndex κ → P,
      (∀ n a, e n a ∈ I n) ∧
      (∀ n a, (b n a).val ≤ e n a) ∧
      (∀ a, Monotone (fun n ↦ e n a)) ∧
      ∀ n, Monotone (e n) := by
  let e : ℕ → CofinalIndex κ → P := fun n a ↦
    (matrixRow I hI hnest κ hκ hcard b a n).val
  refine ⟨e, fun n a ↦ (matrixRow I hI hnest κ hκ hcard b a n).property, ?_, ?_, ?_⟩
  · intro n a
    change (b n a).val ≤ (matrixRow I hI hnest κ hκ hcard b a n).val
    rw [matrixRow_eq]
    exact (show (b n a).val ≤ (rowCap I hI κ hκ hcard b a _ n).val from
      (rowCap_spec I hI κ hκ hcard b a _ n).1).trans
        (cap_le_row I hI hnest κ hκ hcard b a _ n)
  · intro a
    apply monotone_nat_of_le_succ
    intro n
    change (matrixRow I hI hnest κ hκ hcard b a n).val ≤
      (matrixRow I hI hnest κ hκ hcard b a (n + 1)).val
    rw [matrixRow_eq]
    exact row_step I hI hnest κ hκ hcard b a _ n
  · intro n a c hac
    rcases hac.eq_or_lt with rfl | hac
    · exact le_rfl
    · change (matrixRow I hI hnest κ hκ hcard b a n).val ≤
        (matrixRow I hI hnest κ hκ hcard b c n).val
      rw [matrixRow_eq I hI hnest κ hκ hcard b c]
      exact (show (matrixRow I hI hnest κ hκ hcard b a n).val ≤
        (rowCap I hI κ hκ hcard b c _ n).val from
        (rowCap_spec I hI κ hκ hcard b c
          (fun j _ ↦ matrixRow I hI hnest κ hκ hcard b j) n).2 a hac).trans
          (cap_le_row I hI hnest κ hκ hcard b c _ n)

end Construction

end ChainApproximation
