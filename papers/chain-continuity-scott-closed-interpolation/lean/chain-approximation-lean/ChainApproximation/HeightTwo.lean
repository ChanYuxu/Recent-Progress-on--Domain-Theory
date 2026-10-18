import ChainApproximation.Extension

/-!
# The height-two counterexample

Source equation (erne-poset), `thm:closed-counter`, and the noninterpolation
part of `prop:same-lattice`. In this encoding `c n` is the source's `c_(n+1)`;
thus `b m < c n` means `m < n+1`. The shift keeps every index a natural number
while preserving the source requirement that the c-indices start at one.
-/

set_option autoImplicit false

namespace ChainApproximation

open Set

inductive HeightTwo
  | b : ℕ → HeightTwo
  | c : ℕ → HeightTwo
  deriving DecidableEq

namespace HeightTwo

def le : HeightTwo → HeightTwo → Prop
  | b m, b n => m = n
  | b m, c n => m < n + 1
  | c _, b _ => False
  | c m, c n => m = n

instance : PartialOrder HeightTwo where
  le := le
  le_refl := by intro a; cases a <;> rfl
  le_trans := by
    intro a b c hab hbc
    cases a <;> cases b <;> cases c <;> simp_all [le]
  le_antisymm := by
    intro a b hab hba
    cases a <;> cases b <;> simp_all [le]

instance : Countable HeightTwo := by
  let f : HeightTwo → ℕ ⊕ ℕ
    | b n => Sum.inl n
    | c n => Sum.inr n
  apply Function.Injective.countable (f := f)
  intro a b hab
  cases a <;> cases b <;> simp_all [f]

@[simp] theorem b_le_b (m n : ℕ) : b m ≤ b n ↔ m = n := Iff.rfl
@[simp] theorem b_le_c (m n : ℕ) : b m ≤ c n ↔ m < n + 1 := Iff.rfl
@[simp] theorem not_c_le_b (m n : ℕ) : ¬ c m ≤ b n := fun h ↦ h
@[simp] theorem c_le_c (m n : ℕ) : c m ≤ c n ↔ m = n := Iff.rfl

theorem c_maximal {n : ℕ} {q : HeightTwo} (h : c n ≤ q) : q = c n := by
  cases q with
  | b m => exact False.elim h
  | c m => exact congrArg c h.symm

def B : LowerSet HeightTwo :=
  ⟨{q | ∃ n, q = b n}, by
    intro y x hxy hy
    obtain ⟨n, hn⟩ := hy
    subst y
    cases x with
    | b m => exact ⟨m, rfl⟩
    | c m => exact False.elim hxy⟩

@[simp] theorem b_mem_B (n : ℕ) : b n ∈ B := ⟨n, rfl⟩
@[simp] theorem c_not_mem_B (n : ℕ) : c n ∉ B := by
  rintro ⟨m, h⟩
  cases h

theorem B_nonempty : (B : Set HeightTwo).Nonempty := ⟨b 0, b_mem_B 0⟩

theorem B_ne_bot : B ≠ ⊥ := by
  intro hB
  have h : b 0 ∈ (⊥ : LowerSet HeightTwo) := hB ▸ b_mem_B 0
  exact h

def index : HeightTwo → ℕ
  | b n => n
  | c n => n

theorem B_finiteUpper_top : FiniteUpper (B : Set HeightTwo) Set.univ := by
  classical
  intro F hFB
  refine ⟨c (F.sup index), trivial, ?_⟩
  intro q hq
  obtain ⟨m, rfl⟩ := hFB hq
  exact Nat.lt_succ_of_le (Finset.le_sup (f := index) hq)

theorem B_closedBelow_top : ClosedBelow B (⊤ : LowerSet HeightTwo) :=
  (closedBelow_iff_finiteUpper B ⊤ ⟨b 0, trivial⟩).mpr B_finiteUpper_top

theorem B_not_closedBelow_self : ¬ ClosedBelow B B := by
  intro hBB
  have hF : (({b 0, b 1} : Finset HeightTwo) : Set HeightTwo) ⊆ B := by
    intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact b_mem_B 0
    · exact Finset.mem_singleton.mp hq ▸ b_mem_B 1
  obtain ⟨q, hqB, hFq⟩ := (closedBelow_iff_finiteUpper B B B_nonempty).mp hBB _ hF
  obtain ⟨m, rfl⟩ := hqB
  have h0 : 0 = m := hFq (b 0) (Finset.mem_insert_self _ _)
  have h1 : 1 = m := hFq (b 1) (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  omega

theorem closedBelow_top_of_contains_c {A : LowerSet HeightTwo}
    (hA : ClosedBelow A ⊤) {n : ℕ} (hcn : c n ∈ A) : A = LowerSet.Iic (c n) := by
  apply le_antisymm
  · intro a ha
    have hF : (({a, c n} : Finset HeightTwo) : Set HeightTwo) ⊆ A := by
      intro q hq
      rcases Finset.mem_insert.mp hq with rfl | hq
      · exact ha
      · exact Finset.mem_singleton.mp hq ▸ hcn
    obtain ⟨q, _, hFq⟩ := (closedBelow_iff_finiteUpper A ⊤ ⟨b 0, trivial⟩).mp hA _ hF
    have hq : q = c n := c_maximal
      (hFq (c n) (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))
    exact hq ▸ hFq a (Finset.mem_insert_self _ _)
  · exact LowerSet.Iic_le.mpr hcn

theorem B_not_le_principal_c (n : ℕ) : ¬ B ≤ LowerSet.Iic (c n) := by
  intro hB
  have h : n + 1 < n + 1 := hB (b_mem_B (n + 1))
  exact lt_irrefl _ h

theorem closedBelow_top_containing_B {A : LowerSet HeightTwo}
    (hBA : B ≤ A) (hA : ClosedBelow A ⊤) : A = B := by
  apply le_antisymm
  · intro q hq
    cases q with
    | b m => exact b_mem_B m
    | c n =>
      have hEq := closedBelow_top_of_contains_c hA hq
      exact False.elim (B_not_le_principal_c n (hEq ▸ hBA))
  · exact hBA

/-- Source noninterpolating pair (noninterpolating-pair). -/
theorem B_no_closed_intermediate :
    ¬ RelComp ClosedBelow ClosedBelow B (⊤ : LowerSet HeightTwo) := by
  rintro ⟨A, hBA, hAT⟩
  have hA : A = B := closedBelow_top_containing_B hBA.le hAT
  exact B_not_closedBelow_self (hA ▸ hBA)

theorem closedBelow_does_not_interpolate :
    ¬ Interpolates (ClosedBelow (M := LowerSet HeightTwo)) :=
  fun hi ↦ B_no_closed_intermediate (hi B ⊤ B_closedBelow_top)

theorem B_no_closedPlus_intermediate :
    ¬ RelComp ClosedBelowPlus ClosedBelowPlus B (⊤ : LowerSet HeightTwo) :=
  fun h ↦ B_no_closed_intermediate ((closed_intermediate_iff_plus B_ne_bot).mpr h)

theorem closedBelowPlus_does_not_interpolate :
    ¬ Interpolates (ClosedBelowPlus (M := LowerSet HeightTwo)) := by
  intro hi
  exact B_no_closedPlus_intermediate (hi B ⊤
    ((closedBelowPlus_iff B ⊤).mpr (Or.inl B_closedBelow_top)))

end HeightTwo

end ChainApproximation
