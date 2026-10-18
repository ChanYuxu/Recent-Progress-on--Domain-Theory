import Practice.DomainTheory.Papers.UnitIntervalRetracts.Splitting
import Mathlib.Order.KonigLemma

/-!
# Finite dyadic grids and König compactness

This file formalizes `rem:finite-grid`.  A compatible branch through the
finite types of increasing choices on the dyadic grids is obtained from
König's infinity lemma, and then converted into the global dyadic thread used
by `dyadicThreadCriterion`.
-/

set_option autoImplicit false
set_option linter.unnecessarySimpa false

universe u

namespace UnitIntervalRetracts

open Set
open AbramskyJung.Chapter2

noncomputable section

/-- The point `k / 2^n` of the half-open dyadic grid at level `n`. -/
def dyadicGridPoint (n : ℕ) (k : Fin (2 ^ n)) : DyadicBelowOne := by
  have hpowpos : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have hkltReal : (k : ℝ) < (2 : ℝ) ^ n := by
    exact_mod_cast k.isLt
  exact
    ⟨⟨(k : ℝ) / (2 : ℝ) ^ n,
        ⟨div_nonneg (Nat.cast_nonneg k) hpowpos.le,
          (div_le_one₀ hpowpos).2 hkltReal.le⟩⟩,
      ⟨⟨n, k, rfl⟩, (div_lt_one hpowpos).2 hkltReal⟩⟩

/-- The finite grid `D_n = {k / 2^n | 0 ≤ k < 2^n}`. -/
def dyadicGrid (n : ℕ) : Set DyadicBelowOne :=
  Set.range (dyadicGridPoint n)

theorem dyadicGrid_finite (n : ℕ) :
    (dyadicGrid n).Finite :=
  Set.finite_range _

@[simp]
theorem dyadicGridPoint_succ_even (n : ℕ) (k : Fin (2 ^ n)) :
    dyadicGridPoint (n + 1)
        ⟨2 * k, by
          rw [pow_succ]
          simpa [Nat.mul_comm] using
            (Nat.mul_lt_mul_left (by norm_num : 0 < 2)).2
              k.isLt⟩ =
      dyadicGridPoint n k := by
  apply Subtype.ext
  apply Subtype.ext
  simp only [dyadicGridPoint]
  rw [pow_succ]
  norm_num
  ring

theorem dyadicGrid_subset_succ (n : ℕ) :
    dyadicGrid n ⊆ dyadicGrid (n + 1) := by
  rintro d ⟨k, rfl⟩
  exact
    ⟨⟨2 * k, by
        rw [pow_succ]
        simpa [Nat.mul_comm] using
          (Nat.mul_lt_mul_left (by norm_num : 0 < 2)).2
            k.isLt⟩,
      dyadicGridPoint_succ_even n k⟩

theorem dyadicGrid_mono : Monotone dyadicGrid :=
  monotone_nat_of_le_succ dyadicGrid_subset_succ

theorem mem_some_dyadicGrid (d : DyadicBelowOne) :
    ∃ n, d ∈ dyadicGrid n := by
  rcases d.2.1 with ⟨n, k, hdk⟩
  have hpowpos : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have hkltReal : (k : ℝ) < (2 : ℝ) ^ n := by
    rw [← (div_lt_one hpowpos)]
    rw [← hdk]
    exact d.2.2
  have hklt : k < 2 ^ n := by
    exact_mod_cast hkltReal
  refine ⟨n, ⟨⟨k, hklt⟩, ?_⟩⟩
  apply Subtype.ext
  apply Subtype.ext
  exact hdk.symm

variable {Q : Type u} [PartialOrder Q]

/-- Increasing choices from the prescribed finite fibers on one dyadic grid. -/
def DyadicGridChoice
    (E : DyadicBelowOne → Set Q) (n : ℕ) :=
  {c : (d : dyadicGrid n) → E d.1 //
    ∀ ⦃d e : dyadicGrid n⦄, d < e → (c d : Q) ≤ (c e : Q)}

/-- Restrict a choice on a later grid to an earlier grid. -/
def restrictDyadicGridChoice
    (E : DyadicBelowOne → Set Q) {i j : ℕ} (hij : i ≤ j) :
    DyadicGridChoice E j → DyadicGridChoice E i := by
  intro c
  refine
    ⟨fun d =>
        c.1
          ⟨d.1, dyadicGrid_mono hij d.2⟩,
      ?_⟩
  intro d e hde
  exact c.2 hde

theorem restrictDyadicGridChoice_refl
    (E : DyadicBelowOne → Set Q) {i : ℕ}
    (c : DyadicGridChoice E i) :
    restrictDyadicGridChoice E (le_refl i) c = c := by
  apply Subtype.ext
  funext d
  rfl

theorem restrictDyadicGridChoice_trans
    (E : DyadicBelowOne → Set Q) {i j k : ℕ}
    (hij : i ≤ j) (hjk : j ≤ k)
    (c : DyadicGridChoice E k) :
    restrictDyadicGridChoice E hij
        (restrictDyadicGridChoice E hjk c) =
      restrictDyadicGridChoice E (hij.trans hjk) c := by
  apply Subtype.ext
  funext d
  rfl

/-- `rem:finite-grid`, branch form: compatible finite-grid choices determine
one increasing global choice from all prescribed dyadic fibers. -/
theorem exists_increasing_dyadic_choice_of_finite_grids
    (E : DyadicBelowOne → Set Q)
    (hEfinite : ∀ d, (E d).Finite)
    (_hEnonempty : ∀ d, (E d).Nonempty)
    (hgrid : ∀ n, Nonempty (DyadicGridChoice E n)) :
    ∃ x : DyadicBelowOne → Q,
      (∀ d, x d ∈ E d) ∧
        ∀ ⦃d e : DyadicBelowOne⦄, d < e → x d ≤ x e := by
  letI (d : DyadicBelowOne) : Finite (E d) :=
    (hEfinite d).to_subtype
  letI (n : ℕ) : Finite (dyadicGrid n) :=
    (dyadicGrid_finite n).to_subtype
  letI (n : ℕ) : Nonempty (DyadicGridChoice E n) :=
    hgrid n
  have hchoiceFinite (n : ℕ) :
      Finite (DyadicGridChoice E n) := by
    have hPiFinite :
        Finite ((d : dyadicGrid n) → E d.1) := by
      infer_instance
    exact
      Finite.of_injective
        (fun c : DyadicGridChoice E n => c.1)
        (fun _ _ h => Subtype.ext h)
  letI (n : ℕ) : Finite (DyadicGridChoice E n) :=
    hchoiceFinite n
  obtain ⟨choices, hchoices⟩ :=
    exists_seq_forall_proj_of_forall_finite
      (α := fun n => DyadicGridChoice E n)
      (π := fun {_i _j} hij =>
        restrictDyadicGridChoice E hij)
      (π_refl := by
        intro i c
        exact restrictDyadicGridChoice_refl E c)
      (π_trans := by
        intro i j k hij hjk c
        exact restrictDyadicGridChoice_trans E hij hjk c)
      (hfin := by
        intro i a
        exact Set.toFinite _)
  let level : DyadicBelowOne → ℕ :=
    fun d => Classical.choose (mem_some_dyadicGrid d)
  have hlevel (d : DyadicBelowOne) :
      d ∈ dyadicGrid (level d) :=
    Classical.choose_spec (mem_some_dyadicGrid d)
  let x : DyadicBelowOne → Q :=
    fun d =>
      choices (level d) |>.1 ⟨d, hlevel d⟩
  refine ⟨x, ?_, ?_⟩
  · intro d
    exact (choices (level d)).1 ⟨d, hlevel d⟩ |>.2
  · intro d e hde
    let N := max (level d) (level e)
    have hdN : level d ≤ N := le_max_left _ _
    have heN : level e ≤ N := le_max_right _ _
    have hdmem : d ∈ dyadicGrid N :=
      dyadicGrid_mono hdN (hlevel d)
    have hemel : e ∈ dyadicGrid N :=
      dyadicGrid_mono heN (hlevel e)
    change
      ((choices (level d)).1 ⟨d, hlevel d⟩ : Q) ≤
        ((choices (level e)).1 ⟨e, hlevel e⟩ : Q)
    have hdcompat :
        ((choices (level d)).1 ⟨d, hlevel d⟩ : Q) =
          ((choices N).1 ⟨d, hdmem⟩ : Q) := by
      have h :=
        congrArg
          (fun c : DyadicGridChoice E (level d) =>
            ((c.1 ⟨d, hlevel d⟩ : E d) : Q))
          (hchoices hdN)
      simpa [restrictDyadicGridChoice] using h.symm
    have hecompat :
        ((choices (level e)).1 ⟨e, hlevel e⟩ : Q) =
          ((choices N).1 ⟨e, hemel⟩ : Q) := by
      have h :=
        congrArg
          (fun c : DyadicGridChoice E (level e) =>
            ((c.1 ⟨e, hlevel e⟩ : E e) : Q))
          (hchoices heN)
      simpa [restrictDyadicGridChoice] using h.symm
    calc
      ((choices (level d)).1 ⟨d, hlevel d⟩ : Q) =
          ((choices N).1 ⟨d, hdmem⟩ : Q) := hdcompat
      _ ≤ ((choices N).1 ⟨e, hemel⟩ : Q) :=
        (choices N).2 (show
          (⟨d, hdmem⟩ : dyadicGrid N) <
            ⟨e, hemel⟩ from hde)
      _ = ((choices (level e)).1 ⟨e, hlevel e⟩ : Q) :=
        hecompat.symm

/-- `rem:finite-grid`, section form: finite exact fibers and solvability of
every finite dyadic grid force a Scott-continuous section. -/
theorem finiteGridChoices_give_scottContinuous_section
    (hQ : IsDcpo Q) (f : Q → UnitInterval)
    (hf : AbramskyJung.Chapter2.ScottContinuous f)
    (hfSurjective : Function.Surjective f)
    (E : DyadicBelowOne → Set Q)
    (hEfinite : ∀ d, (E d).Finite)
    (hEnonempty : ∀ d, (E d).Nonempty)
    (hEfiber : ∀ d q, q ∈ E d → f q = (d : UnitInterval))
    (hgrid : ∀ n, Nonempty (DyadicGridChoice E n)) :
    ∃ s : UnitInterval → Q,
      AbramskyJung.Chapter2.ScottContinuous s ∧
        Function.LeftInverse f s := by
  obtain ⟨x, hxE, hxmono⟩ :=
    exists_increasing_dyadic_choice_of_finite_grids
      E hEfinite hEnonempty hgrid
  apply
    (dyadicThreadCriterion hQ f hf hfSurjective).2
  exact
    ⟨x,
      ⟨fun d => hEfiber d (x d) (hxE d),
        fun _d _e hde => hxmono hde⟩⟩

end

end UnitIntervalRetracts
