import FiniteValuationApproximable.ContinuousValuation.JonesGridCofinal

/-!
# Directed monotone convergence for the Jones lower integral

The two arguments are handled separately.  In the integrand argument,
strict superlevels commute with directed suprema.  In the valuation argument,
evaluation at every Scott open commutes with directed suprema.  Cofinality of
the finite Jones grids reduces both proofs to synchronization of finitely many
coordinates in one directed family.
-/

set_option autoImplicit false
set_option linter.unnecessarySimpa false

universe u

namespace FiniteValuationApproximable
namespace ContinuousValuation

open AbramskyJung.Chapter2
open scoped BigOperators ENNReal

/-- A finite sum commutes with a supremum indexed by a family which is
simultaneously directed in every coordinate. -/
theorem finset_sum_iSup_of_directed {ι α : Type*}
    (S : Finset ι) (F : ι → α → ℝ≥0∞)
    (hF : ∀ a b : α, ∃ c : α, ∀ i : ι,
      F i a ≤ F i c ∧ F i b ≤ F i c) :
    (∑ i ∈ S, ⨆ a : α, F i a) =
      ⨆ a : α, ∑ i ∈ S, F i a := by
  induction S using Finset.cons_induction with
  | empty => simp
  | cons i S hi ih =>
      simp_rw [Finset.sum_cons, ih]
      refine ENNReal.iSup_add_iSup fun a b => ?_
      rcases hF a b with ⟨c, hc⟩
      exact ⟨c, add_le_add (hc i).1 (Finset.sum_le_sum fun j _ => (hc j).2)⟩

theorem sum_iSup_of_directed {ι α : Type*} [Fintype ι]
    (F : ι → α → ℝ≥0∞)
    (hF : ∀ a b : α, ∃ c : α, ∀ i : ι,
      F i a ≤ F i c ∧ F i b ≤ F i c) :
    (∑ i : ι, ⨆ a : α, F i a) =
      ⨆ a : α, ∑ i : ι, F i a := by
  simpa using finset_sum_iSup_of_directed Finset.univ F hF

namespace JonesGrid

theorem simple_integral_eq_sum {D : Type u} [Preorder D]
    (mu : VSub D) (f : BoundedScottFunction D) (n M : Nat) :
    (simple f n M).integral mu =
      ∑ i : Fin M, ENNReal.ofReal (delta n) * mu (levelOpen f n i.1) := by
  rw [OpenSimpleFunction.integral_eq_sum]
  rfl

end JonesGrid

namespace JonesLowerIntegral

variable {D : Type u} [Preorder D]

noncomputable section

/-- Jones (1990), Theorem 3.13: directed monotone convergence in the
integrand argument. -/
theorem directed_mono_convergence_integrand
    {A : Set (BoundedScottFunction D)}
    (hA : DirectedSet A) (f : BoundedScottFunction D)
    (hf : ∀ x : D,
      IsSup ((fun g : BoundedScottFunction D => g x) '' A) (f x))
    (mu : VSub D) :
    IsSup ((fun g : BoundedScottFunction D => jonesLowerIntegral mu g) '' A)
      (jonesLowerIntegral mu f) := by
  constructor
  · rintro _ ⟨g, hgA, rfl⟩
    apply mono
    intro x
    exact (hf x).1 ⟨g, hgA, rfl⟩
  · intro y hy
    rw [JonesGrid.lowerIntegral_eq_integralSup]
    unfold JonesGrid.integralSup
    refine iSup_le fun n => iSup_le fun M => ?_
    rw [OpenSimpleFunction.integral_eq_sum]
    change (∑ i : Fin M,
      ENNReal.ofReal (JonesGrid.delta n) *
        mu (JonesGrid.levelOpen f n i.1)) ≤ y
    have hcoord (i : Fin M) :
        mu (JonesGrid.levelOpen f n i.1) =
          ⨆ g : A, mu (JonesGrid.levelOpen g.1 n i.1) := by
      have hsup := BoundedScottFunction.valuation_superlevel_isSup
        hA f hf mu
          (ENNReal.ofReal (JonesGrid.threshold n i.1))
      have heq := isSup_image_eq_iSup_subtype
        (fun g : BoundedScottFunction D =>
          mu (BoundedScottFunction.superlevel g
            (ENNReal.ofReal (JonesGrid.threshold n i.1))))
        (mu (BoundedScottFunction.superlevel f
          (ENNReal.ofReal (JonesGrid.threshold n i.1)))) hsup
      simpa [JonesGrid.levelOpen] using heq
    calc
      (∑ i : Fin M,
          ENNReal.ofReal (JonesGrid.delta n) *
            mu (JonesGrid.levelOpen f n i.1)) =
          ∑ i : Fin M,
            ENNReal.ofReal (JonesGrid.delta n) *
              (⨆ g : A, mu (JonesGrid.levelOpen g.1 n i.1)) := by
            apply Finset.sum_congr rfl
            intro i _hi
            rw [hcoord i]
      _ = ∑ i : Fin M, ⨆ g : A,
            ENNReal.ofReal (JonesGrid.delta n) *
              mu (JonesGrid.levelOpen g.1 n i.1) := by
            apply Finset.sum_congr rfl
            intro i _hi
            rw [ENNReal.mul_iSup]
      _ = ⨆ g : A, ∑ i : Fin M,
            ENNReal.ofReal (JonesGrid.delta n) *
              mu (JonesGrid.levelOpen g.1 n i.1) := by
            let F : Fin M → A → ℝ≥0∞ := fun i g =>
              ENNReal.ofReal (JonesGrid.delta n) *
                mu (JonesGrid.levelOpen g.1 n i.1)
            have hF : ∀ g h : A, ∃ k : A, ∀ i : Fin M,
                F i g ≤ F i k ∧ F i h ≤ F i k := by
              intro g h
              rcases hA.2 g.2 h.2 with ⟨k, hkA, hgk, hhk⟩
              refine ⟨⟨k, hkA⟩, fun i => ⟨?_, ?_⟩⟩
              · exact mul_le_mul_right
                  (mu.monotone (BoundedScottFunction.superlevel_mono hgk _))
                  (ENNReal.ofReal (JonesGrid.delta n))
              · exact mul_le_mul_right
                  (mu.monotone (BoundedScottFunction.superlevel_mono hhk _))
                  (ENNReal.ofReal (JonesGrid.delta n))
            simpa only [F] using sum_iSup_of_directed F hF
      _ ≤ y := iSup_le fun g => by
            rw [← JonesGrid.simple_integral_eq_sum]
            exact (JonesGrid.grid_integral_le_lowerIntegral mu g.1 n M).trans
              (hy ⟨g.1, g.2, rfl⟩)

/-- Jones--Plotkin (1989), Theorem 3.3: directed monotone convergence in the
valuation argument. -/
theorem directed_mono_convergence_valuation
    {A : Set (VSub D)} (hA : DirectedSet A) (sigma : VSub D)
    (hsigma : IsSup A sigma) (f : BoundedScottFunction D) :
    IsSup ((fun mu : VSub D => jonesLowerIntegral mu f) '' A)
      (jonesLowerIntegral sigma f) := by
  constructor
  · rintro _ ⟨mu, hmuA, rfl⟩
    exact mono_valuation (hsigma.1 hmuA) f
  · intro y hy
    rw [JonesGrid.lowerIntegral_eq_integralSup]
    unfold JonesGrid.integralSup
    refine iSup_le fun n => iSup_le fun M => ?_
    rw [OpenSimpleFunction.integral_eq_sum]
    change (∑ i : Fin M,
      ENNReal.ofReal (JonesGrid.delta n) *
        sigma (JonesGrid.levelOpen f n i.1)) ≤ y
    have hcoord (i : Fin M) :
        sigma (JonesGrid.levelOpen f n i.1) =
          ⨆ mu : A, mu.1 (JonesGrid.levelOpen f n i.1) := by
      exact isSup_image_eq_iSup_subtype
        (fun mu : VSub D => mu (JonesGrid.levelOpen f n i.1))
        (sigma (JonesGrid.levelOpen f n i.1))
        (VSub.eval_isSup hA hsigma (JonesGrid.levelOpen f n i.1))
    calc
      (∑ i : Fin M,
          ENNReal.ofReal (JonesGrid.delta n) *
            sigma (JonesGrid.levelOpen f n i.1)) =
          ∑ i : Fin M,
            ENNReal.ofReal (JonesGrid.delta n) *
              (⨆ mu : A, mu.1 (JonesGrid.levelOpen f n i.1)) := by
            apply Finset.sum_congr rfl
            intro i _hi
            rw [hcoord i]
      _ = ∑ i : Fin M, ⨆ mu : A,
            ENNReal.ofReal (JonesGrid.delta n) *
              mu.1 (JonesGrid.levelOpen f n i.1) := by
            apply Finset.sum_congr rfl
            intro i _hi
            rw [ENNReal.mul_iSup]
      _ = ⨆ mu : A, ∑ i : Fin M,
            ENNReal.ofReal (JonesGrid.delta n) *
              mu.1 (JonesGrid.levelOpen f n i.1) := by
            let F : Fin M → A → ℝ≥0∞ := fun i mu =>
              ENNReal.ofReal (JonesGrid.delta n) *
                mu.1 (JonesGrid.levelOpen f n i.1)
            have hF : ∀ mu nu : A, ∃ rho : A, ∀ i : Fin M,
                F i mu ≤ F i rho ∧ F i nu ≤ F i rho := by
              intro mu nu
              rcases hA.2 mu.2 nu.2 with ⟨rho, hrhoA, hm, hn⟩
              refine ⟨⟨rho, hrhoA⟩, fun i => ⟨?_, ?_⟩⟩
              · exact mul_le_mul_right
                  (hm (JonesGrid.levelOpen f n i.1))
                  (ENNReal.ofReal (JonesGrid.delta n))
              · exact mul_le_mul_right
                  (hn (JonesGrid.levelOpen f n i.1))
                  (ENNReal.ofReal (JonesGrid.delta n))
            simpa only [F] using sum_iSup_of_directed F hF
      _ ≤ y := iSup_le fun mu => by
            rw [← JonesGrid.simple_integral_eq_sum]
            exact (JonesGrid.grid_integral_le_lowerIntegral mu.1 f n M).trans
              (hy ⟨mu.1, mu.2, rfl⟩)

end
end JonesLowerIntegral
end ContinuousValuation
end FiniteValuationApproximable
