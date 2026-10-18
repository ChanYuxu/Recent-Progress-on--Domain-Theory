import FiniteValuationApproximable.ContinuousValuation.JonesDMC

/-!
# Additivity of the Jones lower integral

Pointwise addition preserves bounded Scott-continuous functions.  The lower
bound for integral additivity follows by adding lower simple functions.  For
the reverse bound, two uniform Jones grids approximate the two summands and
the remaining two-mesh error is sent to zero.
-/

set_option autoImplicit false
set_option linter.unnecessarySimpa false

universe u

namespace FiniteValuationApproximable
namespace ContinuousValuation

open AbramskyJung.Chapter2
open scoped BigOperators ENNReal

namespace BoundedScottFunction

variable {D : Type u} [Preorder D]

noncomputable def zero : BoundedScottFunction D where
  toFun := fun _ => 0
  continuous := const_scottContinuous 0
  bounded := ⟨0, ENNReal.zero_ne_top, fun _ => le_rfl⟩

@[simp] theorem zero_apply (x : D) : (zero : BoundedScottFunction D) x = 0 := rfl

/-- Pointwise sum of bounded Scott-continuous ENNReal-valued functions. -/
noncomputable def add (f g : BoundedScottFunction D) : BoundedScottFunction D where
  toFun := fun x => f x + g x
  continuous := by
    constructor
    · intro x y hxy
      exact add_le_add (f.continuous.monotone hxy) (g.continuous.monotone hxy)
    · intro A s hA hs
      have hf : IsSup (f '' A) (f s) := f.continuous.maps_isSup hA hs
      have hg : IsSup (g '' A) (g s) := g.continuous.maps_isSup hA hs
      constructor
      · rintro _ ⟨x, hxA, rfl⟩
        exact add_le_add (hf.1 ⟨x, hxA, rfl⟩) (hg.1 ⟨x, hxA, rfl⟩)
      · intro y hy
        have hfEq : f s = ⨆ x : A, f x.1 :=
          isSup_image_eq_iSup_subtype f (f s) hf
        have hgEq : g s = ⨆ x : A, g x.1 :=
          isSup_image_eq_iSup_subtype g (g s) hg
        change f s + g s ≤ y
        rw [hfEq, hgEq, ENNReal.iSup_add_iSup (fun x z => by
          rcases hA.2 x.2 z.2 with ⟨w, hwA, hxw, hzw⟩
          exact ⟨⟨w, hwA⟩,
            add_le_add (f.continuous.monotone hxw)
              (g.continuous.monotone hzw)⟩)]
        exact iSup_le fun x => hy ⟨x.1, x.2, rfl⟩
  bounded := by
    rcases f.bounded with ⟨c, hc, hfc⟩
    rcases g.bounded with ⟨d, hd, hgd⟩
    exact ⟨c + d, ENNReal.add_ne_top.2 ⟨hc, hd⟩,
      fun x => add_le_add (hfc x) (hgd x)⟩

@[simp] theorem add_apply (f g : BoundedScottFunction D) (x : D) :
    add f g x = f x + g x := rfl

end BoundedScottFunction

namespace JonesLowerIntegral

variable {D : Type u} [Preorder D]

noncomputable section

private theorem lowerSimple_nonempty (f : BoundedScottFunction D) :
    Nonempty (LowerOpenSimple f) := by
  exact ⟨⟨OpenSimpleFunction.zero, fun x => by simp⟩⟩

/-- Adding two lower simple functions gives the easy direction of integral
additivity. -/
theorem add_le (mu : VSub D) (f g : BoundedScottFunction D) :
    jonesLowerIntegral mu f + jonesLowerIntegral mu g ≤
      jonesLowerIntegral mu (BoundedScottFunction.add f g) := by
  letI : Nonempty (LowerOpenSimple f) := lowerSimple_nonempty f
  letI : Nonempty (LowerOpenSimple g) := lowerSimple_nonempty g
  unfold jonesLowerIntegral
  apply ENNReal.iSup_add_iSup_le
  intro s t
  rw [← OpenSimpleFunction.add_integral]
  apply simple_le
  intro x
  rw [OpenSimpleFunction.add_value,
    ENNReal.ofReal_add (s.1.value_nonneg x) (t.1.value_nonneg x)]
  exact add_le_add (s.2 x) (t.2 x)

/-- A lower simple function for `f+g` is bounded by the sum of uniform grids
for `f` and `g`, plus two meshes. -/
private theorem simple_integral_le_add_add_eps (mu : VSub D)
    (f g : BoundedScottFunction D) (s : OpenSimpleFunction D)
    (hs : ∀ x, ENNReal.ofReal (s.value x) ≤
      BoundedScottFunction.add f g x)
    (ε : NNReal) (hε : 0 < ε) :
    s.integral mu ≤
      jonesLowerIntegral mu f + jonesLowerIntegral mu g + (ε : ℝ≥0∞) := by
  have hεReal : 0 < (ε : ℝ) := by exact_mod_cast hε
  have hhalf : 0 < (ε : ℝ) / 2 := div_pos hεReal (by norm_num)
  rcases exists_nat_one_div_lt hhalf with ⟨n, hn⟩
  have hdelta : 2 * JonesGrid.delta n < (ε : ℝ) := by
    have hd : JonesGrid.delta n < (ε : ℝ) / 2 := by
      simpa [JonesGrid.delta] using hn
    linarith
  rcases JonesGrid.exists_uniform_upper f n with ⟨Mf, hf⟩
  rcases JonesGrid.exists_uniform_upper g n with ⟨Mg, hg⟩
  let qf : OpenSimpleFunction D := JonesGrid.simple f n Mf
  let qg : OpenSimpleFunction D := JonesGrid.simple g n Mg
  let e : OpenSimpleFunction D := OpenSimpleFunction.single
    (2 * JonesGrid.delta n)
      (mul_nonneg (by norm_num) (JonesGrid.delta_nonneg n))
      (ScottOpen.univ : ScottOpen D)
  have hpoint : ∀ x,
      s.value x ≤
        (OpenSimpleFunction.add (OpenSimpleFunction.add qf qg) e).value x := by
    intro x
    have hENN : ENNReal.ofReal (s.value x) ≤
        ENNReal.ofReal (JonesGrid.realValue f n Mf x + JonesGrid.delta n) +
          ENNReal.ofReal (JonesGrid.realValue g n Mg x + JonesGrid.delta n) :=
      (hs x).trans (add_le_add (hf x) (hg x))
    have hnonnegf : 0 ≤ JonesGrid.realValue f n Mf x + JonesGrid.delta n :=
      add_nonneg (JonesGrid.realValue_nonneg f n Mf x) (JonesGrid.delta_nonneg n)
    have hnonnegg : 0 ≤ JonesGrid.realValue g n Mg x + JonesGrid.delta n :=
      add_nonneg (JonesGrid.realValue_nonneg g n Mg x) (JonesGrid.delta_nonneg n)
    rw [← ENNReal.ofReal_add hnonnegf hnonnegg] at hENN
    have hreal : s.value x ≤
        (JonesGrid.realValue f n Mf x + JonesGrid.delta n) +
          (JonesGrid.realValue g n Mg x + JonesGrid.delta n) :=
      (ENNReal.ofReal_le_ofReal_iff (add_nonneg hnonnegf hnonnegg)).mp hENN
    rw [OpenSimpleFunction.add_value, OpenSimpleFunction.add_value]
    have hqfValue : qf.value x = JonesGrid.realValue f n Mf x := by
      simpa only [qf] using JonesGrid.simple_value_eq_realValue f n Mf x
    have hqgValue : qg.value x = JonesGrid.realValue g n Mg x := by
      simpa only [qg] using JonesGrid.simple_value_eq_realValue g n Mg x
    have heValue : e.value x = 2 * JonesGrid.delta n := by
      simp [e]
    rw [hqfValue, hqgValue, heValue]
    linarith
  have hmono := OpenSimpleFunction.integral_mono mu hpoint
  have hqf : qf.integral mu ≤ jonesLowerIntegral mu f := by
    exact JonesGrid.grid_integral_le_lowerIntegral mu f n Mf
  have hqg : qg.integral mu ≤ jonesLowerIntegral mu g := by
    exact JonesGrid.grid_integral_le_lowerIntegral mu g n Mg
  have he : e.integral mu ≤ ENNReal.ofReal (2 * JonesGrid.delta n) := by
    exact JonesGrid.single_univ_integral_le mu (2 * JonesGrid.delta n)
      (mul_nonneg (by norm_num) (JonesGrid.delta_nonneg n))
  have hdeltaENN : ENNReal.ofReal (2 * JonesGrid.delta n) ≤ (ε : ℝ≥0∞) := by
    simpa using ENNReal.ofReal_le_ofReal hdelta.le
  calc
    s.integral mu ≤ (qf.integral mu + qg.integral mu) + e.integral mu := by
      simpa only [OpenSimpleFunction.add_integral] using hmono
    _ ≤ (jonesLowerIntegral mu f + jonesLowerIntegral mu g) +
        ENNReal.ofReal (2 * JonesGrid.delta n) :=
      add_le_add (add_le_add hqf hqg) he
    _ ≤ jonesLowerIntegral mu f + jonesLowerIntegral mu g + (ε : ℝ≥0∞) :=
      add_le_add le_rfl hdeltaENN

/-- Reverse inequality in integral additivity, obtained by sending the grid
error to zero. -/
theorem le_add (mu : VSub D) (f g : BoundedScottFunction D) :
    jonesLowerIntegral mu (BoundedScottFunction.add f g) ≤
      jonesLowerIntegral mu f + jonesLowerIntegral mu g := by
  apply le_of_simple_bounds
  intro s hs
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _hfinite
  exact simple_integral_le_add_add_eps mu f g s hs ε hε

/-- Jones's lower integral is additive on bounded nonnegative
Scott-continuous functions. -/
theorem add (mu : VSub D) (f g : BoundedScottFunction D) :
    jonesLowerIntegral mu (BoundedScottFunction.add f g) =
      jonesLowerIntegral mu f + jonesLowerIntegral mu g := by
  exact le_antisymm (le_add mu f g) (add_le mu f g)

end
end JonesLowerIntegral
end ContinuousValuation
end FiniteValuationApproximable
