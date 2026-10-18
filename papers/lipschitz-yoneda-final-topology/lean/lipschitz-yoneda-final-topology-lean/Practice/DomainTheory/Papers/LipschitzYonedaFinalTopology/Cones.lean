import Mathlib.Data.Finset.Lattice.Fold
import Practice.DomainTheory.Papers.LipschitzYonedaFinalTopology.QuasiMetric

/-!
# Finite cone envelopes

This file formalizes the order-algebraic part of the cone construction used
in `lipschitz_yoneda_final_topology_paper_fifth_audit.tex`.  The analytic
claim that a cone centred at a standard point is Yoneda-continuous is a
separate literature input; none of the results below assumes it.
-/

set_option autoImplicit false
set_option linter.unnecessarySimpa false

open Set
open scoped NNReal ENNReal

universe u v

namespace LipschitzYonedaFinalTopology
namespace QuasiMetric

variable {X : Type u} (d : QuasiMetric X)

/-- The truncated affine cone of height `a`, slope `α`, and centre `x`. -/
noncomputable def cone (α : ℝ≥0) (x : X) (a : ℝ≥0∞) (y : X) : ℝ≥0∞ :=
  a - (α : ℝ≥0∞) * d.edist x y

@[simp]
theorem cone_at_center (α : ℝ≥0) (x : X) (a : ℝ≥0∞) :
    d.cone α x a x = a := by
  simp [cone, d.edist_self]

/-- Every cone satisfies the manuscript's asymmetric `α`-Lipschitz
inequality. -/
theorem cone_isLipschitz (α : ℝ≥0) (x : X) (a : ℝ≥0∞) :
    d.IsLipschitz α (d.cone α x a) := by
  intro y z
  apply (tsub_tsub_tsub_le_tsub.trans)
  apply (tsub_le_iff_left.mpr)
  calc
    (α : ℝ≥0∞) * d.edist x z
        ≤ (α : ℝ≥0∞) * (d.edist x y + d.edist y z) :=
          by
            apply mul_le_mul_right
            exact d.edist_triangle x y z
    _ = (α : ℝ≥0∞) * d.edist x y +
          (α : ℝ≥0∞) * d.edist y z := by rw [mul_add]

/-- A cone based below an `α`-Lipschitz function lies below that function. -/
theorem cone_le_of_isLipschitz
    {α : ℝ≥0} {g : X → ℝ≥0∞}
    (hg : d.IsLipschitz α g) {x : X} {a : ℝ≥0∞}
    (ha : a ≤ g x) :
    d.cone α x a ≤ g := by
  intro y
  apply tsub_le_iff_left.mpr
  calc
    a ≤ g x := ha
    _ ≤ (α : ℝ≥0∞) * d.edist x y + g y := by
      simpa [add_comm] using (tsub_le_iff_left.mp (hg x y))

/-- The maximum of finitely many cones.  Nonemptiness avoids choosing an
artificial bottom cone. -/
noncomputable def finiteConeMax
    (α : ℝ≥0) (s : Finset X) (hs : s.Nonempty)
    (height : X → ℝ≥0∞) (y : X) : ℝ≥0∞ :=
  s.sup' hs (fun x ↦ d.cone α x (height x) y)

/-- A finite cone maximum is again `α`-Lipschitz. -/
theorem finiteConeMax_isLipschitz
    (α : ℝ≥0) (s : Finset X) (hs : s.Nonempty)
    (height : X → ℝ≥0∞) :
    d.IsLipschitz α (d.finiteConeMax α s hs height) := by
  intro y z
  apply tsub_le_iff_left.mpr
  change
    s.sup' hs (fun x ↦ d.cone α x (height x) y) ≤
      s.sup' hs (fun x ↦ d.cone α x (height x) z) +
        (α : ℝ≥0∞) * d.edist y z
  apply (Finset.sup'_le_iff hs
    (fun x ↦ d.cone α x (height x) y)).mpr
  intro x hx
  have hcone := d.cone_isLipschitz α x (height x) y z
  have hxz :
      d.cone α x (height x) z ≤ d.finiteConeMax α s hs height z := by
    exact Finset.le_sup' (fun w ↦ d.cone α w (height w) z) hx
  calc
    d.cone α x (height x) y
        ≤ d.cone α x (height x) z +
            (α : ℝ≥0∞) * d.edist y z :=
          tsub_le_iff_left.mp hcone
    _ ≤ d.finiteConeMax α s hs height z +
          (α : ℝ≥0∞) * d.edist y z := add_le_add hxz le_rfl

/-- The finite cone envelope lies below every `α`-Lipschitz function whose
values dominate the prescribed heights. -/
theorem finiteConeMax_le_of_isLipschitz
    {α : ℝ≥0} {s : Finset X} (hs : s.Nonempty)
    {height g : X → ℝ≥0∞}
    (hg : d.IsLipschitz α g)
    (hheight : ∀ x ∈ s, height x ≤ g x) :
    d.finiteConeMax α s hs height ≤ g := by
  intro y
  change s.sup' hs (fun x ↦ d.cone α x (height x) y) ≤ g y
  apply (Finset.sup'_le_iff hs
    (fun x ↦ d.cone α x (height x) y)).mpr
  intro x hx
  exact d.cone_le_of_isLipschitz hg (hheight x hx) y

/-- If the heights are sampled from an `α`-Lipschitz function, the finite
cone envelope agrees with that function on every sampled centre. -/
theorem finiteConeMax_eq_on_centers
    {α : ℝ≥0} {s : Finset X} (hs : s.Nonempty)
    {g : X → ℝ≥0∞} (hg : d.IsLipschitz α g)
    {x : X} (hx : x ∈ s) :
    d.finiteConeMax α s hs g x = g x := by
  apply le_antisymm
  · exact d.finiteConeMax_le_of_isLipschitz hs hg (fun _ _ ↦ le_rfl) x
  · calc
      g x = d.cone α x (g x) x := (d.cone_at_center α x (g x)).symm
      _ ≤ d.finiteConeMax α s hs g x :=
        Finset.le_sup' (fun w ↦ d.cone α w (g w) x) hx

/-- A strict threshold below a finite cone maximum is witnessed by one of
its cones.  This is the finite parent-selection step used in a cone forest. -/
theorem exists_cone_gt_of_lt_finiteConeMax
    {α : ℝ≥0} {s : Finset X} (hs : s.Nonempty)
    {height : X → ℝ≥0∞} {y : X} {b : ℝ≥0∞}
    (hb : b < d.finiteConeMax α s hs height y) :
    ∃ x ∈ s, b < d.cone α x (height x) y := by
  change b < s.sup' hs (fun x ↦ d.cone α x (height x) y) at hb
  exact (Finset.lt_sup'_iff hs).mp hb

/-- A finite cone maximum indexed by labels rather than by distinct centres.
This is the source-faithful representation when two constraints may choose
the same centre with different heights. -/
noncomputable def finiteConeFamilyMax
    {ι : Type v} (α : ℝ≥0) (s : Finset ι) (hs : s.Nonempty)
    (center : ι → X) (height : ι → ℝ≥0∞) (y : X) : ℝ≥0∞ :=
  s.sup' hs (fun i ↦ d.cone α (center i) (height i) y)

/-- A finitely indexed cone family has the same Lipschitz constant as each
of its members. -/
theorem finiteConeFamilyMax_isLipschitz
    {ι : Type v} (α : ℝ≥0) (s : Finset ι) (hs : s.Nonempty)
    (center : ι → X) (height : ι → ℝ≥0∞) :
    d.IsLipschitz α (d.finiteConeFamilyMax α s hs center height) := by
  intro y z
  apply tsub_le_iff_left.mpr
  change
    s.sup' hs (fun i ↦ d.cone α (center i) (height i) y) ≤
      s.sup' hs (fun i ↦ d.cone α (center i) (height i) z) +
        (α : ℝ≥0∞) * d.edist y z
  apply (Finset.sup'_le_iff hs
    (fun i ↦ d.cone α (center i) (height i) y)).mpr
  intro i hi
  have hcone := d.cone_isLipschitz α (center i) (height i) y z
  have hiz :
      d.cone α (center i) (height i) z ≤
        d.finiteConeFamilyMax α s hs center height z := by
    exact Finset.le_sup'
      (fun j ↦ d.cone α (center j) (height j) z) hi
  calc
    d.cone α (center i) (height i) y
        ≤ d.cone α (center i) (height i) z +
            (α : ℝ≥0∞) * d.edist y z :=
          tsub_le_iff_left.mp hcone
    _ ≤ d.finiteConeFamilyMax α s hs center height z +
          (α : ℝ≥0∞) * d.edist y z := add_le_add hiz le_rfl

/-- The finite labelled envelope lies below an `α`-Lipschitz function when
all of its prescribed heights do. -/
theorem finiteConeFamilyMax_le_of_isLipschitz
    {ι : Type v} {α : ℝ≥0} {s : Finset ι} (hs : s.Nonempty)
    {center : ι → X} {height : ι → ℝ≥0∞} {g : X → ℝ≥0∞}
    (hg : d.IsLipschitz α g)
    (hheight : ∀ i ∈ s, height i ≤ g (center i)) :
    d.finiteConeFamilyMax α s hs center height ≤ g := by
  intro y
  change s.sup' hs
    (fun i ↦ d.cone α (center i) (height i) y) ≤ g y
  apply (Finset.sup'_le_iff hs
    (fun i ↦ d.cone α (center i) (height i) y)).mpr
  intro i hi
  exact d.cone_le_of_isLipschitz hg (hheight i hi) y

/-- A strict threshold below a labelled finite envelope has a witnessing
label.  This is the parent-selection form used by the cone forest. -/
theorem exists_index_cone_gt_of_lt_finiteConeFamilyMax
    {ι : Type v} {α : ℝ≥0} {s : Finset ι} (hs : s.Nonempty)
    {center : ι → X} {height : ι → ℝ≥0∞} {y : X} {b : ℝ≥0∞}
    (hb : b < d.finiteConeFamilyMax α s hs center height y) :
    ∃ i ∈ s, b < d.cone α (center i) (height i) y := by
  change b < s.sup' hs
    (fun i ↦ d.cone α (center i) (height i) y) at hb
  exact (Finset.lt_sup'_iff hs).mp hb

end QuasiMetric
end LipschitzYonedaFinalTopology
