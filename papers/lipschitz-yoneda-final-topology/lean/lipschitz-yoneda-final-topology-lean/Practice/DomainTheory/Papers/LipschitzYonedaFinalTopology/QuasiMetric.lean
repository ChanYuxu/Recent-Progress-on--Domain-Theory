import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Data.ENNReal.Operations
import Mathlib.Data.ENNReal.Real
import Mathlib.Topology.Order.ScottTopology
import Practice.DomainTheory.Papers.LipschitzYonedaFinalTopology.LayeredTopology

/-!
# Source-facing quasi-metric and Lipschitz-layer definitions

This file records the foundational objects used in
`lipschitz_yoneda_final_topology_paper_fifth_audit.tex`.  Distances and
function values lie in `ℝ≥0∞`; formal-ball radii and Lipschitz constants lie
in the finite type `ℝ≥0`.

The direct net definition of Yoneda continuity is represented for nets whose
index type lives in the same universe as the source carrier.  This explicit
universe boundary is recorded in `FORMALIZATION_STATUS.md`.
-/

set_option autoImplicit false
set_option linter.unnecessarySimpa false

open Set Function Topology
open scoped NNReal ENNReal

universe u v

namespace LipschitzYonedaFinalTopology

/-- A `T₀` extended quasi-metric, with values in `[0,+∞]`. -/
structure QuasiMetric (X : Type u) where
  edist : X → X → ℝ≥0∞
  edist_self : ∀ x, edist x x = 0
  edist_triangle : ∀ x y z, edist x z ≤ edist x y + edist y z
  eq_of_edist_zero : ∀ {x y}, edist x y = 0 → edist y x = 0 → x = y

namespace QuasiMetric

variable {X : Type u} (d : QuasiMetric X)

/-- The asymmetric distance on `[0,+∞]` used in the manuscript. -/
def ennreal : QuasiMetric ℝ≥0∞ where
  edist u v := u - v
  edist_self u := tsub_self u
  edist_triangle u v w := tsub_le_tsub_add_tsub
  eq_of_edist_zero := by
    intro u v huv hvu
    exact le_antisymm (tsub_eq_zero_iff_le.mp huv) (tsub_eq_zero_iff_le.mp hvu)

/-- A formal ball has a point as center and a finite nonnegative radius. -/
structure FormalBall (d : QuasiMetric X) where
  center : X
  radius : ℝ≥0

namespace FormalBall

instance : LE (d.FormalBall) where
  le p q := d.edist p.center q.center + (q.radius : ℝ≥0∞) ≤ p.radius

theorem le_def {p q : d.FormalBall} :
    p ≤ q ↔ d.edist p.center q.center + (q.radius : ℝ≥0∞) ≤ p.radius :=
  Iff.rfl

instance : PartialOrder (d.FormalBall) where
  le := (· ≤ ·)
  le_refl p := by simp [le_def, d.edist_self]
  le_trans p q r hpq hqr := by
    have hpq' :
        d.edist p.center q.center + (q.radius : ℝ≥0∞) ≤ p.radius := hpq
    have hqr' :
        d.edist q.center r.center + (r.radius : ℝ≥0∞) ≤ q.radius := hqr
    calc
      d.edist p.center r.center + (r.radius : ℝ≥0∞)
          ≤ (d.edist p.center q.center + d.edist q.center r.center) +
              (r.radius : ℝ≥0∞) :=
            add_le_add (d.edist_triangle _ _ _) le_rfl
      _ = d.edist p.center q.center +
            (d.edist q.center r.center + (r.radius : ℝ≥0∞)) := by
              ac_rfl
      _ ≤ d.edist p.center q.center + (q.radius : ℝ≥0∞) :=
            by
              simpa only [add_comm] using
                add_le_add_right hqr' (d.edist p.center q.center)
      _ ≤ (p.radius : ℝ≥0∞) := hpq'
  le_antisymm p q hpq hqp := by
    rcases p with ⟨x, r⟩
    rcases q with ⟨y, s⟩
    change d.edist x y + (s : ℝ≥0∞) ≤ r at hpq
    change d.edist y x + (r : ℝ≥0∞) ≤ s at hqp
    have hsr : (s : ℝ≥0∞) ≤ r :=
      (show (s : ℝ≥0∞) ≤ d.edist x y + s from le_add_left le_rfl).trans hpq
    have hrs : (r : ℝ≥0∞) ≤ s :=
      (show (r : ℝ≥0∞) ≤ d.edist y x + r from le_add_left le_rfl).trans hqp
    have hradius : r = s := by
      exact_mod_cast le_antisymm hrs hsr
    have hxy_zero : d.edist x y = 0 := by
      apply le_antisymm _ (zero_le _)
      apply (ENNReal.add_le_add_iff_right ENNReal.coe_ne_top).mp
      simpa [hradius] using hpq
    have hyx_zero : d.edist y x = 0 := by
      apply le_antisymm _ (zero_le _)
      apply (ENNReal.add_le_add_iff_right ENNReal.coe_ne_top).mp
      simpa [hradius] using hqp
    obtain rfl := d.eq_of_edist_zero hxy_zero hyx_zero
    obtain rfl := hradius
    rfl

/-- Adding a finite amount to the radius of a formal ball. -/
def shift (t : ℝ≥0) (p : d.FormalBall) : d.FormalBall :=
  ⟨p.center, p.radius + t⟩

end FormalBall

set_option linter.unusedVariables false in
/-- A copy of `X` carrying the topology induced from the Scott topology on
formal balls by `x ↦ (x,0)`. -/
def DScott (d : QuasiMetric X) := X

namespace DScott

instance : TopologicalSpace d.DScott :=
  TopologicalSpace.induced
    (fun x : d.DScott ↦
      WithScott.toScott (⟨x, 0⟩ : d.FormalBall))
    inferInstance

end DScott

/-- Lower semicontinuity with respect to the `d`-Scott topology and the Scott
topology on `[0,+∞]`. -/
def IsLowerSemicontinuous (f : X → ℝ≥0∞) : Prop :=
  Continuous
    (fun x : d.DScott ↦ WithScott.toScott (f x))

/-- The manuscript's one-sided Cauchy condition for a net. -/
def IsCauchyNet {ι : Type v} [Preorder ι] (x : ι → X) : Prop :=
  ∀ ε : ℝ≥0, 0 < ε →
    ∃ i₀ : ι, ∀ i j : ι, i₀ ≤ i → i ≤ j →
      d.edist (x i) (x j) < (ε : ℝ≥0∞)

/-- The explicit `limsup` used in the definition of a `d`-limit. -/
noncomputable def netLimsup {ι : Type v} [Preorder ι] (a : ι → ℝ≥0∞) : ℝ≥0∞ :=
  ⨅ i : ι, ⨆ j : ι, ⨆ (_h : i ≤ j), a j

/-- The limsup of a constant net over a nonempty preorder is that constant. -/
theorem netLimsup_const {ι : Type v} [Preorder ι] [Nonempty ι]
    (a : ℝ≥0∞) :
    netLimsup (fun _ : ι ↦ a) = a := by
  apply le_antisymm
  · refine (iInf_le
      (fun i : ι ↦ ⨆ j : ι, ⨆ (_h : i ≤ j), a)
      (Classical.choice inferInstance)).trans ?_
    apply iSup_le
    intro j
    apply iSup_le
    intro _h
    exact le_rfl
  · apply le_iInf
    intro i
    exact le_iSup_of_le i (le_iSup_of_le le_rfl le_rfl)

/-- A point is a `d`-limit when its outgoing distances are the corresponding
net limsups. -/
def IsDLimit {ι : Type v} [Preorder ι] (x : ι → X) (x₀ : X) : Prop :=
  ∀ y : X, d.edist x₀ y = netLimsup (fun i ↦ d.edist (x i) y)

/-- Direct Yoneda continuity for `[0,+∞]`-valued maps.  Preservation of the
Cauchy property is included explicitly; for Lipschitz maps it is redundant,
but it makes the source's image-net clause directly inspectable. -/
def IsDirectedIndex (ι : Type u) [Preorder ι] : Prop :=
  Nonempty ι ∧ ∀ i j : ι, ∃ k : ι, i ≤ k ∧ j ≤ k

/-- Every directed Cauchy net has a `d`-limit.  This is the source's notion
of Yoneda completeness, with the same explicit universe boundary as
`IsYonedaContinuous`. -/
def IsYonedaComplete : Prop :=
  ∀ (ι : Type u) [Preorder ι] (x : ι → X),
    IsDirectedIndex ι → d.IsCauchyNet x →
      ∃ x₀ : X, d.IsDLimit x x₀

structure IsYonedaContinuous (f : X → ℝ≥0∞) : Prop where
  maps_cauchy :
    ∀ (ι : Type u) [Preorder ι] (x : ι → X),
      IsDirectedIndex ι → d.IsCauchyNet x →
        QuasiMetric.ennreal.IsCauchyNet (fun i ↦ f (x i))
  maps_dLimit :
    ∀ (ι : Type u) [Preorder ι] (x : ι → X) (x₀ : X),
      IsDirectedIndex ι → d.IsCauchyNet x → d.IsDLimit x x₀ →
        QuasiMetric.ennreal.IsDLimit (fun i ↦ f (x i)) (f x₀)

/-- The manuscript's `α`-Lipschitz inequality. -/
def IsLipschitz (α : ℝ≥0) (f : X → ℝ≥0∞) : Prop :=
  ∀ x y : X,
    QuasiMetric.ennreal.edist (f x) (f y) ≤
      (α : ℝ≥0∞) * d.edist x y

theorem IsLipschitz.mono {α β : ℝ≥0} {f : X → ℝ≥0∞}
    (hf : d.IsLipschitz α f) (hαβ : α ≤ β) :
    d.IsLipschitz β f := by
  intro x y
  exact (hf x y).trans (mul_le_mul_left (by exact_mod_cast hαβ) _)

/-- The constant zero map is Lipschitz for every finite constant. -/
theorem zero_isLipschitz (α : ℝ≥0) :
    d.IsLipschitz α (fun _ : X ↦ (0 : ℝ≥0∞)) := by
  intro x y
  simp [QuasiMetric.ennreal]

/-- The constant zero map preserves all directed Cauchy nets and their
`d`-limits. -/
theorem zero_isYonedaContinuous :
    d.IsYonedaContinuous (fun _ : X ↦ (0 : ℝ≥0∞)) where
  maps_cauchy := by
    intro ι _ x hdir _hx ε hε
    letI : Nonempty ι := hdir.1
    refine ⟨Classical.choice inferInstance, ?_⟩
    intro i j _hi _hij
    simpa [QuasiMetric.ennreal] using hε
  maps_dLimit := by
    intro ι _ x x₀ hdir _hx _hlim y
    letI : Nonempty ι := hdir.1
    simp [QuasiMetric.ennreal, netLimsup_const]

/-- Lower semicontinuous `[0,+∞]`-valued maps. -/
def LowerMap := {f : X → ℝ≥0∞ // d.IsLowerSemicontinuous f}

namespace LowerMap

instance : CoeFun d.LowerMap (fun _ ↦ X → ℝ≥0∞) where
  coe f := f.1

instance : PartialOrder d.LowerMap where
  le f g := ∀ x, f x ≤ g x
  le_refl f x := le_rfl
  le_trans f g h hfg hgh x := le_trans (hfg x) (hgh x)
  le_antisymm f g hfg hgf := Subtype.ext (funext fun x ↦ le_antisymm (hfg x) (hgf x))

end LowerMap

/-- `𝓛(X)`, with the Scott topology of its pointwise order. -/
abbrev LSpace := WithScott d.LowerMap

namespace LSpace

instance : CoeFun d.LSpace (fun _ ↦ X → ℝ≥0∞) where
  coe f := (WithScott.ofScott f : d.LowerMap)

end LSpace

/-- The bottom lower-semicontinuous map. -/
def zeroLowerMap : d.LowerMap :=
  ⟨fun _ ↦ 0, continuous_const⟩

/-- The zero map as an element of the ambient Scott function space. -/
def zeroLSpace : d.LSpace :=
  WithScott.toScott d.zeroLowerMap

@[simp]
theorem zeroLSpace_apply (x : X) : d.zeroLSpace x = 0 :=
  rfl

/-- Membership in a fixed Lipschitz Yoneda-continuous layer. -/
def InLayer (α : ℝ≥0) (f : d.LSpace) : Prop :=
  d.IsLipschitz α f ∧ d.IsYonedaContinuous f

/-- The union of all positive finite Lipschitz layers, with the subspace
topology inherited from `𝓛(X)`. -/
abbrev LInf :=
  {f : d.LSpace // ∃ α : ℝ≥0, 0 < α ∧ d.InLayer α f}

namespace LInf

instance : CoeFun d.LInf (fun _ ↦ X → ℝ≥0∞) where
  coe f := f.1

end LInf

/-- The zero function belongs to every positive Lipschitz layer, hence to
`𝓛∞`. -/
def zeroLInf : d.LInf :=
  ⟨d.zeroLSpace, ⟨1, by positivity,
    d.zero_isLipschitz 1, d.zero_isYonedaContinuous⟩⟩

@[simp]
theorem zeroLInf_apply (x : X) : d.zeroLInf x = 0 :=
  rfl

/-- The integer layer indexed by `n`; this is the source layer `𝓛_{n+1}`. -/
def integerLayer (n : ℕ) : Set d.LInf :=
  {f | d.InLayer ((n + 1 : ℕ) : ℝ≥0) f.1}

theorem zeroLInf_mem_integerLayer (n : ℕ) :
    d.zeroLInf ∈ d.integerLayer n :=
  ⟨d.zero_isLipschitz _, d.zero_isYonedaContinuous⟩

theorem integerLayer_mono : Monotone d.integerLayer := by
  intro n m hnm f hf
  exact ⟨IsLipschitz.mono d hf.1 (by
    exact_mod_cast Nat.add_le_add_right hnm 1), hf.2⟩

theorem integerLayer_cover (f : d.LInf) :
    ∃ n : ℕ, f ∈ d.integerLayer n := by
  obtain ⟨α, hα, hfα⟩ := f.2
  obtain ⟨n, hn⟩ := exists_nat_ge α
  refine ⟨n, IsLipschitz.mono d hfα.1 ?_, hfα.2⟩
  exact hn.trans (by exact_mod_cast Nat.le_add_right n 1)

/-- The canonical increasing integer-layer system on `𝓛∞`. -/
def layerSystem : LayerSystem d.LInf where
  layer := d.integerLayer
  cover := d.integerLayer_cover
  monotone_layer := d.integerLayer_mono

/-- Property `D` for the Lipschitz Yoneda-continuous function space. -/
def PropertyD : Prop := d.layerSystem.PropertyD

/-- A positive finite Lipschitz constant. -/
def PositiveConstant := {α : ℝ≥0 // 0 < α}

/-- A layer indexed by an arbitrary positive finite constant. -/
def realLayer (α : PositiveConstant) : Set d.LInf :=
  {f | d.InLayer α.1 f.1}

/-- The manuscript's all-positive-real formulation of property `D` is
equivalent to the cofinal integer-layer formulation. -/
theorem propertyD_iff_all_positive_layers :
    d.PropertyD ↔
      ∀ U : Set d.LInf,
        (∀ α : PositiveConstant,
          IsOpen ((↑) ⁻¹' U : Set (d.realLayer α))) →
            IsOpen U := by
  constructor
  · intro hD U hU
    apply (d.layerSystem.propertyD_iff_layerwise_open.mp hD) U
    intro n
    let α : PositiveConstant :=
      ⟨((n + 1 : ℕ) : ℝ≥0), by positivity⟩
    simpa [realLayer, integerLayer, α] using hU α
  · intro h
    apply d.layerSystem.propertyD_iff_layerwise_open.mpr
    intro U hU
    apply h U
    intro α
    obtain ⟨n, hn⟩ := exists_nat_ge α.1
    have hsubset : d.realLayer α ⊆ d.integerLayer n := by
      intro f hf
      exact ⟨IsLipschitz.mono d hf.1
        (hn.trans (by exact_mod_cast Nat.le_add_right n 1)), hf.2⟩
    let inclusion : d.realLayer α → d.integerLayer n :=
      fun f ↦ ⟨f, hsubset f.2⟩
    have hcont : Continuous inclusion :=
      continuous_subtype_val.subtype_mk _
    simpa [inclusion, Set.preimage] using (hU n).preimage hcont

end QuasiMetric

end LipschitzYonedaFinalTopology
