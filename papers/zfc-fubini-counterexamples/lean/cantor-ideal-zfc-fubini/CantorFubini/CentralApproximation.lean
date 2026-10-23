import CantorFubini.CentralTopology
import CantorFubini.ValuationIntegral

/-! New finite-range clopen approximations for compact-parameter Fubini.
Approximants are genuine locally constant parameter maps into LSC partner
functions, ordered pointwise below the given integrand. They do not store
commutation, integrals, or a desired theorem as record assumptions. -/

set_option autoImplicit false
open Set Topology TopologicalSpace MeasureTheory
open scoped ENNReal
universe u v
namespace CantorFubini

theorem IsRealLSC.ennreal_ofReal {X : Type u} [TopologicalSpace X]
    {f : X → ℝ} (hf : IsRealLSC f) : IsVLSC (fun x => ENNReal.ofReal (f x)) := by
  intro a
  by_cases ha : a = ∞
  · simp [ha]
  · convert hf a.toReal using 1
    ext x
    exact ENNReal.lt_ofReal_iff_toReal_lt ha

structure ClopenStep {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (k : X → Y → ℝ≥0∞) where
  val : X → Y → ℝ≥0∞
  locally_constant : IsLocallyConstant val
  lsc : ∀ x, IsVLSC (val x)
  below : ∀ x y, val x y ≤ k x y

namespace ClopenStep
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
variable {k : X → Y → ℝ≥0∞}

def zero (k : X → Y → ℝ≥0∞) : ClopenStep k where
  val := fun _ _ => 0
  locally_constant := IsLocallyConstant.const (fun _ => 0)
  lsc := fun _ => isVLSC_const 0
  below := fun _ _ => zero_le _

instance : Nonempty (ClopenStep k) := ⟨zero k⟩

def sup (s t : ClopenStep k) : ClopenStep k where
  val := fun x y => s.val x y ⊔ t.val x y
  locally_constant := s.locally_constant.comp₂ t.locally_constant
    (fun f g : Y → ℝ≥0∞ => fun y => f y ⊔ g y)
  lsc := by
    intro x a
    have he : {y | a < s.val x y ⊔ t.val x y} =
        {y | a < s.val x y} ∪ {y | a < t.val x y} := by
      ext y
      change a < s.val x y ⊔ t.val x y ↔ a < s.val x y ∨ a < t.val x y
      exact lt_sup_iff
    rw [he]
    exact (s.lsc x a).union (t.lsc x a)
  below := fun x y => sup_le (s.below x y) (t.below x y)

theorem directed : Directed (· ≤ ·) (fun s : ClopenStep k => s.val) := by
  intro s t
  exact ⟨sup s t, fun x y => le_sup_left, fun x y => le_sup_right⟩

theorem parameter_isLocallyConstant (s : ClopenStep k) (y : Y) :
    IsLocallyConstant (fun x => s.val x y) :=
  s.locally_constant.comp (fun f : Y → ℝ≥0∞ => f y)

theorem parameter_isVLSC (s : ClopenStep k) (y : Y) :
    IsVLSC (fun x => s.val x y) := by
  intro a
  exact s.locally_constant {f : Y → ℝ≥0∞ | a < f y}

theorem range_finite [CompactSpace X] (s : ClopenStep k) : (range s.val).Finite :=
  s.locally_constant.range_finite

/-- A clopen parameter rectangle is an actual member of the approximation
family whenever its height is bounded by the integrand on that rectangle. -/
noncomputable def rectangle (C : Set X) (hC : IsClopen C) (V : Opens Y) (c : ℝ≥0∞)
    (hbelow : ∀ x ∈ C, ∀ y ∈ V, c ≤ k x y) : ClopenStep k where
  val := fun x => C.indicator (fun _ => (V : Set Y).indicator (fun _ => c)) x
  locally_constant :=
    ((LocallyConstant.const X ((V : Set Y).indicator (fun _ => c))).indicator hC).isLocallyConstant
  lsc := by
    intro x
    by_cases hx : x ∈ C
    · simpa only [indicator_of_mem hx] using isVLSC_indicator V c
    · simpa only [indicator_of_notMem hx] using (isVLSC_const (X := Y) 0)
  below := by
    intro x y
    by_cases hx : x ∈ C
    · by_cases hy : y ∈ V
      · simpa only [indicator_of_mem hx, indicator_of_mem hy] using hbelow x hx y hy
      · simp only [indicator_of_mem hx, indicator_of_notMem hy, zero_le]
    · simp only [indicator_of_notMem hx, Pi.zero_apply, zero_le]

end ClopenStep

section Approximation
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
variable [CompactSpace X] [T2Space X] [TotallyDisconnectedSpace X]
variable (k : X → Y → ℝ≥0∞)

/-- Every product-LSC integrand is the directed pointwise supremum of the
finite-range clopen parameter approximants just constructed. -/
theorem clopenStep_iSup (hk : IsVLSC (fun z : X × Y => k z.1 z.2)) (x : X) (y : Y) :
    (⨆ s : ClopenStep k, s.val x y) = k x y := by
  apply le_antisymm
  · exact iSup_le (fun s => s.below x y)
  · apply le_of_forall_lt
    intro a ha
    obtain ⟨c, hac, hck⟩ := exists_between ha
    obtain ⟨U, V, hUo, hVo, hxU, hyV, hUV⟩ :=
      isOpen_prod_iff.mp (hk c) x y hck
    obtain ⟨C, hCc, hxC, hCU⟩ := compact_exists_isClopen_in_isOpen hUo hxU
    let s : ClopenStep k := ClopenStep.rectangle C hCc ⟨V, hVo⟩ c
      (fun t ht z hz => by
        have htz := hUV (show (t, z) ∈ U ×ˢ V from ⟨hCU ht, hz⟩)
        exact htz.le)
    have hs : s.val x y = c := by
      change C.indicator (fun _ => V.indicator (fun _ => c)) x y = c
      rw [indicator_of_mem hxC, indicator_of_mem hyV]
    exact hac.trans_le (hs ▸ le_iSup (fun s : ClopenStep k => s.val x y) s)

end Approximation
end CantorFubini
