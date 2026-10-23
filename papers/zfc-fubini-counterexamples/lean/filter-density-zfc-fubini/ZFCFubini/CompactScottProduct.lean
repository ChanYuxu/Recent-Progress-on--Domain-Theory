import ZFCFubini.Foundations
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Order.ScottContinuity.Prod

/-!
The actual mixed-product continuity bridge used by the compact-Hausdorff
specialization of JMV2021 Lemma 3 / Theorem 4. The target has the intrinsic
Scott topology on the order product, not the product of the two Scott
topologies. This does not assert centrality or construct a valuation monad.
-/

set_option autoImplicit false
open Set Topology TopologicalSpace
open scoped Topology
universe u v w

namespace ZFCFubini

theorem scott_pair_right_continuous {D : Type v} {E : Type w}
    [Preorder D] [Preorder E] (e : E) :
    Continuous (fun d : WithScott D => WithScott.toScott (WithScott.ofScott d, e)) := by
  exact (scott_continuous_iff (fun d : D => (d, e))).mp
    (ScottContinuous.id.prodMk (ScottContinuous.const e))

/-- Compact universal quantification of ordinary slices is Scott-open in the
other coordinate. Its inaccessibility uses a finite directed subcover. -/
theorem compact_forall_scott_isOpen {X : Type u} [TopologicalSpace X]
    {D : Type v} {E : Type w} [Preorder D] [Preorder E]
    (f : X → WithScott D) (hf : Continuous f)
    {O : Set (WithScott (D × E))} (hO : IsOpen O)
    {K : Set X} (hK : IsCompact K) :
    IsOpen {e : WithScott E | ∀ x ∈ K,
      WithScott.toScott (WithScott.ofScott (f x), WithScott.ofScott e) ∈ O} := by
  have hup : IsUpperSet O := IsScott.isUpperSet_of_isOpen (D := univ) hO
  have hacc : DirSupInaccOn univ O :=
    (IsScott.isOpen_iff_isUpperSet_and_dirSupInaccOn (D := univ)).mp hO |>.2
  apply (IsScott.isOpen_iff_isUpperSet_and_dirSupInaccOn (D := univ)).mpr
  constructor
  · intro e e' hee' he x hx
    exact hup (show (WithScott.ofScott (f x), WithScott.ofScott e) ≤
      (WithScott.ofScott (f x), WithScott.ofScott e') from ⟨le_rfl, hee'⟩) (he x hx)
  · intro A _ hn hd e he heK
    letI : Nonempty A := hn.to_subtype
    let U : A → Set X := fun a =>
      {x | WithScott.toScott (WithScott.ofScott (f x), WithScott.ofScott a.val) ∈ O}
    have hUo (a : A) : IsOpen (U a) :=
      hO.preimage ((scott_pair_right_continuous (WithScott.ofScott a.val)).comp hf)
    have hUdir : Directed (· ⊆ ·) U := by
      intro a b
      obtain ⟨c, hc, hac, hbc⟩ := hd a.val a.property b.val b.property
      refine ⟨⟨c, hc⟩, ?_, ?_⟩
      · intro x hx
        exact hup (show (WithScott.ofScott (f x), WithScott.ofScott a.val) ≤
          (WithScott.ofScott (f x), WithScott.ofScott c) from ⟨le_rfl, hac⟩) hx
      · intro x hx
        exact hup (show (WithScott.ofScott (f x), WithScott.ofScott b.val) ≤
          (WithScott.ofScott (f x), WithScott.ofScott c) from ⟨le_rfl, hbc⟩) hx
    have hcover : K ⊆ ⋃ a : A, U a := by
      intro x hx
      let φ : WithScott E → WithScott (D × E) := fun a =>
        WithScott.toScott (WithScott.ofScott (f x), WithScott.ofScott a)
      have hφ : ScottContinuous φ :=
        (ScottContinuous.const (WithScott.ofScott (f x))).prodMk ScottContinuous.id
      have hlub : IsLUB (φ '' A) (φ e) := hφ hn hd he
      obtain ⟨z, ⟨a, ha, rfl⟩, hza⟩ := hacc (mem_univ _) (hn.image φ)
        (DirectedOn.mono_comp hφ.monotone hd) hlub (heK x hx)
      exact mem_iUnion.mpr ⟨⟨a, ha⟩, hza⟩
    obtain ⟨a, haK⟩ := hK.elim_directed_cover U hUo hcover hUdir
    exact ⟨a.val, a.property, haK⟩

/-- A locally compact ordinary parameter space admits the mixed product lift
to the intrinsic Scott topology of the coordinatewise order product. -/
theorem locallyCompact_scott_prod_continuous {X : Type u} [TopologicalSpace X]
    [LocallyCompactSpace X] {D : Type v} {E : Type w} [Preorder D] [Preorder E]
    (f : X → WithScott D) (hf : Continuous f) :
    Continuous (fun z : X × WithScott E =>
      WithScott.toScott (WithScott.ofScott (f z.1), WithScott.ofScott z.2)) := by
  apply continuous_def.mpr
  intro O hO
  apply isOpen_prod_iff.mpr
  intro x e hxe
  let A : Set X :=
    {y | WithScott.toScott (WithScott.ofScott (f y), WithScott.ofScott e) ∈ O}
  have hAo : IsOpen A :=
    hO.preimage ((scott_pair_right_continuous (WithScott.ofScott e)).comp hf)
  obtain ⟨K, hK, hxK, hKA⟩ := exists_compact_subset hAo hxe
  let V : Set (WithScott E) := {e' | ∀ y ∈ K,
    WithScott.toScott (WithScott.ofScott (f y), WithScott.ofScott e') ∈ O}
  have hVo : IsOpen V := compact_forall_scott_isOpen f hf hO hK
  refine ⟨interior K, V, isOpen_interior, hVo, hxK, hKA, ?_⟩
  rintro ⟨y, e'⟩ ⟨hy, he'⟩
  exact he' y (interior_subset hy)

/-- The compact Hausdorff case actually needed for the source maps G_M. No
dcpo-existence or centrality conclusion is stored as an assumption. -/
theorem compact_scott_prod_continuous {X : Type u} [TopologicalSpace X]
    [CompactSpace X] [T2Space X] {D : Type v} {E : Type w} [Preorder D] [Preorder E]
    (f : X → WithScott D) (hf : Continuous f) :
    Continuous (fun z : X × WithScott E =>
      WithScott.toScott (WithScott.ofScott (f z.1), WithScott.ofScott z.2)) :=
  locallyCompact_scott_prod_continuous f hf

end ZFCFubini
