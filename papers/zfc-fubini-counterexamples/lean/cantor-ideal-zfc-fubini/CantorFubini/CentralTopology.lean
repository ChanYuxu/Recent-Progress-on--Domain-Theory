import CantorFubini.ScottBasics
import CantorFubini.PaperIntegral
import Mathlib.Topology.Separation.Profinite
import Mathlib.Topology.LocallyConstant.Basic

/-!
New compact-parameter topology arguments for source Remark 6.5.
The proof specializes the compact-neighborhood argument behind Lemma 3 of
Jia--Mislove--Zamdzhiev, CALCO 2021, to compact Hausdorff zero-dimensional
parameters. No product-Scott/product-topology identification is assumed.
-/

set_option autoImplicit false
open Set Topology TopologicalSpace MeasureTheory
universe u v w
namespace CantorFubini

section CompactSections
variable {X : Type u} [TopologicalSpace X]
variable {D : Type v} [PartialOrder D] {E : Type w} [PartialOrder E]
variable (f : X → WithScott D) (hf : Continuous f)
variable (h : D × E → UnitInterval) (hh : ScottContinuous h)

include hf hh in
theorem parameter_section_isOpen (e : E) (a : ℝ) :
    IsOpen {x : X | a < (h (WithScott.ofScott (f x), e)).val} := by
  have hs : ScottContinuous (fun d : D => h (d, e)) :=
    (ScottContinuous.id.prodMk (ScottContinuous.const e)).comp hh
  exact (unit_scott_isRealLSC hs a).preimage hf

include hh in
theorem partner_section_isOpen (d : D) (a : ℝ) :
    IsOpen {e : WithScott E | a < (h (d, WithScott.ofScott e)).val} := by
  have hs : ScottContinuous (fun e : E => h (d, e)) :=
    ((ScottContinuous.const d).prodMk ScottContinuous.id).comp hh
  exact unit_scott_isRealLSC hs a

include hf hh in
/-- Compact universal sections are Scott-open in an arbitrary partner dcpo.
This is the compact finite-subcover step that makes the topology bridge valid. -/
theorem compact_section_isOpen (K : Set X) (hK : IsCompact K) (a : ℝ) :
    IsOpen {e : WithScott E |
      ∀ x ∈ K, a < (h (WithScott.ofScott (f x), WithScott.ofScott e)).val} := by
  apply (scott_isOpen_iff {e : E |
    ∀ x ∈ K, a < (h (WithScott.ofScott (f x), e)).val}).mpr
  constructor
  · intro e e' hee' he x hx
    exact (he x hx).trans_le (show (h (WithScott.ofScott (f x), e)).val ≤
      (h (WithScott.ofScott (f x), e')).val from hh.monotone ⟨le_rfl, hee'⟩)
  · intro A hn hd e hlub heK
    classical
    letI : Nonempty A := hn.to_subtype
    let O : A → Set X := fun d => {x | a < (h (WithScott.ofScott (f x), d.val)).val}
    have hOo : ∀ d : A, IsOpen (O d) :=
      fun d => parameter_section_isOpen f hf h hh d.val a
    have hcover : K ⊆ ⋃ d : A, O d := by
      intro x hx
      have hacc := ((scott_isOpen_iff {d : E |
        a < (h (WithScott.ofScott (f x), d)).val}).mp
        (partner_section_isOpen h hh (WithScott.ofScott (f x)) a)).2
      obtain ⟨d, hdA, hxd⟩ := hacc hn hd hlub (heK x hx)
      exact mem_iUnion.mpr ⟨⟨d, hdA⟩, hxd⟩
    have hdir : Directed (· ⊆ ·) O := by
      intro d d'
      obtain ⟨d'', hd'', hdd'', hd'd''⟩ := hd d.val d.property d'.val d'.property
      refine ⟨⟨d'', hd''⟩, ?_, ?_⟩
      · intro x hx
        exact hx.trans_le (show (h (WithScott.ofScott (f x), d.val)).val ≤
          (h (WithScott.ofScott (f x), d'')).val from hh.monotone ⟨le_rfl, hdd''⟩)
      · intro x hx
        exact hx.trans_le (show (h (WithScott.ofScott (f x), d'.val)).val ≤
          (h (WithScott.ofScott (f x), d'')).val from hh.monotone ⟨le_rfl, hd'd''⟩)
    obtain ⟨d, hdK⟩ := hK.elim_directed_cover O hOo hcover hdir
    exact ⟨d.val, d.property, hdK⟩

end CompactSections

section ProfiniteParameters
variable {X : Type u} [TopologicalSpace X] [CompactSpace X] [T2Space X]
variable [TotallyDisconnectedSpace X]
variable {D : Type v} [PartialOrder D] {E : Type w} [PartialOrder E]
variable (f : X → WithScott D) (hf : Continuous f)
variable (h : D × E → UnitInterval) (hh : ScottContinuous h)

include hf hh in
/-- A strict observation at one point admits a compact clopen rectangle
inside the pulled-back observation, with the partner carrying its Scott
topology. This does not assume ordinary-product continuity of `h`. -/
theorem clopen_rectangle_of_strict {x : X} {e : E} {a : ℝ}
    (ha : a < (h (WithScott.ofScott (f x), e)).val) :
    ∃ C : Set X, IsClopen C ∧ x ∈ C ∧
      ∃ V : ScottOpens E, WithScott.toScott e ∈ V ∧
        ∀ t ∈ C, ∀ y : E, WithScott.toScott y ∈ V →
          a < (h (WithScott.ofScott (f t), y)).val := by
  obtain ⟨C, hCc, hxC, hC⟩ := compact_exists_isClopen_in_isOpen
    (parameter_section_isOpen f hf h hh e a) ha
  let V : ScottOpens E := ⟨{y | ∀ t ∈ C,
    a < (h (WithScott.ofScott (f t), WithScott.ofScott y)).val},
    compact_section_isOpen f hf h hh C hCc.isClosed.isCompact a⟩
  exact ⟨C, hCc, hxC, V, hC, fun t ht y hy => hy t ht⟩

include hf hh in
/-- The compact parameter pullback is LSC for the ordinary product of the
parameter topology and the full partner Scott topology. -/
theorem compact_parameter_joint_isRealLSC :
    IsRealLSC (fun z : X × WithScott E =>
      (h (WithScott.ofScott (f z.1), WithScott.ofScott z.2)).val) := by
  intro a
  apply isOpen_prod_iff.mpr
  intro x e he
  obtain ⟨C, hCc, hxC, V, heV, hCV⟩ :=
    clopen_rectangle_of_strict f hf h hh he
  exact ⟨C, V, hCc.isOpen, V.isOpen, hxC, heV,
    fun z hz => hCV z.1 hz.1 (WithScott.ofScott z.2) hz.2⟩

end ProfiniteParameters
end CantorFubini
