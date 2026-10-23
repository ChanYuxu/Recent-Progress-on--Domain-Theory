import ZFCFubini.Foundations
import Mathlib.Topology.Bases

/-!
Exact event stabilization by the manuscript's closed-union/countable-dense-set
proof. Generic countably bounded indexing is instantiated later by the actual
null-set collection. No arbitrary-directed valuation conclusion is assumed.
Elementary intersection/common-index helpers are adapted from
CHFubini/EventStabilization.lean (SHA256
8495542ebf3ef5c9361c0303ee33d4077ee7de97323230ae7ec8d50be85d90ac).
-/

set_option autoImplicit false
open Set TopologicalSpace
universe u v w z
namespace ZFCFubini

def CountablyBounded (I : Type u) [LE I] : Prop :=
  ∀ A : Set I, A.Countable → ∃ i : I, ∀ j ∈ A, j ≤ i

theorem antitone_isOpen_eventually_constant
    {I : Type u} [Preorder I] (hI : CountablyBounded I)
    {X : Type v} [TopologicalSpace X] [SecondCountableTopology X]
    (G : I → Set X) (hG : Antitone G) (ho : ∀ i, IsOpen (G i)) :
    ∃ σ : I, ∀ β : I, σ ≤ β → G β = G σ := by
  classical
  let C : Set X := ⋃ i, (G i)ᶜ
  obtain ⟨D, hDc, hDd⟩ := exists_countable_dense C
  have hStage : ∀ x : D, ∃ i : I, x.val.val ∉ G i := by
    intro x
    exact mem_iUnion.mp x.val.property
  let stage : D → I := fun x => (hStage x).choose
  have hstage (x : D) : x.val.val ∉ G (stage x) := (hStage x).choose_spec
  letI : Countable D := hDc.to_subtype
  obtain ⟨σ, hσ⟩ := hI (range stage) (countable_range stage)
  have hDsub : Subtype.val '' D ⊆ (G σ)ᶜ := by
    rintro x ⟨d, hd, rfl⟩
    exact fun hx => hstage ⟨d, hd⟩ (hG (hσ _ (mem_range_self ⟨d, hd⟩)) hx)
  have hCsub : C ⊆ (G σ)ᶜ := by
    intro x hx
    have hcl : x ∈ closure (Subtype.val '' D) :=
      (Topology.IsEmbedding.subtypeVal.isInducing.dense_iff.mp hDd) ⟨x, hx⟩
    exact (ho σ).isClosed_compl.closure_subset_iff.mpr hDsub hcl
  refine ⟨σ, fun β hβ => Subset.antisymm (hG hβ) ?_⟩
  intro x hx
  by_contra hn
  exact hCsub (mem_iUnion.mpr ⟨β, hn⟩) hx

def limitPreimage {I : Type u} {X : Type v} {Y : Type w}
    (F : I → X → Y) (H : Set Y) : Set X := ⋂ i, F i ⁻¹' H

theorem limitPreimage_mono {I : Type u} {X : Type v} {Y : Type w}
    (F : I → X → Y) : Monotone (limitPreimage F) := by
  intro H K hHK x hx
  exact mem_iInter.mpr (fun i => hHK (mem_iInter.mp hx i))

@[simp] theorem limitPreimage_empty {I : Type u} [Nonempty I]
    {X : Type v} {Y : Type w} (F : I → X → Y) : limitPreimage F ∅ = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨i⟩ := ‹Nonempty I›
  exact mem_iInter.mp hx i

@[simp] theorem limitPreimage_univ {I : Type u} {X : Type v} {Y : Type w}
    (F : I → X → Y) : limitPreimage F univ = univ := by simp [limitPreimage]

theorem limitPreimage_inter {I : Type u} {X : Type v} {Y : Type w}
    (F : I → X → Y) (H K : Set Y) :
    limitPreimage F (H ∩ K) = limitPreimage F H ∩ limitPreimage F K := by
  ext x
  simp only [limitPreimage, mem_iInter, mem_preimage, mem_inter_iff]
  exact forall_and

theorem limitPreimage_eq_at_stable_stage
    {I : Type u} [SemilatticeSup I] {X : Type v} {Y : Type w}
    (F : I → X → Y) (H : Set Y)
    (ha : Antitone (fun i => F i ⁻¹' H)) {σ : I}
    (hσ : ∀ i, σ ≤ i → F i ⁻¹' H = F σ ⁻¹' H) :
    limitPreimage F H = F σ ⁻¹' H := by
  apply Subset.antisymm (iInter_subset _ σ)
  intro x hx
  apply mem_iInter.mpr
  intro i
  have hx' : x ∈ F (σ ⊔ i) ⁻¹' H := (hσ _ le_sup_left).symm ▸ hx
  exact ha le_sup_right hx'

theorem limitPreimage_eventually_eq
    {I : Type u} [SemilatticeSup I] (hI : CountablyBounded I)
    {X : Type v} [TopologicalSpace X] [SecondCountableTopology X]
    {Y : Type w} (F : I → X → Y) (H : Set Y)
    (ha : Antitone (fun i => F i ⁻¹' H))
    (ho : ∀ i, IsOpen (F i ⁻¹' H)) :
    ∃ σ : I, ∀ i, σ ≤ i → F i ⁻¹' H = limitPreimage F H := by
  obtain ⟨σ, hσ⟩ := antitone_isOpen_eventually_constant hI _ ha ho
  refine ⟨σ, fun i hi => ?_⟩
  rw [hσ i hi, limitPreimage_eq_at_stable_stage F H ha hσ]

theorem limitPreimage_isOpen
    {I : Type u} [SemilatticeSup I] (hI : CountablyBounded I)
    {X : Type v} [TopologicalSpace X] [SecondCountableTopology X]
    {Y : Type w} (F : I → X → Y) (H : Set Y)
    (ha : Antitone (fun i => F i ⁻¹' H))
    (ho : ∀ i, IsOpen (F i ⁻¹' H)) : IsOpen (limitPreimage F H) := by
  obtain ⟨σ, hσ⟩ := limitPreimage_eventually_eq hI F H ha ho
  rw [← hσ σ le_rfl]
  exact ho σ

theorem limitPreimage_countable_common_stage
    {I : Type u} [SemilatticeSup I] (hI : CountablyBounded I)
    {X : Type v} [TopologicalSpace X] [SecondCountableTopology X]
    {Y : Type w} {J : Type z} [Countable J]
    (F : I → X → Y) (H : J → Set Y)
    (ha : ∀ j, Antitone (fun i => F i ⁻¹' H j))
    (ho : ∀ j i, IsOpen (F i ⁻¹' H j)) :
    ∃ σ : I, ∀ j, limitPreimage F (H j) = F σ ⁻¹' H j := by
  classical
  have he := fun j => limitPreimage_eventually_eq hI F (H j) (ha j) (ho j)
  let stage : J → I := fun j => (he j).choose
  obtain ⟨σ, hσ⟩ := hI (range stage) (countable_range stage)
  exact ⟨σ, fun j => ((he j).choose_spec σ (hσ _ (mem_range_self j))).symm⟩

theorem limitPreimage_iUnion
    {I : Type u} [SemilatticeSup I] (hI : CountablyBounded I)
    {X : Type v} [TopologicalSpace X] [SecondCountableTopology X]
    {Y : Type w} {J : Type z} [Countable J]
    (F : I → X → Y) (H : J → Set Y)
    (ha : ∀ j, Antitone (fun i => F i ⁻¹' H j))
    (ho : ∀ j i, IsOpen (F i ⁻¹' H j)) :
    limitPreimage F (⋃ j, H j) = ⋃ j, limitPreimage F (H j) := by
  obtain ⟨σ, hσ⟩ := limitPreimage_countable_common_stage hI F H ha ho
  apply Subset.antisymm
  · intro x hx
    obtain ⟨j, hj⟩ := mem_iUnion.mp (mem_iInter.mp hx σ)
    exact mem_iUnion.mpr ⟨j, (hσ j).symm ▸ hj⟩
  · intro x hx
    obtain ⟨j, hj⟩ := mem_iUnion.mp hx
    exact limitPreimage_mono F (subset_iUnion H j) hj

theorem limitPreimage_union
    {I : Type u} [SemilatticeSup I] (hI : CountablyBounded I)
    {X : Type v} [TopologicalSpace X] [SecondCountableTopology X]
    {Y : Type w} (F : I → X → Y) (H K : Set Y)
    (haH : Antitone (fun i => F i ⁻¹' H))
    (haK : Antitone (fun i => F i ⁻¹' K))
    (hoH : ∀ i, IsOpen (F i ⁻¹' H))
    (hoK : ∀ i, IsOpen (F i ⁻¹' K)) :
    limitPreimage F (H ∪ K) = limitPreimage F H ∪ limitPreimage F K := by
  have hcond : (fun b : Bool => limitPreimage F (cond b H K)) =
      (fun b : Bool => cond b (limitPreimage F H) (limitPreimage F K)) := by
    funext b
    cases b <;> rfl
  calc
    limitPreimage F (H ∪ K) = limitPreimage F (⋃ b : Bool, cond b H K) :=
      congrArg (limitPreimage F) union_eq_iUnion
    _ = ⋃ b : Bool, limitPreimage F (cond b H K) := by
      apply limitPreimage_iUnion hI
      · intro b
        cases b <;> assumption
      · intro b
        cases b <;> assumption
    _ = limitPreimage F H ∪ limitPreimage F K := by rw [hcond, ← union_eq_iUnion]

end ZFCFubini
