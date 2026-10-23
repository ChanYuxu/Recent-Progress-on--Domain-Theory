import Mathlib.Topology.Bases
import Mathlib.Topology.Baire.Lemmas
import Mathlib.Topology.GDelta.Basic
import Mathlib.SetTheory.Cardinal.Regular

/-!
Pure candidate lemmas for manuscript `lem:omega1-stabilization`, the event-map
part of `lem:psi-countable`, and the dense-carrier step of `prop:null-defect`.

These are helper statements, not source-facing coverage declarations. In
particular, the carrier theorem below does not prove existence of the carriers
or their stabilization; those remain separate construction obligations.
-/

open Set TopologicalSpace

namespace CHFubini

universe u v w z

/-- Every countable set of stages has an upper bound. Unlike ordinary
directedness, this includes arbitrary countable sets, not just finite sets. -/
def CountablyBounded (I : Type u) [LE I] : Prop :=
  ∀ A : Set I, A.Countable → ∃ i : I, ∀ j ∈ A, j ≤ i

/-- A second-countable space has no genuinely changing antitone family of
open sets indexed by a countably bounded preorder. -/
theorem antitone_isOpen_eventually_constant
    {I : Type u} [Preorder I] (hI : CountablyBounded I)
    {X : Type v} [TopologicalSpace X] [SecondCountableTopology X]
    (G : I → Set X) (hG : Antitone G) (ho : ∀ i, IsOpen (G i)) :
    ∃ σ : I, ∀ β : I, σ ≤ β → G β = G σ := by
  classical
  let Bad := {b : countableBasis X // ∃ i : I, ¬(b.1 : Set X) ⊆ G i}
  let stage : Bad → I := fun b => Classical.choose b.2
  have hstage (b : Bad) : ¬(b.1.1 : Set X) ⊆ G (stage b) :=
    Classical.choose_spec b.2
  obtain ⟨σ, hσ⟩ := hI (range stage) (countable_range stage)
  refine ⟨σ, fun β hσβ => Subset.antisymm (hG hσβ) ?_⟩
  intro x hx
  obtain ⟨b, hb, hxb, hbG⟩ :=
    (isBasis_countableBasis X).exists_subset_of_mem_open hx (ho σ)
  by_contra hxbeta
  have hbad : ∃ i : I, ¬b ⊆ G i :=
    ⟨β, fun hbβ => hxbeta (hbβ hxb)⟩
  let bad : Bad := ⟨⟨b, hb⟩, hbad⟩
  exact hstage bad (hbG.trans (hG (hσ (stage bad) (mem_range_self bad))))

/-- The manuscript's countable-ordinal stage set, with no CH assumption. -/
abbrev OmegaOneStage := {β : Ordinal.{0} // β < Ordinal.omega 1}

theorem omegaOneStage_countablyBounded : CountablyBounded OmegaOneStage := by
  intro A hA
  letI : Countable A := hA.to_subtype
  let σ : Ordinal := ⨆ a : A, a.1.1
  have hσ : σ < Ordinal.omega 1 :=
    Ordinal.iSup_lt_omega_one (fun a => a.1.2)
  refine ⟨⟨σ, hσ⟩, fun β hβ => ?_⟩
  exact Ordinal.le_iSup (fun a : A => a.1.1) ⟨β, hβ⟩

/-- Source-exact mathematical content of `lem:omega1-stabilization`. -/
theorem omegaOne_open_stabilization
    {X : Type v} [TopologicalSpace X] [SecondCountableTopology X]
    (G : OmegaOneStage → Set X) (hG : Antitone G)
    (ho : ∀ β, IsOpen (G β)) :
    ∃ σ : OmegaOneStage, ∀ β : OmegaOneStage, σ ≤ β → G β = G σ :=
  antitone_isOpen_eventually_constant omegaOneStage_countablyBounded G hG ho

/-- Intersection of all stagewise events; this is the manuscript's `psi` once
the family of maps `F` has been instantiated. -/
def limitPreimage {I : Type u} {X : Type v} {Y : Type w}
    (F : I → X → Y) (H : Set Y) : Set X := ⋂ β, F β ⁻¹' H

theorem limitPreimage_mono {I : Type u} {X : Type v} {Y : Type w}
    (F : I → X → Y) : Monotone (limitPreimage F) := by
  intro H K hHK x hx
  exact mem_iInter.mpr (fun β => hHK (mem_iInter.mp hx β))

@[simp] theorem limitPreimage_empty {I : Type u} [Nonempty I]
    {X : Type v} {Y : Type w} (F : I → X → Y) :
    limitPreimage F ∅ = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨β⟩ := ‹Nonempty I›
  exact mem_iInter.mp hx β

@[simp] theorem limitPreimage_univ {I : Type u}
    {X : Type v} {Y : Type w} (F : I → X → Y) :
    limitPreimage F univ = univ := by
  simp [limitPreimage]

theorem limitPreimage_inter {I : Type u} {X : Type v} {Y : Type w}
    (F : I → X → Y) (H K : Set Y) :
    limitPreimage F (H ∩ K) = limitPreimage F H ∩ limitPreimage F K := by
  ext x
  simp only [limitPreimage, mem_iInter, mem_preimage, mem_inter_iff]
  exact forall_and

/-- Intersections are preserved without any stage-order or openness
assumptions. This is stronger than the finite-intersection assertion needed
in the manuscript and does not strengthen its hypotheses. -/
theorem limitPreimage_iInter {I : Type u} {X : Type v} {Y : Type w}
    {J : Type z} (F : I → X → Y) (H : J → Set Y) :
    limitPreimage F (⋂ j, H j) = ⋂ j, limitPreimage F (H j) := by
  ext x
  simp only [limitPreimage, mem_iInter, mem_preimage]
  exact forall_comm

/-- An antitone event family equals its full intersection from any
stabilization stage onwards. -/
theorem antitone_iInter_eq_of_eventually_constant
    {I : Type u} [SemilatticeSup I] {X : Type v}
    (G : I → Set X) (hG : Antitone G) {σ : I}
    (hσ : ∀ β : I, σ ≤ β → G β = G σ) :
    (⋂ β, G β) = G σ := by
  apply Subset.antisymm (iInter_subset G σ)
  intro x hx
  apply mem_iInter.mpr
  intro β
  have hx' : x ∈ G (σ ⊔ β) := (hσ _ le_sup_left).symm ▸ hx
  exact hG le_sup_right hx'

theorem limitPreimage_eq_at_stable_stage
    {I : Type u} [SemilatticeSup I] {X : Type v} {Y : Type w}
    (F : I → X → Y) (H : Set Y)
    (ha : Antitone (fun β => F β ⁻¹' H)) {σ : I}
    (hσ : ∀ β : I, σ ≤ β → F β ⁻¹' H = F σ ⁻¹' H) :
    limitPreimage F H = F σ ⁻¹' H :=
  antitone_iInter_eq_of_eventually_constant _ ha hσ

/-- The intersection event is open and is represented by one eventual stage. -/
theorem limitPreimage_isOpen
    {I : Type u} [SemilatticeSup I] (hI : CountablyBounded I)
    {X : Type v} [TopologicalSpace X] [SecondCountableTopology X]
    {Y : Type w} (F : I → X → Y) (H : Set Y)
    (ha : Antitone (fun β => F β ⁻¹' H))
    (ho : ∀ β, IsOpen (F β ⁻¹' H)) :
    IsOpen (limitPreimage F H) := by
  obtain ⟨σ, hσ⟩ := antitone_isOpen_eventually_constant hI _ ha ho
  rw [limitPreimage_eq_at_stable_stage F H ha hσ]
  exact ho σ

theorem limitPreimage_eventually_eq
    {I : Type u} [SemilatticeSup I] (hI : CountablyBounded I)
    {X : Type v} [TopologicalSpace X] [SecondCountableTopology X]
    {Y : Type w} (F : I → X → Y) (H : Set Y)
    (ha : Antitone (fun β => F β ⁻¹' H))
    (ho : ∀ β, IsOpen (F β ⁻¹' H)) :
    ∃ σ : I, ∀ β, σ ≤ β → F β ⁻¹' H = limitPreimage F H := by
  obtain ⟨σ, hσ⟩ := antitone_isOpen_eventually_constant hI _ ha ho
  refine ⟨σ, fun β hβ => ?_⟩
  rw [hσ β hβ, limitPreimage_eq_at_stable_stage F H ha hσ]

/-- Countably many events may be stabilized at one common stage. -/
theorem limitPreimage_countable_common_stage
    {I : Type u} [SemilatticeSup I] (hI : CountablyBounded I)
    {X : Type v} [TopologicalSpace X] [SecondCountableTopology X]
    {Y : Type w} {J : Type z} [Countable J]
    (F : I → X → Y) (H : J → Set Y)
    (ha : ∀ j, Antitone (fun β => F β ⁻¹' H j))
    (ho : ∀ j β, IsOpen (F β ⁻¹' H j)) :
    ∃ σ : I, ∀ j, limitPreimage F (H j) = F σ ⁻¹' H j := by
  classical
  have he (j : J) : ∃ σ : I, ∀ β, σ ≤ β → F β ⁻¹' H j = F σ ⁻¹' H j :=
    antitone_isOpen_eventually_constant hI _ (ha j) (ho j)
  let stage : J → I := fun j => Classical.choose (he j)
  obtain ⟨σ, hσ⟩ := hI (range stage) (countable_range stage)
  refine ⟨σ, fun j => ?_⟩
  have hsj := Classical.choose_spec (he j)
  have hjσ : stage j ≤ σ := hσ _ (mem_range_self j)
  calc
    limitPreimage F (H j) = F (stage j) ⁻¹' H j :=
      limitPreimage_eq_at_stable_stage F (H j) (ha j) hsj
    _ = F σ ⁻¹' H j := (hsj σ hjσ).symm

/-- Exact preservation of countable unions. No assumption of preservation of
arbitrary unions, no measure, and no valuation property is used. -/
theorem limitPreimage_iUnion
    {I : Type u} [SemilatticeSup I] (hI : CountablyBounded I)
    {X : Type v} [TopologicalSpace X] [SecondCountableTopology X]
    {Y : Type w} {J : Type z} [Countable J]
    (F : I → X → Y) (H : J → Set Y)
    (ha : ∀ j, Antitone (fun β => F β ⁻¹' H j))
    (ho : ∀ j β, IsOpen (F β ⁻¹' H j)) :
    limitPreimage F (⋃ j, H j) = ⋃ j, limitPreimage F (H j) := by
  obtain ⟨σ, hσ⟩ := limitPreimage_countable_common_stage hI F H ha ho
  apply Subset.antisymm
  · intro x hx
    have hxσ : F σ x ∈ ⋃ j, H j := mem_iInter.mp hx σ
    obtain ⟨j, hj⟩ := mem_iUnion.mp hxσ
    exact mem_iUnion.mpr ⟨j, (hσ j).symm ▸ hj⟩
  · intro x hx
    obtain ⟨j, hj⟩ := mem_iUnion.mp hx
    exact limitPreimage_mono F (subset_iUnion H j) hj

theorem limitPreimage_union
    {I : Type u} [SemilatticeSup I] (hI : CountablyBounded I)
    {X : Type v} [TopologicalSpace X] [SecondCountableTopology X]
    {Y : Type w} (F : I → X → Y) (H K : Set Y)
    (haH : Antitone (fun β => F β ⁻¹' H))
    (haK : Antitone (fun β => F β ⁻¹' K))
    (hoH : ∀ β, IsOpen (F β ⁻¹' H))
    (hoK : ∀ β, IsOpen (F β ⁻¹' K)) :
    limitPreimage F (H ∪ K) = limitPreimage F H ∪ limitPreimage F K := by
  have hcond : (fun b : Bool => limitPreimage F (cond b H K)) =
      (fun b : Bool => cond b (limitPreimage F H) (limitPreimage F K)) := by
    funext b
    cases b <;> rfl
  calc
    limitPreimage F (H ∪ K) =
        limitPreimage F (⋃ b : Bool, cond b H K) :=
      congrArg (limitPreimage F) union_eq_iUnion
    _ = ⋃ b : Bool, limitPreimage F (cond b H K) := by
      apply limitPreimage_iUnion hI
      · intro b
        cases b <;> assumption
      · intro b
        cases b <;> assumption
    _ = limitPreimage F H ∪ limitPreimage F K := by
      rw [hcond, ← union_eq_iUnion]

/-- The Baire step in the tail-block proof: if the tail difference is
countable and its incidence events are dense open, the two tail-union maps
agree on a dense G-delta. This is a statement about the actual union maps,
not an assumed equality package. -/
theorem tail_union_agreement_contains_dense_Gdelta
    {X : Type u} [TopologicalSpace X] [BaireSpace X]
    {A : Type v} {T₀ T C : Set A} (hT : T₀ = T ∪ C)
    (hC : C.Countable) (R : X → Set A)
    (ho : ∀ a ∈ C, IsOpen {s : X | a ∈ R s})
    (hd : ∀ a ∈ C, Dense {s : X | a ∈ R s}) :
    ∃ G : Set X, Dense G ∧ IsGδ G ∧
      G ⊆ {s : X | T ∪ R s = T₀ ∪ R s} := by
  refine ⟨⋂ a ∈ C, {s : X | a ∈ R s},
    dense_biInter_of_isOpen ho hC hd, IsGδ.biInter_of_isOpen hC ho, ?_⟩
  intro s hs
  have hCR : C ⊆ R s := fun a ha => mem_iInter.mp (mem_iInter.mp hs a) ha
  change T ∪ R s = T₀ ∪ R s
  rw [hT]
  apply Subset.antisymm
  · intro a ha
    rcases ha with ha | ha
    · exact Or.inl (Or.inl ha)
    · exact Or.inr ha
  · intro a ha
    rcases ha with (ha | ha) | ha
    · exact Or.inl ha
    · exact Or.inr (hCR ha)
    · exact Or.inr ha

/-- The topological core of the arbitrary-union null-defect argument.

`hstable` is only eventwise exact stabilization (proved above).
`hcarrier` asserts dense stagewise agreement on this fixed carrier, not the
desired arbitrary-union law. The later stage may depend on the test, while
the initial carrier stage is one fixed stage for all tests.
-/
theorem carrier_defect_empty
    {I : Type u} [SemilatticeSup I]
    {X : Type v} [TopologicalSpace X] {Y : Type w}
    {J : Type z} (F : I → X → Y) (H : J → Set Y) (D : Set X)
    (ho : ∀ β j, IsOpen (F β ⁻¹' H j))
    (hstable : ∀ j, ∃ σ : I, ∀ β, σ ≤ β →
      F β ⁻¹' H j = limitPreimage F (H j))
    (hcarrier : ∃ β₀ : I, ∀ β, β₀ ≤ β →
      Dense {s : D | F β s.1 = F β₀ s.1})
    (hD : D ⊆ limitPreimage F (⋃ j, H j) \ ⋃ j, limitPreimage F (H j)) :
    D = ∅ := by
  classical
  obtain ⟨β₀, hβ₀⟩ := hcarrier
  have htest (j : J) : ∀ s : D, F β₀ s.1 ∉ H j := by
    obtain ⟨σ, hσ⟩ := hstable j
    let β : I := β₀ ⊔ σ
    let U : Set D := {s | F β₀ s.1 ∈ H j}
    have hU : IsOpen U := (ho β₀ j).preimage continuous_subtype_val
    intro s hs
    obtain ⟨t, htU, htEq⟩ :=
      (hβ₀ β le_sup_left).inter_open_nonempty U hU ⟨s, hs⟩
    have htβ : t.1 ∈ F β ⁻¹' H j := by
      change F β t.1 ∈ H j
      rw [htEq]
      exact htU
    have htlim : t.1 ∈ limitPreimage F (H j) :=
      hσ β le_sup_right ▸ htβ
    exact (hD t.2).2 (mem_iUnion.mpr ⟨j, htlim⟩)
  apply eq_empty_iff_forall_notMem.mpr
  intro s hs
  have hsun : F β₀ s ∈ ⋃ j, H j := mem_iInter.mp (hD hs).1 β₀
  obtain ⟨j, hj⟩ := mem_iUnion.mp hsun
  exact htest j ⟨s, hs⟩ hj

end CHFubini

#print axioms CHFubini.omegaOne_open_stabilization
#print axioms CHFubini.limitPreimage_iUnion
#print axioms CHFubini.tail_union_agreement_contains_dense_Gdelta
#print axioms CHFubini.carrier_defect_empty

