import CHFubini.SourceMeasure
import CHFubini.SourceSmyth

/-!
Direct topological route to source `cor:product-topology-strict`, without an
external Fubini theorem: ordinary openness of incidence would make membership
evaluation jointly open, which produces compact neighborhoods in a Hausdorff
space. The actual source valuation is continuous and normalized, while all
actual source compacts are null; this rules out such neighborhoods.
-/

open Set Filter Topology TopologicalSpace MeasureTheory
open scoped Topology ENNReal

namespace CHFubini

universe u v

/-- The finite-open-cover formulation of `U` being way inside `V`. This is
only a local helper; no unproved corecompactness equivalence is used. -/
def OpenFiniteCover {X : Type u} [TopologicalSpace X] (U V : Opens X) : Prop :=
  ∀ S : Set (Opens X), V ≤ sSup S →
    ∃ F : Finset (Opens X), (F : Set (Opens X)) ⊆ S ∧ U ≤ sSup (F : Set (Opens X))

/-- A Scott neighborhood containing `V` whose members all contain `U` yields
the finite-cover relation, by actual directed finite joins. -/
theorem openFiniteCover_of_scott_neighborhood
    {X : Type u} [TopologicalSpace X] (U V : Opens X)
    (H : Opens (WithScott (Opens X))) (hVH : WithScott.toScott V ∈ H)
    (hUH : ∀ W : Opens X, WithScott.toScott W ∈ H → U ≤ W) :
    OpenFiniteCover U V := by
  classical
  intro S hVS
  let D : Set (Opens X) :=
    {W | ∃ F : Finset (Opens X), (F : Set (Opens X)) ⊆ S ∧ W = sSup (F : Set (Opens X))}
  have hDn : D.Nonempty := ⟨⊥, ∅, by simp, by simp⟩
  have hDd : DirectedOn (· ≤ ·) D := by
    rintro W ⟨F, hFS, rfl⟩ Z ⟨G, hGS, rfl⟩
    refine ⟨sSup ((F ∪ G : Finset (Opens X)) : Set (Opens X)),
      ⟨F ∪ G, ?_, rfl⟩, ?_, ?_⟩
    · intro A hA
      rcases Finset.mem_union.mp hA with hA | hA
      · exact hFS hA
      · exact hGS hA
    · exact sSup_le_sSup (fun A hA => Finset.mem_union_left G hA)
    · exact sSup_le_sSup (fun A hA => Finset.mem_union_right F hA)
  have hDLub : IsLUB D (sSup S) := by
    refine ⟨?_, ?_⟩
    · rintro W ⟨F, hFS, rfl⟩
      exact sSup_le_sSup hFS
    · intro W hW
      apply sSup_le
      intro Z hZS
      have hZD : Z ∈ D := ⟨{Z}, by simpa, by simp⟩
      exact hW hZD
  have hup : IsUpperSet (H : Set (WithScott (Opens X))) :=
    IsScott.isUpperSet_of_isOpen (D := univ) H.isOpen
  have hacc : DirSupInaccOn univ (H : Set (WithScott (Opens X))) :=
    (IsScott.isOpen_iff_isUpperSet_and_dirSupInaccOn (D := univ)).mp H.isOpen |>.2
  have hSH : WithScott.toScott (sSup S) ∈ H := hup hVS hVH
  obtain ⟨W, ⟨F, hFS, hWF⟩, hWH⟩ := hacc (mem_univ _) hDn hDd hDLub hSH
  exact ⟨F, hFS, hWF ▸ hUH W hWH⟩

def opensMembership {X : Type u} [TopologicalSpace X] :
    Set (X × WithScott (Opens X)) := {p | p.1 ∈ WithScott.ofScott p.2}

/-- Jointly open membership evaluation supplies way-inside neighborhoods. -/
theorem openFiniteCover_neighborhood_of_membership_open
    {X : Type u} [TopologicalSpace X]
    (hE : IsOpen (@opensMembership X _)) (x : X) (V : Opens X) (hxV : x ∈ V) :
    ∃ U : Opens X, x ∈ U ∧ OpenFiniteCover U V := by
  obtain ⟨U, H, hUo, hHo, hxU, hVH, hrect⟩ :=
    isOpen_prod_iff.mp hE x (WithScott.toScott V) hxV
  refine ⟨⟨U, hUo⟩, hxU,
    openFiniteCover_of_scott_neighborhood ⟨U, hUo⟩ V ⟨H, hHo⟩ hVH ?_⟩
  intro W hWH y hyU
  exact hrect (show (y, WithScott.toScott W) ∈ U ×ˢ H from ⟨hyU, hWH⟩)

/-- Hausdorff separation proves the closure containment needed in the direct
corecompact-to-compact-neighborhood argument. -/
theorem OpenFiniteCover.closure_subset
    {X : Type u} [TopologicalSpace X] [T2Space X]
    {U V : Opens X} (hUV : OpenFiniteCover U V) : closure (U : Set X) ⊆ V := by
  classical
  intro p hp
  by_contra hpV
  let S : Set (Opens X) := {W | p ∉ closure (W : Set X)}
  have hcover : V ≤ sSup S := by
    intro y hy
    have hyp : y ≠ p := fun h => hpV (h ▸ hy)
    obtain ⟨A, B, hAo, hBo, hyA, hpB, hdis⟩ := t2_separation hyp
    have hpA : p ∉ closure A :=
      fun h => Set.disjoint_left.mp (hdis.closure_left hBo) h hpB
    exact Opens.mem_sSup.mpr ⟨⟨A, hAo⟩, hpA, hyA⟩
  obtain ⟨F, hFS, hUF⟩ := hUV S hcover
  have hUsub : (U : Set X) ⊆ ⋃ W ∈ F, closure (W : Set X) := by
    intro x hx
    obtain ⟨W, hWF, hxW⟩ := Opens.mem_sSup.mp (hUF hx)
    exact mem_iUnion₂.mpr ⟨W, hWF, subset_closure hxW⟩
  have hcl : closure (U : Set X) ⊆ ⋃ W ∈ F, closure (W : Set X) :=
    closure_minimal hUsub (isClosed_biUnion_finset (fun _ _ => isClosed_closure))
  obtain ⟨W, hWF, hpW⟩ := mem_iUnion₂.mp (hcl hp)
  exact hFS hWF hpW

/-- Two levels of finite-cover containment yield a genuinely compact
closure; no regularity of the original Hausdorff space is assumed. -/
theorem isCompact_closure_of_openFiniteCover
    {X : Type u} [TopologicalSpace X] [T2Space X]
    {U₀ U₁ : Opens X} (h01 : OpenFiniteCover U₀ U₁) (h1 : OpenFiniteCover U₁ ⊤) :
    IsCompact (closure (U₀ : Set X)) := by
  classical
  apply isCompact_of_finite_subcover
  intro ι O hO hcover
  let bundled : ι → Opens X := fun i => ⟨O i, hO i⟩
  let C : Opens X := ⟨(closure (U₀ : Set X))ᶜ, isClosed_closure.isOpen_compl⟩
  let S : Set (Opens X) := range bundled ∪ {C}
  have hS : (⊤ : Opens X) ≤ sSup S := by
    intro x _
    by_cases hx : x ∈ closure (U₀ : Set X)
    · obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover hx)
      exact Opens.mem_sSup.mpr ⟨bundled i, Or.inl (mem_range_self i), hi⟩
    · exact Opens.mem_sSup.mpr ⟨C, Or.inr rfl, hx⟩
  obtain ⟨F, hFS, hU₁F⟩ := h1 S hS
  let G : Finset (Opens X) := F.filter (fun W => W ∈ range bundled)
  let pick : G → ι := fun W => Classical.choose (Finset.mem_filter.mp W.2).2
  have hpick (W : G) : bundled (pick W) = W.1 :=
    Classical.choose_spec (Finset.mem_filter.mp W.2).2
  refine ⟨G.attach.image pick, fun x hx => ?_⟩
  obtain ⟨W, hWF, hxW⟩ := Opens.mem_sSup.mp (hU₁F (h01.closure_subset hx))
  have hWrange : W ∈ range bundled := by
    rcases hFS hWF with h | h
    · exact h
    · have hWC : W = C := h
      subst W
      exact False.elim (hxW hx)
  have hWG : W ∈ G := Finset.mem_filter.mpr ⟨hWF, hWrange⟩
  let w : G := ⟨W, hWG⟩
  refine mem_iUnion₂.mpr ⟨pick w,
    Finset.mem_image.mpr ⟨w, Finset.mem_attach _ _, rfl⟩, ?_⟩
  have h := hpick w
  change x ∈ bundled (pick w)
  rw [h]
  exact hxW

/-- Explicit compact neighborhoods forced by open membership evaluation. -/
theorem compact_neighborhood_of_membership_open
    {X : Type u} [TopologicalSpace X] [T2Space X]
    (hE : IsOpen (@opensMembership X _)) (x : X) :
    ∃ U : Opens X, x ∈ U ∧ IsCompact (closure (U : Set X)) := by
  obtain ⟨U₁, hx₁, h1⟩ := openFiniteCover_neighborhood_of_membership_open hE x ⊤ trivial
  obtain ⟨U₀, hx₀, h01⟩ := openFiniteCover_neighborhood_of_membership_open hE x U₁ hx₁
  exact ⟨U₀, hx₀, isCompact_closure_of_openFiniteCover h01 h1⟩

/-- A normalized continuous valuation agreeing with a measure that vanishes
on every compact forbids jointly open membership evaluation. The argument
uses the valuation's actual arbitrary-directed-supremum continuity. -/
theorem membership_not_open_of_probability_compact_null
    {X : Type u} [TopologicalSpace X] [T2Space X] [MeasurableSpace X]
    (m : Measure X) (α : Valuation X) (hαprob : α.Probability)
    (hαmass : ∀ U : Opens X, α U = m (U : Set X))
    (hcompact : ∀ K : Set X, IsCompact K → m K = 0) :
    ¬IsOpen (@opensMembership X _) := by
  classical
  intro hE
  let S : Set (Opens X) := {U | ∃ K : Set X, IsCompact K ∧ (U : Set X) ⊆ K}
  have hSn : S.Nonempty := ⟨⊥, ∅, isCompact_empty, by simp⟩
  have hSd : DirectedOn (· ≤ ·) S := by
    rintro U ⟨K, hK, hUK⟩ V ⟨L, hL, hVL⟩
    refine ⟨U ⊔ V, ⟨K ∪ L, hK.union hL, ?_⟩, le_sup_left, le_sup_right⟩
    intro x hx
    rcases hx with hx | hx
    · exact Or.inl (hUK hx)
    · exact Or.inr (hVL hx)
  have hStop : sSup S = (⊤ : Opens X) := by
    apply top_unique
    intro x _
    obtain ⟨U, hxU, hUc⟩ := compact_neighborhood_of_membership_open hE x
    exact Opens.mem_sSup.mpr ⟨U, ⟨closure (U : Set X), hUc, subset_closure⟩, hxU⟩
  have hzero : ∀ U ∈ S, α U = 0 := by
    rintro U ⟨K, hK, hUK⟩
    rw [hαmass]
    exact measure_mono_null hUK (hcompact K hK)
  have hαzero : α ⊤ = 0 := by
    rw [← hStop, α.map_sSup hSn hSd]
    apply le_antisymm
    · exact iSup_le (fun U => iSup_le (fun hUS => (hzero U hUS).le))
    · exact bot_le
  have h : (1 : ℝ≥0∞) = 0 := hαprob.symm.trans hαzero
  exact one_ne_zero h

/-- The source's same incidence witness, now regarded as a subset of the
ordinary product of its two full Scott spaces. -/
def ordinaryIncidence {X : Type u} [TopologicalSpace X] [T2Space X] :
    Set (WithScott (Smyth X) × WithScott (Opens X)) :=
  {p | WithScott.toScott (WithScott.ofScott p.1, WithScott.ofScott p.2) ∈ incidenceOpen}

/-- Pullback by the specified singleton map identifies ordinary-product
incidence openness with the forbidden jointly open membership event. -/
theorem incidence_not_product_open_of_compact_null
    {X : Type u} [TopologicalSpace X] [T2Space X] [MeasurableSpace X]
    (hSingleton : Continuous (@singletonMap X _))
    (m : Measure X) (α : Valuation X) (hαprob : α.Probability)
    (hαmass : ∀ U : Opens X, α U = m (U : Set X))
    (hcompact : ∀ K : Set X, IsCompact K → m K = 0) :
    ¬IsOpen (@ordinaryIncidence X _ _) := by
  intro hW
  have hcont : Continuous (fun p : X × WithScott (Opens X) => (singletonMap p.1, p.2)) :=
    (hSingleton.comp continuous_fst).prodMk continuous_snd
  have hpre : (fun p : X × WithScott (Opens X) => (singletonMap p.1, p.2)) ⁻¹'
      ordinaryIncidence = opensMembership := by
    ext p
    change ({p.1} : Set X) ⊆ ((WithScott.ofScott p.2 : Opens X) : Set X) ↔
      p.1 ∈ WithScott.ofScott p.2
    exact singleton_subset_iff
  have hE : IsOpen (@opensMembership X _) := by
    rw [← hpre]
    exact hW.preimage hcont
  exact membership_not_open_of_probability_compact_null m α hαprob hαmass hcompact hE

/-- Source `cor:product-topology-strict`, for the actual generated source,
actual source valuation, actual singleton map and actual incidence witness.
The CH existence theorem supplies these already-proved construction data. -/
theorem source_incidence_not_product_open
    {T : Type u} [TopologicalSpace T] [T2Space T] [SecondCountableTopology T]
    [MeasurableSpace T] [BorelSpace T]
    (ν : Measure T) [NoAtoms ν] [IsProbabilityMeasure ν] [Measure.InnerRegular ν]
    (a : OmegaOneStage → T) (m : Measure (SourcePoint a))
    (hm : ∀ B : Set T, MeasurableSet B → m (SourcePoint.val ⁻¹' B) = ν B) :
    ¬IsOpen (@ordinaryIncidence (SourcePoint a) _ _) := by
  apply incidence_not_product_open_of_compact_null (sourceSingleton_continuous a) m
    (sourceValuation ν a m hm) (sourceValuation_probability ν a m hm)
  · exact fun U => sourceValuation_apply ν a m hm U
  · exact fun K hK => sourceMeasure_compact_zero ν a m hm hK

/-- The Scott topology of the order product always refines the ordinary
product of the two Scott spaces, via the actual coordinate projections. -/
theorem scottProduct_to_ordinaryProduct_continuous
    {P : Type u} {Q : Type v} [PartialOrder P] [PartialOrder Q] :
    Continuous (fun z : WithScott (P × Q) =>
      (WithScott.toScott (WithScott.ofScott z).1,
        WithScott.toScott (WithScott.ofScott z).2)) :=
  ((scott_continuous_iff (Prod.fst : P × Q → P)).mp ScottContinuous.fst).prodMk
    ((scott_continuous_iff (Prod.snd : P × Q → Q)).mp ScottContinuous.snd)

theorem scottProduct_topology_le_ordinaryProduct
    {P : Type u} {Q : Type v} [PartialOrder P] [PartialOrder Q] :
    (show TopologicalSpace (P × Q) from
      (inferInstance : TopologicalSpace (WithScott (P × Q)))) ≤
    (show TopologicalSpace (P × Q) from
      (inferInstance : TopologicalSpace (WithScott P × WithScott Q))) :=
  continuous_id_iff_le.mp scottProduct_to_ordinaryProduct_continuous

/-- The strict-fineness conclusion of source `cor:product-topology-strict`.
Mathlib orders topologies by reverse open-set inclusion, so strict fineness
is the displayed strict inequality in this direction. -/
theorem source_orderProductScott_strictly_finer
    {T : Type u} [TopologicalSpace T] [T2Space T] [SecondCountableTopology T]
    [MeasurableSpace T] [BorelSpace T]
    (ν : Measure T) [NoAtoms ν] [IsProbabilityMeasure ν] [Measure.InnerRegular ν]
    (a : OmegaOneStage → T) (m : Measure (SourcePoint a))
    (hm : ∀ B : Set T, MeasurableSet B → m (SourcePoint.val ⁻¹' B) = ν B) :
    (show TopologicalSpace (SourceSmyth a × Opens (SourcePoint a)) from
      (inferInstance : TopologicalSpace (WithScott (SourceSmyth a × Opens (SourcePoint a))))) <
    (show TopologicalSpace (SourceSmyth a × Opens (SourcePoint a)) from
      (inferInstance : TopologicalSpace (WithScott (SourceSmyth a) ×
        WithScott (Opens (SourcePoint a))))) := by
  apply lt_of_le_of_ne scottProduct_topology_le_ordinaryProduct
  intro heq
  have hW : @IsOpen (SourceSmyth a × Opens (SourcePoint a))
      (inferInstance : TopologicalSpace (WithScott (SourceSmyth a × Opens (SourcePoint a))))
      (@ordinaryIncidence (SourcePoint a) _ _) := incidenceOpen.isOpen
  have hWprod : IsOpen (@ordinaryIncidence (SourcePoint a) _ _) :=
    Eq.mp (congrArg (fun t : TopologicalSpace (SourceSmyth a × Opens (SourcePoint a)) =>
      @IsOpen (SourceSmyth a × Opens (SourcePoint a)) t
        (@ordinaryIncidence (SourcePoint a) _ _)) heq) hW
  exact source_incidence_not_product_open ν a m hm hWprod

end CHFubini

#print axioms CHFubini.compact_neighborhood_of_membership_open
#print axioms CHFubini.source_incidence_not_product_open
#print axioms CHFubini.source_orderProductScott_strictly_finer
