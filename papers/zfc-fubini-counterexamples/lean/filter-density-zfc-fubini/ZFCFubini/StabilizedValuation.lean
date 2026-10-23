import ZFCFubini.Stabilization
import ZFCFubini.ParameterMeasure

/-!
Source Sections 4 and 6, at the level of a genuine decreasing continuous family.
The comparison lemma is an explicit intermediate theorem input here; the final
source wrapper must discharge it from the actual filter construction. No main
existence theorem or arbitrary-union law is assumed as a record field.
-/

set_option autoImplicit false
open Set TopologicalSpace MeasureTheory Topology
open scoped ENNReal
universe u v w z
namespace ZFCFubini

section Family
variable {I : Type u} [SemilatticeSup I] (hI : CountablyBounded I)
variable {X : Type v} [TopologicalSpace X] [SecondCountableTopology X]
variable {Q : Type w} [PartialOrder Q]
variable (F : I → X → WithScott Q)
variable (hanti : ∀ x, Antitone (fun i => F i x))
variable (hc : ∀ i, Continuous (F i))

include hanti in
theorem stageEvent_antitone (A : ScottOpens Q) :
    Antitone (fun i => F i ⁻¹' (A : Set (WithScott Q))) := by
  intro i j hij x hx
  exact (IsScott.isUpperSet_of_isOpen (D := univ) A.isOpen) (hanti x hij) hx

def stabilizedEvent (A : ScottOpens Q) : Opens X :=
  ⟨limitPreimage F (A : Set (WithScott Q)), limitPreimage_isOpen hI F _
    (stageEvent_antitone F hanti A) (fun i => A.isOpen.preimage (hc i))⟩

theorem stabilizedEvent_eventually_eq (A : ScottOpens Q) :
    ∃ σ : I, ∀ i, σ ≤ i → F i ⁻¹' (A : Set (WithScott Q)) =
      (stabilizedEvent hI F hanti hc A : Set X) :=
  limitPreimage_eventually_eq hI F _ (stageEvent_antitone F hanti A)
    (fun i => A.isOpen.preimage (hc i))

theorem stabilizedEvent_mono : Monotone (stabilizedEvent hI F hanti hc) :=
  fun _ _ h => limitPreimage_mono F h

@[simp] theorem stabilizedEvent_bot [Nonempty I] :
    stabilizedEvent hI F hanti hc ⊥ = ⊥ :=
  Opens.ext (limitPreimage_empty F)

@[simp] theorem stabilizedEvent_top : stabilizedEvent hI F hanti hc ⊤ = ⊤ :=
  Opens.ext (limitPreimage_univ F)

theorem stabilizedEvent_inf (A B : ScottOpens Q) :
    stabilizedEvent hI F hanti hc (A ⊓ B) =
      stabilizedEvent hI F hanti hc A ⊓ stabilizedEvent hI F hanti hc B :=
  Opens.ext (limitPreimage_inter F _ _)

theorem stabilizedEvent_sup (A B : ScottOpens Q) :
    stabilizedEvent hI F hanti hc (A ⊔ B) =
      stabilizedEvent hI F hanti hc A ⊔ stabilizedEvent hI F hanti hc B := by
  apply Opens.ext
  exact limitPreimage_union hI F _ _ (stageEvent_antitone F hanti A)
    (stageEvent_antitone F hanti B)
    (fun i => A.isOpen.preimage (hc i)) (fun i => B.isOpen.preimage (hc i))

theorem stabilizedEvent_iSup {J : Type z} [Countable J] (A : J → ScottOpens Q) :
    stabilizedEvent hI F hanti hc (⨆ j, A j) = ⨆ j, stabilizedEvent hI F hanti hc (A j) := by
  apply Opens.ext
  rw [Opens.coe_iSup]
  change limitPreimage F ((⨆ j, A j : ScottOpens Q) : Set (WithScott Q)) =
    ⋃ j, limitPreimage F (A j : Set (WithScott Q))
  simpa only [Opens.coe_iSup] using limitPreimage_iUnion hI F
    (fun j => (A j : Set (WithScott Q))) (fun j => stageEvent_antitone F hanti (A j))
    (fun j i => (A j).isOpen.preimage (hc i))

variable [T2Space X] [MeasurableSpace X] [OpensMeasurableSpace X]
variable (μ : Measure X) [μ.InnerRegular]

/-- The source quantifier order: one carrier index works for every observation,
although its later stabilization index may depend on that observation. -/
def CarrierIndexComparison : Prop :=
  ∀ D : Set X, PositiveCarrier μ D → ∃ σ : I, ∀ i, σ ≤ i → ∀ A : ScottOpens Q,
    (D ∩ (F σ ⁻¹' (A : Set (WithScott Q)))).Nonempty →
      (D ∩ (F i ⁻¹' (A : Set (WithScott Q)))).Nonempty

theorem stabilizedEvent_arbitrary_union_defect_null
    (hcompare : CarrierIndexComparison F μ) {J : Type z} (A : J → ScottOpens Q) :
    μ ((stabilizedEvent hI F hanti hc (⨆ j, A j) : Set X) \
      ⋃ j, (stabilizedEvent hI F hanti hc (A j) : Set X)) = 0 := by
  classical
  let B : Set X := (stabilizedEvent hI F hanti hc (⨆ j, A j) : Set X) \
    ⋃ j, (stabilizedEvent hI F hanti hc (A j) : Set X)
  have hBm : MeasurableSet B :=
    (stabilizedEvent hI F hanti hc (⨆ j, A j)).isOpen.measurableSet.diff
      (isOpen_iUnion (fun j => (stabilizedEvent hI F hanti hc (A j)).isOpen)).measurableSet
  change μ B = 0
  by_contra hB
  obtain ⟨D, hDB, hD⟩ := positive_compact_carrier μ hBm (pos_iff_ne_zero.mpr hB)
  obtain ⟨σ, hσ⟩ := hcompare D hD
  have htest (j : J) : Disjoint D (F σ ⁻¹' (A j : Set (WithScott Q))) := by
    obtain ⟨τ, hτ⟩ := stabilizedEvent_eventually_eq hI F hanti hc (A j)
    apply Set.disjoint_left.mpr
    intro x hxD hxσ
    obtain ⟨y, hyD, hy⟩ := hσ (σ ⊔ τ) le_sup_left (A j) ⟨x, hxD, hxσ⟩
    have hyψ : y ∈ (stabilizedEvent hI F hanti hc (A j) : Set X) :=
      hτ _ le_sup_right ▸ hy
    exact (hDB hyD).2 (mem_iUnion.mpr ⟨j, hyψ⟩)
  obtain ⟨x, hxD⟩ := hD.nonempty
  have hxσ : F σ x ∈ (⨆ j, A j : ScottOpens Q) := mem_iInter.mp (hDB hxD).1 σ
  have hxunion : F σ x ∈ ⋃ j, (A j : Set (WithScott Q)) := by
    simpa only [← Opens.coe_iSup] using hxσ
  obtain ⟨j, hj⟩ := mem_iUnion.mp hxunion
  exact Set.disjoint_left.mp (htest j) hxD hj

variable [IsProbabilityMeasure μ]

theorem stabilizedEvent_mass_iSup
    (hcompare : CarrierIndexComparison F μ)
    {J : Type z} [Nonempty J] (A : J → ScottOpens Q) (hd : Directed (· ≤ ·) A) :
    μ (stabilizedEvent hI F hanti hc (⨆ j, A j) : Set X) =
      ⨆ j, μ (stabilizedEvent hI F hanti hc (A j) : Set X) := by
  let B : Set X := ⋃ j, (stabilizedEvent hI F hanti hc (A j) : Set X)
  have hsub : B ⊆ (stabilizedEvent hI F hanti hc (⨆ j, A j) : Set X) := by
    intro x hx
    obtain ⟨j, hj⟩ := mem_iUnion.mp hx
    exact stabilizedEvent_mono hI F hanti hc (le_iSup A j) hj
  have hnull := stabilizedEvent_arbitrary_union_defect_null hI F hanti hc μ hcompare A
  have hreverse : μ (B \ (stabilizedEvent hI F hanti hc (⨆ j, A j) : Set X)) = 0 := by
    rw [diff_eq_empty.mpr hsub, measure_empty]
  have heq : μ (stabilizedEvent hI F hanti hc (⨆ j, A j) : Set X) = μ B :=
    (ae_eq_set.2 ⟨hnull, hreverse⟩).measure_eq
  rw [heq]
  simpa only [Opens.coe_iSup] using directed_open_measure μ
    (fun j => stabilizedEvent hI F hanti hc (A j))
    (by
      intro j k
      obtain ⟨l, hjl, hkl⟩ := hd j k
      exact ⟨l, stabilizedEvent_mono hI F hanti hc hjl,
        stabilizedEvent_mono hI F hanti hc hkl⟩)

def stabilizedValuation [Nonempty I] (hcompare : CarrierIndexComparison F μ) :
    Valuation (WithScott Q) where
  mass A := μ (stabilizedEvent hI F hanti hc A : Set X)
  strict := by simp
  modular A B := by
    simpa only [stabilizedEvent_sup, stabilizedEvent_inf, Opens.coe_sup, Opens.coe_inf]
      using (measure_union_add_inter
        (stabilizedEvent hI F hanti hc A : Set X)
        (stabilizedEvent hI F hanti hc B).isOpen.measurableSet).symm
  continuous := by
    intro D hn hd p hp
    have hm : Monotone (fun A : ScottOpens Q =>
        μ (stabilizedEvent hI F hanti hc A : Set X)) := by
      intro A B h
      exact measure_mono (show (stabilizedEvent hI F hanti hc A : Set X) ⊆
        stabilizedEvent hI F hanti hc B from stabilizedEvent_mono hI F hanti hc h)
    refine ⟨?_, ?_⟩
    · rintro b ⟨A, hA, rfl⟩
      exact hm (hp.1 hA)
    · intro z hz
      change μ (stabilizedEvent hI F hanti hc p : Set X) ≤ z
      letI : Nonempty D := hn.to_subtype
      have hp' : p = ⨆ A : D, A.val := hp.unique (by simpa using isLUB_sSup D)
      rw [hp', stabilizedEvent_mass_iSup hI F hanti hc μ hcompare
        (fun A : D => A.val) (by
          intro A B
          obtain ⟨C, hC, hAC, hBC⟩ := hd A.val A.property B.val B.property
          exact ⟨⟨C, hC⟩, hAC, hBC⟩)]
      exact iSup_le (fun A => hz (mem_image_of_mem _ A.property))

theorem stabilizedValuation_probability [Nonempty I]
    (hcompare : CarrierIndexComparison F μ) :
    (stabilizedValuation hI F hanti hc μ hcompare).Probability := by
  change μ (stabilizedEvent hI F hanti hc ⊤ : Set X) = 1
  simp

end Family
end ZFCFubini
