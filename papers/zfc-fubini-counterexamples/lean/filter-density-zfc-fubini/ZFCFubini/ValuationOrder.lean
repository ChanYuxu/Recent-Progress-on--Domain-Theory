import ZFCFubini.Foundations

/-!
# The actual pointwise dcpo of continuous valuations

The order is comparison on every open, not comparison of a representation or
of an auxiliary integration functional. Directed suprema are constructed on
the existing `Valuation` structure. Only nonempty directed families are used;
no bottom element is required of any underlying dcpo.
-/

set_option autoImplicit false
open Set Topology TopologicalSpace
open scoped ENNReal Classical
universe u v

namespace ZFCFubini
namespace Valuation

variable {X : Type u} [TopologicalSpace X]

instance : PartialOrder (Valuation X) where
  le μ ν := ∀ U, μ U ≤ ν U
  le_refl μ U := le_rfl
  le_trans μ ν ρ hμν hνρ U := (hμν U).trans (hνρ U)
  le_antisymm μ ν hμν hνμ := ext fun U => le_antisymm (hμν U) (hνμ U)

@[simp] theorem le_def {μ ν : Valuation X} : μ ≤ ν ↔ ∀ U, μ U ≤ ν U := Iff.rfl

/-- The supremum of a nonempty directed family, evaluated on actual opens. -/
noncomputable def directedSup {ι : Type v} [Nonempty ι]
    (μ : ι → Valuation X) (hd : Directed (· ≤ ·) μ) : Valuation X where
  mass U := ⨆ i, μ i U
  strict := by simp only [Valuation.strict, iSup_const]
  modular U V := by
    have hadd (A B : Opens X) :
        (⨆ i, μ i A) + (⨆ i, μ i B) = ⨆ i, μ i A + μ i B := by
      apply ENNReal.iSup_add_iSup
      intro i j
      obtain ⟨k, hik, hjk⟩ := hd i j
      exact ⟨k, add_le_add (hik A) (hjk B)⟩
    rw [hadd, hadd]
    exact iSup_congr fun i => (μ i).modular U V
  continuous := by
    intro A hn hA p hp
    constructor
    · rintro _ ⟨U, hU, rfl⟩
      exact iSup_mono fun i => (μ i).mono (hp.1 hU)
    · intro b hb
      apply iSup_le
      intro i
      apply ((μ i).continuous hn hA hp).2
      rintro _ ⟨U, hU, rfl⟩
      exact (le_iSup (fun j => μ j U) i).trans (hb ⟨U, hU, rfl⟩)

@[simp] theorem directedSup_apply {ι : Type v} [Nonempty ι]
    (μ : ι → Valuation X) (hd : Directed (· ≤ ·) μ) (U : Opens X) :
    directedSup μ hd U = ⨆ i, μ i U := rfl

theorem le_directedSup {ι : Type v} [Nonempty ι]
    (μ : ι → Valuation X) (hd : Directed (· ≤ ·) μ) (i : ι) :
    μ i ≤ directedSup μ hd := fun U => le_iSup (fun j => μ j U) i

theorem directedSup_le {ι : Type v} [Nonempty ι]
    (μ : ι → Valuation X) (hd : Directed (· ≤ ·) μ) {ν : Valuation X}
    (h : ∀ i, μ i ≤ ν) : directedSup μ hd ≤ ν :=
  fun U => iSup_le fun i => h i U

theorem directedSup_isLUB {ι : Type v} [Nonempty ι]
    (μ : ι → Valuation X) (hd : Directed (· ≤ ·) μ) :
    IsLUB (Set.range μ) (directedSup μ hd) := by
  constructor
  · rintro _ ⟨i, rfl⟩
    exact le_directedSup μ hd i
  · intro ν hν
    exact directedSup_le μ hd fun i => hν (Set.mem_range_self i)

/-- Evaluation at an open preserves all nonempty directed suprema. -/
theorem evaluation_scottContinuous (U : Opens X) :
    ScottContinuous (fun μ : Valuation X => μ U) := by
  intro A hn hd p hp
  letI : Nonempty A := hn.to_subtype
  let μ : A → Valuation X := Subtype.val
  have hμ : Directed (· ≤ ·) μ := by
    intro i j
    obtain ⟨k, hk, hik, hjk⟩ := hd i i.property j j.property
    exact ⟨⟨k, hk⟩, hik, hjk⟩
  have heq : p = directedSup μ hμ := by
    apply hp.unique
    simpa only [μ, Subtype.range_coe_subtype, setOf_mem_eq] using directedSup_isLUB μ hμ
  subst p
  constructor
  · rintro _ ⟨ν, hν, rfl⟩
    exact le_iSup (fun i : A => μ i U) ⟨ν, hν⟩
  · intro b hb
    exact iSup_le fun i => hb ⟨μ i, i.property, rfl⟩

theorem directedSup_subprobability {ι : Type v} [Nonempty ι]
    (μ : ι → Valuation X) (hd : Directed (· ≤ ·) μ)
    (hμ : ∀ i, (μ i).Subprobability) : (directedSup μ hd).Subprobability :=
  iSup_le hμ

theorem push_mono {Y : Type v} [TopologicalSpace Y]
    (f : X → Y) (hf : Continuous f) : Monotone (fun μ : Valuation X => μ.push f hf) :=
  fun _ _ h U => h (Opens.comap ⟨f, hf⟩ U)

theorem push_scottContinuous {Y : Type v} [TopologicalSpace Y]
    (f : X → Y) (hf : Continuous f) :
    ScottContinuous (fun μ : Valuation X => μ.push f hf) := by
  intro A hn hd p hp
  constructor
  · rintro _ ⟨μ, hμ, rfl⟩
    exact push_mono f hf (hp.1 hμ)
  · intro ν hν U
    apply (evaluation_scottContinuous (Opens.comap ⟨f, hf⟩ U) hn hd hp).2
    rintro _ ⟨μ, hμ, rfl⟩
    exact hν ⟨μ, hμ, rfl⟩ U

theorem scottContinuous_of_evaluation {P : Type v} [Preorder P]
    (f : P → Valuation X) (hf : ∀ U, ScottContinuous (fun p => f p U)) :
    ScottContinuous f := by
  intro A hn hd p hp
  constructor
  · rintro _ ⟨a, ha, rfl⟩ U
    exact (hf U).monotone (hp.1 ha)
  · intro ν hν U
    apply (hf U hn hd hp).2
    rintro _ ⟨a, ha, rfl⟩
    exact hν ⟨a, ha, rfl⟩ U

/-- Unit valuation: the actual indicator of membership in an open. -/
noncomputable def dirac (x : X) : Valuation X := by
  classical
  exact {
    mass := fun U => if x ∈ U then 1 else 0
    strict := by simp
    modular := fun U V => by
      by_cases hU : x ∈ U <;> by_cases hV : x ∈ V <;> simp [hU, hV]
    continuous := by
      intro A hn hd p hp
      have heq : p = sSup A := hp.unique (isLUB_sSup A)
      constructor
      · rintro _ ⟨U, hU, rfl⟩
        by_cases hx : x ∈ U
        · simp only [if_pos hx, if_pos (hp.1 hU hx), le_refl]
        · simp only [if_neg hx, zero_le]
      · intro b hb
        by_cases hx : x ∈ p
        · obtain ⟨U, hU, hxU⟩ := Opens.mem_sSup.mp (heq ▸ hx)
          simpa only [if_pos hx, if_pos hxU] using hb ⟨U, hU, rfl⟩
        · simp only [if_neg hx, zero_le] }

@[simp] theorem dirac_apply (x : X) (U : Opens X) :
    dirac x U = if x ∈ U then 1 else 0 := by classical exact rfl

@[simp] theorem dirac_probability (x : X) : (dirac x).Probability := by
  classical
  simp [Probability]

theorem dirac_scottContinuous {P : Type v} [Preorder P] :
    ScottContinuous (fun p : P => dirac (WithScott.toScott p)) := by
  classical
  apply scottContinuous_of_evaluation
  intro U A hn hd p hp
  have hU := (Topology.IsScott.isOpen_iff_isUpperSet_and_dirSupInaccOn
    (D := Set.univ)).mp U.isOpen
  constructor
  · rintro _ ⟨a, ha, rfl⟩
    by_cases hx : WithScott.toScott a ∈ U
    · have hpx : WithScott.toScott p ∈ U := hU.1 (hp.1 ha) hx
      simpa [dirac_apply, hx, hpx] using (le_rfl : (1 : ℝ≥0∞) ≤ 1)
    · simp only [dirac_apply, if_neg hx, zero_le]
  · intro b hb
    by_cases hx : WithScott.toScott p ∈ U
    · obtain ⟨a, ha, hax⟩ := hU.2 (Set.mem_univ _) hn hd hp hx
      have hax' : @WithScott.toScott P a ∈ U := hax
      have hb' : dirac (@WithScott.toScott P a) U ≤ b := hb ⟨a, ha, rfl⟩
      rw [dirac_apply, if_pos hax'] at hb'
      simpa [dirac_apply, hx] using hb'
    · simp only [dirac_apply, if_neg hx, zero_le]

end Valuation

theorem valuation_isDcpo (X : Type u) [TopologicalSpace X] : IsDcpo (Valuation X) := by
  intro A hn hd
  letI : Nonempty A := hn.to_subtype
  have h : Directed (· ≤ ·) (fun i : A => i.val) := by
    intro i j
    obtain ⟨k, hk, hik, hjk⟩ := hd i i.property j j.property
    exact ⟨⟨k, hk⟩, hik, hjk⟩
  refine ⟨Valuation.directedSup (fun i : A => i.val) h, ?_⟩
  simpa only [Subtype.range_coe_subtype, setOf_mem_eq] using
    Valuation.directedSup_isLUB (fun i : A => i.val) h

namespace SubprobValuation

variable {X : Type u} [TopologicalSpace X]

/-- A directed supremum stays a subprobability because total mass is pointwise. -/
noncomputable def directedSup {ι : Type v} [Nonempty ι]
    (μ : ι → SubprobValuation X) (hd : Directed (· ≤ ·) μ) : SubprobValuation X :=
  ⟨Valuation.directedSup (fun i => (μ i).val) hd,
    Valuation.directedSup_subprobability _ hd fun i => (μ i).property⟩

@[simp] theorem directedSup_apply {ι : Type v} [Nonempty ι]
    (μ : ι → SubprobValuation X) (hd : Directed (· ≤ ·) μ) (U : Opens X) :
    (directedSup μ hd).val U = ⨆ i, (μ i).val U := rfl

theorem directedSup_isLUB {ι : Type v} [Nonempty ι]
    (μ : ι → SubprobValuation X) (hd : Directed (· ≤ ·) μ) :
    IsLUB (Set.range μ) (directedSup μ hd) := by
  constructor
  · rintro _ ⟨i, rfl⟩
    exact Valuation.le_directedSup _ hd i
  · intro ν hν
    exact Valuation.directedSup_le _ hd fun i => hν (Set.mem_range_self i)

theorem val_scottContinuous :
    ScottContinuous (Subtype.val : SubprobValuation X → Valuation X) := by
  intro A hn hd p hp
  letI : Nonempty A := hn.to_subtype
  have h : Directed (· ≤ ·) (fun i : A => i.val) := by
    intro i j
    obtain ⟨k, hk, hik, hjk⟩ := hd i i.property j j.property
    exact ⟨⟨k, hk⟩, hik, hjk⟩
  have heq : p = directedSup (fun i : A => i.val) h := by
    apply hp.unique
    simpa only [Subtype.range_coe_subtype, setOf_mem_eq] using directedSup_isLUB _ h
  subst p
  convert Valuation.directedSup_isLUB (fun i : A => i.val.val) h using 1
  ext ν
  simp only [Set.mem_range, Set.mem_image, Subtype.exists, exists_prop]

theorem evaluation_scottContinuous (U : Opens X) :
    ScottContinuous (fun μ : SubprobValuation X => μ.val U) :=
  val_scottContinuous.comp (Valuation.evaluation_scottContinuous U)

theorem scottContinuous_of_evaluation {P : Type v} [Preorder P]
    (f : P → SubprobValuation X) (hf : ∀ U, ScottContinuous (fun p => (f p).val U)) :
    ScottContinuous f := by
  intro A hn hd p hp
  constructor
  · rintro _ ⟨a, ha, rfl⟩ U
    exact (hf U).monotone (hp.1 ha)
  · intro ν hν U
    apply (hf U hn hd hp).2
    rintro _ ⟨a, ha, rfl⟩
    exact hν ⟨a, ha, rfl⟩ U

noncomputable def dirac (x : X) : SubprobValuation X :=
  ⟨Valuation.dirac x, (Valuation.dirac_probability x).subprobability⟩

@[simp] theorem dirac_val (x : X) : (dirac x).val = Valuation.dirac x := rfl

theorem dirac_scottContinuous {P : Type v} [Preorder P] :
    ScottContinuous (fun p : P => dirac (WithScott.toScott p)) := by
  apply scottContinuous_of_evaluation
  intro U
  exact Valuation.dirac_scottContinuous.comp (Valuation.evaluation_scottContinuous U)

noncomputable def push {Y : Type v} [TopologicalSpace Y]
    (μ : SubprobValuation X) (f : X → Y) (hf : Continuous f) : SubprobValuation Y :=
  ⟨μ.val.push f hf, μ.property⟩

@[simp] theorem push_val {Y : Type v} [TopologicalSpace Y]
    (μ : SubprobValuation X) (f : X → Y) (hf : Continuous f) :
    (push μ f hf).val = μ.val.push f hf := rfl

theorem push_scottContinuous {Y : Type v} [TopologicalSpace Y]
    (f : X → Y) (hf : Continuous f) :
    ScottContinuous (fun μ : SubprobValuation X => μ.push f hf) := by
  apply scottContinuous_of_evaluation
  intro U
  exact evaluation_scottContinuous (Opens.comap ⟨f, hf⟩ U)

end SubprobValuation

theorem subprobValuation_isDcpo (X : Type u) [TopologicalSpace X] :
    IsDcpo (SubprobValuation X) := by
  intro A hn hd
  letI : Nonempty A := hn.to_subtype
  have h : Directed (· ≤ ·) (fun i : A => i.val) := by
    intro i j
    obtain ⟨k, hk, hik, hjk⟩ := hd i i.property j j.property
    exact ⟨⟨k, hk⟩, hik, hjk⟩
  refine ⟨SubprobValuation.directedSup (fun i : A => i.val) h, ?_⟩
  simpa only [Subtype.range_coe_subtype, setOf_mem_eq] using
    SubprobValuation.directedSup_isLUB (fun i : A => i.val) h

end ZFCFubini
