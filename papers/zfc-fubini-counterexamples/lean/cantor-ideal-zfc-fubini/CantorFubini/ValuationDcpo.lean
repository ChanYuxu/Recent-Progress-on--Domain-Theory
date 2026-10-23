import CantorFubini.DcpoCategory

/-! Pointwise directed suprema of actual continuous valuations and the actual
subprobability valuation object of DCPO. No integral or monad law is assumed. -/

set_option autoImplicit false
open Set Topology TopologicalSpace CategoryTheory
open scoped ENNReal Classical
universe u v

namespace CantorFubini
namespace Valuation
variable {X : Type u} [TopologicalSpace X]

instance : PartialOrder (Valuation X) where
  le μ ν := ∀ U, μ U ≤ ν U
  le_refl μ U := le_rfl
  le_trans μ ν ρ hμν hνρ U := (hμν U).trans (hνρ U)
  le_antisymm μ ν hμν hνμ := Valuation.ext (fun U => le_antisymm (hμν U) (hνμ U))

@[simp] theorem le_iff {μ ν : Valuation X} : μ ≤ ν ↔ ∀ U, μ U ≤ ν U := Iff.rfl

noncomputable def directedSup {ι : Type v} (f : ι → Valuation X)
    (hf : Directed (· ≤ ·) f) : Valuation X where
  mass U := ⨆ i, f i U
  strict := by
    simp only [strict]
    exact le_antisymm (iSup_le (fun _ => le_rfl)) (zero_le _)
  modular U V := by
    have hadd (U V : Opens X) :
        (⨆ i, f i U) + (⨆ i, f i V) = ⨆ i, (f i U + f i V) := by
      apply ENNReal.iSup_add_iSup
      intro i j
      obtain ⟨k, hik, hjk⟩ := hf i j
      exact ⟨k, add_le_add (hik U) (hjk V)⟩
    rw [hadd, hadd]
    exact iSup_congr (fun i => (f i).modular U V)
  continuous := by
    intro A hn hd p hp
    constructor
    · rintro z ⟨U, hU, rfl⟩
      exact iSup_le (fun i => (f i).mono (hp.1 hU) |>.trans (le_iSup (fun j => f j p) i))
    · intro z hz
      apply iSup_le
      intro i
      apply ((f i).continuous hn hd hp).2
      rintro a ⟨U, hU, rfl⟩
      exact (le_iSup (fun j => f j U) i).trans (hz (mem_image_of_mem _ hU))

@[simp] theorem directedSup_apply {ι : Type v} (f : ι → Valuation X)
    (hf : Directed (· ≤ ·) f) (U : Opens X) : directedSup f hf U = ⨆ i, f i U := rfl

theorem directedSup_isLUB {ι : Type v} (f : ι → Valuation X)
    (hf : Directed (· ≤ ·) f) : IsLUB (range f) (directedSup f hf) := by
  refine ⟨?_, ?_⟩
  · rintro μ ⟨i, rfl⟩ U
    change f i U ≤ ⨆ j, f j U
    exact le_iSup (fun j => f j U) i
  · intro μ hμ U
    exact iSup_le (fun i => hμ (mem_range_self i) U)

theorem isDcpo : IsDcpo (Valuation X) := by
  intro D _ hd
  let f : D → Valuation X := Subtype.val
  have hf : Directed (· ≤ ·) f := hd.directed_val
  refine ⟨directedSup f hf, ?_⟩
  simpa only [f, Subtype.range_val] using directedSup_isLUB f hf

noncomputable def zero : Valuation X where
  mass _ := 0
  strict := rfl
  modular _ _ := rfl
  continuous := ScottContinuous.const 0

noncomputable instance : OrderBot (Valuation X) where
  bot := zero
  bot_le μ U := zero_le _

@[simp] theorem zero_apply (U : Opens X) : (zero : Valuation X) U = 0 := rfl
@[simp] theorem bot_apply (U : Opens X) : (⊥ : Valuation X) U = 0 := rfl

/-- Point evaluation is Scott-continuous in the valuation argument. -/
theorem evaluation_scottContinuous (U : Opens X) : ScottContinuous (fun μ : Valuation X => μ U) := by
  intro D hn hd p hp
  let f : D → Valuation X := Subtype.val
  have hf : Directed (· ≤ ·) f := hd.directed_val
  have hl : IsLUB D (directedSup f hf) := by
    simpa only [f, Subtype.range_val] using directedSup_isLUB f hf
  rw [hp.unique hl]
  change IsLUB ((fun μ : Valuation X => μ U) '' D) (⨆ μ : D, μ.val U)
  convert (isLUB_iSup : IsLUB (range (fun μ : D => μ.val U)) (⨆ μ : D, μ.val U)) using 1
  ext z
  simp only [mem_image, mem_range, Subtype.exists, exists_prop]

/-- Actual point-mass valuation, on the specified topology of X. -/
noncomputable def dirac (x : X) : Valuation X where
  mass U := if x ∈ U then 1 else 0
  strict := by simp
  modular U V := by
    classical
    by_cases hxU : x ∈ U <;> by_cases hxV : x ∈ V <;>
      simp [hxU, hxV]
  continuous := by
    classical
    intro A hn hd p hp
    constructor
    · rintro z ⟨U, hU, rfl⟩
      by_cases hxU : x ∈ U
      · simp only [hxU, if_true]
        simp only [hp.1 hU hxU, if_true, le_refl]
      · simp only [hxU, if_false, zero_le]
    · intro z hz
      by_cases hxp : x ∈ p
      · have hxs : x ∈ (sSup A : Opens X) := hp.unique (isLUB_sSup A) ▸ hxp
        obtain ⟨U, hU, hxU⟩ := Opens.mem_sSup.mp hxs
        simpa only [hxp, hxU, if_true] using hz (mem_image_of_mem _ hU)
      · simp only [hxp, if_false, zero_le]

@[simp] theorem dirac_apply (x : X) (U : Opens X) : dirac x U = if x ∈ U then 1 else 0 := rfl
theorem dirac_probability (x : X) : (dirac x).Probability := by simp [Probability]

end Valuation

namespace SubprobValuation
variable {X : Type u} [TopologicalSpace X]

noncomputable def directedSup {ι : Type v} (f : ι → SubprobValuation X)
    (hf : Directed (· ≤ ·) f) : SubprobValuation X :=
  ⟨Valuation.directedSup (fun i => (f i).val) hf, iSup_le (fun i => (f i).property)⟩

@[simp] theorem directedSup_apply {ι : Type v} (f : ι → SubprobValuation X)
    (hf : Directed (· ≤ ·) f) (U : Opens X) :
    (directedSup f hf).val U = ⨆ i, (f i).val U := rfl

theorem directedSup_isLUB {ι : Type v} (f : ι → SubprobValuation X)
    (hf : Directed (· ≤ ·) f) : IsLUB (range f) (directedSup f hf) := by
  refine ⟨?_, ?_⟩
  · rintro μ ⟨i, rfl⟩ U
    change (f i).val U ≤ ⨆ j, (f j).val U
    exact le_iSup (fun j => (f j).val U) i
  · intro μ hμ U
    exact iSup_le (fun i => hμ (mem_range_self i) U)

theorem isDcpo : IsDcpo (SubprobValuation X) := by
  intro D _ hd
  let f : D → SubprobValuation X := Subtype.val
  have hf : Directed (· ≤ ·) f := hd.directed_val
  refine ⟨directedSup f hf, ?_⟩
  simpa only [f, Subtype.range_val] using directedSup_isLUB f hf

noncomputable instance : OrderBot (SubprobValuation X) where
  bot := ⟨⊥, by simp [Valuation.Subprobability]⟩
  bot_le μ U := zero_le _

theorem evaluation_scottContinuous (U : Opens X) :
    ScottContinuous (fun μ : SubprobValuation X => μ.val U) := by
  intro D hn hd p hp
  let f : D → SubprobValuation X := Subtype.val
  have hf : Directed (· ≤ ·) f := hd.directed_val
  have hl : IsLUB D (directedSup f hf) := by
    simpa only [f, Subtype.range_val] using directedSup_isLUB f hf
  rw [hp.unique hl]
  change IsLUB ((fun μ : SubprobValuation X => μ.val U) '' D) (⨆ μ : D, μ.val.val U)
  convert (isLUB_iSup : IsLUB (range (fun μ : D => μ.val.val U)) (⨆ μ : D, μ.val.val U)) using 1
  ext z
  simp only [mem_image, mem_range, Subtype.exists, exists_prop]

noncomputable def dirac (x : X) : SubprobValuation X :=
  ⟨Valuation.dirac x, (Valuation.dirac_probability x).subprobability⟩

@[ext] theorem ext {μ ν : SubprobValuation X} (h : ∀ U, μ.val U = ν.val U) : μ = ν :=
  Subtype.ext (Valuation.ext h)

theorem scottContinuous_of_evaluations {D : Type v} [Preorder D]
    {f : D → SubprobValuation X}
    (hf : ∀ U : Opens X, ScottContinuous (fun x => (f x).val U)) : ScottContinuous f := by
  intro S hn hd p hp
  constructor
  · rintro μ ⟨x, hx, rfl⟩ U
    exact (hf U hn hd hp).1 (mem_image_of_mem _ hx)
  · intro μ hμ U
    apply (hf U hn hd hp).2
    rintro a ⟨x, hx, rfl⟩
    exact hμ (mem_image_of_mem _ hx) U

noncomputable def push {Y : Type v} [TopologicalSpace Y] (μ : SubprobValuation X)
    (f : X → Y) (hf : Continuous f) : SubprobValuation Y :=
  ⟨μ.val.push f hf, μ.property⟩

@[simp] theorem push_apply {Y : Type v} [TopologicalSpace Y] (μ : SubprobValuation X)
    (f : X → Y) (hf : Continuous f) (U : Opens Y) :
    (μ.push f hf).val U = μ.val (Opens.comap ⟨f, hf⟩ U) := rfl

theorem push_scottContinuous {Y : Type v} [TopologicalSpace Y]
    (f : X → Y) (hf : Continuous f) : ScottContinuous (fun μ : SubprobValuation X => μ.push f hf) :=
  scottContinuous_of_evaluations (fun U => evaluation_scottContinuous (Opens.comap ⟨f, hf⟩ U))

end SubprobValuation

namespace DCPO

def valuations (D : DCPO.{u}) : DCPO.{u} :=
  of (SubprobValuation (WithScott D)) SubprobValuation.isDcpo

/-- The unit point map preserves arbitrary nonempty directed suprema. -/
theorem dirac_scottContinuous (D : DCPO.{u}) :
    ScottContinuous (fun x : D => SubprobValuation.dirac (WithScott.toScott x)) := by
  classical
  intro S hn hd p hp
  constructor
  · rintro μ ⟨x, hx, rfl⟩ U
    by_cases hxU : WithScott.toScott x ∈ U
    · have hpU : WithScott.toScott p ∈ U :=
        (IsScott.isUpperSet_of_isOpen (D := univ) U.isOpen) (hp.1 hx) hxU
      change (if WithScott.toScott x ∈ U then 1 else 0) ≤
        (if WithScott.toScott p ∈ U then 1 else 0)
      rw [if_pos hxU, if_pos hpU]
    · simp [SubprobValuation.dirac, hxU]
  · intro μ hμ U
    by_cases hpU : WithScott.toScott p ∈ U
    · have hacc := ((IsScott.isOpen_iff_isUpperSet_and_dirSupInaccOn (D := univ)).mp U.isOpen).2
      obtain ⟨x, hx, hxU⟩ := hacc (mem_univ _) hn hd hp hpU
      have hxU' : WithScott.toScott x ∈ U := hxU
      have hb := hμ (mem_image_of_mem _ hx) U
      change (if WithScott.toScott p ∈ U then 1 else 0) ≤ μ.val U
      change (if WithScott.toScott x ∈ U then 1 else 0) ≤ μ.val U at hb
      simpa only [hxU', hpU, if_true] using hb
    · simp [SubprobValuation.dirac, hpU]

noncomputable def point (D : DCPO.{u}) : D ⟶ valuations D :=
  hom (fun x => SubprobValuation.dirac (WithScott.toScott x)) (dirac_scottContinuous D)

noncomputable def valuationMap {D E : DCPO.{u}} (f : D ⟶ E) : valuations D ⟶ valuations E :=
  hom (fun μ => SubprobValuation.push μ
    (fun x : WithScott D => WithScott.toScott (f (WithScott.ofScott x)))
    ((scott_continuous_iff f).mp (hom_scottContinuous f)))
    (SubprobValuation.push_scottContinuous _ ((scott_continuous_iff f).mp (hom_scottContinuous f)))

@[simp] theorem valuationMap_apply {D E : DCPO.{u}} (f : D ⟶ E)
    (μ : valuations D) (U : ScottOpens E) :
    (valuationMap f μ).val U = μ.val
      (Opens.comap ⟨(fun x : WithScott D => WithScott.toScott (f (WithScott.ofScott x))),
        ((scott_continuous_iff f).mp (hom_scottContinuous f))⟩ U) := rfl

noncomputable def valuationFunctor : DCPO.{u} ⥤ DCPO.{u} where
  obj := valuations
  map := valuationMap
  map_id D := by
    apply Hom.ext
    intro μ
    apply SubprobValuation.ext
    intro U
    rfl
  map_comp f g := by
    apply Hom.ext
    intro μ
    apply SubprobValuation.ext
    intro U
    rfl

noncomputable def pointNatural : 𝟭 DCPO.{u} ⟶ valuationFunctor where
  app := point
  naturality := by
    intro D E f
    apply Hom.ext
    intro x
    apply SubprobValuation.ext
    intro U
    rfl

end DCPO
end CantorFubini
