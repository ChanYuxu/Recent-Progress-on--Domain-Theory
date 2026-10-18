import Practice.DomainTheory.Papers.RBFunctionSpace.TestDomain

/-!
# The map `Q` and finite requirements

This file formalizes `lem:Q-general`, `lem:standard-step`, and
`lem:requirements-waybelow`.
-/

set_option autoImplicit false
set_option linter.unnecessarySimpa false

universe u v

namespace RBFunctionSpace

open Set
open AbramskyJung.Chapter2

variable {X : Type u} [PartialOrder X]

noncomputable local instance classicalPropDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-- The manuscript's map `Q(x) = (↓↓x, 0)`. -/
def Q (hX : IsDomain X) :
    AbramskyJung.Chapter3.ContFun X (EX X) where
  toFun := fun x =>
    EX.lower (wayBelowLower x)
      (Or.inr (continuous_wayBelowLower_directed hX.2.2 x))
  continuous := by
    constructor
    · intro x y hxy
      rw [EX.le_iff]
      refine ⟨?_, Bool.false_le _⟩
      intro a hax
      exact prop_2_2_2_2 le_rfl hax hxy
    · intro A s hA hs
      constructor
      · intro e he
        rcases he with ⟨x, hxA, rfl⟩
        rw [EX.le_iff]
        refine ⟨?_, Bool.false_le _⟩
        intro a hax
        exact prop_2_2_2_2 le_rfl hax (hs.1 hxA)
      · intro z hz
        rw [EX.le_iff]
        refine ⟨?_, Bool.false_le _⟩
        intro a has
        have hformula :=
          Set.ext_iff.mp
            (cor_2_2_16_wayBelowLower_directed_sup hX.2.2 hA hs) a
        have haUnion : a ∈ ⋃ x ∈ A, wayBelowLower x :=
          hformula.mp has
        rw [Set.mem_iUnion] at haUnion
        rcases haUnion with ⟨x, hxrest⟩
        rw [Set.mem_iUnion] at hxrest
        rcases hxrest with ⟨hxA, hax⟩
        exact (EX.le_iff.mp (hz ⟨x, hxA, rfl⟩)).1 hax

@[simp]
theorem Q_carrier (hX : IsDomain X) (x : X) :
    EX.carrier (Q hX x) = wayBelowLower x :=
  rfl

@[simp]
theorem Q_layer (hX : IsDomain X) (x : X) :
    EX.layer (Q hX x) = false :=
  rfl

/-- The principal upper set of an element. -/
def above {Y : Type v} [Preorder Y] (k : Y) : Set Y :=
  {y | k ≤ y}

theorem scottOpen_above_of_compact
    {Y : Type v} [Preorder Y] {k : Y} (hk : Compact k) :
    ScottOpen (above k) := by
  constructor
  · intro x y hy hxy hx
    exact hy (le_trans hx hxy)
  · intro A s hA hAs hs hsAbove
    rcases hk hA hs hsAbove with ⟨a, haA, hka⟩
    exact (hAs haA) hka

/-- A Scott-open inverse image of a compact principal upper set. -/
def compactPreimageOpen
    {Y : Type v} [Preorder Y]
    (g : AbramskyJung.Chapter3.ContFun X Y) (k : Y)
    (hk : Compact k) :
    ScottOpenSet X where
  val := g ⁻¹' above k
  property :=
    (prop_2_3_4_forward g.continuous)
      (above k) (scottOpen_above_of_compact hk)

theorem compactPreimageOpen_mono
    {Y : Type v} [Preorder Y]
    {g h : AbramskyJung.Chapter3.ContFun X Y} (hgh : g ≤ h)
    (k : Y) (hk : Compact k) :
    compactPreimageOpen g k hk ≤ compactPreimageOpen h k hk := by
  intro x hx
  exact le_trans hx (hgh x)

/-- The underlying function of a standard step. -/
noncomputable def openStepFun
    {Y : Type v} [PartialOrder Y] [OrderBot Y]
    (V : ScottOpenSet X) (k : Y) : X → Y :=
  fun x => if x ∈ V then k else ⊥

theorem openStepFun_scottContinuous
    {Y : Type v} [PartialOrder Y] [OrderBot Y]
    (V : ScottOpenSet X) (k : Y) :
    AbramskyJung.Chapter2.ScottContinuous (openStepFun V k) := by
  classical
  constructor
  · intro x y hxy
    by_cases hx : x ∈ V
    · have hy : y ∈ V :=
        scottOpen_upper V.2 hx hxy
      simp [openStepFun, hx, hy]
    · simp [openStepFun, hx, bot_le]
  · intro A s hA hs
    by_cases hsV : s ∈ V
    · have hHit : ∃ a ∈ A, a ∈ V := by
        by_contra hnone
        have hAsub : A ⊆ (V : Set X)ᶜ := by
          intro a haA haV
          exact hnone ⟨a, haA, haV⟩
        exact (V.2.2 hA hAsub hs) hsV
      rcases hHit with ⟨a₀, ha₀A, ha₀V⟩
      have hvalue : openStepFun V k s = k := by
        simp [openStepFun, hsV]
      rw [hvalue]
      constructor
      · intro y hy
        rcases hy with ⟨a, haA, rfl⟩
        by_cases haV : a ∈ V
        · simp [openStepFun, haV]
        · simp [openStepFun, haV, bot_le]
      · intro y hy
        apply hy
        refine ⟨a₀, ha₀A, ?_⟩
        simp [openStepFun, ha₀V]
    · have hnone : ∀ a ∈ A, a ∉ V := by
        intro a haA haV
        exact hsV (scottOpen_upper V.2 haV (hs.1 haA))
      have hvalue : openStepFun V k s = ⊥ := by
        simp [openStepFun, hsV]
      rw [hvalue]
      constructor
      · intro y hy
        rcases hy with ⟨a, haA, rfl⟩
        simp [openStepFun, hnone a haA]
      · intro y _
        exact bot_le

/-- The standard step map supported by a Scott-open set. -/
noncomputable def openStep
    {Y : Type v} [PartialOrder Y] [OrderBot Y]
    (V : ScottOpenSet X) (k : Y) :
    AbramskyJung.Chapter3.ContFun X Y where
  toFun := openStepFun V k
  continuous := openStepFun_scottContinuous V k

@[simp]
theorem openStep_apply
    {Y : Type v} [PartialOrder Y] [OrderBot Y]
    (V : ScottOpenSet X) (k : Y) (x : X) :
    openStep V k x = if x ∈ V then k else ⊥ :=
  rfl

/-- `lem:standard-step`: the standard step-function way-below lemma. -/
theorem standardStep_wayBelow
    {Y : Type v} [PartialOrder Y] [OrderBot Y]
    (hY : IsDcpoOrder Y)
    (V : ScottOpenSet X) {k : Y} (hk : Compact k)
    (f : AbramskyJung.Chapter3.ContFun X Y)
    (hV : V ≪ compactPreimageOpen f k hk) :
    openStep V k ≪ f := by
  intro A s hA hs hfs
  let W : AbramskyJung.Chapter3.ContFun X Y → ScottOpenSet X :=
    fun g => compactPreimageOpen g k hk
  have hWmono : Monotone W := by
    intro g h hgh
    exact compactPreimageOpen_mono hgh k hk
  have hWA : DirectedSet (W '' A) :=
    DirectedSet.image hWmono hA
  have htarget :
      compactPreimageOpen f k hk ≤ ScottOpenSet.sUnion (W '' A) := by
    intro x hx
    have hEvalSup :
        IsSup
          ((fun g : AbramskyJung.Chapter3.ContFun X Y => g x) '' A)
          (s x) :=
      (AbramskyJung.Chapter3.ContFun.eval_scottContinuous hY.1 x).2 hA hs
    have hkSup : k ≤ s x :=
      le_trans hx (hfs x)
    have hEvalDir :
        DirectedSet
          ((fun g : AbramskyJung.Chapter3.ContFun X Y => g x) '' A) :=
      AbramskyJung.Chapter3.ContFun.eval_directed hA x
    rcases hk hEvalDir hEvalSup hkSup with
      ⟨y, hy, hky⟩
    rcases hy with ⟨g, hgA, rfl⟩
    change x ∈ ⋃ U : (W '' A), (U.1 : Set X)
    rw [Set.mem_iUnion]
    refine ⟨⟨W g, ⟨g, hgA, rfl⟩⟩, ?_⟩
    exact hky
  rcases hV hWA (ScottOpenSet.sUnion_isSup (W '' A)) htarget with
    ⟨U, hU, hVU⟩
  rcases hU with ⟨g, hgA, rfl⟩
  refine ⟨g, hgA, ?_⟩
  intro x
  classical
  by_cases hx : x ∈ V
  · simp only [openStep_apply, if_pos hx]
    exact hVU hx
  · simp only [openStep_apply, if_neg hx]
    exact bot_le

/-- The Scott-open `↑↑u`, bundled as an element of the open-set order. -/
def wayBelowOpen (hX : IsDomain X) (u : X) : ScottOpenSet X :=
  ⟨wayBelowUpper u, scottOpen_wayBelowUpper hX.2.2 u⟩

/-- If `u ≪ v`, then `↑↑v ≪ ↑↑u` in the inclusion order on Scott opens. -/
theorem wayBelowOpen_wayBelow
    (hX : IsDomain X) {u v : X} (huv : u ≪ v) :
    wayBelowOpen hX v ≪ wayBelowOpen hX u := by
  intro 𝒰 s h𝒰 hs hUs
  have hvS : v ∈ s :=
    hUs huv
  have hsEq : s = ScottOpenSet.sUnion 𝒰 :=
    IsSup.unique hs (ScottOpenSet.sUnion_isSup 𝒰)
  have hvUnion : v ∈ ScottOpenSet.sUnion 𝒰 := by
    rw [← hsEq]
    exact hvS
  change v ∈ ⋃ U : 𝒰, (U.1 : Set X) at hvUnion
  rw [Set.mem_iUnion] at hvUnion
  rcases hvUnion with ⟨U, hvU⟩
  refine ⟨U.1, U.2, ?_⟩
  intro x hvx
  exact scottOpen_upper U.1.2 hvU (prop_2_2_2_1 hvx)

/-- The compact lower-layer singleton used by a finite requirement. -/
def requirementValue (u : X) : EX X :=
  EX.lower ({u} : Set X) (Or.inr (directed_singleton u))

theorem requirementValue_compact (u : X) :
    Compact (requirementValue u) :=
  EX.compact_lower (Or.inr (directed_singleton u))
    (Set.finite_singleton u)

/-- The manuscript's requirement map `S_{u,v}`. -/
noncomputable def requirementStep
    (hX : IsDomain X) (u v : X) :
    AbramskyJung.Chapter3.ContFun X (EX X) :=
  openStep (wayBelowOpen hX v) (requirementValue u)

@[simp]
theorem requirementStep_apply
    (hX : IsDomain X) (u v x : X) :
    requirementStep hX u v x =
      if v ≪ x then requirementValue u else ⊥ :=
  rfl

theorem compactPreimage_Q_requirement
    (hX : IsDomain X) (u : X) :
    compactPreimageOpen (Q hX) (requirementValue u)
        (requirementValue_compact u) =
      wayBelowOpen hX u := by
  apply ScottOpenSet.ext
  ext x
  constructor
  · intro hx
    change requirementValue u ≤ Q hX x at hx
    exact (EX.le_iff.mp hx).1 (by simp [requirementValue])
  · intro hux
    change requirementValue u ≤ Q hX x
    rw [EX.le_iff]
    refine ⟨?_, Bool.false_le _⟩
    intro a ha
    have hau : a = u := by simpa [requirementValue] using ha
    simpa [hau] using hux

/-- `lem:requirements-waybelow`: every finite requirement lies below `Q` in
the way-below relation of the function space. -/
theorem requirementStep_wayBelow_Q
    (hX : IsDomain X) {u v : X} (huv : u ≪ v) :
    requirementStep hX u v ≪ Q hX := by
  apply standardStep_wayBelow EX.isDcpoOrder
    (wayBelowOpen hX v) (requirementValue_compact u) (Q hX)
  rw [compactPreimage_Q_requirement hX u]
  exact wayBelowOpen_wayBelow hX huv

end RBFunctionSpace
