import Mathlib
import Mathlib.Data.Nat.Pairing

/-!
# Self-contained order theory for the FVA manuscript

This file is the order-theoretic foundation of the formalization of
`main (17).tex`.  Its import graph stops at Mathlib.  In particular it does not
import the surrounding Abramsky--Jung textbook development or any other paper
formalization.

For migration compatibility, the concrete declarations are provided in the
namespaces `AbramskyJung.Chapter2` and `AbramskyJung.Chapter3` used by the
existing manuscript modules.  These namespaces are defined locally in this
file; they are not aliases to external project modules.  A compact public view
is also exported as `FiniteValuationApproximable.OrderTheory` at the end.
-/

set_option autoImplicit false
set_option linter.unnecessarySimpa false

universe u v w

namespace AbramskyJung
namespace Chapter2

open Set

section Suprema

variable {α : Type u} [Preorder α]

/-- Upper-bound predicate. -/
def IsUpperBound (A : Set α) (x : α) : Prop :=
  ∀ ⦃a : α⦄, a ∈ A → a ≤ x

/-- Lower-bound predicate. -/
def IsLowerBound (A : Set α) (x : α) : Prop :=
  ∀ ⦃a : α⦄, a ∈ A → x ≤ a

/-- A specified supremum of a set. -/
def IsSup (A : Set α) (x : α) : Prop :=
  IsUpperBound A x ∧ ∀ y : α, IsUpperBound A y → x ≤ y

/-- A specified infimum of a set. -/
def IsInf (A : Set α) (x : α) : Prop :=
  IsLowerBound A x ∧ ∀ y : α, IsLowerBound A y → y ≤ x

/-- A least element without installing an `OrderBot` instance. -/
def IsLeast (x : α) : Prop :=
  ∀ y : α, x ≤ y

theorem IsSup.le_of_isSup {A : Set α} {x y : α}
    (hx : IsSup A x) (hy : IsSup A y) : x ≤ y :=
  hx.2 y hy.1

/-- Directed subsets are explicitly nonempty and pairwise upper directed. -/
def DirectedSet (A : Set α) : Prop :=
  A.Nonempty ∧ ∀ ⦃x : α⦄, x ∈ A → ∀ ⦃y : α⦄, y ∈ A →
    ∃ z ∈ A, x ≤ z ∧ y ≤ z

theorem directed_singleton (x : α) : DirectedSet ({x} : Set α) := by
  constructor
  · exact ⟨x, by simp⟩
  · intro a ha b hb
    have hax : a = x := by simpa using ha
    have hbx : b = x := by simpa using hb
    subst a
    subst b
    exact ⟨x, by simp⟩

theorem isSup_singleton (x : α) : IsSup ({x} : Set α) x := by
  constructor
  · intro a ha
    have hax : a = x := by simpa using ha
    subst a
    exact le_rfl
  · intro y hy
    exact hy (a := x) (by simp)

end Suprema

section AntisymmetricSuprema

variable {α : Type u} [PartialOrder α]

theorem IsSup.unique {A : Set α} {x y : α}
    (hx : IsSup A x) (hy : IsSup A y) : x = y :=
  le_antisymm (hx.2 y hy.1) (hy.2 x hx.1)

theorem IsInf.unique {A : Set α} {x y : α}
    (hx : IsInf A x) (hy : IsInf A y) : x = y :=
  le_antisymm (hy.2 x hx.1) (hx.2 y hy.1)

end AntisymmetricSuprema

section DirectedTools

variable {α : Type u} {β : Type v} [Preorder α] [Preorder β]

/-- A monotone image of a directed set is directed. -/
theorem DirectedSet.image {A : Set α} {f : α → β}
    (hf : Monotone f) (hA : DirectedSet A) : DirectedSet (f '' A) := by
  constructor
  · rcases hA.1 with ⟨a, ha⟩
    exact ⟨f a, ⟨a, ha, rfl⟩⟩
  · intro x hx y hy
    rcases hx with ⟨a, ha, rfl⟩
    rcases hy with ⟨b, hb, rfl⟩
    rcases hA.2 ha hb with ⟨c, hc, hac, hbc⟩
    exact ⟨f c, ⟨c, hc, rfl⟩, hf hac, hf hbc⟩

/-- A finite subset of a directed set has an upper bound in that set. -/
theorem DirectedSet.exists_upper_finite {A F : Set α}
    (hA : DirectedSet A) (hFfin : F.Finite) (hFsub : F ⊆ A) :
    ∃ z ∈ A, ∀ x ∈ F, x ≤ z := by
  induction F, hFfin using Set.Finite.induction_on with
  | empty =>
      rcases hA.1 with ⟨z, hz⟩
      exact ⟨z, hz, by intro x hx; cases hx⟩
  | @insert a F haF _ ih =>
      have hFsub' : F ⊆ A := fun _ hx => hFsub (by simp [hx])
      rcases ih hFsub' with ⟨z, hzA, hzF⟩
      have haA : a ∈ A := hFsub (by simp)
      rcases hA.2 haA hzA with ⟨w, hwA, haw, hzw⟩
      refine ⟨w, hwA, ?_⟩
      intro x hx
      rcases Set.mem_insert_iff.mp hx with rfl | hxF
      · exact haw
      · exact le_trans (hzF x hxF) hzw

/-- A finite directed set contains a greatest element and hence its supremum. -/
theorem DirectedSet.exists_isSup_of_finite {A : Set α}
    (hA : DirectedSet A) (hAfin : A.Finite) :
    ∃ z ∈ A, IsSup A z := by
  rcases hA.exists_upper_finite hAfin (fun _ hx => hx) with ⟨z, hzA, hz⟩
  exact ⟨z, hzA, ⟨hz, fun y hy => hy hzA⟩⟩

/-- Finitely many constraints, each bounded by some member of a directed set,
have one common upper bound in that directed set. -/
theorem DirectedSet.exists_upper_finite_of_forall {A F : Set α}
    (hA : DirectedSet A) (hFfin : F.Finite)
    (hF : ∀ x ∈ F, ∃ a ∈ A, x ≤ a) :
    ∃ z ∈ A, ∀ x ∈ F, x ≤ z := by
  induction F, hFfin using Set.Finite.induction_on with
  | empty =>
      rcases hA.1 with ⟨z, hz⟩
      exact ⟨z, hz, by intro x hx; cases hx⟩
  | @insert a F haF _ ih =>
      rcases hF a (by simp) with ⟨ua, huaA, haua⟩
      have hF' : ∀ x ∈ F, ∃ b ∈ A, x ≤ b :=
        fun x hx => hF x (by simp [hx])
      rcases ih hF' with ⟨uF, huFA, huF⟩
      rcases hA.2 huaA huFA with ⟨z, hzA, huaz, huFz⟩
      refine ⟨z, hzA, ?_⟩
      intro x hx
      rcases Set.mem_insert_iff.mp hx with rfl | hxF
      · exact le_trans haua huaz
      · exact le_trans (huF x hxF) huFz

/-- A recursive increasing sequence of upper bounds for a sequence in a
directed subset. -/
noncomputable def DirectedSet.cumulativeUpperSub {A : Set α}
    (hA : DirectedSet A) (u : Nat → α) (hu : ∀ n, u n ∈ A) :
    Nat → {x : α // x ∈ A}
  | 0 => ⟨u 0, hu 0⟩
  | n + 1 =>
      let hw := hA.2
        (cumulativeUpperSub hA u hu n).2 (hu (n + 1))
      ⟨Classical.choose hw, (Classical.choose_spec hw).1⟩

noncomputable def DirectedSet.cumulativeUpper {A : Set α}
    (hA : DirectedSet A) (u : Nat → α) (hu : ∀ n, u n ∈ A) : Nat → α :=
  fun n => (cumulativeUpperSub hA u hu n).1

theorem DirectedSet.cumulativeUpper_mem {A : Set α}
    (hA : DirectedSet A) (u : Nat → α) (hu : ∀ n, u n ∈ A) (n : Nat) :
    cumulativeUpper hA u hu n ∈ A :=
  (cumulativeUpperSub hA u hu n).2

theorem DirectedSet.cumulativeUpper_mono_step {A : Set α}
    (hA : DirectedSet A) (u : Nat → α) (hu : ∀ n, u n ∈ A) (n : Nat) :
    cumulativeUpper hA u hu n ≤ cumulativeUpper hA u hu (n + 1) := by
  unfold cumulativeUpper
  let hw := hA.2 (cumulativeUpperSub hA u hu n).2 (hu (n + 1))
  change (cumulativeUpperSub hA u hu n).1 ≤ Classical.choose hw
  exact (Classical.choose_spec hw).2.1

theorem DirectedSet.le_cumulativeUpper_self {A : Set α}
    (hA : DirectedSet A) (u : Nat → α) (hu : ∀ n, u n ∈ A) (n : Nat) :
    u n ≤ cumulativeUpper hA u hu n := by
  cases n with
  | zero => rfl
  | succ n =>
      unfold cumulativeUpper
      let hw := hA.2 (cumulativeUpperSub hA u hu n).2 (hu (n + 1))
      change u (n + 1) ≤ Classical.choose hw
      exact (Classical.choose_spec hw).2.2

theorem DirectedSet.cumulativeUpper_monotone {A : Set α}
    (hA : DirectedSet A) (u : Nat → α) (hu : ∀ n, u n ∈ A) :
    Monotone (cumulativeUpper hA u hu) := by
  exact monotone_nat_of_le_succ (cumulativeUpper_mono_step hA u hu)

end DirectedTools

section DcpoAndContinuousMaps

variable {α : Type u} {β : Type v} {γ : Type w}
variable [Preorder α] [Preorder β] [Preorder γ]

def IsAntisymmetricOrder (α : Type u) [Preorder α] : Prop :=
  ∀ x y : α, x ≤ y → y ≤ x → x = y

/-- Directed completeness of a preorder. -/
def IsDcpo (α : Type u) [Preorder α] : Prop :=
  ∀ A : Set α, DirectedSet A → ∃ x : α, IsSup A x

/-- A dcpo includes explicit antisymmetry. -/
def IsDcpoOrder (α : Type u) [Preorder α] : Prop :=
  IsDcpo α ∧ IsAntisymmetricOrder α

/-- Short compatibility name. -/
abbrev Dcpo (α : Type u) [Preorder α] : Prop := IsDcpoOrder α

theorem IsDcpoOrder.directedComplete (h : IsDcpoOrder α) : IsDcpo α := h.1
theorem IsDcpoOrder.antisymmetric (h : IsDcpoOrder α) : IsAntisymmetricOrder α := h.2

/-- Preservation of directed suprema. -/
def ScottContinuous (f : α → β) : Prop :=
  Monotone f ∧ ∀ ⦃A : Set α⦄ ⦃x : α⦄,
    DirectedSet A → IsSup A x → IsSup (f '' A) (f x)

theorem ScottContinuous.monotone {f : α → β} (hf : ScottContinuous f) :
    Monotone f := hf.1

theorem ScottContinuous.image_directed {f : α → β} (hf : ScottContinuous f)
    {A : Set α} (hA : DirectedSet A) : DirectedSet (f '' A) :=
  DirectedSet.image hf.1 hA

theorem ScottContinuous.maps_isSup {f : α → β} (hf : ScottContinuous f)
    {A : Set α} {x : α} (hA : DirectedSet A) (hx : IsSup A x) :
    IsSup (f '' A) (f x) := hf.2 hA hx

theorem scottContinuous_id : ScottContinuous (fun x : α => x) := by
  refine ⟨fun _ _ h => h, ?_⟩
  intro A x _ hx
  simpa using hx

theorem ScottContinuous.comp {f : β → γ} {g : α → β}
    (hf : ScottContinuous f) (hg : ScottContinuous g) :
    ScottContinuous (fun x => f (g x)) := by
  constructor
  · exact hf.1.comp hg.1
  · intro A x hA hx
    have hgs : IsSup (g '' A) (g x) := hg.2 hA hx
    have hfgs : IsSup (f '' (g '' A)) (f (g x)) :=
      hf.2 (DirectedSet.image hg.1 hA) hgs
    have himage : (fun a : α => f (g a)) '' A = f '' (g '' A) := by
      ext z
      constructor
      · rintro ⟨a, ha, rfl⟩
        exact ⟨g a, ⟨a, ha, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
        exact ⟨a, ha, rfl⟩
    simpa [himage] using hfgs

theorem const_scottContinuous (b : β) :
    ScottContinuous (fun _ : α => b) := by
  constructor
  · intro _ _ _
    exact le_rfl
  · intro A _ hA _
    have himage : (fun _ : α => b) '' A = ({b} : Set β) := by
      ext y
      constructor
      · rintro ⟨_, _, rfl⟩
        simp
      · intro hy
        have hyb : y = b := by simpa using hy
        rcases hA.1 with ⟨a, ha⟩
        exact ⟨a, ha, hyb.symm⟩
    simpa [himage] using isSup_singleton b

/-- Bundled Scott-continuous functions with pointwise order. -/
structure ScottContFun (α : Type u) (β : Type v) [Preorder α] [Preorder β] where
  toFun : α → β
  continuous : ScottContinuous toFun

namespace ScottContFun

instance : CoeFun (ScottContFun α β) (fun _ => α → β) := ⟨toFun⟩

instance : Preorder (ScottContFun α β) where
  le f g := ∀ x, f x ≤ g x
  le_refl _ _ := le_rfl
  le_trans _ _ _ hfg hgh x := le_trans (hfg x) (hgh x)

theorem ext_apply {f g : ScottContFun α β} (h : ∀ x, f x = g x) : f = g := by
  cases f with
  | mk f hf =>
      cases g with
      | mk g hg =>
          have : f = g := funext h
          subst this
          rfl

@[ext] theorem ext {f g : ScottContFun α β} (h : f.toFun = g.toFun) : f = g := by
  exact ext_apply fun x => congrFun h x

def comp (g : ScottContFun β γ) (f : ScottContFun α β) : ScottContFun α γ where
  toFun x := g (f x)
  continuous := g.continuous.comp f.continuous

@[simp] theorem comp_apply (g : ScottContFun β γ) (f : ScottContFun α β) (x : α) :
    comp g f x = g (f x) := rfl

theorem eval_directed {A : Set (ScottContFun α β)} (hA : DirectedSet A) (x : α) :
    DirectedSet ((fun f : ScottContFun α β => f x) '' A) :=
  DirectedSet.image (A := A) (f := fun f : ScottContFun α β => f x)
    (by intro f g hfg; exact hfg x) hA

noncomputable def directedSupFun (hβ : IsDcpo β)
    (A : Set (ScottContFun α β)) (hA : DirectedSet A) : α → β :=
  fun x => Classical.choose (hβ _ (eval_directed hA x))

theorem directedSupFun_isSup_eval (hβ : IsDcpo β)
    (A : Set (ScottContFun α β)) (hA : DirectedSet A) (x : α) :
    IsSup ((fun f : ScottContFun α β => f x) '' A)
      (directedSupFun hβ A hA x) :=
  Classical.choose_spec (hβ _ (eval_directed hA x))

theorem directedSupFun_monotone (hβ : IsDcpo β)
    (A : Set (ScottContFun α β)) (hA : DirectedSet A) :
    Monotone (directedSupFun hβ A hA) := by
  intro x y hxy
  exact (directedSupFun_isSup_eval hβ A hA x).2 _ (by
    rintro _ ⟨f, hf, rfl⟩
    exact le_trans (f.continuous.monotone hxy)
      ((directedSupFun_isSup_eval hβ A hA y).1 ⟨f, hf, rfl⟩))

theorem directedSupFun_scottContinuous (hβ : IsDcpo β)
    (A : Set (ScottContFun α β)) (hA : DirectedSet A) :
    ScottContinuous (directedSupFun hβ A hA) := by
  constructor
  · exact directedSupFun_monotone hβ A hA
  · intro B s hB hs
    constructor
    · rintro _ ⟨b, hb, rfl⟩
      exact directedSupFun_monotone hβ A hA (hs.1 hb)
    · intro y hy
      exact (directedSupFun_isSup_eval hβ A hA s).2 y (by
        rintro _ ⟨f, hf, rfl⟩
        exact (f.continuous.maps_isSup hB hs).2 y (by
          rintro _ ⟨b, hb, rfl⟩
          exact le_trans
            ((directedSupFun_isSup_eval hβ A hA b).1 ⟨f, hf, rfl⟩)
            (hy ⟨b, hb, rfl⟩)))

noncomputable def directedSup (hβ : IsDcpo β)
    (A : Set (ScottContFun α β)) (hA : DirectedSet A) : ScottContFun α β where
  toFun := directedSupFun hβ A hA
  continuous := directedSupFun_scottContinuous hβ A hA

theorem directedSup_isSup (hβ : IsDcpo β)
    (A : Set (ScottContFun α β)) (hA : DirectedSet A) :
    IsSup A (directedSup hβ A hA) := by
  constructor
  · intro f hf x
    exact (directedSupFun_isSup_eval hβ A hA x).1 ⟨f, hf, rfl⟩
  · intro g hg x
    exact (directedSupFun_isSup_eval hβ A hA x).2 (g x) (by
      rintro _ ⟨f, hf, rfl⟩
      exact hg hf x)

theorem isDcpo_of_codomain (hβ : IsDcpo β) : IsDcpo (ScottContFun α β) :=
  fun A hA => ⟨directedSup hβ A hA, directedSup_isSup hβ A hA⟩

theorem eval_scottContinuous (hβ : IsDcpo β) (x : α) :
    ScottContinuous (fun f : ScottContFun α β => f x) := by
  constructor
  · intro f g hfg
    exact hfg x
  · intro A s hA hs
    constructor
    · rintro _ ⟨f, hf, rfl⟩
      exact hs.1 hf x
    · intro y hy
      have hpoint := directedSupFun_isSup_eval hβ A hA x
      exact le_trans ((hs.2 (directedSup hβ A hA)
        (directedSup_isSup hβ A hA).1) x) (hpoint.2 y hy)

end ScottContFun

end DcpoAndContinuousMaps

section WayBelowAndBases

variable {α : Type u} [Preorder α]

/-- Way-below relation. -/
def WayBelow (x y : α) : Prop :=
  ∀ ⦃A : Set α⦄ ⦃s : α⦄,
    DirectedSet A → IsSup A s → y ≤ s → ∃ a ∈ A, x ≤ a

infix:50 " ≪ " => WayBelow

def wayBelowLower (x : α) : Set α := {y | y ≪ x}
def Approximants (B : Set α) (x : α) : Set α := {b | b ∈ B ∧ b ≪ x}

theorem prop_2_2_2_1 {x y : α} (h : x ≪ y) : x ≤ y := by
  rcases h (directed_singleton y) (isSup_singleton y) le_rfl with ⟨a, ha, hxa⟩
  simpa using hxa.trans_eq (by simpa using ha)

theorem prop_2_2_2_2 {x x' y y' : α}
    (hx : x' ≤ x) (hxy : x ≪ y) (hy : y ≤ y') : x' ≪ y' := by
  intro A s hA hs hys
  rcases hxy hA hs (hy.trans hys) with ⟨a, ha, hxa⟩
  exact ⟨a, ha, hx.trans hxa⟩

def IsBasisRaw (B : Set α) : Prop :=
  ∀ x, ∃ A : Set α, A ⊆ Approximants B x ∧ DirectedSet A ∧ IsSup A x

def IsBasis (B : Set α) : Prop :=
  ∀ x, DirectedSet (Approximants B x) ∧ IsSup (Approximants B x) x

theorem basis_to_raw {B : Set α} (hB : IsBasis B) : IsBasisRaw B :=
  fun x => ⟨Approximants B x, fun _ h => h, (hB x).1, (hB x).2⟩

theorem prop_2_2_4_1 {B : Set α} (hB : IsBasisRaw B) : IsBasis B := by
  intro x
  rcases hB x with ⟨A, hAsub, hAdir, hAsup⟩
  constructor
  · constructor
    · rcases hAdir.1 with ⟨a, ha⟩
      exact ⟨a, hAsub ha⟩
    · intro b hb c hc
      rcases hb.2 hAdir hAsup le_rfl with ⟨a, ha, hba⟩
      rcases hc.2 hAdir hAsup le_rfl with ⟨a', ha', hca'⟩
      rcases hAdir.2 ha ha' with ⟨z, hz, haz, ha'z⟩
      exact ⟨z, hAsub hz, hba.trans haz, hca'.trans ha'z⟩
  · constructor
    · intro b hb
      exact prop_2_2_2_1 hb.2
    · intro y hy
      exact hAsup.2 y (fun _ ha => hy (hAsub ha))

theorem cor_2_2_5_1 {B : Set α} (hB : IsBasisRaw B) :
    IsBasisRaw (Set.univ : Set α) := by
  intro x
  rcases hB x with ⟨A, hA, hdir, hsup⟩
  exact ⟨A, fun a ha => ⟨Set.mem_univ a, (hA ha).2⟩, hdir, hsup⟩

def IsContinuousDomain (α : Type u) [Preorder α] : Prop :=
  ∃ B : Set α, IsBasisRaw B

def IsOmegaContinuousDomain (α : Type u) [Preorder α] : Prop :=
  ∃ B : Set α, B.Countable ∧ IsBasisRaw B

def IsContinuousDcpo (α : Type u) [Preorder α] : Prop :=
  IsDcpoOrder α ∧ IsContinuousDomain α

def IsOmegaContinuousDcpo (α : Type u) [Preorder α] : Prop :=
  IsDcpoOrder α ∧ IsOmegaContinuousDomain α

theorem IsContinuousDcpo.toIsDcpoOrder (h : IsContinuousDcpo α) :
    IsDcpoOrder α := h.1

theorem IsContinuousDcpo.hasBasis (h : IsContinuousDcpo α) :
    IsContinuousDomain α := h.2

theorem prop_2_2_7_1 :
    IsContinuousDomain α ↔ IsBasis (Set.univ : Set α) := by
  constructor
  · rintro ⟨B, hB⟩
    exact prop_2_2_4_1 (cor_2_2_5_1 hB)
  · intro h
    exact ⟨Set.univ, basis_to_raw h⟩

theorem continuous_wayBelowLower_directed
    (hD : IsContinuousDomain α) (x : α) : DirectedSet (wayBelowLower x) := by
  have hB := (prop_2_2_7_1.mp hD x).1
  simpa only [Approximants, Set.mem_univ, true_and] using hB

theorem continuous_wayBelowLower_isSup
    (hD : IsContinuousDomain α) (x : α) : IsSup (wayBelowLower x) x := by
  have hB := (prop_2_2_7_1.mp hD x).2
  simpa only [Approximants, Set.mem_univ, true_and] using hB

def twoStepApproximants (x : α) : Set α :=
  {a | ∃ b, a ≪ b ∧ b ≪ x}

theorem continuous_twoStepApproximants_directed
    (hD : IsContinuousDomain α) (x : α) :
    DirectedSet (twoStepApproximants x) := by
  have hxdir := continuous_wayBelowLower_directed hD x
  constructor
  · rcases hxdir.1 with ⟨b, hbx⟩
    rcases (continuous_wayBelowLower_directed hD b).1 with ⟨a, hab⟩
    exact ⟨a, b, hab, hbx⟩
  · rintro a ⟨a', haa', ha'x⟩ c ⟨c', hcc', hc'x⟩
    rcases hxdir.2 ha'x hc'x with ⟨b, hbx, ha'b, hc'b⟩
    have hab : a ≪ b := prop_2_2_2_2 le_rfl haa' ha'b
    have hcb : c ≪ b := prop_2_2_2_2 le_rfl hcc' hc'b
    have hbdir := continuous_wayBelowLower_directed hD b
    have hbsup := continuous_wayBelowLower_isSup hD b
    rcases hab hbdir hbsup le_rfl with ⟨ua, hua, haua⟩
    rcases hcb hbdir hbsup le_rfl with ⟨uc, huc, hcuc⟩
    rcases hbdir.2 hua huc with ⟨d, hdb, huad, hucd⟩
    exact ⟨d, ⟨b, hdb, hbx⟩, haua.trans huad, hcuc.trans hucd⟩

theorem continuous_twoStepApproximants_isSup
    (hD : IsContinuousDomain α) (x : α) : IsSup (twoStepApproximants x) x := by
  have hxsup := continuous_wayBelowLower_isSup hD x
  constructor
  · rintro a ⟨b, hab, hbx⟩
    exact (prop_2_2_2_1 hab).trans (prop_2_2_2_1 hbx)
  · intro y hy
    exact hxsup.2 y (by
      intro b hbx
      exact (continuous_wayBelowLower_isSup hD b).2 y (by
        intro a hab
        exact hy ⟨b, hab, hbx⟩))

theorem wayBelow_interpolation
    (hD : IsContinuousDomain α) {x y : α} (hxy : x ≪ y) :
    ∃ z, x ≪ z ∧ z ≪ y := by
  rcases hxy (continuous_twoStepApproximants_directed hD y)
      (continuous_twoStepApproximants_isSup hD y) le_rfl with
    ⟨a, ⟨z, haz, hzy⟩, hxa⟩
  exact ⟨z, prop_2_2_2_2 hxa haz le_rfl, hzy⟩

theorem lemma_2_2_15_interpolation
    (hD : IsContinuousDomain α) {M : Set α} {y : α}
    (hMfin : M.Finite) (hMy : ∀ m ∈ M, m ≪ y) :
    ∃ y', (∀ m ∈ M, m ≪ y') ∧ y' ≪ y := by
  classical
  have hdir := continuous_wayBelowLower_directed hD y
  rcases hdir.1 with ⟨default, hdefault⟩
  have hChoice : ∀ m ∈ M, ∃ a ∈ wayBelowLower y, m ≪ a := by
    intro m hm
    rcases wayBelow_interpolation hD (hMy m hm) with ⟨a, hma, hay⟩
    exact ⟨a, hay, hma⟩
  let pick : α → α := fun m =>
    if hm : m ∈ M then Classical.choose (hChoice m hm) else default
  have hpick_mem : ∀ m ∈ M, pick m ∈ wayBelowLower y := by
    intro m hm
    simp [pick, hm, (Classical.choose_spec (hChoice m hm)).1]
  have hpick_way : ∀ m ∈ M, m ≪ pick m := by
    intro m hm
    simp [pick, hm, (Classical.choose_spec (hChoice m hm)).2]
  have hFfin : (pick '' M).Finite := hMfin.image pick
  have hFsub : pick '' M ⊆ wayBelowLower y := by
    rintro _ ⟨m, hm, rfl⟩
    exact hpick_mem m hm
  rcases hdir.exists_upper_finite hFfin hFsub with ⟨y', hy', hupper⟩
  exact ⟨y', fun m hm => prop_2_2_2_2 le_rfl (hpick_way m hm)
    (hupper (pick m) ⟨m, hm, rfl⟩), hy'⟩

end WayBelowAndBases

end Chapter2
end AbramskyJung

namespace AbramskyJung
namespace Chapter3

open Set

abbrev IsUpperBound {α : Type u} [Preorder α] := Chapter2.IsUpperBound (α := α)
abbrev IsLowerBound {α : Type u} [Preorder α] := Chapter2.IsLowerBound (α := α)
abbrev IsSup {α : Type u} [Preorder α] := Chapter2.IsSup (α := α)
abbrev IsInf {α : Type u} [Preorder α] := Chapter2.IsInf (α := α)
abbrev DirectedSet {α : Type u} [Preorder α] := Chapter2.DirectedSet (α := α)
abbrev IsDcpo (α : Type u) [Preorder α] := Chapter2.IsDcpo α
abbrev ScottContinuous {α : Type u} {β : Type v} [Preorder α] [Preorder β] :=
  Chapter2.ScottContinuous (α := α) (β := β)
abbrev WayBelow {α : Type u} [Preorder α] := Chapter2.WayBelow (α := α)
abbrev Approximants {α : Type u} [Preorder α] := Chapter2.Approximants (α := α)
abbrev IsBasis {α : Type u} [Preorder α] := Chapter2.IsBasis (α := α)
abbrev IsContinuousDomain (α : Type u) [Preorder α] := Chapter2.IsContinuousDomain α

section Products

variable {D : Type u} {E : Type v} {F : Type w}
variable [Preorder D] [Preorder E] [Preorder F]

/-- Projected suprema assemble into a product supremum. -/
theorem prod_isSup_of_projection_isSup {A : Set (D × E)} {d : D} {e : E}
    (hd : IsSup (Prod.fst '' A) d) (he : IsSup (Prod.snd '' A) e) :
    IsSup A (d, e) := by
  constructor
  · intro p hp
    exact ⟨hd.1 ⟨p, hp, rfl⟩, he.1 ⟨p, hp, rfl⟩⟩
  · intro z hz
    constructor
    · exact hd.2 z.1 (by
        rintro _ ⟨p, hp, rfl⟩
        exact (hz hp).1)
    · exact he.2 z.2 (by
        rintro _ ⟨p, hp, rfl⟩
        exact (hz hp).2)

theorem prod_fst_isSup {A : Set (D × E)} {s : D × E} (hs : IsSup A s) :
    IsSup (Prod.fst '' A) s.1 := by
  constructor
  · rintro _ ⟨p, hp, rfl⟩
    exact (hs.1 hp).1
  · intro z hz
    exact (hs.2 (z, s.2) (fun p hp => ⟨hz ⟨p, hp, rfl⟩, (hs.1 hp).2⟩)).1

theorem prod_snd_isSup {A : Set (D × E)} {s : D × E} (hs : IsSup A s) :
    IsSup (Prod.snd '' A) s.2 := by
  constructor
  · rintro _ ⟨p, hp, rfl⟩
    exact (hs.1 hp).2
  · intro z hz
    exact (hs.2 (s.1, z) (fun p hp => ⟨(hs.1 hp).1, hz ⟨p, hp, rfl⟩⟩)).2

theorem prod_fst_scottContinuous :
    ScottContinuous (fun p : D × E => p.1) := by
  constructor
  · intro _ _ h
    exact h.1
  · intro A s _ hs
    exact prod_fst_isSup hs

theorem prod_snd_scottContinuous :
    ScottContinuous (fun p : D × E => p.2) := by
  constructor
  · intro _ _ h
    exact h.2
  · intro A s _ hs
    exact prod_snd_isSup hs

theorem prod_pair_scottContinuous {f : F → D} {g : F → E}
    (hf : ScottContinuous f) (hg : ScottContinuous g) :
    ScottContinuous (fun x => (f x, g x)) := by
  constructor
  · intro x y hxy
    exact ⟨hf.monotone hxy, hg.monotone hxy⟩
  · intro A s hA hs
    have hfs := hf.maps_isSup hA hs
    have hgs := hg.maps_isSup hA hs
    constructor
    · rintro _ ⟨a, ha, rfl⟩
      exact ⟨hfs.1 ⟨a, ha, rfl⟩, hgs.1 ⟨a, ha, rfl⟩⟩
    · intro z hz
      constructor
      · exact hfs.2 z.1 (by
          rintro _ ⟨a, ha, rfl⟩
          exact (hz ⟨a, ha, rfl⟩).1)
      · exact hgs.2 z.2 (by
          rintro _ ⟨a, ha, rfl⟩
          exact (hz ⟨a, ha, rfl⟩).2)

/-- Product of Scott-continuous maps. -/
theorem prod_map_scottContinuous
    {D' : Type u} {E' : Type v} [Preorder D'] [Preorder E']
    {f : D → D'} {g : E → E'}
    (hf : ScottContinuous f) (hg : ScottContinuous g) :
    ScottContinuous (fun p : D × E => (f p.1, g p.2)) :=
  prod_pair_scottContinuous
    (hf.comp prod_fst_scottContinuous) (hg.comp prod_snd_scottContinuous)

/-- Compatibility spelling requested by the manuscript's product layer. -/
theorem prodMap_scottContinuous
    {D' : Type u} {E' : Type v} [Preorder D'] [Preorder E']
    {f : D → D'} {g : E → E'}
    (hf : ScottContinuous f) (hg : ScottContinuous g) :
    ScottContinuous (fun p : D × E => (f p.1, g p.2)) :=
  prod_map_scottContinuous hf hg

theorem directed_prod {A : Set D} {B : Set E}
    (hA : DirectedSet A) (hB : DirectedSet B) :
    DirectedSet ({p : D × E | p.1 ∈ A ∧ p.2 ∈ B} : Set (D × E)) := by
  constructor
  · rcases hA.1 with ⟨a, ha⟩
    rcases hB.1 with ⟨b, hb⟩
    exact ⟨(a, b), ha, hb⟩
  · intro x hx y hy
    rcases hA.2 hx.1 hy.1 with ⟨a, ha, hxa, hya⟩
    rcases hB.2 hx.2 hy.2 with ⟨b, hb, hxb, hyb⟩
    exact ⟨(a, b), ⟨ha, hb⟩, ⟨hxa, hxb⟩, ⟨hya, hyb⟩⟩

/-- Products of dcpos are dcpos, with coordinatewise directed suprema. -/
theorem prod_isDcpo (hD : IsDcpo D) (hE : IsDcpo E) : IsDcpo (D × E) := by
  intro A hA
  have hfst : DirectedSet (Prod.fst '' A) :=
    Chapter2.DirectedSet.image (A := A) (f := fun p : D × E => p.1)
      (by intro p q hpq; exact hpq.1) hA
  have hsnd : DirectedSet (Prod.snd '' A) :=
    Chapter2.DirectedSet.image (A := A) (f := fun p : D × E => p.2)
      (by intro p q hpq; exact hpq.2) hA
  rcases hD _ hfst with ⟨d, hd⟩
  rcases hE _ hsnd with ⟨e, he⟩
  exact ⟨(d, e), prod_isSup_of_projection_isSup hd he⟩

/-- Coordinatewise way-below elements form a way-below pair. -/
theorem prod_wayBelow_of {d d' : D} {e e' : E}
    (hd : Chapter2.WayBelow d d') (he : Chapter2.WayBelow e e') :
    Chapter2.WayBelow (d, e) (d', e') := by
  intro A s hA hs hle
  rcases hd (Chapter2.DirectedSet.image (A := A)
      (f := fun p : D × E => p.1) (by intro p q hpq; exact hpq.1) hA)
      (prod_fst_isSup hs) hle.1 with ⟨_, ⟨p, hp, rfl⟩, hdp⟩
  rcases he (Chapter2.DirectedSet.image (A := A)
      (f := fun p : D × E => p.2) (by intro p q hpq; exact hpq.2) hA)
      (prod_snd_isSup hs) hle.2 with ⟨_, ⟨q, hq, rfl⟩, heq⟩
  rcases hA.2 hp hq with ⟨r, hr, hpr, hqr⟩
  exact ⟨r, hr, hdp.trans hpr.1, heq.trans hqr.2⟩

def ProdBasis (B : Set D) (C : Set E) : Set (D × E) :=
  {p | p.1 ∈ B ∧ p.2 ∈ C}

/-- The product of two continuous domains is continuous.  This proof works
directly with the manuscript's raw-basis definition. -/
theorem prod_continuous_domain
    (hD : IsContinuousDomain D) (hE : IsContinuousDomain E) :
    IsContinuousDomain (D × E) := by
  rcases hD with ⟨B, hB⟩
  rcases hE with ⟨C, hC⟩
  refine ⟨ProdBasis B C, ?_⟩
  intro p
  rcases hB p.1 with ⟨A, hAsub, hAdir, hAsup⟩
  rcases hC p.2 with ⟨K, hKsub, hKdir, hKsup⟩
  let T : Set (D × E) := {q | q.1 ∈ A ∧ q.2 ∈ K}
  refine ⟨T, ?_, directed_prod hAdir hKdir, ?_⟩
  · intro q hq
    have hqa := hAsub hq.1
    have hqk := hKsub hq.2
    exact ⟨⟨hqa.1, hqk.1⟩, prod_wayBelow_of hqa.2 hqk.2⟩
  · constructor
    · intro q hq
      exact ⟨hAsup.1 hq.1, hKsup.1 hq.2⟩
    · intro z hz
      constructor
      · exact hAsup.2 z.1 (by
          intro a ha
          rcases hKdir.1 with ⟨k, hk⟩
          exact (hz (a := (a, k)) ⟨ha, hk⟩).1)
      · exact hKsup.2 z.2 (by
          intro k hk
          rcases hAdir.1 with ⟨a, ha⟩
          exact (hz (a := (a, k)) ⟨ha, hk⟩).2)

end Products

section Retractions

variable {D : Type u} {E : Type v} [Preorder D] [Preorder E]

structure SectionRetractionPair
    (D : Type u) (E : Type v) [Preorder D] [Preorder E] where
  s : D → E
  r : E → D
  monotone_s : Monotone s
  monotone_r : Monotone r
  retract : ∀ x, r (s x) = x

namespace SectionRetractionPair

theorem isDcpo_of_isDcpo (sr : SectionRetractionPair D E)
    (hE : IsDcpo E) : IsDcpo D := by
  intro A hA
  have hsdir : DirectedSet (sr.s '' A) :=
    Chapter2.DirectedSet.image sr.monotone_s hA
  rcases hE _ hsdir with ⟨e, he⟩
  refine ⟨sr.r e, ?_⟩
  constructor
  · intro a ha
    calc
      a = sr.r (sr.s a) := (sr.retract a).symm
      _ ≤ sr.r e := sr.monotone_r (he.1 ⟨a, ha, rfl⟩)
  · intro d hd
    calc
      sr.r e ≤ sr.r (sr.s d) := sr.monotone_r (he.2 (sr.s d) (by
        rintro _ ⟨a, ha, rfl⟩
        exact sr.monotone_s (hd ha)))
      _ = d := sr.retract d

end SectionRetractionPair

structure ContinuousSectionRetractionPair
    (D : Type u) (E : Type v) [Preorder D] [Preorder E]
    extends SectionRetractionPair D E where
  continuous_s : ScottContinuous s
  continuous_r : ScottContinuous r

namespace ContinuousSectionRetractionPair

theorem wayBelow_retract (sr : ContinuousSectionRetractionPair D E)
    {b : E} {x : D} (hbx : Chapter2.WayBelow b (sr.s x)) :
    Chapter2.WayBelow (sr.r b) x := by
  intro A t hA ht hxt
  have hsdir : DirectedSet (sr.s '' A) :=
    Chapter2.DirectedSet.image sr.monotone_s hA
  have hssup : IsSup (sr.s '' A) (sr.s t) :=
    sr.continuous_s.maps_isSup hA ht
  rcases hbx hsdir hssup (sr.monotone_s hxt) with
    ⟨_, ⟨a, ha, rfl⟩, hba⟩
  exact ⟨a, ha, by
    calc
      sr.r b ≤ sr.r (sr.s a) := sr.monotone_r hba
      _ = a := sr.retract a⟩

/-- Raw bases are transported by a continuous retraction. -/
theorem retraction_image_basisRaw
    (sr : ContinuousSectionRetractionPair D E) {B : Set E}
    (hB : Chapter2.IsBasisRaw B) :
    Chapter2.IsBasisRaw (sr.r '' B) := by
  intro x
  rcases hB (sr.s x) with ⟨A, hAsub, hAdir, hAsup⟩
  refine ⟨sr.r '' A, ?_, Chapter2.DirectedSet.image sr.monotone_r hAdir, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩
    have haa := hAsub ha
    exact ⟨⟨a, haa.1, rfl⟩, sr.wayBelow_retract haa.2⟩
  · have hrsup := sr.continuous_r.maps_isSup hAdir hAsup
    simpa [sr.retract x] using hrsup

end ContinuousSectionRetractionPair

/-- Continuous retracts preserve continuous dcpos. -/
theorem theorem_3_1_4_retract_continuous_domain
    (sr : ContinuousSectionRetractionPair D E)
    (hE : Chapter2.IsContinuousDcpo E) : Chapter2.IsContinuousDcpo D := by
  refine ⟨⟨sr.toSectionRetractionPair.isDcpo_of_isDcpo hE.1.1, ?_⟩, ?_⟩
  · intro x y hxy hyx
    have hsxy : sr.s x = sr.s y := hE.1.2 _ _
      (sr.monotone_s hxy) (sr.monotone_s hyx)
    calc
      x = sr.r (sr.s x) := (sr.retract x).symm
      _ = sr.r (sr.s y) := congrArg sr.r hsxy
      _ = y := sr.retract y
  · rcases hE.2 with ⟨B, hB⟩
    exact ⟨sr.r '' B, sr.retraction_image_basisRaw hB⟩

/-- Basis-only form of the same theorem. -/
theorem theorem_3_1_4_retract_continuous_domain_basis
    (sr : ContinuousSectionRetractionPair D E)
    (hE : Chapter2.IsContinuousDomain E) : Chapter2.IsContinuousDomain D := by
  rcases hE with ⟨B, hB⟩
  exact ⟨sr.r '' B, sr.retraction_image_basisRaw hB⟩

def HasLeastElement (D : Type u) [Preorder D] : Prop :=
  ∃ b : D, Chapter2.IsLeast b

end Retractions

/-! The Chapter 3 function-space spelling is definitionally the same local
bundled map as the Chapter 2 spelling. -/

abbrev ContFun (D : Type u) (E : Type v) [Preorder D] [Preorder E] :=
  Chapter2.ScottContFun D E

namespace ContFun

variable {D : Type u} {E : Type v} {F : Type w}
variable [Preorder D] [Preorder E] [Preorder F]

abbrev comp (g : ContFun E F) (f : ContFun D E) : ContFun D F :=
  Chapter2.ScottContFun.comp g f

theorem ext_apply {f g : ContFun D E} (h : ∀ x, f x = g x) : f = g :=
  Chapter2.ScottContFun.ext_apply h

theorem isDcpo_of_codomain (hE : IsDcpo E) : IsDcpo (ContFun D E) :=
  Chapter2.ScottContFun.isDcpo_of_codomain hE

theorem eval_scottContinuous (hE : IsDcpo E) (d : D) :
    ScottContinuous (fun f : ContFun D E => f d) :=
  Chapter2.ScottContFun.eval_scottContinuous hE d

end ContFun

end Chapter3
end AbramskyJung

namespace FiniteValuationApproximable
namespace OrderTheory

abbrev DirectedSet {α : Type u} [Preorder α] :=
  AbramskyJung.Chapter2.DirectedSet (α := α)
abbrev IsSup {α : Type u} [Preorder α] :=
  AbramskyJung.Chapter2.IsSup (α := α)
abbrev IsDcpo (α : Type u) [Preorder α] := AbramskyJung.Chapter2.IsDcpo α
abbrev IsDcpoOrder (α : Type u) [Preorder α] := AbramskyJung.Chapter2.IsDcpoOrder α
abbrev WayBelow {α : Type u} [Preorder α] := AbramskyJung.Chapter2.WayBelow (α := α)
abbrev Approximants {α : Type u} [Preorder α] :=
  AbramskyJung.Chapter2.Approximants (α := α)
abbrev IsBasisRaw {α : Type u} [Preorder α] :=
  AbramskyJung.Chapter2.IsBasisRaw (α := α)
abbrev IsBasis {α : Type u} [Preorder α] := AbramskyJung.Chapter2.IsBasis (α := α)
abbrev IsContinuousDomain (α : Type u) [Preorder α] :=
  AbramskyJung.Chapter2.IsContinuousDomain α
abbrev IsContinuousDcpo (α : Type u) [Preorder α] :=
  AbramskyJung.Chapter2.IsContinuousDcpo α
abbrev IsOmegaContinuousDomain (α : Type u) [Preorder α] :=
  AbramskyJung.Chapter2.IsOmegaContinuousDomain α
abbrev IsOmegaContinuousDcpo (α : Type u) [Preorder α] :=
  AbramskyJung.Chapter2.IsOmegaContinuousDcpo α
abbrev ScottContinuous {α : Type u} {β : Type v} [Preorder α] [Preorder β] :=
  AbramskyJung.Chapter2.ScottContinuous (α := α) (β := β)
abbrev ScottContFun (α : Type u) (β : Type v) [Preorder α] [Preorder β] :=
  AbramskyJung.Chapter2.ScottContFun α β
abbrev ContinuousSectionRetractionPair
    (α : Type u) (β : Type v) [Preorder α] [Preorder β] :=
  AbramskyJung.Chapter3.ContinuousSectionRetractionPair α β

end OrderTheory
end FiniteValuationApproximable
