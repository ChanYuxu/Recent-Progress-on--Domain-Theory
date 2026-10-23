import ZFCFubini.ValuationMonad

/-!
# Tensorial strength on the actual cartesian category of dcpos

The general structure below is a strength of a categorical `Monad`, with
naturality, the two cartesian coherences, and compatibility with both monad
operations. The concrete morphism sends `(x, ν)` to the pushforward of `ν`
along `y ↦ (x,y)`. All products carry their intrinsic order Scott topology.
-/

set_option autoImplicit false
open Set Topology TopologicalSpace CategoryTheory
open CategoryTheory.MonoidalCategory
open scoped ENNReal Classical
universe u v

namespace ZFCFubini

/-- The usual five tensorial-strength diagrams for a genuine categorical monad. -/
structure CartesianMonadStrength {C : Type u} [Category.{v} C]
    [CartesianMonoidalCategory C] (T : CategoryTheory.Monad C) where
  σ : ∀ X Y : C, X ⊗ T.obj Y ⟶ T.obj (X ⊗ Y)
  naturality : ∀ {X X' Y Y' : C} (f : X ⟶ X') (g : Y ⟶ Y'),
    (f ⊗ₘ T.map g) ≫ σ X' Y' = σ X Y ≫ T.map (f ⊗ₘ g)
  left_unit : ∀ Y : C,
    σ (𝟙_ C) Y ≫ T.map (λ_ Y).hom = (λ_ (T.obj Y)).hom
  associator : ∀ X Y Z : C,
    (α_ X Y (T.obj Z)).hom ≫ (𝟙 X ⊗ₘ σ Y Z) ≫ σ X (Y ⊗ Z) =
      σ (X ⊗ Y) Z ≫ T.map (α_ X Y Z).hom
  unit : ∀ X Y : C,
    (𝟙 X ⊗ₘ T.η.app Y) ≫ σ X Y = T.η.app (X ⊗ Y)
  mul : ∀ X Y : C,
    (𝟙 X ⊗ₘ T.μ.app Y) ≫ σ X Y =
      σ X (T.obj Y) ≫ T.map (σ X Y) ≫ T.μ.app (X ⊗ Y)

namespace Valuation

variable {X : Type u} [TopologicalSpace X]

/-- Joint evaluation is Scott-continuous for the actual pointwise order. -/
theorem jointEvaluation_scottContinuous :
    ScottContinuous (fun z : SubprobValuation X × Opens X => z.1.val z.2) := by
  intro A hn hd p hp
  have hfst := (ScottContinuous.fst.comp
    (SubprobValuation.evaluation_scottContinuous p.2)) hn hd hp
  have hsnd : IsLUB (Prod.snd '' A) p.2 := ScottContinuous.snd hn hd hp
  have hopen : p.2 = sSup (Prod.snd '' A) := hsnd.unique (isLUB_sSup _)
  have hopenDir : DirectedOn (· ≤ ·) (Prod.snd '' A) := hd.mono_comp fun _ _ h => h.2
  constructor
  · rintro _ ⟨a, ha, rfl⟩
    exact ((hp.1 ha).1 a.2).trans (p.1.val.mono (hp.1 ha).2)
  · intro b hb
    apply hfst.2
    rintro _ ⟨a, ha, rfl⟩
    change a.1.val p.2 ≤ b
    rw [hopen, a.1.val.map_sSup (hn.image _) hopenDir]
    apply iSup_le
    intro U
    apply iSup_le
    rintro ⟨c, hc, rfl⟩
    obtain ⟨d, hdA, had, hcd⟩ := hd a ha c hc
    exact ((had.1 c.2).trans (d.1.val.mono hcd.2)).trans (hb ⟨d, hdA, rfl⟩)

end Valuation

namespace ValuationMonad

def openSection (P Q : DcpoCat.{u}) (U : ScottOpens (P × Q)) (p : P) : ScottOpens Q :=
  Opens.comap
    ⟨fun y => WithScott.toScott (p, WithScott.ofScott y),
      (scott_continuous_iff _).mp ((ScottContinuous.const p).prodMk ScottContinuous.id)⟩ U

@[simp] theorem mem_section (P Q : DcpoCat.{u}) (U : ScottOpens (P × Q)) (p : P) (q : Q) :
    WithScott.toScott q ∈ openSection P Q U p ↔ WithScott.toScott (p, q) ∈ U := Iff.rfl

theorem section_scottContinuous (P Q : DcpoCat.{u}) (U : ScottOpens (P × Q)) :
    ScottContinuous (openSection P Q U) := by
  intro A hn hd p hp
  have hU := (Topology.IsScott.isOpen_iff_isUpperSet_and_dirSupInaccOn
    (D := Set.univ)).mp U.isOpen
  constructor
  · rintro _ ⟨a, ha, rfl⟩ q hq
    exact hU.1 (show (a, WithScott.ofScott q) ≤ (p, WithScott.ofScott q) from
      ⟨hp.1 ha, le_rfl⟩) hq
  · intro V hV q hq
    have hpair : ScottContinuous (fun a : P => (a, WithScott.ofScott q)) :=
      ScottContinuous.id.prodMk (ScottContinuous.const _)
    obtain ⟨z, hz, hzU⟩ := hU.2 (Set.mem_univ _) (hn.image _)
      (hd.mono_comp hpair.monotone) (hpair hn hd hp) hq
    obtain ⟨a, ha, rfl⟩ := hz
    exact hV ⟨a, ha, rfl⟩ hzU

/-- Concrete tensorial strength, as an actual Scott-continuous morphism. -/
noncomputable def strengthHom (P Q : DcpoCat.{u}) : P ⊗ obj Q ⟶ obj (P ⊗ Q) :=
  ⟨fun z => z.2.push
      (fun y => WithScott.toScott (z.1, WithScott.ofScott y))
      ((scott_continuous_iff _).mp
        ((ScottContinuous.const z.1).prodMk ScottContinuous.id)), by
    apply SubprobValuation.scottContinuous_of_evaluation
    intro U
    exact (ScottContinuous.snd.prodMk
      (ScottContinuous.fst.comp (section_scottContinuous P Q U))).comp
        Valuation.jointEvaluation_scottContinuous⟩

@[simp] theorem strengthHom_apply (P Q : DcpoCat.{u}) (p : P) (ν : obj Q)
    (U : ScottOpens (P × Q)) :
    (strengthHom P Q (p, ν)).val U = ν.val (openSection P Q U p) := rfl

theorem strengthHom_naturality {P P' Q Q' : DcpoCat.{u}}
    (f : P ⟶ P') (g : Q ⟶ Q') :
    (f ⊗ₘ map g) ≫ strengthHom P' Q' = strengthHom P Q ≫ map (f ⊗ₘ g) := by
  apply DcpoCat.Hom.ext
  intro z
  apply Subtype.ext
  apply Valuation.ext
  intro U
  rfl

theorem strengthHom_left_unit (Q : DcpoCat.{u}) :
    strengthHom (𝟙_ DcpoCat.{u}) Q ≫ map (λ_ Q).hom = (λ_ (obj Q)).hom := by
  apply DcpoCat.Hom.ext
  intro z
  apply Subtype.ext
  apply Valuation.ext
  intro U
  rfl

theorem strengthHom_associator (P Q R : DcpoCat.{u}) :
    (α_ P Q (obj R)).hom ≫ (𝟙 P ⊗ₘ strengthHom Q R) ≫ strengthHom P (Q ⊗ R) =
      strengthHom (P ⊗ Q) R ≫ map (α_ P Q R).hom := by
  apply DcpoCat.Hom.ext
  intro z
  apply Subtype.ext
  apply Valuation.ext
  intro U
  rfl

theorem strengthHom_unit (P Q : DcpoCat.{u}) :
    (𝟙 P ⊗ₘ unit Q) ≫ strengthHom P Q = unit (P ⊗ Q) := by
  apply DcpoCat.Hom.ext
  intro z
  apply Subtype.ext
  apply Valuation.ext
  intro U
  simp only [DcpoCat.comp_apply, DcpoCat.tensorHom_apply]
  change Valuation.dirac (WithScott.toScott z.2) (openSection P Q U z.1) =
    Valuation.dirac (WithScott.toScott z) U
  simp only [Valuation.dirac_apply, mem_section]
  cases z
  rfl

noncomputable instance : BraidedCategory DcpoCat.{u} :=
  BraidedCategory.ofCartesianMonoidalCategory

@[simp] theorem braiding_hom_apply (P Q : DcpoCat.{u}) (z : P × Q) :
    (β_ P Q).hom z = (z.2, z.1) := rfl

end ValuationMonad

namespace CartesianMonadStrength

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
  [BraidedCategory C] {T : CategoryTheory.Monad C}

/-- Costrength is derived from the same strength using the cartesian braiding. -/
def costrength (S : CartesianMonadStrength T) (X Y : C) :
    T.obj X ⊗ Y ⟶ T.obj (X ⊗ Y) :=
  (β_ (T.obj X) Y).hom ≫ S.σ Y X ≫ T.map (β_ Y X).hom

/-- The first actual double-strength arrow, including categorical multiplication. -/
def doubleStrength (S : CartesianMonadStrength T) (X Y : C) :
    T.obj X ⊗ T.obj Y ⟶ T.obj (X ⊗ Y) :=
  S.costrength X (T.obj Y) ≫ T.map (S.σ X Y) ≫ T.μ.app (X ⊗ Y)

/-- The second actual double-strength arrow, in the opposite integration order. -/
def doubleStrength' (S : CartesianMonadStrength T) (X Y : C) :
    T.obj X ⊗ T.obj Y ⟶ T.obj (X ⊗ Y) :=
  S.σ (T.obj X) Y ≫ T.map (S.costrength X Y) ≫ T.μ.app (X ⊗ Y)

/-- Commutativity is equality of the two actual categorical morphisms. -/
def IsCommutative (S : CartesianMonadStrength T) : Prop :=
  ∀ X Y : C, S.doubleStrength X Y = S.doubleStrength' X Y

end CartesianMonadStrength
end ZFCFubini
