import CantorFubini.ValuationDcpo

/-! The genuine cartesian strength of the subprobability valuation functor.
Its Scott continuity uses section continuity for the intrinsic order product,
not an identification of Scott and ordinary product topologies. -/

set_option autoImplicit false
open Set Topology TopologicalSpace CategoryTheory
open scoped ENNReal Classical MonoidalCategory
universe u v

namespace CantorFubini
namespace SubprobValuation

theorem jointEvaluation_scottContinuous {X : Type u} [TopologicalSpace X] :
    ScottContinuous (fun z : Opens X × SubprobValuation X => z.2.val z.1) := by
  intro S hn hd p hp
  have hU : IsLUB (Prod.fst '' S) p.1 := ScottContinuous.fst hn hd hp
  have hμ : IsLUB (Prod.snd '' S) p.2 := ScottContinuous.snd hn hd hp
  have hdU : DirectedOn (· ≤ ·) (Prod.fst '' S) :=
    directedOn_image.mpr (hd.mono (fun {_ _} h => h.1))
  have hdμ : DirectedOn (· ≤ ·) (Prod.snd '' S) :=
    directedOn_image.mpr (hd.mono (fun {_ _} h => h.2))
  constructor
  · rintro a ⟨z, hz, rfl⟩
    exact ((z.2.val.mono (hp.1 hz).1).trans ((hp.1 hz).2 p.1))
  · intro a ha
    apply (evaluation_scottContinuous p.1 (hn.image Prod.snd) hdμ hμ).2
    rintro b ⟨μ, ⟨s, hs, rfl⟩, rfl⟩
    apply (s.2.val.continuous (hn.image Prod.fst) hdU hU).2
    rintro c ⟨U, ⟨t, ht, rfl⟩, rfl⟩
    obtain ⟨z, hz, hsz, htz⟩ := hd s hs t ht
    exact ((s.2.val.mono htz.1).trans (hsz.2 z.1)).trans (ha (mem_image_of_mem _ hz))

end SubprobValuation

namespace DCPO

def insertLeft (D E : DCPO.{u}) (x : D) : E ⟶ prod D E :=
  hom (fun y => (x, y)) ((ScottContinuous.const x).prodMk ScottContinuous.id)

def insertRight (D E : DCPO.{u}) (y : E) : D ⟶ prod D E :=
  hom (fun x => (x, y)) (ScottContinuous.id.prodMk (ScottContinuous.const y))

def leftSection {D E : DCPO.{u}} (U : ScottOpens (prod D E)) (x : D) : ScottOpens E :=
  Opens.comap ⟨fun y : WithScott E => WithScott.toScott (x, WithScott.ofScott y),
    ((scott_continuous_iff (insertLeft D E x)).mp (hom_scottContinuous _))⟩ U

@[simp] theorem mem_section {D E : DCPO.{u}} (U : ScottOpens (prod D E)) (x : D) (y : E) :
    WithScott.toScott y ∈ leftSection U x ↔ WithScott.toScott (x, y) ∈ U := Iff.rfl

theorem section_scottContinuous {D E : DCPO.{u}} (U : ScottOpens (prod D E)) :
    ScottContinuous (leftSection U) := by
  intro S hn hd p hp
  constructor
  · rintro V ⟨x, hx, rfl⟩ y hy
    have hy' : WithScott.toScott (x, WithScott.ofScott y) ∈ U := hy
    change WithScott.toScott (p, WithScott.ofScott y) ∈ U
    exact (IsScott.isUpperSet_of_isOpen (D := univ) U.isOpen)
      (show WithScott.toScott (x, WithScott.ofScott y) ≤ WithScott.toScott (p, WithScott.ofScott y)
        from ⟨hp.1 hx, le_rfl⟩) hy'
  · intro V hV y hy
    let f : D → WithScott (prod D E) := fun x => WithScott.toScott (x, WithScott.ofScott y)
    have hf : ScottContinuous f := ScottContinuous.id.prodMk (ScottContinuous.const _)
    have hdf : DirectedOn (· ≤ ·) (f '' S) :=
      directedOn_image.mpr (hd.mono (fun {_ _} h => ⟨h, le_rfl⟩))
    have hacc := ((IsScott.isOpen_iff_isUpperSet_and_dirSupInaccOn (D := univ)).mp U.isOpen).2
    obtain ⟨z, ⟨x, hx, rfl⟩, hzx⟩ :=
      hacc (mem_univ _) (hn.image f) hdf (hf hn hd hp) hy
    exact hV (mem_image_of_mem _ hx) hzx

noncomputable def strength (D E : DCPO.{u}) : prod D (valuations E) ⟶ valuations (prod D E) :=
  hom (fun z => SubprobValuation.push z.2
    (fun y : WithScott E => WithScott.toScott (z.1, WithScott.ofScott y))
    ((scott_continuous_iff (insertLeft D E z.1)).mp (hom_scottContinuous _))) (by
      apply SubprobValuation.scottContinuous_of_evaluations
      intro U
      have hs : ScottContinuous (fun z : prod D (valuations E) => (leftSection U z.1, z.2)) :=
        (ScottContinuous.fst.comp (section_scottContinuous U)).prodMk ScottContinuous.snd
      exact hs.comp SubprobValuation.jointEvaluation_scottContinuous)

@[simp] theorem strength_apply (D E : DCPO.{u}) (z : prod D (valuations E))
    (U : ScottOpens (prod D E)) : (strength D E z).val U = z.2.val (leftSection U z.1) := rfl

theorem strength_naturality {D D' E E' : DCPO.{u}} (f : D ⟶ D') (g : E ⟶ E') :
    prodMap f (valuationMap g) ≫ strength D' E' =
      strength D E ≫ valuationMap (prodMap f g) := by
  apply Hom.ext
  intro z
  apply SubprobValuation.ext
  intro U
  rfl

theorem strength_point (D E : DCPO.{u}) :
    prodMap (𝟙 D) (point E) ≫ strength D E = point (prod D E) := by
  apply Hom.ext
  intro z
  apply SubprobValuation.ext
  intro U
  rfl

theorem strength_unitor (D : DCPO.{u}) :
    strength one D ≫ valuationMap (snd one D) = snd one (valuations D) := by
  apply Hom.ext
  intro z
  apply SubprobValuation.ext
  intro U
  rfl

def assocHom (D E F : DCPO.{u}) : prod (prod D E) F ⟶ prod D (prod E F) :=
  hom (fun z => (z.1.1, (z.1.2, z.2)))
    ((ScottContinuous.fst.comp ScottContinuous.fst).prodMk
      ((ScottContinuous.fst.comp ScottContinuous.snd).prodMk ScottContinuous.snd))

theorem associator_apply (D E F : DCPO.{u}) (z : prod (prod D E) F) :
    ((α_ D E F).hom : prod (prod D E) F ⟶ prod D (prod E F)) z = (z.1.1, (z.1.2, z.2)) := rfl

theorem strength_associator (D E F : DCPO.{u}) :
    strength (prod D E) F ≫ valuationMap (assocHom D E F) =
      assocHom D E (valuations F) ≫ prodMap (𝟙 D) (strength E F) ≫ strength D (prod E F) := by
  apply Hom.ext
  intro z
  apply SubprobValuation.ext
  intro U
  rfl

def swap (D E : DCPO.{u}) : prod D E ⟶ prod E D :=
  hom Prod.swap (ScottContinuous.snd.prodMk ScottContinuous.fst)

noncomputable def costrength (D E : DCPO.{u}) : prod (valuations D) E ⟶ valuations (prod D E) :=
  swap (valuations D) E ≫ strength E D ≫ valuationMap (swap E D)

@[simp] theorem costrength_apply (D E : DCPO.{u}) (z : prod (valuations D) E)
    (U : ScottOpens (prod D E)) : (costrength D E z).val U = z.1.val
      (Opens.comap ⟨fun x : WithScott D => WithScott.toScott (WithScott.ofScott x, z.2),
        ((scott_continuous_iff (insertRight D E z.2)).mp (hom_scottContinuous _))⟩ U) := rfl

/-- Standard tensorial strength for an endofunctor on the explicitly chosen
cartesian category. These are the ordinary naturality/unitor/associator
diagrams, stated with the concrete chosen product morphisms. -/
structure CartesianFunctorStrength (T : DCPO.{u} ⥤ DCPO.{u}) where
  app : ∀ D E, prod D (T.obj E) ⟶ T.obj (prod D E)
  naturality : ∀ {D D' E E'} (f : D ⟶ D') (g : E ⟶ E'),
    prodMap f (T.map g) ≫ app D' E' = app D E ≫ T.map (prodMap f g)
  unitor : ∀ D, app one D ≫ T.map (snd one D) = snd one (T.obj D)
  associator : ∀ D E F,
    app (prod D E) F ≫ T.map (assocHom D E F) =
      assocHom D E (T.obj F) ≫ prodMap (𝟙 D) (app E F) ≫ app D (prod E F)

noncomputable def valuationFunctorStrength : CartesianFunctorStrength valuationFunctor where
  app := strength
  naturality := strength_naturality
  unitor := strength_unitor
  associator := strength_associator

/-- A strong monad here contains a genuine `CategoryTheory.Monad`, together
with a tensorial strength and its unit/multiplication compatibility diagrams.
The valuation instance will supply proofs for every field, not premises. -/
structure CartesianMonadStrength (T : CategoryTheory.Monad DCPO.{u})
    extends CartesianFunctorStrength T.toFunctor where
  unit : ∀ D E, prodMap (𝟙 D) (T.η.app E) ≫ app D E = T.η.app (prod D E)
  multiplication : ∀ D E,
    prodMap (𝟙 D) (T.μ.app E) ≫ app D E =
      app D (T.obj E) ≫ T.map (app D E) ≫ T.μ.app (prod D E)

namespace CartesianMonadStrength
variable {T : CategoryTheory.Monad DCPO.{u}} (s : CartesianMonadStrength T)

def costrength (D E : DCPO.{u}) : prod (T.obj D) E ⟶ T.obj (prod D E) :=
  swap (T.obj D) E ≫ s.app E D ≫ T.map (swap E D)

/-- First canonical double strength: costrength, mapped strength, then μ. -/
def doubleLeft (D E : DCPO.{u}) : prod (T.obj D) (T.obj E) ⟶ T.obj (prod D E) :=
  s.costrength D (T.obj E) ≫ T.map (s.app D E) ≫ T.μ.app (prod D E)

/-- Second canonical double strength: strength, mapped costrength, then μ. -/
def doubleRight (D E : DCPO.{u}) : prod (T.obj D) (T.obj E) ⟶ T.obj (prod D E) :=
  s.app (T.obj D) E ≫ T.map (s.costrength D E) ≫ T.μ.app (prod D E)

/-- Categorical commutativity is equality of the two constructed double
strength morphisms. No Fubini predicate appears in this definition. -/
def IsCommutative : Prop := ∀ D E, s.doubleLeft D E = s.doubleRight D E

end CartesianMonadStrength

end DCPO
end CantorFubini
