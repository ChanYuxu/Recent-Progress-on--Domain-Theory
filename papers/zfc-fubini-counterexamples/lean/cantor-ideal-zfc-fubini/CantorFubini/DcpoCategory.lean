import CantorFubini.Foundations
import Mathlib.CategoryTheory.Monad.Basic
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic

/-! The actual category of dcpos and Scott-continuous maps. Objects may be
empty and need no bottom. Products are the ordinary order products, whose
intrinsic Scott topology need not be the ordinary product topology. -/

set_option autoImplicit false
open Set Topology TopologicalSpace CategoryTheory CategoryTheory.Limits
universe u

namespace CantorFubini

structure DCPO where
  carrier : Type u
  [order : PartialOrder carrier]
  complete : IsDcpo carrier

attribute [instance] DCPO.order

namespace DCPO

instance : CoeSort DCPO (Type u) := ⟨DCPO.carrier⟩

def of (D : Type u) [PartialOrder D] (hD : IsDcpo D) : DCPO := ⟨D, hD⟩

structure Hom (D E : DCPO.{u}) where
  toFun : D → E
  continuous : ScottContinuous toFun

instance {D E : DCPO.{u}} : CoeFun (Hom D E) (fun _ => D → E) := ⟨Hom.toFun⟩

@[ext] theorem Hom.ext {D E : DCPO.{u}} {f g : Hom D E}
    (h : ∀ x, f x = g x) : f = g := by
  cases f; cases g
  congr
  exact funext h

instance : Category DCPO.{u} where
  Hom := Hom
  id D := ⟨id, ScottContinuous.id⟩
  comp f g := ⟨g ∘ f, f.continuous.comp g.continuous⟩
  id_comp f := Hom.ext (fun _ => rfl)
  comp_id f := Hom.ext (fun _ => rfl)
  assoc f g h := Hom.ext (fun _ => rfl)

instance {D E : DCPO.{u}} : CoeFun (D ⟶ E) (fun _ => D → E) :=
  ⟨fun f => (show Hom D E from f).toFun⟩

theorem hom_scottContinuous {D E : DCPO.{u}} (f : D ⟶ E) : ScottContinuous f :=
  (show Hom D E from f).continuous

@[simp] theorem id_apply (D : DCPO.{u}) (x : D) : (𝟙 D : D ⟶ D) x = x := rfl
@[simp] theorem comp_apply {D E F : DCPO.{u}} (f : D ⟶ E) (g : E ⟶ F) (x : D) :
    (f ≫ g) x = g (f x) := rfl

def hom {D E : DCPO.{u}} (f : D → E) (hf : ScottContinuous f) : D ⟶ E := ⟨f, hf⟩

theorem isDcpo_prod (D E : DCPO.{u}) : IsDcpo (D × E) := by
  intro S hn hd
  have hf : DirectedOn (· ≤ ·) (Prod.fst '' S) :=
    directedOn_image.mpr (hd.mono (fun {_ _} h => h.1))
  have hg : DirectedOn (· ≤ ·) (Prod.snd '' S) :=
    directedOn_image.mpr (hd.mono (fun {_ _} h => h.2))
  obtain ⟨x, hx⟩ := D.complete (Prod.fst '' S) (hn.image Prod.fst) hf
  obtain ⟨y, hy⟩ := E.complete (Prod.snd '' S) (hn.image Prod.snd) hg
  refine ⟨(x, y), ?_⟩
  rw [isLUB_prod]
  exact ⟨hx, hy⟩

def prod (D E : DCPO.{u}) : DCPO := of (D × E) (isDcpo_prod D E)

def fst (D E : DCPO.{u}) : prod D E ⟶ D := hom Prod.fst ScottContinuous.fst
def snd (D E : DCPO.{u}) : prod D E ⟶ E := hom Prod.snd ScottContinuous.snd

def pair {D E F : DCPO.{u}} (f : D ⟶ E) (g : D ⟶ F) : D ⟶ prod E F :=
  hom (fun x => (f x, g x)) ((hom_scottContinuous f).prodMk (hom_scottContinuous g))

def prodMap {D D' E E' : DCPO.{u}} (f : D ⟶ D') (g : E ⟶ E') :
    prod D E ⟶ prod D' E' :=
  pair (fst D E ≫ f) (snd D E ≫ g)

@[simp] theorem fst_apply (D E : DCPO.{u}) (z : prod D E) : fst D E z = z.1 := rfl
@[simp] theorem snd_apply (D E : DCPO.{u}) (z : prod D E) : snd D E z = z.2 := rfl
@[simp] theorem pair_apply {D E F : DCPO.{u}} (f : D ⟶ E) (g : D ⟶ F) (x : D) :
    pair f g x = (f x, g x) := rfl
@[simp] theorem prodMap_apply {D D' E E' : DCPO.{u}} (f : D ⟶ D') (g : E ⟶ E')
    (z : prod D E) : prodMap f g z = (f z.1, g z.2) := rfl

def productCone (D E : DCPO.{u}) : LimitCone (Limits.pair D E) where
  cone := BinaryFan.mk (fst D E) (snd D E)
  isLimit := BinaryFan.IsLimit.mk _
    (fun f g => DCPO.pair f g)
    (fun _ _ => Hom.ext (fun _ => rfl))
    (fun _ _ => Hom.ext (fun _ => rfl))
    (fun {T} f g m hf hg => by
      apply Hom.ext
      intro x
      exact Prod.ext (congrArg (fun k : T ⟶ D => k x) hf)
        (congrArg (fun k : T ⟶ E => k x) hg))

theorem punit_isDcpo : IsDcpo PUnit.{u + 1} := by
  intro S hn _
  refine ⟨PUnit.unit, ?_, ?_⟩ <;> intro z hz <;> trivial

def one : DCPO.{u} := of PUnit.{u + 1} punit_isDcpo
def terminate (D : DCPO.{u}) : D ⟶ one := hom (fun _ => PUnit.unit) (ScottContinuous.const _)

def terminalCone : LimitCone (Functor.empty DCPO.{u}) where
  cone := asEmptyCone one
  isLimit := IsTerminal.ofUniqueHom terminate (fun D f => Hom.ext (fun x =>
    (show (f x : PUnit.{u + 1}) = PUnit.unit from PUnit.ext _ _)))

noncomputable instance cartesianMonoidal : CartesianMonoidalCategory DCPO.{u} :=
  CartesianMonoidalCategory.ofChosenFiniteProducts terminalCone productCone

end DCPO
end CantorFubini
