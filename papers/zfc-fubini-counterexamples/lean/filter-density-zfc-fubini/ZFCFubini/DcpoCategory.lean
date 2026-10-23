import ZFCFubini.Foundations
import Mathlib.CategoryTheory.Monad.Basic
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic

/-!
# DCPOs and Scott-continuous maps, with their actual cartesian products

`IsDcpo` throughout means existence of suprema of nonempty directed sets.
Neither objects nor their product factors are required to have a bottom.
The cartesian monoidal structure is built from the universal properties of
the ordinary order product and the one-element dcpo.
-/

set_option autoImplicit false
open Set CategoryTheory CategoryTheory.Limits
universe u

namespace ZFCFubini

theorem prod_isDcpo {P Q : Type u} [PartialOrder P] [PartialOrder Q]
    (hP : IsDcpo P) (hQ : IsDcpo Q) : IsDcpo (P × Q) := by
  intro A hn hd
  obtain ⟨p, hp⟩ := hP (Prod.fst '' A) (hn.image _)
    (hd.mono_comp (fun _ _ h => h.1))
  obtain ⟨q, hq⟩ := hQ (Prod.snd '' A) (hn.image _)
    (hd.mono_comp (fun _ _ h => h.2))
  exact ⟨(p, q), isLUB_prod.mpr ⟨hp, hq⟩⟩

/-- A genuine dcpo, without a distinguished least element. -/
structure DcpoCat where
  carrier : Type u
  [order : PartialOrder carrier]
  dcpo : IsDcpo carrier

namespace DcpoCat

instance : CoeSort DcpoCat (Type u) := ⟨carrier⟩
attribute [instance] order

def of (P : Type u) [PartialOrder P] (hP : IsDcpo P) : DcpoCat := ⟨P, hP⟩

/-- Morphisms are actual functions with the order-theoretic Scott condition. -/
structure Hom (P Q : DcpoCat.{u}) where
  toFun : P → Q
  continuous : ScottContinuous toFun

instance {P Q : DcpoCat.{u}} : CoeFun (Hom P Q) (fun _ => P → Q) := ⟨Hom.toFun⟩

@[ext] theorem Hom.ext {P Q : DcpoCat.{u}} {f g : Hom P Q}
    (h : ∀ x, f x = g x) : f = g := by
  cases f; cases g; congr; exact funext h

instance dcpoCategory : Category DcpoCat.{u} where
  Hom P Q := Hom P Q
  id P := ⟨id, ScottContinuous.id⟩
  comp f g := ⟨g ∘ f, f.continuous.comp g.continuous⟩
  id_comp f := Hom.ext fun _ => rfl
  comp_id f := Hom.ext fun _ => rfl
  assoc f g h := Hom.ext fun _ => rfl

instance {P Q : DcpoCat.{u}} : CoeFun (P ⟶ Q) (fun _ => P → Q) := ⟨Hom.toFun⟩

@[simp] theorem id_apply (P : DcpoCat.{u}) (x : P) : (𝟙 P : P ⟶ P) x = x := rfl
@[simp] theorem comp_apply {P Q R : DcpoCat.{u}} (f : P ⟶ Q) (g : Q ⟶ R) (x : P) :
    (f ≫ g) x = g (f x) := rfl

def prod (P Q : DcpoCat.{u}) : DcpoCat := of (P × Q) (prod_isDcpo P.dcpo Q.dcpo)

def terminal : DcpoCat.{u} := of PUnit fun _ _ _ => ⟨PUnit.unit, by
  constructor
  · intro x _; exact le_rfl
  · intro x _; exact le_rfl⟩

def fst (P Q : DcpoCat.{u}) : prod P Q ⟶ P := ⟨Prod.fst, ScottContinuous.fst⟩
def snd (P Q : DcpoCat.{u}) : prod P Q ⟶ Q := ⟨Prod.snd, ScottContinuous.snd⟩

def lift {P Q R : DcpoCat.{u}} (f : R ⟶ P) (g : R ⟶ Q) : R ⟶ prod P Q :=
  ⟨fun x => (f x, g x), f.continuous.prodMk g.continuous⟩

def prodMap {P P' Q Q' : DcpoCat.{u}} (f : P ⟶ P') (g : Q ⟶ Q') :
    prod P Q ⟶ prod P' Q' :=
  lift (fst P Q ≫ f) (snd P Q ≫ g)

@[simp] theorem fst_apply (P Q : DcpoCat.{u}) (x : P × Q) : fst P Q x = x.1 := rfl
@[simp] theorem snd_apply (P Q : DcpoCat.{u}) (x : P × Q) : snd P Q x = x.2 := rfl
@[simp] theorem lift_apply {P Q R : DcpoCat.{u}} (f : R ⟶ P) (g : R ⟶ Q) (x : R) :
    lift f g x = (f x, g x) := rfl
@[simp] theorem prodMap_apply {P P' Q Q' : DcpoCat.{u}}
    (f : P ⟶ P') (g : Q ⟶ Q') (x : P × Q) : prodMap f g x = (f x.1, g x.2) := rfl

def terminalCone : LimitCone (Functor.empty.{0} DcpoCat.{u}) where
  cone := asEmptyCone terminal
  isLimit := (isTerminalEquivUnique _ _).symm fun P =>
    { default := ⟨fun _ => PUnit.unit, ScottContinuous.const _⟩
      uniq := fun f => Hom.ext fun x => @Subsingleton.elim PUnit inferInstance _ _ }

def binaryProductCone (P Q : DcpoCat.{u}) : LimitCone (pair P Q) where
  cone := BinaryFan.mk (fst P Q) (snd P Q)
  isLimit := BinaryFan.IsLimit.mk _ (fun f g => lift f g)
    (fun f g => Hom.ext fun _ => rfl)
    (fun f g => Hom.ext fun _ => rfl)
    (fun f g m hf hg => Hom.ext fun x => by
      have hfst := congrArg (fun k : _ ⟶ P => k x) hf
      have hsnd := congrArg (fun k : _ ⟶ Q => k x) hg
      exact Prod.ext hfst hsnd)

noncomputable instance cartesianMonoidalCategory : CartesianMonoidalCategory DcpoCat.{u} :=
  CartesianMonoidalCategory.ofChosenFiniteProducts terminalCone binaryProductCone

open MonoidalCategory

@[simp] theorem tensorObj_eq (P Q : DcpoCat.{u}) : P ⊗ Q = prod P Q := rfl
@[simp] theorem tensorHom_apply {P P' Q Q' : DcpoCat.{u}}
    (f : P ⟶ P') (g : Q ⟶ Q') (x : P × Q) : (f ⊗ₘ g) x = (f x.1, g x.2) := rfl

@[simp] theorem leftUnitor_hom_apply (P : DcpoCat.{u}) (x : PUnit × P) :
    (λ_ P).hom x = x.2 := rfl

@[simp] theorem associator_hom_apply (P Q R : DcpoCat.{u}) (x : (P × Q) × R) :
    (α_ P Q R).hom x = (x.1.1, x.1.2, x.2) := rfl

/-- The cartesian swap, later used to derive costrength from strength. -/
def swap (P Q : DcpoCat.{u}) : prod P Q ⟶ prod Q P := lift (snd P Q) (fst P Q)

@[simp] theorem swap_apply (P Q : DcpoCat.{u}) (x : P × Q) :
    swap P Q x = (x.2, x.1) := rfl

end DcpoCat
end ZFCFubini
