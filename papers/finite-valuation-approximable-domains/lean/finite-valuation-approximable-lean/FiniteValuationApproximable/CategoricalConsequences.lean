import FiniteValuationApproximable.MainTheorem
import FiniteValuationApproximable.ContinuousValuation.Monad

/-!
# Categorical consequences of the FVA closure theorem

This file supplies the local categorical and monadic structure mentioned after
the main theorem of `main (17).tex`.  Objects are partially ordered carriers
equipped with an `IsFVA` proof, and homs are *definitionally* the bundled
Scott-continuous maps of the standalone development.  Thus the results below
are universal properties and algebraic laws, not merely objectwise closure
statements under new names.

The two valuation restrictions are presented as Kleisli triples.  This is an
equivalent formulation of a monad: the record contains its object and arrow
maps, unit, multiplication, Kleisli extension, the two unit laws, associativity,
and the equations recovering arrow map and multiplication from extension.
The `VSub` instance uses the audited Jones boundary.  The `VOne` instance is
derived from it by proving internally that Kleisli extension of a
probability-valued kernel preserves total mass one.
-/

set_option autoImplicit false
set_option linter.unnecessarySimpa false

universe u

namespace FiniteValuationApproximable

open Set
open AbramskyJung.Chapter2

/-! ## The full local category of FVA objects -/

/-- An object of the full subcategory cut out by `IsFVA`. -/
structure FVAObject where
  carrier : Type u
  partialOrder : PartialOrder carrier
  isFVA : @IsFVA.{u, u} carrier partialOrder.toPreorder partialOrder

namespace FVAObject

instance : CoeSort FVAObject.{u} (Type u) where
  coe X := X.carrier

instance (X : FVAObject.{u}) : PartialOrder X := X.partialOrder

end FVAObject

/-- Homs in the full FVA subcategory are exactly Scott-continuous maps. -/
abbrev FVAHom (X Y : FVAObject.{u}) :=
  AbramskyJung.Chapter3.ContFun X Y

/-- Identity in the full FVA subcategory. -/
def fvaHomId (X : FVAObject.{u}) : FVAHom X X where
  toFun x := x
  continuous := scottContinuous_id

/-- Composition in the full FVA subcategory. -/
def fvaHomComp {X Y Z : FVAObject.{u}}
    (g : FVAHom Y Z) (f : FVAHom X Y) : FVAHom X Z :=
  AbramskyJung.Chapter3.ContFun.comp g f

@[simp] theorem fvaHomId_apply (X : FVAObject.{u}) (x : X) :
    fvaHomId X x = x := rfl

@[simp] theorem fvaHomComp_apply {X Y Z : FVAObject.{u}}
    (g : FVAHom Y Z) (f : FVAHom X Y) (x : X) :
    fvaHomComp g f x = g (f x) := rfl

theorem fvaHomComp_id_left {X Y : FVAObject.{u}} (f : FVAHom X Y) :
    fvaHomComp (fvaHomId Y) f = f := by
  apply AbramskyJung.Chapter3.ContFun.ext_apply
  intro x
  rfl

theorem fvaHomComp_id_right {X Y : FVAObject.{u}} (f : FVAHom X Y) :
    fvaHomComp f (fvaHomId X) = f := by
  apply AbramskyJung.Chapter3.ContFun.ext_apply
  intro x
  rfl

theorem fvaHomComp_assoc {W X Y Z : FVAObject.{u}}
    (h : FVAHom Y Z) (g : FVAHom X Y) (f : FVAHom W X) :
    fvaHomComp h (fvaHomComp g f) =
      fvaHomComp (fvaHomComp h g) f := by
  apply AbramskyJung.Chapter3.ContFun.ext_apply
  intro x
  rfl

/-! ## Terminal object and binary products -/

/-- The empty finite valuation stage, bundled as the terminal FVA object. -/
def fvaTerminal : FVAObject.{u} where
  carrier := (emptyFinitePoset.{u}).VSub
  partialOrder := inferInstance
  isFVA := terminal_isFVA

/-- The unique arrow to the terminal FVA object. -/
def fvaTerminate (X : FVAObject.{u}) : FVAHom X fvaTerminal :=
  terminalMap X

theorem fvaTerminate_unique (X : FVAObject.{u})
    (f : FVAHom X fvaTerminal) : f = fvaTerminate X :=
  terminalMap_unique X f

/-- Binary product object in the full FVA subcategory. -/
def fvaProduct (X Y : FVAObject.{u}) : FVAObject.{u} where
  carrier := X × Y
  partialOrder := inferInstance
  isFVA := global_product X.isFVA Y.isFVA

/-- First product projection. -/
def fvaFst (X Y : FVAObject.{u}) : FVAHom (fvaProduct X Y) X where
  toFun := Prod.fst
  continuous := AbramskyJung.Chapter3.prod_fst_scottContinuous

/-- Second product projection. -/
def fvaSnd (X Y : FVAObject.{u}) : FVAHom (fvaProduct X Y) Y where
  toFun := Prod.snd
  continuous := AbramskyJung.Chapter3.prod_snd_scottContinuous

/-- Pairing of two arrows with a common source. -/
def fvaPair {W X Y : FVAObject.{u}}
    (f : FVAHom W X) (g : FVAHom W Y) :
    FVAHom W (fvaProduct X Y) where
  toFun w := (f w, g w)
  continuous := AbramskyJung.Chapter3.prod_pair_scottContinuous
    f.continuous g.continuous

@[simp] theorem fvaFst_pair {W X Y : FVAObject.{u}}
    (f : FVAHom W X) (g : FVAHom W Y) :
    fvaHomComp (fvaFst X Y) (fvaPair f g) = f := by
  apply AbramskyJung.Chapter3.ContFun.ext_apply
  intro w
  rfl

@[simp] theorem fvaSnd_pair {W X Y : FVAObject.{u}}
    (f : FVAHom W X) (g : FVAHom W Y) :
    fvaHomComp (fvaSnd X Y) (fvaPair f g) = g := by
  apply AbramskyJung.Chapter3.ContFun.ext_apply
  intro w
  rfl

theorem fvaPair_unique {W X Y : FVAObject.{u}}
    (f : FVAHom W X) (g : FVAHom W Y)
    (h : FVAHom W (fvaProduct X Y))
    (hfst : fvaHomComp (fvaFst X Y) h = f)
    (hsnd : fvaHomComp (fvaSnd X Y) h = g) :
    h = fvaPair f g := by
  apply AbramskyJung.Chapter3.ContFun.ext_apply
  intro w
  apply Prod.ext
  · exact congrArg (fun k : FVAHom W X => k w) hfst
  · exact congrArg (fun k : FVAHom W Y => k w) hsnd

/-! ## Exponentials -/

/-- The exponential object, conditional only on the isolated finite function
generator theorem used by the objectwise main theorem. -/
def fvaExponential
    (hFiniteFunctions : FiniteFunctionGeneratorsAreFVA.{u})
    (X Y : FVAObject.{u}) : FVAObject.{u} where
  carrier := AbramskyJung.Chapter3.ContFun X Y
  partialOrder := inferInstance
  isFVA := global_functionSpace_of_finite_generators
    hFiniteFunctions X.isFVA Y.isFVA

/-- The value of currying at one source point. -/
def fvaCurryValue
    (hFiniteFunctions : FiniteFunctionGeneratorsAreFVA.{u})
    {W X Y : FVAObject.{u}}
    (h : FVAHom (fvaProduct W X) Y) (w : W) :
    fvaExponential hFiniteFunctions X Y where
  toFun x := h (w, x)
  continuous := h.continuous.comp
    (AbramskyJung.Chapter3.prod_pair_scottContinuous
      (const_scottContinuous w) scottContinuous_id)

/-- Currying is a Scott-continuous arrow into the function-space dcpo. -/
def fvaCurry
    (hFiniteFunctions : FiniteFunctionGeneratorsAreFVA.{u})
    {W X Y : FVAObject.{u}}
    (h : FVAHom (fvaProduct W X) Y) :
    FVAHom W (fvaExponential hFiniteFunctions X Y) where
  toFun w := fvaCurryValue hFiniteFunctions h w
  continuous := by
    constructor
    · intro w w' hww' x
      exact h.continuous.monotone ⟨hww', le_rfl⟩
    · intro A s hA hs
      constructor
      · rintro _ ⟨w, hwA, rfl⟩ x
        exact h.continuous.monotone ⟨hs.1 hwA, le_rfl⟩
      · intro g hg x
        let slice : AbramskyJung.Chapter3.ContFun W Y := {
          toFun := fun w => h (w, x)
          continuous := h.continuous.comp
            (AbramskyJung.Chapter3.prod_pair_scottContinuous
              scottContinuous_id (const_scottContinuous x)) }
        have hSlice := slice.continuous.maps_isSup hA hs
        apply hSlice.2 (g.toFun x)
        rintro _ ⟨w, hwA, rfl⟩
        exact (hg ⟨w, hwA, rfl⟩) x

/-- Uncurrying is Scott-continuous by separate continuity of evaluation. -/
def fvaUncurry
    (hFiniteFunctions : FiniteFunctionGeneratorsAreFVA.{u})
    {W X Y : FVAObject.{u}}
    (k : FVAHom W (fvaExponential hFiniteFunctions X Y)) :
    FVAHom (fvaProduct W X) Y where
  toFun p := (k p.1).toFun p.2
  continuous := scottContinuous_uncurry_of_separately
    (fun w x => (k w).toFun x)
    (fun x =>
      (AbramskyJung.Chapter3.ContFun.eval_scottContinuous
        Y.isFVA.1.1.1 x).comp k.continuous)
    (fun w => (k w).continuous)

/-- Evaluation is the uncurrying of the identity on the exponential object. -/
def fvaEvaluation
    (hFiniteFunctions : FiniteFunctionGeneratorsAreFVA.{u})
    (X Y : FVAObject.{u}) :
    FVAHom (fvaProduct (fvaExponential hFiniteFunctions X Y) X) Y :=
  fvaUncurry hFiniteFunctions
    (fvaHomId (fvaExponential hFiniteFunctions X Y))

@[simp] theorem fvaUncurry_curry
    (hFiniteFunctions : FiniteFunctionGeneratorsAreFVA.{u})
    {W X Y : FVAObject.{u}}
    (h : FVAHom (fvaProduct W X) Y) :
    fvaUncurry hFiniteFunctions (fvaCurry hFiniteFunctions h) = h := by
  apply AbramskyJung.Chapter3.ContFun.ext_apply
  intro p
  change h (p.1, p.2) = h p
  cases p
  rfl

@[simp] theorem fvaCurry_uncurry
    (hFiniteFunctions : FiniteFunctionGeneratorsAreFVA.{u})
    {W X Y : FVAObject.{u}}
    (k : FVAHom W (fvaExponential hFiniteFunctions X Y)) :
    fvaCurry hFiniteFunctions (fvaUncurry hFiniteFunctions k) = k := by
  apply AbramskyJung.Chapter3.ContFun.ext_apply
  intro w
  apply AbramskyJung.Chapter3.ContFun.ext_apply
  intro x
  change (k w).toFun x = (k w).toFun x
  rfl

/-- Uniqueness half of the exponential universal property. -/
theorem fvaCurry_unique
    (hFiniteFunctions : FiniteFunctionGeneratorsAreFVA.{u})
    {W X Y : FVAObject.{u}}
    (h : FVAHom (fvaProduct W X) Y)
    (k : FVAHom W (fvaExponential hFiniteFunctions X Y))
    (hk : fvaUncurry hFiniteFunctions k = h) :
    k = fvaCurry hFiniteFunctions h := by
  rw [← hk, fvaCurry_uncurry]

/-- A proof package collecting the actual category, terminal, product, and
exponential laws established above. -/
structure FVALocalCartesianClosed
    (hFiniteFunctions : FiniteFunctionGeneratorsAreFVA.{u}) : Prop where
  left_identity : ∀ {X Y : FVAObject.{u}} (f : FVAHom X Y),
    fvaHomComp (fvaHomId Y) f = f
  right_identity : ∀ {X Y : FVAObject.{u}} (f : FVAHom X Y),
    fvaHomComp f (fvaHomId X) = f
  associativity : ∀ {W X Y Z : FVAObject.{u}}
    (h : FVAHom Y Z) (g : FVAHom X Y) (f : FVAHom W X),
    fvaHomComp h (fvaHomComp g f) = fvaHomComp (fvaHomComp h g) f
  terminal_unique : ∀ (X : FVAObject.{u}) (f : FVAHom X fvaTerminal),
    f = fvaTerminate X
  product_fst : ∀ {W X Y : FVAObject.{u}}
    (f : FVAHom W X) (g : FVAHom W Y),
    fvaHomComp (fvaFst X Y) (fvaPair f g) = f
  product_snd : ∀ {W X Y : FVAObject.{u}}
    (f : FVAHom W X) (g : FVAHom W Y),
    fvaHomComp (fvaSnd X Y) (fvaPair f g) = g
  product_unique : ∀ {W X Y : FVAObject.{u}}
    (f : FVAHom W X) (g : FVAHom W Y)
    (h : FVAHom W (fvaProduct X Y)),
    fvaHomComp (fvaFst X Y) h = f →
    fvaHomComp (fvaSnd X Y) h = g → h = fvaPair f g
  uncurry_curry : ∀ {W X Y : FVAObject.{u}}
    (h : FVAHom (fvaProduct W X) Y),
    fvaUncurry hFiniteFunctions (fvaCurry hFiniteFunctions h) = h
  curry_uncurry : ∀ {W X Y : FVAObject.{u}}
    (k : FVAHom W (fvaExponential hFiniteFunctions X Y)),
    fvaCurry hFiniteFunctions (fvaUncurry hFiniteFunctions k) = k

/-- The full FVA subcategory is Cartesian closed in the standalone
Scott-continuous-map API.  Here `Local` in the package name refers to that
standalone interface, not to local Cartesian closedness of all slices. -/
theorem fvaLocalCartesianClosed
    (hFiniteFunctions : FiniteFunctionGeneratorsAreFVA.{u}) :
    FVALocalCartesianClosed hFiniteFunctions where
  left_identity := fvaHomComp_id_left
  right_identity := fvaHomComp_id_right
  associativity := fvaHomComp_assoc
  terminal_unique := fvaTerminate_unique
  product_fst := fvaFst_pair
  product_snd := fvaSnd_pair
  product_unique := fun f g h hf hg => fvaPair_unique f g h hf hg
  uncurry_curry := fvaUncurry_curry hFiniteFunctions
  curry_uncurry := fvaCurry_uncurry hFiniteFunctions

/-! ## A concrete interface for restricted monads -/

/-- Kleisli-triple presentation of a monad restricted to FVA objects.

Besides the three Kleisli laws, the record retains the ordinary functorial
arrow map and an explicit multiplication arrow.  The final two fields tie
those operations to Kleisli extension, so they cannot be unrelated closure
data. -/
structure FVAKleisliMonadRestriction where
  object : FVAObject.{u} → FVAObject.{u}
  map : ∀ {X Y : FVAObject.{u}},
    FVAHom X Y → FVAHom (object X) (object Y)
  unit : ∀ X : FVAObject.{u}, FVAHom X (object X)
  multiplication : ∀ X : FVAObject.{u},
    FVAHom (object (object X)) (object X)
  extend : ∀ {X Y : FVAObject.{u}},
    FVAHom X (object Y) → FVAHom (object X) (object Y)
  map_id : ∀ X : FVAObject.{u}, map (fvaHomId X) = fvaHomId (object X)
  map_comp : ∀ {X Y Z : FVAObject.{u}}
    (g : FVAHom Y Z) (f : FVAHom X Y),
    map (fvaHomComp g f) = fvaHomComp (map g) (map f)
  extend_unit_left : ∀ {X Y : FVAObject.{u}}
    (k : FVAHom X (object Y)),
    fvaHomComp (extend k) (unit X) = k
  extend_unit_right : ∀ X : FVAObject.{u},
    extend (unit X) = fvaHomId (object X)
  extend_assoc : ∀ {X Y Z : FVAObject.{u}}
    (k : FVAHom X (object Y)) (l : FVAHom Y (object Z)),
    fvaHomComp (extend l) (extend k) =
      extend (fvaHomComp (extend l) k)
  map_as_extend : ∀ {X Y : FVAObject.{u}} (f : FVAHom X Y),
    map f = extend (fvaHomComp (unit Y) f)
  multiplication_as_extend : ∀ X : FVAObject.{u},
    multiplication X = extend (fvaHomId (object X))

namespace FVAKleisliMonadRestriction

variable (M : FVAKleisliMonadRestriction.{u})

/-- Naturality of the unit, derived from the Kleisli left-unit law. -/
theorem unit_natural {X Y : FVAObject.{u}} (f : FVAHom X Y) :
    fvaHomComp (M.map f) (M.unit X) =
      fvaHomComp (M.unit Y) f := by
  rw [M.map_as_extend f, M.extend_unit_left]

/-- First multiplication unit law: `mu ∘ eta_T = id`. -/
theorem multiplication_unit_left (X : FVAObject.{u}) :
    fvaHomComp (M.multiplication X) (M.unit (M.object X)) =
      fvaHomId (M.object X) := by
  rw [M.multiplication_as_extend X, M.extend_unit_left]

/-- Second multiplication unit law: `mu ∘ T eta = id`. -/
theorem multiplication_unit_right (X : FVAObject.{u}) :
    fvaHomComp (M.multiplication X) (M.map (M.unit X)) =
      fvaHomId (M.object X) := by
  rw [M.multiplication_as_extend X, M.map_as_extend, M.extend_assoc]
  have hkernel :
      fvaHomComp (M.extend (fvaHomId (M.object X)))
          (fvaHomComp (M.unit (M.object X)) (M.unit X)) =
        M.unit X := by
    rw [fvaHomComp_assoc, M.extend_unit_left, fvaHomComp_id_left]
  rw [hkernel, M.extend_unit_right]

/-- Naturality of multiplication. -/
theorem multiplication_natural {X Y : FVAObject.{u}} (f : FVAHom X Y) :
    fvaHomComp (M.map f) (M.multiplication X) =
      fvaHomComp (M.multiplication Y) (M.map (M.map f)) := by
  have hleft :
      fvaHomComp (M.map f) (M.multiplication X) = M.extend (M.map f) := by
    rw [M.map_as_extend f, M.multiplication_as_extend X, M.extend_assoc,
      fvaHomComp_id_right]
  have hright :
      fvaHomComp (M.multiplication Y) (M.map (M.map f)) =
        M.extend (M.map f) := by
    rw [M.multiplication_as_extend Y, M.map_as_extend, M.extend_assoc]
    have hkernel :
        fvaHomComp (M.extend (fvaHomId (M.object Y)))
            (fvaHomComp (M.unit (M.object Y)) (M.map f)) =
          M.map f := by
      rw [fvaHomComp_assoc, M.extend_unit_left, fvaHomComp_id_left]
    rw [hkernel]
  exact hleft.trans hright.symm

/-- Multiplication associativity: `mu ∘ T mu = mu ∘ mu_T`. -/
theorem multiplication_assoc (X : FVAObject.{u}) :
    fvaHomComp (M.multiplication X) (M.map (M.multiplication X)) =
      fvaHomComp (M.multiplication X) (M.multiplication (M.object X)) := by
  have hleft :
      fvaHomComp (M.multiplication X) (M.map (M.multiplication X)) =
        M.extend (M.multiplication X) := by
    rw [M.multiplication_as_extend X, M.map_as_extend, M.extend_assoc]
    have hkernel :
        fvaHomComp (M.extend (fvaHomId (M.object X)))
            (fvaHomComp (M.unit (M.object X))
              (M.extend (fvaHomId (M.object X)))) =
          M.extend (fvaHomId (M.object X)) := by
      rw [fvaHomComp_assoc, M.extend_unit_left, fvaHomComp_id_left]
    rw [hkernel]
  have hright :
      fvaHomComp (M.multiplication X) (M.multiplication (M.object X)) =
        M.extend (M.multiplication X) := by
    rw [M.multiplication_as_extend X,
      M.multiplication_as_extend (M.object X), M.extend_assoc,
      fvaHomComp_id_right]
  exact hleft.trans hright.symm

end FVAKleisliMonadRestriction

/-! ## Restriction of the subprobability valuation monad -/

/-- Object action of the subprobability valuation monad on FVA. -/
def vSubFVAObject
    (hFiniteDouble : FiniteDoubleValuationGeneratorsAreFVA.{u})
    (X : FVAObject.{u}) : FVAObject.{u} where
  carrier := ContinuousValuation.VSub X
  partialOrder := inferInstance
  isFVA := global_vSub_of_finite_double_generators hFiniteDouble X.isFVA

/-- Arrow action of the subprobability valuation monad. -/
def vSubFVAMap
    (hFiniteDouble : FiniteDoubleValuationGeneratorsAreFVA.{u})
    {X Y : FVAObject.{u}} (f : FVAHom X Y) :
    FVAHom (vSubFVAObject hFiniteDouble X)
      (vSubFVAObject hFiniteDouble Y) where
  toFun := ContinuousValuation.pushforward f
  continuous := ContinuousValuation.pushforward_scottContinuous f

/-- Dirac unit as a morphism of the FVA subcategory. -/
noncomputable def vSubFVAUnit
    (hFiniteDouble : FiniteDoubleValuationGeneratorsAreFVA.{u})
    (X : FVAObject.{u}) :
    FVAHom X (vSubFVAObject hFiniteDouble X) :=
  ContinuousValuation.unit (D := X)

/-- Jones Kleisli extension as a morphism between valuation objects. -/
noncomputable def vSubFVAExtend
    (hFiniteDouble : FiniteDoubleValuationGeneratorsAreFVA.{u})
    {X Y : FVAObject.{u}}
    (k : FVAHom X (vSubFVAObject hFiniteDouble Y)) :
    FVAHom (vSubFVAObject hFiniteDouble X)
      (vSubFVAObject hFiniteDouble Y) where
  toFun := ContinuousValuation.bind k
  continuous := ContinuousValuation.bind_scottContinuous_input k

/-- Monad multiplication is Kleisli extension of the identity kernel. -/
noncomputable def vSubFVAMultiplication
    (hFiniteDouble : FiniteDoubleValuationGeneratorsAreFVA.{u})
    (X : FVAObject.{u}) :
    FVAHom (vSubFVAObject hFiniteDouble (vSubFVAObject hFiniteDouble X))
      (vSubFVAObject hFiniteDouble X) :=
  vSubFVAExtend hFiniteDouble (fvaHomId (vSubFVAObject hFiniteDouble X))

theorem vSubFVAMap_id
    (hFiniteDouble : FiniteDoubleValuationGeneratorsAreFVA.{u})
    (X : FVAObject.{u}) :
    vSubFVAMap hFiniteDouble (fvaHomId X) =
      fvaHomId (vSubFVAObject hFiniteDouble X) := by
  apply AbramskyJung.Chapter3.ContFun.ext_apply
  intro mu
  change ContinuousValuation.pushforward (fvaHomId X) mu = mu
  have hid : fvaHomId X = ContinuousValuation.idMap (D := X) := by
    apply ScottContFun.ext_apply
    intro x
    rfl
  rw [hid, ContinuousValuation.pushforward_idMap]

theorem vSubFVAMap_comp
    (hFiniteDouble : FiniteDoubleValuationGeneratorsAreFVA.{u})
    {X Y Z : FVAObject.{u}}
    (g : FVAHom Y Z) (f : FVAHom X Y) :
    vSubFVAMap hFiniteDouble (fvaHomComp g f) =
      fvaHomComp (vSubFVAMap hFiniteDouble g)
        (vSubFVAMap hFiniteDouble f) := by
  apply AbramskyJung.Chapter3.ContFun.ext_apply
  intro mu
  exact (ContinuousValuation.pushforward_comp f g mu).symm

theorem vSubFVAExtend_unit_left
    (hFiniteDouble : FiniteDoubleValuationGeneratorsAreFVA.{u})
    {X Y : FVAObject.{u}}
    (k : FVAHom X (vSubFVAObject hFiniteDouble Y)) :
    fvaHomComp (vSubFVAExtend hFiniteDouble k)
        (vSubFVAUnit hFiniteDouble X) = k := by
  apply AbramskyJung.Chapter3.ContFun.ext_apply
  intro x
  exact ContinuousValuation.bind_dirac k x

theorem vSubFVAExtend_unit_right
    (hFiniteDouble : FiniteDoubleValuationGeneratorsAreFVA.{u})
    (X : FVAObject.{u}) :
    vSubFVAExtend hFiniteDouble (vSubFVAUnit hFiniteDouble X) =
      fvaHomId (vSubFVAObject hFiniteDouble X) := by
  apply AbramskyJung.Chapter3.ContFun.ext_apply
  intro mu
  exact ContinuousValuation.bind_unit mu

theorem vSubFVAExtend_assoc
    (hFiniteDouble : FiniteDoubleValuationGeneratorsAreFVA.{u})
    {X Y Z : FVAObject.{u}}
    (k : FVAHom X (vSubFVAObject hFiniteDouble Y))
    (l : FVAHom Y (vSubFVAObject hFiniteDouble Z)) :
    fvaHomComp (vSubFVAExtend hFiniteDouble l)
        (vSubFVAExtend hFiniteDouble k) =
      vSubFVAExtend hFiniteDouble
        (fvaHomComp (vSubFVAExtend hFiniteDouble l) k) := by
  apply AbramskyJung.Chapter3.ContFun.ext_apply
  intro mu
  change ContinuousValuation.bind l (ContinuousValuation.bind k mu) =
    ContinuousValuation.bind
      (fvaHomComp (vSubFVAExtend hFiniteDouble l) k) mu
  rw [ContinuousValuation.bind_assoc]
  apply congrArg (fun q => ContinuousValuation.bind q mu)
  apply AbramskyJung.Chapter3.ContFun.ext_apply
  intro x
  rfl

theorem vSubFVAMap_as_extend
    (hFiniteDouble : FiniteDoubleValuationGeneratorsAreFVA.{u})
    {X Y : FVAObject.{u}} (f : FVAHom X Y) :
    vSubFVAMap hFiniteDouble f =
      vSubFVAExtend hFiniteDouble
        (fvaHomComp (vSubFVAUnit hFiniteDouble Y) f) := by
  apply AbramskyJung.Chapter3.ContFun.ext_apply
  intro mu
  exact (ContinuousValuation.bind_unit_comp_eq_pushforward f mu).symm

/-- The Jones subprobability monad genuinely restricts to FVA objects. -/
noncomputable def vSubFVAMonadRestriction
    (hFiniteDouble : FiniteDoubleValuationGeneratorsAreFVA.{u}) :
    FVAKleisliMonadRestriction.{u} where
  object := vSubFVAObject hFiniteDouble
  map := vSubFVAMap hFiniteDouble
  unit := vSubFVAUnit hFiniteDouble
  multiplication := vSubFVAMultiplication hFiniteDouble
  extend := vSubFVAExtend hFiniteDouble
  map_id := vSubFVAMap_id hFiniteDouble
  map_comp := vSubFVAMap_comp hFiniteDouble
  extend_unit_left := vSubFVAExtend_unit_left hFiniteDouble
  extend_unit_right := vSubFVAExtend_unit_right hFiniteDouble
  extend_assoc := vSubFVAExtend_assoc hFiniteDouble
  map_as_extend := vSubFVAMap_as_extend hFiniteDouble
  multiplication_as_extend := fun _ => rfl

/-! ## Probability Kleisli extension -/

namespace ContinuousValuation

open scoped ENNReal

/-- The inclusion of probability valuations into subprobability valuations,
bundled as a Scott-continuous map. -/
def vOneToVSubMap {D : Type u} [Preorder D] :
    ScottContFun (VOne D) (VSub D) where
  toFun := VOne.toVSub
  continuous := vOneInclusion_scottContinuous

/-- The probability Dirac valuation. -/
noncomputable def probabilityDirac {D : Type u} [Preorder D]
    (x : D) : VOne D := by
  refine ⟨(dirac x).1, ?_⟩
  rw [dirac_apply, openIndicator_of_mem (ScottOpen.mem_univ x)]

@[simp] theorem probabilityDirac_toVSub
    {D : Type u} [Preorder D] (x : D) :
    VOne.toVSub (probabilityDirac x) = dirac x := rfl

/-- Probability Dirac is Scott-continuous. -/
theorem probabilityDirac_scottContinuous
    {D : Type u} [Preorder D] :
    AbramskyJung.Chapter2.ScottContinuous
      (probabilityDirac : D → VOne D) := by
  constructor
  · intro x y hxy
    exact dirac_scottContinuous.monotone hxy
  · intro A s hA hs
    have hDirac := dirac_scottContinuous.maps_isSup hA hs
    constructor
    · rintro _ ⟨x, hxA, rfl⟩
      exact hDirac.1 ⟨x, hxA, rfl⟩
    · intro nu hnu
      have hle : dirac s ≤ VOne.toVSub nu := hDirac.2 _ (by
        rintro _ ⟨x, hxA, rfl⟩
        exact hnu ⟨x, hxA, rfl⟩)
      exact hle

/-- Bundled probability Dirac unit. -/
noncomputable def probabilityUnit {D : Type u} [Preorder D] :
    ScottContFun D (VOne D) where
  toFun := probabilityDirac
  continuous := probabilityDirac_scottContinuous (D := D)

/-- Forgetting normalization in a probability-valued kernel. -/
def probabilityKernelToVSub
    {D E : Type u} [Preorder D] [Preorder E]
    (k : ScottContFun D (VOne E)) : ScottContFun D (VSub E) :=
  ScottContFun.comp vOneToVSubMap k

/-- At the whole carrier, every probability kernel section is the constant
one function, i.e. the indicator of the whole Scott open. -/
theorem probabilityKernelSection_univ
    {D E : Type u} [Preorder D] [Preorder E]
    (k : ScottContFun D (VOne E)) :
    kernelSection (probabilityKernelToVSub k) ScottOpen.univ =
      BoundedScottFunction.indicator (ScottOpen.univ : ScottOpen D) := by
  apply BoundedScottFunction.ext
  intro x
  change k x ScottOpen.univ = openIndicator ScottOpen.univ x
  rw [openIndicator_of_mem (ScottOpen.mem_univ x)]
  exact (k x).2

/-- Jones bind of a probability kernel against a probability input has total
mass exactly one. -/
theorem probabilityBind_total
    {D E : Type u} [Preorder D] [Preorder E]
    (k : ScottContFun D (VOne E)) (mu : VOne D) :
    bind (probabilityKernelToVSub k) (VOne.toVSub mu)
        ScottOpen.univ = 1 := by
  rw [bind_apply, probabilityKernelSection_univ, integral_indicator]
  exact mu.2

/-- Kleisli extension for probability valuations, derived from the Jones
subprobability extension and the preceding mass-one calculation. -/
noncomputable def probabilityBind
    {D E : Type u} [Preorder D] [Preorder E]
    (k : ScottContFun D (VOne E)) (mu : VOne D) : VOne E :=
  ⟨(bind (probabilityKernelToVSub k) (VOne.toVSub mu)).1,
    probabilityBind_total k mu⟩

@[simp] theorem probabilityBind_toVSub
    {D E : Type u} [Preorder D] [Preorder E]
    (k : ScottContFun D (VOne E)) (mu : VOne D) :
    VOne.toVSub (probabilityBind k mu) =
      bind (probabilityKernelToVSub k) (VOne.toVSub mu) := rfl

/-- Probability bind is Scott-continuous in its input valuation. -/
theorem probabilityBind_scottContinuous_input
    {D E : Type u} [Preorder D] [Preorder E]
    (k : ScottContFun D (VOne E)) :
    AbramskyJung.Chapter2.ScottContinuous (probabilityBind k) := by
  let lifted := probabilityKernelToVSub k
  constructor
  · intro mu nu hmunu
    exact bind_mono_input lifted (vOneInclusion_monotone hmunu)
  · intro A s hA hs
    have hInclDir : DirectedSet (VOne.toVSub '' A) :=
      vOneInclusion_scottContinuous.image_directed hA
    have hInclSup : IsSup (VOne.toVSub '' A) (VOne.toVSub s) :=
      vOneInclusion_scottContinuous.maps_isSup hA hs
    have hBindSup :=
      (bind_scottContinuous_input lifted).maps_isSup hInclDir hInclSup
    constructor
    · rintro _ ⟨mu, hmuA, rfl⟩
      exact bind_mono_input lifted
        (vOneInclusion_monotone (hs.1 hmuA))
    · intro tau htau
      have hle : bind lifted (VOne.toVSub s) ≤ VOne.toVSub tau :=
        hBindSup.2 _ (by
          rintro _ ⟨rho, ⟨mu, hmuA, rfl⟩, rfl⟩
          exact htau ⟨mu, hmuA, rfl⟩)
      exact hle

/-- Bundled probability Kleisli extension. -/
noncomputable def probabilityExtend
    {D E : Type u} [Preorder D] [Preorder E]
    (k : ScottContFun D (VOne E)) : ScottContFun (VOne D) (VOne E) where
  toFun := probabilityBind k
  continuous := probabilityBind_scottContinuous_input k

@[simp] theorem probabilityBind_dirac
    {D E : Type u} [Preorder D] [Preorder E]
    (k : ScottContFun D (VOne E)) (x : D) :
    probabilityBind k (probabilityDirac x) = k x := by
  apply VOne.toVSub_injective
  change bind (probabilityKernelToVSub k) (dirac x) = VOne.toVSub (k x)
  exact bind_dirac (probabilityKernelToVSub k) x

@[simp] theorem probabilityBind_unit
    {D : Type u} [Preorder D] (mu : VOne D) :
    probabilityBind (probabilityUnit (D := D)) mu = mu := by
  apply VOne.toVSub_injective
  change bind (probabilityKernelToVSub probabilityUnit)
      (VOne.toVSub mu) = VOne.toVSub mu
  have hkernel : probabilityKernelToVSub
      (probabilityUnit (D := D)) = unit (D := D) := by
    apply ScottContFun.ext_apply
    intro x
    exact probabilityDirac_toVSub x
  rw [hkernel, bind_unit]

/-- Probability Kleisli composition. -/
noncomputable def probabilityKleisliCompose
    {D E F : Type u} [Preorder D] [Preorder E] [Preorder F]
    (k : ScottContFun D (VOne E)) (l : ScottContFun E (VOne F)) :
    ScottContFun D (VOne F) :=
  ScottContFun.comp (probabilityExtend l) k

theorem probabilityBind_assoc
    {D E F : Type u} [Preorder D] [Preorder E] [Preorder F]
    (k : ScottContFun D (VOne E)) (l : ScottContFun E (VOne F))
    (mu : VOne D) :
    probabilityBind l (probabilityBind k mu) =
      probabilityBind (probabilityKleisliCompose k l) mu := by
  apply VOne.toVSub_injective
  change bind (probabilityKernelToVSub l)
      (bind (probabilityKernelToVSub k) (VOne.toVSub mu)) =
    bind (probabilityKernelToVSub (probabilityKleisliCompose k l))
      (VOne.toVSub mu)
  rw [bind_assoc]
  apply congrArg (fun q => bind q (VOne.toVSub mu))
  apply ScottContFun.ext_apply
  intro x
  exact (probabilityBind_toVSub l (k x)).symm

end ContinuousValuation

/-! ## Restriction of the probability valuation monad -/

/-- Object action of the probability valuation monad on FVA. -/
def vOneFVAObject
    (hFiniteDouble : FiniteDoubleValuationGeneratorsAreFVA.{u})
    (X : FVAObject.{u}) : FVAObject.{u} where
  carrier := ContinuousValuation.VOne X
  partialOrder := inferInstance
  isFVA := global_vOne_of_finite_double_generators hFiniteDouble X.isFVA

/-- Probability Dirac as an FVA morphism. -/
noncomputable def vOneFVAUnit
    (hFiniteDouble : FiniteDoubleValuationGeneratorsAreFVA.{u})
    (X : FVAObject.{u}) :
    FVAHom X (vOneFVAObject hFiniteDouble X) :=
  ContinuousValuation.probabilityUnit (D := X)

/-- Probability Kleisli extension as an FVA morphism. -/
noncomputable def vOneFVAExtend
    (hFiniteDouble : FiniteDoubleValuationGeneratorsAreFVA.{u})
    {X Y : FVAObject.{u}}
    (k : FVAHom X (vOneFVAObject hFiniteDouble Y)) :
    FVAHom (vOneFVAObject hFiniteDouble X)
      (vOneFVAObject hFiniteDouble Y) :=
  ContinuousValuation.probabilityExtend k

/-- Arrow action, recovered in the standard way from unit and Kleisli
extension.  Its underlying subprobability map is ordinary pushforward. -/
noncomputable def vOneFVAMap
    (hFiniteDouble : FiniteDoubleValuationGeneratorsAreFVA.{u})
    {X Y : FVAObject.{u}} (f : FVAHom X Y) :
    FVAHom (vOneFVAObject hFiniteDouble X)
      (vOneFVAObject hFiniteDouble Y) :=
  vOneFVAExtend hFiniteDouble
    (fvaHomComp (vOneFVAUnit hFiniteDouble Y) f)

/-- Probability monad multiplication. -/
noncomputable def vOneFVAMultiplication
    (hFiniteDouble : FiniteDoubleValuationGeneratorsAreFVA.{u})
    (X : FVAObject.{u}) :
    FVAHom (vOneFVAObject hFiniteDouble (vOneFVAObject hFiniteDouble X))
      (vOneFVAObject hFiniteDouble X) :=
  vOneFVAExtend hFiniteDouble (fvaHomId (vOneFVAObject hFiniteDouble X))

theorem vOneFVAMap_toVSub
    (hFiniteDouble : FiniteDoubleValuationGeneratorsAreFVA.{u})
    {X Y : FVAObject.{u}} (f : FVAHom X Y)
    (mu : ContinuousValuation.VOne X) :
    ContinuousValuation.VOne.toVSub (vOneFVAMap hFiniteDouble f mu) =
      ContinuousValuation.pushforward f
        (ContinuousValuation.VOne.toVSub mu) := by
  change ContinuousValuation.bind
      (ContinuousValuation.probabilityKernelToVSub
        (fvaHomComp (vOneFVAUnit hFiniteDouble Y) f))
      (ContinuousValuation.VOne.toVSub mu) = _
  have hkernel :
      ContinuousValuation.probabilityKernelToVSub
          (fvaHomComp (vOneFVAUnit hFiniteDouble Y) f) =
        ScottContFun.comp (ContinuousValuation.unit (D := Y)) f := by
    apply ScottContFun.ext_apply
    intro x
    exact ContinuousValuation.probabilityDirac_toVSub (f x)
  rw [hkernel]
  exact ContinuousValuation.bind_unit_comp_eq_pushforward f _

theorem vOneFVAMap_id
    (hFiniteDouble : FiniteDoubleValuationGeneratorsAreFVA.{u})
    (X : FVAObject.{u}) :
    vOneFVAMap hFiniteDouble (fvaHomId X) =
      fvaHomId (vOneFVAObject hFiniteDouble X) := by
  apply AbramskyJung.Chapter3.ContFun.ext_apply
  intro mu
  apply ContinuousValuation.VOne.toVSub_injective
  rw [vOneFVAMap_toVSub]
  exact ContinuousValuation.pushforward_idMap _

theorem vOneFVAMap_comp
    (hFiniteDouble : FiniteDoubleValuationGeneratorsAreFVA.{u})
    {X Y Z : FVAObject.{u}}
    (g : FVAHom Y Z) (f : FVAHom X Y) :
    vOneFVAMap hFiniteDouble (fvaHomComp g f) =
      fvaHomComp (vOneFVAMap hFiniteDouble g)
        (vOneFVAMap hFiniteDouble f) := by
  apply AbramskyJung.Chapter3.ContFun.ext_apply
  intro mu
  apply ContinuousValuation.VOne.toVSub_injective
  change ContinuousValuation.VOne.toVSub
      (vOneFVAMap hFiniteDouble (fvaHomComp g f) mu) =
    ContinuousValuation.VOne.toVSub
      (vOneFVAMap hFiniteDouble g (vOneFVAMap hFiniteDouble f mu))
  rw [vOneFVAMap_toVSub, vOneFVAMap_toVSub, vOneFVAMap_toVSub]
  exact (ContinuousValuation.pushforward_comp f g
    (ContinuousValuation.VOne.toVSub mu)).symm

theorem vOneFVAExtend_unit_left
    (hFiniteDouble : FiniteDoubleValuationGeneratorsAreFVA.{u})
    {X Y : FVAObject.{u}}
    (k : FVAHom X (vOneFVAObject hFiniteDouble Y)) :
    fvaHomComp (vOneFVAExtend hFiniteDouble k)
        (vOneFVAUnit hFiniteDouble X) = k := by
  apply AbramskyJung.Chapter3.ContFun.ext_apply
  intro x
  change ContinuousValuation.probabilityBind k
      (ContinuousValuation.probabilityDirac x) = k x
  exact ContinuousValuation.probabilityBind_dirac k x

theorem vOneFVAExtend_unit_right
    (hFiniteDouble : FiniteDoubleValuationGeneratorsAreFVA.{u})
    (X : FVAObject.{u}) :
    vOneFVAExtend hFiniteDouble (vOneFVAUnit hFiniteDouble X) =
      fvaHomId (vOneFVAObject hFiniteDouble X) := by
  apply AbramskyJung.Chapter3.ContFun.ext_apply
  intro mu
  change ContinuousValuation.probabilityBind
      (ContinuousValuation.probabilityUnit (D := X)) mu = mu
  exact ContinuousValuation.probabilityBind_unit mu

theorem vOneFVAExtend_assoc
    (hFiniteDouble : FiniteDoubleValuationGeneratorsAreFVA.{u})
    {X Y Z : FVAObject.{u}}
    (k : FVAHom X (vOneFVAObject hFiniteDouble Y))
    (l : FVAHom Y (vOneFVAObject hFiniteDouble Z)) :
    fvaHomComp (vOneFVAExtend hFiniteDouble l)
        (vOneFVAExtend hFiniteDouble k) =
      vOneFVAExtend hFiniteDouble
        (fvaHomComp (vOneFVAExtend hFiniteDouble l) k) := by
  apply AbramskyJung.Chapter3.ContFun.ext_apply
  intro mu
  change ContinuousValuation.probabilityBind l
      (ContinuousValuation.probabilityBind k mu) =
    ContinuousValuation.probabilityBind
      (ContinuousValuation.probabilityKleisliCompose k l) mu
  exact ContinuousValuation.probabilityBind_assoc k l mu

/-- The probability valuation monad genuinely restricts to FVA objects. -/
noncomputable def vOneFVAMonadRestriction
    (hFiniteDouble : FiniteDoubleValuationGeneratorsAreFVA.{u}) :
    FVAKleisliMonadRestriction.{u} where
  object := vOneFVAObject hFiniteDouble
  map := vOneFVAMap hFiniteDouble
  unit := vOneFVAUnit hFiniteDouble
  multiplication := vOneFVAMultiplication hFiniteDouble
  extend := vOneFVAExtend hFiniteDouble
  map_id := vOneFVAMap_id hFiniteDouble
  map_comp := vOneFVAMap_comp hFiniteDouble
  extend_unit_left := vOneFVAExtend_unit_left hFiniteDouble
  extend_unit_right := vOneFVAExtend_unit_right hFiniteDouble
  extend_assoc := vOneFVAExtend_assoc hFiniteDouble
  map_as_extend := fun _ => rfl
  multiplication_as_extend := fun _ => rfl

/-! ## Source-facing final package -/

/-- The actual local structures claimed in the manuscript's `Hence` sentence:
the full FVA subcategory has terminal objects, binary products and
exponentials with their universal properties, while both valuation monads
restrict with continuous unit/multiplication and all monad laws. -/
structure MainTheoremCategoricalConsequences
    (hFiniteFunctions : FiniteFunctionGeneratorsAreFVA.{u})
    (hFiniteDouble : FiniteDoubleValuationGeneratorsAreFVA.{u}) where
  cartesianClosed : FVALocalCartesianClosed hFiniteFunctions
  vSubRestriction : FVAKleisliMonadRestriction.{u}
  vOneRestriction : FVAKleisliMonadRestriction.{u}

/-- Categorical `Hence` conclusion of the main theorem, conditional on exactly
the same two isolated finite-generator inputs as the objectwise assembly. -/
noncomputable def thm_main_categorical_consequences_of_generators
    (hFiniteFunctions : FiniteFunctionGeneratorsAreFVA.{u})
    (hFiniteDouble : FiniteDoubleValuationGeneratorsAreFVA.{u}) :
    MainTheoremCategoricalConsequences hFiniteFunctions hFiniteDouble where
  cartesianClosed := fvaLocalCartesianClosed hFiniteFunctions
  vSubRestriction := vSubFVAMonadRestriction hFiniteDouble
  vOneRestriction := vOneFVAMonadRestriction hFiniteDouble

end FiniteValuationApproximable
