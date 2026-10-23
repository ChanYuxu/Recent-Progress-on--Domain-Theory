import ZFCFubini.ValuationOrder
import ZFCFubini.DcpoCategory

/-!
# The continuous subprobability valuation endofunctor

The object part uses all actual continuous subprobability valuations on the
intrinsic Scott topology. The arrow part is the existing actual pushforward.
The unit is Dirac mass, not a chosen representation of a valuation.
-/

set_option autoImplicit false
open Set Topology TopologicalSpace CategoryTheory
open scoped Classical
universe u

namespace ZFCFubini.ValuationMonad

noncomputable def obj (P : DcpoCat.{u}) : DcpoCat :=
  DcpoCat.of (SubprobValuation (WithScott P)) (subprobValuation_isDcpo _)

noncomputable def map {P Q : DcpoCat.{u}} (f : P ⟶ Q) : obj P ⟶ obj Q :=
  ⟨fun μ => μ.push
    (fun x => WithScott.toScott (f (WithScott.ofScott x)))
    ((scott_continuous_iff f).mp f.continuous),
    SubprobValuation.push_scottContinuous _ _⟩

@[simp] theorem map_apply {P Q : DcpoCat.{u}} (f : P ⟶ Q) (μ : obj P) (U : ScottOpens Q) :
    (map f μ).val U = μ.val (Opens.comap
      ⟨fun x => WithScott.toScott (f (WithScott.ofScott x)),
        (scott_continuous_iff f).mp f.continuous⟩ U) := rfl

/-- The genuine categorical endofunctor on dcpos and Scott maps. -/
noncomputable def functor : DcpoCat.{u} ⥤ DcpoCat.{u} where
  obj := obj
  map := map
  map_id P := by
    apply DcpoCat.Hom.ext
    intro μ
    apply Subtype.ext
    apply Valuation.ext
    intro U
    rfl
  map_comp f g := by
    apply DcpoCat.Hom.ext
    intro μ
    apply Subtype.ext
    apply Valuation.ext
    intro U
    rfl

noncomputable def unit (P : DcpoCat.{u}) : P ⟶ obj P :=
  ⟨fun p => SubprobValuation.dirac (WithScott.toScott p),
    SubprobValuation.dirac_scottContinuous⟩

@[simp] theorem unit_apply (P : DcpoCat.{u}) (p : P) (U : ScottOpens P) :
    (unit P p).val U = if WithScott.toScott p ∈ U then 1 else 0 := by
  classical exact Valuation.dirac_apply _ _

noncomputable def unitNatTrans : 𝟭 DcpoCat.{u} ⟶ functor where
  app := unit
  naturality {P Q} f := by
    apply DcpoCat.Hom.ext
    intro p
    apply Subtype.ext
    apply Valuation.ext
    intro U
    classical
    simp only [DcpoCat.comp_apply, unit_apply, map_apply, Valuation.dirac_apply]
    rfl

end ZFCFubini.ValuationMonad
