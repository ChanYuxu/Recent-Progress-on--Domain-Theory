import FiniteValuationApproximable.Abstract.CountableBasis
import FiniteValuationApproximable.FiniteValuation.ProbabilityFS
import FiniteValuationApproximable.FiniteValuation.Kernel

/-!
# Global transfer: exact algebra and explicit semantic boundaries

This file formalizes the valuation-independent and finite/discrete core of
source lines 3135--3475 of `main (17).tex` (source SHA-256
`4b2e65f0f96347bea4df7571e8993ad6e888c0ff7181c1305c5056880365ac94`).

The unconditional results include:

* product distributions and their two marginals on finite probability
  vectors, including stochastic monotonicity and the retraction equation;
* transport of section--retraction pairs through order isomorphisms;
* the explicit finite-poset stage used for the generator-product argument;
* product and function-sandwich approximate identities and their exact
  algebraic factorizations;
* the valuation-independent flattening of approximations through FVA
  intermediate objects, conditional only on the openly named finite-stage FS
  premise already used by `Abstract.Saturation`.

The current project has no type for continuous valuations on an arbitrary
dcpo and no proved Jones--Plotkin/Jones local-continuity theorem.  Moreover,
the finite-dimensional Euclidean-to-Scott step needed to upgrade the product
distribution/marginal retraction is not yet in the local API.  Consequently
the source-facing global closure theorems below are explicitly named
`..._conditional` and expose these premises as arguments.  No unconditional
version of `cor:finite-generators`, `thm:global-transfer`,
`thm:global-Vone`, or `thm:main` is asserted.
-/

set_option autoImplicit false
set_option linter.unnecessarySimpa false

universe u v w z

namespace FiniteValuationApproximable

open scoped BigOperators
open AbstractApproximation
open SubprobabilityVector

/-- Bridge the Chapter 2 bundled-map type used by approximate identities to
the Chapter 3 bundled-map type used for function spaces. -/
def asContFun {D : Type u} {E : Type v} [Preorder D] [Preorder E]
    (f : ScottContFun D E) : AbramskyJung.Chapter3.ContFun D E :=
  f

/-! ## General order/continuity transport utilities -/

/-- Bundled continuous maps into a partial order are themselves a partial
order under pointwise comparison. -/
instance contFunPartialOrder
    {D : Type u} {E : Type v} [Preorder D] [PartialOrder E] :
    PartialOrder (AbramskyJung.Chapter3.ContFun D E) where
  le_antisymm f g hfg hgf := by
    apply AbramskyJung.Chapter3.ContFun.ext_apply
    intro x
    exact le_antisymm (hfg x) (hgf x)

/-- Product of two order isomorphisms. -/
def prodOrderIso
    {D : Type u} {D' : Type v} {E : Type w} {E' : Type z}
    [Preorder D] [Preorder D'] [Preorder E] [Preorder E']
    (e : D ≃o D') (f : E ≃o E') : D × E ≃o D' × E' where
  toEquiv := e.toEquiv.prodCongr f.toEquiv
  map_rel_iff' := by
    intro x y
    exact and_congr e.le_iff_le f.le_iff_le

/-- Transport a continuous section--retraction pair across order
isomorphisms on source and target. -/
def transportContinuousSectionRetractionPair
    {D : Type u} {D' : Type v} {E : Type w} {E' : Type z}
    [Preorder D] [Preorder D'] [Preorder E] [Preorder E']
    (sourceIso : D ≃o D') (targetIso : E ≃o E')
    (sr : AbramskyJung.Chapter3.ContinuousSectionRetractionPair D' E') :
    AbramskyJung.Chapter3.ContinuousSectionRetractionPair D E where
  s x := targetIso.symm (sr.s (sourceIso x))
  r y := sourceIso.symm (sr.r (targetIso y))
  monotone_s := by
    intro x y hxy
    exact targetIso.symm.monotone (sr.monotone_s (sourceIso.monotone hxy))
  monotone_r := by
    intro x y hxy
    exact sourceIso.symm.monotone (sr.monotone_r (targetIso.monotone hxy))
  retract x := by simp [sr.retract]
  continuous_s :=
    (orderIso_scottContinuous targetIso.symm).comp
      (sr.continuous_s.comp (orderIso_scottContinuous sourceIso))
  continuous_r :=
    (orderIso_scottContinuous sourceIso.symm).comp
      (sr.continuous_r.comp (orderIso_scottContinuous targetIso))

/-- A Scott factorization through a retract of another intermediate object
lifts to a factorization through the ambient retract object. -/
def ScottFactorization.liftThroughRetract
    {D : Type u} {E : Type v} {B : Type w} {C : Type z}
    [Preorder D] [Preorder E] [Preorder B] [Preorder C]
    {f : D -> E} (F : ScottFactorization f B)
    (sr : AbramskyJung.Chapter3.ContinuousSectionRetractionPair B C) :
    ScottFactorization f C where
  encode x := sr.s (F.encode x)
  decode c := F.decode (sr.r c)
  encode_continuous := sr.continuous_s.comp F.encode_continuous
  decode_continuous := F.decode_continuous.comp sr.continuous_r
  factor x := by rw [sr.retract, F.factor]

/-- Conditional generator theorem already implicit in the current API: once
finite stages are known to be continuous dcpos, their constant identity
approximation makes them FVA objects. -/
theorem finiteStage_isFVA_conditional
    (hDomains : FiniteStagesAreContinuousDcpos.{u})
    (P : FinitePoset.{u}) : IsFVA.{u, u} P.VSub :=
  ⟨hDomains P, ⟨finiteStageApproximateIdentity P⟩⟩

/-! ## Relabelling finite subprobability vectors -/

section Relabelling

variable {P : Type u} {Q : Type v}
variable [Fintype P] [Fintype Q] [PartialOrder P] [PartialOrder Q]

/-- Pushforward along a monotone finite map is monotone in its input law. -/
theorem finitePushforward_mono_input
    {mu nu : SubprobabilityVector P} (hmunu : mu <= nu)
    {f : P -> Q} (hf : Monotone f) :
    finitePushforward mu f <= finitePushforward nu f := by
  apply finiteBind_mono_input hmunu
  intro x y hxy
  exact dirac_le_dirac_iff.mpr (hf hxy)

/-- Relabelling along an order isomorphism is an order isomorphism of finite
subprobability vectors. -/
noncomputable def subprobabilityOrderIso (e : P ≃o Q) :
    SubprobabilityVector P ≃o SubprobabilityVector Q where
  toFun mu := finitePushforward mu e
  invFun nu := finitePushforward nu e.symm
  left_inv mu := by
    calc
      finitePushforward (finitePushforward mu e) e.symm =
          finitePushforward mu (e.symm ∘ e) :=
        finitePushforward_comp mu e e.symm
      _ = finitePushforward mu id := by
        congr 1
        funext x
        exact e.symm_apply_apply x
      _ = mu := finitePushforward_id mu
  right_inv nu := by
    calc
      finitePushforward (finitePushforward nu e.symm) e =
          finitePushforward nu (e ∘ e.symm) :=
        finitePushforward_comp nu e.symm e
      _ = finitePushforward nu id := by
        congr 1
        funext x
        exact e.apply_symm_apply x
      _ = nu := finitePushforward_id nu
  map_rel_iff' := by
    intro mu nu
    constructor
    · intro h
      change finitePushforward mu (fun x => e x) <=
        finitePushforward nu (fun x => e x) at h
      have h' :
          finitePushforward (finitePushforward mu (fun x => e x))
              (fun y => e.symm y) <=
            finitePushforward (finitePushforward nu (fun x => e x))
              (fun y => e.symm y) :=
        finitePushforward_mono_input (P := Q) (Q := P) h e.symm.monotone
      have hmuId : finitePushforward mu (fun x : P => x) = mu := by
        change finitePushforward mu id = mu
        exact finitePushforward_id mu
      have hnuId : finitePushforward nu (fun x : P => x) = nu := by
        change finitePushforward nu id = nu
        exact finitePushforward_id nu
      have hcomp :
          (fun y => e.symm y) ∘ (fun x => e x) = (fun x : P => x) := by
        funext x
        exact e.symm_apply_apply x
      rw [finitePushforward_comp, finitePushforward_comp,
        hcomp, hmuId, hnuId] at h'
      exact h'
    · exact fun h => finitePushforward_mono_input h e.monotone

end Relabelling

/-- Deleting the fresh bottom from `WithBot P` recovers `P` as an ordered
type. -/
def withoutBotOrderIso (P : Type u) [PartialOrder P] :
    WithoutPoint (⊥ : WithBot P) ≃o P where
  toEquiv := Equiv.withBotSubtypeNe
  map_rel_iff' := by
    intro x y
    exact WithBot.unbot_le_unbot_iff x.2 y.2

/-- A single canonical classical `Fintype` for deleting one point.  Naming
this instance prevents otherwise extensionally equal decidability procedures
from producing non-definitionally-equal finite-vector types. -/
noncomputable abbrev withoutPointFintype
    (X : Type u) [Fintype X] (bot : X) : Fintype (WithoutPoint bot) :=
  @Subtype.fintype X (fun x => x ≠ bot)
    (fun x => @instDecidableNot (x = bot)
      (Classical.propDecidable (x = bot))) inferInstance

/-- The source's missing-mass-at-bottom isomorphism, oriented from finite
subprobabilities on `P` to probabilities on `WithBot P`. -/
noncomputable def subprobabilityWithBotProbabilityOrderIso
    (P : Type u) [hP : Fintype P] [PartialOrder P] :
    SubprobabilityVector P ≃o ProbabilityVector (WithBot P) := by
  classical
  exact ((probabilityOrderIso (⊥ : WithBot P) (fun _ => bot_le)).trans
    (@subprobabilityOrderIso (WithoutPoint (⊥ : WithBot P)) P
      (withoutPointFintype (WithBot P) (⊥ : WithBot P)) hP
      inferInstance inferInstance (withoutBotOrderIso P))).symm

/-! ## Product distributions and marginals -/

section ProbabilityProducts

variable {P : Type u} {Q : Type v}
variable [Fintype P] [Fintype Q]

/-- Ordinary product of two finite probability distributions. -/
noncomputable def probabilityProduct
    (mu : ProbabilityVector P) (nu : ProbabilityVector Q) :
    ProbabilityVector (P × Q) := by
  let coeff : P × Q -> Real := fun p => mu p.1 * nu p.2
  have hsum : (∑ p : P × Q, coeff p) = 1 := by
    classical
    rw [Fintype.sum_prod_type]
    calc
      (∑ x : P, ∑ y : Q, mu x * nu y) =
          ∑ x : P, mu x * (∑ y : Q, nu y) := by
            apply Finset.sum_congr rfl
            intro x hx
            rw [Finset.mul_sum]
      _ = ∑ x : P, mu x := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [show (∑ y : Q, nu y) = 1 from nu.2]
        ring
      _ = 1 := mu.2
  let result : SubprobabilityVector (P × Q) := {
    coeff := coeff
    coeff_nonneg := fun p =>
      mul_nonneg (mu.1.coeff_nonneg p.1) (nu.1.coeff_nonneg p.2)
    total_le_one := hsum.le }
  exact ⟨result, hsum⟩

@[simp]
theorem probabilityProduct_apply
    (mu : ProbabilityVector P) (nu : ProbabilityVector Q) (p : P × Q) :
    probabilityProduct mu nu p = mu p.1 * nu p.2 :=
  rfl

/-- Finite Fubini formula for a product distribution. -/
theorem weightedSum_probabilityProduct
    (mu : ProbabilityVector P) (nu : ProbabilityVector Q)
    (g : P × Q -> Real) :
    weightedSum (probabilityProduct mu nu).1 g =
      weightedSum mu.1 (fun x => weightedSum nu.1 (fun y => g (x, y))) := by
  classical
  simp only [weightedSum, probabilityProduct_apply]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y hy
  ring

/-- The two marginal laws of a finite probability vector on a product. -/
noncomputable def probabilityMarginals
    (xi : ProbabilityVector (P × Q)) :
    ProbabilityVector P × ProbabilityVector Q :=
  (probabilityPushforward xi Prod.fst,
    probabilityPushforward xi Prod.snd)

/-- First marginal of a product distribution. -/
theorem firstMarginal_probabilityProduct
    (mu : ProbabilityVector P) (nu : ProbabilityVector Q) :
    (probabilityMarginals (probabilityProduct mu nu)).1 = mu := by
  apply ProbabilityVector.ext
  intro x
  classical
  simp only [probabilityMarginals, probabilityPushforward_apply,
    probabilityProduct_apply, dirac_apply]
  rw [Fintype.sum_prod_type]
  calc
    (∑ a : P, ∑ b : Q, (mu a * nu b) * if x = a then 1 else 0) =
        ∑ a : P, mu a * (if x = a then 1 else 0) * (∑ b : Q, nu b) := by
          apply Finset.sum_congr rfl
          intro a ha
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro b hb
          ring
    _ = ∑ a : P, mu a * (if x = a then 1 else 0) := by
      have hnu : (∑ b : Q, nu b) = 1 := by
        simpa [SubprobabilityVector.totalMass] using nu.2
      rw [hnu]
      simp
    _ = mu x := by simp

/-- Second marginal of a product distribution. -/
theorem secondMarginal_probabilityProduct
    (mu : ProbabilityVector P) (nu : ProbabilityVector Q) :
    (probabilityMarginals (probabilityProduct mu nu)).2 = nu := by
  apply ProbabilityVector.ext
  intro y
  classical
  simp only [probabilityMarginals, probabilityPushforward_apply,
    probabilityProduct_apply, dirac_apply]
  rw [Fintype.sum_prod_type]
  calc
    (∑ a : P, ∑ b : Q, (mu a * nu b) * if y = b then 1 else 0) =
        ∑ a : P, mu a * (∑ b : Q, nu b * (if y = b then 1 else 0)) := by
          apply Finset.sum_congr rfl
          intro a ha
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro b hb
          ring
    _ = (∑ a : P, mu a) *
        (∑ b : Q, nu b * (if y = b then 1 else 0)) := by
          rw [Finset.sum_mul]
    _ = ∑ b : Q, nu b * (if y = b then 1 else 0) := by
      have hmu : (∑ a : P, mu a) = 1 := by
        simpa [SubprobabilityVector.totalMass] using mu.2
      rw [hmu]
      simp
    _ = nu y := by simp

theorem probabilityMarginals_product
    (mu : ProbabilityVector P) (nu : ProbabilityVector Q) :
    probabilityMarginals (probabilityProduct mu nu) = (mu, nu) := by
  apply Prod.ext
  · exact firstMarginal_probabilityProduct mu nu
  · exact secondMarginal_probabilityProduct mu nu

end ProbabilityProducts

section ProbabilityProductOrder

variable {P : Type u} {Q : Type v}
variable [Fintype P] [Fintype Q] [PartialOrder P] [PartialOrder Q]

/-- Product distribution is monotone in both probability laws for stochastic
order. -/
theorem probabilityProduct_mono
    {mu mu' : ProbabilityVector P} {nu nu' : ProbabilityVector Q}
    (hmu : mu <= mu') (hnu : nu <= nu') :
    probabilityProduct mu nu <= probabilityProduct mu' nu' := by
  change (probabilityProduct mu nu).1 <= (probabilityProduct mu' nu').1
  rw [stochasticLE_iff_weightedSum_le]
  intro g hg hg0
  rw [weightedSum_probabilityProduct, weightedSum_probabilityProduct]
  let inner : P -> Real := fun x => weightedSum nu.1 (fun y => g (x, y))
  let inner' : P -> Real := fun x => weightedSum nu'.1 (fun y => g (x, y))
  have hinner0 : forall x, 0 <= inner x := by
    intro x
    exact Finset.sum_nonneg fun y hy =>
      mul_nonneg (nu.1.coeff_nonneg y) (hg0 (x, y))
  have hinner_mono : Monotone inner := by
    intro x x' hxx'
    unfold inner weightedSum
    apply Finset.sum_le_sum
    intro y hy
    exact mul_le_mul_of_nonneg_left (hg ⟨hxx', le_rfl⟩) (nu.1.coeff_nonneg y)
  have hinner_le : forall x, inner x <= inner' x := by
    intro x
    apply (stochasticLE_iff_weightedSum_le.mp hnu)
    · intro y y' hyy'
      exact hg ⟨le_rfl, hyy'⟩
    · intro y
      exact hg0 (x, y)
  calc
    weightedSum mu.1 inner <= weightedSum mu'.1 inner :=
      (stochasticLE_iff_weightedSum_le.mp hmu) inner hinner_mono hinner0
    _ <= weightedSum mu'.1 inner' := by
      unfold weightedSum
      apply Finset.sum_le_sum
      intro x hx
      exact mul_le_mul_of_nonneg_left (hinner_le x) (mu'.1.coeff_nonneg x)

/-- Pushforward of probabilities along a monotone finite map is monotone. -/
theorem probabilityPushforward_mono
    {mu nu : ProbabilityVector P} (hmunu : mu <= nu)
    {f : P -> Q} (hf : Monotone f) :
    probabilityPushforward mu f <= probabilityPushforward nu f :=
  finitePushforward_mono_input hmunu hf

theorem probabilityMarginals_mono :
    Monotone (probabilityMarginals :
      ProbabilityVector (P × Q) -> ProbabilityVector P × ProbabilityVector Q) := by
  intro xi xi' hxi
  exact ⟨probabilityPushforward_mono hxi (fun _ _ h => h.1),
    probabilityPushforward_mono hxi (fun _ _ h => h.2)⟩

/-- The product distribution and marginal maps form a monotone
section--retraction pair. -/
noncomputable def probabilityProductSectionRetractionPair :
    AbramskyJung.Chapter3.SectionRetractionPair
      (ProbabilityVector P × ProbabilityVector Q)
      (ProbabilityVector (P × Q)) where
  s p := probabilityProduct p.1 p.2
  r := probabilityMarginals
  monotone_s := by
    intro p q hpq
    exact probabilityProduct_mono hpq.1 hpq.2
  monotone_r := probabilityMarginals_mono
  retract p := probabilityMarginals_product p.1 p.2

/-- The one finite-dimensional semantic premise still missing locally from
the source proof of `prop:generator-product`: product distributions and
marginals preserve arbitrary existing directed suprema. -/
def ProbabilityProductMapsAreScottContinuous : Prop :=
  AbramskyJung.Chapter2.ScottContinuous
      (fun p : ProbabilityVector P × ProbabilityVector Q =>
        probabilityProduct p.1 p.2) ∧
    AbramskyJung.Chapter2.ScottContinuous
      (probabilityMarginals :
        ProbabilityVector (P × Q) ->
          ProbabilityVector P × ProbabilityVector Q)

/-- Under the explicitly named Euclidean-to-Scott premise, the algebraic
probability retraction upgrades to a continuous retraction. -/
noncomputable def probabilityProductContinuousSectionRetractionPair
    (hcont : ProbabilityProductMapsAreScottContinuous (P := P) (Q := Q)) :
    AbramskyJung.Chapter3.ContinuousSectionRetractionPair
      (ProbabilityVector P × ProbabilityVector Q)
      (ProbabilityVector (P × Q)) where
  toSectionRetractionPair := probabilityProductSectionRetractionPair
  continuous_s := by
    simpa [probabilityProductSectionRetractionPair] using hcont.1
  continuous_r := by
    simpa [probabilityProductSectionRetractionPair] using hcont.2

end ProbabilityProductOrder

/-! ## The finite generator-product retraction -/

/-- The finite poset obtained from the product of two bottom-adjoined posets
by deleting the joint least point. -/
abbrev ProductGeneratorCarrier
    (P : Type u) (Q : Type v) [PartialOrder P] [PartialOrder Q] :=
  WithoutPoint ((⊥, ⊥) : WithBot P × WithBot Q)

/-- Bundled finite stage used by `prop:generator-product`. -/
noncomputable def productGeneratorStage
    (P : FinitePoset.{u}) (Q : FinitePoset.{u}) : FinitePoset.{u} := by
  classical
  exact {
    carrier := ProductGeneratorCarrier P Q
    fintype := withoutPointFintype (WithBot P × WithBot Q) (⊥, ⊥)
    partialOrder := inferInstance }

/-- Conditional continuous retraction at the heart of
`prop:generator-product`.  All order isomorphisms and the retraction equation
are proved; only finite probability product/marginal Scott continuity is an
explicit premise. -/
noncomputable def generatorProductContinuousRetraction
    (P Q : FinitePoset.{u})
    (hcont : ProbabilityProductMapsAreScottContinuous
      (P := WithBot P) (Q := WithBot Q)) :
    AbramskyJung.Chapter3.ContinuousSectionRetractionPair
      (P.VSub × Q.VSub) (productGeneratorStage P Q).VSub := by
  classical
  let sourceIso :
      P.VSub × Q.VSub ≃o
        ProbabilityVector (WithBot P) × ProbabilityVector (WithBot Q) :=
    prodOrderIso (subprobabilityWithBotProbabilityOrderIso P)
      (subprobabilityWithBotProbabilityOrderIso Q)
  let targetIso :
      (productGeneratorStage P Q).VSub ≃o
        ProbabilityVector (WithBot P × WithBot Q) := by
    let carrierIso :
        (productGeneratorStage P Q : Type u) ≃o
          ProductGeneratorCarrier P Q := {
      toEquiv := Equiv.refl _
      map_rel_iff' := Iff.rfl }
    let stageIso :=
      @subprobabilityOrderIso
        (productGeneratorStage P Q : Type u)
        (ProductGeneratorCarrier P Q)
        (productGeneratorStage P Q).fintype
        (withoutPointFintype (WithBot P × WithBot Q) (⊥, ⊥))
        (productGeneratorStage P Q).partialOrder inferInstance carrierIso
    exact stageIso.trans
      (probabilityOrderIso ((⊥, ⊥) : WithBot P × WithBot Q)
        (fun x => Prod.le_def.mpr ⟨bot_le, bot_le⟩)).symm
  exact transportContinuousSectionRetractionPair sourceIso targetIso
    (probabilityProductContinuousSectionRetractionPair hcont)

/-- Uniform form of the sole finite-dimensional continuity dependency. -/
def AllProbabilityProductMapsAreScottContinuous : Prop :=
  ∀ P Q : FinitePoset.{u},
    ProbabilityProductMapsAreScottContinuous
      (P := WithBot P) (Q := WithBot Q)

/-- Exact conditional form of `prop:generator-product` in the current API. -/
theorem generatorProduct_isFVA_conditional
    (hDomains : FiniteStagesAreContinuousDcpos.{u})
    (hProductCont : AllProbabilityProductMapsAreScottContinuous.{u})
    (P Q : FinitePoset.{u}) : IsFVA.{u, u} (P.VSub × Q.VSub) := by
  apply IsFVA.retract
    (generatorProductContinuousRetraction P Q (hProductCont P Q))
  exact finiteStage_isFVA_conditional hDomains (productGeneratorStage P Q)

/-! ## Approximation through FVA intermediate objects -/

/-- A universe-bundled partially ordered FVA intermediate stage.  This is
data supplied to the conditional flattening theorem, not an assertion that a
particular source construction has already produced such a stage. -/
structure FVAIntermediateStage where
  carrier : Type u
  partialOrder : PartialOrder carrier
  isFVA : @IsFVA.{u, u} carrier partialOrder.toPreorder partialOrder

namespace FVAIntermediateStage

instance : CoeSort FVAIntermediateStage.{u} (Type u) where
  coe B := B.carrier

instance (B : FVAIntermediateStage.{u}) : PartialOrder B :=
  B.partialOrder

end FVAIntermediateStage

section IntermediateFlattening

variable {D : Type u} [PartialOrder D]

/-- A self-map factored through an explicitly FVA intermediate object. -/
structure FVAIntermediateFactorization (f : D -> D) where
  stage : FVAIntermediateStage.{w}
  factorization : ScottFactorization f stage

/-- An increasing approximate identity whose maps factor through FVA
objects, rather than immediately through finite valuation stages. -/
structure FVAIntermediateApproximateIdentity
    (D : Type u) [PartialOrder D]
    extends IncreasingApproximateIdentity D where
  factorable : ∀ n : Nat,
    Nonempty (FVAIntermediateFactorization.{u, w} (map n))

namespace FVAIntermediateApproximateIdentity

variable (A : FVAIntermediateApproximateIdentity.{u, w} D)

/-- The sandwiched inner approximation through the FVA intermediate stage. -/
noncomputable def innerMap
    {i : Nat}
    (F : FVAIntermediateFactorization.{u, w} (A.map i))
    (Q : SaturatedFVApproximateIdentity.{w, w} F.stage) (j : Nat) :
    ScottContFun D D where
  toFun x := F.factorization.decode
    (Q.map j (F.factorization.encode x))
  continuous := F.factorization.decode_continuous.comp
    ((Q.map j).continuous.comp F.factorization.encode_continuous)

theorem innerMap_monotone
    {i : Nat}
    (F : FVAIntermediateFactorization.{u, w} (A.map i))
    (Q : SaturatedFVApproximateIdentity.{w, w} F.stage)
    {j k : Nat} (hjk : j <= k) (x : D) :
    A.innerMap F Q j x <= A.innerMap F Q k x :=
  F.factorization.decode_continuous.monotone
    (Q.monotone hjk (F.factorization.encode x))

theorem innerMap_below
    {i : Nat}
    (F : FVAIntermediateFactorization.{u, w} (A.map i))
    (Q : SaturatedFVApproximateIdentity.{w, w} F.stage)
    (j : Nat) (x : D) : A.innerMap F Q j x <= x := by
  calc
    A.innerMap F Q j x <=
        F.factorization.decode (F.factorization.encode x) :=
      F.factorization.decode_continuous.monotone
        (Q.below_id j (F.factorization.encode x))
    _ = A.map i x := F.factorization.factor x
    _ <= x := A.below_id i x

theorem innerMap_finitelySeparated
    {i : Nat}
    (F : FVAIntermediateFactorization.{u, w} (A.map i))
    (Q : SaturatedFVApproximateIdentity.{w, w} F.stage)
    (j : Nat) : IsFinitelySeparated (A.innerMap F Q j) := by
  apply IsFinitelySeparated.sandwich (Q.finitelySeparated j)
    F.factorization.decode_continuous.monotone
  intro x
  rw [F.factorization.factor]
  exact A.below_id i x

theorem innerMap_pointwise_isSup
    {i : Nat}
    (F : FVAIntermediateFactorization.{u, w} (A.map i))
    (Q : SaturatedFVApproximateIdentity.{w, w} F.stage) (x : D) :
    AbramskyJung.Chapter2.IsSup (Set.range (fun j => A.innerMap F Q j x)) (A.map i x) := by
  have hmapped := F.factorization.decode_continuous.maps_isSup
    (Q.range_directed (F.factorization.encode x))
    (Q.pointwise_sup (F.factorization.encode x))
  have hrange :
      Set.range (fun j => A.innerMap F Q j x) =
        F.factorization.decode ''
          Set.range (fun j => Q.map j (F.factorization.encode x)) := by
    ext y
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨Q.map j (F.factorization.encode x), ⟨j, rfl⟩, rfl⟩
    · rintro ⟨b, ⟨j, rfl⟩, rfl⟩
      exact ⟨j, rfl⟩
  rw [hrange]
  simpa only [F.factorization.factor x] using hmapped

/-- Each sandwiched inner map still factors through the finite valuation
stage selected by the intermediate FVA approximation. -/
noncomputable def innerMapFiniteFactorization
    {i : Nat}
    (F : FVAIntermediateFactorization.{u, w} (A.map i))
    (Q : SaturatedFVApproximateIdentity.{w, w} F.stage) (j : Nat) :
    FiniteValuationFactorization.{u, u, w} (A.innerMap F Q j) := by
  let H : FiniteValuationFactorization.{w, w, w} (Q.map j) :=
    Classical.choice (Q.factorable j)
  refine {
    stage := H.stage
    factorization := {
      encode := fun x => H.factorization.encode (F.factorization.encode x)
      decode := fun b => F.factorization.decode (H.factorization.decode b)
      encode_continuous := H.factorization.encode_continuous.comp
        F.factorization.encode_continuous
      decode_continuous := F.factorization.decode_continuous.comp
        H.factorization.decode_continuous
      factor := ?_ } }
  intro x
  rw [H.factorization.factor]
  rfl

/-- Conditional form of saturation part (ii): approximation through FVA
intermediate objects can be flattened to finite valuation stages. -/
theorem flatten
    (A : FVAIntermediateApproximateIdentity.{u, w} D)
    (hStages : FiniteStagesHaveFSApproximateIdentities.{w})
    (hD : AbramskyJung.Chapter2.IsContinuousDomain D) :
    Nonempty (FVApproximateIdentity.{u, w} D) := by
  let F : ∀ i : Nat, FVAIntermediateFactorization.{u, w} (A.map i) :=
    fun i => Classical.choice (A.factorable i)
  let Q : ∀ i : Nat, SaturatedFVApproximateIdentity.{w, w} (F i).stage :=
    fun i => Classical.choice ((F i).stage.isFVA.saturated hStages)
  let N : NestedApproximation D := {
    outer := A.toIncreasingApproximateIdentity
    inner := fun i j => A.innerMap (F i) (Q i) j
    inner_monotone := fun i j k hjk x => A.innerMap_monotone (F i) (Q i) hjk x
    inner_below_id := fun i j x => A.innerMap_below (F i) (Q i) j x
    inner_pointwise_sup := fun i x => A.innerMap_pointwise_isSup (F i) (Q i) x
    inner_finitelySeparated := fun i j =>
      A.innerMap_finitelySeparated (F i) (Q i) j }
  rcases N.existsSquaredFSApproximateIdentity hD with ⟨C, hCmem⟩
  refine ⟨{
    toIncreasingApproximateIdentity := C.toIncreasingApproximateIdentity
    factorable := ?_ }⟩
  intro n
  rcases hCmem n with ⟨⟨i, j⟩, hij⟩
  have hfactor := (A.innerMapFiniteFactorization (F i) (Q i) j).factorization.square
  refine ⟨{
    stage := (A.innerMapFiniteFactorization (F i) (Q i) j).stage
    factorization := ?_ }⟩
  have hijfun :
      (fun x => A.innerMap (F i) (Q i) j
        (A.innerMap (F i) (Q i) j x)) = C.map n := by
    funext x
    have hx := congrArg (fun g : ScottContFun D D => g x) hij
    simpa only [N, squareMap_apply] using hx
  rw [← hijfun]
  exact hfactor

end FVAIntermediateApproximateIdentity

end IntermediateFlattening

/-! ## Product transfer -/

section ProductTransfer

variable {D : Type u} {E : Type u} [PartialOrder D] [PartialOrder E]

/-- Product of two increasing approximate identities, using the diagonal
sequence from the manuscript. -/
def increasingApproximateIdentityProd
    (A : IncreasingApproximateIdentity D)
    (B : IncreasingApproximateIdentity E) :
    IncreasingApproximateIdentity (D × E) where
  map n := {
    toFun := fun p => (A.map n p.1, B.map n p.2)
    continuous := AbramskyJung.Chapter3.prod_map_scottContinuous
      (A.map n).continuous (B.map n).continuous }
  monotone := by
    intro m n hmn p
    exact ⟨A.monotone hmn p.1, B.monotone hmn p.2⟩
  below_id := by
    intro n p
    exact ⟨A.below_id n p.1, B.below_id n p.2⟩
  pointwise_sup := by
    intro p
    constructor
    · intro q hq
      rcases hq with ⟨n, rfl⟩
      exact ⟨(A.pointwise_sup p.1).1 ⟨n, rfl⟩,
        (B.pointwise_sup p.2).1 ⟨n, rfl⟩⟩
    · intro q hq
      constructor
      · apply (A.pointwise_sup p.1).2 q.1
        intro a ha
        rcases ha with ⟨n, rfl⟩
        exact (hq ⟨n, rfl⟩).1
      · apply (B.pointwise_sup p.2).2 q.2
        intro b hb
        rcases hb with ⟨n, rfl⟩
        exact (hq ⟨n, rfl⟩).2

/-- Product of two abstract Scott factorizations. -/
def scottFactorizationProd
    {f : D -> D} {g : E -> E}
    {B : Type v} {C : Type w} [Preorder B] [Preorder C]
    (F : ScottFactorization f B) (G : ScottFactorization g C) :
    ScottFactorization (fun p : D × E => (f p.1, g p.2)) (B × C) where
  encode p := (F.encode p.1, G.encode p.2)
  decode q := (F.decode q.1, G.decode q.2)
  encode_continuous := AbramskyJung.Chapter3.prod_pair_scottContinuous
    (F.encode_continuous.comp AbramskyJung.Chapter3.prod_fst_scottContinuous)
    (G.encode_continuous.comp AbramskyJung.Chapter3.prod_snd_scottContinuous)
  decode_continuous := AbramskyJung.Chapter3.prod_pair_scottContinuous
    (F.decode_continuous.comp AbramskyJung.Chapter3.prod_fst_scottContinuous)
    (G.decode_continuous.comp AbramskyJung.Chapter3.prod_snd_scottContinuous)
  factor p := by rw [F.factor, G.factor]

/-- The product approximate identity factors through the product of the two
finite valuation stages. -/
noncomputable def productIntermediateFactorization
    (hDomains : FiniteStagesAreContinuousDcpos.{u})
    (hProductCont : AllProbabilityProductMapsAreScottContinuous.{u})
    (A : FVApproximateIdentity.{u, u} D)
    (B : FVApproximateIdentity.{u, u} E) (n : Nat) :
    FVAIntermediateFactorization.{u, u}
      ((increasingApproximateIdentityProd A.toIncreasingApproximateIdentity
        B.toIncreasingApproximateIdentity).map n) := by
  let FA : FiniteValuationFactorization.{u, u, u} (A.map n) :=
    Classical.choice (A.factorable n)
  let FB : FiniteValuationFactorization.{u, u, u} (B.map n) :=
    Classical.choice (B.factorable n)
  let stage : FVAIntermediateStage.{u} := {
    carrier := FA.stage.VSub × FB.stage.VSub
    partialOrder := inferInstance
    isFVA := by
      exact generatorProduct_isFVA_conditional hDomains hProductCont FA.stage FB.stage }
  exact {
    stage := stage
    factorization := scottFactorizationProd FA.factorization FB.factorization }

/-- Exact conditional product component of `thm:global-transfer`. -/
theorem global_product_conditional
    (hStages : FiniteStagesHaveFSApproximateIdentities.{u})
    (hDomains : FiniteStagesAreContinuousDcpos.{u})
    (hProductCont : AllProbabilityProductMapsAreScottContinuous.{u})
    (hD : IsFVA.{u, u} D) (hE : IsFVA.{u, u} E) :
    IsFVA.{u, u} (D × E) := by
  rcases hD.2 with ⟨A⟩
  rcases hE.2 with ⟨B⟩
  let outer := increasingApproximateIdentityProd
    A.toIncreasingApproximateIdentity B.toIncreasingApproximateIdentity
  let intermediate : FVAIntermediateApproximateIdentity.{u, u} (D × E) := {
    toIncreasingApproximateIdentity := outer
    factorable := fun n =>
      ⟨productIntermediateFactorization
        (hDomains := hDomains) (hProductCont := hProductCont) A B n⟩ }
  have hProdDomain : AbramskyJung.Chapter2.IsContinuousDcpo (D × E) :=
    ⟨⟨AbramskyJung.Chapter3.prod_isDcpo hD.1.1.1 hE.1.1.1,
        fun x y hxy hyx => Prod.ext
          (hD.1.1.2 x.1 y.1 hxy.1 hyx.1)
          (hE.1.1.2 x.2 y.2 hxy.2 hyx.2)⟩,
      AbramskyJung.Chapter3.prod_continuous_domain hD.1.hasBasis hE.1.hasBasis⟩
  exact ⟨hProdDomain,
    FVAIntermediateApproximateIdentity.flatten
      intermediate hStages hProdDomain.hasBasis⟩

end ProductTransfer

/-! ## Function-space sandwiching and transfer -/

section FunctionSpaceComposition

variable {A : Type u} {B : Type v} {C : Type w}
variable [Preorder A] [Preorder B] [Preorder C]

/-- Precomposition by a fixed Scott-continuous map. -/
def precomposeContFun (k : AbramskyJung.Chapter3.ContFun A B) :
    AbramskyJung.Chapter3.ContFun B C -> AbramskyJung.Chapter3.ContFun A C :=
  fun g => AbramskyJung.Chapter3.ContFun.comp g k

/-- Postcomposition by a fixed Scott-continuous map. -/
def postcomposeContFun (k : AbramskyJung.Chapter3.ContFun B C) :
    AbramskyJung.Chapter3.ContFun A B -> AbramskyJung.Chapter3.ContFun A C :=
  fun g => AbramskyJung.Chapter3.ContFun.comp k g

/-- Precomposition preserves directed suprema computed pointwise. -/
theorem precomposeContFun_scottContinuous
    (hC : AbramskyJung.Chapter2.IsDcpo C) (k : AbramskyJung.Chapter3.ContFun A B) :
    AbramskyJung.Chapter2.ScottContinuous (precomposeContFun (C := C) k) := by
  constructor
  · intro f g hfg x
    exact hfg (k x)
  · intro G s hG hs
    constructor
    · intro y hy
      rcases hy with ⟨g, hg, rfl⟩
      intro x
      exact hs.1 hg (k x)
    · intro q hq x
      have hEvalSup := (AbramskyJung.Chapter3.ContFun.eval_scottContinuous hC (k x)).2 hG hs
      apply hEvalSup.2 (q x)
      intro y hy
      rcases hy with ⟨g, hg, rfl⟩
      exact hq ⟨g, hg, rfl⟩ x

/-- Postcomposition preserves directed suprema when its fixed map is Scott
continuous. -/
theorem postcomposeContFun_scottContinuous
    (hB : AbramskyJung.Chapter2.IsDcpo B) (k : AbramskyJung.Chapter3.ContFun B C) :
    AbramskyJung.Chapter2.ScottContinuous (postcomposeContFun (A := A) k) := by
  constructor
  · intro f g hfg x
    exact k.continuous.monotone (hfg x)
  · intro G s hG hs
    constructor
    · intro y hy
      rcases hy with ⟨g, hg, rfl⟩
      intro x
      exact k.continuous.monotone (hs.1 hg x)
    · intro q hq x
      have hEvalSup := (AbramskyJung.Chapter3.ContFun.eval_scottContinuous hB x).2 hG hs
      have hEvalDir : AbramskyJung.Chapter2.DirectedSet
          ((fun g : AbramskyJung.Chapter3.ContFun A B => g x) '' G) :=
        AbramskyJung.Chapter2.DirectedSet.image
          (AbramskyJung.Chapter3.ContFun.eval_scottContinuous hB x).monotone hG
      have hPostSup := k.continuous.maps_isSup hEvalDir hEvalSup
      apply hPostSup.2 (q x)
      intro y hy
      rcases hy with ⟨z, hz, rfl⟩
      rcases hz with ⟨g, hg, rfl⟩
      exact hq ⟨g, hg, rfl⟩ x

end FunctionSpaceComposition

section FunctionTransfer

variable {D : Type u} {E : Type u} [PartialOrder D] [PartialOrder E]

/-- The manuscript's function-space approximant
`f |-> b o f o a`. -/
def functionSandwichMap
    (a : AbramskyJung.Chapter3.ContFun D D) (b : AbramskyJung.Chapter3.ContFun E E) :
    AbramskyJung.Chapter3.ContFun D E -> AbramskyJung.Chapter3.ContFun D E :=
  fun f => AbramskyJung.Chapter3.ContFun.comp b (AbramskyJung.Chapter3.ContFun.comp f a)

@[simp]
theorem functionSandwichMap_apply
    (a : AbramskyJung.Chapter3.ContFun D D) (b : AbramskyJung.Chapter3.ContFun E E)
    (f : AbramskyJung.Chapter3.ContFun D E) (x : D) :
    functionSandwichMap a b f x = b (f (a x)) :=
  rfl

/-- Function sandwiching is Scott-continuous in the function argument. -/
theorem functionSandwichMap_scottContinuous
    (hE : AbramskyJung.Chapter2.IsDcpo E)
    (a : AbramskyJung.Chapter3.ContFun D D) (b : AbramskyJung.Chapter3.ContFun E E) :
    AbramskyJung.Chapter2.ScottContinuous (functionSandwichMap a b) := by
  exact (postcomposeContFun_scottContinuous (A := D) hE b).comp
    (precomposeContFun_scottContinuous (C := E) hE a)

/-- The diagonal sequence of function-sandwich approximants is an increasing
approximate identity.  The cofinal-diagonal argument is proved directly. -/
noncomputable def functionSandwichApproximateIdentity
    (hE : AbramskyJung.Chapter2.IsDcpo E)
    (A : IncreasingApproximateIdentity D)
    (B : IncreasingApproximateIdentity E) :
    IncreasingApproximateIdentity (AbramskyJung.Chapter3.ContFun D E) where
  map n := {
    toFun := functionSandwichMap (asContFun (A.map n)) (asContFun (B.map n))
    continuous := functionSandwichMap_scottContinuous hE
      (asContFun (A.map n)) (asContFun (B.map n)) }
  monotone := by
    intro m n hmn f x
    calc
      B.map m (f (A.map m x)) <= B.map n (f (A.map m x)) :=
        B.monotone hmn _
      _ <= B.map n (f (A.map n x)) :=
        (B.map n).continuous.monotone
          (f.continuous.monotone (A.monotone hmn x))
  below_id := by
    intro n f x
    calc
      B.map n (f (A.map n x)) <= f (A.map n x) := B.below_id n _
      _ <= f x := f.continuous.monotone (A.below_id n x)
  pointwise_sup := by
    intro f
    constructor
    · intro g hg
      rcases hg with ⟨n, rfl⟩
      intro x
      exact le_trans (B.below_id n _) (f.continuous.monotone (A.below_id n x))
    · intro g hg
      intro x
      have hfSup := f.continuous.maps_isSup
        (A.range_directed x) (A.pointwise_sup x)
      apply hfSup.2 (g x)
      intro y hy
      rcases hy with ⟨ax, ⟨i, rfl⟩, rfl⟩
      apply (B.pointwise_sup (f (A.map i x))).2 (g x)
      intro z hz
      rcases hz with ⟨j, rfl⟩
      let n := max i j
      calc
        B.map j (f (A.map i x)) <= B.map n (f (A.map i x)) :=
          B.monotone (Nat.le_max_right i j) _
        _ <= B.map n (f (A.map n x)) :=
          (B.map n).continuous.monotone
            (f.continuous.monotone (A.monotone (Nat.le_max_left i j) x))
        _ <= g x := hg ⟨n, rfl⟩ x

/-- Finite function-generator premise supplied in the manuscript by
`cor:finite-generators`, but currently dependent on the absent continuous
valuation kernel-lifting API. -/
def FiniteFunctionGeneratorsAreFVA : Prop :=
  ∀ P Q : FinitePoset.{u},
    IsFVA.{u, u} (AbramskyJung.Chapter3.ContFun P.VSub Q.VSub)

/-- Exact function-space factorization
`S_n (R_n f) = b_n o f o a_n`. -/
noncomputable def functionSandwichScottFactorization
    {a : ScottContFun D D} {b : ScottContFun E E}
    (FA : FiniteValuationFactorization.{u, u, u} a)
    (FB : FiniteValuationFactorization.{u, u, u} b)
    (hE : AbramskyJung.Chapter2.IsDcpo E)
    (hQ : AbramskyJung.Chapter2.IsDcpo FB.stage.VSub) :
    ScottFactorization
      (functionSandwichMap
        (asContFun a) (asContFun b))
      (AbramskyJung.Chapter3.ContFun FA.stage.VSub FB.stage.VSub) := by
  let eX : AbramskyJung.Chapter3.ContFun FA.stage.VSub D :=
    ⟨FA.factorization.decode, FA.factorization.decode_continuous⟩
  let pX : AbramskyJung.Chapter3.ContFun D FA.stage.VSub :=
    ⟨FA.factorization.encode, FA.factorization.encode_continuous⟩
  let eY : AbramskyJung.Chapter3.ContFun FB.stage.VSub E :=
    ⟨FB.factorization.decode, FB.factorization.decode_continuous⟩
  let pY : AbramskyJung.Chapter3.ContFun E FB.stage.VSub :=
    ⟨FB.factorization.encode, FB.factorization.encode_continuous⟩
  let encode : AbramskyJung.Chapter3.ContFun D E -> AbramskyJung.Chapter3.ContFun FA.stage.VSub FB.stage.VSub :=
    fun f => AbramskyJung.Chapter3.ContFun.comp pY (AbramskyJung.Chapter3.ContFun.comp f eX)
  let decode : AbramskyJung.Chapter3.ContFun FA.stage.VSub FB.stage.VSub -> AbramskyJung.Chapter3.ContFun D E :=
    fun k => AbramskyJung.Chapter3.ContFun.comp eY (AbramskyJung.Chapter3.ContFun.comp k pX)
  refine {
    encode := encode
    decode := decode
    encode_continuous := ?_
    decode_continuous := ?_
    factor := ?_ }
  · exact (postcomposeContFun_scottContinuous (A := FA.stage.VSub) hE pY).comp
      (precomposeContFun_scottContinuous (C := E) hE eX)
  · exact (postcomposeContFun_scottContinuous (A := D) hQ eY).comp
      (precomposeContFun_scottContinuous (C := FB.stage.VSub) hQ pX)
  · intro f
    apply AbramskyJung.Chapter3.ContFun.ext_apply
    intro x
    change FB.factorization.decode
      (FB.factorization.encode
        (f (FA.factorization.decode (FA.factorization.encode x)))) =
      b (f (a x))
    rw [FA.factorization.factor, FB.factorization.factor]

/-- The `n`th function approximant factors through the finite function
generator selected by the two FVA factorizations. -/
noncomputable def functionIntermediateFactorization
    (hDomains : FiniteStagesAreContinuousDcpos.{u})
    (hFiniteFunctions : FiniteFunctionGeneratorsAreFVA.{u})
    (hE : AbramskyJung.Chapter2.IsDcpo E)
    (A : FVApproximateIdentity.{u, u} D)
    (B : FVApproximateIdentity.{u, u} E) (n : Nat) :
    FVAIntermediateFactorization.{u, u}
      ((functionSandwichApproximateIdentity hE
        A.toIncreasingApproximateIdentity
        B.toIncreasingApproximateIdentity).map n) := by
  let FA : FiniteValuationFactorization.{u, u, u} (A.map n) :=
    Classical.choice (A.factorable n)
  let FB : FiniteValuationFactorization.{u, u, u} (B.map n) :=
    Classical.choice (B.factorable n)
  let stage : FVAIntermediateStage.{u} := {
    carrier := AbramskyJung.Chapter3.ContFun FA.stage.VSub FB.stage.VSub
    partialOrder := inferInstance
    isFVA := hFiniteFunctions FA.stage FB.stage }
  exact {
    stage := stage
    factorization := functionSandwichScottFactorization FA FB hE
      (hDomains FB.stage).1.1 }

/-- Exact conditional function-space component of `thm:global-transfer`.
Continuity of the function-space domain and finite kernel lifting are exposed
as premises. -/
theorem global_functionSpace_conditional
    (hStages : FiniteStagesHaveFSApproximateIdentities.{u})
    (hDomains : FiniteStagesAreContinuousDcpos.{u})
    (hFiniteFunctions : FiniteFunctionGeneratorsAreFVA.{u})
    (hD : IsFVA.{u, u} D) (hE : IsFVA.{u, u} E)
    (hFunctionDomain : AbramskyJung.Chapter2.IsContinuousDcpo (AbramskyJung.Chapter3.ContFun D E)) :
    IsFVA.{u, u} (AbramskyJung.Chapter3.ContFun D E) := by
  rcases hD.2 with ⟨A⟩
  rcases hE.2 with ⟨B⟩
  let outer := functionSandwichApproximateIdentity hE.1.1.1
    A.toIncreasingApproximateIdentity B.toIncreasingApproximateIdentity
  let intermediate :
      FVAIntermediateApproximateIdentity.{u, u} (AbramskyJung.Chapter3.ContFun D E) := {
    toIncreasingApproximateIdentity := outer
    factorable := fun n =>
      ⟨functionIntermediateFactorization hDomains hFiniteFunctions hE.1.1.1 A B n⟩ }
  exact ⟨hFunctionDomain,
    FVAIntermediateApproximateIdentity.flatten
      intermediate hStages hFunctionDomain.hasBasis⟩

end FunctionTransfer

/-! ## Explicit conditional valuation and global closure composition -/

section FiniteGeneratorDependency

/-- The exact two conclusions supplied by the manuscript's kernel-lifting
theorem at one finite subprobability generator.  `V2 Q` stands for the second
continuous-valuation application, whose arbitrary-dcpo type is absent from
the current project. -/
def FiniteKernelLiftingConclusion
    (V2 : FinitePoset.{u} -> Type u)
    (v2Order : ∀ Q, PartialOrder (V2 Q)) (Q : FinitePoset.{u}) : Prop :=
  @IsFVA.{u, u} (V2 Q) (v2Order Q).toPreorder (v2Order Q) ∧
    ∀ P : FinitePoset.{u}, IsFVA.{u, u} (AbramskyJung.Chapter3.ContFun Q.VSub P.VSub)

/-- Exact conditional form of `cor:finite-generators`: it is a direct
specialization of the still-external kernel-lifting conclusion, and does not
claim that the continuous valuation functor has been constructed locally. -/
theorem cor_finite_generators_conditional
    (V2 : FinitePoset.{u} -> Type u)
    (v2Order : ∀ Q, PartialOrder (V2 Q))
    (hKernelLifting : ∀ Q : FinitePoset.{u},
      FiniteKernelLiftingConclusion V2 v2Order Q) :
    (∀ Q : FinitePoset.{u},
      @IsFVA.{u, u} (V2 Q) (v2Order Q).toPreorder (v2Order Q)) ∧
      FiniteFunctionGeneratorsAreFVA.{u} := by
  constructor
  · intro Q
    exact (hKernelLifting Q).1
  · intro P Q
    exact (hKernelLifting P).2 Q

end FiniteGeneratorDependency

section ConditionalValuationTransfer

variable {D : Type u} [PartialOrder D]

/-- Exact conditional valuation-transfer pattern.  The caller must supply
the continuous-valuation locality result as an actual increasing approximate
identity on `VD`, together with its functorial factorizations through FVA
intermediate stages. -/
theorem global_Vsub_conditional
    {VD : Type u} [PartialOrder VD]
    (hStages : FiniteStagesHaveFSApproximateIdentities.{u})
    (hVDomain : AbramskyJung.Chapter2.IsContinuousDcpo VD)
    (outer : IncreasingApproximateIdentity VD)
    (hFactor : ∀ n : Nat,
      Nonempty (FVAIntermediateFactorization.{u, u} (outer.map n))) :
    IsFVA.{u, u} VD := by
  let intermediate : FVAIntermediateApproximateIdentity.{u, u} VD := {
    toIncreasingApproximateIdentity := outer
    factorable := hFactor }
  exact ⟨hVDomain, FVAIntermediateApproximateIdentity.flatten
    intermediate hStages hVDomain.hasBasis⟩

/-- Exact conditional normalized-valuation closure: a continuous
normalization/inclusion retraction transfers FVA from subprobabilities to
probabilities. -/
theorem global_Vone_conditional
    {VD VOneD : Type u} [PartialOrder VD] [PartialOrder VOneD]
    (hVD : IsFVA.{u, u} VD)
    (normalizationRetract : AbramskyJung.Chapter3.ContinuousSectionRetractionPair VOneD VD) :
    IsFVA.{u, u} VOneD :=
  IsFVA.retract normalizationRetract hVD

end ConditionalValuationTransfer

section FiniteProbabilityGenerator

variable {Q : Type u} [Fintype Q] [PartialOrder Q]

/-- Finite normalized probabilities with a least carrier point are FVA,
conditional only on the standard continuous-domain theorem for finite
subprobability stages. -/
theorem finiteProbability_isFVA_conditional
    (hDomains : FiniteStagesAreContinuousDcpos.{u})
    (bot : Q) (hbot : ∀ x : Q, bot <= x) :
    IsFVA.{u, u} (ProbabilityVector Q) := by
  classical
  let P : FinitePoset.{u} := {
    carrier := WithoutPoint bot
    fintype := withoutPointFintype Q bot
    partialOrder := inferInstance }
  apply IsFVA.retract
    (orderIsoContinuousSectionRetractionPair
      (probabilityOrderIso bot hbot))
  exact finiteStage_isFVA_conditional hDomains P

end FiniteProbabilityGenerator

section GlobalTransferComposition

variable {D E VD : Type u}
variable [PartialOrder D] [PartialOrder E] [PartialOrder VD]

/-- The three clauses of `thm:global-transfer`, with the missing semantic
inputs displayed in the theorem signature.  Product transfer is reduced to
finite-dimensional product/marginal Scott continuity; function transfer to
finite kernel lifting and function-space domain continuity; valuation
transfer to the continuous-valuation local/functorial approximation data. -/
theorem thm_global_transfer_conditional
    (hStages : FiniteStagesHaveFSApproximateIdentities.{u})
    (hDomains : FiniteStagesAreContinuousDcpos.{u})
    (hProductCont : AllProbabilityProductMapsAreScottContinuous.{u})
    (hFiniteFunctions : FiniteFunctionGeneratorsAreFVA.{u})
    (hD : IsFVA.{u, u} D) (hE : IsFVA.{u, u} E)
    (hFunctionDomain : AbramskyJung.Chapter2.IsContinuousDcpo (AbramskyJung.Chapter3.ContFun D E))
    (hVDomain : AbramskyJung.Chapter2.IsContinuousDcpo VD)
    (valuationOuter : IncreasingApproximateIdentity VD)
    (valuationFactor : ∀ n : Nat,
      Nonempty
        (FVAIntermediateFactorization.{u, u} (valuationOuter.map n))) :
    IsFVA.{u, u} (D × E) ∧
      IsFVA.{u, u} (AbramskyJung.Chapter3.ContFun D E) ∧
      IsFVA.{u, u} VD := by
  exact ⟨global_product_conditional hStages hDomains hProductCont hD hE,
    global_functionSpace_conditional hStages hDomains hFiniteFunctions
      hD hE hFunctionDomain,
    global_Vsub_conditional hStages hVDomain valuationOuter valuationFactor⟩

/-- Objectwise, explicitly conditional form of the source's `thm:main`.
Besides the three transfer premises, the probability object is obtained from
the supplied normalization retraction.  Pointedness, countable basedness,
finite generators, and retract closure come from the already proved local
API. -/
theorem thm_main_objectwise_conditional
    {VOneD : Type u} [PartialOrder VOneD]
    (hStages : FiniteStagesHaveFSApproximateIdentities.{u})
    (hDomains : FiniteStagesAreContinuousDcpos.{u})
    (hProductCont : AllProbabilityProductMapsAreScottContinuous.{u})
    (hFiniteFunctions : FiniteFunctionGeneratorsAreFVA.{u})
    (hD : IsFVA.{u, u} D) (hE : IsFVA.{u, u} E)
    (hFunctionDomain : AbramskyJung.Chapter2.IsContinuousDcpo (AbramskyJung.Chapter3.ContFun D E))
    (hVDomain : AbramskyJung.Chapter2.IsContinuousDcpo VD)
    (valuationOuter : IncreasingApproximateIdentity VD)
    (valuationFactor : ∀ n : Nat,
      Nonempty
        (FVAIntermediateFactorization.{u, u} (valuationOuter.map n)))
    (normalizationRetract : AbramskyJung.Chapter3.ContinuousSectionRetractionPair VOneD VD) :
    AbramskyJung.Chapter3.HasLeastElement D ∧
      AbramskyJung.Chapter2.IsOmegaContinuousDcpo D ∧
      (∀ P : FinitePoset.{u}, IsFVA.{u, u} P.VSub) ∧
      IsFVA.{u, u} (D × E) ∧
      IsFVA.{u, u} (AbramskyJung.Chapter3.ContFun D E) ∧
      IsFVA.{u, u} VD ∧
      IsFVA.{u, u} VOneD := by
  have hTransfer := thm_global_transfer_conditional
    hStages hDomains hProductCont hFiniteFunctions hD hE
    hFunctionDomain hVDomain valuationOuter valuationFactor
  have hVOne : IsFVA.{u, u} VOneD :=
    global_Vone_conditional hTransfer.2.2 normalizationRetract
  exact ⟨hD.hasLeastElement,
    hD.isOmegaContinuousDcpo hStages,
    fun P => finiteStage_isFVA_conditional hDomains P,
    hTransfer.1, hTransfer.2.1, hTransfer.2.2, hVOne⟩

end GlobalTransferComposition

end FiniteValuationApproximable
