import FiniteValuationApproximable.Global
import FiniteValuationApproximable.FiniteValuation.DirectedSup
import FiniteValuationApproximable.FiniteValuation.Consequences

/-!
# Scott continuity of finite probability products and marginals

This module closes the finite-dimensional continuity premise isolated in
`Global.lean`.  It proves, without an external axiom, that ordinary products
of finite probability distributions and their two marginal maps preserve
every existing directed supremum in the stochastic order.

The key finite-dimensional input is the simultaneous upper-mass approximation
theorem from `FiniteValuation.DirectedSup`.  It yields a sequence from any
directed family with a specified supremum whose atomic coefficients converge
to those of the supremum.  Finite sums and products then commute with that
limit.

Source: Proposition `prop:generator-product` in `main (17).tex`, source
SHA-256
`4b2e65f0f96347bea4df7571e8993ad6e888c0ff7181c1305c5056880365ac94`.
-/

set_option autoImplicit false
set_option linter.unnecessarySimpa false

universe u v w

namespace FiniteValuationApproximable

open scoped BigOperators Topology
open Set Filter Topology
open SubprobabilityVector

abbrev ProductContinuityDirectedSet {D : Type u} [Preorder D] :=
  AbramskyJung.Chapter2.DirectedSet (α := D)

abbrev ProductContinuityIsSup {D : Type u} [Preorder D] :=
  AbramskyJung.Chapter2.IsSup (α := D)

/-! ## Directed limits in a normalized finite simplex -/

section ProbabilityDirectedLimits

variable {P : Type u} [Fintype P] [PartialOrder P]

/-- A supremum among normalized finite probability vectors is also a least
upper bound of the underlying subprobability vectors.  The only point to
check is that every subprobability upper bound of a nonempty normalized family
has total mass one and hence is itself normalized. -/
theorem probabilityUnderlying_isLUB
    {A : Set (ProbabilityVector P)} {p : ProbabilityVector P}
    (hA : ProductContinuityDirectedSet A)
    (hp : ProductContinuityIsSup A p) :
    IsLUB ((fun q : ProbabilityVector P => q.1) '' A) p.1 := by
  constructor
  · rintro _ ⟨q, hqA, rfl⟩
    exact hp.1 hqA
  · intro b hb
    rcases hA.1 with ⟨q, hqA⟩
    let univUpper : UpperSet P := ⟨Set.univ, isUpperSet_univ⟩
    have hqb : q.1 ≤ b := hb ⟨q, hqA, rfl⟩
    have hmass := hqb univUpper
    have hqmass : upperMass q.1 univUpper = 1 := by
      simpa [univUpper, upperMass] using
        ProbabilityVector.totalMass_eq_one q
    have hbmass : upperMass b univUpper = b.totalMass := by
      simp [univUpper, upperMass]
    rw [hqmass, hbmass] at hmass
    have hbtotal : b.totalMass = 1 :=
      le_antisymm b.totalMass_le_one hmass
    let b' : ProbabilityVector P := ⟨b, hbtotal⟩
    have hb' : ∀ q ∈ A, q ≤ b' := by
      intro r hrA
      exact hb ⟨r, hrA, rfl⟩
    change p.1 ≤ b
    exact hp.2 b' hb'

/-- Every specified directed supremum in a normalized finite stochastic
simplex admits a sequence from the directed family which converges in every
atomic coefficient. -/
theorem exists_probability_coeff_tendsto_sequence_of_isSup
    (A : Set (ProbabilityVector P)) (p : ProbabilityVector P)
    (hA : ProductContinuityDirectedSet A)
    (hp : ProductContinuityIsSup A p) :
    ∃ q : Nat → ProbabilityVector P,
      (∀ n, q n ∈ A) ∧
        ∀ x : P, Tendsto (fun n => q n x) atTop (nhds (p x)) := by
  let D : Set (SubprobabilityVector P) :=
    (fun q : ProbabilityVector P => q.1) '' A
  have hDne : D.Nonempty := by
    rcases hA.1 with ⟨q, hqA⟩
    exact ⟨q.1, ⟨q, hqA, rfl⟩⟩
  have hDdir : DirectedOn (· ≤ ·) D := by
    rintro x ⟨qx, hqxA, rfl⟩ y ⟨qy, hqyA, rfl⟩
    rcases hA.2 hqxA hqyA with ⟨q, hqA, hxq, hyq⟩
    exact ⟨q.1, ⟨q, hqA, rfl⟩, hxq, hyq⟩
  have hLUB : IsLUB D p.1 := by
    simpa only [D] using probabilityUnderlying_isLUB hA hp
  let δ : Nat → Real := fun n => 1 / ((n : Real) + 1)
  have hδ_pos (n : Nat) : 0 < δ n := by
    dsimp only [δ]
    positivity
  have hδ_tendsto : Tendsto δ atTop (nhds 0) := by
    simpa only [δ] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := Real))
  have happ (n : Nat) :
      ∃ r ∈ D, ∀ U : UpperSet P,
        upperMass p.1 U - δ n < upperMass r U :=
    Erosion.directedUpperMassApproximation D p.1 hDne hDdir hLUB
      (δ n) (hδ_pos n)
  choose r hrD hrclose using happ
  have hr_preimage (n : Nat) :
      ∃ q : ProbabilityVector P, q ∈ A ∧ q.1 = r n := by
    rcases hrD n with ⟨q, hqA, hqr⟩
    exact ⟨q, hqA, hqr⟩
  choose q hqA hqval using hr_preimage
  refine ⟨q, hqA, ?_⟩
  have hmass_tendsto (U : UpperSet P) :
      Tendsto (fun n => upperMass (q n).1 U) atTop
        (nhds (upperMass p.1 U)) := by
    have hlower :
        Tendsto (fun n => upperMass p.1 U - δ n) atTop
          (nhds (upperMass p.1 U)) := by
      simpa using tendsto_const_nhds.sub hδ_tendsto
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlower
      tendsto_const_nhds
      (fun n => by
        have hclose := hrclose n U
        rw [← hqval n] at hclose
        exact le_of_lt hclose)
      (fun n => (hp.1 (hqA n)) U)
  intro x
  have hprincipal := hmass_tendsto (principalUpperSet x)
  have hpunctured := hmass_tendsto (puncturedPrincipalUpperSet x)
  simpa only [upperMass_principal_sub_punctured] using
    hprincipal.sub hpunctured

end ProbabilityDirectedLimits

/-! ## A general separate-continuity lemma -/

/-- A binary map which is Scott-continuous in each argument is
Scott-continuous on the product.  Directedness is used to synchronize the two
members witnessing the separate directed suprema. -/
theorem scottContinuous_uncurry_of_separately
    {X : Type u} {Y : Type v} {Z : Type w}
    [Preorder X] [Preorder Y] [Preorder Z]
    (F : X → Y → Z)
    (hleft : ∀ y, AbramskyJung.Chapter2.ScottContinuous (fun x => F x y))
    (hright : ∀ x, AbramskyJung.Chapter2.ScottContinuous (fun y => F x y)) :
    AbramskyJung.Chapter2.ScottContinuous
      (fun p : X × Y => F p.1 p.2) := by
  have hmono : Monotone (fun p : X × Y => F p.1 p.2) := by
    intro a b hab
    exact ((hleft a.2).monotone hab.1).trans
      ((hright b.1).monotone hab.2)
  refine ⟨hmono, ?_⟩
  intro A s hA hs
  have hfstDir : ProductContinuityDirectedSet (Prod.fst '' A) :=
    AbramskyJung.Chapter2.DirectedSet.image
      (A := A) (f := fun p : X × Y => p.1)
      (by intro a b hab; exact hab.1) hA
  have hsndDir : ProductContinuityDirectedSet (Prod.snd '' A) :=
    AbramskyJung.Chapter2.DirectedSet.image
      (A := A) (f := fun p : X × Y => p.2)
      (by intro a b hab; exact hab.2) hA
  have hfstSup : ProductContinuityIsSup (Prod.fst '' A) s.1 :=
    AbramskyJung.Chapter3.prod_fst_isSup hs
  have hsndSup : ProductContinuityIsSup (Prod.snd '' A) s.2 :=
    AbramskyJung.Chapter3.prod_snd_isSup hs
  constructor
  · rintro _ ⟨a, haA, rfl⟩
    exact hmono (hs.1 haA)
  · intro z hz
    have hleftSup := (hleft s.2).maps_isSup hfstDir hfstSup
    refine hleftSup.2 z ?_
    rintro _ ⟨x, hx, rfl⟩
    rcases hx with ⟨a, haA, rfl⟩
    have hrightSup := (hright a.1).maps_isSup hsndDir hsndSup
    refine hrightSup.2 z ?_
    rintro _ ⟨y, hy, rfl⟩
    rcases hy with ⟨b, hbA, rfl⟩
    rcases hA.2 haA hbA with ⟨c, hcA, hac, hbc⟩
    exact ((hleft b.2).monotone hac.1).trans
      (((hright c.1).monotone hbc.2).trans
        (hz ⟨c, hcA, rfl⟩))

/-! ## Product distributions -/

section ProbabilityProducts

variable {P : Type u} {Q : Type v}
variable [Fintype P] [Fintype Q] [PartialOrder P] [PartialOrder Q]

/-- With the right factor fixed, finite probability product preserves every
existing directed supremum. -/
theorem probabilityProduct_left_scottContinuous
    (nu : ProbabilityVector Q) :
    AbramskyJung.Chapter2.ScottContinuous
      (fun mu : ProbabilityVector P => probabilityProduct mu nu) := by
  constructor
  · intro mu mu' hmu
    exact probabilityProduct_mono hmu le_rfl
  · intro A mu hA hmu
    rcases exists_probability_coeff_tendsto_sequence_of_isSup A mu hA hmu with
      ⟨q, hqA, hqcoeff⟩
    constructor
    · rintro _ ⟨r, hrA, rfl⟩
      exact probabilityProduct_mono (hmu.1 hrA) le_rfl
    · intro b hb U
      have hmass :
          Tendsto
            (fun n => upperMass (probabilityProduct (q n) nu).1 U)
            atTop (nhds (upperMass (probabilityProduct mu nu).1 U)) := by
        unfold upperMass SubprobabilityVector.mass
        apply tendsto_finset_sum Finset.univ
        intro z hz
        by_cases hzU : z ∈ (U : Set (P × Q))
        · simpa [hzU, probabilityProduct_apply] using
            (hqcoeff z.1).mul_const (nu z.2)
        · simp [hzU]
      exact le_of_tendsto' hmass (fun n =>
        (hb ⟨q n, hqA n, rfl⟩) U)

/-- With the left factor fixed, finite probability product preserves every
existing directed supremum. -/
theorem probabilityProduct_right_scottContinuous
    (mu : ProbabilityVector P) :
    AbramskyJung.Chapter2.ScottContinuous
      (fun nu : ProbabilityVector Q => probabilityProduct mu nu) := by
  constructor
  · intro nu nu' hnu
    exact probabilityProduct_mono le_rfl hnu
  · intro A nu hA hnu
    rcases exists_probability_coeff_tendsto_sequence_of_isSup A nu hA hnu with
      ⟨q, hqA, hqcoeff⟩
    constructor
    · rintro _ ⟨r, hrA, rfl⟩
      exact probabilityProduct_mono le_rfl (hnu.1 hrA)
    · intro b hb U
      have hmass :
          Tendsto
            (fun n => upperMass (probabilityProduct mu (q n)).1 U)
            atTop (nhds (upperMass (probabilityProduct mu nu).1 U)) := by
        unfold upperMass SubprobabilityVector.mass
        apply tendsto_finset_sum Finset.univ
        intro z hz
        by_cases hzU : z ∈ (U : Set (P × Q))
        · simpa [hzU, probabilityProduct_apply] using
            tendsto_const_nhds.mul (hqcoeff z.2)
        · simp [hzU]
      exact le_of_tendsto' hmass (fun n =>
        (hb ⟨q n, hqA n, rfl⟩) U)

/-- Ordinary finite probability product is jointly Scott-continuous. -/
theorem probabilityProduct_scottContinuous :
    AbramskyJung.Chapter2.ScottContinuous
      (fun p : ProbabilityVector P × ProbabilityVector Q =>
        probabilityProduct p.1 p.2) := by
  exact scottContinuous_uncurry_of_separately probabilityProduct
    probabilityProduct_left_scottContinuous
    probabilityProduct_right_scottContinuous

end ProbabilityProducts

/-! ## Pushforwards and marginals -/

section ProbabilityPushforwards

variable {X : Type u} {Y : Type v}
variable [Fintype X] [Fintype Y] [PartialOrder X] [PartialOrder Y]

/-- Pushforward along a monotone map of finite posets preserves every
existing directed supremum of normalized probabilities. -/
theorem probabilityPushforward_scottContinuous
    (f : X → Y) (hf : Monotone f) :
    AbramskyJung.Chapter2.ScottContinuous
      (fun mu : ProbabilityVector X => probabilityPushforward mu f) := by
  constructor
  · intro mu nu hmunu
    exact probabilityPushforward_mono hmunu hf
  · intro A mu hA hmu
    rcases exists_probability_coeff_tendsto_sequence_of_isSup A mu hA hmu with
      ⟨q, hqA, hqcoeff⟩
    constructor
    · rintro _ ⟨r, hrA, rfl⟩
      exact probabilityPushforward_mono (hmu.1 hrA) hf
    · intro b hb U
      have houtcoeff (y : Y) :
          Tendsto (fun n => probabilityPushforward (q n) f y) atTop
            (nhds (probabilityPushforward mu f y)) := by
        simp only [probabilityPushforward_apply]
        apply tendsto_finset_sum Finset.univ
        intro x hx
        exact (hqcoeff x).mul_const (dirac (f x) y)
      have hmass :
          Tendsto
            (fun n => upperMass (probabilityPushforward (q n) f).1 U)
            atTop (nhds (upperMass (probabilityPushforward mu f).1 U)) := by
        unfold upperMass SubprobabilityVector.mass
        apply tendsto_finset_sum Finset.univ
        intro y hy
        by_cases hyU : y ∈ (U : Set Y)
        · simpa [hyU] using houtcoeff y
        · simp [hyU]
      exact le_of_tendsto' hmass (fun n =>
        (hb ⟨q n, hqA n, rfl⟩) U)

end ProbabilityPushforwards

section ProbabilityMarginals

variable {P : Type u} {Q : Type v}
variable [Fintype P] [Fintype Q] [PartialOrder P] [PartialOrder Q]

/-- The pair of finite probability marginals is Scott-continuous. -/
theorem probabilityMarginals_scottContinuous :
    AbramskyJung.Chapter2.ScottContinuous
      (probabilityMarginals :
        ProbabilityVector (P × Q) →
          ProbabilityVector P × ProbabilityVector Q) := by
  simpa only [probabilityMarginals] using
    AbramskyJung.Chapter3.prod_pair_scottContinuous
      (probabilityPushforward_scottContinuous Prod.fst
        (fun (a b : P × Q) (h : a ≤ b) => h.1))
      (probabilityPushforward_scottContinuous Prod.snd
        (fun (a b : P × Q) (h : a ≤ b) => h.2))

/-- The product-distribution/marginal section--retraction pair from
`Global.lean` is genuinely Scott-continuous. -/
theorem probabilityProductMapsAreScottContinuous :
    ProbabilityProductMapsAreScottContinuous (P := P) (Q := Q) :=
  ⟨probabilityProduct_scottContinuous,
    probabilityMarginals_scottContinuous⟩

end ProbabilityMarginals

/-- Uniform unconditional discharge of the finite-dimensional continuity
premise used by source Proposition `prop:generator-product`. -/
theorem allProbabilityProductMapsAreScottContinuous :
    AllProbabilityProductMapsAreScottContinuous.{u} := by
  intro P Q
  exact probabilityProductMapsAreScottContinuous
    (P := WithBot P) (Q := WithBot Q)

/-! ## Premise-free source-facing product theorems -/

/-- Unconditional finite generator-product theorem: the finite-stage domain
premise and the product/marginal continuity premise are both proved in the
standalone development. -/
theorem generatorProduct_isFVA (P Q : FinitePoset.{u}) :
    IsFVA.{u, u} (P.VSub × Q.VSub) :=
  generatorProduct_isFVA_conditional
    finiteStagesAreContinuousDcpos
    allProbabilityProductMapsAreScottContinuous P Q

section GlobalProduct

variable {D : Type u} {E : Type u} [PartialOrder D] [PartialOrder E]

/-- Unconditional product component of source theorem `thm:global-transfer`.
All three semantic premises of `global_product_conditional` are discharged by
the finite-stage erosion construction and the continuity results above. -/
theorem global_product
    (hD : IsFVA.{u, u} D) (hE : IsFVA.{u, u} E) :
    IsFVA.{u, u} (D × E) :=
  global_product_conditional
    finiteStagesHaveFSApproximateIdentities
    finiteStagesAreContinuousDcpos
    allProbabilityProductMapsAreScottContinuous hD hE

end GlobalProduct

end FiniteValuationApproximable
