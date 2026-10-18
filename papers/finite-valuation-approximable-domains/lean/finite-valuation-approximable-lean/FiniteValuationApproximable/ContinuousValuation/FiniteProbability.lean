import FiniteValuationApproximable.ContinuousValuation.Finite

/-!
# Probability valuations on a finite poset

Randomized rounding is first constructed as an atomic `ProbabilityVector`.
Kernel lifting, however, consumes the genuine Jones--Plotkin type `VOne`.
This module proves that the two representations are order isomorphic on a
finite poset; no definitional identification is used.
-/

set_option autoImplicit false
set_option linter.unnecessarySimpa false

universe u

namespace FiniteValuationApproximable
namespace ContinuousValuation

open scoped BigOperators ENNReal
open SubprobabilityVector

variable {P : Type u} [Fintype P] [PartialOrder P]

/-- An atomic finite probability vector defines a genuine normalized
continuous valuation. -/
noncomputable def probabilityVectorToVOne
    (p : ProbabilityVector P) : VOne P := by
  refine ⟨(vectorToVSub p.1).1, ?_⟩
  change ENNReal.ofReal (p.1.mass Set.univ) = 1
  rw [p.1.mass_univ, p.2]
  simp

@[simp]
theorem probabilityVectorToVOne_toVSub
    (p : ProbabilityVector P) :
    VOne.toVSub (probabilityVectorToVOne p) = vectorToVSub p.1 :=
  rfl

/-- Recover the finite atomic probability vector from a genuine normalized
continuous valuation. -/
noncomputable def vOneToProbabilityVector
    (mu : VOne P) : ProbabilityVector P := by
  refine ⟨valuationToVector (VOne.toVSub mu), ?_⟩
  have hrepr : (VOne.toVSub mu) (ScottOpen.univ : ScottOpen P) =
      ∑ x : P, valuationAtom (VOne.toVSub mu) x := by
    simpa [finiteAtomicMass] using valuation_eq_finiteAtomicMass
      (VOne.toVSub mu) (ScottOpen.univ : ScottOpen P)
  have hsum :
      (∑ x : P, (valuationAtom (VOne.toVSub mu) x).toReal) =
        ((VOne.toVSub mu) (ScottOpen.univ : ScottOpen P)).toReal := by
    rw [← ENNReal.toReal_sum]
    · exact congrArg ENNReal.toReal hrepr.symm
    · intro x hx
      exact valuationAtom_ne_top (VOne.toVSub mu) x
  change (∑ x : P, (valuationAtom (VOne.toVSub mu) x).toReal) = 1
  rw [hsum]
  change (mu (ScottOpen.univ : ScottOpen P)).toReal = 1
  rw [mu.2]
  simp

@[simp]
theorem vOneToProbabilityVector_coe
    (mu : VOne P) :
    (vOneToProbabilityVector mu).1 =
      valuationToVector (VOne.toVSub mu) :=
  rfl

/-- Exact order isomorphism between finite atomic probability vectors and
genuine continuous probability valuations. -/
noncomputable def finiteVOneOrderIso :
    ProbabilityVector P ≃o VOne P where
  toFun := probabilityVectorToVOne
  invFun := vOneToProbabilityVector
  left_inv := by
    intro p
    apply ProbabilityVector.ext
    intro x
    change valuationToVector (vectorToVSub p.1) x = p.1 x
    rw [valuationToVector_vectorToVSub]
  right_inv := by
    intro mu
    apply VOne.toVSub_injective
    change vectorToVSub
      (valuationToVector (VOne.toVSub mu)) = VOne.toVSub mu
    exact vectorToVSub_valuationToVector (VOne.toVSub mu)
  map_rel_iff' := by
    intro p q
    change vectorToVSub p.1 <= vectorToVSub q.1 ↔ p.1 <= q.1
    exact (finiteVSubOrderIso (P := P)).le_iff_le

/-! ## Kernels and finite-support sandwiches -/

section Kernels

variable {X : Type u} [Preorder X]

/-- Scott continuity of a normalized finite kernel can be checked after
forgetting normalization to the atomic subprobability simplex. -/
theorem probabilityKernel_scottContinuous_of_coe
    (p : X → ProbabilityVector P)
    (hp : AbramskyJung.Chapter2.ScottContinuous (fun x => (p x).1)) :
    AbramskyJung.Chapter2.ScottContinuous p := by
  constructor
  · intro x y hxy
    exact hp.monotone hxy
  · intro A s hA hs
    have hcoe := hp.maps_isSup hA hs
    constructor
    · rintro _ ⟨x, hx, rfl⟩
      exact hcoe.1 ⟨x, hx, rfl⟩
    · intro q hq
      exact hcoe.2 q.1 (by
        rintro _ ⟨x, hx, rfl⟩
        exact hq ⟨x, hx, rfl⟩)

/-- Bundle an atomic finite probability kernel as a genuine normalized
continuous-valuation kernel. -/
noncomputable def probabilityKernelToFiniteVOne
    (p : X → ProbabilityVector P)
    (hp : AbramskyJung.Chapter2.ScottContinuous (fun x => (p x).1)) :
    AbramskyJung.Chapter2.ScottContFun X (VOne P) where
  toFun x := finiteVOneOrderIso (p x)
  continuous :=
    (orderIso_scottContinuous finiteVOneOrderIso).comp
      (probabilityKernel_scottContinuous_of_coe p hp)

@[simp]
theorem probabilityKernelToFiniteVOne_apply
    (p : X → ProbabilityVector P)
    (hp : AbramskyJung.Chapter2.ScottContinuous (fun x => (p x).1))
    (x : X) :
    probabilityKernelToFiniteVOne p hp x = probabilityVectorToVOne (p x) :=
  rfl

/-- A finite normalized law whose positive-support labels lie in an order
interval pushes forward to a genuine valuation between the corresponding
Dirac valuations.  The target need not be finite. -/
theorem pushforward_probabilityVector_sandwich
    (p : ProbabilityVector P)
    (y : AbramskyJung.Chapter2.ScottContFun P X) {a b : X}
    (ha : ∀ l, 0 < p l → a ≤ y l)
    (hb : ∀ l, 0 < p l → y l ≤ b) :
    dirac a ≤ pushforward y (VOne.toVSub (probabilityVectorToVOne p)) ∧
      pushforward y (VOne.toVSub (probabilityVectorToVOne p)) ≤ dirac b := by
  classical
  let pre (U : ScottOpen X) : Set P :=
    ScottOpen.preimage y y.continuous U
  have hmass_one (U : ScottOpen X) (haU : a ∈ U) :
      p.1.mass (pre U) = 1 := by
    calc
      p.1.mass (pre U) = p.1.totalMass := by
        unfold SubprobabilityVector.mass SubprobabilityVector.totalMass
        apply Finset.sum_congr rfl
        intro l hl
        by_cases hlpre : l ∈ pre U
        · simp [hlpre]
        · have hyl : y l ∉ U := by simpa [pre] using hlpre
          have hnpos : ¬ 0 < p l := by
            intro hpos
            exact hyl (U.upper (ha l hpos) haU)
          have hzero : p l = 0 :=
            le_antisymm (not_lt.mp hnpos) (p.1.coeff_nonneg l)
          simp [hlpre, hzero]
      _ = 1 := p.2
  have hmass_zero (U : ScottOpen X) (hbU : b ∉ U) :
      p.1.mass (pre U) = 0 := by
    unfold SubprobabilityVector.mass
    apply Finset.sum_eq_zero
    intro l hl
    by_cases hlpre : l ∈ pre U
    · have hyl : y l ∈ U := by simpa [pre] using hlpre
      have hnpos : ¬ 0 < p l := by
        intro hpos
        exact hbU (U.upper (hb l hpos) hyl)
      have hzero : p l = 0 :=
        le_antisymm (not_lt.mp hnpos) (p.1.coeff_nonneg l)
      simp [hlpre, hzero]
    · simp [hlpre]
  constructor
  · intro U
    by_cases haU : a ∈ U
    · change openIndicator U a ≤ ENNReal.ofReal (p.1.mass (pre U))
      rw [hmass_one U haU]
      simp [openIndicator, haU]
    · simp [dirac_apply, openIndicator, haU]
  · intro U
    by_cases hbU : b ∈ U
    · simpa [dirac_apply, openIndicator, hbU] using
        (pushforward y
          (VOne.toVSub (probabilityVectorToVOne p))).value_le_one U
    · change ENNReal.ofReal (p.1.mass (pre U)) ≤ openIndicator U b
      rw [hmass_zero U hbU]
      simp [openIndicator, hbU]

end Kernels

end ContinuousValuation
end FiniteValuationApproximable
