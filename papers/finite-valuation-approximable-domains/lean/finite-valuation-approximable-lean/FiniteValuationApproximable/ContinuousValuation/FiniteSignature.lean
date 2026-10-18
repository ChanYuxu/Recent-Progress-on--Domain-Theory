import FiniteValuationApproximable.ContinuousValuation.Finite
import Mathlib.Data.Fintype.Pi

/-!
# Finite Boolean signatures of Scott opens

For a finite family of Scott opens, membership gives a Scott-continuous map
into the finite Boolean cube.  Pushing a continuous valuation along this map
and using the already proved finite-poset atomic representation produces the
finite Boolean dissection used in Jones's simple-function arguments.

The important support theorem below is not assumed: an unrealised Boolean
cell has zero reconstructed atomic coefficient.  It follows by comparing the
preimages of the principal and punctured-principal opens of that cell.
-/

set_option autoImplicit false
set_option linter.unnecessarySimpa false

universe u v

namespace FiniteValuationApproximable
namespace ContinuousValuation

open Set
open AbramskyJung.Chapter2
open scoped ENNReal BigOperators

/-- The finite Boolean cube recording membership in a family indexed by
`ι`.  Its order is coordinatewise `false ≤ true`. -/
abbrev MembershipPattern (ι : Type v) := ι → Bool

/-- Membership in a finite family of Scott opens. -/
noncomputable def membershipSignature
    {D : Type u} [Preorder D] {ι : Type v}
    (O : ι → ScottOpen D) (x : D) : MembershipPattern ι := by
  classical
  exact fun i => decide (x ∈ O i)

@[simp] theorem membershipSignature_apply_eq_true
    {D : Type u} [Preorder D] {ι : Type v}
    (O : ι → ScottOpen D) (x : D) (i : ι) :
    membershipSignature O x i = true ↔ x ∈ O i := by
  classical
  simp [membershipSignature]

@[simp] theorem membershipSignature_apply_eq_false
    {D : Type u} [Preorder D] {ι : Type v}
    (O : ι → ScottOpen D) (x : D) (i : ι) :
    membershipSignature O x i = false ↔ x ∉ O i := by
  classical
  simp [membershipSignature]

/-- Membership signatures are monotone. -/
theorem membershipSignature_mono
    {D : Type u} [Preorder D] {ι : Type v}
    (O : ι → ScottOpen D) : Monotone (membershipSignature O) := by
  classical
  intro x y hxy
  rw [Pi.le_def]
  intro i
  by_cases hx : x ∈ O i
  · have hy : y ∈ O i := (O i).upper hxy hx
    simp [membershipSignature, hx, hy]
  · simp [membershipSignature, hx, Bool.false_le]

/-- Finite Scott-open membership signatures preserve every directed
supremum. -/
theorem membershipSignature_scottContinuous
    {D : Type u} [Preorder D] {ι : Type v}
    (O : ι → ScottOpen D) :
    AbramskyJung.Chapter2.ScottContinuous (membershipSignature O) := by
  classical
  constructor
  · exact membershipSignature_mono O
  · intro A s hA hs
    constructor
    · rintro _ ⟨x, hxA, rfl⟩
      exact membershipSignature_mono O (hs.1 hxA)
    · intro q hq
      rw [Pi.le_def]
      intro i
      by_cases hsi : s ∈ O i
      · rcases (O i).inaccessible hA hs hsi with ⟨x, hxA, hxi⟩
        have hxq : membershipSignature O x ≤ q :=
          hq ⟨x, hxA, rfl⟩
        have htrue : true ≤ q i := by
          simpa [membershipSignature, hxi] using hxq i
        have hqi : q i = true := Bool.eq_true_of_true_le htrue
        simp [membershipSignature, hsi, hqi]
      · simp [membershipSignature, hsi, Bool.false_le]

/-- Bundled signature map. -/
noncomputable def membershipSignatureMap
    {D : Type u} [Preorder D] {ι : Type v}
    (O : ι → ScottOpen D) : ScottContFun D (MembershipPattern ι) where
  toFun := membershipSignature O
  continuous := membershipSignature_scottContinuous O

/-- The coordinate upper set `{p | p i = true}` of the Boolean cube. -/
def coordinateUpperSet {ι : Type v} (i : ι) :
    UpperSet (MembershipPattern ι) where
  carrier := {p | p i = true}
  upper' := by
    intro p q hpq hp
    exact Bool.eq_true_of_true_le (hp ▸ hpq i)

/-- The coordinate upper set as a Scott open of the finite cube. -/
def coordinateScottOpen {ι : Type v} [Fintype ι] [DecidableEq ι]
    (i : ι) :
    ScottOpen (MembershipPattern ι) :=
  upperSetToScottOpen (coordinateUpperSet i)

@[simp] theorem mem_coordinateScottOpen_iff
    {ι : Type v} [Fintype ι] [DecidableEq ι]
    (p : MembershipPattern ι) (i : ι) :
    p ∈ coordinateScottOpen i ↔ p i = true :=
  by
    change p i = true ↔ p i = true
    rfl

/-- Pulling a coordinate open back along the signature recovers the original
Scott open. -/
theorem coordinateScottOpen_preimage
    {D : Type u} [Preorder D] {ι : Type v}
    [Fintype ι] [DecidableEq ι]
    (O : ι → ScottOpen D) (i : ι) :
    ScottOpen.preimage (membershipSignatureMap O)
        (membershipSignatureMap O).continuous (coordinateScottOpen i) =
      O i := by
  classical
  apply ScottOpen.ext
  ext x
  change membershipSignature O x i = true ↔ x ∈ O i
  exact membershipSignature_apply_eq_true O x i

/-- Push a valuation to the finite Boolean signature cube. -/
noncomputable def signaturePushforward
    {D : Type u} [Preorder D] {ι : Type v}
    (mu : VSub D) (O : ι → ScottOpen D) :
    VSub (MembershipPattern ι) :=
  pushforward (membershipSignatureMap O) mu

/-- The atomic finite vector of the signature pushforward. -/
noncomputable def signatureVector
    {D : Type u} [Preorder D] {ι : Type v}
    [Fintype ι] [DecidableEq ι]
    (mu : VSub D) (O : ι → ScottOpen D) :
    SubprobabilityVector (MembershipPattern ι) :=
  valuationToVector (signaturePushforward mu O)

/-- A Boolean cell with positive reconstructed mass is actually realised by
a point of the source. -/
theorem exists_of_signatureVector_pos
    {D : Type u} [Preorder D] {ι : Type v}
    [Fintype ι] [DecidableEq ι]
    (mu : VSub D) (O : ι → ScottOpen D)
    (p : MembershipPattern ι)
    (hp : 0 < signatureVector mu O p) :
    ∃ x : D, membershipSignature O x = p := by
  classical
  by_contra hnone
  push_neg at hnone
  let principal : ScottOpen (MembershipPattern ι) := principalScottOpen p
  let punctured : ScottOpen (MembershipPattern ι) :=
    puncturedPrincipalScottOpen p
  have hpre :
      ScottOpen.preimage (membershipSignatureMap O)
          (membershipSignatureMap O).continuous principal =
        ScottOpen.preimage (membershipSignatureMap O)
          (membershipSignatureMap O).continuous punctured := by
    apply ScottOpen.ext
    ext x
    change (p ≤ membershipSignature O x) ↔
      (p ≤ membershipSignature O x ∧ membershipSignature O x ≠ p)
    exact (and_iff_left (hnone x)).symm
  have hvalue :
      signaturePushforward mu O principal =
        signaturePushforward mu O punctured := by
    change mu (ScottOpen.preimage (membershipSignatureMap O)
        (membershipSignatureMap O).continuous principal) =
      mu (ScottOpen.preimage (membershipSignatureMap O)
        (membershipSignatureMap O).continuous punctured)
    rw [hpre]
  have hatom : valuationAtom (signaturePushforward mu O) p = 0 := by
    change signaturePushforward mu O principal -
      signaturePushforward mu O punctured = 0
    rw [hvalue]
    exact tsub_self _
  have hcoeff : signatureVector mu O p = 0 := by
    rw [show signatureVector mu O p =
        (valuationAtom (signaturePushforward mu O) p).toReal by rfl,
      hatom]
    simp
  exact (ne_of_gt hp) hcoeff

/-- The real mass of any upper set in the signature vector is the value of
the source valuation on its signature preimage. -/
theorem signatureVector_upperMass_real
    {D : Type u} [Preorder D] {ι : Type v}
    [Fintype ι] [DecidableEq ι]
    (mu : VSub D) (O : ι → ScottOpen D)
    (U : UpperSet (MembershipPattern ι)) :
    (signatureVector mu O).mass (U : Set (MembershipPattern ι)) =
      (mu (ScottOpen.preimage (membershipSignatureMap O)
        (membershipSignatureMap O).continuous
        (upperSetToScottOpen U))).toReal := by
  have hrepr :=
    vectorToVSub_valuationToVector (signaturePushforward mu O)
  change vectorToVSub (signatureVector mu O) =
    signaturePushforward mu O at hrepr
  have hvalue := congrArg
    (fun rho : VSub (MembershipPattern ι) => rho (upperSetToScottOpen U))
    hrepr
  have hENN :
      ENNReal.ofReal
          ((signatureVector mu O).mass (U : Set (MembershipPattern ι))) =
        mu (ScottOpen.preimage (membershipSignatureMap O)
          (membershipSignatureMap O).continuous
          (upperSetToScottOpen U)) := by
    calc
      ENNReal.ofReal
          ((signatureVector mu O).mass (U : Set (MembershipPattern ι))) =
          vectorToVSub (signatureVector mu O) (upperSetToScottOpen U) :=
        rfl
      _ = signaturePushforward mu O (upperSetToScottOpen U) := hvalue
      _ = mu (ScottOpen.preimage (membershipSignatureMap O)
          (membershipSignatureMap O).continuous
          (upperSetToScottOpen U)) := rfl
  have hreal := congrArg ENNReal.toReal hENN
  simpa [ENNReal.toReal_ofReal
      ((signatureVector mu O).mass_nonneg (U : Set (MembershipPattern ι)))]
    using hreal

/-- In particular, a coordinate mass of the signature vector is exactly the
original valuation of that Scott open. -/
theorem signatureVector_coordinateMass_real
    {D : Type u} [Preorder D] {ι : Type v}
    [Fintype ι] [DecidableEq ι]
    (mu : VSub D) (O : ι → ScottOpen D) (i : ι) :
    (signatureVector mu O).mass
        (coordinateUpperSet i : Set (MembershipPattern ι)) =
      (mu (O i)).toReal := by
  rw [signatureVector_upperMass_real mu O (coordinateUpperSet i),
    show upperSetToScottOpen (coordinateUpperSet i) =
      coordinateScottOpen i by rfl,
    coordinateScottOpen_preimage]

end ContinuousValuation
end FiniteValuationApproximable
