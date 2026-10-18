import ChainApproximation.AlgebraSharp

/-!
# Naming one element of a Jónsson algebra

This module formalizes the elementary named-constant expansion used immediately
before source `thm:sharp`. A separate direct Lean construction supplies the
locally finite Jónsson algebra of cardinality `aleph1` used there.
-/

set_option autoImplicit false

universe u

namespace ChainApproximation
namespace Algebra

open Set Cardinal FirstOrder
open FirstOrder.Language

variable {L : FirstOrder.Language.{u, u}} {M : Type u}

/-- The new constant symbol whose interpretation is the chosen element `a`. -/
def namedConstant (a : M) : L[[({a} : Set M)]].Constants :=
  Sum.inr ⟨a, Set.mem_singleton a⟩

/-- Substructures after naming `a` are exactly the original substructures that
contain `a`, with the same inclusion order. -/
def substructureWithNamedConstantOrderIso [L.Structure M] (a : M) :
    L[[({a} : Set M)]].Substructure M ≃o
      {S : L.Substructure M // a ∈ S} where
  toFun S :=
    ⟨(L.lhomWithConstants ({a} : Set M)).substructureReduct S, by
      change a ∈ S
      exact S.constants_mem (namedConstant a)⟩
  invFun S := S.1.withConstants (by
    intro x hx
    simpa only [Set.mem_singleton_iff.mp hx] using S.2)
  left_inv S := by ext x; rfl
  right_inv S := by apply Subtype.ext; ext x; rfl
  map_rel_iff' := Iff.rfl

/-- Naming one element preserves local finiteness.  The closure in the
expanded language is the old closure of the generators together with `a`. -/
theorem locallyFinite_withNamedConstant [L.Structure M]
    (hLF : LocallyFinite L M) (a : M) :
    @LocallyFinite L[[({a} : Set M)]] M
      (L.withConstantsStructure ({a} : Set M)) := by
  letI : L[[({a} : Set M)]].Structure M :=
    L.withConstantsStructure ({a} : Set M)
  intro F
  rw [Substructure.closure_withConstants_eq]
  change (Substructure.closure L (({a} : Set M) ∪ (F : Set M)) : Set M).Finite
  have hAF : (({a} : Set M) ∪ (F : Set M)).Finite :=
    Set.finite_singleton a |>.union F.finite_toSet
  simpa only [Set.Finite.coe_toFinset] using hLF hAF.toFinset

/-- Adding one constant to a countable finitary signature preserves
countability of the total family of function symbols. -/
theorem countable_signature_withNamedConstant
    (h : Countable (Σ n, L.Functions n)) (a : M) :
    Countable (Σ n, (L[[({a} : Set M)]]).Functions n) := by
  let A : Set M := {a}
  letI : Countable (Σ n, L.Functions n) := h
  letI (n : ℕ) : Countable (L.Functions n) :=
    (sigma_mk_injective (i := n)).countable
  letI : Countable A := (Set.countable_singleton a).to_subtype
  letI (n : ℕ) : Countable ((constantsOn A).Functions n) := by
    change Countable (constantsOnFunc A n)
    cases n <;> simp only [constantsOnFunc] <;> infer_instance
  letI (n : ℕ) : Countable ((L[[A]]).Functions n) := by
    change Countable (L.Functions n ⊕ (constantsOn A).Functions n)
    infer_instance
  change Countable (Σ n, (L[[A]]).Functions n)
  exact inferInstance

/-- Naming one element preserves the Jónsson property.  A substructure of
the expansion has the same carrier as its reduct to the original language. -/
theorem jonsson_withNamedConstant [L.Structure M]
    (hJ : Jonsson L M) (a : M) :
    @Jonsson L[[({a} : Set M)]] M
      (L.withConstantsStructure ({a} : Set M)) := by
  let A : Set M := {a}
  letI : L[[A]].Structure M := L.withConstantsStructure A
  refine ⟨hJ.1, countable_signature_withNamedConstant hJ.2.1 a, ?_⟩
  intro S hcard
  let R : L.Substructure M := (L.lhomWithConstants A).substructureReduct S
  have hRS : Cardinal.mk R = Cardinal.mk S := by
    apply Cardinal.mk_congr
    exact Equiv.setCongr (by ext x; simp [R])
  have hRtop : R = ⊤ := hJ.2.2 R (hRS.trans hcard)
  ext x
  constructor
  · exact fun _ ↦ trivial
  · intro _
    have hxR : x ∈ R := by rw [hRtop]; trivial
    exact hxR

end Algebra
end ChainApproximation
