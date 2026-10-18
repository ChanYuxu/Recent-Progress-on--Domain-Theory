import ChainApproximation.JonssonLF
import ChainApproximation.AlgebraExpansion

/-!
# Unconditional sharpness instance

The manuscript's source theorem is conditional on a locally finite Jónsson
algebra. This module constructs the named-constant algebra and applies that
theorem to a directly proved ZFC existence witness.
-/

set_option autoImplicit false

universe u

namespace ChainApproximation
namespace SourceFacingSharp

open Set Cardinal FirstOrder
open FirstOrder.Language

/-- The expansion of an explicitly given algebra structure by a constant
naming `a`; this keeps the witness structure visible in the statement. -/
@[reducible] def namedExpansionStructure (L : FirstOrder.Language.{u, u}) (M : Type u)
    (str : L.Structure M) (a : M) :
    (L[[({a} : Set M)]]).Structure M := by
  letI : L.Structure M := str
  exact L.withConstantsStructure ({a} : Set M)

/-- The new symbol is interpreted as the element it names. -/
def NamedConstantMeans (L : FirstOrder.Language.{u, u}) (M : Type u)
    (str : L.Structure M) (a : M)
    (c : (L[[({a} : Set M)]]).Constants) : Prop := by
  letI : (L[[({a} : Set M)]]).Structure M :=
    namedExpansionStructure L M str a
  exact (c : M) = a

/-- The full lattice conclusion of source `thm:sharp`, including the strictness
and failure of strong chain continuity stated in prose. -/
def SharpConclusion (L : FirstOrder.Language.{u, u}) (M : Type u)
    [L.Structure M] : Prop :=
  IsDcpo (L.Substructure M) ∧
  IsChainContinuous (L.Substructure M) ∧
  IsAlgebraic (L.Substructure M) ∧
  (∀ S B : L.Substructure M, B ≠ ⊤ →
    (ChainBelow S B ↔ S ≤ B ∧ (S : Set M).Finite)) ∧
  (∀ S : L.Substructure M, ChainBelow S ⊤ ↔ S ≠ ⊤) ∧
  (∀ S B : L.Substructure M,
    WayBelow S B ↔ S ≤ B ∧ (S : Set M).Finite) ∧
  (∀ S B : L.Substructure M, WayBelow S B ↔ Square S B) ∧
  (∀ S B : L.Substructure M, WayBelow S B → ChainBelow S B) ∧
  (∃ S B : L.Substructure M, ChainBelow S B ∧ ¬ WayBelow S B) ∧
  ¬ Interpolates (ChainBelow (P := L.Substructure M)) ∧
  ¬ IsStrongChainContinuous (L.Substructure M)

private theorem sharpConclusion_of_sharp {L : FirstOrder.Language.{u, u}} {M : Type u}
    [L.Structure M] (hLF : Algebra.LocallyFinite L M)
    (hJ : Algebra.Jonsson L M) (hcard : Cardinal.mk M = Cardinal.aleph 1)
    (c : L.Constants) : SharpConclusion L M := by
  obtain ⟨hdcpo, hchain, hproper, htop, hway, hsquare,
    hsub, hstrict, hninterp⟩ := Algebra.sharp hLF hJ hcard c
  exact ⟨hdcpo, hchain, Algebra.algebraic hLF, hproper, htop,
    hway, hsquare, hsub, hstrict, hninterp, fun hstrong => hninterp hstrong.2⟩

/-- Unconditional source-facing sharpness instance. The algebra comes from the
internal ZFC construction, and its language is extended by a constant naming `a`. -/
theorem exists_named_sharp :
    ∃ (L : FirstOrder.Language.{0, 0}) (M : Type)
      (str : L.Structure M) (a : M)
      (c : (L[[({a} : Set M)]]).Constants),
      c = Algebra.namedConstant a ∧
      NamedConstantMeans L M str a c ∧
      Cardinal.mk M = Cardinal.aleph 1 ∧
      @Algebra.LocallyFinite L[[({a} : Set M)]] M
        (namedExpansionStructure L M str a) ∧
      @Algebra.Jonsson L[[({a} : Set M)]] M
        (namedExpansionStructure L M str a) ∧
      @SharpConclusion L[[({a} : Set M)]] M
        (namedExpansionStructure L M str a) := by
  obtain ⟨L, M, str, hcard, hLF, hJ⟩ := JonssonLF.exists_locallyFinite_jonsson_aleph_one
  letI : L.Structure M := str
  letI : Infinite M := hJ.1
  let a : M := Classical.choice (inferInstance : Nonempty M)
  letI : (L[[({a} : Set M)]]).Structure M :=
    namedExpansionStructure L M str a
  let c : (L[[({a} : Set M)]]).Constants := Algebra.namedConstant a
  have hc : NamedConstantMeans L M str a c := by
    change (c : M) = a
    rfl
  have hLF' : Algebra.LocallyFinite (L[[({a} : Set M)]]) M :=
    Algebra.locallyFinite_withNamedConstant hLF a
  have hJ' : Algebra.Jonsson (L[[({a} : Set M)]]) M :=
    Algebra.jonsson_withNamedConstant hJ a
  have hSharp : SharpConclusion (L[[({a} : Set M)]]) M :=
    sharpConclusion_of_sharp hLF' hJ' hcard c
  exact ⟨L, M, str, a, c, rfl, hc, hcard, hLF', hJ', hSharp⟩

end SourceFacingSharp
end ChainApproximation
