import FiniteValuationApproximable.Abstract.FSClass
import FiniteValuationApproximable.MonotoneTableDomain
import FiniteValuationApproximable.External.GierzInternal

/-!
# FS exponentials

This module exposes the source-facing name for the internally formalized
FS-exponential theorem.

Source: G. Gierz, K. H. Hofmann, K. Keimel, J. D. Lawson, M. Mislove and
D. S. Scott, *Continuous Lattices and Domains*, Cambridge University Press,
2003, Proposition II-2.18, printed page 168.

Exact source content: if `S` and `T` are FS-domains, then the dcpo of
Scott-continuous maps `[S -> T]`, ordered pointwise, is an FS-domain.

The source-facing theorem below is an alias for the internal proof in
`External/GierzInternal.lean`.  It introduces no axiom and does not mention
FVA, finite valuation kernels, global transfer, or the manuscript's main
theorem.
-/

set_option autoImplicit false

universe u

namespace FiniteValuationApproximable
namespace External

/-- Gierz et al. (2003), Proposition II-2.18, p. 168. -/
theorem gierz_II_2_18_fs_exponential
    {S T : Type u} [Preorder S] [Preorder T]
    (hS : IsFSDomain S) (hT : IsFSDomain T) :
    IsFSDomain (AbramskyJung.Chapter3.ContFun S T) :=
  GierzInternal.fs_exponential hS hT

end External

section Consequences

/-- Saturation turns every FVA approximate identity into a sequential FS
approximate identity; hence every FVA object is an FS-domain internally. -/
theorem IsFVA.isFSDomain_unconditional
    {D : Type u} [PartialOrder D] (hD : IsFVA.{u, u} D) :
    IsFSDomain D := by
  rcases hD.saturated_unconditional with ⟨A⟩
  exact A.toFSApproximateIdentity.isFSDomain hD.1.1

/-- The audited Gierz theorem discharges the function-space domain premise
for any two FVA objects. -/
theorem fvaFunction_isFSDomain
    {D E : Type u} [PartialOrder D] [PartialOrder E]
    (hD : IsFVA.{u, u} D) (hE : IsFVA.{u, u} E) :
    IsFSDomain (AbramskyJung.Chapter3.ContFun D E) :=
  External.gierz_II_2_18_fs_exponential
    hD.isFSDomain_unconditional hE.isFSDomain_unconditional

/-- Continuous-dcpo consequence used by `global_functionSpace_conditional`. -/
theorem fvaFunction_isContinuousDcpo
    {D E : Type u} [PartialOrder D] [PartialOrder E]
    (hD : IsFVA.{u, u} D) (hE : IsFVA.{u, u} E) :
    AbramskyJung.Chapter2.IsContinuousDcpo
      (AbramskyJung.Chapter3.ContFun D E) :=
  (fvaFunction_isFSDomain hD hE).isContinuousDcpo

variable {A P : Type u}
variable [Fintype A] [PartialOrder A] [Fintype P] [PartialOrder P]

/-- Source lemma `lem:M-domain`, derived from the audited external
exponential theorem after proving internally that finite `A` and finite
`VSub(P)` are FS-domains and that monotone tables are exactly the relevant
Scott-continuous function space. -/
theorem monotoneTable_isFSDomain : IsFSDomain (MonotoneTable A P) := by
  apply IsFSDomain.of_orderIso
    (monotoneTableOrderIsoContFun (A := A) (P := P))
  exact External.gierz_II_2_18_fs_exponential
    (finite_isFSDomain A)
    (Erosion.finiteSubprobability_isFSDomain (P := P))

/-- Continuous-dcpo component of `lem:M-domain`. -/
theorem monotoneTable_isContinuousDcpo :
    AbramskyJung.Chapter2.IsContinuousDcpo (MonotoneTable A P) :=
  monotoneTable_isFSDomain.isContinuousDcpo

end Consequences

end FiniteValuationApproximable
