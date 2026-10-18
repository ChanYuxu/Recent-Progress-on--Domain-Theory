import Practice.DomainTheory.Papers.RBFunctionSpace.Basic

/-!
# Located external inputs

The manuscript explicitly invokes two literature results before
`thm:rb-characterization`.  They are isolated here so that every theorem
depending on external mathematics has an inspectable axiom boundary.
-/

set_option autoImplicit false

universe u v

namespace RBFunctionSpace

/-- `prop:fact` (i), located in Miao--Luan--Liu--Li,
*Spaces of functions from RB-domains to quasicontinuous domains*,
Houston Journal of Mathematics 49 (2023), 87--103: a function space from an
RB-domain to a domain is continuous. -/
axiom rb_functionSpace_continuous
    {X : Type u} {E : Type v}
    [PartialOrder X] [PartialOrder E]
    (hX : IsDomain X) (hE : IsDomain E)
    (hRB : IsRBDomain X) :
    HasContinuousFunctionSpace X E

/-- `prop:fact` (iv), Abramsky--Jung, *Domain Theory*, Lemma 4.3.6:
if `[X → E]` is continuous, then `X` is Scott compact or `E` is a
disjoint union of pointed domains. -/
axiom continuous_functionSpace_compact_or_pointedComponents
    {X : Type u} {E : Type v}
    [PartialOrder X] [PartialOrder E]
    (hX : IsDomain X) (hE : IsDomain E)
    (hFun : HasContinuousFunctionSpace X E) :
    IsScottCompact X ∨ IsDisjointUnionOfPointedDomains E

end RBFunctionSpace
