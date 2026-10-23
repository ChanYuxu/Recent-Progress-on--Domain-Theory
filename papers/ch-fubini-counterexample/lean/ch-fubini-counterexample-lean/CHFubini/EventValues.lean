import CHFubini.EventStabilization

/-! Pure event identities completing the connection from the tail construction
to fixed-point and full-mass tests in source `lem:rho-values`. -/

open Set

namespace CHFubini

universe u v w z

/-- Once the source point has entered one initial segment, its intersection
event is exactly coverage by the random open. No limit/intersection exchange
or measure-zero modification is used. -/
theorem limitPreimage_pointMembership_eq
    {I : Type u} {X : Type v} {A : Type w} {Y : Type z}
    (F : I → X → Y) (decode : Y → Set A) (initial : I → Set A)
    (R : X → Set A)
    (hF : ∀ β s, decode (F β s) = (initial β)ᶜ ∪ R s)
    (a : A) (ha : ∃ β, a ∈ initial β) :
    limitPreimage F {V : Y | a ∈ decode V} = {s : X | a ∈ R s} := by
  ext s
  constructor
  · intro hs
    obtain ⟨β, haβ⟩ := ha
    have hmem : a ∈ decode (F β s) := mem_iInter.mp hs β
    rw [hF] at hmem
    exact hmem.resolve_left (fun hnot => hnot haβ)
  · intro hs
    apply mem_iInter.mpr
    intro β
    change a ∈ decode (F β s)
    rw [hF]
    exact Or.inr hs

/-- Full-mass stage maps make all below-full-mass superlevel tests certain. -/
theorem limitPreimage_mass_superlevel_univ
    {I : Type u} {X : Type v} {Y : Type w}
    {M : Type z} [Preorder M]
    (F : I → X → Y) (mass : Y → M) (v r : M)
    (hF : ∀ β s, mass (F β s) = v) (hr : r < v) :
    limitPreimage F {V : Y | r < mass V} = univ := by
  apply eq_univ_of_forall
  intro s
  apply mem_iInter.mpr
  intro β
  change r < mass (F β s)
  rw [hF]
  exact hr

/-- At or above the constant mass level the same tests have empty events. -/
theorem limitPreimage_mass_superlevel_empty
    {I : Type u} [Nonempty I] {X : Type v} {Y : Type w}
    {M : Type z} [Preorder M]
    (F : I → X → Y) (mass : Y → M) (v r : M)
    (hF : ∀ β s, mass (F β s) = v) (hr : v ≤ r) :
    limitPreimage F {V : Y | r < mass V} = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro s hs
  obtain ⟨β⟩ := ‹Nonempty I›
  have hmem : r < mass (F β s) := mem_iInter.mp hs β
  rw [hF] at hmem
  exact (not_lt_of_ge hr) hmem

end CHFubini

#print axioms CHFubini.limitPreimage_pointMembership_eq

