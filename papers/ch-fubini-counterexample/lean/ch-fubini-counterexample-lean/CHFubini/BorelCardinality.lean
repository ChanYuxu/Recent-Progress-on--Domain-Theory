import CHFubini.EventStabilization
import Mathlib.MeasureTheory.MeasurableSpace.Card
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace

/-!
Pure mathlib candidates for the CH-enumeration step of the manuscript.

The sigma-algebra cardinality theorem is reused from mathlib's fully proved
`MeasurableSpace.cardinal_measurableSet_le_continuum`, not a new W-type argument.
No CH axiom or additional measurable-space structure on the source is assumed.
CH is an explicit hypothesis of the enumeration results only.

The cardinality statements are universe-polymorphic. Enumeration statements
are specialized to `Type 0`, sufficient for the concrete circle in the paper.
Both the small ordinal representation and the literal countable-ordinal stage
subtype are exposed, with a proved bridge.
-/

set_option autoImplicit false

open Set TopologicalSpace MeasureTheory Cardinal
open scoped Cardinal

namespace CHFubini

universe u

/-- In any second-countable space, the family of Borel sets has cardinal at
most the continuum. No separation or countability of points is required. -/
theorem cardinal_borelSet_le_continuum
    (X : Type u) [TopologicalSpace X] [SecondCountableTopology X] :
    #({s : Set X // @MeasurableSet X (borel X) s}) ≤ 𝔠 := by
  obtain ⟨b, hb, _, hbasis⟩ := exists_countable_basis X
  rw [hbasis.borel_eq_generateFrom]
  exact MeasurableSpace.cardinal_measurableSet_le_continuum
    ((Cardinal.le_aleph0_iff_set_countable.mpr hb).trans aleph0_le_continuum)

/-- Every family whose members are Borel has the same bound, including the
families of Borel null sets and positive-measure compact sets. -/
theorem cardinal_borelFamily_le_continuum
    {X : Type u} [TopologicalSpace X] [SecondCountableTopology X]
    (p : Set X → Prop)
    (hp : ∀ s, p s → @MeasurableSet X (borel X) s) :
    #({s : Set X // p s}) ≤ 𝔠 := by
  exact (Cardinal.mk_le_of_injective
    (f := fun s : {s : Set X // p s} =>
      (⟨s.1, hp s.1 s.2⟩ : {s : Set X // @MeasurableSet X (borel X) s}))
    (fun _ _ h => Subtype.ext
      (congrArg (fun t : {s : Set X // @MeasurableSet X (borel X) s} => t.1) h))).trans
      (cardinal_borelSet_le_continuum X)

/-- The Borel null sets of any measure on the Borel sigma-algebra form a
family of cardinal at most continuum. -/
theorem cardinal_borelNull_le_continuum
    {X : Type u} [TopologicalSpace X] [SecondCountableTopology X]
    (m : @Measure X (borel X)) :
    #({s : Set X // @MeasurableSet X (borel X) s ∧ m s = 0}) ≤ 𝔠 :=
  cardinal_borelFamily_le_continuum _ (fun _ h => h.1)

/-- Hausdorff compact sets are closed and therefore Borel. Positivity is a
restriction, not an extra cardinality hypothesis. -/
theorem cardinal_positiveCompact_le_continuum
    {X : Type u} [TopologicalSpace X] [SecondCountableTopology X] [T2Space X]
    (m : @Measure X (borel X)) :
    #({s : Set X // IsCompact s ∧ 0 < m s}) ≤ 𝔠 := by
  letI : MeasurableSpace X := borel X
  letI : BorelSpace X := ⟨rfl⟩
  exact cardinal_borelFamily_le_continuum _ (fun _ h => h.1.isClosed.measurableSet)

/-- A small representation of all countable ordinals, cardinal aleph-one. -/
abbrev SmallOmegaOneStage := (Cardinal.aleph.{0} 1).ord.ToType


theorem cardinal_smallOmegaOneStage : #SmallOmegaOneStage = Cardinal.aleph.{0} 1 := by
  simp [SmallOmegaOneStage]

/-- CH permits repetitions: every nonempty family bounded by continuum can
be enumerated by all countable ordinals. -/
theorem exists_surjective_smallOmegaOneStage
    {Y : Type} (hCH : Cardinal.continuum.{0} = Cardinal.aleph.{0} 1)
    (hY : #Y ≤ Cardinal.continuum.{0}) [Nonempty Y] :
    ∃ f : SmallOmegaOneStage → Y, Function.Surjective f := by
  apply Function.exists_surjective_iff.mpr
  refine ⟨⟨fun _ => Classical.ofNonempty⟩, ?_⟩
  apply (Cardinal.le_def Y SmallOmegaOneStage).mp
  simpa [cardinal_smallOmegaOneStage, hCH] using hY

/-- Change only the ordinal representation, not the collection of stages. -/
theorem exists_surjective_omegaOneStage
    {Y : Type} (hCH : Cardinal.continuum.{0} = Cardinal.aleph.{0} 1)
    (hY : #Y ≤ Cardinal.continuum.{0}) [Nonempty Y] :
    ∃ f : OmegaOneStage → Y, Function.Surjective f := by
  obtain ⟨f, hf⟩ := exists_surjective_smallOmegaOneStage hCH hY
  have e : OmegaOneStage ≃o SmallOmegaOneStage := by
    change {β : Ordinal.{0} // β < Ordinal.omega.{0} 1} ≃o
      (Cardinal.aleph.{0} 1).ord.ToType
    rw [Cardinal.ord_aleph]
    exact Ordinal.ToType.mk
  exact ⟨f ∘ e, hf.comp e.surjective⟩

/-- Source step (287-297): CH enumerates all members of any nonempty Borel
family of a second-countable `Type 0` space, with repetitions allowed. -/
theorem exists_borelFamily_enumeration
    {X : Type} [TopologicalSpace X] [SecondCountableTopology X]
    (hCH : Cardinal.continuum.{0} = Cardinal.aleph.{0} 1)
    (p : Set X → Prop)
    (hp : ∀ s, p s → @MeasurableSet X (borel X) s)
    (hne : ∃ s, p s) :
    ∃ f : OmegaOneStage → Set X, (∀ β, p (f β)) ∧
      ∀ s, p s → ∃ β, f β = s := by
  letI : Nonempty {s : Set X // p s} := by
    obtain ⟨s, hs⟩ := hne
    exact ⟨⟨s, hs⟩⟩
  obtain ⟨f, hf⟩ := exists_surjective_omegaOneStage hCH
    (cardinal_borelFamily_le_continuum p hp)
  refine ⟨fun β => (f β).1, fun β => (f β).2, ?_⟩
  intro s hs
  obtain ⟨β, hβ⟩ := hf ⟨s, hs⟩
  exact ⟨β, congrArg Subtype.val hβ⟩

/-- The manuscript's null-set enumeration. The empty set supplies the
nonempty-family witness for every Borel measure. -/
theorem exists_borelNull_enumeration
    {X : Type} [TopologicalSpace X] [SecondCountableTopology X]
    (hCH : Cardinal.continuum.{0} = Cardinal.aleph.{0} 1)
    (m : @Measure X (borel X)) :
    ∃ N : OmegaOneStage → Set X,
      (∀ β, @MeasurableSet X (borel X) (N β) ∧ m (N β) = 0) ∧
      ∀ s, @MeasurableSet X (borel X) s → m s = 0 → ∃ β, N β = s := by
  letI : MeasurableSpace X := borel X
  obtain ⟨N, hN, hsurj⟩ := exists_borelFamily_enumeration hCH
    (fun s => @MeasurableSet X (borel X) s ∧ m s = 0)
    (fun _ h => h.1) ⟨∅, MeasurableSet.empty, measure_empty⟩
  exact ⟨N, hN, fun s hs hm => hsurj s ⟨hs, hm⟩⟩

/-- The manuscript's positive-compact enumeration. A positive compact
witness is explicit, so the empty family is never falsely enumerated. -/
theorem exists_positiveCompact_enumeration
    {X : Type} [TopologicalSpace X] [SecondCountableTopology X] [T2Space X]
    (hCH : Cardinal.continuum.{0} = Cardinal.aleph.{0} 1)
    (m : @Measure X (borel X)) (hne : ∃ s, IsCompact s ∧ 0 < m s) :
    ∃ K : OmegaOneStage → Set X,
      (∀ β, IsCompact (K β) ∧ 0 < m (K β)) ∧
      ∀ s, IsCompact s → 0 < m s → ∃ β, K β = s := by
  letI : MeasurableSpace X := borel X
  letI : BorelSpace X := ⟨rfl⟩
  obtain ⟨K, hK, hsurj⟩ := exists_borelFamily_enumeration hCH
    (fun s => IsCompact s ∧ 0 < m s)
    (fun _ h => h.1.isClosed.measurableSet) hne
  exact ⟨K, hK, fun s hs hm => hsurj s ⟨hs, hm⟩⟩

end CHFubini

-- Candidate-only evidence commands. They are not additional assumptions.
#print axioms CHFubini.cardinal_borelSet_le_continuum
#print axioms CHFubini.cardinal_borelFamily_le_continuum
#print axioms CHFubini.cardinal_borelNull_le_continuum
#print axioms CHFubini.cardinal_positiveCompact_le_continuum
#print axioms CHFubini.cardinal_smallOmegaOneStage
#print axioms CHFubini.exists_surjective_smallOmegaOneStage
#print axioms CHFubini.exists_surjective_omegaOneStage
#print axioms CHFubini.exists_borelFamily_enumeration
#print axioms CHFubini.exists_borelNull_enumeration
#print axioms CHFubini.exists_positiveCompact_enumeration

