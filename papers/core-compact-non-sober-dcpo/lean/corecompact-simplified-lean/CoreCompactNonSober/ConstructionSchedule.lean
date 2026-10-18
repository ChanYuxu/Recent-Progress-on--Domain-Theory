import CoreCompactNonSober.WitnessFamily
import Mathlib.SetTheory.Ordinal.Basic

/-!
# The initial-ordinal schedule and the stock bound

Source: Section 5.2, including `eq:stock-bound`.
Every key is scheduled unboundedly often. The proof only uses that a proper
initial segment of an initial ordinal has smaller cardinality; no regularity
of the localization cardinal is assumed.
-/

set_option autoImplicit false

namespace CoreCompactNonSober.Construction

open Set Cardinal Ambient Localization

local instance : TopologicalSpace Carrier := scottTopology Carrier

abbrev Stage := lambda.ord.ToType

theorem stage_cardinality : Cardinal.mk Stage = lambda := Cardinal.mk_ord_toType lambda

instance stageNonempty : Nonempty Stage := by
  apply Cardinal.mk_ne_zero_iff.mp
  rw [stage_cardinality]
  exact (Cardinal.aleph0_pos.trans aleph0_lt_lambda).ne'

theorem stage_predecessors_small (α : Stage) : Cardinal.mk (Set.Iio α) < lambda := by
  have hinit : Cardinal.ord (Cardinal.mk Stage) = Ordinal.type (fun a b : Stage ↦ a < b) := by
    rw [stage_cardinality]
    exact (Ordinal.type_toType lambda.ord).symm
  simpa only [stage_cardinality] using Cardinal.mk_Iio_lt α hinit

theorem stage_initial_segment_small (α : Stage) : Cardinal.mk (Set.Iic α) < lambda := by
  have heq : Set.Iic α = Set.Iio α ∪ {α} := by
    ext β
    simp only [Set.mem_Iic, Set.mem_union, Set.mem_Iio, Set.mem_singleton_iff]
    exact le_iff_lt_or_eq
  have hle : Cardinal.mk (Set.Iic α) ≤ max (Cardinal.mk (Set.Iio α)) Cardinal.aleph0 := by
    rw [heq]
    calc
      Cardinal.mk (Set.Iio α ∪ {α} : Set Stage) ≤ Cardinal.mk (Set.Iio α) + 1 := by
        simpa only [Cardinal.mk_singleton] using Cardinal.mk_union_le (Set.Iio α) {α}
      _ ≤ max (Cardinal.mk (Set.Iio α)) Cardinal.aleph0 +
          max (Cardinal.mk (Set.Iio α)) Cardinal.aleph0 :=
        add_le_add (le_max_left _ _) (Cardinal.one_le_aleph0.trans (le_max_right _ _))
      _ = max (Cardinal.mk (Set.Iio α)) Cardinal.aleph0 :=
        Cardinal.add_eq_self (le_max_right _ _)
  exact hle.trans_lt (max_lt (stage_predecessors_small α) aleph0_lt_lambda)

/-- Countably many points per previous stage still give fewer than lambda
old positive points, including when lambda is singular. -/
theorem predecessor_countable_stock_card_le (α : Stage) :
    Cardinal.mk ((Set.Iio α) × ℕ) ≤ max (Cardinal.mk (Set.Iio α)) Cardinal.aleph0 := by
  calc
    Cardinal.mk ((Set.Iio α) × ℕ) = Cardinal.mk (Set.Iio α) * Cardinal.aleph0 := by simp
    _ ≤ max (Cardinal.mk (Set.Iio α)) Cardinal.aleph0 *
        max (Cardinal.mk (Set.Iio α)) Cardinal.aleph0 :=
      mul_le_mul' (le_max_left _ _) (le_max_right _ _)
    _ = max (Cardinal.mk (Set.Iio α)) Cardinal.aleph0 :=
      Cardinal.mul_eq_self (le_max_right _ _)

theorem predecessor_countable_stock_small (α : Stage) :
    Cardinal.mk ((Set.Iio α) × ℕ) < lambda :=
  (predecessor_countable_stock_card_le α).trans_lt
    (max_lt (stage_predecessors_small α) aleph0_lt_lambda)

abbrev StaticKey :=
  {k : witnessFamily × PrintedBasic // k.1.val ∈ printedBasicSet k.2}

/-- The manuscript's literal static tasks use basis *sets*. The convenient
implementation uses `PrintedBasic` indices, which can repeat a basis set;
this projection proves that no literal task is lost. -/
abbrev SourceStaticKey :=
  {k : witnessFamily × {V : Set Carrier // V ∈ Set.range printedBasicSet} //
    k.1.val ∈ k.2.val}

def staticKeyToSource (k : StaticKey) : SourceStaticKey :=
  ⟨(k.val.1, ⟨printedBasicSet k.val.2, ⟨k.val.2, rfl⟩⟩), k.property⟩

/-- A literal source basis-set task carries its actual Scott-open set;
the proof of openness does not choose a different neighborhood. -/
def sourceStaticOpen (k : SourceStaticKey) : ScottOpens Carrier :=
  ⟨k.val.2.val, by
    obtain ⟨B, hB⟩ := k.val.2.property
    rw [← hB]
    exact printedBasicSet_isOpen_scott B⟩

theorem sourceStaticOpen_staticKeyToSource (k : StaticKey) :
    sourceStaticOpen (staticKeyToSource k) =
      (⟨printedBasicSet k.val.2, printedBasicSet_isOpen_scott _⟩ : ScottOpens Carrier) := by
  apply TopologicalSpace.Opens.ext
  rfl

theorem staticKeyToSource_surjective : Function.Surjective staticKeyToSource := by
  rintro ⟨⟨b, V⟩, hbV⟩
  obtain ⟨B, hB⟩ := V.property
  have hbB : b.val ∈ printedBasicSet B := by rw [hB]; exact hbV
  refine ⟨⟨(b, B), hbB⟩, ?_⟩
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · exact Subtype.ext hB

abbrev PotentialLabel := Stage × ℕ
/-- The printed reference family R*; the partner is not required to be retained. -/
def referenceFamily : Set Carrier := witnessFamily ∪ {⊤}

abbrev Reference := referenceFamily
abbrev DynamicKey := PotentialLabel × Reference
abbrev Key := StaticKey ⊕ DynamicKey
abbrev SourceKey := SourceStaticKey ⊕ DynamicKey

def keyToSource : Key → SourceKey
  | Sum.inl k => Sum.inl (staticKeyToSource k)
  | Sum.inr d => Sum.inr d

theorem keyToSource_surjective : Function.Surjective keyToSource := by
  intro k
  cases k with
  | inl k =>
    obtain ⟨j, rfl⟩ := staticKeyToSource_surjective k
    exact ⟨Sum.inl j, rfl⟩
  | inr d => exact ⟨Sum.inr d, rfl⟩

theorem reference_card_le : Cardinal.mk Reference ≤ lambda := by
  calc
    Cardinal.mk Reference ≤ Cardinal.mk witnessFamily + 1 := by
      simpa only [Reference, referenceFamily, Cardinal.mk_singleton] using
        Cardinal.mk_union_le witnessFamily ({⊤} : Set Carrier)
    _ ≤ lambda + lambda := add_le_add witnessFamily_card_le
      (Cardinal.one_le_aleph0.trans aleph0_lt_lambda.le)
    _ = lambda := Cardinal.add_eq_self aleph0_lt_lambda.le

theorem top_mem_reference : (⊤ : Carrier) ∈ referenceFamily := Or.inr rfl

theorem witness_mem_reference {b : Carrier} (hb : b ∈ witnessFamily) :
    b ∈ referenceFamily := Or.inl hb

theorem staticKey_card_le : Cardinal.mk StaticKey ≤ lambda := by
  calc
    Cardinal.mk StaticKey ≤ Cardinal.mk (witnessFamily × PrintedBasic) := Cardinal.mk_subtype_le _
    _ = Cardinal.mk witnessFamily * Cardinal.mk PrintedBasic := by simp
    _ ≤ lambda * Cardinal.aleph0 := mul_le_mul' witnessFamily_card_le Cardinal.mk_le_aleph0
    _ = lambda := Cardinal.mul_eq_left aleph0_lt_lambda.le aleph0_lt_lambda.le Cardinal.aleph0_ne_zero

theorem potentialLabel_cardinality : Cardinal.mk PotentialLabel = lambda := by
  simp only [PotentialLabel, Cardinal.mk_prod, Cardinal.lift_id, Cardinal.mk_nat, stage_cardinality]
  exact Cardinal.mul_eq_left aleph0_lt_lambda.le aleph0_lt_lambda.le Cardinal.aleph0_ne_zero

theorem dynamicKey_cardinality : Cardinal.mk DynamicKey = lambda := by
  apply le_antisymm
  · calc
      Cardinal.mk DynamicKey = lambda * Cardinal.mk Reference := by
        rw [Cardinal.mk_prod, Cardinal.lift_id, Cardinal.lift_id, potentialLabel_cardinality]
      _ ≤ lambda * lambda := mul_le_mul' le_rfl reference_card_le
      _ = lambda := Cardinal.mul_eq_self aleph0_lt_lambda.le
  · have hinj : Function.Injective
        (fun l : PotentialLabel ↦ (l, (⟨⊤, top_mem_reference⟩ : Reference))) := by
      intro a b h
      exact congrArg Prod.fst h
    simpa only [potentialLabel_cardinality] using Cardinal.mk_le_of_injective hinj

theorem key_cardinality : Cardinal.mk Key = lambda := by
  apply le_antisymm
  · calc
      Cardinal.mk Key = Cardinal.mk StaticKey + lambda := by
        simp only [Key, Cardinal.mk_sum, Cardinal.lift_id, dynamicKey_cardinality]
      _ ≤ lambda + lambda := add_le_add staticKey_card_le le_rfl
      _ = lambda := Cardinal.add_eq_self aleph0_lt_lambda.le
  · have hle : Cardinal.mk DynamicKey ≤ Cardinal.mk Key :=
      Cardinal.mk_le_of_injective (f := (Sum.inr : DynamicKey → Key)) Sum.inr_injective
    simpa only [dynamicKey_cardinality] using hle

theorem sourceKey_cardinality : Cardinal.mk SourceKey = lambda := by
  apply le_antisymm
  · exact (Cardinal.mk_le_of_surjective keyToSource_surjective).trans key_cardinality.le
  · have hle : Cardinal.mk DynamicKey ≤ Cardinal.mk SourceKey :=
      Cardinal.mk_le_of_injective (f := (Sum.inr : DynamicKey → SourceKey)) Sum.inr_injective
    simpa only [dynamicKey_cardinality] using hle

noncomputable def scheduleEquiv : Stage ≃ Key × Stage :=
  Classical.choice (Cardinal.eq.mp (by
    simp only [Cardinal.mk_prod, Cardinal.lift_id, stage_cardinality, key_cardinality]
    exact (Cardinal.mul_eq_self aleph0_lt_lambda.le).symm))

noncomputable def scheduledKey (α : Stage) : Key := (scheduleEquiv α).1

theorem scheduledKey_unbounded (k : Key) (α : Stage) :
    ∃ β : Stage, α < β ∧ scheduledKey β = k := by
  by_contra hnone
  have hbound : ∀ γ : Stage, scheduleEquiv.symm (k, γ) ≤ α := by
    intro γ
    apply le_of_not_gt
    intro hlt
    apply hnone
    exact ⟨scheduleEquiv.symm (k, γ), hlt, by simp [scheduledKey]⟩
  let f : Stage → Set.Iic α := fun γ ↦ ⟨scheduleEquiv.symm (k, γ), hbound γ⟩
  have hf : Function.Injective f := by
    intro γ δ h
    have hval := congrArg Subtype.val h
    change scheduleEquiv.symm (k, γ) = scheduleEquiv.symm (k, δ) at hval
    have heq : (k, γ) = (k, δ) := scheduleEquiv.symm.injective hval
    exact congrArg Prod.snd heq
  have hcard := Cardinal.mk_le_of_injective hf
  rw [stage_cardinality] at hcard
  exact not_le_of_gt (stage_initial_segment_small α) hcard

/-- Projecting repeated syntactic basis indices gives exactly a legal
bookkeeping sequence of the source's literal I0 ∪ I1 requirements. -/
noncomputable def sourceScheduledKey (α : Stage) : SourceKey :=
  keyToSource (scheduledKey α)

theorem sourceScheduledKey_unbounded (k : SourceKey) (α : Stage) :
    ∃ β : Stage, α < β ∧ sourceScheduledKey β = k := by
  obtain ⟨j, rfl⟩ := keyToSource_surjective k
  obtain ⟨β, hβ, hkey⟩ := scheduledKey_unbounded j α
  exact ⟨β, hβ, by simp only [sourceScheduledKey, hkey]⟩

end CoreCompactNonSober.Construction
