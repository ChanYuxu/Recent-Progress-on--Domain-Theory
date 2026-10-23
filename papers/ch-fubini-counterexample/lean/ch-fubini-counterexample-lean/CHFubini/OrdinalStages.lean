import CHFubini.EventStabilization

open Set Cardinal
open scoped Cardinal Ordinal
namespace CHFubini

/-- Each proper initial segment of the first uncountable ordinal is countable. -/
theorem omegaOneStage_Iio_countable (γ : CHFubini.OmegaOneStage) :
    (Iio γ).Countable := by
  have hcard : γ.1.card < Cardinal.aleph.{0} 1 := by
    apply Cardinal.lt_ord.mp
    simpa only [Cardinal.ord_aleph] using γ.2
  have hsmall : Countable (Iio γ.1) := by
    apply Cardinal.mk_le_aleph0_iff.mp
    simpa only [Cardinal.mk_Iio_ordinal, Cardinal.lift_le_aleph0] using
      (Cardinal.lt_aleph_one_iff.mp hcard)
  letI := hsmall
  let f : Iio γ → Iio γ.1 := fun ξ => ⟨ξ.1.1, ξ.2⟩
  have hf : Function.Injective f := by
    intro ξ η h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : Iio γ.1 => z.1) h
  exact Set.countable_coe_iff.mp hf.countable

/-- Countability includes the current stage, as required by the null-set
union in source equation `transfinite-choice`. -/
theorem omegaOneStage_Iic_countable (γ : CHFubini.OmegaOneStage) :
    (Iic γ).Countable := by
  rw [← Iio_union_Icc_eq_Iic (le_refl γ), Icc_self]
  exact (omegaOneStage_Iio_countable γ).union (countable_singleton γ)

/-- Every countable family of stages is bounded strictly below a single
countable ordinal, including when the family is empty. -/
theorem omegaOneStage_countable_strict_bound
    (A : Set CHFubini.OmegaOneStage) (hA : A.Countable) :
    ∃ β : CHFubini.OmegaOneStage, ∀ γ ∈ A, γ < β := by
  obtain ⟨σ, hσ⟩ := CHFubini.omegaOneStage_countablyBounded A hA
  refine ⟨⟨Order.succ σ.1, (Cardinal.isSuccLimit_omega 1).succ_lt σ.2⟩, ?_⟩
  intro γ hγ
  exact (hσ γ hγ).trans_lt (Order.lt_succ σ.1)


end CHFubini

