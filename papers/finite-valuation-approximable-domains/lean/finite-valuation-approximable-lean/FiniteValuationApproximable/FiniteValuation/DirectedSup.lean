import FiniteValuationApproximable.FiniteValuation.ErosionFS

/-!
# Directed suprema of finite stochastic simplices

This module closes the finite-dimensional directed-supremum bridge isolated in
`FiniteValuation.ErosionFS`.  The proof is internal to Mathlib and the
manuscript development.

For a directed family `D` with supremum `p`, let `s U` be the real supremum of
the `U`-masses of members of `D`.  Directedness and finiteness of the type of
upper sets give a sequence in `D` which approaches every `s U`
simultaneously.  Its coefficient functions lie in the compact cube
`[0,1]^P`, so a subsequence converges to a subprobability vector `r`.  Finite
sums show that every upper-set mass of `r` is `s U`; hence `r` is an upper
bound of `D`.  Leastness of `p`, together with `r <= p`, gives `r = p`.
-/

set_option autoImplicit false
set_option linter.unnecessarySimpa false

universe u

namespace FiniteValuationApproximable.Erosion

open scoped Classical BigOperators Topology
open Set Filter Topology

variable {P : Type u} [Fintype P] [PartialOrder P]

/-- Every coefficient of a subprobability vector lies in the unit interval. -/
theorem subprobability_coeff_mem_Icc (p : SubprobabilityVector P) (x : P) :
    p x ∈ Set.Icc (0 : Real) 1 := by
  constructor
  · exact p.coeff_nonneg x
  · calc
      p x = p.mass ({x} : Set P) := by
        simp [SubprobabilityVector.mass]
      _ ≤ p.mass (Set.univ : Set P) :=
        p.mass_mono (Set.subset_univ _)
      _ = p.totalMass := SubprobabilityVector.mass_univ p
      _ ≤ 1 := p.totalMass_le_one

/-- Upper-set mass commutes with coefficientwise sequential limits. -/
theorem tendsto_upperMass_of_tendsto_coeff
    {q : Nat → SubprobabilityVector P} {r : P → Real}
    (h : ∀ x : P, Tendsto (fun n => q n x) atTop (nhds (r x)))
    (U : UpperSet P) :
    Tendsto (fun n => upperMass (q n) U) atTop
      (nhds (∑ x, if x ∈ (U : Set P) then r x else 0)) := by
  unfold upperMass SubprobabilityVector.mass
  apply tendsto_finset_sum Finset.univ
  intro x hx
  by_cases hxU : x ∈ (U : Set P)
  · simpa [hxU] using h x
  · simp [hxU]

/-- A coefficientwise limit of finite subprobability vectors is again a
finite subprobability vector. -/
noncomputable def limitSubprobabilityVector
    {q : Nat → SubprobabilityVector P} {r : P → Real}
    (h : ∀ x : P, Tendsto (fun n => q n x) atTop (nhds (r x))) :
    SubprobabilityVector P where
  coeff := r
  coeff_nonneg x := by
    exact ge_of_tendsto' (h x) (fun n => (q n).coeff_nonneg x)
  total_le_one := by
    have hsum : Tendsto (fun n => ∑ x, q n x) atTop
        (nhds (∑ x, r x)) :=
      tendsto_finset_sum Finset.univ (fun x _ => h x)
    exact le_of_tendsto' hsum (fun n => (q n).total_le_one)

@[simp]
theorem limitSubprobabilityVector_apply
    {q : Nat → SubprobabilityVector P} {r : P → Real}
    (h : ∀ x : P, Tendsto (fun n => q n x) atTop (nhds (r x))) (x : P) :
    limitSubprobabilityVector h x = r x :=
  rfl

/-- The finite stochastic simplex satisfies the simultaneous upper-mass
approximation property required by the erosion proof of Scott continuity. -/
theorem directedUpperMassApproximation :
    DirectedUpperMassApproximation (P := P) := by
  intro D p hDne hDdir hp

  let massSet : UpperSet P → Set Real :=
    fun U => (fun d : SubprobabilityVector P => upperMass d U) '' D
  let s : UpperSet P → Real := fun U => sSup (massSet U)

  have hmassSet_nonempty (U : UpperSet P) : (massSet U).Nonempty := by
    rcases hDne with ⟨d, hdD⟩
    exact ⟨upperMass d U, ⟨d, hdD, rfl⟩⟩
  have hmassSet_bdd (U : UpperSet P) : BddAbove (massSet U) := by
    refine ⟨upperMass p U, ?_⟩
    rintro y ⟨d, hdD, rfl⟩
    exact hp.1 hdD U
  have hs_le_p (U : UpperSet P) : s U ≤ upperMass p U := by
    apply csSup_le (hmassSet_nonempty U)
    rintro y ⟨d, hdD, rfl⟩
    exact hp.1 hdD U

  let δ : Nat → Real := fun n => 1 / ((n : Real) + 1)
  have hδ_pos (n : Nat) : 0 < δ n := by
    dsimp only [δ]
    positivity
  have hδ_tendsto : Tendsto δ atTop (nhds 0) := by
    simpa only [δ] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := Real))

  have hpointApprox : ∀ n : Nat, ∀ U : UpperSet P,
      ∃ d ∈ D, s U - δ n < upperMass d U := by
    intro n U
    have hlt : s U - δ n < s U := sub_lt_self _ (hδ_pos n)
    rcases exists_lt_of_lt_csSup (hmassSet_nonempty U) hlt with
      ⟨y, hyset, hsy⟩
    rcases hyset with ⟨d, hdD, rfl⟩
    exact ⟨d, hdD, hsy⟩
  choose a haD haApprox using hpointApprox

  have hsimultaneous : ∀ n : Nat,
      ∃ d ∈ D, ∀ U : UpperSet P, s U - δ n < upperMass d U := by
    intro n
    letI : Nonempty {d : SubprobabilityVector P // d ∈ D} :=
      ⟨⟨Classical.choose hDne, Classical.choose_spec hDne⟩⟩
    let candidates : Finset {d : SubprobabilityVector P // d ∈ D} :=
      Finset.univ.image fun U : UpperSet P => ⟨a n U, haD n U⟩
    rcases hDdir.directed_val.finset_le candidates with ⟨z, hz⟩
    refine ⟨z.1, z.2, ?_⟩
    intro U
    have haz : a n U ≤ z.1 := by
      exact hz ⟨a n U, haD n U⟩
        (Finset.mem_image.mpr ⟨U, Finset.mem_univ U, rfl⟩)
    exact (haApprox n U).trans_le (haz U)
  choose q hqD hqApprox using hsimultaneous

  have hq_mass_le_s (n : Nat) (U : UpperSet P) :
      upperMass (q n) U ≤ s U := by
    apply le_csSup (hmassSet_bdd U)
    exact ⟨q n, hqD n, rfl⟩
  have hq_mass_tendsto (U : UpperSet P) :
      Tendsto (fun n => upperMass (q n) U) atTop (nhds (s U)) := by
    have hlower : Tendsto (fun n => s U - δ n) atTop (nhds (s U)) := by
      simpa using tendsto_const_nhds.sub hδ_tendsto
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlower
      tendsto_const_nhds
      (fun n => le_of_lt (hqApprox n U))
      (fun n => hq_mass_le_s n U)

  let cube : Set (P → Real) :=
    Set.pi Set.univ fun _ => Set.Icc (0 : Real) 1
  have hcube_compact : IsCompact cube := by
    exact isCompact_univ_pi fun _ => isCompact_Icc
  have hq_cube (n : Nat) : (fun x => q n x) ∈ cube := by
    intro x hx
    exact subprobability_coeff_mem_Icc (q n) x
  rcases hcube_compact.tendsto_subseq hq_cube with
    ⟨r, hr_cube, φ, hφ, hφlim⟩
  have hcoeff (x : P) :
      Tendsto (fun n => q (φ n) x) atTop (nhds (r x)) := by
    exact tendsto_pi_nhds.mp hφlim x
  let rv : SubprobabilityVector P :=
    limitSubprobabilityVector hcoeff

  have hmass_r (U : UpperSet P) :
      Tendsto (fun n => upperMass (q (φ n)) U) atTop
        (nhds (upperMass rv U)) := by
    have hm := tendsto_upperMass_of_tendsto_coeff hcoeff U
    simpa [rv, upperMass, SubprobabilityVector.mass] using hm
  have hs_eq_r (U : UpperSet P) : s U = upperMass rv U := by
    exact tendsto_nhds_unique
      ((hq_mass_tendsto U).comp hφ.tendsto_atTop) (hmass_r U)

  have hrv_upper : ∀ d ∈ D, d ≤ rv := by
    intro d hdD U
    calc
      upperMass d U ≤ s U := by
        apply le_csSup (hmassSet_bdd U)
        exact ⟨d, hdD, rfl⟩
      _ = upperMass rv U := hs_eq_r U
  have hrv_le_p : rv ≤ p := by
    intro U
    rw [← hs_eq_r U]
    exact hs_le_p U
  have hp_le_rv : p ≤ rv := hp.2 hrv_upper
  have hrv_eq_p : rv = p := le_antisymm hrv_le_p hp_le_rv
  have hs_eq_p (U : UpperSet P) : s U = upperMass p U := by
    simpa [hrv_eq_p] using hs_eq_r U

  intro ε hε
  have heventually : ∀ᶠ n in atTop, δ n < ε := by
    exact hδ_tendsto (Iio_mem_nhds hε)
  rcases heventually.exists with ⟨n, hn⟩
  refine ⟨q n, hqD n, ?_⟩
  intro U
  calc
    upperMass p U - ε < s U - δ n := by
      rw [hs_eq_p U]
      linarith
    _ < upperMass (q n) U := hqApprox n U

/-- Every upper-set mass of a subprobability vector is at most one. -/
theorem upperMass_le_one (p : SubprobabilityVector P) (U : UpperSet P) :
    upperMass p U ≤ 1 := by
  calc
    upperMass p U ≤ p.mass (Set.univ : Set P) :=
      p.mass_mono (Set.subset_univ _)
    _ = p.totalMass := SubprobabilityVector.mass_univ p
    _ ≤ 1 := p.totalMass_le_one

/-- Every nonempty directed subset of the finite stochastic simplex has a
least upper bound.  This is the existence half of directed completeness and
uses the same simultaneous real-supremum/compactness construction as
`directedUpperMassApproximation`, but does not assume a supremum in advance. -/
theorem finiteSubprobability_exists_isLUB
    (D : Set (SubprobabilityVector P)) (hDne : D.Nonempty)
    (hDdir : DirectedOn (· ≤ ·) D) :
    ∃ p : SubprobabilityVector P, IsLUB D p := by
  let massSet : UpperSet P → Set Real :=
    fun U => (fun d : SubprobabilityVector P => upperMass d U) '' D
  let s : UpperSet P → Real := fun U => sSup (massSet U)
  have hmassSet_nonempty (U : UpperSet P) : (massSet U).Nonempty := by
    rcases hDne with ⟨d, hdD⟩
    exact ⟨upperMass d U, ⟨d, hdD, rfl⟩⟩
  have hmassSet_bdd (U : UpperSet P) : BddAbove (massSet U) := by
    refine ⟨1, ?_⟩
    rintro y ⟨d, hdD, rfl⟩
    exact upperMass_le_one d U
  let δ : Nat → Real := fun n => 1 / ((n : Real) + 1)
  have hδ_pos (n : Nat) : 0 < δ n := by
    dsimp only [δ]
    positivity
  have hδ_tendsto : Tendsto δ atTop (nhds 0) := by
    simpa only [δ] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := Real))
  have hpointApprox : ∀ n : Nat, ∀ U : UpperSet P,
      ∃ d ∈ D, s U - δ n < upperMass d U := by
    intro n U
    have hlt : s U - δ n < s U := sub_lt_self _ (hδ_pos n)
    rcases exists_lt_of_lt_csSup (hmassSet_nonempty U) hlt with
      ⟨y, hyset, hsy⟩
    rcases hyset with ⟨d, hdD, rfl⟩
    exact ⟨d, hdD, hsy⟩
  choose a haD haApprox using hpointApprox
  have hsimultaneous : ∀ n : Nat,
      ∃ d ∈ D, ∀ U : UpperSet P, s U - δ n < upperMass d U := by
    intro n
    letI : Nonempty {d : SubprobabilityVector P // d ∈ D} :=
      ⟨⟨Classical.choose hDne, Classical.choose_spec hDne⟩⟩
    let candidates : Finset {d : SubprobabilityVector P // d ∈ D} :=
      Finset.univ.image fun U : UpperSet P => ⟨a n U, haD n U⟩
    rcases hDdir.directed_val.finset_le candidates with ⟨z, hz⟩
    refine ⟨z.1, z.2, ?_⟩
    intro U
    have haz : a n U ≤ z.1 := by
      exact hz ⟨a n U, haD n U⟩
        (Finset.mem_image.mpr ⟨U, Finset.mem_univ U, rfl⟩)
    exact (haApprox n U).trans_le (haz U)
  choose q hqD hqApprox using hsimultaneous
  have hq_mass_le_s (n : Nat) (U : UpperSet P) :
      upperMass (q n) U ≤ s U := by
    apply le_csSup (hmassSet_bdd U)
    exact ⟨q n, hqD n, rfl⟩
  have hq_mass_tendsto (U : UpperSet P) :
      Tendsto (fun n => upperMass (q n) U) atTop (nhds (s U)) := by
    have hlower : Tendsto (fun n => s U - δ n) atTop (nhds (s U)) := by
      simpa using tendsto_const_nhds.sub hδ_tendsto
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlower
      tendsto_const_nhds
      (fun n => le_of_lt (hqApprox n U))
      (fun n => hq_mass_le_s n U)
  let cube : Set (P → Real) :=
    Set.pi Set.univ fun _ => Set.Icc (0 : Real) 1
  have hcube_compact : IsCompact cube := by
    exact isCompact_univ_pi fun _ => isCompact_Icc
  have hq_cube (n : Nat) : (fun x => q n x) ∈ cube := by
    intro x hx
    exact subprobability_coeff_mem_Icc (q n) x
  rcases hcube_compact.tendsto_subseq hq_cube with
    ⟨r, hr_cube, φ, hφ, hφlim⟩
  have hcoeff (x : P) :
      Tendsto (fun n => q (φ n) x) atTop (nhds (r x)) := by
    exact tendsto_pi_nhds.mp hφlim x
  let rv : SubprobabilityVector P :=
    limitSubprobabilityVector hcoeff
  have hmass_r (U : UpperSet P) :
      Tendsto (fun n => upperMass (q (φ n)) U) atTop
        (nhds (upperMass rv U)) := by
    have hm := tendsto_upperMass_of_tendsto_coeff hcoeff U
    simpa [rv, upperMass, SubprobabilityVector.mass] using hm
  have hs_eq_r (U : UpperSet P) : s U = upperMass rv U := by
    exact tendsto_nhds_unique
      ((hq_mass_tendsto U).comp hφ.tendsto_atTop) (hmass_r U)
  have hrv_upper : ∀ d ∈ D, d ≤ rv := by
    intro d hdD U
    calc
      upperMass d U ≤ s U := by
        apply le_csSup (hmassSet_bdd U)
        exact ⟨d, hdD, rfl⟩
      _ = upperMass rv U := hs_eq_r U
  have hrv_le_upper (b : SubprobabilityVector P)
      (hb : ∀ d ∈ D, d ≤ b) : rv ≤ b := by
    intro U
    rw [← hs_eq_r U]
    apply csSup_le (hmassSet_nonempty U)
    rintro y ⟨d, hdD, rfl⟩
    exact hb d hdD U
  exact ⟨rv, ⟨hrv_upper, fun b hb => hrv_le_upper b hb⟩⟩

/-- Unconditional Scott continuity of every nonnegative-time erosion map. -/
theorem exactPhi_scott {t : Real} (ht0 : 0 ≤ t) :
    ScottContinuous (fun p : SubprobabilityVector P => exactPhi t p) :=
  exactPhi_scott_of_directedUpperMassApproximation
    directedUpperMassApproximation ht0

/-- Unconditional explicit FS approximate identity on every finite
subprobability stochastic simplex. -/
theorem explicitFSApproximateIdentity :
    HasExplicitFSApproximateIdentity (P := P) :=
  explicitFSApproximateIdentity_of_directedUpperMassApproximation
    directedUpperMassApproximation

end FiniteValuationApproximable.Erosion
