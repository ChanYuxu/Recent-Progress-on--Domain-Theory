import FiniteValuationApproximable.FiniteValuation.ProbabilityFS

/-!
# Finite bounded-complete domains and the heavy-set retraction

This module formalizes the finite combinatorial core of source item
`lem:finite-bc-fva` (source lines 3558--3607 of `main (17).tex`) and the
finite meet-closure step in `prop:omega-bc-fva`.

The bounded-completeness assumption is stated directly as existence of
suprema for bounded subsets; it contains no FVA or retraction conclusion.
The sole finite-valuation semantic boundary is also explicit:
`ProbabilityUpperMassPreservesDirectedSuprema` says that each finite
upper-set mass coordinate preserves an already existing directed supremum.
Under this premise, the manuscript's threshold construction gives an actual
Scott-continuous retraction from normalized finite probabilities.

Source version: SHA-256
`4b2e65f0f96347bea4df7571e8993ad6e888c0ff7181c1305c5056880365ac94`.
-/

set_option autoImplicit false
set_option linter.unnecessarySimpa false

universe u v

namespace FiniteValuationApproximable

open scoped BigOperators Classical
open Set
open SubprobabilityVector

abbrev LocalIsUpperBound {X : Type u} [Preorder X] :=
  AbramskyJung.Chapter2.IsUpperBound (α := X)

abbrev LocalIsLowerBound {X : Type u} [Preorder X] :=
  AbramskyJung.Chapter2.IsLowerBound (α := X)

abbrev LocalIsSup {X : Type u} [Preorder X] :=
  AbramskyJung.Chapter2.IsSup (α := X)

abbrev LocalIsInf {X : Type u} [Preorder X] :=
  AbramskyJung.Chapter2.IsInf (α := X)

abbrev LocalDirectedSet {X : Type u} [Preorder X] :=
  AbramskyJung.Chapter2.DirectedSet (α := X)

/-! ## Bounded completeness and finite infimum closure -/

section BoundedCompleteness

variable {B : Type u} [PartialOrder B]

/-- A subset has a common upper bound. -/
def HasCommonUpperBound (S : Set B) : Prop :=
  ∃ u : B, LocalIsUpperBound S u

/-- Bounded completeness, stated without any domain or FVA conclusion. -/
def IsBoundedCompleteOrder (B : Type u) [PartialOrder B] : Prop :=
  ∀ S : Set B, HasCommonUpperBound S → ∃ s : B, LocalIsSup S s

/-- Existence of infima for every nonempty finite subset. -/
def HasNonemptyFiniteInfima (B : Type u) [Fintype B] [PartialOrder B] : Prop :=
  ∀ S : Finset B, S.Nonempty → ∃ m : B, LocalIsInf (S : Set B) m

/-- A finite poset with all nonempty finite infima is bounded complete.

For a bounded set `A`, take the infimum of the nonempty finite set of all
upper bounds of `A`.  This is exactly the finite lattice calculation used in
the proof of `prop:omega-bc-fva`. -/
theorem isBoundedCompleteOrder_of_nonemptyFiniteInfima
    [Fintype B] [Nonempty B]
    (hInf : HasNonemptyFiniteInfima B) :
    IsBoundedCompleteOrder B := by
  intro A hA
  let U : Finset B :=
    Finset.univ.filter (fun u => LocalIsUpperBound A u)
  have hUne : U.Nonempty := by
    rcases hA with ⟨u, hu⟩
    exact ⟨u, Finset.mem_filter.mpr ⟨Finset.mem_univ u, hu⟩⟩
  rcases hInf U hUne with ⟨m, hm⟩
  refine ⟨m, ?_⟩
  constructor
  · intro a ha
    apply hm.2 a
    intro u hu
    exact (Finset.mem_filter.mp hu).2 ha
  · intro y hy
    apply hm.1
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ y, hy⟩

variable {D : Type v} [PartialOrder D]

/-- A finite subset of an ambient poset is closed under all nonempty finite
infima, with the ambient infimum required to remain in the subset. -/
def ClosedUnderNonemptyFiniteInfima (C : Finset D) : Prop :=
  ∀ S : Finset D, S.Nonempty → S ⊆ C →
    ∃ m ∈ C, LocalIsInf (S : Set D) m

/-- The finite carrier cut out by a finite subset. -/
abbrev FiniteCarrier (C : Finset D) := {x : D // x ∈ C}

/-- Ambient nonempty-infimum closure descends to the finite subtype. -/
theorem finiteCarrier_hasNonemptyFiniteInfima
    (C : Finset D) (hC : ClosedUnderNonemptyFiniteInfima C) :
    HasNonemptyFiniteInfima (FiniteCarrier C) := by
  classical
  intro S hSne
  let T : Finset D := S.image (fun x : FiniteCarrier C => x.1)
  have hTne : T.Nonempty := by
    rcases hSne with ⟨x, hx⟩
    exact ⟨x.1, Finset.mem_image.mpr ⟨x, hx, rfl⟩⟩
  have hTC : T ⊆ C := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨y, _hy, rfl⟩
    exact y.2
  rcases hC T hTne hTC with ⟨m, hmC, hmInf⟩
  refine ⟨⟨m, hmC⟩, ?_⟩
  constructor
  · intro x hx
    exact hmInf.1 (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
  · intro y hy
    apply hmInf.2 y.1
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨z, hz, rfl⟩
    exact hy hz

/-- The infimum-closed finite carrier is bounded complete. -/
theorem finiteCarrier_isBoundedCompleteOrder
    (C : Finset D) (hCne : C.Nonempty)
    (hC : ClosedUnderNonemptyFiniteInfima C) :
    IsBoundedCompleteOrder (FiniteCarrier C) := by
  classical
  haveI : Nonempty (FiniteCarrier C) := by
    rcases hCne with ⟨x, hx⟩
    exact ⟨⟨x, hx⟩⟩
  exact isBoundedCompleteOrder_of_nonemptyFiniteInfima
    (finiteCarrier_hasNonemptyFiniteInfima C hC)

end BoundedCompleteness

/-! ## Threshold and heavy sets -/

section HeavySets

variable {B : Type u} [Fintype B] [PartialOrder B]

/-- The gap `1/(|B|+1)` complementary to the manuscript threshold. -/
noncomputable def finiteBcThresholdGap (B : Type u) [Fintype B] : Real :=
  1 / ((Fintype.card B : Real) + 1)

/-- The manuscript threshold `tau = 1 - 1/(|B|+1)`. -/
noncomputable def finiteBcThreshold (B : Type u) [Fintype B] : Real :=
  1 - finiteBcThresholdGap B

theorem finiteBcThresholdGap_pos :
    0 < finiteBcThresholdGap B := by
  unfold finiteBcThresholdGap
  positivity

theorem finiteBcThresholdGap_lt_one [Nonempty B] :
    finiteBcThresholdGap B < 1 := by
  have hcardNat : 0 < Fintype.card B := Fintype.card_pos
  have hcard : (0 : Real) < Fintype.card B := by exact_mod_cast hcardNat
  have hden : (0 : Real) < (Fintype.card B : Real) + 1 := by linarith
  unfold finiteBcThresholdGap
  apply (div_lt_iff₀ hden).2
  nlinarith

theorem finiteBcThreshold_pos [Nonempty B] :
    0 < finiteBcThreshold B := by
  unfold finiteBcThreshold
  linarith [finiteBcThresholdGap_lt_one (B := B)]

theorem finiteBcThreshold_lt_one :
    finiteBcThreshold B < 1 := by
  unfold finiteBcThreshold
  linarith [finiteBcThresholdGap_pos (B := B)]

/-- Elements whose principal upper set has mass strictly above `tau`. -/
noncomputable def finiteBcHeavySet (p : ProbabilityVector B) : Finset B :=
  Finset.univ.filter (fun b =>
    finiteBcThreshold B < upperMass p.1 (principalUpperSet b))

@[simp]
theorem mem_finiteBcHeavySet (p : ProbabilityVector B) (b : B) :
    b ∈ finiteBcHeavySet p ↔
      finiteBcThreshold B < upperMass p.1 (principalUpperSet b) := by
  simp [finiteBcHeavySet]

/-- Mass splits across a finite set and its complement. -/
theorem ProbabilityVector.mass_add_mass_compl
    (p : ProbabilityVector B) (S : Set B) :
    p.1.mass S + p.1.mass Sᶜ = 1 := by
  classical
  calc
    p.1.mass S + p.1.mass Sᶜ = p.1.totalMass := by
      unfold SubprobabilityVector.mass SubprobabilityVector.totalMass
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro x _hx
      by_cases hx : x ∈ S <;> simp [hx]
    _ = 1 := ProbabilityVector.totalMass_eq_one p

theorem ProbabilityVector.mass_compl
    (p : ProbabilityVector B) (S : Set B) :
    p.1.mass Sᶜ = 1 - p.1.mass S := by
  linarith [ProbabilityVector.mass_add_mass_compl p S]

@[simp]
theorem SubprobabilityVector.mass_singleton
    (p : SubprobabilityVector B) (x : B) :
    p.mass ({x} : Set B) = p x := by
  classical
  unfold SubprobabilityVector.mass
  simp

theorem ProbabilityVector.coeff_le_mass_of_mem
    (p : ProbabilityVector B) {x : B} {S : Set B} (hx : x ∈ S) :
    p x ≤ p.1.mass S := by
  have hmono := p.1.mass_mono
    (show ({x} : Set B) ⊆ S by simpa using hx)
  simpa using hmono

/-- Some atom has mass at least `1/(|B|+1)`.  This is a slightly sharper
route to the common-upper-point conclusion than the source's union bound. -/
theorem ProbabilityVector.exists_thresholdGap_le_coeff
    [Nonempty B] (p : ProbabilityVector B) :
    ∃ x : B, finiteBcThresholdGap B ≤ p x := by
  by_contra h
  have hlt : ∀ x : B, p x < finiteBcThresholdGap B := by
    intro x
    exact lt_of_not_ge (fun hx => h ⟨x, hx⟩)
  have hsumlt :
      (∑ x : B, p x) < ∑ _x : B, finiteBcThresholdGap B := by
    exact Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
      (fun x _hx => hlt x)
  have hright :
      (∑ _x : B, finiteBcThresholdGap B) =
        (Fintype.card B : Real) * finiteBcThresholdGap B := by
    simp
  have hden : (0 : Real) < (Fintype.card B : Real) + 1 := by positivity
  have hratio :
      (Fintype.card B : Real) * finiteBcThresholdGap B < 1 := by
    unfold finiteBcThresholdGap
    rw [show (Fintype.card B : Real) * (1 / ((Fintype.card B : Real) + 1)) =
      (Fintype.card B : Real) / ((Fintype.card B : Real) + 1) by ring]
    exact (div_lt_one hden).2 (by linarith)
  have htotal : (∑ x : B, p x) = 1 :=
    ProbabilityVector.totalMass_eq_one p
  rw [htotal, hright] at hsumlt
  linarith

/-- Every heavy set has a common upper point.  The chosen atom `x` cannot
lie outside any heavy principal upper set, since its mass is at least the
threshold gap while every such complement has mass strictly below that gap. -/
theorem finiteBcHeavySet_hasCommonUpperBound
    [Nonempty B] (p : ProbabilityVector B) :
    HasCommonUpperBound (finiteBcHeavySet p : Set B) := by
  obtain ⟨x, hx⟩ :=
    ProbabilityVector.exists_thresholdGap_le_coeff p
  refine ⟨x, ?_⟩
  intro b hb
  have hbHeavy := (mem_finiteBcHeavySet p b).mp hb
  by_contra hbx
  have hxCompl : x ∈ (Set.Ici b)ᶜ := by simpa using hbx
  have hxMass : p x ≤ p.1.mass ((Set.Ici b)ᶜ : Set B) :=
    ProbabilityVector.coeff_le_mass_of_mem p hxCompl
  have hCompl :
      p.1.mass ((Set.Ici b)ᶜ : Set B) =
        1 - upperMass p.1 (principalUpperSet b) := by
    simpa [upperMass, principalUpperSet] using
      ProbabilityVector.mass_compl p (Set.Ici b)
  have hComplLt :
      p.1.mass ((Set.Ici b)ᶜ : Set B) < finiteBcThresholdGap B := by
    rw [hCompl]
    unfold finiteBcThreshold at hbHeavy
    linarith
  linarith

/-- Stochastic comparison can only enlarge the heavy set. -/
theorem finiteBcHeavySet_mono {p q : ProbabilityVector B} (hpq : p ≤ q) :
    finiteBcHeavySet p ⊆ finiteBcHeavySet q := by
  intro b hb
  apply (mem_finiteBcHeavySet q b).2
  exact (mem_finiteBcHeavySet p b).1 hb |>.trans_le
    (hpq (principalUpperSet b))

end HeavySets

/-! ## Bounded-complete selection map -/

section Selection

variable {B : Type u} [Fintype B] [PartialOrder B] [Nonempty B]

/-- A selected supremum of a bounded finite subset. -/
noncomputable def finiteBcSelectedSup
    (hBC : IsBoundedCompleteOrder B) (S : Finset B)
    (hS : HasCommonUpperBound (S : Set B)) : B :=
  Classical.choose (hBC (S : Set B) hS)

theorem finiteBcSelectedSup_isSup
    (hBC : IsBoundedCompleteOrder B) (S : Finset B)
    (hS : HasCommonUpperBound (S : Set B)) :
    LocalIsSup (S : Set B) (finiteBcSelectedSup hBC S hS) :=
  Classical.choose_spec (hBC (S : Set B) hS)

/-- Suprema selected from nested bounded finite sets are ordered. -/
theorem finiteBcSelectedSup_mono
    (hBC : IsBoundedCompleteOrder B)
    {S T : Finset B}
    (hS : HasCommonUpperBound (S : Set B))
    (hT : HasCommonUpperBound (T : Set B))
    (hST : S ⊆ T) :
    finiteBcSelectedSup hBC S hS ≤ finiteBcSelectedSup hBC T hT := by
  apply (finiteBcSelectedSup_isSup hBC S hS).2
  intro x hx
  exact (finiteBcSelectedSup_isSup hBC T hT).1 (hST hx)

/-- The source selection map `r_B(mu) = sup S(mu)`. -/
noncomputable def finiteBcRetraction
    (hBC : IsBoundedCompleteOrder B) (p : ProbabilityVector B) : B :=
  finiteBcSelectedSup hBC (finiteBcHeavySet p)
    (finiteBcHeavySet_hasCommonUpperBound p)

theorem finiteBcRetraction_monotone
    (hBC : IsBoundedCompleteOrder B) :
    Monotone (finiteBcRetraction hBC) := by
  intro p q hpq
  exact finiteBcSelectedSup_mono hBC
    (finiteBcHeavySet_hasCommonUpperBound p)
    (finiteBcHeavySet_hasCommonUpperBound q)
    (finiteBcHeavySet_mono hpq)

theorem upperMass_diracProbability_principal (b x : B) :
    upperMass (diracProbability x).1 (principalUpperSet b) =
      if b ≤ x then 1 else 0 := by
  change (dirac x).mass (Set.Ici b) = if b ≤ x then 1 else 0
  rw [SubprobabilityVector.mass_dirac]
  simp

/-- The heavy set of a Dirac mass is exactly the finite lower set of its
support point. -/
theorem mem_finiteBcHeavySet_diracProbability (b x : B) :
    b ∈ finiteBcHeavySet (diracProbability x) ↔ b ≤ x := by
  rw [mem_finiteBcHeavySet, upperMass_diracProbability_principal]
  by_cases hbx : b ≤ x
  · simp [hbx, finiteBcThreshold_lt_one (B := B)]
  · simp [hbx, le_of_lt (finiteBcThreshold_pos (B := B))]

theorem finiteBcHeavySet_diracProbability_isSup (x : B) :
    LocalIsSup (finiteBcHeavySet (diracProbability x) : Set B) x := by
  constructor
  · intro b hb
    exact (mem_finiteBcHeavySet_diracProbability b x).1 hb
  · intro y hy
    exact hy ((mem_finiteBcHeavySet_diracProbability x x).2 le_rfl)

/-- The threshold map retracts the Dirac embedding exactly. -/
theorem finiteBcRetraction_diracProbability
    (hBC : IsBoundedCompleteOrder B) (x : B) :
    finiteBcRetraction hBC (diracProbability x) = x := by
  exact AbramskyJung.Chapter2.IsSup.unique
    (finiteBcSelectedSup_isSup hBC _
      (finiteBcHeavySet_hasCommonUpperBound (diracProbability x)))
    (finiteBcHeavySet_diracProbability_isSup x)

end Selection

/-! ## Directed suprema and Scott continuity -/

section ScottContinuity

variable {B : Type u} [Fintype B] [PartialOrder B] [Nonempty B]

/-- The exact finite-dimensional semantic bridge used in the source proof:
every upper-set mass coordinate preserves every already existing directed
supremum of normalized finite probability vectors.

This proposition neither mentions the threshold map nor contains an FVA or
retraction conclusion. -/
def ProbabilityUpperMassPreservesDirectedSuprema
    (B : Type u) [Fintype B] [PartialOrder B] : Prop :=
  ∀ (A : Set (ProbabilityVector B)) (p : ProbabilityVector B),
    LocalDirectedSet A → LocalIsSup A p → ∀ U : UpperSet B,
      LocalIsSup
        ((fun q : ProbabilityVector B => upperMass q.1 U) '' A)
        (upperMass p.1 U)

/-- The minimal directed-supremum premise needed by the threshold map: every
coordinate that is heavy at the supremum is already heavy at some member.
It is strictly weaker in form than preservation of the entire real-valued
upper-mass supremum. -/
def FiniteBcHeavyCoordinatesAccessible
    (B : Type u) [Fintype B] [PartialOrder B] : Prop :=
  ∀ (A : Set (ProbabilityVector B)) (p : ProbabilityVector B),
    LocalDirectedSet A → LocalIsSup A p → ∀ b : B,
      b ∈ finiteBcHeavySet p →
        ∃ q ∈ A, b ∈ finiteBcHeavySet q

/-- A finite family of persistent requirements can be met simultaneously in
a directed set. -/
theorem exists_mem_forall_finset_of_directed
    {X : Type u} {K : Type v} [Preorder X]
    {A : Set X} (hA : LocalDirectedSet A)
    (S : Finset K) (R : K → X → Prop)
    (hexists : ∀ k ∈ S, ∃ x ∈ A, R k x)
    (hpersist : ∀ k ∈ S, ∀ {x y : X}, R k x → x ≤ y → R k y) :
    ∃ y ∈ A, ∀ k ∈ S, R k y := by
  classical
  induction S using Finset.induction with
  | empty =>
      rcases hA.1 with ⟨y, hy⟩
      exact ⟨y, hy, by simp⟩
  | @insert k S hk ih =>
      have htailExists : ∀ j ∈ S, ∃ x ∈ A, R j x := by
        intro j hj
        exact hexists j (by simp [hj])
      have htailPersist :
          ∀ j ∈ S, ∀ {x y : X}, R j x → x ≤ y → R j y := by
        intro j hj x y hRx hxy
        exact hpersist j (by simp [hj]) hRx hxy
      rcases ih htailExists htailPersist with ⟨x, hxA, hxR⟩
      rcases hexists k (by simp) with ⟨z, hzA, hzR⟩
      rcases hA.2 hxA hzA with ⟨y, hyA, hxy, hzy⟩
      refine ⟨y, hyA, ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hjS
      · exact hpersist _ (by simp) hzR hzy
      · exact hpersist j (by simp [hjS]) (hxR j hjS) hxy

/-- If `b` is heavy at a directed supremum, then it is already heavy at one
member of the directed family. -/
theorem exists_mem_heavy_of_directedSup
    (hCoord : ProbabilityUpperMassPreservesDirectedSuprema B)
    {A : Set (ProbabilityVector B)} {p : ProbabilityVector B}
    (hA : LocalDirectedSet A) (hp : LocalIsSup A p)
    {b : B} (hb : b ∈ finiteBcHeavySet p) :
    ∃ q ∈ A, b ∈ finiteBcHeavySet q := by
  have hmassSup := hCoord A p hA hp (principalUpperSet b)
  by_contra h
  have hUpper :
      LocalIsUpperBound
        ((fun q : ProbabilityVector B =>
          upperMass q.1 (principalUpperSet b)) '' A)
        (finiteBcThreshold B) := by
    intro z hz
    rcases hz with ⟨q, hqA, rfl⟩
    apply le_of_not_gt
    intro hgt
    exact h ⟨q, hqA, (mem_finiteBcHeavySet q b).2 hgt⟩
  have hle := hmassSup.2 (finiteBcThreshold B) hUpper
  exact (not_le_of_gt ((mem_finiteBcHeavySet p b).1 hb)) hle

/-- Full upper-mass preservation implies the minimal heavy-coordinate
accessibility property. -/
theorem heavyCoordinatesAccessible_of_upperMassPreservesDirectedSuprema
    (hCoord : ProbabilityUpperMassPreservesDirectedSuprema B) :
    FiniteBcHeavyCoordinatesAccessible B := by
  intro A p hA hp b hb
  exact exists_mem_heavy_of_directedSup hCoord hA hp hb

/-- Scott continuity of the threshold selection map.  Finiteness is used to
combine the finitely many heavy-coordinate witnesses into one directed-stage
witness. -/
theorem finiteBcRetraction_scottContinuous_of_heavyAccessibility
    (hBC : IsBoundedCompleteOrder B)
    (hAccess : FiniteBcHeavyCoordinatesAccessible B) :
    AbramskyJung.Chapter2.ScottContinuous (finiteBcRetraction hBC) := by
  refine ⟨finiteBcRetraction_monotone hBC, ?_⟩
  intro A p hA hp
  constructor
  · intro y hy
    rcases hy with ⟨q, hqA, rfl⟩
    exact finiteBcRetraction_monotone hBC (hp.1 hqA)
  · intro y hy
    have hexists :
        ∀ b ∈ finiteBcHeavySet p,
          ∃ q ∈ A, b ∈ finiteBcHeavySet q := by
      intro b hb
      exact hAccess A p hA hp b hb
    have hpersist :
        ∀ b ∈ finiteBcHeavySet p,
          ∀ {q r : ProbabilityVector B},
            b ∈ finiteBcHeavySet q → q ≤ r →
              b ∈ finiteBcHeavySet r := by
      intro b _hb q r hbq hqr
      exact finiteBcHeavySet_mono hqr hbq
    rcases exists_mem_forall_finset_of_directed hA
      (finiteBcHeavySet p)
      (fun b q => b ∈ finiteBcHeavySet q)
      hexists hpersist with ⟨q, hqA, hqHeavy⟩
    calc
      finiteBcRetraction hBC p ≤ finiteBcRetraction hBC q :=
        finiteBcSelectedSup_mono hBC
          (finiteBcHeavySet_hasCommonUpperBound p)
          (finiteBcHeavySet_hasCommonUpperBound q)
          (fun b hb => hqHeavy b hb)
      _ ≤ y := hy ⟨q, hqA, rfl⟩

/-- Source-coordinate form of Scott continuity. -/
theorem finiteBcRetraction_scottContinuous
    (hBC : IsBoundedCompleteOrder B)
    (hCoord : ProbabilityUpperMassPreservesDirectedSuprema B) :
    AbramskyJung.Chapter2.ScottContinuous (finiteBcRetraction hBC) :=
  finiteBcRetraction_scottContinuous_of_heavyAccessibility hBC
    (heavyCoordinatesAccessible_of_upperMassPreservesDirectedSuprema hCoord)

/-- A monotone map out of a finite poset is Scott-continuous: every directed
subset of the finite source contains its supremum. -/
theorem scottContinuous_of_monotone_finiteSource
    {X : Type u} {Y : Type v}
    [Fintype X] [PartialOrder X] [Preorder Y]
    {f : X → Y} (hf : Monotone f) :
    AbramskyJung.Chapter2.ScottContinuous f := by
  refine ⟨hf, ?_⟩
  intro A x hA hx
  obtain ⟨z, hzA, hz⟩ :=
    AbramskyJung.Chapter2.DirectedSet.exists_isSup_of_finite
      hA (Set.toFinite A)
  have hzx : z = x := AbramskyJung.Chapter2.IsSup.unique hz hx
  subst x
  constructor
  · intro y hy
    rcases hy with ⟨a, ha, rfl⟩
    exact hf (hz.1 ha)
  · intro y hy
    exact hy ⟨z, hzA, rfl⟩

/-- The Dirac embedding of a finite poset is Scott-continuous. -/
theorem diracProbability_scottContinuous :
    AbramskyJung.Chapter2.ScottContinuous
      (fun x : B => diracProbability x) := by
  apply scottContinuous_of_monotone_finiteSource
  intro x y hxy
  change dirac x ≤ dirac y
  exact (dirac_le_dirac_iff).2 hxy

/-- The source threshold construction as a genuine continuous
section--retraction pair. -/
noncomputable def finiteBcContinuousRetraction_of_heavyAccessibility
    (hBC : IsBoundedCompleteOrder B)
    (hAccess : FiniteBcHeavyCoordinatesAccessible B) :
    AbramskyJung.Chapter3.ContinuousSectionRetractionPair
      B (ProbabilityVector B) where
  s := fun x => diracProbability x
  r := finiteBcRetraction hBC
  monotone_s := diracProbability_scottContinuous.monotone
  monotone_r := finiteBcRetraction_monotone hBC
  retract := finiteBcRetraction_diracProbability hBC
  continuous_s := diracProbability_scottContinuous
  continuous_r :=
    finiteBcRetraction_scottContinuous_of_heavyAccessibility hBC hAccess

/-- Source-coordinate specialization of the continuous retraction. -/
noncomputable def finiteBcContinuousRetraction
    (hBC : IsBoundedCompleteOrder B)
    (hCoord : ProbabilityUpperMassPreservesDirectedSuprema B) :
    AbramskyJung.Chapter3.ContinuousSectionRetractionPair
      B (ProbabilityVector B) :=
  finiteBcContinuousRetraction_of_heavyAccessibility hBC
    (heavyCoordinatesAccessible_of_upperMassPreservesDirectedSuprema hCoord)

end ScottContinuity

/-! ## Conditional FVA conclusion -/

section FiniteBcFVA

variable {B : Type u} [Fintype B] [PartialOrder B]

/-- The normalized finite probability stage is FVA whenever the standard
continuous-dcpo theorem for finite subprobability stages is supplied and `B`
has a least element.  This is the exact `prop:probability-positive` plus
`lem:generators` step needed by `lem:finite-bc-fva`. -/
theorem probabilityVector_isFVA_of_least
    (hDomains : FiniteStagesAreContinuousDcpos.{u})
    (bot : B) (hbot : ∀ x : B, bot ≤ x) :
    IsFVA.{u, u} (ProbabilityVector B) := by
  let P : FinitePoset.{u} := {
    carrier := WithoutPoint bot
    fintype := Subtype.fintype fun x : B => x ≠ bot
    partialOrder := inferInstance
  }
  let sr := orderIsoContinuousSectionRetractionPair
    (probabilityOrderIso bot hbot)
  exact IsFVA.retract sr (finiteStages_areFVA hDomains P)

/-- Strongest noncircular local form of source item `lem:finite-bc-fva`.

The order assumptions (`bot`, `hbot`, `hBC`) are the finite bc-domain data.
The two finite-valuation semantic inputs are visible: continuous dcpo
structure for finite subprobability stages, and preservation of directed
suprema by the finitely many upper-mass coordinates. -/
theorem finite_bc_isFVA_conditional
    (hDomains : FiniteStagesAreContinuousDcpos.{u})
    (bot : B) (hbot : ∀ x : B, bot ≤ x)
    (hBC : IsBoundedCompleteOrder B)
    (hCoord : ProbabilityUpperMassPreservesDirectedSuprema B) :
    IsFVA.{u, u} B := by
  letI : Nonempty B := ⟨bot⟩
  exact IsFVA.retract
    (finiteBcContinuousRetraction hBC hCoord)
    (probabilityVector_isFVA_of_least hDomains bot hbot)

/-- Minimal-premise version of the finite-bc FVA result.  Only accessibility
of the finitely many threshold coordinates is needed; the full equality of
upper-mass directed suprema is not used. -/
theorem finite_bc_isFVA_of_heavyAccessibility
    (hDomains : FiniteStagesAreContinuousDcpos.{u})
    (bot : B) (hbot : ∀ x : B, bot ≤ x)
    (hBC : IsBoundedCompleteOrder B)
    (hAccess : FiniteBcHeavyCoordinatesAccessible B) :
    IsFVA.{u, u} B := by
  letI : Nonempty B := ⟨bot⟩
  exact IsFVA.retract
    (finiteBcContinuousRetraction_of_heavyAccessibility hBC hAccess)
    (probabilityVector_isFVA_of_least hDomains bot hbot)

end FiniteBcFVA

/-! ## Finite meet-closure stages in the omega-bc argument -/

section FiniteMeetClosureStages

variable {D : Type u} [PartialOrder D]

/-- A selected least point obtained from bounded completeness and
nonemptiness (the supremum of the empty set). -/
noncomputable def boundedCompleteLeast
    [Nonempty D] (hBC : IsBoundedCompleteOrder D) : D :=
  Classical.choose
    (hBC ∅ ⟨Classical.choice (inferInstance : Nonempty D),
      by intro a ha; exact False.elim ha⟩)

theorem boundedCompleteLeast_isLeast
    [Nonempty D] (hBC : IsBoundedCompleteOrder D) :
    ∀ x : D, boundedCompleteLeast hBC ≤ x := by
  intro x
  have hSup : LocalIsSup (∅ : Set D) (boundedCompleteLeast hBC) :=
    Classical.choose_spec
      (hBC ∅ ⟨Classical.choice (inferInstance : Nonempty D),
        by intro a ha; exact False.elim ha⟩)
  exact hSup.2 x (by intro a ha; exact False.elim ha)

variable (C : Finset D)

/-- Corestrict a finite-range map to a specified finite carrier. -/
def finiteRangeCorestrict (g : D → D) (hrange : ∀ x, g x ∈ C) :
    D → FiniteCarrier C :=
  fun x => ⟨g x, hrange x⟩

theorem finiteRangeCorestrict_monotone
    {g : D → D} (hrange : ∀ x, g x ∈ C) (hg : Monotone g) :
    Monotone (finiteRangeCorestrict C g hrange) := by
  intro x y hxy
  exact hg hxy

/-- Corestriction preserves Scott continuity.  No finiteness argument is
needed here: the subtype inclusion reflects order. -/
theorem finiteRangeCorestrict_scottContinuous
    {g : D → D} (hrange : ∀ x, g x ∈ C)
    (hg : AbramskyJung.Chapter2.ScottContinuous g) :
    AbramskyJung.Chapter2.ScottContinuous
      (finiteRangeCorestrict C g hrange) := by
  refine ⟨finiteRangeCorestrict_monotone C hrange hg.monotone, ?_⟩
  intro A x hA hx
  have hgSup := hg.maps_isSup hA hx
  constructor
  · intro y hy
    rcases hy with ⟨a, ha, rfl⟩
    exact hgSup.1 ⟨a, ha, rfl⟩
  · intro y hy
    change g x ≤ y.1
    apply hgSup.2 y.1
    intro z hz
    rcases hz with ⟨a, ha, rfl⟩
    exact hy ⟨a, ha, rfl⟩

/-- Inclusion of a finite subposet is Scott-continuous because every directed
subset of the finite source contains its supremum. -/
theorem finiteCarrier_inclusion_scottContinuous :
    AbramskyJung.Chapter2.ScottContinuous
      (fun x : FiniteCarrier C => x.1) := by
  apply scottContinuous_of_monotone_finiteSource
  intro x y hxy
  exact hxy

/-- A finite-range Scott-continuous map factors through its specified finite
carrier, exactly as in the `C_n` paragraph of `prop:omega-bc-fva`. -/
def finiteRangeScottFactorization
    {g : D → D} (hrange : ∀ x, g x ∈ C)
    (hg : AbramskyJung.Chapter2.ScottContinuous g) :
    AbstractApproximation.ScottFactorization g (FiniteCarrier C) where
  encode := finiteRangeCorestrict C g hrange
  decode := fun x => x.1
  encode_continuous := finiteRangeCorestrict_scottContinuous C hrange hg
  decode_continuous := finiteCarrier_inclusion_scottContinuous C
  factor := fun _ => rfl

/-- An ambient nonempty-infimum-closed finite set is a finite bc-domain and
hence is FVA, conditional only on the two finite-valuation semantic inputs
already exposed by `finite_bc_isFVA_conditional`. -/
theorem finiteCarrier_isFVA_conditional
    (hDomains : FiniteStagesAreContinuousDcpos.{u})
    (hCne : C.Nonempty)
    (hC : ClosedUnderNonemptyFiniteInfima C)
    (hCoord :
      ProbabilityUpperMassPreservesDirectedSuprema (FiniteCarrier C)) :
    IsFVA.{u, u} (FiniteCarrier C) := by
  let hBC : IsBoundedCompleteOrder (FiniteCarrier C) :=
    finiteCarrier_isBoundedCompleteOrder C hCne hC
  letI : Nonempty (FiniteCarrier C) := by
    rcases hCne with ⟨x, hx⟩
    exact ⟨⟨x, hx⟩⟩
  let bot : FiniteCarrier C := boundedCompleteLeast hBC
  exact finite_bc_isFVA_conditional hDomains bot
    (boundedCompleteLeast_isLeast hBC) hBC hCoord

/-- Fully assembled internal finite-stage conclusion used by the omega-bc
proof: a finite-range Scott-continuous map factors through a concrete finite
carrier which is FVA.  The external theorem `BC ⊆ RB`, the extraction of the
maps `g_n`, and saturation part (ii) are deliberately not assumed here. -/
theorem finiteRange_factorsThroughFVA_conditional
    {g : D → D} (hrange : ∀ x, g x ∈ C)
    (hg : AbramskyJung.Chapter2.ScottContinuous g)
    (hDomains : FiniteStagesAreContinuousDcpos.{u})
    (hCne : C.Nonempty)
    (hC : ClosedUnderNonemptyFiniteInfima C)
    (hCoord :
      ProbabilityUpperMassPreservesDirectedSuprema (FiniteCarrier C)) :
    IsFVA.{u, u} (FiniteCarrier C) ∧
      Nonempty (AbstractApproximation.ScottFactorization g (FiniteCarrier C)) :=
  ⟨finiteCarrier_isFVA_conditional C hDomains hCne hC hCoord,
    ⟨finiteRangeScottFactorization C hrange hg⟩⟩

end FiniteMeetClosureStages

end FiniteValuationApproximable
