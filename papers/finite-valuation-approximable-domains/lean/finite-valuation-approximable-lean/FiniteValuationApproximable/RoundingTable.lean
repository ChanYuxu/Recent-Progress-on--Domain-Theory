import FiniteValuationApproximable.Rounding
import FiniteValuationApproximable.Abstract.FVA
import FiniteValuationApproximable.ConeGenerators

/-!
# Finite table carriers for randomized grid rounding

This module supplies the measure-free finite-carrier, support-geometry, and
geometric-scale parts of source items `prop:p-kernel`, `lem:flow-sandwich`,
and `prop:finite-kernels` in `main (17).tex` (source SHA-256
`4b2e65f0f96347bea4df7571e8993ad6e888c0ff7181c1305c5056880365ac94`).

The probability law, Haar-invariant coupling, and null-boundary limit are
kept in `RoundingMeasure.lean`.  No measure-theoretic premise occurs here.
-/

set_option autoImplicit false
set_option linter.unnecessarySimpa false

universe u v w

namespace FiniteValuationApproximable

open scoped Classical BigOperators Topology
open Set Filter

/-! ## The source carrier `Lambda_epsilon` -/

section ScaledTableCarrier

variable {A : Type u} {P : Type v}
variable [Fintype A] [PartialOrder A] [Fintype P] [PartialOrder P]

/-- Flatten the atomic coefficients of a monotone table into the source's
ambient space `R^(A x P)`. -/
def tableCoefficients (x : MonotoneTable A P) : A × P -> Real :=
  fun ap => x ap.1 ap.2

/-- The ambient coefficient realization of `M(A,P)`. -/
def TableCoefficientSet (A : Type u) (P : Type v)
    [Fintype A] [PartialOrder A] [Fintype P] [PartialOrder P] :
    Set (A × P -> Real) :=
  Set.range tableCoefficients

/-- An integer vector is a valid grid point at mesh `h` precisely when its
rescaled atomic coefficient vector is a monotone table. -/
def IsScaledTableGridPoint (h : Real) (l : A × P -> Int) : Prop :=
  h • castIntVector l ∈ TableCoefficientSet A P

/-- The fixed finite carrier `Lambda_h = {l : h l in M(A,P)}`. -/
def ScaledTableGrid (A : Type u) (P : Type v)
    [Fintype A] [PartialOrder A] [Fintype P] [PartialOrder P]
    (h : Real) :=
  {l : A × P -> Int // IsScaledTableGridPoint (A := A) (P := P) h l}

theorem atom_le_one (x : MonotoneTable A P) (a : A) (p : P) :
    x a p <= 1 := by
  calc
    x a p = (x a).mass ({p} : Set P) := by
      simp [SubprobabilityVector.mass]
    _ <= (x a).mass (Set.univ : Set P) :=
      (x a).mass_mono (Set.subset_univ _)
    _ = (x a).totalMass := SubprobabilityVector.mass_univ (x a)
    _ <= 1 := (x a).totalMass_le_one

theorem scaledTableGrid_coordinate_bounds {h : Real} (hh : 0 < h)
    (l : ScaledTableGrid A P h) (ap : A × P) :
    (0 : Int) <= l.1 ap ∧ l.1 ap <= Int.floor (1 / h) := by
  rcases l.2 with ⟨x, hx⟩
  have hcoord := congrFun hx ap
  have hcoord' : x ap.1 ap.2 = h * (l.1 ap : Real) := by
    simpa [tableCoefficients, Pi.smul_apply, smul_eq_mul, castIntVector] using hcoord
  have hx0 : 0 <= x ap.1 ap.2 := (x ap.1).coeff_nonneg ap.2
  have hx1 : x ap.1 ap.2 <= 1 := atom_le_one x ap.1 ap.2
  rw [hcoord'] at hx0 hx1
  have hcast0 : (0 : Real) <= (l.1 ap : Real) := by
    apply nonneg_of_mul_nonneg_left _ hh
    simpa [mul_comm] using hx0
  have hcast1 : (l.1 ap : Real) <= 1 / h := by
    apply (le_div_iff₀ hh).2
    simpa [mul_comm] using hx1
  constructor
  · exact_mod_cast hcast0
  · exact (Int.le_floor).2 hcast1

theorem scaledTableGrid_set_finite {h : Real} (hh : 0 < h) :
    ({l : A × P -> Int | IsScaledTableGridPoint (A := A) (P := P) h l} :
      Set (A × P -> Int)).Finite := by
  let box : A × P -> Set Int := fun _ => Set.Icc 0 (Int.floor (1 / h))
  have hbox : (Set.pi Set.univ box).Finite :=
    Set.Finite.pi fun _ => Set.finite_Icc _ _
  apply hbox.subset
  intro l hl ap hap
  let q : ScaledTableGrid A P h := ⟨l, hl⟩
  exact scaledTableGrid_coordinate_bounds hh q ap

noncomputable instance scaledTableGridFintype (h : Real) [Fact (0 < h)] :
    Fintype (ScaledTableGrid A P h) :=
  (scaledTableGrid_set_finite (A := A) (P := P) (Fact.out : 0 < h)).fintype

/-- Cone-induced order on the fixed integer carrier. -/
instance scaledTableGridLE (h : Real) : LE (ScaledTableGrid A P h) where
  le l m := FlatGridLE l.1 m.1

instance scaledTableGridPartialOrder (h : Real) :
    PartialOrder (ScaledTableGrid A P h) where
  le_refl l := flatGridLE_refl l.1
  le_trans l m n := flatGridLE_trans
  le_antisymm l m hlm hml := Subtype.ext (flatGridLE_antisymm hlm hml)

/-- Recover the unique monotone table represented by a valid scaled grid
point. -/
noncomputable def scaledTableGridEmbedding (h : Real) :
    ScaledTableGrid A P h -> MonotoneTable A P :=
  fun l => Classical.choose l.2

/-- The zero monotone table, used only as the unreachable fallback of the
total finite-carrier encoder outside the valid scaled grid. -/
def zeroMonotoneTable : MonotoneTable A P where
  toFun := fun _ => 0
  monotone' := fun _ _ _ => le_rfl

/-- The zero integer vector is a valid point at every mesh. -/
noncomputable def zeroScaledTableGrid (h : Real) : ScaledTableGrid A P h := by
  refine ⟨0, ?_⟩
  refine ⟨zeroMonotoneTable, ?_⟩
  funext ap
  simp [tableCoefficients, zeroMonotoneTable, castIntVector]

/-- Total encoder into the fixed carrier.  Every actual rounding outcome is
proved valid before this encoder is used, so its fallback branch has zero
probability. -/
noncomputable def scaledTableGridEncode (h : Real) (q : A × P -> Int) :
    ScaledTableGrid A P h :=
  if hq : IsScaledTableGridPoint (A := A) (P := P) h q then ⟨q, hq⟩
  else zeroScaledTableGrid h

@[simp]
theorem scaledTableGridEncode_val_of_mem (h : Real) {q : A × P -> Int}
    (hq : IsScaledTableGridPoint (A := A) (P := P) h q) :
    (scaledTableGridEncode h q).1 = q := by
  simp [scaledTableGridEncode, hq]

theorem scaledTableGridEncode_le_of_mem
    (h : Real) {q r : A × P -> Int}
    (hq : IsScaledTableGridPoint (A := A) (P := P) h q)
    (hr : IsScaledTableGridPoint (A := A) (P := P) h r)
    (hqr : FlatGridLE q r) :
    scaledTableGridEncode h q <= scaledTableGridEncode h r := by
  simpa [scaledTableGridEncode, hq, hr]

theorem scaledTableGridEmbedding_coeff (h : Real)
    (l : ScaledTableGrid A P h) (a : A) (p : P) :
    scaledTableGridEmbedding h l a p = h * (l.1 (a, p) : Real) := by
  have hspec := Classical.choose_spec l.2
  have hap := congrFun hspec (a, p)
  simpa [tableCoefficients, Pi.smul_apply, smul_eq_mul] using hap

theorem scaledTableGridEmbedding_upperCoordinate (h : Real)
    (l : ScaledTableGrid A P h) (a : A) (U : UpperSet P) :
    (scaledTableGridEmbedding h l).upperCoordinate a U =
      h * vectorUpperMass (fun p => (l.1 (a, p) : Real)) U := by
  classical
  unfold MonotoneTable.upperCoordinate upperMass SubprobabilityVector.mass
    vectorUpperMass
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hpU : p ∈ (U : Set P)
  · simp [hpU, scaledTableGridEmbedding_coeff]
  · simp [hpU]

/-- The source grid embedding is monotone for the cone-induced order. -/
theorem scaledTableGridEmbedding_mono {h : Real} (hh : 0 <= h) :
    Monotone (scaledTableGridEmbedding (A := A) (P := P) h) := by
  intro l m hlm a U
  change (scaledTableGridEmbedding h l).upperCoordinate a U <=
    (scaledTableGridEmbedding h m).upperCoordinate a U
  rw [scaledTableGridEmbedding_upperCoordinate,
    scaledTableGridEmbedding_upperCoordinate]
  apply mul_le_mul_of_nonneg_left _ hh
  have hcone := hlm a U
  have hdiff :
      vectorUpperMass
          (fun p => realGridDifference l.1 m.1 (a, p)) U =
        vectorUpperMass (fun p => (m.1 (a, p) : Real)) U -
          vectorUpperMass (fun p => (l.1 (a, p) : Real)) U := by
    classical
    unfold vectorUpperMass realGridDifference
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    by_cases hpU : p ∈ (U : Set P)
    · simp [hpU]
    · simp [hpU]
  rw [hdiff] at hcone
  exact sub_nonneg.mp hcone

/-- Bundle the fixed scaled carrier as the finite poset used by the FVA
factorization. -/
noncomputable def scaledTableGridFinitePoset (h : Real) (hh : 0 < h) :
    FinitePoset.{max u v} where
  carrier := ScaledTableGrid A P h
  fintype := @scaledTableGridFintype A P _ _ _ _ h ⟨hh⟩
  partialOrder := scaledTableGridPartialOrder h

end ScaledTableCarrier

/-! ## Outcome inclusion and deterministic support error -/

section TableRoundingGeometry

variable {A : Type u} {P : Type v}
variable [Fintype A] [PartialOrder A] [Fintype P] [PartialOrder P]

theorem tableCoefficients_mem (x : MonotoneTable A P) :
    tableCoefficients x ∈ TableCoefficientSet A P :=
  ⟨x, rfl⟩

/-- `M(A,P)` is convex in its atomic coefficient realization. -/
theorem tableCoefficientSet_convex :
    Convex Real (TableCoefficientSet A P) := by
  intro _ hx _ hy s t hs ht hst
  rcases hx with ⟨x, rfl⟩
  rcases hy with ⟨y, rfl⟩
  let row : A -> SubprobabilityVector P := fun a =>
    { coeff := fun p => s * x a p + t * y a p
      coeff_nonneg := fun p =>
        add_nonneg (mul_nonneg hs ((x a).coeff_nonneg p))
          (mul_nonneg ht ((y a).coeff_nonneg p))
      total_le_one := by
        change (∑ p, (s * x a p + t * y a p)) <= 1
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        calc
          s * (∑ p, x a p) + t * (∑ p, y a p) <= s * 1 + t * 1 :=
            add_le_add
              (mul_le_mul_of_nonneg_left (x a).total_le_one hs)
              (mul_le_mul_of_nonneg_left (y a).total_le_one ht)
          _ = 1 := by nlinarith }
  have hmass (a : A) (U : UpperSet P) :
      upperMass (row a) U =
        s * upperMass (x a) U + t * upperMass (y a) U := by
    classical
    unfold upperMass SubprobabilityVector.mass
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    by_cases hpU : p ∈ (U : Set P)
    · simp [row, hpU]
    · simp [row, hpU]
  have hrow : Monotone row := by
    intro a b hab U
    rw [hmass a U, hmass b U]
    exact add_le_add
      (mul_le_mul_of_nonneg_left (x.monotone' hab U) hs)
      (mul_le_mul_of_nonneg_left (y.monotone' hab U) ht)
  let z : MonotoneTable A P := ⟨row, hrow⟩
  refine ⟨z, ?_⟩
  funext ap
  simp only [tableCoefficients, z, row, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul]

/-- A positive finite family admits one uniform positive lower bound. -/
theorem exists_uniform_pos_lower_bound
    {I : Type w} [Fintype I] (f : I -> Real) (hf : forall i, 0 < f i) :
    exists delta : Real, 0 < delta ∧ forall i, delta <= f i := by
  classical
  cases isEmpty_or_nonempty I with
  | inl hI =>
      letI := hI
      exact ⟨1, by norm_num, fun i => isEmptyElim i⟩
  | inr hI =>
      letI := hI
      have hs : (Finset.univ.image f).Nonempty := by
        rcases Classical.arbitrary I with i
        exact ⟨f i, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩
      let delta : Real := (Finset.univ.image f).min' hs
      have hmem : delta ∈ Finset.univ.image f := Finset.min'_mem _ _
      have hdelta : 0 < delta := by
        rcases Finset.mem_image.mp hmem with ⟨i, hi, hidelta⟩
        rw [← hidelta]
        exact hf i
      refine ⟨delta, hdelta, ?_⟩
      intro i
      exact Finset.min'_le _ _
        (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)

/-- Reconstruct a monotone table from the finite family of atomic, mass, and
upper-set monotonicity inequalities defining its coefficient polytope. -/
theorem mem_tableCoefficientSet_of_constraints
    (z : A × P -> Real)
    (hatom : forall a p, 0 <= z (a, p))
    (hmass : forall a, (∑ p, z (a, p)) <= 1)
    (hmono : forall ⦃a b : A⦄, a <= b -> forall U : UpperSet P,
      vectorUpperMass (fun p => z (a, p)) U <=
        vectorUpperMass (fun p => z (b, p)) U) :
    z ∈ TableCoefficientSet A P := by
  let row : A -> SubprobabilityVector P := fun a =>
    { coeff := fun p => z (a, p)
      coeff_nonneg := hatom a
      total_le_one := hmass a }
  have hrow : Monotone row := by
    intro a b hab U
    exact hmono hab U
  refine ⟨⟨row, hrow⟩, ?_⟩
  rfl

/-- The explicit strictly feasible table has a genuine sup-norm ball inside
the finite coefficient polytope.  This is the elementary finite-constraint
content of source `lem:interior-point`; no convex-geometry axiom is used. -/
theorem strictFeasibleTable_interior_ball [Nonempty A] [Nonempty P] :
    exists r : Real, 0 < r ∧
      Metric.ball
          (tableCoefficients (strictFeasibleTable : MonotoneTable A P)) r ⊆
        interior (TableCoefficientSet A P) := by
  let u : MonotoneTable A P := strictFeasibleTable
  have hu := strictFeasibleTable_isStrictlyFeasible (A := A) (P := P)
  obtain ⟨deltaAtom, hdeltaAtom, hdeltaAtomLe⟩ :=
    exists_uniform_pos_lower_bound
      (fun ap : A × P => u ap.1 ap.2)
      (fun ap => hu.1 ap.1 ap.2)
  obtain ⟨deltaMass, hdeltaMass, hdeltaMassLe⟩ :=
    exists_uniform_pos_lower_bound
      (fun a : A => 1 - (u a).totalMass)
      (fun a => sub_pos.mpr (hu.2.1 a))
  let MonoConstraint :=
    {t : A × (A × UpperSet P) //
      t.1 < t.2.1 ∧ (t.2.2 : Set P).Nonempty}
  let monoSlack : MonoConstraint -> Real := fun t =>
    u.upperCoordinate t.1.2.1 t.1.2.2 -
      u.upperCoordinate t.1.1 t.1.2.2
  have hmonoSlack (t : MonoConstraint) : 0 < monoSlack t := by
    exact sub_pos.mpr (hu.2.2 t.2.1 t.1.2.2 t.2.2)
  obtain ⟨deltaMono, hdeltaMono, hdeltaMonoLe⟩ :=
    exists_uniform_pos_lower_bound monoSlack hmonoSlack
  let N : Real := Fintype.card P
  let r : Real := min deltaAtom
    (min (deltaMass / (N + 1)) (deltaMono / (2 * N + 1))) / 2
  have hN : 0 < N := by
    dsimp only [N]
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card P)
  have hmassDen : 0 < N + 1 := by linarith
  have hmonoDen : 0 < 2 * N + 1 := by linarith
  have hr : 0 < r := by
    dsimp only [r]
    positivity
  have hrAtom : r < deltaAtom := by
    dsimp only [r]
    have hminpos : 0 < min deltaAtom
        (min (deltaMass / (N + 1)) (deltaMono / (2 * N + 1))) := by
      positivity
    have hle := min_le_left deltaAtom
      (min (deltaMass / (N + 1)) (deltaMono / (2 * N + 1)))
    nlinarith
  have hNrMass : N * r < deltaMass := by
    have hrle : r < deltaMass / (N + 1) := by
      dsimp only [r]
      have hminpos : 0 < min deltaAtom
          (min (deltaMass / (N + 1)) (deltaMono / (2 * N + 1))) := by
        positivity
      have hle : min deltaAtom
          (min (deltaMass / (N + 1)) (deltaMono / (2 * N + 1))) <=
          deltaMass / (N + 1) :=
        le_trans (min_le_right _ _) (min_le_left _ _)
      nlinarith
    have := (lt_div_iff₀ hmassDen).mp hrle
    nlinarith [mul_pos hr hN]
  have hTwoNrMono : 2 * N * r < deltaMono := by
    have hrle : r < deltaMono / (2 * N + 1) := by
      dsimp only [r]
      have hminpos : 0 < min deltaAtom
          (min (deltaMass / (N + 1)) (deltaMono / (2 * N + 1))) := by
        positivity
      have hle : min deltaAtom
          (min (deltaMass / (N + 1)) (deltaMono / (2 * N + 1))) <=
          deltaMono / (2 * N + 1) :=
        le_trans (min_le_right _ _) (min_le_right _ _)
      nlinarith
    have := (lt_div_iff₀ hmonoDen).mp hrle
    nlinarith [mul_pos hr hN]
  refine ⟨r, hr, ?_⟩
  have hballSet : Metric.ball (tableCoefficients u) r ⊆
      TableCoefficientSet A P := by
    intro z hz
    have hnorm : ‖z - tableCoefficients u‖ < r := by
      simpa [Metric.mem_ball, dist_eq_norm] using hz
    have hperturb (a : A) (p : P) :
        |z (a, p) - u a p| < r := by
      have happ := norm_le_pi_norm (z - tableCoefficients u) (a, p)
      have happ' : ‖(z - tableCoefficients u) (a, p)‖ < r :=
        happ.trans_lt hnorm
      simpa [tableCoefficients, Real.norm_eq_abs] using happ'
    apply mem_tableCoefficientSet_of_constraints z
    · intro a p
      have hlower := (neg_lt_of_abs_lt (hperturb a p))
      have huLower := hdeltaAtomLe (a, p)
      linarith
    · intro a
      have hterm (p : P) : z (a, p) <= u a p + r := by
        linarith [lt_of_abs_lt (hperturb a p)]
      calc
        (∑ p, z (a, p)) <= ∑ p, (u a p + r) :=
          Finset.sum_le_sum fun p hp => hterm p
        _ = (u a).totalMass + N * r := by
          simp only [Finset.sum_add_distrib, SubprobabilityVector.totalMass,
            Finset.sum_const, Finset.card_univ, nsmul_eq_mul, N]
        _ <= 1 := by
          have hslack := hdeltaMassLe a
          linarith
    · intro a b hab U
      rcases hab.lt_or_eq with hablt | rfl
      · by_cases hUnonempty : (U : Set P).Nonempty
        · let t : MonoConstraint := ⟨(a, (b, U)), hablt, hUnonempty⟩
          have hslack := hdeltaMonoLe t
          have hlower (p : P) : u b p - r <= z (b, p) := by
            linarith [neg_lt_of_abs_lt (hperturb b p)]
          have hupper (p : P) : z (a, p) <= u a p + r := by
            linarith [lt_of_abs_lt (hperturb a p)]
          have hbmass :
              u.upperCoordinate b U - N * r <=
                vectorUpperMass (fun p => z (b, p)) U := by
            unfold MonotoneTable.upperCoordinate upperMass
              SubprobabilityVector.mass vectorUpperMass
            calc
              (∑ p, if p ∈ (U : Set P) then u b p else 0) - N * r <=
                  ∑ p, ((if p ∈ (U : Set P) then u b p else 0) - r) := by
                rw [Finset.sum_sub_distrib]
                simp [N]
              _ <= ∑ p, if p ∈ (U : Set P) then z (b, p) else 0 := by
                apply Finset.sum_le_sum
                intro p hp
                by_cases hpU : p ∈ (U : Set P)
                · simp [hpU, hlower p]
                · simp [hpU, hr.le]
          have hamass :
              vectorUpperMass (fun p => z (a, p)) U <=
                u.upperCoordinate a U + N * r := by
            unfold MonotoneTable.upperCoordinate upperMass
              SubprobabilityVector.mass vectorUpperMass
            calc
              (∑ p, if p ∈ (U : Set P) then z (a, p) else 0) <=
                  ∑ p, ((if p ∈ (U : Set P) then u a p else 0) + r) := by
                apply Finset.sum_le_sum
                intro p hp
                by_cases hpU : p ∈ (U : Set P)
                · simp [hpU, hupper p]
                · simp [hpU, hr.le]
              _ = (∑ p, if p ∈ (U : Set P) then u a p else 0) + N * r := by
                rw [Finset.sum_add_distrib]
                simp [N]
          dsimp only [monoSlack, t] at hslack
          linarith
        · have hUempty : (U : Set P) = ∅ := Set.not_nonempty_iff_eq_empty.mp hUnonempty
          simp [vectorUpperMass, hUempty]
      · exact le_rfl
  intro z hz
  exact mem_interior.2
    ⟨Metric.ball (tableCoefficients u) r, hballSet,
      Metric.isOpen_ball, hz⟩

/-- The affine inward displacement in ambient atomic coordinates. -/
def affineTableCoefficients (epsilon : Real)
    (x u : MonotoneTable A P) : A × P -> Real :=
  (1 - epsilon) • tableCoefficients x + epsilon • tableCoefficients u

/-- A deterministic rounding outcome belongs to the fixed source carrier.
The hypotheses are exactly the compact-zonotope radius bound and the interior
ball chosen before `prop:p-kernel`; the conclusion contains no probability or
continuity premise. -/
theorem roundingOutcome_isScaledTableGridPoint
    {J : Type w} [Fintype J]
    (x u : MonotoneTable A P)
    {epsilon c r R : Real}
    (hepsilon : 0 < epsilon) (hepsilon1 : epsilon <= 1)
    (hc : 0 < c) (hR : 0 <= R) (hcr : c * R < r)
    (hball : Metric.ball (tableCoefficients u) r ⊆
      interior (TableCoefficientSet A P))
    (xi : J -> A × P -> Int)
    (hzonotopeNorm : forall q, InRoundingZonotope xi q -> ‖q‖ <= R)
    {l : A × P -> Int}
    (hl : l ∈ RoundingOutcomeSet
      (divideVector (affineTableCoefficients epsilon x u) (c * epsilon)) xi) :
    IsScaledTableGridPoint (A := A) (P := P) (c * epsilon) l := by
  let h : Real := c * epsilon
  let z : A × P -> Real := affineTableCoefficients epsilon x u
  let q : A × P -> Real := divideVector z h - castIntVector l
  have hh : 0 < h := mul_pos hc hepsilon
  have hqzone : InRoundingZonotope xi q := by
    exact outcome_mem_zonotope hl
  have hqnorm : ‖q‖ <= R := hzonotopeNorm q hqzone
  have hvnorm : ‖(-h) • q‖ < epsilon * r := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_neg (neg_neg_of_pos hh)]
    have hnonnegNorm : 0 <= ‖q‖ := norm_nonneg q
    calc
      -(-h) * ‖q‖ = h * ‖q‖ := by ring
      _ <= h * R := mul_le_mul_of_nonneg_left hqnorm hh.le
      _ = epsilon * (c * R) := by simp only [h]; ring
      _ < epsilon * r := mul_lt_mul_of_pos_left hcr hepsilon
  have hin := affine_interior tableCoefficientSet_convex
    (tableCoefficients_mem x) hepsilon hepsilon1 hball hvnorm
  have hinSet :
      (1 - epsilon) • tableCoefficients x + epsilon • tableCoefficients u +
          (-h) • q ∈ TableCoefficientSet A P :=
    interior_subset hin
  have hdiff :
      scaledGridDifference z h l = h • q := by
    exact scaledGridDifference_eq_smul hh.ne' l
  have heq :
      h • castIntVector l =
        (1 - epsilon) • tableCoefficients x + epsilon • tableCoefficients u +
          (-h) • q := by
    have hz : z =
        (1 - epsilon) • tableCoefficients x + epsilon • tableCoefficients u := rfl
    rw [← hz]
    funext ap
    have hd := congrFun hdiff ap
    simp only [scaledGridDifference, Pi.sub_apply, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul] at hd ⊢
    linarith
  change h • castIntVector l ∈ TableCoefficientSet A P
  rw [heq]
  exact hinSet

/-- Package one deterministic randomized-floor outcome in the fixed carrier. -/
noncomputable def scaledTableRoundingOutcome
    {J : Type w} [Fintype J]
    (x u : MonotoneTable A P)
    {epsilon c r R : Real}
    (hepsilon : 0 < epsilon) (hepsilon1 : epsilon <= 1)
    (hc : 0 < c) (hR : 0 <= R) (hcr : c * R < r)
    (hball : Metric.ball (tableCoefficients u) r ⊆
      interior (TableCoefficientSet A P))
    (xi : J -> A × P -> Int)
    (hzonotopeNorm : forall q, InRoundingZonotope xi q -> ‖q‖ <= R)
    (uInput : A × P -> Real) (sInput : J -> Real)
    (huInput : InUnitCube uInput) (hsInput : InUnitCube sInput) :
    ScaledTableGrid A P (c * epsilon) := by
  let l := randomizedFloor
    (divideVector (affineTableCoefficients epsilon x u) (c * epsilon))
    uInput sInput xi
  exact ⟨l, roundingOutcome_isScaledTableGridPoint x u hepsilon hepsilon1
    hc hR hcr hball xi hzonotopeNorm
      ⟨uInput, sInput, huInput, hsInput, rfl⟩⟩

@[simp]
theorem scaledTableRoundingOutcome_val
    {J : Type w} [Fintype J]
    (x u : MonotoneTable A P)
    {epsilon c r R : Real}
    (hepsilon : 0 < epsilon) (hepsilon1 : epsilon <= 1)
    (hc : 0 < c) (hR : 0 <= R) (hcr : c * R < r)
    (hball : Metric.ball (tableCoefficients u) r ⊆
      interior (TableCoefficientSet A P))
    (xi : J -> A × P -> Int)
    (hzonotopeNorm : forall q, InRoundingZonotope xi q -> ‖q‖ <= R)
    (uInput : A × P -> Real) (sInput : J -> Real)
    (huInput : InUnitCube uInput) (hsInput : InUnitCube sInput) :
    (scaledTableRoundingOutcome x u hepsilon hepsilon1 hc hR hcr hball xi
      hzonotopeNorm uInput sInput huInput hsInput).1 =
      randomizedFloor
        (divideVector (affineTableCoefficients epsilon x u) (c * epsilon))
        uInput sInput xi :=
  rfl

theorem vectorUpperMass_affineTableCoefficients
    (epsilon : Real) (x u : MonotoneTable A P) (a : A) (U : UpperSet P) :
    vectorUpperMass
        (fun p => affineTableCoefficients epsilon x u (a, p)) U =
      (1 - epsilon) * x.upperCoordinate a U +
        epsilon * u.upperCoordinate a U := by
  classical
  unfold affineTableCoefficients tableCoefficients
    MonotoneTable.upperCoordinate upperMass SubprobabilityVector.mass
    vectorUpperMass
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hpU : p ∈ (U : Set P)
  · simp [hpU]
  · simp [hpU]

/-- Exact upper-coordinate form of the deterministic support identity
`z - h l = h q`. -/
theorem scaledTableGridEmbedding_upperCoordinate_of_difference
    {h : Real} (hh : h ≠ 0) (z : A × P -> Real)
    (l : ScaledTableGrid A P h) (a : A) (U : UpperSet P) :
    (scaledTableGridEmbedding h l).upperCoordinate a U =
      vectorUpperMass (fun p => z (a, p)) U -
        h * vectorUpperMass
          (fun p => (divideVector z h - castIntVector l.1) (a, p)) U := by
  classical
  let q : A × P -> Real := divideVector z h - castIntVector l.1
  have hdiff : scaledGridDifference z h l.1 = h • q :=
    scaledGridDifference_eq_smul hh l.1
  rw [scaledTableGridEmbedding_upperCoordinate]
  unfold vectorUpperMass
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  have hd := congrFun hdiff (a, p)
  simp only [scaledGridDifference, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    castIntVector, q] at hd
  by_cases hpU : p ∈ (U : Set P)
  · simp [hpU, q, castIntVector]
    linarith
  · simp [hpU, q, castIntVector]

/-- Deterministic positive-support estimate behind `lem:flow-sandwich`.
Once a grid label decodes to an actual rounding outcome, its upper-set
coordinates differ from the input by at most the manuscript's raw errors.
There is no measure or continuity premise in this result. -/
theorem scaledTableGridEmbedding_coordinate_errors_of_outcome
    {J : Type w} [Fintype J]
    (x u : MonotoneTable A P)
    {epsilon c R : Real}
    (hepsilon : 0 < epsilon) (hc : 0 < c) (hR : 0 <= R)
    (xi : J -> A × P -> Int)
    (hxi : forall j,
      castIntDirection (xi j) ∈ FlatTableOrderCone A P)
    (hzonotopeUpper : forall q, InRoundingZonotope xi q -> forall a U,
      vectorUpperMass (fun p => q (a, p)) U <= R)
    (l : ScaledTableGrid A P (c * epsilon))
    (hl : l.1 ∈ RoundingOutcomeSet
      (divideVector (affineTableCoefficients epsilon x u) (c * epsilon)) xi) :
    forall a U,
      x.upperCoordinate a U - (epsilon + c * epsilon * R) <=
          (scaledTableGridEmbedding (c * epsilon) l).upperCoordinate a U ∧
        (scaledTableGridEmbedding (c * epsilon) l).upperCoordinate a U <=
          x.upperCoordinate a U + epsilon := by
  intro a U
  let z : A × P -> Real := affineTableCoefficients epsilon x u
  let h : Real := c * epsilon
  let q : A × P -> Real := divideVector z h - castIntVector l.1
  have hqzone : InRoundingZonotope xi q := outcome_mem_zonotope hl
  have hqcone : q ∈ FlatTableOrderCone A P :=
    roundingZonotope_mem_flatTableOrderCone hxi hqzone
  have hq0 : 0 <= vectorUpperMass (fun p => q (a, p)) U := hqcone a U
  have hqR : vectorUpperMass (fun p => q (a, p)) U <= R :=
    hzonotopeUpper q hqzone a U
  have hx0 : 0 <= x.upperCoordinate a U := (x a).mass_nonneg U
  have hu0 : 0 <= u.upperCoordinate a U := (u a).mass_nonneg U
  have hx1 : x.upperCoordinate a U <= 1 := by
    exact le_trans ((x a).mass_mono (Set.subset_univ (U : Set P)))
      (by simpa using (x a).totalMass_le_one)
  have hu1 : u.upperCoordinate a U <= 1 := by
    exact le_trans ((u a).mass_mono (Set.subset_univ (U : Set P)))
      (by simpa using (u a).totalMass_le_one)
  have hhpos : 0 < h := mul_pos hc hepsilon
  have hh0 : 0 <= h := hhpos.le
  have hgrid := scaledTableGridEmbedding_upperCoordinate_of_difference
    hhpos.ne' z l a U
  have hzcoord := vectorUpperMass_affineTableCoefficients epsilon x u a U
  change (scaledTableGridEmbedding h l).upperCoordinate a U = _ at hgrid
  change vectorUpperMass (fun p => z (a, p)) U = _ at hzcoord
  have hgridEq :
      (scaledTableGridEmbedding h l).upperCoordinate a U =
        (1 - epsilon) * x.upperCoordinate a U +
          epsilon * u.upperCoordinate a U -
            h * vectorUpperMass (fun p => q (a, p)) U := by
    rw [hgrid, hzcoord]
  have hqmul := mul_le_mul_of_nonneg_left hqR hh0
  have hepsx : 0 <= epsilon * x.upperCoordinate a U :=
    mul_nonneg hepsilon.le hx0
  have hepsu : epsilon * u.upperCoordinate a U <= epsilon := by
    nlinarith [mul_le_mul_of_nonneg_left hu1 hepsilon.le]
  have hepsxle : epsilon * x.upperCoordinate a U <= epsilon := by
    nlinarith [mul_le_mul_of_nonneg_left hx1 hepsilon.le]
  have hhq0 : 0 <= h * vectorUpperMass (fun p => q (a, p)) U :=
    mul_nonneg hh0 hq0
  change
    x.upperCoordinate a U - (epsilon + h * R) <=
        (scaledTableGridEmbedding h l).upperCoordinate a U ∧
      (scaledTableGridEmbedding h l).upperCoordinate a U <=
        x.upperCoordinate a U + epsilon
  constructor <;> nlinarith

end TableRoundingGeometry

/-! ## Fixed transfer directions and exact cone coordinates -/

section ConeCoordinates

variable {A : Type u} {P : Type v}
variable [Fintype A] [PartialOrder A] [Fintype P] [PartialOrder P]

/-- All strict transfer directions; the conic decomposition only assigns
nonzero coefficients to covers, but this fixed finite superfamily is more
convenient for the probability space. -/
def StrictTransferIndex (P : Type v) [Fintype P] [PartialOrder P] :=
  {pq : P × P // pq.1 < pq.2}

noncomputable instance strictTransferIndexFintype :
    Fintype (StrictTransferIndex P) :=
  Fintype.ofInjective
    (fun j : StrictTransferIndex P => j.1) Subtype.val_injective

noncomputable def strictTransferDirection
    (j : StrictTransferIndex P) : P -> Real :=
  transferDirection j.1.1 j.1.2

theorem upperOrderCone_exists_strictTransferCoordinates
    {z : P -> Real} (hz : z ∈ UpperOrderCone P) :
    exists alpha : P -> Real, exists beta : StrictTransferIndex P -> Real,
      (forall p, 0 <= alpha p) ∧ (forall j, 0 <= beta j) ∧
        forall p, z p = alpha p +
          ∑ j, beta j * strictTransferDirection j p := by
  classical
  have hhull := upperOrderCone_subset_conicHull hz
  clear hz
  induction hhull with
  | zero =>
      refine ⟨0, 0, ?_, ?_, ?_⟩
      · simp
      · simp
      · intro p
        simp
  | @generator g hg =>
      rcases hg with ⟨p, rfl⟩ | ⟨p, q, hpq, rfl⟩
      · refine ⟨standardBasis p, 0, ?_, ?_, ?_⟩
        · intro r
          by_cases hrp : r = p <;> simp [standardBasis, hrp]
        · simp
        · intro r
          simp
      · let j0 : StrictTransferIndex P := ⟨(p, q), hpq.1⟩
        refine ⟨0, (fun j => if j = j0 then 1 else 0), ?_, ?_, ?_⟩
        · simp
        · intro j
          by_cases hj : j = j0 <;> simp [hj]
        · intro r
          simp [j0, strictTransferDirection]
  | @add z w _ _ ihz ihw =>
      rcases ihz with ⟨alphaZ, betaZ, haZ, hbZ, hZ⟩
      rcases ihw with ⟨alphaW, betaW, haW, hbW, hW⟩
      refine ⟨alphaZ + alphaW, betaZ + betaW, ?_, ?_, ?_⟩
      · intro p
        exact add_nonneg (haZ p) (haW p)
      · intro j
        exact add_nonneg (hbZ j) (hbW j)
      · intro p
        rw [Pi.add_apply, hZ p, hW p]
        simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
        ring
  | @nonneg_smul c z hc _ ih =>
      rcases ih with ⟨alpha, beta, ha, hb, hzEq⟩
      refine ⟨c • alpha, c • beta, ?_, ?_, ?_⟩
      · intro p
        exact mul_nonneg hc (ha p)
      · intro j
        exact mul_nonneg hc (hb j)
      · intro p
        rw [Pi.smul_apply, smul_eq_mul, hzEq p]
        simp only [Pi.smul_apply, smul_eq_mul, mul_add]
        have hsum :
            (∑ j, c * beta j * strictTransferDirection j p) =
              c * ∑ j, beta j * strictTransferDirection j p := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          ring
        rw [hsum]

/-- Row-tagged transfer indices for the product cone `C_P^A`. -/
abbrev FlatStrictTransferIndex (A : Type u) (P : Type v)
    [Fintype P] [PartialOrder P] :=
  A × StrictTransferIndex P

/-- The fixed integral row transfer used by randomized rounding. -/
noncomputable def flatStrictTransferDirection
    (j : FlatStrictTransferIndex A P) : A × P -> Int :=
  flatTransferDirection j.1 j.2.1.1 j.2.1.2

theorem cast_flatStrictTransferDirection_mem_cone
    (j : FlatStrictTransferIndex A P) :
    castIntDirection (flatStrictTransferDirection j) ∈
      FlatTableOrderCone A P := by
  exact cast_flatTransferDirection_mem_flatTableOrderCone j.1 j.2.2.le

/-- Exact fixed-family decomposition of every element of the flattened table
order cone. -/
theorem flatTableOrderCone_exists_coordinates
    {z : A × P -> Real} (hz : z ∈ FlatTableOrderCone A P) :
    exists alpha : A × P -> Real,
      exists beta : FlatStrictTransferIndex A P -> Real,
        (forall i, 0 <= alpha i) ∧ (forall j, 0 <= beta j) ∧
          forall i, z i = alpha i +
            ∑ j, beta j *
              (flatStrictTransferDirection j i : Real) := by
  classical
  have hrow (a : A) :=
    upperOrderCone_exists_strictTransferCoordinates (hz a)
  choose alphaRow betaRow hAlpha hBeta hEq using hrow
  let alpha : A × P -> Real := fun i => alphaRow i.1 i.2
  let beta : FlatStrictTransferIndex A P -> Real :=
    fun j => betaRow j.1 j.2
  refine ⟨alpha, beta, ?_, ?_, ?_⟩
  · intro i
    exact hAlpha i.1 i.2
  · intro j
    exact hBeta j.1 j.2
  · rintro ⟨a, p⟩
    rw [hEq a p]
    congr 1
    rw [Fintype.sum_prod_type]
    simp only [beta, flatStrictTransferDirection, flatTransferDirection,
      intCoordinateBasis, Pi.sub_apply, Int.cast_sub, Int.cast_ite,
      Int.cast_one, Int.cast_zero]
    rw [Finset.sum_eq_single a]
    · apply Finset.sum_congr rfl
      intro j hj
      simp [strictTransferDirection, transferDirection, standardBasis]
    · intro b hb hba
      have hne : a ≠ b := fun hab => hba hab.symm
      simp [hne]
    · simp

end ConeCoordinates

/-! ## Explicit uniform bounds for the rounding zonotope -/

section ZonotopeBounds

variable {I : Type u} {J : Type v}
variable [Fintype I] [Fintype J]

/-- A simple nonnegative bound, deliberately larger than the exact max, for
both the sup norm and all later finite upper-set sums. -/
noncomputable def roundingZonotopeBound (xi : J -> I -> Int) : Real :=
  (Fintype.card I + 1) * (2 + ∑ i, directionRadius xi i)

theorem roundingZonotopeBound_pos (xi : J -> I -> Int) :
    0 < roundingZonotopeBound xi := by
  unfold roundingZonotopeBound
  have hsum : 0 <= ∑ i, directionRadius xi i :=
    Finset.sum_nonneg fun i hi => directionRadius_nonneg xi i
  have hcard : (0 : Real) < Fintype.card I + 1 := by positivity
  nlinarith

theorem abs_roundingShiftSum_le_of_closedCube
    {s : J -> Real} (hs : InClosedUnitCube s)
    (xi : J -> I -> Int) (i : I) :
    |roundingShiftSum s xi i| <= directionRadius xi i := by
  calc
    |roundingShiftSum s xi i| <= ∑ j, |s j * (xi j i : Real)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ <= ∑ j, |(xi j i : Real)| := by
      apply Finset.sum_le_sum
      intro j hj
      rw [abs_mul, abs_of_nonneg (hs j).1]
      simpa using mul_le_mul_of_nonneg_right (hs j).2 (abs_nonneg _)
    _ = directionRadius xi i := rfl

theorem roundingZonotope_norm_le_bound
    (xi : J -> I -> Int) {q : I -> Real}
    (hq : InRoundingZonotope xi q) :
    ‖q‖ <= roundingZonotopeBound xi := by
  rcases hq with ⟨u, theta, hu, htheta, t, ht, hq⟩
  have hcoord (i : I) : |q i| <= 2 + directionRadius xi i := by
    rw [hq i]
    calc
      |u i + theta i + ∑ j, t j * (xi j i : Real)| <=
          |u i| + |theta i| + |∑ j, t j * (xi j i : Real)| := by
        exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ <= 1 + 1 + directionRadius xi i := by
        gcongr
        · simpa [abs_of_nonneg (hu i).1] using (hu i).2
        · simpa [abs_of_nonneg (htheta i).1] using (htheta i).2
        · exact abs_roundingShiftSum_le_of_closedCube ht xi i
      _ = 2 + directionRadius xi i := by ring
  have hsmall (i : I) :
      2 + directionRadius xi i <= roundingZonotopeBound xi := by
    unfold roundingZonotopeBound
    have hdir : directionRadius xi i <= ∑ k, directionRadius xi k :=
      Finset.single_le_sum (fun k hk => directionRadius_nonneg xi k)
        (Finset.mem_univ i)
    have hsum : 0 <= ∑ k, directionRadius xi k :=
      Finset.sum_nonneg fun k hk => directionRadius_nonneg xi k
    have hbase : 0 <= 2 + ∑ k, directionRadius xi k := by linarith
    calc
      2 + directionRadius xi i <= 2 + ∑ k, directionRadius xi k := by linarith
      _ <= (Fintype.card I + 1 : Real) *
          (2 + ∑ k, directionRadius xi k) := by
        have hcard0 : (0 : Real) <= Fintype.card I := by positivity
        have hcard : (1 : Real) <= Fintype.card I + 1 := by linarith
        nlinarith
  apply (pi_norm_le_iff_of_nonneg (roundingZonotopeBound_pos xi).le).2
  intro i
  simpa [Real.norm_eq_abs] using (hcoord i).trans (hsmall i)

end ZonotopeBounds

/-! ## Canonical finite-table rounding geometry -/

section CanonicalTableGeometry

variable {A : Type u} {P : Type v}
variable [Fintype A] [PartialOrder A] [Fintype P] [PartialOrder P]
variable [Nonempty A] [Nonempty P]

/-- A chosen explicit interior radius supplied by the finite-constraint proof
above. -/
noncomputable def tableInteriorRadius : Real :=
  Classical.choose (strictFeasibleTable_interior_ball (A := A) (P := P))

theorem tableInteriorRadius_pos : 0 < tableInteriorRadius (A := A) (P := P) :=
  (Classical.choose_spec
    (strictFeasibleTable_interior_ball (A := A) (P := P))).1

theorem tableInteriorRadius_ball :
    Metric.ball
        (tableCoefficients
          (strictFeasibleTable : MonotoneTable A P))
        (tableInteriorRadius (A := A) (P := P)) ⊆
      interior (TableCoefficientSet A P) :=
  (Classical.choose_spec
    (strictFeasibleTable_interior_ball (A := A) (P := P))).2

/-- Fixed integral transfer family for `C_P^A`. -/
noncomputable def tableRoundingDirections :
    FlatStrictTransferIndex A P -> A × P -> Int :=
  flatStrictTransferDirection

/-- One bound large enough both for the zonotope sup norm and for every
row upper-set coordinate. -/
noncomputable def tableRoundingBound : Real :=
  (Fintype.card P + 1) *
    roundingZonotopeBound (tableRoundingDirections (A := A) (P := P))

theorem tableRoundingBound_pos : 0 < tableRoundingBound (A := A) (P := P) := by
  unfold tableRoundingBound
  exact mul_pos (by positivity)
    (roundingZonotopeBound_pos (tableRoundingDirections (A := A) (P := P)))

theorem tableRoundingZonotope_norm_le
    {q : A × P -> Real}
    (hq : InRoundingZonotope
      (tableRoundingDirections (A := A) (P := P)) q) :
    ‖q‖ <= tableRoundingBound (A := A) (P := P) := by
  have hbase := roundingZonotope_norm_le_bound
    (tableRoundingDirections (A := A) (P := P)) hq
  have hcard : (0 : Real) <= Fintype.card P := Nat.cast_nonneg _
  have hfactor : (1 : Real) <= Fintype.card P + 1 := by linarith
  have hbase0 :=
    (roundingZonotopeBound_pos
      (tableRoundingDirections (A := A) (P := P))).le
  unfold tableRoundingBound
  exact hbase.trans (by nlinarith)

theorem tableRoundingZonotope_upperMass_le
    {q : A × P -> Real}
    (hq : InRoundingZonotope
      (tableRoundingDirections (A := A) (P := P)) q)
    (a : A) (U : UpperSet P) :
    vectorUpperMass (fun p => q (a, p)) U <=
      tableRoundingBound (A := A) (P := P) := by
  let B := roundingZonotopeBound
    (tableRoundingDirections (A := A) (P := P))
  have hnorm := roundingZonotope_norm_le_bound
    (tableRoundingDirections (A := A) (P := P)) hq
  have hcoord (p : P) : q (a, p) <= B := by
    have habs : |q (a, p)| <= ‖q‖ := by
      simpa [Real.norm_eq_abs] using norm_le_pi_norm q (a, p)
    exact (le_abs_self _).trans (habs.trans hnorm)
  unfold vectorUpperMass
  calc
    (∑ p, if p ∈ (U : Set P) then q (a, p) else 0) <= ∑ _p : P, B := by
      apply Finset.sum_le_sum
      intro p hp
      by_cases hpU : p ∈ (U : Set P)
      · simp only [if_pos hpU]
        exact hcoord p
      · simp only [if_neg hpU]
        exact (roundingZonotopeBound_pos
          (tableRoundingDirections (A := A) (P := P))).le
    _ = (Fintype.card P : Real) * B := by simp
    _ <= tableRoundingBound (A := A) (P := P) := by
      unfold tableRoundingBound
      dsimp only [B]
      have hB := roundingZonotopeBound_pos
        (tableRoundingDirections (A := A) (P := P))
      nlinarith

/-- A concrete mesh coefficient satisfying `c R < r`. -/
noncomputable def tableMeshCoefficient : Real :=
  tableInteriorRadius (A := A) (P := P) /
    (2 * (tableRoundingBound (A := A) (P := P) + 1))

theorem tableMeshCoefficient_pos :
    0 < tableMeshCoefficient (A := A) (P := P) := by
  have hr := tableInteriorRadius_pos (A := A) (P := P)
  have hR := tableRoundingBound_pos (A := A) (P := P)
  unfold tableMeshCoefficient
  exact div_pos hr (mul_pos (by norm_num) (by linarith))

theorem tableMeshCoefficient_mul_bound_lt_radius :
    tableMeshCoefficient (A := A) (P := P) *
        tableRoundingBound (A := A) (P := P) <
      tableInteriorRadius (A := A) (P := P) := by
  have hr := tableInteriorRadius_pos (A := A) (P := P)
  have hR := tableRoundingBound_pos (A := A) (P := P)
  unfold tableMeshCoefficient
  have hden :
      0 < 2 * (tableRoundingBound (A := A) (P := P) + 1) := by
    positivity
  have hcoef :
      0 < tableInteriorRadius (A := A) (P := P) /
        (2 * (tableRoundingBound (A := A) (P := P) + 1)) :=
    div_pos hr hden
  have hlt :
      tableRoundingBound (A := A) (P := P) <
        2 * (tableRoundingBound (A := A) (P := P) + 1) := by
    nlinarith
  calc
    tableInteriorRadius (A := A) (P := P) /
          (2 * (tableRoundingBound (A := A) (P := P) + 1)) *
        tableRoundingBound (A := A) (P := P) <
      tableInteriorRadius (A := A) (P := P) /
          (2 * (tableRoundingBound (A := A) (P := P) + 1)) *
        (2 * (tableRoundingBound (A := A) (P := P) + 1)) :=
      mul_lt_mul_of_pos_left hlt hcoef
    _ = tableInteriorRadius (A := A) (P := P) := by
      field_simp

end CanonicalTableGeometry

/-! ## The manuscript's geometric epsilon scales -/

section GeometricScales

/-- `epsilon_n = epsilon_0 theta^n`. -/
def geometricEpsilon (epsilon0 theta : Real) (n : Nat) : Real :=
  epsilon0 * theta ^ n

/-- The source mesh `h_n = c epsilon_n`. -/
def geometricMesh (epsilon0 theta c : Real) (n : Nat) : Real :=
  c * geometricEpsilon epsilon0 theta n

/-- The extra label erosion time `2 epsilon_n`. -/
def geometricLabelTime (epsilon0 theta : Real) (n : Nat) : Real :=
  2 * geometricEpsilon epsilon0 theta n

/-- `alpha_n = epsilon_n / K_P`. -/
noncomputable def geometricAlpha (epsilon0 theta K : Real) (n : Nat) : Real :=
  geometricEpsilon epsilon0 theta n / K

/-- The source constant `C_* = 1 + 2 K_P + c R_(A,P)`. -/
def geometricScaleConstant (K c R : Real) : Real :=
  1 + 2 * K + c * R

/-- `beta_n = C_* epsilon_n`. -/
def geometricBeta (epsilon0 theta K c R : Real) (n : Nat) : Real :=
  geometricScaleConstant K c R * geometricEpsilon epsilon0 theta n

/-- The raw lower coordinate error `epsilon_n + c epsilon_n R`. -/
def geometricLowerError (epsilon0 theta c R : Real) (n : Nat) : Real :=
  geometricEpsilon epsilon0 theta n +
    c * geometricEpsilon epsilon0 theta n * R

/-- The raw upper coordinate error `epsilon_n`. -/
def geometricUpperError (epsilon0 theta : Real) (n : Nat) : Real :=
  geometricEpsilon epsilon0 theta n

theorem geometricEpsilon_pos {epsilon0 theta : Real}
    (hepsilon0 : 0 < epsilon0) (htheta : 0 < theta) (n : Nat) :
    0 < geometricEpsilon epsilon0 theta n := by
  exact mul_pos hepsilon0 (pow_pos htheta n)

theorem geometricEpsilon_nonneg {epsilon0 theta : Real}
    (hepsilon0 : 0 <= epsilon0) (htheta : 0 <= theta) (n : Nat) :
    0 <= geometricEpsilon epsilon0 theta n := by
  exact mul_nonneg hepsilon0 (pow_nonneg htheta n)

theorem geometricEpsilon_succ (epsilon0 theta : Real) (n : Nat) :
    geometricEpsilon epsilon0 theta (n + 1) =
      theta * geometricEpsilon epsilon0 theta n := by
  simp only [geometricEpsilon, pow_succ]
  ring

theorem geometricEpsilon_tendsto_zero {epsilon0 theta : Real}
    (htheta0 : 0 <= theta) (htheta1 : theta < 1) :
    Tendsto (geometricEpsilon epsilon0 theta) atTop (nhds 0) := by
  have hpow : Tendsto (fun n : Nat => theta ^ n) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one htheta0 htheta1
  simpa [geometricEpsilon] using tendsto_const_nhds.mul hpow

theorem geometricMesh_pos {epsilon0 theta c : Real}
    (hepsilon0 : 0 < epsilon0) (htheta : 0 < theta) (hc : 0 < c)
    (n : Nat) : 0 < geometricMesh epsilon0 theta c n := by
  exact mul_pos hc (geometricEpsilon_pos hepsilon0 htheta n)

theorem geometricLabelTime_nonneg {epsilon0 theta : Real}
    (hepsilon0 : 0 <= epsilon0) (htheta : 0 <= theta) (n : Nat) :
    0 <= geometricLabelTime epsilon0 theta n := by
  exact mul_nonneg (by norm_num) (geometricEpsilon_nonneg hepsilon0 htheta n)

theorem geometricAlpha_nonneg {epsilon0 theta K : Real}
    (hepsilon0 : 0 <= epsilon0) (htheta : 0 <= theta) (hK : 0 <= K)
    (n : Nat) : 0 <= geometricAlpha epsilon0 theta K n := by
  exact div_nonneg (geometricEpsilon_nonneg hepsilon0 htheta n) hK

theorem geometricScaleConstant_pos {K c R : Real}
    (hK : 0 < K) (hc : 0 <= c) (hR : 0 <= R) :
    0 < geometricScaleConstant K c R := by
  unfold geometricScaleConstant
  nlinarith [mul_nonneg hc hR]

theorem geometricBeta_nonneg {epsilon0 theta K c R : Real}
    (hepsilon0 : 0 <= epsilon0) (htheta : 0 <= theta)
    (hK : 0 < K) (hc : 0 <= c) (hR : 0 <= R) (n : Nat) :
    0 <= geometricBeta epsilon0 theta K c R n := by
  exact mul_nonneg (geometricScaleConstant_pos hK hc hR).le
    (geometricEpsilon_nonneg hepsilon0 htheta n)

theorem geometricBeta_tendsto_zero {epsilon0 theta K c R : Real}
    (htheta0 : 0 <= theta) (htheta1 : theta < 1) :
    Tendsto (geometricBeta epsilon0 theta K c R) atTop (nhds 0) := by
  simpa [geometricBeta] using tendsto_const_nhds.mul
    (geometricEpsilon_tendsto_zero (epsilon0 := epsilon0) htheta0 htheta1)

/-- The source restriction `theta < 1/(K C_*)` gives the exact interleaving
`beta_(n+1) <= alpha_n`. -/
theorem geometricBeta_succ_le_alpha {epsilon0 theta K c R : Real}
    (hepsilon0 : 0 <= epsilon0) (htheta0 : 0 <= theta)
    (hK : 0 < K) (hc : 0 <= c) (hR : 0 <= R)
    (htheta : theta < 1 / (K * geometricScaleConstant K c R))
    (n : Nat) :
    geometricBeta epsilon0 theta K c R (n + 1) <=
      geometricAlpha epsilon0 theta K n := by
  have hC : 0 < geometricScaleConstant K c R :=
    geometricScaleConstant_pos hK hc hR
  have hKC : 0 < K * geometricScaleConstant K c R := mul_pos hK hC
  have hthetaKC : theta * (K * geometricScaleConstant K c R) < 1 := by
    exact (lt_div_iff₀ hKC).mp htheta
  have hCtheta : geometricScaleConstant K c R * theta < 1 / K := by
    apply (lt_div_iff₀ hK).2
    nlinarith
  have hepsilon : 0 <= geometricEpsilon epsilon0 theta n :=
    geometricEpsilon_nonneg hepsilon0 htheta0 n
  have hmul := mul_le_mul_of_nonneg_right hCtheta.le hepsilon
  rw [geometricBeta, geometricEpsilon_succ, geometricAlpha]
  calc
    geometricScaleConstant K c R *
        (theta * geometricEpsilon epsilon0 theta n) =
      (geometricScaleConstant K c R * theta) *
        geometricEpsilon epsilon0 theta n := by ring
    _ <= (1 / K) * geometricEpsilon epsilon0 theta n := hmul
    _ = geometricEpsilon epsilon0 theta n / K := by ring

/-- The lower scale inequality in `gridLabel_sandwich_of_coordinate_error`
is in fact an exact identity for the manuscript constants. -/
theorem geometric_lower_scale_identity
    (epsilon0 theta K c R : Real) (n : Nat) :
    geometricLowerError epsilon0 theta c R n +
        K * geometricLabelTime epsilon0 theta n =
      geometricBeta epsilon0 theta K c R n := by
  unfold geometricLowerError geometricLabelTime geometricBeta
    geometricScaleConstant
  ring

/-- The upper scale inequality is also exact when `K` is positive. -/
theorem geometric_upper_scale_identity
    (epsilon0 theta K : Real) (hK : K ≠ 0) (n : Nat) :
    geometricUpperError epsilon0 theta n +
        K * geometricAlpha epsilon0 theta K n =
      geometricLabelTime epsilon0 theta n := by
  unfold geometricUpperError geometricAlpha geometricLabelTime
  field_simp [hK]
  ring

end GeometricScales

end FiniteValuationApproximable
