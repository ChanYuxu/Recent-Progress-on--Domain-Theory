import FiniteValuationApproximable.Polytope
import Mathlib.Analysis.Convex.Cone.Dual
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Convex.Combination
import Mathlib.Order.Interval.Finset.Basic

/-!
# Finite upper-set cone generators

This module advances Lemma `lem:cone-generators` (source lines 1825--1943).
`Polytope.lean` already proves that the conic hull of the displayed standard
basis and cover-transfer generators is contained in the upper-set cone.

Here we prove the substantive dual argument in the reverse direction.  The key
finite layer-cake lemma says that every nonnegative monotone real function has
nonnegative pairing with every vector in `C_P`.  Hahn--Banach separation then
shows that every vector of `C_P` belongs to the *closure* of the displayed
conic hull.

We then prove that the conic hull itself is closed.  A strictly positive height
functional, built from `finiteRankScale`, normalizes every nonzero conic
combination into the convex hull of a finite normalized generator set.  Compactness
of that convex hull gives sequential closedness.  Combining the two arguments
yields the exact, unclosed equality printed in `lem:cone-generators`.

Source version: SHA-256
`4b2e65f0f96347bea4df7571e8993ad6e888c0ff7181c1305c5056880365ac94`.
-/

set_option autoImplicit false

universe u

namespace FiniteValuationApproximable

open Set
open Filter
open scoped BigOperators

section LayerCake

variable {P : Type u} [Fintype P] [PartialOrder P]

/-- The finite dot product used in the source's dual-cone proof. -/
noncomputable def finitePairing (z g : P -> Real) : Real :=
  ∑ p, z p * g p

/-- The positive support of a real-valued function on a finite type. -/
noncomputable def positiveSupport (g : P -> Real) : Finset P :=
  Finset.univ.filter fun p => 0 < g p

@[simp]
theorem mem_positiveSupport {g : P -> Real} {p : P} :
    p ∈ positiveSupport g <-> 0 < g p := by
  classical
  simp [positiveSupport]

/-- Positive support is an upper set for a nonnegative monotone function. -/
def positiveUpperSet (g : P -> Real) (hg : Monotone g) : UpperSet P where
  carrier := {p | 0 < g p}
  upper' := by
    intro p q hpq hp
    exact hp.trans_le (hg hpq)

@[simp]
theorem mem_positiveUpperSet {g : P -> Real} {hg : Monotone g} {p : P} :
    p ∈ (positiveUpperSet g hg : Set P) <-> 0 < g p :=
  Iff.rfl

/-- Finite layer-cake argument: pairing an upper-set-cone vector with a
nonnegative monotone function is nonnegative.

The proof repeatedly subtracts the least positive value of `g` from its
positive upper support.  This strictly decreases the finite positive support,
and each removed layer contributes a nonnegative scalar multiple of an
upper-set mass. -/
theorem finitePairing_nonneg_of_upperOrderCone
    (z : P -> Real) (hz : z ∈ UpperOrderCone P)
    (g : P -> Real) (hg0 : forall p, 0 <= g p) (hg : Monotone g) :
    0 <= finitePairing z g := by
  classical
  let S : Finset P := positiveSupport g
  by_cases hS : S.Nonempty
  · let V : Finset Real := S.image g
    have hV : V.Nonempty := hS.image g
    let m : Real := V.min' hV
    have hmV : m ∈ V := Finset.min'_mem V hV
    obtain ⟨p0, hp0S, hp0m⟩ := Finset.mem_image.mp hmV
    have hp0pos : 0 < g p0 := by
      simpa [S] using hp0S
    have hmpos : 0 < m := by
      simpa [hp0m] using hp0pos
    have hm_le (p : P) (hp : 0 < g p) : m <= g p := by
      apply Finset.min'_le V (g p)
      exact Finset.mem_image.mpr ⟨p, by simpa [S] using hp, rfl⟩
    let g' : P -> Real := fun p => g p - if 0 < g p then m else 0
    have hg'0 (p : P) : 0 <= g' p := by
      dsimp only [g']
      by_cases hp : 0 < g p
      · simp only [if_pos hp]
        exact sub_nonneg.mpr (hm_le p hp)
      · simpa [hp] using hg0 p
    have hg' : Monotone g' := by
      intro p q hpq
      dsimp only [g']
      by_cases hp : 0 < g p
      · have hq : 0 < g q := hp.trans_le (hg hpq)
        simp only [if_pos hp, if_pos hq]
        linarith [hg hpq]
      · have hgpzero : g p = 0 := le_antisymm (le_of_not_gt hp) (hg0 p)
        have hleft : g p - (if 0 < g p then m else 0) = 0 := by
          rw [hgpzero]
          simp
        rw [hleft]
        change 0 <= g' q
        exact hg'0 q
    have hsupport_subset : positiveSupport g' ⊆ positiveSupport g := by
      intro p hp
      have hp' : 0 < g' p := mem_positiveSupport.mp hp
      by_contra hnot
      have hnotpos : ¬ 0 < g p := by simpa using hnot
      have hgpzero : g p = 0 := le_antisymm (le_of_not_gt hnotpos) (hg0 p)
      simp [g', hnotpos, hgpzero] at hp'
    have hp0not : p0 ∉ positiveSupport g' := by
      apply (mem_positiveSupport.not).2
      have hzero : g' p0 = 0 := by
        dsimp only [g']
        rw [if_pos hp0pos, hp0m]
        ring
      rw [hzero]
      exact lt_irrefl 0
    have hsupport_strict : positiveSupport g' ⊂ positiveSupport g := by
      refine Finset.ssubset_iff_subset_ne.mpr ⟨hsupport_subset, ?_⟩
      intro heq
      exact hp0not (heq ▸ (show p0 ∈ positiveSupport g by simpa [S] using hp0S))
    have ih := finitePairing_nonneg_of_upperOrderCone z hz g' hg'0 hg'
    have hU : 0 <= vectorUpperMass z (positiveUpperSet g hg) :=
      hz (positiveUpperSet g hg)
    have hdecomp :
        finitePairing z g =
          finitePairing z g' + m * vectorUpperMass z (positiveUpperSet g hg) := by
      unfold finitePairing vectorUpperMass
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro p hp
      dsimp only [g']
      by_cases hgp : 0 < g p
      · simp [positiveUpperSet, hgp]
        ring
      · simp [positiveUpperSet, hgp]
    rw [hdecomp]
    exact add_nonneg ih (mul_nonneg (le_of_lt hmpos) hU)
  · have hgzero : g = 0 := by
      funext p
      have hpnot : ¬ 0 < g p := by
        intro hp
        exact hS ⟨p, by simpa [S] using hp⟩
      exact le_antisymm (le_of_not_gt hpnot) (hg0 p)
    subst g
    simp [finitePairing]
termination_by (positiveSupport g).card
decreasing_by
  exact Finset.card_lt_card hsupport_strict

end LayerCake

section HullBridge

variable {P : Type u} [Fintype P] [PartialOrder P]

/-- The manuscript's syntax-level conic hull agrees exactly with mathlib's
pointed-cone hull.  This is only a representation bridge; no closure is used. -/
theorem inConicHull_iff_mem_pointedHull {z : P -> Real} :
    InConicHull (ConeGenerator P) z <->
      z ∈ PointedCone.hull Real (ConeGenerator P) := by
  constructor
  · intro hz
    induction hz with
    | zero => exact Submodule.zero_mem _
    | generator hz => exact PointedCone.subset_hull hz
    | add hz hw ihz ihw => exact Submodule.add_mem _ ihz ihw
    | nonneg_smul c hc hz ih => exact PointedCone.smul_mem _ hc ih
  · intro hz
    refine Submodule.span_induction
      (p := fun z _ => InConicHull (ConeGenerator P) z) ?_ ?_ ?_ ?_ hz
    · intro z hz
      exact InConicHull.generator hz
    · exact InConicHull.zero
    · intro x y hx hy ihx ihy
      exact InConicHull.add ihx ihy
    · intro c x hx ih
      exact InConicHull.nonneg_smul c.1 c.2 ih

/-- The pointed cone generated by the displayed directions. -/
noncomputable abbrev generatorPointedCone : PointedCone Real (P -> Real) :=
  PointedCone.hull Real (ConeGenerator P)

/-- Its topological closure, bundled as a proper cone so that finite-dimensional
Hahn--Banach separation applies without asserting the missing closedness of the
unclosed hull. -/
noncomputable def generatorClosureCone : ProperCone Real (P -> Real) where
  toSubmodule := (generatorPointedCone (P := P)).closure
  isClosed' := isClosed_closure

theorem mem_generatorClosureCone_iff {z : P -> Real} :
    z ∈ generatorClosureCone (P := P) <->
      z ∈ closure {w : P -> Real | InConicHull (ConeGenerator P) w} := by
  change z ∈ closure (generatorPointedCone (P := P) : Set (P -> Real)) <-> _
  have hsets :
      (generatorPointedCone (P := P) : Set (P -> Real)) =
        {w : P -> Real | InConicHull (ConeGenerator P) w} := by
    ext w
    exact inConicHull_iff_mem_pointedHull.symm
  rw [hsets]

/-- Coordinate expansion in the standard basis. -/
theorem sum_smul_standardBasis (z : P -> Real) :
    (∑ p, z p • standardBasis p) = z := by
  classical
  funext q
  simp [standardBasis]

/-- Every continuous linear functional on the finite coordinate space is the
finite pairing with its values on standard basis vectors. -/
theorem continuousLinearMap_eq_finitePairing
    (f : StrongDual Real (P -> Real)) (z : P -> Real) :
    f z = finitePairing z (fun p => f (standardBasis p)) := by
  calc
    f z = f (∑ p, z p • standardBasis p) :=
      congrArg f (sum_smul_standardBasis z).symm
    _ = ∑ p, f (z p • standardBasis p) := by rw [map_sum]
    _ = ∑ p, z p * f (standardBasis p) := by simp
    _ = finitePairing z (fun p => f (standardBasis p)) := rfl

/-- Nonnegativity on the generator hull forces the coordinate function of a
linear functional to be nonnegative and monotone. -/
theorem generator_nonnegative_implies_coordinate_monotone
    (f : StrongDual Real (P -> Real))
    (hf : forall w, w ∈ generatorPointedCone (P := P) -> 0 <= f w) :
    (forall p, 0 <= f (standardBasis p)) ∧
      Monotone (fun p => f (standardBasis p)) := by
  classical
  constructor
  · intro p
    apply hf
    exact PointedCone.subset_hull
      (show standardBasis p ∈ ConeGenerator P from Or.inl ⟨p, rfl⟩)
  · letI : LocallyFiniteOrder P := Fintype.toLocallyFiniteOrder
    rw [monotone_iff_forall_covBy]
    intro p q hpq
    have hgenerator : transferDirection p q ∈ ConeGenerator P := by
      right
      exact ⟨p, q, hpq, rfl⟩
    have hnonneg := hf (transferDirection p q)
      (PointedCone.subset_hull hgenerator)
    rw [transferDirection, map_sub] at hnonneg
    exact sub_nonneg.mp hnonneg

/-- P3 closure form of the hard inclusion in `lem:cone-generators`: every
upper-set-cone vector lies in the closure of the displayed finite conic hull.

The proof follows the manuscript's dual-cone argument.  If a vector were
outside the closed hull, Hahn--Banach would give a linear functional
nonnegative on every generator but negative on that vector.  Its basis values
form a nonnegative monotone function, contradicting the finite layer-cake
lemma above. -/
theorem upperOrderCone_subset_closure_conicHull {z : P -> Real}
    (hz : z ∈ UpperOrderCone P) :
    z ∈ closure {w : P -> Real | InConicHull (ConeGenerator P) w} := by
  rw [← mem_generatorClosureCone_iff]
  by_contra hnot
  obtain ⟨f, hf, hfz⟩ :=
    (generatorClosureCone (P := P)).hyperplane_separation_point hnot
  have hfonHull : forall w, w ∈ generatorPointedCone (P := P) -> 0 <= f w := by
    intro w hw
    exact hf w (subset_closure hw)
  obtain ⟨hf0, hfmono⟩ :=
    generator_nonnegative_implies_coordinate_monotone f hfonHull
  have hpair := finitePairing_nonneg_of_upperOrderCone z hz
    (fun p => f (standardBasis p)) hf0 hfmono
  rw [← continuousLinearMap_eq_finitePairing] at hpair
  exact (not_lt_of_ge hpair) hfz

/-- The upper-set cone is closed in the finite coordinate topology. -/
theorem isClosed_upperOrderCone : IsClosed (UpperOrderCone P) := by
  have hcontinuous (U : UpperSet P) :
      Continuous (fun z : P -> Real => vectorUpperMass z U) := by
    unfold vectorUpperMass
    refine continuous_finset_sum Finset.univ ?_
    intro p hp
    by_cases hpU : p ∈ (U : Set P)
    · simpa [hpU] using (continuous_apply p :
        Continuous (fun z : P -> Real => z p))
    · simpa [hpU] using (continuous_const :
        Continuous (fun _z : P -> Real => (0 : Real)))
  rw [show UpperOrderCone P =
      ⋂ U : UpperSet P, {z : P -> Real | 0 <= vectorUpperMass z U} by
    ext z
    simp [UpperOrderCone]]
  exact isClosed_iInter fun U => isClosed_Ici.preimage (hcontinuous U)

/-- Exact closure equality obtained by combining the already proved easy
generator inclusion, closedness of `C_P`, and the dual separation theorem. -/
theorem closure_conicHull_generators_eq_upperOrderCone :
    closure {w : P -> Real | InConicHull (ConeGenerator P) w} =
      UpperOrderCone P := by
  apply Set.Subset.antisymm
  · apply closure_minimal
    · intro z hz
      exact conicHull_generators_subset_upperOrderCone hz
    · exact isClosed_upperOrderCone
  · intro z hz
    exact upperOrderCone_subset_closure_conicHull hz

/-! ### Closedness of the finite generated cone

The positive height below is the missing finite-dimensional bridge in the
closure argument.  Every listed generator has strictly positive height.  A
nonzero conic combination can therefore be normalized to height one, where it
belongs to the convex hull of the finite normalized generator set. -/

/-- A strictly positive linear height on the displayed generator set. -/
noncomputable def generatorHeight (z : P -> Real) : Real :=
  ∑ p, finiteRankScale p * z p

@[simp]
theorem generatorHeight_zero : generatorHeight (P := P) 0 = 0 := by
  simp [generatorHeight]

theorem generatorHeight_add (z w : P -> Real) :
    generatorHeight (z + w) = generatorHeight z + generatorHeight w := by
  simp [generatorHeight, mul_add, Finset.sum_add_distrib]

theorem generatorHeight_smul (c : Real) (z : P -> Real) :
    generatorHeight (c • z) = c * generatorHeight z := by
  simp [generatorHeight, Finset.mul_sum, mul_left_comm]

theorem generatorHeight_standardBasis (p : P) :
    generatorHeight (standardBasis p) = finiteRankScale p := by
  classical
  simp [generatorHeight, standardBasis]

theorem generatorHeight_transferDirection (p q : P) :
    generatorHeight (transferDirection p q) =
      finiteRankScale q - finiteRankScale p := by
  classical
  simp [transferDirection, generatorHeight, standardBasis,
    Finset.sum_sub_distrib, mul_sub]

/-- Every standard-basis or cover-transfer generator has positive height. -/
theorem generatorHeight_pos_of_mem {z : P -> Real}
    (hz : z ∈ ConeGenerator P) : 0 < generatorHeight z := by
  rcases hz with ⟨p, rfl⟩ | ⟨p, q, hpq, rfl⟩
  · simpa [generatorHeight_standardBasis] using finiteRankScale_pos p
  · rw [generatorHeight_transferDirection]
    exact sub_pos.mpr (finiteRankScale_strict hpq.1)

theorem generatorHeight_nonneg_of_hull {z : P -> Real}
    (hz : InConicHull (ConeGenerator P) z) : 0 <= generatorHeight z := by
  induction hz with
  | zero => simp
  | generator hz => exact (generatorHeight_pos_of_mem hz).le
  | add hz hw ihz ihw => rw [generatorHeight_add]; positivity
  | nonneg_smul c hc hz ih => rw [generatorHeight_smul]; positivity

/-- The height vanishes on the generated cone only at its vertex. -/
theorem eq_zero_of_hull_generatorHeight_eq_zero {z : P -> Real}
    (hz : InConicHull (ConeGenerator P) z) (hzero : generatorHeight z = 0) : z = 0 := by
  induction hz with
  | zero => rfl
  | generator hz =>
      exact False.elim ((generatorHeight_pos_of_mem hz).ne' hzero)
  | @add z w hz hw ihz ihw =>
      have hz0 : 0 <= generatorHeight z := generatorHeight_nonneg_of_hull hz
      have hw0 : 0 <= generatorHeight w := generatorHeight_nonneg_of_hull hw
      rw [generatorHeight_add] at hzero
      have hzeq : generatorHeight z = 0 := by linarith
      have hweq : generatorHeight w = 0 := by linarith
      rw [ihz hzeq, ihw hweq]
      exact add_zero 0
  | nonneg_smul c hc hz ih =>
      rw [generatorHeight_smul] at hzero
      rcases mul_eq_zero.mp hzero with hc0 | hz0
      · subst c
        exact zero_smul Real _
      · rw [ih hz0]
        exact smul_zero c

/-- Radial normalization to the height-one hyperplane. -/
noncomputable def generatorNormalize (z : P -> Real) : P -> Real :=
  (generatorHeight z)⁻¹ • z

/-- The finite set of normalized standard-basis and cover-transfer generators. -/
def NormalizedConeGenerator (P : Type u) [Fintype P] [PartialOrder P] : Set (P -> Real) :=
  generatorNormalize '' ConeGenerator P

theorem coneGenerator_finite : (ConeGenerator P).Finite := by
  apply ((Set.finite_range (standardBasis : P -> P -> Real)).union
    (Set.finite_range (fun pq : P × P => transferDirection pq.1 pq.2))).subset
  intro z hz
  rcases hz with ⟨p, rfl⟩ | ⟨p, q, hpq, rfl⟩
  · exact Or.inl ⟨p, rfl⟩
  · exact Or.inr ⟨(p, q), rfl⟩

theorem normalizedConeGenerator_finite :
    (NormalizedConeGenerator P).Finite := by
  exact coneGenerator_finite.image generatorNormalize

/-- A positive-height conic combination normalizes into the convex hull of
the finite normalized generator set. -/
theorem generatorNormalize_mem_convexHull {z : P -> Real}
    (hz : InConicHull (ConeGenerator P) z)
    (hpos : 0 < generatorHeight z) :
    generatorNormalize z ∈ convexHull Real (NormalizedConeGenerator P) := by
  induction hz with
  | zero => simp at hpos
  | @generator z hz =>
      exact subset_convexHull Real _ ⟨z, hz, rfl⟩
  | @add z w hz hw ihz ihw =>
      have hz0 : 0 <= generatorHeight z := generatorHeight_nonneg_of_hull hz
      have hw0 : 0 <= generatorHeight w := generatorHeight_nonneg_of_hull hw
      rw [generatorHeight_add] at hpos
      by_cases hzeq : generatorHeight z = 0
      · have hzv : z = 0 := eq_zero_of_hull_generatorHeight_eq_zero hz hzeq
        subst z
        have hwpos : 0 < generatorHeight w := by
          simpa only [generatorHeight_zero, zero_add] using hpos
        simpa [generatorNormalize] using ihw hwpos
      · by_cases hweq : generatorHeight w = 0
        · have hwv : w = 0 := eq_zero_of_hull_generatorHeight_eq_zero hw hweq
          subst w
          have hzpos : 0 < generatorHeight z := by
            simpa only [generatorHeight_zero, add_zero] using hpos
          simpa [generatorNormalize] using ihz hzpos
        · have hzpos : 0 < generatorHeight z := lt_of_le_of_ne hz0 (Ne.symm hzeq)
          have hwpos : 0 < generatorHeight w := lt_of_le_of_ne hw0 (Ne.symm hweq)
          let d := generatorHeight z + generatorHeight w
          have hdpos : 0 < d := add_pos hzpos hwpos
          have ha : 0 <= generatorHeight z / d := div_nonneg hz0 hdpos.le
          have hb : 0 <= generatorHeight w / d := div_nonneg hw0 hdpos.le
          have hab : generatorHeight z / d + generatorHeight w / d = 1 := by
            dsimp only [d]
            field_simp
          have hcomb := (convex_convexHull Real (NormalizedConeGenerator P))
            (ihz hzpos) (ihw hwpos) ha hb hab
          have heq :
              (generatorHeight z / d) • generatorNormalize z +
                  (generatorHeight w / d) • generatorNormalize w =
                generatorNormalize (z + w) := by
            funext p
            simp only [generatorNormalize, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
              generatorHeight_add]
            dsimp only [d]
            field_simp
          rwa [heq] at hcomb
  | @nonneg_smul c z hc hz ih =>
      rw [generatorHeight_smul] at hpos
      have hcpos : 0 < c := by
        have hz0 := generatorHeight_nonneg_of_hull hz
        nlinarith
      have hzpos : 0 < generatorHeight z := by
        nlinarith
      have heq : generatorNormalize (c • z) = generatorNormalize z := by
        funext p
        simp only [generatorNormalize, generatorHeight_smul, Pi.smul_apply,
          smul_eq_mul]
        field_simp
      rw [heq]
      exact ih hzpos

theorem generatorHeight_continuous :
    Continuous (generatorHeight : (P -> Real) -> Real) := by
  unfold generatorHeight
  refine continuous_finset_sum Finset.univ ?_
  intro p hp
  exact continuous_const.mul (continuous_apply p)

/-- The convex hull of the normalized generators remains inside the original
syntax-level conic hull. -/
theorem convexHull_normalized_subset_conicHull :
    convexHull Real (NormalizedConeGenerator P) ⊆
      {z : P -> Real | InConicHull (ConeGenerator P) z} := by
  apply convexHull_min
  · intro z hz
    rcases hz with ⟨g, hg, rfl⟩
    exact InConicHull.nonneg_smul _
      (inv_nonneg.mpr (generatorHeight_pos_of_mem hg).le)
      (InConicHull.generator hg)
  · have hsets :
        {z : P -> Real | InConicHull (ConeGenerator P) z} =
          (generatorPointedCone (P := P) : Set (P -> Real)) := by
      ext z
      exact inConicHull_iff_mem_pointedHull
    rw [hsets]
    exact (generatorPointedCone (P := P)).convex

/-- Every conic combination is its nonnegative height times a point of the
compact normalized convex hull. -/
theorem exists_generatorHeight_smul_convexHull [Nonempty P] {z : P -> Real}
    (hz : InConicHull (ConeGenerator P) z) :
    ∃ k ∈ convexHull Real (NormalizedConeGenerator P),
      z = generatorHeight z • k := by
  by_cases hzero : generatorHeight z = 0
  · have hz0 : z = 0 := eq_zero_of_hull_generatorHeight_eq_zero hz hzero
    let p : P := Classical.choice inferInstance
    let k : P -> Real := generatorNormalize (standardBasis p)
    have hkN : k ∈ NormalizedConeGenerator P := by
      exact ⟨standardBasis p, Or.inl ⟨p, rfl⟩, rfl⟩
    refine ⟨k, subset_convexHull Real _ hkN, ?_⟩
    rw [hz0]
    simp
  · have hnonneg := generatorHeight_nonneg_of_hull hz
    have hpos : 0 < generatorHeight z := lt_of_le_of_ne hnonneg (Ne.symm hzero)
    refine ⟨generatorNormalize z,
      generatorNormalize_mem_convexHull hz hpos, ?_⟩
    funext p
    simp only [generatorNormalize, Pi.smul_apply, smul_eq_mul]
    field_simp

/-- The syntax-level conic hull of the finite displayed generator set is
closed.  The empty-poset case is trivial; otherwise compactness of the finite
normalized convex hull supplies a convergent subsequence. -/
theorem isClosed_conicHull_generators :
    IsClosed {z : P -> Real | InConicHull (ConeGenerator P) z} := by
  rw [← isSeqClosed_iff_isClosed]
  intro x z hx hxtend
  cases isEmpty_or_nonempty P with
  | inl hP =>
      letI := hP
      have hz0 : z = 0 := Subsingleton.elim z 0
      rw [hz0]
      exact InConicHull.zero
  | inr hP =>
      letI := hP
      have hdecomp (n : Nat) :
          ∃ k ∈ convexHull Real (NormalizedConeGenerator P),
            x n = generatorHeight (x n) • k :=
        exists_generatorHeight_smul_convexHull (hx n)
      choose k hk hxk using hdecomp
      obtain ⟨k0, hk0, phi, hphi, hk_tendsto⟩ :=
        (normalizedConeGenerator_finite (P := P)).isCompact_convexHull Real
          |>.tendsto_subseq hk
      have hheight_tendsto :
          Tendsto (fun n => generatorHeight (x n)) atTop
            (nhds (generatorHeight z)) :=
        ((generatorHeight_continuous (P := P)).tendsto z).comp hxtend
      have hphi_tendsto : Tendsto phi atTop atTop := hphi.tendsto_atTop
      have hheight_sub := hheight_tendsto.comp hphi_tendsto
      have hx_sub : Tendsto (x ∘ phi) atTop (nhds z) := hxtend.comp hphi_tendsto
      have hsmul_sub :
          Tendsto (x ∘ phi) atTop (nhds (generatorHeight z • k0)) := by
        have hprod := hheight_sub.smul hk_tendsto
        have hfun :
            (fun n => generatorHeight (x (phi n)) • k (phi n)) = x ∘ phi := by
          funext n
          exact (hxk (phi n)).symm
        rw [← hfun]
        simpa only [Function.comp_apply] using hprod
      have hz_eq : z = generatorHeight z • k0 :=
        tendsto_nhds_unique hx_sub hsmul_sub
      have hheight_nonneg (n : Nat) : 0 <= generatorHeight (x n) :=
        generatorHeight_nonneg_of_hull (hx n)
      have hzheight_nonneg : 0 <= generatorHeight z := by
        exact isClosed_Ici.mem_of_tendsto hheight_tendsto
          (Eventually.of_forall hheight_nonneg)
      rw [hz_eq]
      exact InConicHull.nonneg_smul _ hzheight_nonneg
        (convexHull_normalized_subset_conicHull hk0)

/-- Generic extraction of the exact reverse inclusion from a closedness proof. -/
theorem upperOrderCone_subset_conicHull_of_isClosed
    (hclosed : IsClosed {w : P -> Real | InConicHull (ConeGenerator P) w})
    {z : P -> Real} (hz : z ∈ UpperOrderCone P) :
    InConicHull (ConeGenerator P) z := by
  have hz' := upperOrderCone_subset_closure_conicHull hz
  rwa [hclosed.closure_eq] at hz'

/-- Generic extraction of exact set equality from a closedness proof. -/
theorem conicHull_generators_eq_upperOrderCone_of_isClosed
    (hclosed : IsClosed {w : P -> Real | InConicHull (ConeGenerator P) w}) :
    {w : P -> Real | InConicHull (ConeGenerator P) w} = UpperOrderCone P := by
  apply Set.Subset.antisymm
  · intro z hz
    exact conicHull_generators_subset_upperOrderCone hz
  · intro z hz
    exact upperOrderCone_subset_conicHull_of_isClosed hclosed hz

/-- P3 hard inclusion in `lem:cone-generators`: every vector satisfying all
upper-set inequalities is an actual finite conic combination of the displayed
standard-basis and cover-transfer generators. -/
theorem upperOrderCone_subset_conicHull {z : P -> Real}
    (hz : z ∈ UpperOrderCone P) :
    InConicHull (ConeGenerator P) z :=
  upperOrderCone_subset_conicHull_of_isClosed isClosed_conicHull_generators hz

/-- Exact generator equality from `lem:cone-generators`, with no topological
closure and no additional hypothesis. -/
theorem conicHull_generators_eq_upperOrderCone :
    {w : P -> Real | InConicHull (ConeGenerator P) w} = UpperOrderCone P :=
  conicHull_generators_eq_upperOrderCone_of_isClosed isClosed_conicHull_generators

end HullBridge

end FiniteValuationApproximable
