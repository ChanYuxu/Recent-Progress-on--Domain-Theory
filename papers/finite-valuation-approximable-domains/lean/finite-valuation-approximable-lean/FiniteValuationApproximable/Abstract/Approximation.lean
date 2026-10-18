import FiniteValuationApproximable.OrderTheory
import Mathlib.Data.Nat.Pairing

/-!
# Abstract finite-separation and approximation machinery

This module formalizes the order-theoretic core used in
`main17-4b2e65f0f963` (SHA-256
`4b2e65f0f96347bea4df7571e8993ad6e888c0ff7181c1305c5056880365ac94`).
It deliberately contains no definition of continuous valuations or of the
finite-valuation-approximable class.  Those notions require separate semantic
interfaces.

Source relation:

* `IsFiniteSeparator` and `IsFinitelySeparated` encode `def:FS`, source lines
  288--305, without assuming pointedness.
* `IsFinitelySeparated.wayBelow` proves the order-theoretic statement cited as
  `lem:fs-waybelow`, source lines 1416--1419.
* the square declarations isolate the general, valuation-free content of
  `lem:square`, source lines 1431--1455.
* the pullback declarations isolate the approximation calculation in
  `cor:retract`, source lines 1601--1622.
-/

set_option autoImplicit false
set_option linter.unnecessarySimpa false

universe u v w

namespace FiniteValuationApproximable
namespace AbstractApproximation

open Set
open AbramskyJung.Chapter2

/- `Mathlib.Data.Nat.Pairing` and the Chapter 3 retraction module both expose
order-theoretic names that overlap with the Chapter 2 API used by this file.
Keep the source semantics explicit and give the intended declarations local
aliases rather than relying on ambiguous `open` resolution. -/
abbrev DirectedSet {X : Type u} [Preorder X] (A : Set X) : Prop :=
  AbramskyJung.Chapter2.DirectedSet A
abbrev IsSup {X : Type u} [Preorder X] (A : Set X) (x : X) : Prop :=
  AbramskyJung.Chapter2.IsSup A x
abbrev IsDcpo (X : Type u) [Preorder X] : Prop :=
  AbramskyJung.Chapter2.IsDcpo X
abbrev IsContinuousDomain (X : Type u) [Preorder X] : Prop :=
  AbramskyJung.Chapter2.IsContinuousDomain X
abbrev ScottContinuous
    {X : Type u} {Y : Type v} [Preorder X] [Preorder Y]
    (f : X -> Y) : Prop :=
  AbramskyJung.Chapter2.ScottContinuous f
abbrev ContinuousSectionRetractionPair
    (X : Type u) (Y : Type v) [Preorder X] [Preorder Y] :=
  AbramskyJung.Chapter3.ContinuousSectionRetractionPair X Y

section FiniteSeparation

variable {D : Type u} [Preorder D]

/-- Source item `def_FS` (lines 288--305), separator clause: `M` is finite and
for every `x` it contains an `m` with `f x ≤ m ≤ x`.  Scott continuity is kept
separate, exactly as a property of the map rather than of the finite witness. -/
def IsFiniteSeparator (M : Set D) (f : D → D) : Prop :=
  M.Finite ∧ ∀ x : D, ∃ m ∈ M, f x ≤ m ∧ m ≤ x

/-- Source item `def_FS` (lines 288--305): existence of a finite separator from
the identity. -/
def IsFinitelySeparated (f : D → D) : Prop :=
  ∃ M : Set D, IsFiniteSeparator M f

namespace IsFinitelySeparated

theorem below_id {f : D → D} (hf : IsFinitelySeparated f) (x : D) :
    f x ≤ x := by
  rcases hf with ⟨M, _hMfinite, hM⟩
  rcases hM x with ⟨m, _hmM, hfxm, hmx⟩
  exact le_trans hfxm hmx

/-- Pointwise smaller maps inherit a finite separator. -/
theorem of_pointwise_le {f g : D → D} (hf : IsFinitelySeparated f)
    (hgf : ∀ x : D, g x ≤ f x) :
    IsFinitelySeparated g := by
  rcases hf with ⟨M, hMfinite, hM⟩
  refine ⟨M, hMfinite, ?_⟩
  intro x
  rcases hM x with ⟨m, hmM, hfxm, hmx⟩
  exact ⟨m, hmM, le_trans (hgf x) hfxm, hmx⟩

/-- If `f` is finitely separated, its square is separated by the same finite
set.  This is the finite-separation clause of source item `lem_square`. -/
theorem square {f : D → D} (hf : IsFinitelySeparated f) :
    IsFinitelySeparated (fun x => f (f x)) := by
  have hbelow : ∀ x : D, f x ≤ x := hf.below_id
  rcases hf with ⟨M, hMfinite, hM⟩
  refine ⟨M, hMfinite, ?_⟩
  intro x
  rcases hM x with ⟨m, hmM, hfxm, hmx⟩
  exact ⟨m, hmM, le_trans (hbelow (f x)) hfxm, hmx⟩

/-- Finite separation transports through a monotone reconstruction map.  This
is the abstract calculation used in both parts of source item
`thm:saturation`: a separator `M` for `q` becomes the finite image `e '' M`
for `x ↦ e (q (p x))`, provided `e ∘ p ≤ id`. -/
theorem sandwich
    {E : Type v} [Preorder E]
    {q : E → E} {p : D → E} {e : E → D}
    (hq : IsFinitelySeparated q) (he : Monotone e)
    (hep : ∀ x : D, e (p x) ≤ x) :
    IsFinitelySeparated (fun x => e (q (p x))) := by
  rcases hq with ⟨M, hMfinite, hM⟩
  refine ⟨e '' M, hMfinite.image e, ?_⟩
  intro x
  rcases hM (p x) with ⟨m, hmM, hqpm, hmpx⟩
  exact ⟨e m, ⟨m, hmM, rfl⟩, he hqpm,
    le_trans (he hmpx) (hep x)⟩

/-- Source item `lem_fs_waybelow` (lines 1416--1419), proved here rather than
postulated: a Scott-continuous finitely separated map satisfies `f x ≪ x`.
The proof uses only the Chapter 2 directed-supremum API and finiteness of the
separator. -/
theorem wayBelow {f : D → D} (hf : ScottContinuous f)
    (hsep : IsFinitelySeparated f) (x : D) :
    f x ≪ x := by
  intro A s hA hs hxs
  rcases hsep with ⟨M, hMfinite, hM⟩
  let R : Set D := {m | m ∈ M ∧ ∃ a ∈ A, m ≤ a}
  have hRfinite : R.Finite := by
    apply hMfinite.subset
    intro m hm
    exact hm.1
  have hRbounded : ∀ m ∈ R, ∃ a ∈ A, m ≤ a := by
    intro m hm
    exact hm.2
  obtain ⟨a0, ha0A, hRa0⟩ :=
    DirectedSet.exists_upper_finite_of_forall hA hRfinite hRbounded
  refine ⟨a0, ha0A, le_trans (hf.monotone hxs) ?_⟩
  have hfsup : IsSup (f '' A) (f s) := hf.maps_isSup hA hs
  apply hfsup.2 a0
  intro y hy
  rcases hy with ⟨a, haA, rfl⟩
  rcases hM a with ⟨m, hmM, hfam, hma⟩
  exact le_trans hfam (hRa0 m ⟨hmM, a, haA, hma⟩)

/-- Source-facing wrapper for `lem:fs-waybelow`.  The dcpo hypothesis is kept
to match the manuscript literally; the implementation above proves the
strictly more general preorder statement. -/
theorem lem_fs_waybelow (_hD : IsDcpo D) {f : D → D}
    (hf : ScottContinuous f) (hsep : IsFinitelySeparated f) (x : D) :
    f x ≪ x :=
  hsep.wayBelow hf x

end IsFinitelySeparated

/-- Four interpolation steps in a continuous domain.  This is the exact
way-below shape used twice in the proof of source item `lem_square`. -/
theorem fourStepInterpolation
    (hD : IsContinuousDomain D) {x y : D} (hxy : x ≪ y) :
    ∃ r s t : D, x ≪ r ∧ r ≪ s ∧ s ≪ t ∧ t ≪ y := by
  rcases wayBelow_interpolation hD hxy with ⟨r, hxr, hry⟩
  rcases wayBelow_interpolation hD hry with ⟨s, hrs, hsy⟩
  rcases wayBelow_interpolation hD hsy with ⟨t, hst, hty⟩
  exact ⟨r, s, t, hxr, hrs, hst, hty⟩

/-- A bundled choice of the four-step interpolation chain. -/
structure FourStepChain (x y : D) where
  r : D
  s : D
  t : D
  first : x ≪ r
  second : r ≪ s
  third : s ≪ t
  fourth : t ≪ y

theorem fourStepChain_nonempty
    (hD : IsContinuousDomain D) {x y : D} (hxy : x ≪ y) :
    Nonempty (FourStepChain x y) := by
  rcases fourStepInterpolation hD hxy with ⟨r, s, t, hxr, hrs, hst, hty⟩
  exact ⟨⟨r, s, t, hxr, hrs, hst, hty⟩⟩

end FiniteSeparation

section ApproximateIdentities

variable {D : Type u} [Preorder D]

/-- The range of an increasing sequence is directed in the Chapter 2 sense. -/
theorem directedSet_range_of_monotone (f : Nat → D) (hf : Monotone f) :
    DirectedSet (Set.range f) := by
  constructor
  · exact ⟨f 0, ⟨0, rfl⟩⟩
  · intro x hx y hy
    rcases hx with ⟨m, rfl⟩
    rcases hy with ⟨n, rfl⟩
    exact ⟨f (max m n), ⟨max m n, rfl⟩,
      hf (Nat.le_max_left m n), hf (Nat.le_max_right m n)⟩

/-- Finitely many upward-stable natural-number constraints have one common
index.  This packages the repeated `max` choice used in `lem:square`. -/
theorem exists_nat_forall_fintype
    {ι : Type v} [Fintype ι] (P : ι → Nat → Prop)
    (hexists : ∀ a : ι, ∃ n : Nat, P a n)
    (hupward : ∀ a : ι, ∀ {m n : Nat}, P a m → m ≤ n → P a n) :
    ∃ n : Nat, ∀ a : ι, P a n := by
  classical
  choose bound hbound using hexists
  refine ⟨Finset.univ.sup bound, ?_⟩
  intro a
  exact hupward a (hbound a)
    (Finset.le_sup (s := Finset.univ) (f := bound) (Finset.mem_univ a))

/-- Source item `def_FS` (lines 299--302), without the finite-separation
field: an increasing sequence of Scott-continuous self-maps below the identity
whose pointwise supremum is the identity. -/
structure IncreasingApproximateIdentity (D : Type u) [Preorder D] where
  map : Nat → ScottContFun D D
  monotone : Monotone map
  below_id : ∀ n : Nat, ∀ x : D, map n x ≤ x
  pointwise_sup : ∀ x : D, IsSup (Set.range (fun n => map n x)) x

/-- Source item `def_FS` (lines 288--305), sequential form.  The manuscript
allows a general directed family in the definition; this structure is the
specialized sequence interface used by `lem_square` and later FVA arguments. -/
structure FSApproximateIdentity (D : Type u) [Preorder D]
    extends IncreasingApproximateIdentity D where
  finitelySeparated : ∀ n : Nat, IsFinitelySeparated (map n)

/-- Source item `def_FS` in its general directed-family form.  A set of
Scott-continuous maps is directed in pointwise order, every member is finitely
separated, and evaluation at each point has supremum that point. -/
structure DirectedFSApproximateIdentity (D : Type u) [Preorder D] where
  maps : Set (ScottContFun D D)
  directed : DirectedSet maps
  finitelySeparated :
    ∀ f : ScottContFun D D, f ∈ maps → IsFinitelySeparated f
  pointwise_sup :
    ∀ x : D, IsSup ((fun f : ScottContFun D D => f x) '' maps) x

/-- The exact nested approximation data in source item `lem_square`: an outer
approximate identity `aᵢ` and, for each `i`, an increasing inner sequence
`hᵢⱼ` with pointwise supremum `aᵢ`, lying below the identity and finitely
separated. -/
structure NestedApproximation (D : Type u) [Preorder D] where
  outer : IncreasingApproximateIdentity D
  inner : Nat → Nat → ScottContFun D D
  inner_monotone : ∀ i : Nat, Monotone (inner i)
  inner_below_id : ∀ i j : Nat, ∀ x : D, inner i j x ≤ x
  inner_pointwise_sup :
    ∀ i : Nat, ∀ x : D,
      IsSup (Set.range (fun j => inner i j x)) (outer.map i x)
  inner_finitelySeparated :
    ∀ i j : Nat, IsFinitelySeparated (inner i j)

namespace IncreasingApproximateIdentity

variable (A : IncreasingApproximateIdentity D)

theorem range_directed (x : D) :
    DirectedSet (Set.range (fun n => A.map n x)) :=
  directedSet_range_of_monotone _ fun _m _n hmn => A.monotone hmn x

end IncreasingApproximateIdentity

namespace FSApproximateIdentity

variable (A : FSApproximateIdentity D)

/-- A sequential FS approximate identity gives the general directed family in
`def_FS` by taking the range of its sequence. -/
def toDirected : DirectedFSApproximateIdentity D where
  maps := Set.range A.map
  directed := directedSet_range_of_monotone A.map A.monotone
  finitelySeparated := by
    intro f hf
    rcases hf with ⟨n, rfl⟩
    exact A.finitelySeparated n
  pointwise_sup := by
    intro x
    have himage :
        (fun f : ScottContFun D D => f x) '' Set.range A.map =
          Set.range (fun n => A.map n x) := by
      ext y
      constructor
      · rintro ⟨f, ⟨n, rfl⟩, rfl⟩
        exact ⟨n, rfl⟩
      · rintro ⟨n, rfl⟩
        exact ⟨A.map n, ⟨n, rfl⟩, rfl⟩
    rw [himage]
    exact A.pointwise_sup x

end FSApproximateIdentity

namespace NestedApproximation

variable (A : NestedApproximation D)

theorem inner_range_directed (i : Nat) (x : D) :
    DirectedSet (Set.range (fun j => A.inner i j x)) :=
  directedSet_range_of_monotone _ fun _j _k hjk =>
    A.inner_monotone i hjk x

end NestedApproximation

end ApproximateIdentities

section Factorization

variable {D : Type u} {E : Type v} [Preorder D] [Preorder E]

/-- A valuation-free Scott-continuous factorization of `f` through `B`.
This is only the abstract factorization interface; it does not assert that `B`
is a valuation space. -/
structure ScottFactorization (f : D → E) (B : Type w) [Preorder B] where
  encode : D → B
  decode : B → E
  encode_continuous : ScottContinuous encode
  decode_continuous : ScottContinuous decode
  factor : ∀ x : D, decode (encode x) = f x

namespace ScottFactorization

variable {B : Type w} [Preorder B] {f : D → E}

theorem continuous (F : ScottFactorization f B) : ScottContinuous f := by
  have hcomp : ScottContinuous (fun x => F.decode (F.encode x)) :=
    F.decode_continuous.comp F.encode_continuous
  have hfun : (fun x => F.decode (F.encode x)) = f :=
    funext F.factor
  simpa only [hfun] using hcomp

variable {D : Type u} [Preorder D] {f : D → D}

/-- The factorization clause of source item `lem_square`: if `f` factors
through `B`, then `f²` factors through the same `B`. -/
def square (F : ScottFactorization f B) :
    ScottFactorization (fun x => f (f x)) B where
  encode := F.encode
  decode := fun b => f (F.decode b)
  encode_continuous := F.encode_continuous
  decode_continuous := F.continuous.comp F.decode_continuous
  factor := by
    intro x
    rw [F.factor]

end ScottFactorization

end Factorization

section Squares

variable {D : Type u} [Preorder D]

/-- The square of a bundled Scott-continuous endomap. -/
def squareMap (f : ScottContFun D D) : ScottContFun D D where
  toFun := fun x => f (f x)
  continuous := f.continuous.comp f.continuous

@[simp]
theorem squareMap_apply (f : ScottContFun D D) (x : D) :
    squareMap f x = f (f x) :=
  rfl

/-- The two-index square family from source item `lem_square`. -/
def squareSet (h : Nat → Nat → ScottContFun D D) :
    Set (ScottContFun D D) :=
  Set.range fun ij : Nat × Nat => squareMap (h ij.1 ij.2)

/-- Explicit pairwise square-refinement condition.  The full source proof
derives this condition from finite separation and interpolation; exposing it
also makes the purely directed-order core reusable independently. -/
def PairwiseSquareRefinement
    (h : Nat → Nat → ScottContFun D D) : Prop :=
  ∀ i j k l : Nat, ∃ p q : Nat,
    squareMap (h i j) ≤ squareMap (h p q) ∧
      squareMap (h k l) ≤ squareMap (h p q)

/-- Way-below cofinality of the square family, the hypothesis needed to prove
that its pointwise supremum is the identity. -/
def SquaresWayBelowCofinal
    (h : Nat → Nat → ScottContFun D D) : Prop :=
  ∀ x y : D, y ≪ x → ∃ i j : Nat, y ≤ squareMap (h i j) x

/-- The manuscript hypotheses imply way-below cofinality of the squares.
This formalizes the second interpolation argument in source item `lem_square`:
one common outer index and one common inner index are obtained by taking maxima
of the two constraints at each level. -/
theorem NestedApproximation.squaresWayBelowCofinal
    (A : NestedApproximation D) (hD : IsContinuousDomain D) :
    SquaresWayBelowCofinal A.inner := by
  intro x y hyx
  rcases fourStepInterpolation hD hyx with
    ⟨r, s, t, hyr, hrs, hst, htx⟩
  rcases htx (A.outer.range_directed x) (A.outer.pointwise_sup x) le_rfl with
    ⟨_at, ⟨it, rfl⟩, htit⟩
  rcases hrs (A.outer.range_directed s) (A.outer.pointwise_sup s) le_rfl with
    ⟨_ar, ⟨ir, rfl⟩, hrir⟩
  let i : Nat := max it ir
  have hti : t ≤ A.outer.map i x :=
    le_trans htit (A.outer.monotone (Nat.le_max_left it ir) x)
  have hri : r ≤ A.outer.map i s :=
    le_trans hrir (A.outer.monotone (Nat.le_max_right it ir) s)
  have hsi : s ≪ A.outer.map i x :=
    prop_2_2_2_2 le_rfl hst hti
  have hyi : y ≪ A.outer.map i s :=
    prop_2_2_2_2 le_rfl hyr hri
  rcases hsi (A.inner_range_directed i x)
      (A.inner_pointwise_sup i x) le_rfl with
    ⟨_hs, ⟨js, rfl⟩, hsjs⟩
  rcases hyi (A.inner_range_directed i s)
      (A.inner_pointwise_sup i s) le_rfl with
    ⟨_hy, ⟨jy, rfl⟩, hyjy⟩
  let j : Nat := max js jy
  have hsj : s ≤ A.inner i j x :=
    le_trans hsjs (A.inner_monotone i (Nat.le_max_left js jy) x)
  have hyj : y ≤ A.inner i j s :=
    le_trans hyjy (A.inner_monotone i (Nat.le_max_right js jy) s)
  refine ⟨i, j, ?_⟩
  exact le_trans hyj ((A.inner i j).continuous.monotone hsj)

/-- The manuscript hypotheses imply pairwise refinement of the squares.  The
proof tags the two finite separators, interpolates four times at every tagged
separator point, and uses `exists_nat_forall_fintype` twice to choose one outer
index and one inner index satisfying all constraints simultaneously.  This is
the directedness argument of source item `lem_square`. -/
theorem NestedApproximation.pairwiseSquareRefinement
    (A : NestedApproximation D) (hD : IsContinuousDomain D) :
    PairwiseSquareRefinement A.inner := by
  classical
  intro i1 j1 i2 j2
  let q1 : ScottContFun D D := A.inner i1 j1
  let q2 : ScottContFun D D := A.inner i2 j2
  rcases A.inner_finitelySeparated i1 j1 with
    ⟨M1, hM1finite, hM1⟩
  rcases A.inner_finitelySeparated i2 j2 with
    ⟨M2, hM2finite, hM2⟩
  let K : Set (D ⊕ D) :=
    Sum.inl '' M1 ∪ Sum.inr '' M2
  have hKfinite : K.Finite := by
    exact (hM1finite.image (fun m => Sum.inl m)).union
      (hM2finite.image (fun m => Sum.inr m))
  letI : Fintype {z : D ⊕ D // z ∈ K} := hKfinite.fintype
  let point : {z : D ⊕ D // z ∈ K} → D := fun z =>
    match z.1 with
    | Sum.inl m => m
    | Sum.inr m => m
  let q : {z : D ⊕ D // z ∈ K} → ScottContFun D D := fun z =>
    match z.1 with
    | Sum.inl _ => q1
    | Sum.inr _ => q2
  have hqWayBelow :
      ∀ z : {z : D ⊕ D // z ∈ K}, q z (point z) ≪ point z := by
    intro z
    rcases z with ⟨z, hz⟩
    cases z with
    | inl m =>
        change q1 m ≪ m
        exact IsFinitelySeparated.wayBelow q1.continuous
          (A.inner_finitelySeparated i1 j1) m
    | inr m =>
        change q2 m ≪ m
        exact IsFinitelySeparated.wayBelow q2.continuous
          (A.inner_finitelySeparated i2 j2) m
  let chain :
      ∀ z : {z : D ⊕ D // z ∈ K},
        FourStepChain (q z (point z)) (point z) := fun z =>
    Classical.choice (fourStepChain_nonempty hD (hqWayBelow z))
  have hOuterExists :
      ∀ z : {z : D ⊕ D // z ∈ K}, ∃ n : Nat,
        (chain z).t ≤ A.outer.map n (point z) ∧
          (chain z).r ≤ A.outer.map n (chain z).s := by
    intro z
    rcases (chain z).fourth
        (A.outer.range_directed (point z))
        (A.outer.pointwise_sup (point z)) le_rfl with
      ⟨_at, ⟨it, rfl⟩, htit⟩
    rcases (chain z).second
        (A.outer.range_directed (chain z).s)
        (A.outer.pointwise_sup (chain z).s) le_rfl with
      ⟨_ar, ⟨ir, rfl⟩, hrir⟩
    refine ⟨max it ir, ?_, ?_⟩
    · exact le_trans htit
        (A.outer.monotone (Nat.le_max_left it ir) (point z))
    · exact le_trans hrir
        (A.outer.monotone (Nat.le_max_right it ir) (chain z).s)
  obtain ⟨i, hi⟩ := exists_nat_forall_fintype
    (fun z n =>
      (chain z).t ≤ A.outer.map n (point z) ∧
        (chain z).r ≤ A.outer.map n (chain z).s)
    hOuterExists (by
      intro z m n hm hmn
      exact ⟨le_trans hm.1 (A.outer.monotone hmn (point z)),
        le_trans hm.2 (A.outer.monotone hmn (chain z).s)⟩)
  have hInnerExists :
      ∀ z : {z : D ⊕ D // z ∈ K}, ∃ n : Nat,
        (chain z).s ≤ A.inner i n (point z) ∧
          q z (point z) ≤ A.inner i n (chain z).s := by
    intro z
    have hst : (chain z).s ≪ A.outer.map i (point z) :=
      prop_2_2_2_2 le_rfl (chain z).third (hi z).1
    have hqr : q z (point z) ≪ A.outer.map i (chain z).s :=
      prop_2_2_2_2 le_rfl (chain z).first (hi z).2
    rcases hst (A.inner_range_directed i (point z))
        (A.inner_pointwise_sup i (point z)) le_rfl with
      ⟨_hs, ⟨js, rfl⟩, hsjs⟩
    rcases hqr (A.inner_range_directed i (chain z).s)
        (A.inner_pointwise_sup i (chain z).s) le_rfl with
      ⟨_hq, ⟨jq, rfl⟩, hqjq⟩
    refine ⟨max js jq, ?_, ?_⟩
    · exact le_trans hsjs
        (A.inner_monotone i (Nat.le_max_left js jq) (point z))
    · exact le_trans hqjq
        (A.inner_monotone i (Nat.le_max_right js jq) (chain z).s)
  obtain ⟨j, hj⟩ := exists_nat_forall_fintype
    (fun z n =>
      (chain z).s ≤ A.inner i n (point z) ∧
        q z (point z) ≤ A.inner i n (chain z).s)
    hInnerExists (by
      intro z m n hm hmn
      exact ⟨le_trans hm.1 (A.inner_monotone i hmn (point z)),
        le_trans hm.2 (A.inner_monotone i hmn (chain z).s)⟩)
  refine ⟨i, j, ?_, ?_⟩
  · intro x
    rcases hM1 x with ⟨m, hmM1, hqxm, hmx⟩
    let z : {z : D ⊕ D // z ∈ K} :=
      ⟨Sum.inl m, by
        dsimp [K]
        exact Or.inl ⟨m, hmM1, rfl⟩⟩
    have hsH : (chain z).s ≤ A.inner i j m := by
      simpa only [point, z] using (hj z).1
    have hqH : q1 m ≤ A.inner i j (chain z).s := by
      simpa only [q, point, z] using (hj z).2
    change q1 (q1 x) ≤ A.inner i j (A.inner i j x)
    calc
      q1 (q1 x) ≤ q1 m := q1.continuous.monotone hqxm
      _ ≤ A.inner i j (chain z).s := hqH
      _ ≤ A.inner i j (A.inner i j m) :=
        (A.inner i j).continuous.monotone hsH
      _ ≤ A.inner i j (A.inner i j x) :=
        (A.inner i j).continuous.monotone
          ((A.inner i j).continuous.monotone hmx)
  · intro x
    rcases hM2 x with ⟨m, hmM2, hqxm, hmx⟩
    let z : {z : D ⊕ D // z ∈ K} :=
      ⟨Sum.inr m, by
        dsimp [K]
        exact Or.inr ⟨m, hmM2, rfl⟩⟩
    have hsH : (chain z).s ≤ A.inner i j m := by
      simpa only [point, z] using (hj z).1
    have hqH : q2 m ≤ A.inner i j (chain z).s := by
      simpa only [q, point, z] using (hj z).2
    change q2 (q2 x) ≤ A.inner i j (A.inner i j x)
    calc
      q2 (q2 x) ≤ q2 m := q2.continuous.monotone hqxm
      _ ≤ A.inner i j (chain z).s := hqH
      _ ≤ A.inner i j (A.inner i j m) :=
        (A.inner i j).continuous.monotone hsH
      _ ≤ A.inner i j (A.inner i j x) :=
        (A.inner i j).continuous.monotone
          ((A.inner i j).continuous.monotone hmx)

theorem squareSet_directed
    {h : Nat → Nat → ScottContFun D D}
    (hrefine : PairwiseSquareRefinement h) :
    DirectedSet (squareSet h) := by
  constructor
  · exact ⟨squareMap (h 0 0), ⟨(0, 0), rfl⟩⟩
  · intro f hf g hg
    rcases hf with ⟨⟨i, j⟩, rfl⟩
    rcases hg with ⟨⟨k, l⟩, rfl⟩
    rcases hrefine i j k l with ⟨p, q, hipq, hkpq⟩
    exact ⟨squareMap (h p q), ⟨(p, q), rfl⟩, hipq, hkpq⟩

/-- The square family has pointwise supremum the identity whenever it is
way-below cofinal and every underlying map is below the identity. -/
theorem squareSet_pointwise_isSup
    (hD : IsContinuousDomain D)
    {h : Nat → Nat → ScottContFun D D}
    (hbelow : ∀ i j : Nat, ∀ x : D, h i j x ≤ x)
    (hcofinal : SquaresWayBelowCofinal h) (x : D) :
    IsSup ((fun f : ScottContFun D D => f x) '' squareSet h) x := by
  constructor
  · intro y hy
    rcases hy with ⟨f, hf, rfl⟩
    rcases hf with ⟨⟨i, j⟩, rfl⟩
    exact le_trans (hbelow i j (h i j x)) (hbelow i j x)
  · intro z hz
    have hwaySup : IsSup (wayBelowLower x) x :=
      continuous_wayBelowLower_isSup hD x
    apply hwaySup.2 z
    intro y hy
    rcases hcofinal x y hy with ⟨i, j, hyij⟩
    exact le_trans hyij (hz ⟨squareMap (h i j), ⟨(i, j), rfl⟩, rfl⟩)

/-- An increasing sequence contained in `S` and cofinal in `S`. -/
def IsIncreasingCofinalSequence
    {A : Type u} [Preorder A] (S : Set A) (c : Nat → A) : Prop :=
  (∀ n : Nat, c n ∈ S) ∧ Monotone c ∧
    ∀ a ∈ S, ∃ n : Nat, a ≤ c n

/-- Every directed two-index square family contains an increasing cofinal
sequence.  This is the countability clause of source item `lem_square`; the
enumeration is the canonical pairing of two natural indices. -/
theorem squareSet_exists_increasingCofinalSequence
    {h : Nat → Nat → ScottContFun D D}
    (hdir : DirectedSet (squareSet h)) :
    ∃ c : Nat → ScottContFun D D,
      IsIncreasingCofinalSequence (squareSet h) c := by
  let e : Nat → ScottContFun D D := fun n =>
    squareMap (h (Nat.unpair n).1 (Nat.unpair n).2)
  have he : ∀ n : Nat, e n ∈ squareSet h := by
    intro n
    exact ⟨Nat.unpair n, rfl⟩
  let c : Nat → ScottContFun D D :=
    DirectedSet.cumulativeUpper hdir e he
  refine ⟨c, ?_, DirectedSet.cumulativeUpper_monotone hdir e he, ?_⟩
  · intro n
    exact DirectedSet.cumulativeUpper_mem hdir e he n
  · intro f hf
    rcases hf with ⟨⟨i, j⟩, rfl⟩
    refine ⟨Nat.pair i j, ?_⟩
    have hle := DirectedSet.le_cumulativeUpper_self hdir e he (Nat.pair i j)
    simpa [e, Nat.unpair_pair] using hle

/-- The pointwise supremum property passes from a directed square family to
any increasing sequence contained in and cofinal in that family. -/
theorem cofinalSequence_pointwise_isSup
    {h : Nat → Nat → ScottContFun D D}
    {c : Nat → ScottContFun D D}
    (hc : IsIncreasingCofinalSequence (squareSet h) c)
    (hsup : ∀ x : D,
      IsSup ((fun f : ScottContFun D D => f x) '' squareSet h) x)
    (x : D) :
    IsSup (Set.range (fun n => c n x)) x := by
  constructor
  · intro y hy
    rcases hy with ⟨n, rfl⟩
    exact (hsup x).1 ⟨c n, hc.1 n, rfl⟩
  · intro z hz
    apply (hsup x).2 z
    intro y hy
    rcases hy with ⟨f, hf, rfl⟩
    rcases hc.2.2 f hf with ⟨n, hfn⟩
    exact le_trans (hfn x) (hz ⟨n, rfl⟩)

/-- The complete valuation-free conclusion of source item `lem_square`.  The
factorization-through-the-same-object clause is represented separately by
`ScottFactorization.square`, because the intermediate object is not part of
the nested approximation data. -/
structure SquareRefinementConclusion
    (h : Nat → Nat → ScottContFun D D) : Prop where
  directed : DirectedSet (squareSet h)
  pointwise_sup :
    ∀ x : D, IsSup ((fun f : ScottContFun D D => f x) '' squareSet h) x
  increasing_cofinal_sequence :
    ∃ c : Nat → ScottContFun D D,
      IsIncreasingCofinalSequence (squareSet h) c
  finitelySeparated :
    ∀ f : ScottContFun D D, f ∈ squareSet h → IsFinitelySeparated f

/-- Source item `lem_square` (lines 1431--1455), abstract core.  Under exactly
the manuscript's nested approximation and continuous-domain hypotheses, the
squares form a directed family with pointwise supremum the identity, contain
an increasing cofinal sequence, and are all finitely separated. -/
theorem NestedApproximation.squareRefinement
    (A : NestedApproximation D) (hD : IsContinuousDomain D) :
    SquareRefinementConclusion A.inner := by
  have hrefine : PairwiseSquareRefinement A.inner :=
    A.pairwiseSquareRefinement hD
  have hdir : DirectedSet (squareSet A.inner) :=
    squareSet_directed hrefine
  have hcofinal : SquaresWayBelowCofinal A.inner :=
    A.squaresWayBelowCofinal hD
  refine ⟨hdir, ?_, squareSet_exists_increasingCofinalSequence hdir, ?_⟩
  · intro x
    exact squareSet_pointwise_isSup hD A.inner_below_id hcofinal x
  · intro f hf
    rcases hf with ⟨⟨i, j⟩, rfl⟩
    change IsFinitelySeparated
      (fun x => A.inner i j (A.inner i j x))
    exact (A.inner_finitelySeparated i j).square

/-- Literal domain-hypothesis wrapper for source item `lem_square`.  The
conclusion's factorization clause remains the separate theorem
`ScottFactorization.square`, so the source item is represented as a deliberate
split rather than by hiding a heterogeneous intermediate type in this record. -/
theorem lem_square
    [PartialOrder D] (hD : IsContinuousDcpo D)
    (A : NestedApproximation D) :
    SquareRefinementConclusion A.inner :=
  A.squareRefinement hD.hasBasis

/-- A packaged consequence of `lem_square`: the increasing cofinal sequence
of squares is itself an FS approximate identity, and every selected map is a
member of the square family. -/
theorem NestedApproximation.existsSquaredFSApproximateIdentity
    (A : NestedApproximation D) (hD : IsContinuousDomain D) :
    ∃ C : FSApproximateIdentity D,
      ∀ n : Nat, C.map n ∈ squareSet A.inner := by
  have hresult := A.squareRefinement hD
  rcases hresult.increasing_cofinal_sequence with ⟨c, hc⟩
  have hcsep : ∀ n : Nat, IsFinitelySeparated (c n) := by
    intro n
    exact hresult.finitelySeparated (c n) (hc.1 n)
  let C : FSApproximateIdentity D := {
    map := c
    monotone := hc.2.1
    below_id := fun n x => (hcsep n).below_id x
    pointwise_sup := fun x =>
      cofinalSequence_pointwise_isSup hc hresult.pointwise_sup x
    finitelySeparated := hcsep }
  exact ⟨C, hc.1⟩

end Squares

section Retracts

variable {D : Type u} {E : Type v} [Preorder D] [Preorder E]

/-- Pull a Scott-continuous endomap on `E` back along a continuous
section--retraction pair `D ⇄ E`. -/
def pullbackMap (sr : ContinuousSectionRetractionPair D E)
    (f : ScottContFun E E) : ScottContFun D D where
  toFun := fun x => sr.r (f (sr.s x))
  continuous := sr.continuous_r.comp (f.continuous.comp sr.continuous_s)

@[simp]
theorem pullbackMap_apply (sr : ContinuousSectionRetractionPair D E)
    (f : ScottContFun E E) (x : D) :
    pullbackMap sr f x = sr.r (f (sr.s x)) :=
  rfl

/-- Finite separation is preserved by pullback along a retraction; the finite
separator is the retraction image of the original separator. -/
theorem IsFinitelySeparated.pullback
    (sr : ContinuousSectionRetractionPair D E)
    {f : ScottContFun E E} (hf : IsFinitelySeparated f) :
    IsFinitelySeparated (pullbackMap sr f) := by
  simpa only [pullbackMap_apply] using
    hf.sandwich sr.continuous_r.monotone
      (fun x => le_of_eq (sr.retract x))

namespace IncreasingApproximateIdentity

/-- Abstract retract-closure theorem behind source item `cor_retract`: an
increasing Scott-continuous approximate identity pulls back along a continuous
section--retraction pair. -/
def pullback (A : IncreasingApproximateIdentity E)
    (sr : ContinuousSectionRetractionPair D E) :
    IncreasingApproximateIdentity D where
  map n := pullbackMap sr (A.map n)
  monotone := by
    intro m n hmn x
    exact sr.continuous_r.monotone (A.monotone hmn (sr.s x))
  below_id := by
    intro n x
    calc
      sr.r (A.map n (sr.s x)) ≤ sr.r (sr.s x) :=
        sr.continuous_r.monotone (A.below_id n (sr.s x))
      _ = x := sr.retract x
  pointwise_sup := by
    intro x
    have hsup := sr.continuous_r.maps_isSup
      (A.range_directed (sr.s x)) (A.pointwise_sup (sr.s x))
    have himage :
        sr.r '' Set.range (fun n => A.map n (sr.s x)) =
          Set.range (fun n => pullbackMap sr (A.map n) x) := by
      ext y
      constructor
      · rintro ⟨z, ⟨n, rfl⟩, rfl⟩
        exact ⟨n, rfl⟩
      · rintro ⟨n, rfl⟩
        exact ⟨A.map n (sr.s x), ⟨n, rfl⟩, rfl⟩
    rw [himage] at hsup
    simpa only [sr.retract x] using hsup

end IncreasingApproximateIdentity

namespace FSApproximateIdentity

/-- FS approximate identities are preserved by continuous retracts. -/
def pullback (A : FSApproximateIdentity E)
    (sr : ContinuousSectionRetractionPair D E) :
    FSApproximateIdentity D where
  toIncreasingApproximateIdentity :=
    A.toIncreasingApproximateIdentity.pullback sr
  finitelySeparated n := (A.finitelySeparated n).pullback sr

end FSApproximateIdentity

namespace ScottFactorization

variable {B : Type w} [Preorder B] {f : E → E}

/-- A factorization through `B` pulls back along a continuous retraction and
still factors through the same object `B`.  This is the factorization
calculation used in source item `cor_retract`. -/
def pullback (F : ScottFactorization f B)
    (sr : ContinuousSectionRetractionPair D E) :
    ScottFactorization (fun x => sr.r (f (sr.s x))) B where
  encode := fun x => F.encode (sr.s x)
  decode := fun b => sr.r (F.decode b)
  encode_continuous := F.encode_continuous.comp sr.continuous_s
  decode_continuous := sr.continuous_r.comp F.decode_continuous
  factor := by
    intro x
    rw [F.factor]

end ScottFactorization

end Retracts

end AbstractApproximation
end FiniteValuationApproximable
