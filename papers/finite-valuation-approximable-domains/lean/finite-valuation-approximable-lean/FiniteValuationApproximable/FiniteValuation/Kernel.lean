import FiniteValuationApproximable.FiniteValuation.Probability
import FiniteValuationApproximable.Polytope

/-!
# Finite stochastic kernels and barycentric reconstruction

This file formalizes the finite/discrete algebraic core of the section
`Finite stochastic-kernel approximations and kernel lifting` in
`main (17).tex` (source SHA-256
`4b2e65f0f96347bea4df7571e8993ad6e888c0ff7181c1305c5056880365ac94`).

The results proved here are deliberately bounded to what the current API
expresses exactly:

* finite Kleisli extension for subprobability and probability vectors;
* the finite Fubini/integration formula and both unit laws and associativity;
* monotonicity of Kleisli extension in a stochastic-order-preserving kernel;
* finite pushforward, its integration formula, and the Dirac sandwich for
  labels bounded on the positive support;
* barycentric reconstruction of monotone tables, monotonicity of the
  reconstruction map, and the pointwise table sandwich from the manuscript.

The source's continuous-valuation monad on an arbitrary dcpo, Scott
continuity, directed-supremum/DCT arguments, and the Jones--Plotkin local
continuity theorems are not available in the finite-vector API.  They are not
asserted here as assumptions or hidden in structures.
-/

set_option autoImplicit false
set_option linter.unnecessarySimpa false

universe u v w z

namespace FiniteValuationApproximable

open scoped BigOperators
open Set
open SubprobabilityVector

section FiniteKleisli

variable {X : Type u} {Y : Type v} {Z : Type w}
variable [Fintype X] [Fintype Y] [Fintype Z]

/-- Finite Kleisli extension for subprobability vectors.  Its coefficient at
`y` is the finite sum `sum_x mu_x * k(x)_y`. -/
noncomputable def finiteBind (mu : SubprobabilityVector X)
    (k : X -> SubprobabilityVector Y) : SubprobabilityVector Y where
  coeff y := ∑ x, mu x * k x y
  coeff_nonneg y :=
    Finset.sum_nonneg fun x _ =>
      mul_nonneg (mu.coeff_nonneg x) ((k x).coeff_nonneg y)
  total_le_one := by
    calc
      (∑ y, ∑ x, mu x * k x y) = ∑ x, ∑ y, mu x * k x y := Finset.sum_comm
      _ = ∑ x, mu x * (k x).totalMass := by
        apply Finset.sum_congr rfl
        intro x hx
        change (∑ y, mu x * k x y) = mu x * ∑ y, k x y
        exact (Finset.mul_sum _ _ _).symm
      _ <= ∑ x, mu x * 1 := by
        apply Finset.sum_le_sum
        intro x hx
        exact mul_le_mul_of_nonneg_left (k x).totalMass_le_one (mu.coeff_nonneg x)
      _ = mu.totalMass := by simp [SubprobabilityVector.totalMass]
      _ <= 1 := mu.totalMass_le_one

@[simp]
theorem finiteBind_apply (mu : SubprobabilityVector X)
    (k : X -> SubprobabilityVector Y) (y : Y) :
    finiteBind mu k y = ∑ x, mu x * k x y :=
  rfl

/-- Finite Fubini, or equivalently the defining integration law for Kleisli
extension. -/
theorem weightedSum_finiteBind (mu : SubprobabilityVector X)
    (k : X -> SubprobabilityVector Y) (g : Y -> Real) :
    weightedSum (finiteBind mu k) g =
      weightedSum mu (fun x => weightedSum (k x) g) := by
  classical
  simp only [weightedSum, finiteBind_apply]
  calc
    (∑ y, (∑ x, mu x * k x y) * g y) =
        ∑ y, ∑ x, (mu x * k x y) * g y := by
          apply Finset.sum_congr rfl
          intro y hy
          rw [Finset.sum_mul]
    _ = ∑ x, ∑ y, (mu x * k x y) * g y := Finset.sum_comm
    _ = ∑ x, mu x * ∑ y, k x y * g y := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y hy
      ring

@[simp]
theorem finiteBind_dirac_left (x : X) (k : X -> SubprobabilityVector Y) :
    finiteBind (dirac x) k = k x := by
  apply SubprobabilityVector.ext
  intro y
  classical
  simp [finiteBind, dirac]

@[simp]
theorem finiteBind_dirac_right (mu : SubprobabilityVector X) :
    finiteBind mu (fun x => dirac x) = mu := by
  apply SubprobabilityVector.ext
  intro y
  classical
  simp [finiteBind, dirac]

@[simp]
theorem finiteBind_zero_left (k : X -> SubprobabilityVector Y) :
    finiteBind (0 : SubprobabilityVector X) k = 0 := by
  apply SubprobabilityVector.ext
  intro y
  simp [finiteBind]

/-- Associativity of finite subprobability Kleisli extension. -/
theorem finiteBind_assoc (mu : SubprobabilityVector X)
    (k : X -> SubprobabilityVector Y) (h : Y -> SubprobabilityVector Z) :
    finiteBind (finiteBind mu k) h =
      finiteBind mu (fun x => finiteBind (k x) h) := by
  apply SubprobabilityVector.ext
  intro z
  classical
  simp only [finiteBind_apply]
  calc
    (∑ y, (∑ x, mu x * k x y) * h y z) =
        ∑ y, ∑ x, (mu x * k x y) * h y z := by
          apply Finset.sum_congr rfl
          intro y hy
          rw [Finset.sum_mul]
    _ = ∑ x, ∑ y, (mu x * k x y) * h y z := Finset.sum_comm
    _ = ∑ x, mu x * ∑ y, k x y * h y z := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y hy
      ring

/-- A normalized finite kernel sends a probability vector to a probability
vector. -/
noncomputable def probabilityBind (mu : ProbabilityVector X)
    (k : X -> ProbabilityVector Y) : ProbabilityVector Y := by
  let result := finiteBind mu.1 (fun x => (k x).1)
  refine ⟨result, ?_⟩
  change (∑ y, ∑ x, mu x * k x y) = 1
  calc
    (∑ y, ∑ x, mu x * k x y) = ∑ x, ∑ y, mu x * k x y := Finset.sum_comm
    _ = ∑ x, mu x * (∑ y, k x y) := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.mul_sum]
    _ = ∑ x, mu x := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [show (∑ y, k x y) = 1 from (k x).2]
      ring
    _ = 1 := mu.2

@[simp]
theorem probabilityBind_apply (mu : ProbabilityVector X)
    (k : X -> ProbabilityVector Y) (y : Y) :
    probabilityBind mu k y = ∑ x, mu x * k x y :=
  rfl

@[simp]
theorem probabilityBind_dirac_left (x : X) (k : X -> ProbabilityVector Y) :
    probabilityBind (diracProbability x) k = k x := by
  apply ProbabilityVector.ext
  intro y
  classical
  simp [probabilityBind, diracProbability, dirac]

@[simp]
theorem probabilityBind_dirac_right (mu : ProbabilityVector X) :
    probabilityBind mu (fun x => diracProbability x) = mu := by
  apply ProbabilityVector.ext
  intro y
  classical
  simp [probabilityBind, diracProbability, dirac]

/-- Associativity of finite probability Kleisli extension. -/
theorem probabilityBind_assoc (mu : ProbabilityVector X)
    (k : X -> ProbabilityVector Y) (h : Y -> ProbabilityVector Z) :
    probabilityBind (probabilityBind mu k) h =
      probabilityBind mu (fun x => probabilityBind (k x) h) := by
  apply ProbabilityVector.ext
  intro z
  change finiteBind (finiteBind mu.1 (fun x => (k x).1)) (fun y => (h y).1) z =
    finiteBind mu.1 (fun x => finiteBind (k x).1 (fun y => (h y).1)) z
  rw [finiteBind_assoc]

end FiniteKleisli

section KleisliOrder

variable {X : Type u} {Y : Type v}
variable [Fintype X] [Fintype Y] [PartialOrder Y]

/-- Kleisli extension is monotone in the kernel, pointwise in stochastic
order. -/
theorem finiteBind_mono_kernel (mu : SubprobabilityVector X)
    {k h : X -> SubprobabilityVector Y} (hkh : forall x, k x <= h x) :
    finiteBind mu k <= finiteBind mu h := by
  rw [stochasticLE_iff_weightedSum_le]
  intro g hg hg0
  rw [weightedSum_finiteBind, weightedSum_finiteBind]
  unfold weightedSum
  apply Finset.sum_le_sum
  intro x hx
  exact mul_le_mul_of_nonneg_left
    ((stochasticLE_iff_weightedSum_le.mp (hkh x)) g hg hg0)
    (mu.coeff_nonneg x)

/-- The same kernel monotonicity with hypotheses only on the positive support
of the input vector. -/
theorem finiteBind_mono_kernel_on_support (mu : SubprobabilityVector X)
    {k h : X -> SubprobabilityVector Y}
    (hkh : forall x, 0 < mu x -> k x <= h x) :
    finiteBind mu k <= finiteBind mu h := by
  rw [stochasticLE_iff_weightedSum_le]
  intro g hg hg0
  rw [weightedSum_finiteBind, weightedSum_finiteBind]
  unfold weightedSum
  apply Finset.sum_le_sum
  intro x hx
  by_cases hzero : mu x = 0
  · simp [hzero]
  · have hpos : 0 < mu x := lt_of_le_of_ne (mu.coeff_nonneg x) (Ne.symm hzero)
    exact mul_le_mul_of_nonneg_left
      ((stochasticLE_iff_weightedSum_le.mp (hkh x hpos)) g hg hg0)
      (mu.coeff_nonneg x)

/-- Kleisli extension is monotone in its input whenever the kernel is
stochastic-order preserving.  This is the exact finite analogue of the local
valuation monotonicity used in the manuscript. -/
theorem finiteBind_mono_input [PartialOrder X]
    {mu nu : SubprobabilityVector X} (hmunu : mu <= nu)
    {k : X -> SubprobabilityVector Y} (hk : Monotone k) :
    finiteBind mu k <= finiteBind nu k := by
  rw [stochasticLE_iff_weightedSum_le]
  intro g hg hg0
  rw [weightedSum_finiteBind, weightedSum_finiteBind]
  apply (stochasticLE_iff_weightedSum_le.mp hmunu)
  · intro x x' hxx'
    exact (stochasticLE_iff_weightedSum_le.mp (hk hxx')) g hg hg0
  · intro x
    unfold weightedSum
    exact Finset.sum_nonneg fun y hy =>
      mul_nonneg ((k x).coeff_nonneg y) (hg0 y)

theorem finiteBind_mono [PartialOrder X]
    {mu nu : SubprobabilityVector X} (hmunu : mu <= nu)
    {k h : X -> SubprobabilityVector Y} (hk : Monotone k)
    (hkh : forall x, k x <= h x) :
    finiteBind mu k <= finiteBind nu h :=
  le_trans (finiteBind_mono_input hmunu hk) (finiteBind_mono_kernel nu hkh)

end KleisliOrder

section FinitePushforward

variable {X : Type u} {Y : Type v} {Z : Type w}
variable [Fintype X] [Fintype Y] [Fintype Z]

/-- Pushforward of a finite subprobability vector along a map of finite
carriers. -/
noncomputable def finitePushforward (mu : SubprobabilityVector X) (f : X -> Y) :
    SubprobabilityVector Y :=
  finiteBind mu (fun x => dirac (f x))

/-- Pushforward of a finite probability vector. -/
noncomputable def probabilityPushforward (mu : ProbabilityVector X) (f : X -> Y) :
    ProbabilityVector Y :=
  probabilityBind mu (fun x => diracProbability (f x))

@[simp]
theorem finitePushforward_apply (mu : SubprobabilityVector X) (f : X -> Y) (y : Y) :
    finitePushforward mu f y = ∑ x, mu x * dirac (f x) y :=
  rfl

@[simp]
theorem probabilityPushforward_apply (mu : ProbabilityVector X) (f : X -> Y) (y : Y) :
    probabilityPushforward mu f y = ∑ x, mu x * dirac (f x) y :=
  rfl

/-- Integration against a finite pushforward is integration after
composition. -/
theorem weightedSum_finitePushforward (mu : SubprobabilityVector X)
    (f : X -> Y) (g : Y -> Real) :
    weightedSum (finitePushforward mu f) g = weightedSum mu (g ∘ f) := by
  rw [finitePushforward, weightedSum_finiteBind]
  unfold weightedSum Function.comp
  apply Finset.sum_congr rfl
  intro x hx
  change mu x * weightedSum (dirac (f x)) g = mu x * g (f x)
  classical
  simp [weightedSum, dirac]

@[simp]
theorem finitePushforward_id (mu : SubprobabilityVector X) :
    finitePushforward mu id = mu := by
  simpa [finitePushforward] using finiteBind_dirac_right mu

theorem finitePushforward_comp (mu : SubprobabilityVector X)
    (f : X -> Y) (g : Y -> Z) :
    finitePushforward (finitePushforward mu f) g = finitePushforward mu (g ∘ f) := by
  apply SubprobabilityVector.ext
  intro z
  classical
  simp [finitePushforward, finiteBind_assoc]

@[simp]
theorem probabilityPushforward_id (mu : ProbabilityVector X) :
    probabilityPushforward mu id = mu := by
  simpa [probabilityPushforward] using probabilityBind_dirac_right mu

theorem probabilityPushforward_comp (mu : ProbabilityVector X)
    (f : X -> Y) (g : Y -> Z) :
    probabilityPushforward (probabilityPushforward mu f) g =
      probabilityPushforward mu (g ∘ f) := by
  unfold probabilityPushforward
  rw [probabilityBind_assoc]
  congr 1
  funext x
  simp

@[simp]
theorem probabilityPushforward_dirac (x : X) (f : X -> Y) :
    probabilityPushforward (diracProbability x) f = diracProbability (f x) := by
  simp [probabilityPushforward]

/-- A finite probability pushforward along a constant map is Dirac. -/
theorem probabilityPushforward_const (mu : ProbabilityVector X) (y : Y) :
    (probabilityPushforward mu (fun _ => y)).1 = dirac y := by
  apply SubprobabilityVector.ext
  intro y'
  classical
  change (∑ x, mu x * (if y' = y then 1 else 0)) =
    (if y' = y then 1 else 0)
  by_cases h : y' = y
  · subst y'
    simpa [SubprobabilityVector.totalMass] using mu.2
  · simp [h]

/-- The finite counterpart of the factorization used in the source's kernel
lifting proof: extending a pushed-forward kernel equals pushforward after
extending the kernel before its labels. -/
theorem finiteBind_pushforward_factorization (mu : SubprobabilityVector X)
    (p : X -> SubprobabilityVector Y) (f : Y -> Z) :
    finiteBind mu (fun x => finitePushforward (p x) f) =
      finitePushforward (finiteBind mu p) f := by
  unfold finitePushforward
  exact (finiteBind_assoc mu p (fun y => dirac (f y))).symm

/-- Normalized finite-kernel factorization
`(V(f) o p)^dagger = V(f) o p^dagger`. -/
theorem probabilityBind_pushforward_factorization (mu : ProbabilityVector X)
    (p : X -> ProbabilityVector Y) (f : Y -> Z) :
    probabilityBind mu (fun x => probabilityPushforward (p x) f) =
      probabilityPushforward (probabilityBind mu p) f := by
  unfold probabilityPushforward
  exact (probabilityBind_assoc mu p (fun y => diracProbability (f y))).symm

end FinitePushforward

section FiniteKernelFactorization

variable {X : Type u} {L : Type v} {Y : Type w}
variable [Fintype L] [Fintype Y]

/-- A discrete probability kernel is simply a family of finite probability
vectors. -/
abbrev DiscreteProbabilityKernel (X : Type u) (Y : Type v) [Fintype Y] :=
  X -> ProbabilityVector Y

/-- The manuscript's finite-kernel factorization `V(y) o p`, in the exact
case where the target carrier is finite. -/
noncomputable def finiteProbabilityKernel
    (p : X -> ProbabilityVector L) (y : L -> Y) :
    DiscreteProbabilityKernel X Y :=
  fun x => probabilityPushforward (p x) y

@[simp]
theorem finiteProbabilityKernel_apply
    (p : X -> ProbabilityVector L) (y : L -> Y) (x : X) :
    finiteProbabilityKernel p y x = probabilityPushforward (p x) y :=
  rfl

/-- Integration through a finite kernel is the finite weighted sum over its
factor carrier. -/
theorem weightedSum_finiteProbabilityKernel
    (p : X -> ProbabilityVector L) (y : L -> Y) (x : X) (g : Y -> Real) :
    weightedSum (finiteProbabilityKernel p y x).1 g =
      weightedSum (p x).1 (g ∘ y) :=
  weightedSum_finitePushforward (p x).1 y g

end FiniteKernelFactorization

section PushforwardOrder

variable {X : Type u} {Y : Type v}
variable [Fintype X] [Fintype Y] [PartialOrder Y]

/-- Changing labels upward on the positive support changes their finite
pushforward upward in stochastic order. -/
theorem finitePushforward_mono_on_support (mu : SubprobabilityVector X)
    {f g : X -> Y} (hfg : forall x, 0 < mu x -> f x <= g x) :
    finitePushforward mu f <= finitePushforward mu g := by
  rw [stochasticLE_iff_weightedSum_le]
  intro phi hphi hphi0
  rw [weightedSum_finitePushforward, weightedSum_finitePushforward]
  unfold weightedSum Function.comp
  apply Finset.sum_le_sum
  intro x hx
  by_cases hzero : mu x = 0
  · simp [hzero]
  · have hpos : 0 < mu x := lt_of_le_of_ne (mu.coeff_nonneg x) (Ne.symm hzero)
    exact mul_le_mul_of_nonneg_left (hphi (hfg x hpos)) (mu.coeff_nonneg x)

/-- The finite stochastic-kernel sandwich: a probability law whose
positive-weight labels lie in `[a,b]` lies between the two Dirac laws. -/
theorem probabilityPushforward_sandwich (mu : ProbabilityVector X)
    (f : X -> Y) {a b : Y}
    (ha : forall x, 0 < mu x -> a <= f x)
    (hb : forall x, 0 < mu x -> f x <= b) :
    dirac a <= (probabilityPushforward mu f).1 ∧
      (probabilityPushforward mu f).1 <= dirac b := by
  have hlo := finitePushforward_mono_on_support mu.1
    (f := fun _ => a) (g := f) ha
  have hhi := finitePushforward_mono_on_support mu.1
    (f := f) (g := fun _ => b) hb
  change finitePushforward mu.1 (fun _ => a) <= finitePushforward mu.1 f at hlo
  change finitePushforward mu.1 f <= finitePushforward mu.1 (fun _ => b) at hhi
  rw [show finitePushforward mu.1 f = (probabilityPushforward mu f).1 by rfl] at hlo hhi
  rw [show finitePushforward mu.1 (fun _ => a) = dirac a by
    simpa only [probabilityPushforward] using probabilityPushforward_const mu a] at hlo
  rw [show finitePushforward mu.1 (fun _ => b) = dirac b by
    simpa only [probabilityPushforward] using probabilityPushforward_const mu b] at hhi
  exact ⟨hlo, hhi⟩

end PushforwardOrder

section FiniteKernelOrder

variable {X : Type u} {L : Type v} {Y : Type w}
variable [Fintype L] [Fintype Y] [PartialOrder Y]

/-- Pointwise kernel sandwich obtained from support-wise label bounds. -/
theorem finiteProbabilityKernel_sandwich
    (p : X -> ProbabilityVector L) (y : L -> Y)
    (lower upper : X -> Y)
    (hlower : forall x l, 0 < p x l -> lower x <= y l)
    (hupper : forall x l, 0 < p x l -> y l <= upper x) (x : X) :
    dirac (lower x) <= (finiteProbabilityKernel p y x).1 ∧
      (finiteProbabilityKernel p y x).1 <= dirac (upper x) :=
  probabilityPushforward_sandwich (p x) y (hlower x) (hupper x)

end FiniteKernelOrder

section CoordinateBarycenter

variable {L : Type u} {I : Type v} [Fintype L]

/-- Coordinatewise finite barycentric reconstruction.  Missing
subprobability mass is implicitly placed at the zero vector. -/
def finiteBarycenter (mu : SubprobabilityVector L) (y : L -> I -> Real) : I -> Real :=
  fun i => weightedSum mu (fun l => y l i)

@[simp]
theorem finiteBarycenter_apply (mu : SubprobabilityVector L)
    (y : L -> I -> Real) (i : I) :
    finiteBarycenter mu y i = ∑ l, mu l * y l i :=
  rfl

@[simp]
theorem finiteBarycenter_dirac (l : L) (y : L -> I -> Real) :
    finiteBarycenter (dirac l) y = y l := by
  classical
  funext i
  simp [finiteBarycenter, weightedSum, dirac]

/-- Coordinate sandwich for a normalized barycentre.  Bounds are required
only where the coefficient is positive, matching the manuscript's support
hypothesis. -/
theorem finiteBarycenter_probability_sandwich (mu : ProbabilityVector L)
    (y : L -> I -> Real) {a b : I -> Real}
    (ha : forall l, 0 < mu l -> forall i, a i <= y l i)
    (hb : forall l, 0 < mu l -> forall i, y l i <= b i) :
    a <= finiteBarycenter mu.1 y ∧ finiteBarycenter mu.1 y <= b := by
  constructor <;> intro i
  · calc
      a i = ∑ l, mu l * a i := by
        rw [← Finset.sum_mul]
        rw [show (∑ l, mu l) = 1 from mu.2]
        simp
      _ <= ∑ l, mu l * y l i := by
        apply Finset.sum_le_sum
        intro l hl
        by_cases hzero : mu l = 0
        · simp [hzero]
        · have hpos : 0 < mu l :=
            lt_of_le_of_ne (mu.1.coeff_nonneg l) (Ne.symm hzero)
          exact mul_le_mul_of_nonneg_left (ha l hpos i) (mu.1.coeff_nonneg l)
  · calc
      (∑ l, mu l * y l i) <= ∑ l, mu l * b i := by
        apply Finset.sum_le_sum
        intro l hl
        by_cases hzero : mu l = 0
        · simp [hzero]
        · have hpos : 0 < mu l :=
            lt_of_le_of_ne (mu.1.coeff_nonneg l) (Ne.symm hzero)
          exact mul_le_mul_of_nonneg_left (hb l hpos i) (mu.1.coeff_nonneg l)
      _ = b i := by
        rw [← Finset.sum_mul]
        rw [show (∑ l, mu l) = 1 from mu.2]
        simp

/-- Subprobability barycentric reconstruction with missing mass at zero: if
the positive-support labels lie between zero and `b`, so does the
reconstruction. -/
theorem finiteBarycenter_subprobability_zero_sandwich
    (mu : SubprobabilityVector L) (y : L -> I -> Real) (b : I -> Real)
    (hb0 : forall i, 0 <= b i)
    (hy0 : forall l, 0 < mu l -> forall i, 0 <= y l i)
    (hyb : forall l, 0 < mu l -> forall i, y l i <= b i) :
    (0 : I -> Real) <= finiteBarycenter mu y ∧ finiteBarycenter mu y <= b := by
  constructor <;> intro i
  · change 0 <= ∑ l, mu l * y l i
    apply Finset.sum_nonneg
    intro l hl
    by_cases hzero : mu l = 0
    · simp [hzero]
    · have hpos : 0 < mu l :=
        lt_of_le_of_ne (mu.coeff_nonneg l) (Ne.symm hzero)
      exact mul_nonneg (mu.coeff_nonneg l) (hy0 l hpos i)
  · calc
      (∑ l, mu l * y l i) <= ∑ l, mu l * b i := by
        apply Finset.sum_le_sum
        intro l hl
        by_cases hzero : mu l = 0
        · simp [hzero]
        · have hpos : 0 < mu l :=
            lt_of_le_of_ne (mu.coeff_nonneg l) (Ne.symm hzero)
          exact mul_le_mul_of_nonneg_left (hyb l hpos i) (mu.coeff_nonneg l)
      _ = mu.totalMass * b i := by
        rw [← Finset.sum_mul]
        rfl
      _ <= 1 * b i :=
        mul_le_mul_of_nonneg_right mu.totalMass_le_one (hb0 i)
      _ = b i := one_mul _

end CoordinateBarycenter

section TableBarycenter

variable {L : Type u} {A : Type v} {P : Type w}
variable [Fintype L] [Preorder A] [Fintype P] [PartialOrder P]

/-- Barycentric reconstruction inside the manuscript's monotone-table
polytope.  At every source point it is finite Kleisli mixing of the labelled
subprobability vectors. -/
noncomputable def tableBarycenter (mu : SubprobabilityVector L)
    (y : L -> MonotoneTable A P) : MonotoneTable A P where
  toFun a := finiteBind mu (fun l => y l a)
  monotone' := by
    intro a a' haa'
    exact finiteBind_mono_kernel mu
      (fun l => MonotoneTable.monotone A P (y l) haa')

@[simp]
theorem tableBarycenter_apply (mu : SubprobabilityVector L)
    (y : L -> MonotoneTable A P) (a : A) (p : P) :
    tableBarycenter mu y a p = ∑ l, mu l * y l a p :=
  rfl

@[simp]
theorem tableBarycenter_dirac (l : L) (y : L -> MonotoneTable A P) :
    tableBarycenter (dirac l) y = y l := by
  apply MonotoneTable.ext_apply
  intro a
  exact finiteBind_dirac_left l (fun l => y l a)

/-- A probability-weighted constant family reconstructs that constant. -/
theorem tableBarycenter_const (mu : ProbabilityVector L)
    (x : MonotoneTable A P) :
    tableBarycenter mu.1 (fun _ => x) = x := by
  apply MonotoneTable.ext_coeff
  intro a p
  simp only [tableBarycenter_apply]
  rw [← Finset.sum_mul]
  rw [show (∑ l, mu l) = 1 from mu.2]
  simp

/-- The reconstruction map `e` is monotone when the label map is monotone.
This is the exact finite stochastic-order argument in the source: every
nonnegative monotone upper-set coordinate is integrated against the input
vector. -/
theorem tableBarycenter_mono [PartialOrder L]
    {y : L -> MonotoneTable A P} (hy : Monotone y) :
    Monotone (fun mu : SubprobabilityVector L => tableBarycenter mu y) := by
  intro mu nu hmunu a
  apply finiteBind_mono_input hmunu
  intro l l' hll'
  exact hy hll' a

/-- Exact barycentric reconstruction sandwich in `M(A,P)`. -/
theorem tableBarycenter_probability_sandwich (mu : ProbabilityVector L)
    (y : L -> MonotoneTable A P) {lower upper : MonotoneTable A P}
    (hlower : forall l, 0 < mu l -> lower <= y l)
    (hupper : forall l, 0 < mu l -> y l <= upper) :
    lower <= tableBarycenter mu.1 y ∧ tableBarycenter mu.1 y <= upper := by
  have hlo : tableBarycenter mu.1 (fun _ => lower) <= tableBarycenter mu.1 y := by
    intro a
    apply finiteBind_mono_kernel_on_support
    intro l hl
    exact hlower l hl a
  have hhi : tableBarycenter mu.1 y <= tableBarycenter mu.1 (fun _ => upper) := by
    intro a
    apply finiteBind_mono_kernel_on_support
    intro l hl
    exact hupper l hl a
  rw [tableBarycenter_const mu lower] at hlo
  rw [tableBarycenter_const mu upper] at hhi
  exact ⟨hlo, hhi⟩

/-- The barycentric map associated with a finite factor kernel. -/
noncomputable def finiteTableApproximant {X : Type z}
    (p : X -> ProbabilityVector L) (y : L -> MonotoneTable A P) :
    X -> MonotoneTable A P :=
  fun x => tableBarycenter (p x).1 y

@[simp]
theorem finiteTableApproximant_apply {X : Type z}
    (p : X -> ProbabilityVector L) (y : L -> MonotoneTable A P) (x : X) :
    finiteTableApproximant p y x = tableBarycenter (p x).1 y :=
  rfl

/-- Pointwise barycentric sandwich for a finite table-valued approximant. -/
theorem finiteTableApproximant_sandwich {X : Type z}
    (p : X -> ProbabilityVector L) (y : L -> MonotoneTable A P)
    (lower upper : X -> MonotoneTable A P)
    (hlower : forall x l, 0 < p x l -> lower x <= y l)
    (hupper : forall x l, 0 < p x l -> y l <= upper x) (x : X) :
    lower x <= finiteTableApproximant p y x ∧
      finiteTableApproximant p y x <= upper x :=
  tableBarycenter_probability_sandwich (p x) y (hlower x) (hupper x)

end TableBarycenter

end FiniteValuationApproximable
