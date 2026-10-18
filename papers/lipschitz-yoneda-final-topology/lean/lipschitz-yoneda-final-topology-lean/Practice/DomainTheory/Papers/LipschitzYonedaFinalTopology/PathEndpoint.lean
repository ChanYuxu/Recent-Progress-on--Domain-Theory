import Practice.DomainTheory.Papers.LipschitzYonedaFinalTopology.ConeForest

/-!
# Endpoint map on the compact cone-forest path space

This file turns every finite or infinite compactified path into one uniform
increasing sequence of formal balls.  A finite path is continued by the
zero-radius ball at its last center; an infinite path uses the source formal
balls.  Yoneda completeness therefore constructs the endpoint map without a
separate finite/infinite definition, and the least-upper-bound property gives
its continuity by a prefix-cylinder argument.
-/

set_option autoImplicit false
set_option linter.unnecessarySimpa false

open Set Filter Topology
open scoped NNReal ENNReal Topology

noncomputable section

universe u

namespace LipschitzYonedaFinalTopology
namespace QuasiMetric

variable {X : Type u} {d : QuasiMetric X}

namespace FiniteConeForestData

/-- The first coordinate of every valid path contains a node. -/
theorem path_zero_exists (C : d.FiniteConeForestData)
    (p : C.forest.Path) :
    ∃ s : C.forest.Node 0, p.1 0 = some s := by
  cases hzero : p.1 0 with
  | none => exact False.elim (p.2.1 hzero)
  | some s => exact ⟨s, rfl⟩

/-- The selected root node of a valid path. -/
def pathRootNode (C : d.FiniteConeForestData)
    (p : C.forest.Path) : C.forest.Node 0 :=
  Classical.choose (C.path_zero_exists p)

@[simp]
theorem pathRootNode_spec (C : d.FiniteConeForestData)
    (p : C.forest.Path) :
    p.1 0 = some (C.pathRootNode p) :=
  Classical.choose_spec (C.path_zero_exists p)

/-- The formal-ball sequence attached to a compactified path.  At the first
terminal coordinate it jumps to radius zero at the preceding center, and it
then remains constant. -/
def pathFormalBall (C : d.FiniteConeForestData)
    (p : C.forest.Path) : ℕ → d.FormalBall := by
  classical
  intro n
  induction n with
  | zero => exact C.formalBall 0 (C.pathRootNode p)
  | succ n previous =>
      if h : ∃ t : C.forest.Node (n + 1), p.1 (n + 1) = some t then
        exact C.formalBall (n + 1) (Classical.choose h)
      else
        exact ⟨previous.center, 0⟩

/-- At a nonterminal coordinate, the unified path sequence is the source
formal ball of that node. -/
theorem pathFormalBall_of_some
    (C : d.FiniteConeForestData) (p : C.forest.Path)
    {n : ℕ} {s : C.forest.Node n} (hs : p.1 n = some s) :
    C.pathFormalBall p n = C.formalBall n s := by
  classical
  cases n with
  | zero =>
      have hroot : C.pathRootNode p = s := by
        exact Option.some.inj ((C.pathRootNode_spec p).symm.trans hs)
      simp [pathFormalBall, hroot]
  | succ n =>
      change
        (if h : ∃ t : C.forest.Node (n + 1),
            p.1 (n + 1) = some t then
          C.formalBall (n + 1) (Classical.choose h)
        else
          ⟨(C.pathFormalBall p n).center, 0⟩) =
        C.formalBall (n + 1) s
      split
      · rename_i h
        have hchosen := Classical.choose_spec h
        have heq : Classical.choose h = s :=
          Option.some.inj (hchosen.symm.trans hs)
        simp [heq]
      · rename_i h
        exact False.elim (h ⟨s, hs⟩)

/-- At a terminal successor coordinate, the path sequence is the zero-radius
ball at the preceding path-formal-ball center. -/
theorem pathFormalBall_of_none
    (C : d.FiniteConeForestData) (p : C.forest.Path)
    (n : ℕ) (hnone : p.1 (n + 1) = none) :
    C.pathFormalBall p (n + 1) =
      ⟨(C.pathFormalBall p n).center, 0⟩ := by
  classical
  change
    (if h : ∃ t : C.forest.Node (n + 1),
        p.1 (n + 1) = some t then
      C.formalBall (n + 1) (Classical.choose h)
    else
      ⟨(C.pathFormalBall p n).center, 0⟩) =
      ⟨(C.pathFormalBall p n).center, 0⟩
  split
  · rename_i h
    obtain ⟨t, ht⟩ := h
    rw [hnone] at ht
    contradiction
  · rfl

/-- The unified formal-ball sequence is increasing for every finite or
infinite path. -/
theorem pathFormalBall_step
    (C : d.FiniteConeForestData) (p : C.forest.Path) (n : ℕ) :
    C.pathFormalBall p n ≤ C.pathFormalBall p (n + 1) := by
  cases hnext : p.1 (n + 1) with
  | none =>
      rw [C.pathFormalBall_of_none p n hnext, FormalBall.le_def]
      simp [d.edist_self]
  | some t =>
      have hparent :
          p.1 n = some (C.forest.parent n t) := by
        have hstep := p.2.2 n
        rw [hnext] at hstep
        exact hstep
      rw [C.pathFormalBall_of_some p hparent,
        C.pathFormalBall_of_some p hnext]
      apply d.formalBall_le_of_scaled_edist_lt
        (C.slope_pos n) (C.slope_mono (Nat.le_succ n))
      exact C.parent_scaled_edist_lt n t

/-- Monotonicity of the unified formal-ball sequence. -/
theorem pathFormalBall_monotone
    (C : d.FiniteConeForestData) (p : C.forest.Path) :
    Monotone (C.pathFormalBall p) :=
  monotone_nat_of_le_succ (C.pathFormalBall_step p)

/-- Every nonterminal option contains a uniquely selectable node. -/
theorem exists_some_of_ne_none {A : Type u} (o : Option A)
    (ho : o ≠ none) : ∃ a : A, o = some a := by
  cases o with
  | none => exact False.elim (ho rfl)
  | some a => exact ⟨a, rfl⟩

/-- A path with no terminal coordinate determines an infinite branch. -/
def infiniteBranchOfPath
    (C : d.FiniteConeForestData) (p : C.forest.Path)
    (hinfinite : ∀ n, p.1 n ≠ none) : C.InfiniteBranch where
  node n := Classical.choose
    (exists_some_of_ne_none (p.1 n) (hinfinite n))
  parent_eq n := by
    have hn := Classical.choose_spec
      (exists_some_of_ne_none (p.1 n) (hinfinite n))
    have hnext := Classical.choose_spec
      (exists_some_of_ne_none (p.1 (n + 1)) (hinfinite (n + 1)))
    have hstep := p.2.2 n
    rw [hnext] at hstep
    exact (Option.some.inj (hn.symm.trans hstep)).symm

@[simp]
theorem infiniteBranchOfPath_node_spec
    (C : d.FiniteConeForestData) (p : C.forest.Path)
    (hinfinite : ∀ n, p.1 n ≠ none) (n : ℕ) :
    p.1 n = some ((C.infiniteBranchOfPath p hinfinite).node n) :=
  Classical.choose_spec
    (exists_some_of_ne_none (p.1 n) (hinfinite n))

/-- On an infinite path, the unified sequence agrees with its branch
sequence. -/
theorem pathFormalBall_eq_infiniteBranch
    (C : d.FiniteConeForestData) (p : C.forest.Path)
    (hinfinite : ∀ n, p.1 n ≠ none) (n : ℕ) :
    C.pathFormalBall p n =
      C.formalBall n ((C.infiniteBranchOfPath p hinfinite).node n) :=
  C.pathFormalBall_of_some p
    (C.infiniteBranchOfPath_node_spec p hinfinite n)

/-- The radii of the unified path sequence tend to zero, both for paths
that terminate and for infinite paths. -/
theorem pathFormalBall_radius_tendsto_zero
    (C : d.FiniteConeForestData)
    (base : ℕ)
    (hslope : ∀ n,
      C.slope n = ((base + n + 1 : ℕ) : ℝ≥0))
    (p : C.forest.Path) :
    Tendsto (fun n ↦ (C.pathFormalBall p n).radius)
      atTop (𝓝 0) := by
  by_cases hinfinite : ∀ n, p.1 n ≠ none
  · simpa only [C.pathFormalBall_eq_infiniteBranch p hinfinite] using
      C.branch_radius_tendsto_zero_from_base base hslope
        (C.infiniteBranchOfPath p hinfinite)
  · push Not at hinfinite
    obtain ⟨N, hN⟩ := hinfinite
    have hNpos : 0 < N := by
      exact Nat.pos_of_ne_zero fun hzero ↦
        p.2.1 (hzero ▸ hN)
    have heq :
        (fun n ↦ (C.pathFormalBall p n).radius) =ᶠ[atTop]
          (fun _ ↦ (0 : ℝ≥0)) := by
      filter_upwards [eventually_ge_atTop N] with n hn
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero
        (ne_of_gt (hNpos.trans_le hn))
      have hterminal : p.1 (m + 1) = none :=
        C.forest.terminal_of_le p.2 hN hn
      rw [C.pathFormalBall_of_none p m hterminal]
    exact (tendsto_congr' heq).2 tendsto_const_nhds

/-- The endpoint of a finite or infinite compactified path, constructed as
the center of the zero-radius least upper bound of its unified chain. -/
def pathEndpoint
    (C : d.FiniteConeForestData)
    (hcomplete : d.IsYonedaComplete)
    (base : ℕ)
    (hslope : ∀ n,
      C.slope n = ((base + n + 1 : ℕ) : ℝ≥0))
    (p : C.forest.Path) : X :=
  Classical.choose <|
    d.exists_zeroRadius_isLUB_of_monotone hcomplete
      (C.pathFormalBall p) (C.pathFormalBall_monotone p)
      (C.pathFormalBall_radius_tendsto_zero base hslope p)

/-- Every path endpoint satisfies the defining least-upper-bound equation. -/
theorem pathEndpoint_isLUB
    (C : d.FiniteConeForestData)
    (hcomplete : d.IsYonedaComplete)
    (base : ℕ)
    (hslope : ∀ n,
      C.slope n = ((base + n + 1 : ℕ) : ℝ≥0))
    (p : C.forest.Path) :
    IsLUB (Set.range (C.pathFormalBall p))
      (⟨C.pathEndpoint hcomplete base hslope p, 0⟩ : d.FormalBall) :=
  Classical.choose_spec <|
    d.exists_zeroRadius_isLUB_of_monotone hcomplete
      (C.pathFormalBall p) (C.pathFormalBall_monotone p)
      (C.pathFormalBall_radius_tendsto_zero base hslope p)

/-- A finite path realizing a node has exactly that node height. -/
theorem pathHeight_nodePath
    (C : d.FiniteConeForestData) (n : ℕ) (s : C.forest.Node n) :
    C.pathHeight (C.forest.nodePath n s) = (C.height n s : ℝ≥0∞) :=
  C.pathHeight_eq_height_of_terminal (C.forest.nodePath n s)
    (C.forest.nodePath_at_last n s) (C.forest.nodePath_terminal n s)

/-- At the terminal coordinate of the finite path to `s`, the unified chain
is the zero-radius ball centered at `s`. -/
theorem nodePath_pathFormalBall_terminal
    (C : d.FiniteConeForestData) (n : ℕ) (s : C.forest.Node n) :
    C.pathFormalBall (C.forest.nodePath n s) (n + 1) =
      (⟨C.center n s, 0⟩ : d.FormalBall) := by
  rw [C.pathFormalBall_of_none (C.forest.nodePath n s) n
      (C.forest.nodePath_terminal n s),
    C.pathFormalBall_of_some (C.forest.nodePath n s)
      (C.forest.nodePath_at_last n s)]
  rfl

/-- The finite-node path chain remains at its terminal zero-radius ball. -/
theorem nodePath_pathFormalBall_of_terminal_le
    (C : d.FiniteConeForestData) (n : ℕ) (s : C.forest.Node n)
    {m : ℕ} (hm : n + 1 ≤ m) :
    C.pathFormalBall (C.forest.nodePath n s) m =
      (⟨C.center n s, 0⟩ : d.FormalBall) := by
  induction m, hm using Nat.le_induction with
  | base => exact C.nodePath_pathFormalBall_terminal n s
  | succ m _hm ih =>
      have hnone : (C.forest.nodePath n s).1 (m + 1) = none :=
        C.forest.terminal_of_le (C.forest.nodePath n s).2
          (C.forest.nodePath_terminal n s) (Nat.le_succ_of_le _hm)
      rw [C.pathFormalBall_of_none (C.forest.nodePath n s) m hnone, ih]

/-- The endpoint map sends a finite node path to that node's center. -/
theorem pathEndpoint_nodePath
    (C : d.FiniteConeForestData)
    (hcomplete : d.IsYonedaComplete)
    (base : ℕ)
    (hslope : ∀ k,
      C.slope k = ((base + k + 1 : ℕ) : ℝ≥0))
    (n : ℕ) (s : C.forest.Node n) :
    C.pathEndpoint hcomplete base hslope (C.forest.nodePath n s) =
      C.center n s := by
  let p := C.forest.nodePath n s
  let z : d.FormalBall := ⟨C.center n s, 0⟩
  have hzAt : C.pathFormalBall p (n + 1) = z :=
    C.nodePath_pathFormalBall_terminal n s
  have hzLUB : IsLUB (Set.range (C.pathFormalBall p)) z := by
    constructor
    · intro b hb
      obtain ⟨m, rfl⟩ := hb
      by_cases hm : m ≤ n + 1
      · exact (C.pathFormalBall_monotone p hm).trans_eq hzAt
      · rw [C.nodePath_pathFormalBall_of_terminal_le n s
          (Nat.le_of_lt (Nat.lt_of_not_ge hm))]
    · intro q hq
      exact hq ⟨n + 1, hzAt⟩
  have heq :
      (⟨C.pathEndpoint hcomplete base hslope p, 0⟩ : d.FormalBall) = z :=
    (C.pathEndpoint_isLUB hcomplete base hslope p).unique hzLUB
  exact congrArg FormalBall.center heq

/-- The root margin propagates to the center of every term of the unified
path chain.  After a finite path terminates, the center stays fixed, so the
same estimate continues to hold. -/
theorem pathFormalBall_center_margin
    (C : d.FiniteConeForestData)
    {f : X → ℝ≥0∞} (hf : d.IsLipschitz (C.slope 0) f)
    {δ : ℝ≥0}
    (hrootMargin : ∀ r : C.forest.Node 0,
      ((C.height 0 r + δ : ℝ≥0) : ℝ≥0∞) ≤ f (C.center 0 r))
    (p : C.forest.Path) (n : ℕ) :
    C.pathHeight p + (δ : ℝ≥0∞) ≤
      f (C.pathFormalBall p n).center := by
  induction n with
  | zero =>
      let r := C.pathRootNode p
      have hr : p.1 0 = some r := C.pathRootNode_spec p
      rw [C.pathFormalBall_of_some p hr]
      exact (calc
        C.pathHeight p + (δ : ℝ≥0∞)
            ≤ (C.height 0 r : ℝ≥0∞) + δ :=
          add_le_add (C.pathHeight_le_node p hr) le_rfl
        _ = ((C.height 0 r + δ : ℝ≥0) : ℝ≥0∞) := by
          rw [ENNReal.coe_add]
        _ ≤ f (C.center 0 r) := hrootMargin r)
  | succ n ih =>
      cases hnext : p.1 (n + 1) with
      | none =>
          rw [C.pathFormalBall_of_none p n hnext]
          exact ih
      | some s =>
          rw [C.pathFormalBall_of_some p hnext]
          obtain ⟨r, hrs⟩ :=
            C.root_scaled_edist_lt (n + 1) s (Nat.succ_ne_zero n)
          have hstrict :
              (C.height (n + 1) s : ℝ≥0∞) + (δ : ℝ≥0∞) <
                f (C.center (n + 1) s) :=
            d.margin_of_scaled_edist_lt hf hrs (hrootMargin r)
          exact (add_le_add (C.pathHeight_le_node p hnext) le_rfl).trans
            hstrict.le

/-- Source equation `eq:uniform-margin` for the actual endpoint map.  The
proof avoids signed subtraction: the formal-ball order bounds the distance
from the `n`-th center to the endpoint by the `n`-th radius, and those radii
tend to zero. -/
theorem pathHeight_add_margin_le_endpoint
    (C : d.FiniteConeForestData)
    (hcomplete : d.IsYonedaComplete)
    (base : ℕ)
    (hslope : ∀ n,
      C.slope n = ((base + n + 1 : ℕ) : ℝ≥0))
    {f : X → ℝ≥0∞} (hf : d.IsLipschitz (C.slope 0) f)
    {δ : ℝ≥0}
    (hrootMargin : ∀ r : C.forest.Node 0,
      ((C.height 0 r + δ : ℝ≥0) : ℝ≥0∞) ≤ f (C.center 0 r))
    (p : C.forest.Path) :
    C.pathHeight p + (δ : ℝ≥0∞) ≤
      f (C.pathEndpoint hcomplete base hslope p) := by
  have hradius := C.pathFormalBall_radius_tendsto_zero base hslope p
  have herror :
      Tendsto
        (fun n ↦ C.slope 0 * (C.pathFormalBall p n).radius)
        atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul hradius
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _hendpointFinite
  have hevent : ∀ᶠ n in atTop,
      C.slope 0 * (C.pathFormalBall p n).radius < ε :=
    (tendsto_order.1 herror).2 ε hε
  obtain ⟨n, hn⟩ := hevent.exists
  have hball :=
    (C.pathEndpoint_isLUB hcomplete base hslope p).1 ⟨n, rfl⟩
  have hdist :
      d.edist (C.pathFormalBall p n).center
          (C.pathEndpoint hcomplete base hslope p) ≤
        ((C.pathFormalBall p n).radius : ℝ≥0∞) := by
    rw [FormalBall.le_def] at hball
    simpa using hball
  have hcenterEndpoint :
      f (C.pathFormalBall p n).center ≤
        (C.slope 0 : ℝ≥0∞) *
            d.edist (C.pathFormalBall p n).center
              (C.pathEndpoint hcomplete base hslope p) +
          f (C.pathEndpoint hcomplete base hslope p) := by
    simpa [add_comm] using tsub_le_iff_left.mp
      (hf (C.pathFormalBall p n).center
        (C.pathEndpoint hcomplete base hslope p))
  calc
    C.pathHeight p + (δ : ℝ≥0∞)
        ≤ f (C.pathFormalBall p n).center :=
      C.pathFormalBall_center_margin hf hrootMargin p n
    _ ≤ (C.slope 0 : ℝ≥0∞) *
          d.edist (C.pathFormalBall p n).center
            (C.pathEndpoint hcomplete base hslope p) +
        f (C.pathEndpoint hcomplete base hslope p) := hcenterEndpoint
    _ ≤ (C.slope 0 : ℝ≥0∞) *
          ((C.pathFormalBall p n).radius : ℝ≥0∞) +
        f (C.pathEndpoint hcomplete base hslope p) := by
      apply add_le_add _ le_rfl
      simpa [mul_comm] using
        mul_le_mul_left hdist (C.slope 0 : ℝ≥0∞)
    _ = ((C.slope 0 * (C.pathFormalBall p n).radius : ℝ≥0) : ℝ≥0∞) +
        f (C.pathEndpoint hcomplete base hslope p) := by
      rw [ENNReal.coe_mul]
    _ ≤ (ε : ℝ≥0∞) +
        f (C.pathEndpoint hcomplete base hslope p) := by
      exact add_le_add (ENNReal.coe_le_coe.mpr hn.le) le_rfl
    _ = f (C.pathEndpoint hcomplete base hslope p) + ε := add_comm _ _

/-- Prefix-equal paths have identical unified formal balls through the
specified level. -/
theorem pathFormalBall_eq_of_mem_prefixCylinder
    (C : d.FiniteConeForestData)
    (p q : C.forest.Path) (N : ℕ)
    (hq : q ∈ C.forest.PrefixCylinder p N)
    {n : ℕ} (hn : n ≤ N) :
    C.pathFormalBall q n = C.pathFormalBall p n := by
  induction n with
  | zero =>
      let s := C.pathRootNode p
      have hps : p.1 0 = some s := C.pathRootNode_spec p
      have hqs : q.1 0 = some s := (hq 0 (Nat.zero_le N)).trans hps
      rw [C.pathFormalBall_of_some p hps,
        C.pathFormalBall_of_some q hqs]
  | succ n ih =>
      have hn' : n ≤ N := (Nat.le_succ n).trans hn
      have hcoord : q.1 (n + 1) = p.1 (n + 1) := hq (n + 1) hn
      cases hpnext : p.1 (n + 1) with
      | none =>
          have hqnext : q.1 (n + 1) = none := hcoord.trans hpnext
          rw [C.pathFormalBall_of_none p n hpnext,
            C.pathFormalBall_of_none q n hqnext, ih hn']
      | some s =>
          have hqnext : q.1 (n + 1) = some s := hcoord.trans hpnext
          rw [C.pathFormalBall_of_some p hpnext,
            C.pathFormalBall_of_some q hqnext]

/-- The endpoint least-upper-bound equation transported to `WithScott`,
the type on which Scott openness is stated. -/
theorem pathEndpoint_isLUB_scott
    (C : d.FiniteConeForestData)
    (hcomplete : d.IsYonedaComplete)
    (base : ℕ)
    (hslope : ∀ n,
      C.slope n = ((base + n + 1 : ℕ) : ℝ≥0))
    (p : C.forest.Path) :
    IsLUB
      (Set.range (fun n ↦ WithScott.toScott (C.pathFormalBall p n)))
      (WithScott.toScott
        (⟨C.pathEndpoint hcomplete base hslope p, 0⟩ : d.FormalBall)) := by
  have hraw := C.pathEndpoint_isLUB hcomplete base hslope p
  constructor
  · intro z hz
    obtain ⟨n, rfl⟩ := hz
    exact hraw.1 ⟨n, rfl⟩
  · intro z hz
    exact hraw.2 (by
      intro b hb
      obtain ⟨n, rfl⟩ := hb
      exact hz ⟨n, rfl⟩)

/-- The endpoint map with its codomain kept definitionally at the induced
`d`-Scott topology. -/
def pathEndpointDScott
    (C : d.FiniteConeForestData)
    (hcomplete : d.IsYonedaComplete)
    (base : ℕ)
    (hslope : ∀ n,
      C.slope n = ((base + n + 1 : ℕ) : ℝ≥0)) :
    C.forest.Path → d.DScott :=
  fun p ↦ C.pathEndpoint hcomplete base hslope p

/-- Source line 555: the endpoint map from the compact path space to the
`d`-Scott space is continuous.  The proof is the manuscript's cylinder
argument, now driven by the actual least-upper-bound theorem. -/
theorem continuous_pathEndpoint
    (C : d.FiniteConeForestData)
    (hcomplete : d.IsYonedaComplete)
    (base : ℕ)
    (hslope : ∀ n,
      C.slope n = ((base + n + 1 : ℕ) : ℝ≥0)) :
    Continuous (C.pathEndpointDScott hcomplete base hslope) := by
  rw [continuous_def]
  intro O hO
  rw [isOpen_induced_iff] at hO
  obtain ⟨V, hVopen, hVO⟩ := hO
  apply isOpen_iff_forall_mem_open.mpr
  intro p hpO
  have hpV :
      WithScott.toScott
        (⟨C.pathEndpoint hcomplete base hslope p, 0⟩ : d.FormalBall) ∈ V := by
    change C.pathEndpoint hcomplete base hslope p ∈
      (fun x : d.DScott ↦
        WithScott.toScott (⟨x, 0⟩ : d.FormalBall)) ⁻¹' V
    rw [hVO]
    exact hpO
  have hV :=
    (Topology.IsScott.isOpen_iff_isUpperSet_and_dirSupInaccOn
      (D := Set.univ)).mp hVopen
  have hdirected :
      DirectedOn (· ≤ ·)
        (Set.range (fun n ↦
          WithScott.toScott (C.pathFormalBall p n))) := by
    rw [← directedOn_range]
    exact (C.pathFormalBall_monotone p).directed_le
  obtain ⟨z, hzrange, hzV⟩ := hV.2
    (d := Set.range (fun n ↦
      WithScott.toScott (C.pathFormalBall p n)))
    (by simp) (Set.range_nonempty _) hdirected
    (C.pathEndpoint_isLUB_scott hcomplete base hslope p) hpV
  obtain ⟨N, rfl⟩ := hzrange
  refine ⟨C.forest.PrefixCylinder p N, ?_,
    C.forest.isOpen_prefixCylinder p N, ?_⟩
  · intro q hq
    have hpq : C.pathFormalBall q N = C.pathFormalBall p N :=
      C.pathFormalBall_eq_of_mem_prefixCylinder p q N hq le_rfl
    have hleRaw : C.pathFormalBall q N ≤
        (⟨C.pathEndpoint hcomplete base hslope q, 0⟩ : d.FormalBall) :=
      (C.pathEndpoint_isLUB hcomplete base hslope q).1 ⟨N, rfl⟩
    have hleScott :
        WithScott.toScott (C.pathFormalBall p N) ≤
          WithScott.toScott
            (⟨C.pathEndpoint hcomplete base hslope q, 0⟩ : d.FormalBall) := by
      simpa only [hpq] using hleRaw
    have hqV := hV.1 hleScott hzV
    change C.pathEndpoint hcomplete base hslope q ∈ O
    rw [← hVO]
    exact hqV
  · intro k _hk
    rfl

end FiniteConeForestData
end QuasiMetric
end LipschitzYonedaFinalTopology
