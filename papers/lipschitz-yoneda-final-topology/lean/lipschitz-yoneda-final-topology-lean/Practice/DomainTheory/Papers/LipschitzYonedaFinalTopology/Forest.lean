import Mathlib.Data.Fintype.Option
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Constructions
import Mathlib.Topology.Separation.Hausdorff

/-!
# Compact path space of a finite-level forest

This module formalizes the compactness core of
`lem:path-compactification`.  A path is represented by a sequence in the
product of the finite discrete types `Option (Node n)`.  `none` is the
terminal symbol.  Valid paths start with a node and satisfy the parent
relation whenever the next coordinate is nonterminal; this condition also
forces a path to remain terminal after its first `none`.
-/

set_option autoImplicit false
set_option linter.unnecessarySimpa false

open Set Filter
open scoped Topology

universe u

namespace LipschitzYonedaFinalTopology

/-- A forest with a finite set of nodes at each level and specified parent
maps between successive levels. -/
structure FiniteLevelForest where
  Node : ℕ → Type u
  finite_node : ∀ n, Finite (Node n)
  parent : ∀ n, Node (n + 1) → Node n

namespace FiniteLevelForest

variable (F : FiniteLevelForest)

instance nodeFinite (n : ℕ) : Finite (F.Node n) := F.finite_node n

/-- A node or the terminal symbol at one level. -/
def Level (n : ℕ) := Option (F.Node n)

namespace Level

instance (n : ℕ) : Finite (F.Level n) := by
  letI : Finite (F.Node n) := F.finite_node n
  change Finite (Option (F.Node n))
  exact inferInstance

instance (n : ℕ) : TopologicalSpace (F.Level n) := ⊥

instance (n : ℕ) : DiscreteTopology (F.Level n) :=
  discreteTopology_bot _

end Level

/-- The ambient product of all levels. -/
abbrev RawPath := ∀ n : ℕ, F.Level n

/-- Compatibility of two consecutive coordinates.  A terminal next
coordinate ends a finite path; a nonterminal next coordinate must have the
displayed parent. -/
def StepOK (n : ℕ) (a : F.Level n) (b : F.Level (n + 1)) : Prop :=
  match b with
  | none => True
  | some t => a = some (F.parent n t)

/-- Valid finite-or-infinite paths in the forest. -/
def Valid (p : F.RawPath) : Prop :=
  p 0 ≠ none ∧ ∀ n : ℕ, F.StepOK n (p n) (p (n + 1))

/-- If a valid path is terminal at level `n`, it is terminal at level
`n+1`. -/
theorem terminal_succ {p : F.RawPath} (hp : F.Valid p) {n : ℕ}
    (hn : p n = none) : p (n + 1) = none := by
  cases hnext : p (n + 1) with
  | none => rfl
  | some t =>
      have hstep := hp.2 n
      rw [hnext] at hstep
      change p n = some (F.parent n t) at hstep
      rw [hn] at hstep
      contradiction

/-- Once a valid path reaches the terminal symbol, every later coordinate is
terminal. -/
theorem terminal_of_le {p : F.RawPath} (hp : F.Valid p) {n m : ℕ}
    (hn : p n = none) (hnm : n ≤ m) : p m = none := by
  induction m, hnm using Nat.le_induction with
  | base => exact hn
  | succ m _ ih => exact F.terminal_succ hp ih

/-- The valid-path subset is closed in the product of finite discrete
levels. -/
theorem isClosed_valid : IsClosed {p : F.RawPath | F.Valid p} := by
  have hfirst : IsClosed {p : F.RawPath | p 0 ≠ none} := by
    have htarget : IsClosed {a : F.Level 0 | a ≠ none} :=
      isClosed_discrete _
    exact htarget.preimage (continuous_apply 0)
  have hsteps : IsClosed {p : F.RawPath |
      ∀ n : ℕ, F.StepOK n (p n) (p (n + 1))} := by
    rw [show {p : F.RawPath | ∀ n : ℕ, F.StepOK n (p n) (p (n + 1))} =
        ⋂ n : ℕ, {p : F.RawPath | F.StepOK n (p n) (p (n + 1))} by
      ext p
      simp]
    apply isClosed_iInter
    intro n
    have hpair : IsClosed {z : F.Level n × F.Level (n + 1) |
        F.StepOK n z.1 z.2} := isClosed_discrete _
    exact hpair.preimage ((continuous_apply n).prodMk (continuous_apply (n + 1)))
  simpa [Valid, setOf_and] using hfirst.inter hsteps

/-- The space of nonempty finite compatible paths and infinite compatible
paths. -/
abbrev Path := {p : F.RawPath // F.Valid p}

instance : CompactSpace F.Path :=
  F.isClosed_valid.isClosedEmbedding_subtypeVal.compactSpace

instance : T2Space F.Path := inferInstance

/-- Lemma `lem:path-compactification`, compactness clause. -/
theorem pathSpace_isCompact : IsCompact (Set.univ : Set F.Path) :=
  isCompact_univ

/-- Lemma `lem:path-compactification`, Hausdorff clause. -/
theorem pathSpace_isHausdorff : Pairwise (fun x y : F.Path ↦ Disjoint (𝓝 x) (𝓝 y)) :=
  pairwise_disjoint_nhds

/-- Paths sharing the first `N + 1` coordinates with `p`. -/
def PrefixCylinder (p : F.Path) (N : ℕ) : Set F.Path :=
  {q | ∀ k : ℕ, k ≤ N → q.1 k = p.1 k}

/-- Finite-prefix cylinders are open in the product-subspace topology. -/
theorem isOpen_prefixCylinder (p : F.Path) (N : ℕ) :
    IsOpen (F.PrefixCylinder p N) := by
  rw [show F.PrefixCylinder p N =
      ⋂ k ∈ Finset.range (N + 1),
        {q : F.Path | q.1 k = p.1 k} by
    ext q
    simp [PrefixCylinder, Nat.lt_succ_iff]]
  apply isOpen_biInter_finset
  intro k _hk
  have hopen : IsOpen ({a : F.Level k | a = p.1 k}) := isOpen_discrete _
  exact hopen.preimage ((continuous_apply k).comp continuous_subtype_val)

/-- A prefix ending with the terminal symbol determines the whole valid
path: all later coordinates must remain terminal. -/
theorem prefixCylinder_eq_singleton_of_terminal
    (p : F.Path) (n : ℕ) (hp : p.1 (n + 1) = none) :
    F.PrefixCylinder p (n + 1) = {p} := by
  ext q
  constructor
  · intro hq
    have hq_terminal : q.1 (n + 1) = none := by
      rw [hq (n + 1) le_rfl]
      exact hp
    apply Set.mem_singleton_iff.mpr
    apply Subtype.ext
    funext k
    by_cases hk : k ≤ n + 1
    · exact hq k hk
    · have hnk : n + 1 ≤ k := Nat.le_of_lt (Nat.lt_of_not_ge hk)
      rw [F.terminal_of_le p.2 hp hnk,
        F.terminal_of_le q.2 hq_terminal hnk]
  · intro hq
    rw [Set.mem_singleton_iff.mp hq]
    intro k _hk
    rfl

/-- The finite paths in the path compactification are isolated. -/
theorem isOpen_singleton_of_terminal
    (p : F.Path) (n : ℕ) (hp : p.1 (n + 1) = none) :
    IsOpen ({p} : Set F.Path) := by
  rw [← F.prefixCylinder_eq_singleton_of_terminal p n hp]
  exact F.isOpen_prefixCylinder p (n + 1)

/-- The ancestor at level `k ≤ n` of a node at level `n`. -/
def ancestor : (n : ℕ) → F.Node n → (k : ℕ) → k ≤ n → F.Node k
  | 0, s, k, hk => by
      have hkzero : k = 0 := Nat.eq_zero_of_le_zero hk
      subst k
      exact s
  | n + 1, s, k, hk =>
      if hlast : k = n + 1 then
        hlast ▸ s
      else
        ancestor n (F.parent n s) k (by omega)

@[simp]
theorem ancestor_self (n : ℕ) (s : F.Node n) :
    F.ancestor n s n le_rfl = s := by
  induction n with
  | zero => rfl
  | succ n ih => simp [ancestor]

@[simp]
theorem ancestor_succ_last (n : ℕ) (s : F.Node (n + 1)) :
    F.ancestor (n + 1) s (n + 1) le_rfl = s := by
  simp [ancestor]

/-- Below the last level, taking an ancestor first takes one parent step. -/
theorem ancestor_succ_of_le
    (n : ℕ) (s : F.Node (n + 1)) (k : ℕ) (hk : k ≤ n) :
    F.ancestor (n + 1) s k (hk.trans (Nat.le_succ n)) =
      F.ancestor n (F.parent n s) k hk := by
  simp [ancestor, Nat.ne_of_lt (hk.trans_lt (Nat.lt_succ_self n))]

/-- Consecutive ancestors satisfy the forest parent relation. -/
theorem parent_ancestor
    (n : ℕ) (s : F.Node n) (k : ℕ) (hk : k < n) :
    F.parent k
        (F.ancestor n s (k + 1) (Nat.succ_le_iff.mpr hk)) =
      F.ancestor n s k hk.le := by
  induction n generalizing k with
  | zero => omega
  | succ n ih =>
      by_cases hkn : k = n
      · subst k
        rw [F.ancestor_succ_last n s,
          F.ancestor_succ_of_le n s n le_rfl,
          F.ancestor_self n (F.parent n s)]
      · have hk' : k < n := by omega
        rw [F.ancestor_succ_of_le n s (k + 1)
            (Nat.succ_le_iff.mpr hk'),
          F.ancestor_succ_of_le n s k hk'.le]
        exact ih (F.parent n s) k hk'

/-- The raw compactified path from a root to a prescribed node, followed by
terminal symbols. -/
def nodePathRaw (n : ℕ) (s : F.Node n) : F.RawPath :=
  fun k ↦ if hk : k ≤ n then some (F.ancestor n s k hk) else none

/-- The raw path to a node is valid. -/
theorem nodePathRaw_valid (n : ℕ) (s : F.Node n) :
    F.Valid (F.nodePathRaw n s) := by
  constructor
  · simp [nodePathRaw]
  · intro k
    by_cases hnext : k + 1 ≤ n
    · have hk : k ≤ n := (Nat.le_succ k).trans hnext
      simp only [nodePathRaw, dif_pos hnext, dif_pos hk, StepOK]
      rw [F.parent_ancestor n s k (Nat.succ_le_iff.mp hnext)]
    · simp [nodePathRaw, hnext, StepOK]

/-- A compactified finite path ending at any prescribed forest node. -/
def nodePath (n : ℕ) (s : F.Node n) : F.Path :=
  ⟨F.nodePathRaw n s, F.nodePathRaw_valid n s⟩

@[simp]
theorem nodePath_at_last (n : ℕ) (s : F.Node n) :
    (F.nodePath n s).1 n = some s := by
  simp [nodePath, nodePathRaw]

@[simp]
theorem nodePath_terminal (n : ℕ) (s : F.Node n) :
    (F.nodePath n s).1 (n + 1) = none := by
  simp [nodePath, nodePathRaw]

end FiniteLevelForest

end LipschitzYonedaFinalTopology
