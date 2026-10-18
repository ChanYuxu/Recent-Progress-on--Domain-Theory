import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.SetTheory.Ordinal.Rank
import Mathlib.SetTheory.Cardinal.Regular
import Mathlib.Order.WellFounded
import Mathlib.Data.List.GetD
import Mathlib.Data.List.OfFn

/-!
Background for He–Zhang Lemma 4.12 (analytic well-founded rank boundedness).
The source cites this result without prescribing its proof.  We prove the
background by a countable finite-prefix approximation tree; this is not a
replacement of any of the domain-theoretic arguments of Theorem 4.13.
-/

set_option autoImplicit false

universe u

namespace CoreCompactSimplified.HeZhangRank

open Set Filter Ordinal
open scoped Topology Cardinal

abbrev Baire := ℕ → ℕ

/-- Every rank of a well-founded relation on a countable carrier is countable. -/
theorem countable_rank_lt_omega_one {α : Type} [Countable α]
    {R : α → α → Prop} (hR : WellFounded R) (x : α) :
    (hR.apply x).rank < ω₁ := by
  induction x using hR.induction with
  | h x ih =>
    rw [Acc.rank_eq]
    apply Ordinal.iSup_lt_omega_one
    rintro ⟨y, hy⟩
    exact (Cardinal.isSuccLimit_omega _).succ_lt (ih y hy)

private def cell (s : List (List ℕ)) (i j : ℕ) : ℕ := (s.getD i []).getD j 0

private def gridOf (c : ℕ → Baire) (n : ℕ) : List (List ℕ) :=
  List.ofFn fun i : Fin n ↦ List.ofFn fun j : Fin n ↦ c i j

@[simp] private theorem gridOf_length (c : ℕ → Baire) (n : ℕ) :
    (gridOf c n).length = n := by simp [gridOf]

private theorem gridOf_cell (c : ℕ → Baire) (n i j : ℕ) (hi : i < n) (hj : j < n) :
    cell (gridOf c n) i j = c i j := by
  simp [cell, gridOf, hi, hj]

private def Realizes (R : Baire → Baire → Prop) (s : List (List ℕ))
    (c : ℕ → Baire) : Prop :=
  (∀ i, i + 1 < s.length → R (c (i + 1)) (c i)) ∧
  ∀ i j, i < s.length → j < s.length → c i j = cell s i j

private def Node (R : Baire → Baire → Prop) :=
  {s : List (List ℕ) // ∃ c, Realizes R s c}

private instance (R : Baire → Baire → Prop) : Countable (Node R) :=
  inferInstanceAs (Countable {s : List (List ℕ) // ∃ c, Realizes R s c})

private def Extension (R : Baire → Baire → Prop) (t s : Node R) : Prop :=
  t.val.length = s.val.length + 1 ∧
  ∀ i j, i < s.val.length → j < s.val.length → cell t.val i j = cell s.val i j

private def root (R : Baire → Baire → Prop) : Node R :=
  ⟨[], fun _ _ ↦ 0, by simp [Realizes]⟩

private theorem chain_length {R : Baire → Baire → Prop} (a : ℕ → Node R)
    (ha : ∀ k, Extension R (a (k + 1)) (a k)) (k : ℕ) :
    (a k).val.length = (a 0).val.length + k := by
  induction k with
  | zero => simp
  | succ k ih => rw [(ha k).1, ih]; omega

private theorem chain_cell {R : Baire → Baire → Prop} (a : ℕ → Node R)
    (ha : ∀ k, Extension R (a (k + 1)) (a k)) {k l : ℕ} (hkl : k ≤ l)
    {i j : ℕ} (hi : i < (a k).val.length) (hj : j < (a k).val.length) :
    cell (a l).val i j = cell (a k).val i j := by
  induction l, hkl using Nat.le_induction with
  | base => rfl
  | succ l hkl ih =>
    have hlen : (a k).val.length ≤ (a l).val.length := by
      rw [chain_length a ha k, chain_length a ha l]
      omega
    exact ((ha l).2 i j (hi.trans_le hlen) (hj.trans_le hlen)).trans ih

private theorem extension_wellFounded {R : Baire → Baire → Prop}
    (hclosed : IsClosed {p : Baire × Baire | R p.1 p.2})
    (hR : WellFounded R) : WellFounded (Extension R) := by
  apply wellFounded_iff_isEmpty_descending_chain.mpr
  constructor
  rintro ⟨a, ha⟩
  choose c hc using fun k ↦ (a k).property
  let b : ℕ → Baire := fun i j ↦ cell (a (i + j + 1)).val i j
  have hcoordinates (i j : ℕ) :
      ∀ᶠ k in atTop, c k i j = b i j := by
    filter_upwards [eventually_ge_atTop (i + j + 1)] with k hk
    have hi : i < (a (i + j + 1)).val.length := by
      rw [chain_length a ha]
      omega
    have hj : j < (a (i + j + 1)).val.length := by
      rw [chain_length a ha]
      omega
    have hlen : (a (i + j + 1)).val.length ≤ (a k).val.length := by
      rw [chain_length a ha (i + j + 1), chain_length a ha k]
      omega
    exact ((hc k).2 i j (hi.trans_le hlen) (hj.trans_le hlen)).trans
      (chain_cell a ha hk hi hj)
  have hlim (i : ℕ) : Tendsto (fun k ↦ c k i) atTop (𝓝 (b i)) := by
    apply tendsto_pi_nhds.mpr
    intro j
    exact tendsto_const_nhds.congr' ((hcoordinates i j).mono fun _ h ↦ h.symm)
  have hb (i : ℕ) : R (b (i + 1)) (b i) := by
    apply hclosed.mem_of_tendsto ((hlim (i + 1)).prodMk_nhds (hlim i))
    filter_upwards [eventually_ge_atTop (i + 2)] with k hk
    apply (hc k).1
    rw [chain_length a ha]
    omega
  exact (wellFounded_iff_isEmpty_descending_chain.mp hR).false ⟨b, hb⟩

private def appendPoint (c : ℕ → Baire) (n : ℕ) (y : Baire) : ℕ → Baire :=
  fun i ↦ if i < n then c i else y

private theorem append_realizes {R : Baire → Baire → Prop} {s : List (List ℕ)}
    {c : ℕ → Baire} (hc : Realizes R s c) (hn : 0 < s.length) {y : Baire}
    (hy : R y (c (s.length - 1))) :
    Realizes R (gridOf (appendPoint c s.length y) (s.length + 1))
      (appendPoint c s.length y) := by
  constructor
  · intro i hi
    simp only [gridOf_length] at hi
    by_cases hlt : i + 1 < s.length
    · simpa [appendPoint, hlt, show i < s.length by omega] using hc.1 i hlt
    · have heq : i = s.length - 1 := by omega
      simpa [appendPoint, heq, show ¬ s.length - 1 + 1 < s.length by omega,
        show s.length - 1 < s.length by omega] using hy
  · intro i j hi hj
    simp only [gridOf_length] at hi hj
    exact (gridOf_cell _ _ i j hi hj).symm

private def extendNode {R : Baire → Baire → Prop} (s : Node R)
    (c : ℕ → Baire) (hc : Realizes R s.val c) (hn : 0 < s.val.length)
    (y : Baire) (hy : R y (c (s.val.length - 1))) : Node R :=
  ⟨gridOf (appendPoint c s.val.length y) (s.val.length + 1), _,
    append_realizes hc hn hy⟩

private theorem extendNode_extension {R : Baire → Baire → Prop} (s : Node R)
    (c : ℕ → Baire) (hc : Realizes R s.val c) (hn : 0 < s.val.length)
    (y : Baire) (hy : R y (c (s.val.length - 1))) :
    Extension R (extendNode s c hc hn y hy) s := by
  constructor
  · simp [extendNode]
  · intro i j hi hj
    change cell (gridOf _ _) i j = _
    rw [gridOf_cell _ _ _ _ (by omega) (by omega)]
    simpa [appendPoint, hi] using hc.2 i j hi hj

private theorem rank_le_realizing_node {R : Baire → Baire → Prop} (hR : WellFounded R)
    (hN : WellFounded (Extension R)) (x : Baire) :
    ∀ (s : Node R) (c : ℕ → Baire), Realizes R s.val c → 0 < s.val.length →
      c (s.val.length - 1) = x → (hR.apply x).rank ≤ (hN.apply s).rank := by
  induction x using hR.induction with
  | h x ih =>
    intro s c hc hn hx
    rw [Acc.rank_eq]
    apply Ordinal.iSup_le
    rintro ⟨y, hy⟩
    have hy' : R y (c (s.val.length - 1)) := hx ▸ hy
    let t := extendNode s c hc hn y hy'
    have ht : Extension R t s := extendNode_extension s c hc hn y hy'
    have hty : (appendPoint c s.val.length y) (t.val.length - 1) = y := by
      simp [t, extendNode, appendPoint]
    have hle := ih y hy t (appendPoint c s.val.length y)
      (append_realizes hc hn hy') (by simp [t, extendNode]) hty
    have hlt : (hN.apply t).rank < (hN.apply s).rank := Acc.rank_lt_of_rel _ ht
    exact Order.succ_le_of_lt (hle.trans_lt hlt)

/-- A closed well-founded relation on Baire space has a uniform countable
ordinal bound.  The finite-prefix witness tree is itself countable. -/
theorem closed_baire_rank_bounded (R : Baire → Baire → Prop)
    (hclosed : IsClosed {p : Baire × Baire | R p.1 p.2})
    (hR : WellFounded R) :
    ∃ γ : Ordinal, γ < ω₁ ∧ ∀ x, (hR.apply x).rank < γ := by
  let hN := extension_wellFounded hclosed hR
  refine ⟨(hN.apply (root R)).rank, countable_rank_lt_omega_one hN (root R), ?_⟩
  intro x
  let c : ℕ → Baire := fun _ ↦ x
  let s : Node R := ⟨gridOf c 1, c, by simp [Realizes, gridOf_cell]⟩
  have hs : Extension R s (root R) := by simp [Extension, s, root]
  have hle : (hR.apply x).rank ≤ (hN.apply s).rank :=
    rank_le_realizing_node hR hN x s c (by simp [s, Realizes, gridOf_cell])
      (by simp [s]) (by simp [s, c])
  exact hle.trans_lt (Acc.rank_lt_of_rel _ hs)

private theorem endpoint_rank_comparison {X : Type u} (R : X → X → Prop)
    (hR : WellFounded R) (f : Baire → X × X)
    (hf : Set.range f = {p | R p.1 p.2})
    (hC : WellFounded (fun a b ↦ (f a).2 = (f b).1)) (x : X) :
    ∀ a, (f a).1 = x →
      (hR.apply x).rank ≤ Ordinal.lift.{u} (hC.apply a).rank := by
  induction x using hR.induction with
  | h x ih =>
    intro a ha
    rw [Acc.rank_eq]
    apply Ordinal.iSup_le
    rintro ⟨y, hy⟩
    have hymem : (y, x) ∈ Set.range f := hf.symm ▸ hy
    obtain ⟨b, hb⟩ := hymem
    have hby : (f b).1 = y := congrArg Prod.fst hb
    have hba : (f b).2 = (f a).1 := (congrArg Prod.snd hb).trans ha.symm
    have hle := ih y hy b hby
    have hlt : Ordinal.lift.{u} (hC.apply b).rank < Ordinal.lift.{u} (hC.apply a).rank :=
      Ordinal.lift_lt.mpr <|
        Acc.rank_lt_of_rel (r := fun a b ↦ (f a).2 = (f b).1) (hC.apply a) hba
    exact Order.succ_le_of_lt (hle.trans_lt hlt)

/-- He–Zhang Lemma 4.12, in the topological presentation of an analytic
relation.  Hausdorffness suffices; a Polish carrier is not additionally needed
once analyticity of the relation has been supplied. -/
theorem analytic_wellFounded_rank_bounded {X : Type u} [TopologicalSpace X] [T2Space X]
    (R : X → X → Prop) (hR : MeasureTheory.AnalyticSet {p : X × X | R p.1 p.2})
    (hwf : WellFounded R) :
    ∃ γ : Ordinal.{u}, γ < ω₁ ∧ ∀ x, (hwf.apply x).rank < γ := by
  classical
  rw [MeasureTheory.AnalyticSet] at hR
  rcases hR with hempty | ⟨f, hcont, hfrange⟩
  · refine ⟨1, ?_, ?_⟩
    · simpa using (Ordinal.natCast_lt_omega0 1).trans Ordinal.omega0_lt_omega_one
    · intro x
      rw [Acc.rank_eq]
      haveI : IsEmpty {y // R y x} := ⟨fun y ↦ by
        have hy : (y.val, x) ∈ ({p : X × X | R p.1 p.2} : Set (X × X)) := y.property
        rw [hempty] at hy
        exact hy⟩
      simp
  · let C : Baire → Baire → Prop := fun a b ↦ (f a).2 = (f b).1
    have hfed (a : Baire) : R (f a).1 (f a).2 := by
      have ha : f a ∈ Set.range f := Set.mem_range_self a
      rwa [hfrange] at ha
    have hC : WellFounded C := by
      apply (InvImage.wf (fun a ↦ (f a).1) hwf).mono
      intro a b hab
      change R (f a).1 (f b).1
      change (f a).2 = (f b).1 at hab
      exact hab ▸ hfed a
    have hclosed : IsClosed {p : Baire × Baire | C p.1 p.2} :=
      isClosed_eq (hcont.snd.comp continuous_fst) (hcont.fst.comp continuous_snd)
    obtain ⟨γ, hγ, hbound⟩ := closed_baire_rank_bounded C hclosed hC
    have hlift : Ordinal.lift.{u} γ < (ω₁ : Ordinal.{u}) := by
      simpa using (Ordinal.lift_lt.{u}.mpr hγ)
    refine ⟨Order.succ (Ordinal.lift.{u} γ),
      (Cardinal.isSuccLimit_omega _).succ_lt hlift, ?_⟩
    intro x
    apply Order.lt_succ_of_le
    rw [Acc.rank_eq]
    apply Ordinal.iSup_le
    rintro ⟨y, hy⟩
    have hymem : (y, x) ∈ Set.range f := hfrange.symm ▸ hy
    obtain ⟨b, hb⟩ := hymem
    have hle := endpoint_rank_comparison R hwf f hfrange hC y b (congrArg Prod.fst hb)
    exact Order.succ_le_of_lt (hle.trans_lt (Ordinal.lift_lt.mpr (hbound b)))

/-- Closed relations on Polish spaces are a source-facing special case of
the analytic boundedness theorem used in the proof of Theorem 4.13. -/
theorem closed_polish_rank_bounded {X : Type u} [TopologicalSpace X] [PolishSpace X]
    (R : X → X → Prop) (hclosed : IsClosed {p : X × X | R p.1 p.2})
    (hwf : WellFounded R) :
    ∃ γ : Ordinal.{u}, γ < ω₁ ∧ ∀ x, (hwf.apply x).rank < γ := by
  apply analytic_wellFounded_rank_bounded R _ hwf
  letI : MeasurableSpace (X × X) := borel (X × X)
  letI : BorelSpace (X × X) := ⟨rfl⟩
  exact hclosed.measurableSet.analyticSet

/-- Analyticity on a standard Borel space, displayed through a compatible
Polish presentation.  This existential contains only the usual descriptive-set
hypotheses, not a rank bound or any part of the conclusion. -/
def StandardBorelAnalyticRelation {X : Type u} [MeasurableSpace X]
    (R : X → X → Prop) : Prop :=
  ∃ τ : TopologicalSpace X, letI := τ
    BorelSpace X ∧ PolishSpace X ∧
      MeasureTheory.AnalyticSet {p : X × X | R p.1 p.2}

/-- He–Zhang Lemma 4.12 with the printed standard-Borel interface. -/
theorem standardBorel_analytic_rank_bounded {X : Type u} [MeasurableSpace X]
    [StandardBorelSpace X] (R : X → X → Prop)
    (hR : StandardBorelAnalyticRelation R) (hwf : WellFounded R) :
    ∃ γ : Ordinal.{u}, γ < ω₁ ∧ ∀ x, (hwf.apply x).rank < γ := by
  obtain ⟨τ, hBorel, hPolish, hAnalytic⟩ := hR
  letI : TopologicalSpace X := τ
  letI : BorelSpace X := hBorel
  letI : PolishSpace X := hPolish
  exact analytic_wellFounded_rank_bounded R hAnalytic hwf

end CoreCompactSimplified.HeZhangRank
