import CHFubini.Smyth
import Mathlib.Topology.Bases
import Mathlib.Topology.NhdsSet

/-!
New mathlib-only candidates for the paper's outer-base and Vietoris/Scott
claims. This file is intentionally separate from the frozen Smyth candidate.
-/

set_option autoImplicit false

open Set Topology TopologicalSpace Filter

universe u v

namespace CHFubini

/-- A decreasing sequence of open neighborhoods cofinal among all open
neighborhoods of a fixed set. -/
def IsDecreasingOuterBase {X : Type u} [TopologicalSpace X]
    (C : Set X) (N : ℕ → Set X) : Prop :=
  (∀ n, IsOpen (N n) ∧ C ⊆ N n) ∧ Antitone N ∧
    ∀ U : Set X, IsOpen U → C ⊆ U → ∃ n, N n ⊆ U

/-- Source `lem:outer-base`, for every compact countable subset of every
first-countable space; no separation axiom is added. -/
theorem compact_countable_decreasing_outer_base {X : Type u}
    [TopologicalSpace X] [FirstCountableTopology X]
    (C : Set X) (hc : IsCompact C) (hcount : C.Countable) :
    ∃ N : ℕ → Set X, IsDecreasingOuterBase C N := by
  classical
  letI : Countable C := hcount.to_subtype
  choose b hb hbase using fun x : C => (nhds_basis_opens x.val).exists_antitone_subbasis
  let B : Finset (C × ℕ) → Set X := fun t => ⋃ p ∈ t, b p.1 p.2
  have hBopen : ∀ t, IsOpen (B t) := by
    intro t
    exact isOpen_biUnion (fun p _ => (hb p.1 p.2).2)
  have hcofinal : ∀ U : Set X, IsOpen U → C ⊆ U →
      ∃ t : Finset (C × ℕ), C ⊆ B t ∧ B t ⊆ U := by
    intro U hU hCU
    let J := {p : C × ℕ // b p.1 p.2 ⊆ U}
    have hcover : C ⊆ ⋃ p : J, b p.val.1 p.val.2 := by
      intro x hx
      obtain ⟨n, hn⟩ := (hbase ⟨x, hx⟩).mem_iff.mp (hU.mem_nhds (hCU hx))
      exact mem_iUnion.mpr ⟨⟨(⟨x, hx⟩, n), hn⟩, (hb ⟨x, hx⟩ n).1⟩
    obtain ⟨s, hs⟩ := hc.elim_finite_subcover
      (fun p : J => b p.val.1 p.val.2) (fun p => (hb p.val.1 p.val.2).2) hcover
    let t : Finset (C × ℕ) := s.image Subtype.val
    refine ⟨t, ?_, ?_⟩
    · intro x hx
      obtain ⟨p, hp, hxp⟩ := mem_iUnion₂.mp (hs hx)
      exact mem_iUnion₂.mpr ⟨p.val, Finset.mem_image.mpr ⟨p, hp, rfl⟩, hxp⟩
    · intro x hx
      obtain ⟨p, hp, hxp⟩ := mem_iUnion₂.mp hx
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
      exact q.property hxp
  have hB : (𝓝ˢ C).HasBasis (fun t : Finset (C × ℕ) => C ⊆ B t) B := by
    constructor
    intro U
    constructor
    · intro hU
      obtain ⟨V, hV, hCV, hVU⟩ := mem_nhdsSet_iff_exists.mp hU
      obtain ⟨t, hCt, htV⟩ := hcofinal V hV hCV
      exact ⟨t, hCt, htV.trans hVU⟩
    · rintro ⟨t, hCt, htU⟩
      exact mem_nhdsSet_iff_exists.mpr ⟨B t, hBopen t, hCt, htU⟩
  letI : IsCountablyGenerated (𝓝ˢ C) := hB.isCountablyGenerated
  obtain ⟨N, hN, hNbase⟩ := (hasBasis_nhdsSet C).exists_antitone_subbasis
  refine ⟨N, hN, hNbase.2, ?_⟩
  intro U hU hCU
  exact hNbase.mem_iff.mp (mem_nhdsSet_iff_exists.mpr ⟨U, hU, hCU, Subset.rfl⟩)

/-- A compact set together with a sequence of compact sets which eventually
lies in each neighborhood of the first set has compact total union. -/
theorem compact_union_sequence_of_eventually_subset {X : Type u}
    [TopologicalSpace X] (C : Set X) (hc : IsCompact C)
    (F : ℕ → Set X) (hF : ∀ n, IsCompact (F n))
    (hconv : ∀ U : Set X, IsOpen U → C ⊆ U → ∃ N, ∀ n ≥ N, F n ⊆ U) :
    IsCompact (C ∪ ⋃ n, F n) := by
  classical
  apply isCompact_of_finite_subcover
  intro I U hU hcover
  have hCcover : C ⊆ ⋃ i, U i := subset_union_left.trans hcover
  obtain ⟨tC, htC⟩ := hc.elim_finite_subcover U hU hCcover
  obtain ⟨N, hN⟩ := hconv (⋃ i ∈ tC, U i) (isOpen_biUnion (fun i _ => hU i)) htC
  let E : Set X := ⋃ n ∈ Finset.range N, F n
  have hE : IsCompact E := (Finset.range N).isCompact_biUnion (fun n _ => hF n)
  have hEcover : E ⊆ ⋃ i, U i := by
    intro x hx
    obtain ⟨n, hn, hxn⟩ := mem_iUnion₂.mp hx
    exact hcover (Or.inr (mem_iUnion.mpr ⟨n, hxn⟩))
  obtain ⟨tE, htE⟩ := hE.elim_finite_subcover U hU hEcover
  refine ⟨tC ∪ tE, ?_⟩
  intro x hx
  rcases hx with hx | hx
  · obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (htC hx)
    exact mem_iUnion₂.mpr ⟨i, Finset.mem_union.mpr (Or.inl hi), hxi⟩
  · obtain ⟨n, hxn⟩ := mem_iUnion.mp hx
    by_cases hn : n < N
    · have hxE : x ∈ E := mem_iUnion₂.mpr ⟨n, Finset.mem_range.mpr hn, hxn⟩
      obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (htE hxE)
      exact mem_iUnion₂.mpr ⟨i, Finset.mem_union.mpr (Or.inr hi), hxi⟩
    · obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (hN n (Nat.le_of_not_gt hn) hxn)
      exact mem_iUnion₂.mpr ⟨i, Finset.mem_union.mpr (Or.inl hi), hxi⟩

/-- Every Scott neighborhood of a compact set contains a box from any of its
decreasing countable outer bases. This proves the relevant Vietoris/Scott
comparison directly, rather than installing the cited comparison as an axiom. -/
theorem scott_open_contains_box_of_outer_base {X : Type u}
    [TopologicalSpace X] [T2Space X] (C : Smyth X) (N : ℕ → Set X)
    (hN : IsDecreasingOuterBase (carrier C) N)
    {H : Set (WithScott (Smyth X))} (hH : IsOpen H)
    (hCH : WithScott.toScott C ∈ H) :
    ∃ n, (boxOpen ⟨N n, (hN.1 n).1⟩ : Set (WithScott (Smyth X))) ⊆ H := by
  classical
  by_contra hno
  have hbad : ∀ n, ∃ D : Smyth X, carrier D ⊆ N n ∧ WithScott.toScott D ∉ H := by
    intro n
    have hnot : ¬ (boxOpen ⟨N n, (hN.1 n).1⟩ : Set (WithScott (Smyth X))) ⊆ H :=
      fun h => hno ⟨n, h⟩
    obtain ⟨D, hD, hDH⟩ := Set.not_subset.mp hnot
    exact ⟨WithScott.ofScott D, hD, hDH⟩
  choose F hFN hFH using hbad
  have hconv : ∀ U : Set X, IsOpen U → carrier C ⊆ U →
      ∃ M, ∀ n ≥ M, carrier (F n) ⊆ U := by
    intro U hU hCU
    obtain ⟨M, hM⟩ := hN.2.2 U hU hCU
    exact ⟨M, fun n hn => (hFN n).trans ((hN.2.1 hn).trans hM)⟩
  have hcomp : ∀ n, IsCompact (carrier C ∪ ⋃ k, carrier (F (n + k))) := by
    intro n
    apply compact_union_sequence_of_eventually_subset _
      (OrderDual.ofDual C : NonemptyCompacts X).isCompact _
      (fun k => (OrderDual.ofDual (F (n + k)) : NonemptyCompacts X).isCompact)
    intro U hU hCU
    obtain ⟨M, hM⟩ := hconv U hU hCU
    exact ⟨M, fun k hk => hM (n + k) (hk.trans (Nat.le_add_left k n))⟩
  let K : ℕ → Smyth X := fun n => OrderDual.toDual
    ⟨⟨carrier C ∪ ⋃ k, carrier (F (n + k)), hcomp n⟩,
      (OrderDual.ofDual C : NonemptyCompacts X).nonempty.mono subset_union_left⟩
  have hK : Monotone K := by
    intro n m hnm
    change (carrier C ∪ ⋃ k, carrier (F (m + k))) ⊆
      (carrier C ∪ ⋃ k, carrier (F (n + k)))
    rintro x (hx | hx)
    · exact Or.inl hx
    · obtain ⟨k, hxk⟩ := mem_iUnion.mp hx
      obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le hnm
      exact Or.inr (mem_iUnion.mpr ⟨l + k, by simpa only [Nat.add_assoc] using hxk⟩)
  have hKC : IsLUB (range K) C := by
    constructor
    · rintro D ⟨n, rfl⟩
      exact subset_union_left
    · intro D hD
      change carrier D ⊆ carrier C
      intro x hxD
      by_contra hxC
      have hCavoid : carrier C ⊆ ({x} : Set X)ᶜ := by
        intro y hy hyx
        exact hxC ((Set.mem_singleton_iff.mp hyx) ▸ hy)
      obtain ⟨n, hn⟩ := hN.2.2 ({x} : Set X)ᶜ isClosed_singleton.isOpen_compl hCavoid
      have hxK : x ∈ carrier (K n) := hD (mem_range_self n) hxD
      rcases hxK with hx | hx
      · exact hxC hx
      · obtain ⟨k, hxk⟩ := mem_iUnion.mp hx
        exact hn ((hN.2.1 (Nat.le_add_right n k)) (hFN (n + k) hxk)) rfl
  have hinacc := ((Topology.IsScott.isOpen_iff_isUpperSet_and_dirSupInaccOn
    (D := Set.univ)).mp hH).2
  obtain ⟨D, ⟨n, rfl⟩, hKH⟩ := hinacc (mem_univ _) (range_nonempty K)
    hK.directed_le.directedOn_range hKC hCH
  have hKF : K n ≤ F n := by
    change carrier (F n) ⊆ carrier C ∪ ⋃ k, carrier (F (n + k))
    intro x hx
    exact Or.inr (mem_iUnion.mpr ⟨0, by simpa only [Nat.add_zero] using hx⟩)
  exact hFH n ((Topology.IsScott.isUpperSet_of_isOpen (D := Set.univ) hH) hKF hKH)

/-- The upper Vietoris topology generated by exactly the source's box sets,
on the same carrier as the actual Scott space. -/
@[implicit_reducible]
def upperVietorisTopology (X : Type u) [TopologicalSpace X] [T2Space X] :
    TopologicalSpace (WithScott (Smyth X)) :=
  generateFrom {B | ∃ U : Opens X, B = (boxOpen U : Set (WithScott (Smyth X)))}

theorem scott_eq_upperVietoris_of_outer_bases {X : Type u}
    [TopologicalSpace X] [T2Space X]
    (houter : ∀ C : Smyth X, ∃ N, IsDecreasingOuterBase (carrier C) N) :
    (inferInstance : TopologicalSpace (WithScott (Smyth X))) = upperVietorisTopology X := by
  apply le_antisymm
  · apply le_generateFrom
    rintro B ⟨U, rfl⟩
    exact (boxOpen U).isOpen
  · intro H hH
    apply @isOpen_iff_forall_mem_open _ (upperVietorisTopology X) _ |>.mpr
    intro C hCH
    obtain ⟨N, hN⟩ := houter (WithScott.ofScott C)
    obtain ⟨n, hn⟩ := scott_open_contains_box_of_outer_base (WithScott.ofScott C) N hN hH hCH
    refine ⟨boxOpen ⟨N n, (hN.1 n).1⟩, hn, ?_, (hN.1 n).2⟩
    exact isOpen_generateFrom_of_mem ⟨⟨N n, (hN.1 n).1⟩, rfl⟩

theorem smyth_firstCountable_of_outer_bases {X : Type u}
    [TopologicalSpace X] [T2Space X]
    (houter : ∀ C : Smyth X, ∃ N, IsDecreasingOuterBase (carrier C) N) :
    FirstCountableTopology (WithScott (Smyth X)) := by
  constructor
  intro C
  obtain ⟨N, hN⟩ := houter (WithScott.ofScott C)
  let B : ℕ → Set (WithScott (Smyth X)) :=
    fun n => boxOpen ⟨N n, (hN.1 n).1⟩
  have hB : (𝓝 C).HasBasis (fun _ : ℕ => True) B := by
    constructor
    intro U
    constructor
    · intro hU
      obtain ⟨H, hHU, hH, hCH⟩ := mem_nhds_iff.mp hU
      obtain ⟨n, hn⟩ := scott_open_contains_box_of_outer_base (WithScott.ofScott C) N hN hH hCH
      exact ⟨n, trivial, hn.trans hHU⟩
    · rintro ⟨n, _, hn⟩
      exact mem_of_superset ((boxOpen ⟨N n, (hN.1 n).1⟩).isOpen.mem_nhds (hN.1 n).2) hn
  exact hB.isCountablyGenerated

/-- Source `thm:Vietoris-Scott`, its topology equality and first-countability
conclusions, for the general situation supplied by `lem:compact-countable`.
Sobriety and well-filteredness are not smuggled into this interface. -/
theorem smyth_scott_eq_upperVietoris_and_firstCountable {X : Type u}
    [TopologicalSpace X] [T2Space X] [FirstCountableTopology X]
    (hcount : ∀ C : NonemptyCompacts X, (C : Set X).Countable) :
    (inferInstance : TopologicalSpace (WithScott (Smyth X))) = upperVietorisTopology X ∧
      FirstCountableTopology (WithScott (Smyth X)) := by
  have houter : ∀ C : Smyth X, ∃ N, IsDecreasingOuterBase (carrier C) N := by
    intro C
    exact compact_countable_decreasing_outer_base (carrier C)
      (OrderDual.ofDual C : NonemptyCompacts X).isCompact (hcount (OrderDual.ofDual C))
  exact ⟨scott_eq_upperVietoris_of_outer_bases houter, smyth_firstCountable_of_outer_bases houter⟩

/-- Source singleton map, using the specified singleton compact set rather
than an arbitrary order-theoretic or topological isomorphic replacement. -/
def singletonMap {X : Type u} [TopologicalSpace X] (x : X) : WithScott (Smyth X) :=
  WithScott.toScott (OrderDual.toDual ({x} : NonemptyCompacts X))

@[simp] theorem carrier_singletonMap {X : Type u} [TopologicalSpace X] (x : X) :
    carrier (WithScott.ofScott (singletonMap x)) = {x} := rfl

@[simp] theorem mem_compactNeighborhood_singleton {X : Type u} [TopologicalSpace X]
    (x : X) (U : WithScott (Opens X)) :
    U ∈ compactNeighborhood (WithScott.ofScott (singletonMap x)) ↔
      x ∈ (WithScott.ofScott U : Opens X) := by
  change ({x} : Set X) ⊆ ((WithScott.ofScott U : Opens X) : Set X) ↔ _
  exact singleton_subset_iff

theorem singletonMap_continuous_of_outer_bases {X : Type u}
    [TopologicalSpace X] [T2Space X]
    (houter : ∀ C : Smyth X, ∃ N, IsDecreasingOuterBase (carrier C) N) :
    Continuous (@singletonMap X _) := by
  rw [continuous_def]
  intro H hH
  apply isOpen_iff_forall_mem_open.mpr
  intro x hxH
  obtain ⟨N, hN⟩ := houter (WithScott.ofScott (singletonMap x))
  obtain ⟨n, hn⟩ := scott_open_contains_box_of_outer_base
    (WithScott.ofScott (singletonMap x)) N hN hH hxH
  refine ⟨N n, ?_, (hN.1 n).1, ?_⟩
  · intro y hy
    apply hn
    change ({y} : Set X) ⊆ N n
    exact singleton_subset_iff.mpr hy
  · exact (hN.1 n).2 rfl

theorem singletonMap_continuous_of_countable_compacts {X : Type u}
    [TopologicalSpace X] [T2Space X] [FirstCountableTopology X]
    (hcount : ∀ C : NonemptyCompacts X, (C : Set X).Countable) :
    Continuous (@singletonMap X _) := by
  apply singletonMap_continuous_of_outer_bases
  intro C
  exact compact_countable_decreasing_outer_base (carrier C)
    (OrderDual.ofDual C : NonemptyCompacts X).isCompact (hcount (OrderDual.ofDual C))

end CHFubini

